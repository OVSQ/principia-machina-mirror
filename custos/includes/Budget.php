<?php
/**
 * Budget: the budget roll-up (charter 8.3, 8.5; TPS 5.3.31-5.3.37), the work of the job custosBudget,
 * run by the job runner out of the web request. Plain PHP the harness runs without MediaWiki.
 *
 *   run(now) the meter's rows over the three horizons summed (CPU use in thousandths of a CPU
 *            second, each row weighted by its sample), the PRESSURE LEVEL asked of the Calculator
 *            (`governor pressure_level` over the sums, the level the last roll-up kept as `prev`),
 *            the roll-up and the level written to the budget; each account's traffic record read
 *            at now (`governor traffic_stage`) and its stage written beside it, conditionally: the
 *            stage is written only where the stored record is still the text read (MeterStore::
 *            stageTraffic), so a Landing step written between the read and the write is never
 *            erased; on a miss the record is read again and asked again, at most STAGE_TRIES times;
 *            the meter's rows older than the widest horizon pruned; the PRE-GATE's deny list
 *            written: one line per CONTAINED account, "account<TAB><name><TAB><retry_after>", the
 *            wait the Calculator's (`traffic_stage`'s served_retry_after) plus `governor jitter`,
 *            written to a temporary file of mode 0640 in the list's folder and renamed over it, so
 *            the PRE-GATE reads the old list or the new, never a part; a temporary file a crashed
 *            run left behind is removed at the next.
 * PHP adds the use of the rows and the jitter to the wait and decides nothing: every level, stage,
 * wait and jitter is the Calculator's. The traffic record is handed to the Calculator as the text it
 * answered, and the roll-up never writes it: the Landing's step under the seat lock is its one writer.
 */

namespace Custos;

final class Budget {
	public const DENY_HEAD = '# custos pre-gate deny list';
	/** The reads of one account's record a roll-up makes before it leaves the stage to the next roll-up. */
	public const STAGE_TRIES = 3;
	/** A temporary file of the list older than this many seconds is a crashed run's leftover. */
	public const LEFTOVER_AGE = 60;
	/** The temporary file's mode, set before any byte is written and before the rename. */
	public const DENY_MODE = 0640;
	private const JSON = JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_THROW_ON_ERROR;

	/** @var callable():array */
	private $draw;

	/**
	 * @param string $denyFile the PRE-GATE's list ($wgCustosPreGateFile); empty: none written
	 * @param callable|null $draw the jitter's draw [num, den]; null: random_int over 10^6
	 */
	public function __construct( private Calculator $calc, private MeterStore $meter, private string $denyFile, ?callable $draw = null ) {
		$this->draw = $draw ?? static fn (): array => [ random_int( 0, 999999 ), 1000000 ];
	}

	/** The roll-up at $now: ["use", "requests", "level", "kept", "stages", "denied", "pruned", "unsettled"]. */
	public function run( int $now ): array {
		$use = $requests = [];
		foreach ( MeterStore::HORIZONS as $h => $span ) {
			$use[$h] = $requests[$h] = 0;
		}
		foreach ( $this->meter->rows( $now - MeterStore::HORIZONS['thirty_days'] ) as $r ) {
			foreach ( MeterStore::HORIZONS as $h => $span ) {
				if ( $r['time'] > $now - $span ) {
					$use[$h] += $r['cpu'] * max( 1, $r['weight'] );
					$requests[$h] += max( 1, $r['weight'] );
				}
			}
		}
		$prev = $this->meter->budget()['kept'];
		$p = $this->ask( 'pressure_level', json_encode( [ 'use' => $use, 'prev' => $prev, 'external_until' => 0, 'now' => $now ], self::JSON ) );
		if ( !is_string( $p['level'] ?? null ) || !is_string( $p['kept'] ?? null ) ) {
			throw new CalculatorFault( 'the pressure level is not of the form {"level", "kept", "ratio"}', CalculatorFault::ANSWER_FORM, 'governor', 'pressure_level' );
		}
		$this->meter->putBudget( $use, $requests, $now, $p['level'], $p['kept'] );
		$pruned = $this->meter->prune( $now - MeterStore::HORIZONS['thirty_days'] );

		$stages = $deny = $unsettled = [];
		foreach ( $this->meter->accounts() as $account ) {
			$s = null;
			$written = false;
			for ( $try = 0; $try < self::STAGE_TRIES && !$written; $try++ ) {
				$t = $this->meter->traffic( $account );
				if ( $t === null ) {
					break;
				}
				$s = $this->stage( $t['record'], $now, 'PETITION' );
				$written = $this->meter->stageTraffic( $account, $t['record'], $s['stage'], $now );
			}
			if ( $s === null ) {
				continue;
			}
			if ( !$written ) {
				// Every read was overtaken by a Landing step: its record and stage stand, the next roll-up settles it.
				$unsettled[] = $account;
			}
			$stages[$account] = $s['stage'];
			if ( $s['stage'] === 'CONTAINED' ) {
				if ( !is_int( $s['served_retry_after'] ?? null ) || $s['served_retry_after'] < 0 ) {
					throw new CalculatorFault( 'a CONTAINED stage carries no served_retry_after', CalculatorFault::ANSWER_FORM, 'governor', 'traffic_stage' );
				}
				$base = $s['served_retry_after'];
				$deny[$account] = $base + $this->jitter( $base );
			}
		}
		ksort( $deny, SORT_STRING );
		if ( $this->denyFile !== '' ) {
			self::writeDeny( $this->denyFile, $deny, $now );
		}
		return [ 'use' => $use, 'requests' => $requests, 'level' => $p['level'], 'kept' => $p['kept'], 'stages' => $stages, 'denied' => $deny,
			'pruned' => $pruned, 'unsettled' => $unsettled ];
	}

	/** `governor traffic_stage` of a record's text at $now for a request of $kind. */
	public function stage( string $record, int $now, string $kind ): array {
		$s = $this->ask( 'traffic_stage', '{"traffic":' . $record . ',"now":' . $now . ',"kind":' . json_encode( $kind, self::JSON ) . '}' );
		if ( !is_string( $s['stage'] ?? null ) ) {
			throw new CalculatorFault( 'the traffic stage carries no stage', CalculatorFault::ANSWER_FORM, 'governor', 'traffic_stage' );
		}
		return $s;
	}

	private function jitter( int $base ): int {
		$j = $this->calc->call( 'governor', 'jitter', json_encode( [ 'base' => $base, 'draw' => ( $this->draw )() ], self::JSON ) );
		if ( $j['exit'] !== 0 || !is_int( $j['value'] ) || $j['value'] < 0 ) {
			throw new CalculatorFault( 'the governor\'s jitter is not a count', CalculatorFault::ANSWER_FORM, 'governor', 'jitter' );
		}
		return $j['value'];
	}

	private function ask( string $fn, string $json ): array {
		$a = $this->calc->call( 'governor', $fn, $json );
		if ( $a['exit'] !== 0 || !is_array( $a['value'] ) ) {
			throw new CalculatorFault( "the governor's $fn was refused: " . (string)( $a['refused'] ?? '' ), CalculatorFault::ANSWER_FORM, 'governor', $fn );
		}
		return $a['value'];
	}

	/**
	 * The deny list written whole: a temporary file in the list's folder, made with mode 0640 before any
	 * byte is written, then renamed over it. A temporary file of the list older than LEFTOVER_AGE (a
	 * crashed run's) is removed first; a younger one may be a concurrent run's and is left.
	 * @param array<string, int> $deny account => retry_after
	 */
	public static function writeDeny( string $file, array $deny, int $now ): void {
		$text = self::DENY_HEAD . " $now\n";
		foreach ( $deny as $account => $after ) {
			$account = (string)$account;
			if ( preg_match( '/[\x00-\x1f\x7f]/', $account ) === 1 ) {
				continue;
			}
			$text .= "account\t$account\t" . (int)$after . "\n";
		}
		foreach ( glob( $file . '.tmp.*', GLOB_NOSORT ) ?: [] as $old ) {
			$m = @filemtime( $old );
			if ( preg_match( '/\.tmp\.[0-9a-f]{12}\z/', $old ) === 1 && $m !== false && $m < time() - self::LEFTOVER_AGE ) {
				@unlink( $old );
			}
		}
		$tmp = $file . '.tmp.' . bin2hex( random_bytes( 6 ) );
		$h = @fopen( $tmp, 'x' );
		$ok = $h !== false && @chmod( $tmp, self::DENY_MODE ) && clearstatcache( true, $tmp ) === null && ( fileperms( $tmp ) & 0777 ) === self::DENY_MODE
			&& @fwrite( $h, $text ) === strlen( $text ) && @fflush( $h );
		if ( $h !== false ) {
			$ok = @fclose( $h ) && $ok;
		}
		if ( !$ok || !@rename( $tmp, $file ) ) {
			@unlink( $tmp );
			throw new \RuntimeException( 'the PRE-GATE list could not be written' );
		}
	}
}
