<?php
/**
 * Meter: the governor's meter (charter 8.3, TPS 5.3.31). GA0, the hook BeforeInitialize: the request's
 * start (wall clock, CPU from getrusage), and ApiBeforeMain for api.php. GA9, the hook ApiAfterExecute and a shutdown function: one row
 * written to custos_meter (MeterStore) for a governed request: the account (empty for an anonymous one,
 * which carries its network instead), the kind, its lane read from custos/lanes.json (the table
 * `pcalc governor lane` answers for every kind, written at build like the permissions table and
 * checked against the built pcalc by the harness), CPU and wall in thousandths of a second, peak
 * memory, response bytes and landed bytes; anonymous reads sampled 1 in $wgCustosMeterSample, the
 * row weighted by it. Then the job custosBudget pushed, deduplicated. No Calculator is called in a
 * web request: the lane is the table's.
 *
 * kind() maps a request to a governed kind's word: action=pma's op (POLL is POLL OTHER until the
 * holder is read, a corner), an agent's other API call AGENT CORE READ, a signed-in account's
 * request SIGNED IN USER, an anonymous one ANONYMOUS READ. row() is the pure part the harness runs.
 */

namespace Custos;

use MediaWiki\MediaWikiServices;
use Throwable;

final class Meter {
	public const PMA_KINDS = [ 'PETITION' => 'PETITION', 'PUSH' => 'PUSH', 'RELEASE' => 'RELEASE', 'POLL' => 'POLL OTHER',
		'STATUS' => 'STATUS', 'INQUIRE' => 'INQUIRE', 'HEARTBEAT' => 'HEARTBEAT' ];

	private static ?array $lanes = null;
	private static ?array $start = null;
	private static bool $done = false;
	private static ?string $op = null;

	/** The lane table, read once per request cycle. @throws PageFault */
	public static function lanes(): array {
		if ( self::$lanes === null ) {
			$t = json_decode( (string)@file_get_contents( dirname( __DIR__ ) . '/lanes.json' ), true, 2 );
			if ( !is_array( $t ) ) {
				throw new PageFault( 'the lane table is not readable' );
			}
			self::$lanes = $t;
		}
		return self::$lanes;
	}

	/** The governed kind of a request. */
	public static function kind( bool $registered, bool $agent, ?string $action, ?string $op ): string {
		if ( $action === 'pma' && $op !== null && isset( self::PMA_KINDS[$op] ) ) {
			return self::PMA_KINDS[$op];
		}
		if ( !$registered ) {
			return 'ANONYMOUS READ';
		}
		return $agent ? 'AGENT CORE READ' : 'SIGNED IN USER';
	}

	/** An anonymous request's network: an IPv4 /24 or an IPv6 /48, as text. */
	public static function network( string $ip ): string {
		if ( filter_var( $ip, FILTER_VALIDATE_IP, FILTER_FLAG_IPV4 ) !== false ) {
			return implode( '.', array_slice( explode( '.', $ip ), 0, 3 ) ) . '.0/24';
		}
		$bin = @inet_pton( $ip );
		if ( $bin === false || strlen( $bin ) !== 16 ) {
			return '';
		}
		return inet_ntop( substr( $bin, 0, 6 ) . str_repeat( "\0", 10 ) ) . '/48';
	}

	/** CPU time used so far, thousandths of a CPU second (getrusage's user and system). */
	public static function cpuNow(): int {
		$u = getrusage();
		return intdiv( (int)$u['ru_utime.tv_sec'] * 1000000 + (int)$u['ru_utime.tv_usec'] + (int)$u['ru_stime.tv_sec'] * 1000000 + (int)$u['ru_stime.tv_usec'], 1000 );
	}

	/**
	 * One meter row, or null when the sample passes it over.
	 * @param array $start ["time", "wall_ms", "cpu"] at GA0; @param array $end ["wall_ms", "cpu", "memory", "bytes", "landed"]
	 * @param int $draw a draw in [0, $sample): the row is kept for an anonymous read when it is 0
	 */
	public static function row( array $lanes, string $kind, string $account, string $network, array $start, array $end, int $sample, int $draw ): ?array {
		$weight = 1;
		if ( $kind === 'ANONYMOUS READ' && $sample > 1 ) {
			if ( $draw !== 0 ) {
				return null;
			}
			$weight = $sample;
		}
		return [ 'time' => (int)$start['time'], 'account' => $account, 'network' => $account === '' ? $network : '', 'op' => $kind,
			'lane' => (int)( $lanes[$kind] ?? 0 ), 'cpu' => max( 0, (int)$end['cpu'] - (int)$start['cpu'] ),
			'wall' => max( 0, (int)$end['wall_ms'] - (int)$start['wall_ms'] ), 'memory' => max( 0, (int)$end['memory'] ),
			'bytes' => max( 0, (int)$end['bytes'] ), 'landed' => max( 0, (int)$end['landed'] ), 'weight' => $weight ];
	}

	/** GA0: the hook BeforeInitialize. */
	public function onBeforeInitialize( $title, $unused, $output, $user, $request, $mediaWiki ): void {
		self::begin();
	}

	/** GA0 for api.php: the hook ApiBeforeMain. */
	public function onApiBeforeMain( &$main ): void {
		self::begin();
	}

	/** GA9's API part: the hook ApiAfterExecute names the op. */
	public function onApiAfterExecute( $module ): void {
		if ( $module->getModuleName() === 'pma' ) {
			self::$op = $module->getRequest()->getRawVal( 'op' );
		}
		self::begin();
	}

	private static function begin(): void {
		if ( self::$start !== null ) {
			return;
		}
		self::$start = [ 'time' => time(), 'wall_ms' => (int)( hrtime( true ) / 1000000 ), 'cpu' => self::cpuNow() ];
		register_shutdown_function( [ self::class, 'finish' ] );
	}

	/** GA9: the row written at the request's end, and the roll-up job pushed. A failure is logged, never shown. */
	public static function finish(): void {
		if ( self::$done || self::$start === null ) {
			return;
		}
		self::$done = true;
		try {
			$services = MediaWikiServices::getInstance();
			$config = $services->getMainConfig();
			$ctx = \RequestContext::getMain();
			$user = $ctx->getUser();
			$req = $ctx->getRequest();
			$registered = $user->isRegistered();
			$agent = $registered && in_array( 'pma-agent', $services->getUserGroupManager()->getUserGroups( $user ), true );
			$kind = self::kind( $registered, $agent, $req->getRawVal( 'action' ), self::$op ?? $req->getRawVal( 'op' ) );
			$sample = max( 1, (int)$config->get( 'CustosMeterSample' ) );
			$row = self::row( self::lanes(), $kind, $registered ? $user->getName() : '', $registered ? '' : self::network( $req->getIP() ),
				self::$start, [ 'wall_ms' => (int)( hrtime( true ) / 1000000 ), 'cpu' => self::cpuNow(), 'memory' => memory_get_peak_usage(),
					'bytes' => max( 0, (int)ob_get_length() ), 'landed' => 0 ], $sample, random_int( 0, $sample - 1 ) );
			if ( $row !== null ) {
				( new DbMeterStore() )->record( $row );
				$services->getJobQueueGroup()->push( new BudgetJob( [] ) );
			}
		} catch ( Throwable $e ) {
			if ( function_exists( 'wfDebugLog' ) ) {
				wfDebugLog( Landing::LOG, 'meter: ' . get_class( $e ) . ': ' . $e->getMessage() );
			}
		}
	}
}
