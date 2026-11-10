<?php
/**
 * BatchJob: the frame every batch job of Custos shares (the re-audit, the cluster month, the
 * bibliography recheck). run( $job ) does, in this order:
 *  1. writes the run record (JobRunStore::start);
 *  2. checks the job's context (JobContext), else the outcome JOB CONTEXT and the Calculator is
 *     never started;
 *  3. asks `governor admit` in lane 5 (kind DEFERRABLE JOB, for the recheck BIBLIOGRAPHY RECHECK
 *     JOB), the state carrying the pressure level CustosBatch names (CLEAR until the level is
 *     metered); a decision other than ADMITTED ends the run DEFERRED with the retry-after, and
 *     nothing is written but the run record;
 *  4. runs the job's body, a callable ( Calculator ): array{outcome, detail?, counts?}; the three
 *     jobs answer NOT BUILT until their units (outcome NOTHING DUE, detail NOT BUILT);
 *  5. finishes the run record once, whatever happened.
 * A DIGEST MISMATCH ends the run INTEGRITY HALT; any other fault of the Calculator, the page
 * writer or the body ends it FAULT; the detail is the words Refusal::detail allows (no path, no
 * query, no server name), the exception itself going to the error channel. Not retried.
 */

namespace Custos;

use Throwable;

final class BatchJob {
	public const REAUDIT = 'reaudit';
	public const CLUSTER = 'cluster';
	public const RECHECK = 'recheck';
	/** The jobs and the request kind each asks the governor under (both sort to lane 5). */
	public const JOBS = [
		self::REAUDIT => 'DEFERRABLE JOB',
		self::CLUSTER => 'DEFERRABLE JOB',
		self::RECHECK => 'BIBLIOGRAPHY RECHECK JOB',
	];
	public const OUTCOMES = [ 'DONE', 'NOTHING DUE', 'DEFERRED', 'JOB CONTEXT', 'SOURCE FAILING', 'REFUSED', 'FAULT', 'INTEGRITY HALT' ];
	public const NOT_BUILT = 'NOT BUILT';
	public const LOG = 'Custos';
	/** CustosBatch's members and their defaults. */
	public const DEFAULTS = [ 'pressure' => 'CLEAR', 'defer_wait' => 300 ];
	private const PRESSURES = [ 'CLEAR', 'BUSY', 'STRAINED', 'OVERLOADED' ];

	/** @var callable */
	private $clock;
	/** @var callable */
	private $draw;
	/** @var callable */
	private $fault;
	/** @var array<string,callable> */
	private array $bodies;

	/**
	 * @param array $conf governor_off, agent_stop (bools), min_address_space (KiB), limits (the text of /proc/self/limits; a test's; null: read it), pressure, defer_wait (seconds)
	 * @param array<string,callable> $bodies a body per job name; a job with none answers NOT BUILT
	 */
	public function __construct( private Calculator $calc, private JobRunStore $runs, private array $conf = [],
		array $bodies = [], ?callable $clock = null, ?callable $draw = null, ?callable $fault = null
	) {
		$this->conf += self::DEFAULTS + [ 'governor_off' => false, 'agent_stop' => false,
			'min_address_space' => JobContext::MIN_ADDRESS_SPACE ];
		$this->bodies = $bodies;
		$this->clock = $clock ?? static fn (): int => time();
		$this->draw = $draw ?? static fn (): array => [ random_int( 0, 999999 ), 1000000 ];
		$this->fault = $fault ?? static function ( string $job, Throwable $e ): void {
			if ( function_exists( 'wfDebugLog' ) ) {
				wfDebugLog( self::LOG, "batch job $job: " . get_class( $e ) . ': ' . $e->getMessage() );
			}
		};
	}

	/** The configuration's members, read from the wiki's settings. */
	public static function confFrom( \MediaWiki\Config\Config $config ): array {
		$ctx = (array)$config->get( 'CustosJobContext' );
		return (array)$config->get( 'CustosBatch' ) + [
			'governor_off' => (bool)$config->get( 'CustosGovernorOff' ),
			'agent_stop' => (bool)$config->get( 'CustosAgentStop' ),
			'min_address_space' => (int)( $ctx['min_address_space'] ?? JobContext::MIN_ADDRESS_SPACE ),
		];
	}

	/**
	 * One run of $job. The run's row as it stands at the end, with the members of the outcome:
	 * ["id", "job", "outcome", "detail", "counts", "retry_after"?].
	 */
	public function run( string $job ): array {
		if ( !isset( self::JOBS[$job] ) ) {
			throw new \InvalidArgumentException( 'not a batch job' );
		}
		$id = $this->runs->start( $job, $this->stamp() );
		$answer = $this->frame( $job );
		$answer += [ 'detail' => '', 'counts' => [] ];
		$counts = json_encode( (object)$answer['counts'], JSON_UNESCAPED_SLASHES | JSON_THROW_ON_ERROR );
		$this->runs->finish( $id, $answer['outcome'], $answer['detail'], $counts, $this->stamp() );
		return [ 'id' => $id, 'job' => $job, 'counts' => $counts ] + $answer;
	}

	private function frame( string $job ): array {
		try {
			$refusal = JobContext::refusal( (int)$this->conf['min_address_space'], $this->conf['limits'] ?? null );
			if ( $refusal !== null ) {
				return [ 'outcome' => 'JOB CONTEXT', 'detail' => $refusal ];
			}
			$d = $this->admit( $job );
			if ( !is_array( $d ) || ( $d['decision'] ?? null ) !== 'ADMITTED' ) {
				$after = is_array( $d ) && is_int( $d['retry_after'] ?? null ) ? $d['retry_after'] : (int)$this->conf['defer_wait'];
				return [ 'outcome' => 'DEFERRED', 'retry_after' => $after,
					'detail' => 'the governor did not admit the job: ' . ( is_array( $d ) ? (string)( $d['decision'] ?? '' ) : '' )
						. ' (retry after ' . $after . ' seconds)' ];
			}
			$body = $this->bodies[$job] ?? static fn ( Calculator $c ): array => [ 'outcome' => 'NOTHING DUE', 'detail' => self::NOT_BUILT ];
			$r = $body( $this->calc );
			if ( !in_array( $r['outcome'] ?? null, self::OUTCOMES, true ) ) {
				throw new CalculatorFault( 'the job body answered an outcome outside the closed set', CalculatorFault::ANSWER_FORM );
			}
			return $r;
		} catch ( Throwable $e ) {
			( $this->fault )( $job, $e );
			$d = Refusal::detail( $e );
			if ( $d['refused'] === 'INTEGRITY HALT' ) {
				return [ 'outcome' => 'INTEGRITY HALT', 'detail' => (string)$d['detail'] ];
			}
			return [ 'outcome' => 'FAULT', 'detail' => (string)( $d['detail'] ?? $d['refused'] . ': ' . ( $d['class'] ?? '' ) ) ];
		}
	}

	/** `governor admit` over the state of a job with no account: no seats, nothing in flight. */
	private function admit( string $job ): mixed {
		$pressure = in_array( $this->conf['pressure'], self::PRESSURES, true ) ? $this->conf['pressure'] : 'CLEAR';
		$state = [
			'now' => ( $this->clock )(),
			'agent_stop' => (bool)$this->conf['agent_stop'],
			'suspended' => false,
			'governor_off' => (bool)$this->conf['governor_off'],
			'agent_seats' => [ 0, 0 ],
			'sponsor_seats' => [ 0, 0 ],
			'agent_in_flight' => 0,
			'sponsor_in_flight' => 0,
			'finishing_in_flight' => 0,
			'starting_in_flight' => 0,
			'pressure' => $pressure,
		];
		$request = [ 'kind' => self::JOBS[$job], 'seats' => 0, 'draw' => ( $this->draw )() ];
		$r = $this->calc->call( 'governor', 'admit', json_encode( [ 'state' => $state, 'request' => $request ],
			JSON_UNESCAPED_SLASHES | JSON_THROW_ON_ERROR ) );
		if ( $r['exit'] !== 0 ) {
			throw new CalculatorFault( 'the governor refused the request: ' . $r['refused'], CalculatorFault::ANSWER_FORM, 'governor', 'admit' );
		}
		return $r['value'];
	}

	private function stamp(): string {
		return gmdate( 'YmdHis', ( $this->clock )() );
	}
}
