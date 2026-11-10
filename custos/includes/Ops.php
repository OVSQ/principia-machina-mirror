<?php
/**
 * Ops: the ops of action=pma the live-exercise path takes (version 1's wire words PETITION, POLL,
 * PUSH, RELEASE), plain PHP the harness runs without MediaWiki; ApiPma is the glue. An op that
 * changes state runs GA1, the request's shape and nothing else (every parameter a string, its
 * bytes counted, the prefix in its form, no unknown parameter, no account parameter), writes
 * one ticket with the parameters as received and enqueues the job custosLand with the ticket's
 * id; it answers the ticket, QUEUED, and when to poll. Its work is the job's: no Calculator is
 * called here and `records` is never parsed, only its bytes counted. The identity values
 * (`prompt_digest`, `stated_model`, `relayed_model`, optional) are shape-checked here and ride on the
 * ticket's request as received; nothing compares or rewrites them (the refusals FAMILY, MODEL and
 * PROMPT are owed to the unit that enforces them). POLL reads a
 * ticket of the account's own.
 *
 * The sweep: a ticket whose job was lost (its enqueue failed after the row was written, or the job
 * runner dropped it) would stay QUEUED for ever. POLL of the account's own ticket that is QUEUED and
 * at least $wgCustosSweepAfter seconds old (by its created time) pushes custosLand for it again; the
 * job is pushed with MediaWiki's deduplication, so one job per ticket waits, and the job's
 * conditional claim (QUEUED -> IN WORK, TicketStore::claim) lands each ticket once: a second job for
 * a ticket already claimed or answered writes nothing. POLL's answer keeps its form. The sweep runs
 * on POLL only, and an IN WORK ticket is never swept (the job context's timeout and the integrity
 * halt stand). The 202's poll_after stays the configured constant: no Calculator in a web request.
 *
 * The governor's ops (charter 8.3, TPS 5.3.35): HEARTBEAT writes a ticket as the other write ops do (the
 * job extends the holder's lease). STATUS and INQUIRE are reads, answered from the meter's store with no
 * Calculator: STATUS the site's part (the Calculator's version and digest from $wgCustosBuild, the
 * pressure level of the last budget roll-up) and the account's traffic stage; INQUIRE the account's
 * traffic stage (its dossier page a later corner). POLL of a ticket the job answered with a refusal
 * that carries the governor's HTTP status (403, 429, 503) answers it as `http_status` with its
 * `retry_after` (the decision's, jitter included, exactly), which ApiPma sends as the status and Retry-After; an answer without a wait is answered with
 * the status alone, no Retry-After.
 */

namespace Custos;

use MediaWiki\Config\Config;

final class Ops {
	public const OPS = [ 'PETITION', 'POLL', 'PUSH', 'RELEASE', 'HEARTBEAT', 'STATUS', 'INQUIRE', 'STRUCTURE_TEST' ];
	public const WRITE_OPS = [ 'PETITION', 'PUSH', 'RELEASE', 'HEARTBEAT', 'STRUCTURE_TEST' ];
	public const READ_OPS = [ 'POLL', 'STATUS', 'INQUIRE' ];
	/** The HTTP statuses a governor's refusal carries (TPS 5.3.35): a switch, an account cause, a fleet cause. */
	public const REFUSAL_STATUSES = [ 403, 429, 503 ];

	/**
	 * The parameters each op takes beside op and prefix; POLL takes no prefix. A PUSH's
	 * challenge_response is its answer to the execution challenge, checked by the job (Landing).
	 */
	public const PARAMS = [
		'PETITION' => [ 'block', 'prompt_digest', 'stated_model', 'relayed_model' ],
		'PUSH' => [ 'records', 'block', 'prompt_digest', 'relayed_model', 'challenge_response' ],
		'RELEASE' => [ 'block' ],
		'HEARTBEAT' => [ 'block' ],
		'STRUCTURE_TEST' => [],
		'POLL' => [ 'ticket' ],
		'STATUS' => [],
		'INQUIRE' => [],
	];
	public const REQUIRED = [ 'PUSH' => [ 'records' ], 'POLL' => [ 'ticket' ] ];

	/** `records` at most this many bytes by default: the Calculator's reader bound. */
	public const MAX_REQUEST_BYTES = 1048576;
	/** The bound of a prefix in bytes: the column ct_prefix is VARBINARY(255). */
	public const MAX_PREFIX_BYTES = 255;
	/** The bound of `stated_model` and `relayed_model` in bytes: a model's name as the client presents it. */
	public const MAX_MODEL_BYTES = 128;
	public const POLL_AFTER = 30;
	/** A QUEUED ticket at least this many seconds old is re-enqueued when its account polls it. */
	public const SWEEP_AFTER = 600;

	/** A work block's name: a letter or digit, then at most 63 of letters, digits, "_", ".", ":", "-". */
	private const BLOCK = '/\A[A-Za-z0-9][A-Za-z0-9_.:-]{0,63}\z/';
	/** The identity values' prompt digest: 64 lowercase hexadecimal (a digest the client computed; Custos recomputes nothing). */
	private const PROMPT_DIGEST = '/\A[0-9a-f]{64}\z/';
	private const TICKET = '/\A[1-9][0-9]{0,17}\z/';

	private TicketStore $tickets;
	/** @var callable(int):void */
	private $enqueue;
	private int $pollAfter;
	private int $maxRequestBytes;
	private int $sweepAfter;
	/** @var callable():int */
	private $clock;
	/** @var callable(int, \Throwable):void */
	private $fault;
	private MeterStore $meter;
	private array $build;

	/**
	 * @param callable(int):void $enqueue pushes the job custosLand for the ticket of that id, deduplicated
	 * @param callable|null $clock the server time, whole seconds; null: time()
	 * @param callable|null $fault the error channel of the sweep: called with the ticket's number and
	 *   the exception of a push that threw; null: MediaWiki's debug log `Custos` (wfDebugLog) where it
	 *   exists, the exception's class only, else nothing
	 */
	public function __construct( TicketStore $tickets, callable $enqueue, int $pollAfter = self::POLL_AFTER,
		int $maxRequestBytes = self::MAX_REQUEST_BYTES, int $sweepAfter = self::SWEEP_AFTER, ?callable $clock = null,
		?callable $fault = null, ?MeterStore $meter = null, array $build = [] ) {
		$this->meter = $meter ?? new MemMeterStore();
		$this->build = [ 'version' => (string)( $build['version'] ?? '' ), 'digest' => (string)( $build['digest'] ?? '' ) ];
		$this->tickets = $tickets;
		$this->enqueue = $enqueue;
		$this->pollAfter = $pollAfter;
		$this->maxRequestBytes = $maxRequestBytes;
		$this->sweepAfter = $sweepAfter;
		$this->clock = $clock ?? static fn (): int => time();
		$this->fault = $fault ?? static function ( int $id, \Throwable $e ): void {
			if ( function_exists( 'wfDebugLog' ) ) {
				wfDebugLog( Landing::LOG, "sweep ticket $id: the push threw " . get_class( $e ) );
			}
		};
	}

	public static function fromConfig( Config $config, TicketStore $tickets, callable $enqueue, ?MeterStore $meter = null ): self {
		$build = $config->get( 'CustosBuild' );
		return new self( $tickets, $enqueue, (int)$config->get( 'CustosPollAfter' ), (int)$config->get( 'CustosMaxRequestBytes' ),
			(int)$config->get( 'CustosSweepAfter' ), null, null, $meter, is_array( $build ) ? $build : [] );
	}

	public function heartbeat( mixed $prefix, string $account, array $params ): array {
		return $this->write( 'HEARTBEAT', $prefix, $account, $params );
	}

	/** STRUCTURE_TEST: a ticket and its job, as PETITION; the test and the holder's check are the job's. */
	public function structureTest( mixed $prefix, string $account, array $params ): array {
		return $this->write( 'STRUCTURE_TEST', $prefix, $account, $params );
	}

	/** STATUS: the site's part and the account's stage; any account, or none. */
	public function status( array $params, string $account ): array {
		$this->shape( 'STATUS', $params );
		$b = $this->meter->budget();
		return [ 'build' => $this->build, 'governor' => [ 'level' => (string)$b['level'], 'rolled' => (int)$b['rolled'] ],
			'stage' => $account === '' ? null : $this->stage( $account ) ];
	}

	/** INQUIRE: the account's traffic stage (CR11's inquiry; the dossier page a later corner). */
	public function inquire( array $params, string $account ): array {
		$this->shape( 'INQUIRE', $params );
		if ( $account === '' ) {
			throw new Refusal( 'custos-not-agent', 'INQUIRE needs an account' );
		}
		return [ 'account' => $account, 'stage' => $this->stage( $account ) ];
	}

	/** The stage the meter's store holds for the account; NORMAL for an account with no record. */
	private function stage( string $account ): string {
		return $this->meter->traffic( $account )['stage'] ?? 'NORMAL';
	}

	/**
	 * The governor's HTTP status and Retry-After of a ticket's answer, Custos's own JSON (Landing wrote it
	 * with json_encode): its top-level `status` when one of 403, 429, 503, and its `poll_after`, null
	 * when the answer carries none (no Retry-After is sent).
	 * @return array{0: int, 1: ?int}|null
	 */
	public static function refusalStatus( string $answer ): ?array {
		$a = json_decode( $answer, true, 16 );
		if ( !is_array( $a ) || !in_array( $a['status'] ?? null, self::REFUSAL_STATUSES, true ) ) {
			return null;
		}
		return [ $a['status'], is_int( $a['poll_after'] ?? null ) ? max( 0, $a['poll_after'] ) : null ];
	}

	public function petition( mixed $prefix, string $account, array $params ): array {
		return $this->write( 'PETITION', $prefix, $account, $params );
	}

	public function push( mixed $prefix, string $account, array $params ): array {
		return $this->write( 'PUSH', $prefix, $account, $params );
	}

	public function release( mixed $prefix, string $account, array $params ): array {
		return $this->write( 'RELEASE', $prefix, $account, $params );
	}

	/** The ticket's state; when DONE, the job's answer text as `answer`, else when to poll again. */
	public function poll( array $params, string $account ): array {
		$p = $this->shape( 'POLL', $params );
		$row = $this->tickets->get( (int)$p['ticket'] );
		if ( $row === null ) {
			throw new Refusal( 'custos-no-ticket', 'there is no ticket ' . $p['ticket'] );
		}
		if ( $account === '' || $row['account'] !== $account ) {
			throw new Refusal( 'custos-ticket-not-yours', 'the ticket ' . $p['ticket'] . ' is another account\'s' );
		}
		if ( $row['state'] === TicketStore::QUEUED && $this->stale( (string)$row['created'] ) ) {
			// The sweep: the ticket's job may be lost; pushed again, deduplicated, claimed once by the job.
			// A push that throws (the job queue down, the wiki read-only) is logged and POLL still answers.
			try {
				( $this->enqueue )( (int)$row['id'] );
			} catch ( \Throwable $e ) {
				( $this->fault )( (int)$row['id'], $e );
			}
		}
		$out = [ 'ticket' => $row['id'], 'ticket_op' => $row['op'], 'state' => $row['state'] ];
		if ( $row['state'] === TicketStore::DONE ) {
			$out['answer'] = (string)$row['answer'];
			$http = self::refusalStatus( (string)$row['answer'] );
			if ( $http !== null ) {
				$out['http_status'] = $http[0];
				if ( $http[1] !== null ) {
					$out['retry_after'] = $http[1];
				}
			}
		} else {
			$out['poll_after'] = $this->pollAfter;
		}
		return $out;
	}

	/** The ticket's created time (14 digits, UTC) at least the sweep age before now; an unreadable time is never stale. */
	private function stale( string $created ): bool {
		$t = \DateTimeImmutable::createFromFormat( '!YmdHis', $created, new \DateTimeZone( 'UTC' ) );
		if ( preg_match( '/\A[0-9]{14}\z/', $created ) !== 1 || $t === false || $t->format( 'YmdHis' ) !== $created ) {
			return false;
		}
		return ( $this->clock )() - $t->getTimestamp() >= $this->sweepAfter;
	}

	/** One op by its wire word: the dispatch ApiPma makes. */
	public function run( string $op, mixed $prefix, string $account, array $params ): array {
		switch ( $op ) {
			case 'PETITION':
				return $this->petition( $prefix, $account, $params );
			case 'PUSH':
				return $this->push( $prefix, $account, $params );
			case 'RELEASE':
				return $this->release( $prefix, $account, $params );
			case 'HEARTBEAT':
				return $this->heartbeat( $prefix, $account, $params );
			case 'STRUCTURE_TEST':
				return $this->structureTest( $prefix, $account, $params );
			case 'STATUS':
			case 'INQUIRE':
				if ( $prefix !== null ) {
					throw new Refusal( 'custos-unknown-param', "$op takes no prefix" );
				}
				return $op === 'STATUS' ? $this->status( $params, $account ) : $this->inquire( $params, $account );
			case 'POLL':
				if ( $prefix !== null ) {
					throw new Refusal( 'custos-unknown-param', 'POLL takes no prefix' );
				}
				return $this->poll( $params, $account );
		}
		throw new Refusal( 'custos-op', 'not an op of action=pma: ' . self::show( $op ) );
	}

	private function write( string $op, mixed $prefix, string $account, array $params ): array {
		if ( $prefix === null || $prefix === '' ) {
			throw new Refusal( 'custos-prefix', "$op needs a prefix" );
		}
		if ( !is_string( $prefix ) ) {
			throw new Refusal( 'custos-shape', 'the parameter prefix is not one string' );
		}
		if ( strlen( $prefix ) > self::MAX_PREFIX_BYTES ) {
			throw new Refusal( 'custos-prefix', 'the prefix is ' . strlen( $prefix ) . ' bytes, past the bound of '
				. self::MAX_PREFIX_BYTES . ' (the column ct_prefix)' );
		}
		if ( !PageTitles::isBuildablePrefix( $prefix ) ) {
			throw new Refusal( 'custos-prefix', 'not a record prefix: ' . self::show( $prefix ) );
		}
		if ( $account === '' ) {
			throw new Refusal( 'custos-not-agent', "$op needs an account" );
		}
		$p = $this->shape( $op, $params );
		$p['prefix'] = $prefix;
		ksort( $p, SORT_STRING );
		$request = json_encode( $p, JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_THROW_ON_ERROR );
		$id = $this->tickets->create( $op, $account, $prefix, $request );
		( $this->enqueue )( $id );
		return [ 'ticket' => $id, 'state' => TicketStore::QUEUED, 'poll_after' => $this->pollAfter ];
	}

	/** GA1: the parameters' shape, nothing parsed; the parameters, every one a string. */
	private function shape( string $op, array $params ): array {
		if ( array_key_exists( 'account', $params ) ) {
			throw new Refusal( 'custos-account', 'the account is the authenticated one; a parameter account is refused' );
		}
		$allowed = self::PARAMS[$op];
		$out = [];
		foreach ( $params as $k => $v ) {
			$k = (string)$k;
			if ( !in_array( $k, $allowed, true ) ) {
				throw new Refusal( 'custos-unknown-param', "$op takes no parameter " . self::show( $k ) );
			}
			if ( !is_string( $v ) ) {
				throw new Refusal( 'custos-shape', "the parameter $k is not one string" );
			}
			if ( $k === 'records' ) {
				if ( strlen( $v ) > $this->maxRequestBytes ) {
					throw new Refusal( 'custos-too-large', 'records is ' . strlen( $v ) . ' bytes, past the bound of '
						. $this->maxRequestBytes );
				}
				if ( preg_match( '//u', $v ) !== 1 ) {
					throw new Refusal( 'custos-shape', 'records is not UTF-8' );
				}
			} elseif ( $k === 'block' && preg_match( self::BLOCK, $v ) !== 1 ) {
				throw new Refusal( 'custos-shape', 'not a work block\'s name: ' . self::show( $v ) );
			} elseif ( $k === 'prompt_digest' && preg_match( self::PROMPT_DIGEST, $v ) !== 1 ) {
				throw new Refusal( 'custos-shape', 'not a prompt digest (64 lowercase hexadecimal): ' . self::show( $v ) );
			} elseif ( ( $k === 'stated_model' || $k === 'relayed_model' ) && !self::modelShape( $v ) ) {
				throw new Refusal( 'custos-shape', "the parameter $k is not a model name (1 to " . self::MAX_MODEL_BYTES
					. ' bytes of printable UTF-8): ' . self::show( $v ) );
			} elseif ( $k === 'ticket' && preg_match( self::TICKET, $v ) !== 1 ) {
				throw new Refusal( 'custos-no-ticket', 'not a ticket: ' . self::show( $v ) );
			}
			$out[$k] = $v;
		}
		foreach ( self::REQUIRED[$op] ?? [] as $k ) {
			if ( !isset( $out[$k] ) || $out[$k] === '' ) {
				throw new Refusal( 'custos-missing-param', "$op needs the parameter $k" );
			}
		}
		return $out;
	}

	/** A model name's shape: 1 to MAX_MODEL_BYTES bytes, UTF-8, no control character. Its meaning is not read here. */
	private static function modelShape( string $v ): bool {
		return $v !== '' && strlen( $v ) <= self::MAX_MODEL_BYTES && preg_match( '//u', $v ) === 1
			&& preg_match( '/[\x00-\x1f\x7f]/', $v ) !== 1;
	}

	/** A value in a message: at most 64 bytes of it, printable ASCII, the rest escaped. */
	private static function show( string $s ): string {
		$cut = strlen( $s ) > 64 ? substr( $s, 0, 64 ) . '...' : $s;
		return '"' . addcslashes( $cut, "\0..\37\"\\\177..\377" ) . '"';
	}
}
