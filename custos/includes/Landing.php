<?php
/**
 * Landing: the work of one ticket, out of the web request: the job custosLand
 * and the maintenance script Custos:land run it. Plain PHP the harness runs without MediaWiki.
 *
 *   run(id)  the ticket claimed (QUEUED -> IN WORK); its request read through the Calculator; the
 *            account's certificate read (CertificateStore, the table custos_certificate written by
 *            Custos:Certify): none, or one not ACTIVE, answers ADMISSION "the account has no
 *            certificate in force" before the governor is asked, nothing charged; the
 *            governor asked (`governor seat_cost`, then `governor admit` over a MeteredState read
 *            from the seat table, the certificate table, the ticket table and configuration: the
 *            agent's bucket its own account's, the sponsor's bucket the certificate's Sponsor's,
 *            the sponsor's tickets in flight those of every agent bound to that Sponsor); a refusal
 *            answered with nothing written; an admission's charge written to the seat table; the
 *            read of the seats, the `admit` call and the write of its charge one critical section,
 *            under the account's and its Sponsor's seat locks (SeatStore::lock,
 *            `custos-seat:<account>`, taken in the order of their names), released before the
 *            op (never held across the page writes) and after a refusal or a fault; a lock not
 *            obtained within $wgCustosSeatLockSeconds answers ADMISSION with SLOT RETRY-AFTER
 *            plus the governor's jitter and charges nothing; then the op:
 *   PETITION the UWC's ACCESS POLICY asked of the Calculator (ACCESS); the lock granted when free
 *            or expired ($wgCustosLockLease), else LOCK HELD; the grant answered with a fresh nonce
 *            of the execution challenge (`challenge`);
 *   PUSH     the holder checked, and the block: the lock's grant, a request naming another refused
 *            NOT HOLDER; the ACCESS POLICY asked again (ACCESS); the execution challenge (TPS 5.3.19): the account's outstanding nonce taken
 *            (consumed, the next one issued at once and carried by every answer from here on, landed
 *            or refused, as `challenge`), the request's `challenge_response` compared with `pcalc
 *            digest digest_fields` over [TAG, FORM, nonce] (Challenge::verify): a match is EXECUTED
 *            (`execution` in the answer), a mismatch, an absent response or no nonce outstanding is
 *            REASONED and refuses every value the PUSH presents, CHALLENGE, nothing landed;
 *            then, in push() after the challenge, the ACCESS POLICY asked again (ACCESS); the DIGEST
 *            GATE (the three Research Assembly pages' digest,
 *            `zone digest_research_assembly_of`, equal to the badge's); each record checked at
 *            stage PUSH (`record record_check`, under the UWC's BIBLIOGRAPHY SETTING from its
 *            DRAFT UWC page, OFF when the page states none), then `record_form_check` (RESULT,
 *            ASSUMPTION) and `domain_check` (RESULT); a record carrying SUPERSEDES refused (WITHDRAWAL:
 *            the withdrawal is not built); all or nothing, as v1; each identifier the next free one,
 *            formed by `hold allocate_identifiers` (SEQUENCE); the fields Custos owns filled;
 *            `citation_check` against the register as read and the batch before it;
 *            `derivation credit_record` for a RESULT's class; `record_digest`; the filled record
 *            checked again at stage LANDED; the strike screen (`landing strike_screen`, SR3's
 *            mechanical tests over the register with the batch): a batch the strike rule would
 *            strike, or citing a record it would strike, refused RECORD CHECK, each problem
 *            STRIKE OWED (the strike is not written at landing yet); the open register volume rewritten with the batch
 *            appended and the INDEX AND BADGE page written last (PageWriter, one save per page);
 *   RELEASE  the holder's lock freed and the badge's last release advanced;
 *   HEARTBEAT the holder's lock, within its lease, extended to now plus $wgCustosLockLease (its
 *            grant and block kept), else NOT HOLDER;
 *   STRUCTURE_TEST the holder's (within its lease, else NOT HOLDER): the structure test with
 *            register (TPS 5.3.47) and its line, below.
 * The structure test with register: the Research Assembly through the DIGEST GATE, the open register
 * volume (volume 1, as a PUSH), and one call `eom eom_register_test {"tfk", "records"}` over the
 * register whole: the Calculator takes the standing records whose declared form carries a ROLE. The
 * STRUCTURE TEST LINE is composed from its answer alone: "STRUCTURE TEST <date> <result> WITH
 * <identifiers>", the result "structurally regular with register" exactly when the answer's findings
 * are empty, else FINDINGS and each finding as the Calculator wrote it (its JSON), in the answer's
 * order; the identifiers the answer's USED, in its order (prefix, then number), "-" when none. An
 * answer ["REFUSED", reason] is refused STRUCTURE TEST, nothing written. The line stands in the INDEX
 * AND BADGE page's block pma-structure (PageTexts), written through PageWriter, one save, only when
 * what it says beside its date changes (PageTexts::structureSays); a PUSH or a RELEASE that rewrites
 * the badge carries it through. After every PUSH that lands, the job custosStructureTest is pushed for
 * the UWC (the after-push callable, deduplicated per UWC by the job queue); structureJob() is that
 * job's work, admitted through `governor admit` as STRUCTURE TEST JOB (lane 5, refused by pressure
 * alone), with no account, no ticket and no charge.
 * The metered state (charter 8.3, the meter's MeterStore): the pressure level the last budget
 * roll-up kept (`pressure`) and the use over the three horizons (`use`), from which `admit` takes the
 * level in force (`levelStep`); the account's traffic record (`traffic`, the Calculator's text of it,
 * handed back as text), from which `admit` reads the stage. Once at the job's end the record is
 * read again and stepped with the request's end (`governor traffic_step {"end"}`): an admitted op
 * SUCCEEDED, or FAILED when it was refused after admission (NOT HOLDER, CHALLENGE, RECORD CHECK, a
 * PAGE FAULT) or faulted; a refusal by its word with its retry_after; a request refused by its shape
 * before admission (GA1, a 400: NOT READ, REQUEST, RECORDS of the ticket's request) SHAPE; a CACHED
 * ONLY decision not at all (it ends no governed request of an AGENT account); a seat lock not
 * obtained at admission not at all (no decision was made). It is stepped once more with the event
 * ERROR STREAK when the Calculator says TE2 is raised; the record and its stage are written back by
 * a compare and set on the record read (MeterStore::casTraffic), with no lock to wait for: a miss
 * (another job's step landed between the read and the write) is read and stepped again, so the step
 * is written exactly once, never lost to a lock's timeout and never written twice. A refusal's answer carries the decision's HTTP `status`
 * and its `poll_after`: the decision's retry_after (the Calculator's, jitter included), exactly
 * (below); POLL answers it as the HTTP status and Retry-After (ApiPma).
 * Every answer, refusal or not, is written to the ticket for POLL, as one JSON object. A wait the job
 * answers (`poll_after` of LOCK HELD and of PAGE FAULT) is the configured base plus the governor's jitter, `governor jitter {"base",
 * "draw"}`, the draw made as admission's is, so agents refused together do not poll together; PHP
 * adds the two and computes nothing else. An ADMISSION refusal's `poll_after` is the decision's
 * `retry_after` exactly; a refusing decision without a `retry_after` that is a whole number of seconds (0 or more; the governor's contract admits 0 for a slot wait tuned to 0) is a Calculator
 * fault (ANSWER_FORM), never a configured wait, and steps no traffic record (no decision was made).
 *
 * Every answer is made by Refusal::detail, whose table says what each refusal may say: POLL shows it
 * the ticket's account, and a fault's message may hold a database query, a path, the server's name or
 * pcalc's stderr (RESTRICTED). INTEGRITY HALT says "digest mismatch"; CALCULATOR FAULT the fault's
 * name from a closed set and the call's family and function (an UNSAFE RESIDENCE the check that failed,
 * never the path); PAGE FAULT the page's class and the fault's name; a fault of no kind named here
 * `{"refused": "JOB FAULT", "class": <the exception's short class name>}`. The class and message of
 * every fault go to the error channel, the debug log `Custos` (ApiPma's) the Operator reads on the
 * host, and every fault but a PAGE FAULT is rethrown so the job's setLastError has it.
 *
 * Reading. PHP parses no payload: every text read (the request, the records, the lock, the badge,
 * the register, the Research Assembly) goes through `pcalc canonical canonical_json` as the
 * member "value" of a request built by concatenation, so the Calculator is the one parser (a text
 * that is not one JSON value, or that would add a member, is refused by it), and PHP decodes only
 * the Calculator's canonical answer, and only where that value written again is the canonical text
 * byte for byte, or the Calculator's canonical text of it is (else NOT READ: a number the landing
 * cannot hold exactly). A record's class and identifier are read from
 * `record record_view` (view HOLD); its fields are never read by PHP, save that the presence of the
 * member SUPERSEDES is tested (its value never read) to refuse it. Custos's own fields are
 * written as members, and the Calculator's canonical_json writes the register's text.
 *
 * Never: a write before every check passed; a record landed whose `record_check` at PUSH and at
 * LANDED is not OK; a record landed that the strike screen holds; a write on a refusal; a landing past a DIGEST MISMATCH (the ticket answered
 * INTEGRITY HALT, the exception rethrown so the job halts).
 */

namespace Custos;

use JsonException;
use MediaWiki\Config\Config;
use RuntimeException;
use stdClass;
use Throwable;

final class Landing {
	public const LEASE = 3600;
	/** The seconds the admission waits for the account's seat lock ($wgCustosSeatLockSeconds). */
	public const SEAT_LOCK_SECONDS = 10;
	/**
	 * SLOT RETRY-AFTER, wall-clock seconds: Principia/Parameters.lean's slotRetryAfter (the harness
	 * reads it there). The wait a seat lock not obtained answers, before the governor's jitter.
	 */
	public const SLOT_RETRY_AFTER = 5;
	/** The detail of the ADMISSION refusal of an account with no certificate in force. */
	public const NO_CERTIFICATE = 'the account has no certificate in force';
	/** The classes this unit lands; the rest are refused (the later briefs' corners). */
	public const LANDS = [ 'RESULT', 'ASSUMPTION', 'ENTRY_STATUS' ];
	/** The DRAFT UWC page's block naming the UWC's BIBLIOGRAPHY SETTING, its words, and the fleet default. */
	public const SETTING = 'setting';
	public const SETTINGS = [ 'OFF', 'ON', 'CLOSED' ];
	public const SETTING_DEFAULT = 'OFF';
	/** The DRAFT UWC page's block naming the UWC's ACCESS POLICY (TPS 5.16.1), its words, and the reading when it states none. */
	public const POLICY = 'policy';
	public const POLICIES = [ 'OPEN', 'CLOSED' ];
	public const POLICY_DEFAULT = 'OPEN';
	/** The ACCESS LIST page's block: a JSON list of account names. */
	public const ACCESS = 'access';
	/** The bound of the identifier range `hold allocate_identifiers` draws a pushed record's identifier from. */
	public const ID_HIGH = 999999999;
	/** The debug log channel of Custos (ApiPma's too): the Operator reads a fault's class and message there. */
	public const LOG = 'Custos';
	/** The detail of a text whose value the landing cannot hold as the Calculator read it. */
	public const HOLD = 'a number the landing cannot hold exactly';
	/** A request's endings as `governor traffic_step` reads them. */
	public const ENDINGS = [ 'SWITCH', 'TRAFFIC', 'PRESSURE', 'RATE', 'SLOTS', 'SHAPE', 'FAILED', 'SUCCEEDED' ];
	/**
	 * The reads a traffic step makes at most: each miss of its compare and set is another step of the
	 * account written in between, so the bound is reached only by that many steps landing inside one.
	 */
	public const STEP_TRIES = 100;
	/** The refusals of a request's shape before admission (GA1, HTTP 400), stepped SHAPE. */
	public const SHAPE_WORDS = [ 'NOT READ', 'REQUEST', 'RECORDS' ];
	/** A NORMAL account with no history: the traffic record of an account the meter has not seen. */
	public const FRESH_TRAFFIC = '{"backoff_until":0,"breaker_until":0,"flood_inquire":null,"flood_release":null,"last_event":0,'
		. '"penalized_times":[],"retry_after":0,"stage":"NORMAL","streak":0,"te3_times":[],"throttled_times":[],"trial_pending":false}';
	private const JSON = JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_PRESERVE_ZERO_FRACTION | JSON_THROW_ON_ERROR;

	/** @var callable():int */
	private $clock;
	/** @var callable():array */
	private $draw;
	/** @var callable(int, Throwable):void */
	private $fault;
	private array $conf;
	/** @var array<string, int> the lane number of each governed kind, asked once */
	private array $lanes = [];
	/** The class of the page being read or written (PageClass's word), for a PAGE FAULT's answer; null: none. */
	private ?string $page = null;
	/** The execution challenge's nonces (custos_nonce). */
	private NonceStore $nonces;
	/** The members every answer of this run carries once a PUSH consumed its nonce: execution and the next challenge. */
	private ?array $after = null;
	/** The admission's decision, to be stepped into the traffic record at the job's end; null: none made. */
	private ?array $end = null;
	/** The governor's meter: the budget roll-up and the traffic records. */
	private MeterStore $meter;
	/** @var callable(string):void pushes the structure-test job for a UWC after a PUSH lands; null: none */
	private $afterPush;

	/**
	 * @param array $conf lease (seconds), poll_after (seconds), seat_lock_seconds, agent_stop,
	 *   governor_off (bool), suspended (account names), tps, d_is (the fields Custos fills), digest
	 *   (CustosBuild's)
	 * @param callable|null $clock the server time, whole seconds; null: time()
	 * @param callable|null $draw the jitter's draw [num, den]; null: random_int over 10^6
	 * @param callable|null $fault the error channel: called with the ticket's number and the exception
	 *   of every fault (INTEGRITY HALT, CALCULATOR FAULT, PAGE FAULT, JOB FAULT), whose message the
	 *   ticket's answer leaves out; null: MediaWiki's debug log `Custos` (wfDebugLog) where it exists,
	 *   else nothing
	 * @param NonceStore|null $nonces the execution challenge's nonces; null: this object's memory
	 * @param callable|null $afterPush called with the UWC's prefix after a PUSH lands (the job
	 *   custosStructureTest pushed, deduplicated); one that throws goes to the error channel and the
	 *   landing stands; null: nothing pushed
	 */
	public function __construct(
		private Calculator $calc,
		private PageStore $store,
		private PageTitles $titles,
		private TicketStore $tickets,
		private SeatStore $seats,
		private CertificateStore $certs,
		array $conf,
		?callable $clock = null,
		?callable $draw = null,
		?callable $fault = null,
		?NonceStore $nonces = null,
		?MeterStore $meter = null,
		?callable $afterPush = null
	) {
		$this->afterPush = $afterPush;
		$this->meter = $meter ?? new MemMeterStore();
		// No store named: the challenge is checked all the same, over nonces this object issued.
		$this->nonces = $nonces ?? new MemNonceStore();
		$this->conf = $conf + [ 'lease' => self::LEASE, 'poll_after' => Ops::POLL_AFTER, 'seat_lock_seconds' => self::SEAT_LOCK_SECONDS, 'agent_stop' => false,
			'governor_off' => false, 'suspended' => [], 'tps' => '', 'd_is' => '', 'digest' => '' ];
		$this->clock = $clock ?? static fn (): int => time();
		$this->draw = $draw ?? static fn (): array => [ random_int( 0, 999999 ), 1000000 ];
		$this->fault = $fault ?? static function ( int $id, Throwable $e ): void {
			if ( function_exists( 'wfDebugLog' ) ) {
				wfDebugLog( self::LOG, "land ticket $id: " . get_class( $e ) . ': ' . $e->getMessage() );
			}
		};
	}

	/** The configuration's members, read from the wiki's settings. */
	public static function confFrom( Config $config ): array {
		$build = $config->get( 'CustosBuild' );
		return [
			'lease' => (int)$config->get( 'CustosLockLease' ),
			'poll_after' => (int)$config->get( 'CustosPollAfter' ),
			'seat_lock_seconds' => (int)$config->get( 'CustosSeatLockSeconds' ),
			'agent_stop' => (bool)$config->get( 'CustosAgentStop' ),
			'governor_off' => (bool)$config->get( 'CustosGovernorOff' ),
			'suspended' => array_values( array_map( 'strval', (array)$config->get( 'CustosSuspended' ) ) ),
			'tps' => (string)$config->get( 'CustosTps' ),
			'd_is' => (string)$config->get( 'CustosDIs' ),
			'digest' => is_array( $build ) ? (string)( $build['digest'] ?? '' ) : '',
		];
	}

	/**
	 * Run the ticket $id: its answer, as written to the ticket. A ticket that is not QUEUED is not
	 * claimed and nothing is written: ["refused" => "NOT QUEUED"].
	 *
	 * @throws DigestMismatch after the ticket is answered INTEGRITY HALT
	 * @throws UnsafeResidence|CalculatorFault after the ticket is answered CALCULATOR FAULT
	 * @throws Throwable any other, after the ticket is answered JOB FAULT with its short class name
	 * Each after the error channel has its class and message, which the answer never carries.
	 */
	public function run( int $id ): array {
		$row = $this->tickets->claim( $id );
		if ( $row === null ) {
			return [ 'refused' => 'NOT QUEUED', 'detail' => "the ticket $id is not QUEUED; nothing was run" ];
		}
		// PHP writes a float as its shortest text only under serialize_precision -1 (php.ini may say 17):
		// the job sets it, and refuses rather than run under another, so every text it writes is the one read,
		// the ticket's answer included. ini_set in disable_functions is absent in PHP 8 (calling it would raise
		// an Error, and at the restore replace the fault in flight): then the setting must already be -1.
		$precision = (string)ini_get( 'serialize_precision' );
		$this->after = null;
		$this->end = null;
		try {
			try {
				if ( function_exists( 'ini_set' ) ) {
					ini_set( 'serialize_precision', '-1' );
				}
				if ( ini_get( 'serialize_precision' ) !== '-1' ) {
					throw new LandRefused( 'CONFIGURATION', 'PHP\'s serialize_precision is not -1; nothing is landed' );
				}
				$answer = $this->attempt( $row ) + ( $this->after ?? [] );
				$outcome = 'SUCCEEDED';
			} catch ( LandRefused $e ) {
				$answer = Refusal::detail( $e ) + ( $this->after ?? [] );
				$outcome = 'FAILED';
			} catch ( Throwable $e ) {
				// A fault (the digest, the residence, the Calculator's protocol, the database, the store, PHP
				// itself): the ticket is answered, never left IN WORK and counted in flight for good, and the
				// job fails with it. The answer reaches the ticket's account by POLL, so Refusal::detail says a
				// fixed word and a detail from its closed set, nothing of the message, which may hold a query,
				// a path, the server's name or pcalc's stderr (RESTRICTED); the class and message go to the
				// error channel first (it never throws), and the rethrown exception reaches the job.
				$this->report( $id, $e );
				try {
					// An admitted op that faulted failed: stepped FAILED, a fault of the step itself reported.
					$this->stepEnd( 'FAILED' );
				} catch ( Throwable $f ) {
					$this->report( $id, $f );
				}
				$this->answer( $id, Refusal::detail( $e ) + ( $this->after ?? [] ) );
				throw $e;
			}
			try {
				$this->stepEnd( $outcome );
			} catch ( Throwable $f ) {
				// The op's answer stands (its pages may be written); the step's fault goes to the error
				// channel and reaches the job.
				$this->report( $id, $f );
				$this->answer( $id, $answer );
				throw $f;
			}
			$this->answer( $id, $answer );
			return $answer;
		} finally {
			if ( function_exists( 'ini_set' ) ) {
				ini_set( 'serialize_precision', $precision );
			}
		}
	}

	/**
	 * The ending `governor traffic_step` is stepped with, of a decision and the op's outcome
	 * (SUCCEEDED or FAILED): an admitted op by its outcome; a refusal by its word (FAILED when the
	 * word is none of ENDINGS); null for CACHED ONLY and any other decision, which ends no governed
	 * request of an AGENT account (Principia.Governor.Traffic's `Ending` names none) and steps nothing.
	 */
	public static function endingOf( mixed $decision, string $outcome ): ?string {
		if ( !is_array( $decision ) ) {
			return 'FAILED';
		}
		switch ( $decision['decision'] ?? null ) {
			case 'ADMITTED':
				return $outcome === 'SUCCEEDED' ? 'SUCCEEDED' : 'FAILED';
			case 'REFUSED':
				$w = $decision['refusal'] ?? null;
				return is_string( $w ) && in_array( $w, self::ENDINGS, true ) ? $w : 'FAILED';
		}
		return null;
	}

	/**
	 * The request's end stepped into the account's traffic record, once, at the job's end (stepTraffic,
	 * a compare and set: no lock taken, none to time out). SHAPE for a request refused by its shape
	 * before admission; nothing when no decision was made otherwise (a seat lock not obtained at
	 * admission, a fault before it) or the decision ends no governed request (endingOf).
	 */
	private function stepEnd( string $outcome ): void {
		$end = $this->end;
		$this->end = null;
		if ( $end === null ) {
			return;
		}
		$ending = $end['ending'] ?? self::endingOf( $end['decision'], $outcome );
		if ( $ending === null ) {
			return;
		}
		$this->stepTraffic( $end['account'], $end['op'], $ending, $end['retry_after'], ( $this->clock )() );
	}

	/** The exception's class name without its namespace, and without the file an anonymous class's name carries. */
	public static function faultClass( Throwable $e ): string {
		return Refusal::faultClass( $e );
	}

	/** The fault to the error channel: it fails nothing, the ticket still answered and the exception still rethrown. */
	private function report( int $id, Throwable $e ): void {
		try {
			( $this->fault )( $id, $e );
		} catch ( Throwable ) {
			// The channel is down too: the ticket's answer and the rethrown exception stand.
		}
	}

	private function answer( int $id, array $answer ): void {
		$this->tickets->answer( $id, json_encode( $answer, self::JSON ) );
	}

	/**
	 * The op, a PAGE FAULT made a refusal with its jittered wait: the jitter's call runs inside run()'s
	 * try, so its own refusal or fault is answered as any other.
	 */
	private function attempt( array $row ): array {
		$this->page = null;
		try {
			return $this->op( $row );
		} catch ( PageFault $e ) {
			// The page's class and the fault's name answer it; its message, a title's bytes or a
			// payload's, goes to the error channel.
			$this->report( (int)$row['id'], $e );
			$d = Refusal::detail( $e, $this->page );
			throw new LandRefused( $d['refused'], $d['detail'], [ 'poll_after' => $this->wait() ] );
		}
	}

	/**
	 * A wait the job answers: $base (null: the configured poll_after) plus `governor jitter {"base",
	 * "draw"}` over a draw made as admission's (random_int by default). The Calculator's answer must
	 * be a count.
	 */
	private function wait( ?int $base = null ): int {
		$base ??= (int)$this->conf['poll_after'];
		$j = $this->ask( 'governor', 'jitter', [ 'base' => $base, 'draw' => ( $this->draw )() ], 'the wait\'s jitter' );
		if ( !is_int( $j ) || $j < 0 ) {
			throw new CalculatorFault( 'the governor\'s jitter is not a count: ' . self::cut( self::json( $j ) ),
				CalculatorFault::ANSWER_FORM, 'governor', 'jitter' );
		}
		return $base + $j;
	}

	private function op( array $row ): array {
		try {
			[ $req, $block, $records ] = $this->shape( $row );
		} catch ( LandRefused $e ) {
			// GA1: a request refused by its shape (a 400) is stepped SHAPE at the job's end.
			if ( in_array( $e->word, self::SHAPE_WORDS, true ) ) {
				$this->end = [ 'account' => (string)$row['account'], 'op' => (string)$row['op'], 'decision' => null, 'ending' => 'SHAPE',
					'retry_after' => null ];
			}
			throw $e;
		}
		$now = ( $this->clock )();
		$this->admit( $row, count( $records ), $now );
		if ( $row['op'] === 'PUSH' ) {
			// A PUSH lands under the block the lock was granted for, never one the request names.
			$block = $this->granted( $row, $req, $now );
			$this->challenge( $row, $req, $now );
		}
		$w = new PageWriter( $this->store, $this->titles );
		$this->page = PageClass::INDEX_AND_BADGE;
		$w->begin( (string)$row['prefix'], $block );
		switch ( $row['op'] ) {
			case 'PETITION':
				return $this->petition( $w, $row, $block, $now );
			case 'PUSH':
				return $this->push( $w, $row, $block, $records, $now );
			case 'RELEASE':
				return $this->release( $w, $row, $now );
			case 'HEARTBEAT':
				return $this->heartbeat( $w, $row, $now );
			case 'STRUCTURE_TEST':
				return $this->structureOp( $w, $row, $now );
		}
		throw new LandRefused( 'REQUEST', 'not an op the job runs: ' . PageTitles::show( (string)$row['op'] ) );
	}

	/**
	 * GA1, the request's shape: the ticket's request read (an object), its block, and a PUSH's
	 * records read (a list of one record or more). @return array{0: stdClass, 1: string, 2: array}
	 */
	private function shape( array $row ): array {
		$req = $this->read( (string)$row['request'], 'the ticket\'s request' );
		if ( !$req instanceof stdClass ) {
			throw new LandRefused( 'REQUEST', 'the ticket\'s request is not an object' );
		}
		$block = isset( $req->block ) && is_string( $req->block ) ? $req->block : 't' . $row['id'];
		$records = [];
		if ( $row['op'] === 'PUSH' ) {
			if ( !isset( $req->records ) || !is_string( $req->records ) ) {
				throw new LandRefused( 'REQUEST', 'a PUSH carries records' );
			}
			$records = $this->read( $req->records, 'the records' );
			if ( !is_array( $records ) || $records === [] ) {
				throw new LandRefused( 'RECORDS', 'records is a list of one record or more' );
			}
		}
		return [ $req, $block, $records ];
	}

	// ---- admission ---------------------------------------------------------------------------

	/**
	 * The governor's decision over the MeteredState read now; a refusal throws, an admission charges.
	 * The read of the seats, the decision and the charge's write run under the account's seat lock,
	 * released on every way out; a lock not obtained refuses ADMISSION with nothing charged.
	 */
	private function admit( array $row, int $records, int $now ): void {
		$op = (string)$row['op'];
		$account = (string)$row['account'];
		// The certificate first: an agent with none in force is refused before the governor is asked,
		// and nothing is charged.
		$cert = $this->certs->get( $account );
		if ( $cert === null || ( $cert['state'] ?? null ) !== CertificateStore::ACTIVE || !is_string( $cert['sponsor'] ?? null )
			|| $cert['sponsor'] === '' ) {
			throw new LandRefused( 'ADMISSION', self::NO_CERTIFICATE );
		}
		$sponsor = $cert['sponsor'];
		$seats = $this->ask( 'governor', 'seat_cost', [ 'kind' => $op, 'records' => $records, 'rows' => 0 ], 'the seats' );
		$within = max( 0, (int)$this->conf['seat_lock_seconds'] );
		// The agent's seat lock and its Sponsor's, taken in the order of their names (two admissions
		// never wait on each other in a cycle), so two agents of one Sponsor never both spend its last seat.
		$locks = array_values( array_unique( [ $account, $sponsor ] ) );
		sort( $locks, SORT_STRING );
		$held = [];
		foreach ( $locks as $name ) {
			if ( !$this->seats->lock( $name, $within ) ) {
				$this->unlockAll( $held, (int)$row['id'] );
				$whose = $name === $account ? "the account's" : "the account's sponsor's";
				throw new LandRefused( 'ADMISSION', "$whose seat lock was not obtained within $within s; nothing was charged",
					[ 'poll_after' => $this->wait( self::SLOT_RETRY_AFTER ) ] );
			}
			$held[] = $name;
		}
		try {
			$this->decide( $row, $op, $account, $sponsor, $seats, $now );
		} catch ( Throwable $e ) {
			// An unlock that throws while the critical section's own exception is in flight goes to the
			// error channel; the original exception is the one rethrown.
			$this->unlockAll( $held, (int)$row['id'] );
			throw $e;
		}
		$this->unlockAll( $held, (int)$row['id'], true );
	}

	/**
	 * Release the seat locks $held, the last taken first. With $raise, the first unlock that throws is
	 * rethrown after the rest are released; without, each goes to the error channel.
	 */
	private function unlockAll( array $held, int $id, bool $raise = false ): void {
		$first = null;
		foreach ( array_reverse( $held ) as $name ) {
			try {
				$this->seats->unlock( $name );
			} catch ( Throwable $u ) {
				if ( $raise && $first === null ) {
					$first = $u;
				} else {
					$this->report( $id, $u );
				}
			}
		}
		if ( $first !== null ) {
			throw $first;
		}
	}

	/**
	 * The admission's critical section, under the agent's and its Sponsor's seat locks: read, decide,
	 * charge. The Sponsor's bucket is its own account's; its tickets in flight are those of every
	 * agent its certificates bind to it.
	 */
	private function decide( array $row, string $op, string $account, string $sponsor, mixed $seats, int $now ): void {
		$bound = array_fill_keys( $this->certs->agentsOf( $sponsor ), true );
		$bound[$account] = true;
		[ $agentIn, $sponsorIn, $finishing, $starting ] = $this->inFlight( $row['id'], $account, $bound );
		$state = [
			'now' => $now,
			'agent_stop' => (bool)$this->conf['agent_stop'],
			'suspended' => in_array( $account, (array)$this->conf['suspended'], true ),
			'governor_off' => (bool)$this->conf['governor_off'],
			'agent_seats' => $this->seats->get( $account, SeatStore::AGENT ),
			'sponsor_seats' => $this->seats->get( $sponsor, SeatStore::SPONSOR ),
			'agent_in_flight' => $agentIn,
			'sponsor_in_flight' => $sponsorIn,
			'finishing_in_flight' => $finishing,
			'starting_in_flight' => $starting,
		];
		$budget = $this->meter->budget();
		$state['pressure'] = (string)$budget['kept'];
		$state['use'] = $budget['use'];
		$traffic = $this->meter->traffic( $account );
		$stateJson = self::json( $state );
		if ( $traffic !== null ) {
			// The record as the Calculator answered it, handed back as text: PHP reads no member of it.
			$stateJson = substr( $stateJson, 0, -1 ) . ',"traffic":' . $traffic['record'] . '}';
		}
		$draw = ( $this->draw )();
		$d = $this->askText( 'governor', 'admit', '{"state":' . $stateJson . ',"request":'
			. self::json( [ 'kind' => $op, 'seats' => $seats, 'draw' => $draw ] ) . '}', 'the admission' );
		$admitted = is_array( $d ) && ( $d['decision'] ?? null ) === 'ADMITTED';
		if ( !$admitted ) {
			if ( !is_array( $d ) || !is_int( $d['retry_after'] ?? null ) || $d['retry_after'] < 0 ) {
				throw new CalculatorFault( 'the governor\'s refusal carries no count as retry_after: ' . self::cut( self::json( $d ) ),
					CalculatorFault::ANSWER_FORM, 'governor', 'admit' );
			}
			$after = $d['retry_after'];
			// Stepped once at the job's end (stepEnd) by the refusal's word, with the Retry-After POLL
			// sends: the decision's, exactly.
			$this->end = [ 'account' => $account, 'op' => $op, 'decision' => $d, 'retry_after' => $after ];
			$extra = [ 'decision' => $d, 'poll_after' => $after ];
			if ( is_int( $d['status'] ?? null ) ) {
				$extra['status'] = $d['status'];
			}
			throw new LandRefused( 'ADMISSION', 'the governor did not admit the request: ' . ( is_array( $d ) ? (string)( $d['decision'] ?? '' ) : '' ),
				$extra );
		}
		// Stepped once at the job's end (stepEnd) by the op's outcome, with no Retry-After.
		$this->end = [ 'account' => $account, 'op' => $op, 'decision' => $d, 'retry_after' => null ];
		// The charge is applied whole or the job faults: never skipped. It is null only where the
		// governor charges nothing (`admit`: the governor off, or a lane outside 2 to 4).
		$charge = array_key_exists( 'charge', $d ) ? $d['charge'] : false;
		if ( $charge === null && ( $this->conf['governor_off'] || !in_array( $this->lane( $op ), [ 2, 3, 4 ], true ) ) ) {
			return;
		}
		if ( !self::isCharge( $charge ) ) {
			throw new CalculatorFault( 'the governor admitted the request with a charge not of the form '
				. '{"agent": [level, since], "sponsor": [level, since]}: ' . self::cut( self::json( $charge ) ),
				CalculatorFault::ANSWER_FORM, 'governor', 'admit' );
		}
		// Both buckets in one write: a fault between the agent's row and the sponsor's leaves neither.
		$this->seats->charge( $account, $charge['agent'], $sponsor, $charge['sponsor'] );
	}

	/**
	 * The tickets IN WORK but $skip: the account's, those of the accounts $bound (keys: the agents a
	 * Sponsor's certificates bind to it), lane 2's and lanes 3 and 4's together.
	 * @return array{0: int, 1: int, 2: int, 3: int}
	 */
	private function inFlight( mixed $skip, string $account, array $bound = [] ): array {
		$agentIn = $sponsorIn = $finishing = $starting = 0;
		foreach ( $this->tickets->inWork() as $t ) {
			if ( $t['id'] === $skip ) {
				continue;
			}
			if ( $account !== '' && $t['account'] === $account ) {
				$agentIn++;
			}
			if ( isset( $bound[(string)$t['account']] ) ) {
				$sponsorIn++;
			}
			$lane = $this->lane( (string)$t['op'] );
			if ( $lane === 2 ) {
				$finishing++;
			} elseif ( $lane === 3 || $lane === 4 ) {
				$starting++;
			}
		}
		return [ $agentIn, $sponsorIn, $finishing, $starting ];
	}

	/**
	 * The account's traffic record stepped with the request's end (`governor traffic_step`), and with
	 * ERROR STREAK when the Calculator raises TE2; the record written back with its stage by a compare
	 * and set on the text read (casTraffic). A miss, another step written between the read and the
	 * write, is read and stepped again, at most STEP_TRIES reads: the step is written once, on the
	 * record as it then stands, and never twice. A step that leaves the record's text as it was writes
	 * nothing: the store only compares it with the record read, and a miss is read and stepped
	 * again like any other. The first record is the Calculator's NORMAL account with no history, stepped from the
	 * empty record, and made only where none is.
	 */
	private function stepTraffic( string $account, string $op, string $ending, ?int $retryAfter, int $now ): void {
		$end = self::json( [ 'kind' => $op, 'ending' => in_array( $ending, self::ENDINGS, true ) ? $ending : 'FAILED', 'retry_after' => $retryAfter ] );
		for ( $try = 0; $try < self::STEP_TRIES; $try++ ) {
			$was = $this->meter->traffic( $account )['record'] ?? null;
			$a = $this->askText( 'governor', 'traffic_step', '{"traffic":' . ( $was ?? self::FRESH_TRAFFIC ) . ',"now":' . $now . ',"end":' . $end . '}',
				'the traffic record' );
			if ( is_array( $a ) && ( $a['raises'] ?? false ) === true && is_array( $a['traffic'] ?? null ) ) {
				$a = $this->ask( 'governor', 'traffic_step', [ 'traffic' => $a['traffic'], 'now' => $now, 'event' => 'ERROR STREAK' ], 'the traffic record' );
			}
			if ( !is_array( $a ) || !is_array( $a['traffic'] ?? null ) || !is_string( $a['traffic']['stage'] ?? null ) ) {
				throw new CalculatorFault( 'the traffic step is not of the form {"raises", "traffic"}', CalculatorFault::ANSWER_FORM, 'governor', 'traffic_step' );
			}
			$record = self::json( $a['traffic'] );
			if ( $this->meter->casTraffic( $account, $was, $record, $a['traffic']['stage'], $now ) ) {
				return;
			}
		}
		throw new RuntimeException( 'the traffic record was overtaken at each of ' . self::STEP_TRIES . ' reads; the step was not written' );
	}

	/** A charge as `admit` answers one: exactly the agent's and the sponsor's buckets, each [level, since] of two counts. */
	private static function isCharge( mixed $c ): bool {
		if ( !is_array( $c ) || count( $c ) !== 2 ) {
			return false;
		}
		foreach ( [ 'agent', 'sponsor' ] as $k ) {
			$b = $c[$k] ?? null;
			if ( !is_array( $b ) || !array_is_list( $b ) || count( $b ) !== 2 || !is_int( $b[0] ) || !is_int( $b[1] ) || $b[0] < 0 || $b[1] < 0 ) {
				return false;
			}
		}
		return true;
	}

	private function lane( string $op ): int {
		if ( !isset( $this->lanes[$op] ) ) {
			$l = $this->ask( 'governor', 'lane', [ 'kind' => $op ], 'the lane' );
			$this->lanes[$op] = is_array( $l ) && is_int( $l['number'] ?? null ) ? $l['number'] : 0;
		}
		return $this->lanes[$op];
	}

	// ---- the ops -----------------------------------------------------------------------------

	private function petition( PageWriter $w, array $row, string $block, int $now ): array {
		$prefix = (string)$row['prefix'];
		$account = (string)$row['account'];
		[ $badgeText ] = $this->live( $w, $prefix );
		// The petition row is the Coworker's append to the collaboration page (TPS 5.8.8).
		$this->access( $w, $prefix, $account, 'COWORKER', 'COLLABORATION', 'APPEND' );
		$lock = $this->lock( $w, $prefix );
		$stamp = self::stamp( $now );
		$free = $lock->holder === null || strcmp( (string)$lock->expires_at, $stamp ) <= 0;
		if ( !$free && $lock->holder !== $account ) {
			throw new LandRefused( 'LOCK HELD', 'the lock of ' . $prefix . ' is held until ' . $lock->expires_at,
				[ 'poll_after' => $this->wait() ] );
		}
		$expires = self::stamp( $now + (int)$this->conf['lease'] );
		$this->page = PageClass::LOCK_PAGE;
		$w->put( $this->titles->lock( $prefix ), PageTexts::lock( $prefix, $account, $stamp, $expires, $block, $this->lockText( ... ) ) );
		$this->page = PageClass::INDEX_AND_BADGE;
		$w->put( $this->titles->index( $prefix ), $badgeText );
		$this->page = null;
		$w->commit();
		return [ 'grant' => $stamp, 'expires' => $expires, 'block' => $block, 'challenge' => $this->issue( $account, $prefix, $now ) ];
	}

	// ---- the execution challenge (TPS 5.3.19) ------------------------------------------------

	/** A fresh nonce for $account on $prefix: 128 bits of random_bytes, 32 lowercase hexadecimal; now its only outstanding one. */
	private function issue( string $account, string $prefix, int $now ): string {
		$nonce = bin2hex( random_bytes( 16 ) );
		$this->nonces->put( $account, $prefix, $nonce, $now );
		return $nonce;
	}

	/**
	 * The PUSH's challenge: the outstanding nonce taken and the next issued (every answer of this run
	 * carries it), the response checked through the Calculator. EXECUTED goes on; REASONED refuses the
	 * PUSH whole, CHALLENGE, before any record is read for landing.
	 */
	private function challenge( array $row, stdClass $req, int $now ): void {
		$prefix = (string)$row['prefix'];
		$account = (string)$row['account'];
		$nonce = $this->nonces->take( $account, $prefix );
		$this->after = [ 'execution' => 'REASONED', 'challenge' => $this->issue( $account, $prefix, $now ) ];
		$response = property_exists( $req, 'challenge_response' ) ? $req->challenge_response : null;
		$why = null;
		if ( $nonce === null ) {
			$why = "no challenge is outstanding for the account on $prefix (one is answered at PETITION and on every PUSH)";
		} elseif ( !Challenge::nonceOk( $nonce ) ) {
			$why = Challenge::BAD_NONCE;
		} elseif ( $response === null || $response === '' ) {
			$why = 'the challenge response is missing';
		} elseif ( !Challenge::responseOk( $response ) ) {
			$why = 'the challenge response is not 64 lowercase hexadecimal characters';
		} elseif ( !Challenge::verify( $this->calc, $nonce, $response ) ) {
			$why = 'the challenge response is wrong';
		}
		if ( $why !== null ) {
			throw new LandRefused( 'CHALLENGE', "$why; attested REASONED: every value this PUSH presents is refused, nothing is landed" );
		}
		$this->after['execution'] = 'EXECUTED';
	}

	private function release( PageWriter $w, array $row, int $now ): array {
		$prefix = (string)$row['prefix'];
		[ $badgeText, $badge, $volume ] = $this->live( $w, $prefix );
		$lock = $this->lock( $w, $prefix );
		if ( $lock->holder !== (string)$row['account'] ) {
			throw new LandRefused( 'NOT HOLDER', 'the account does not hold the lock of ' . $prefix );
		}
		$this->page = PageClass::INDEX_AND_BADGE;
		$structure = PageTexts::readStructure( $badgeText );
		$stamp = self::stamp( $now );
		$this->page = PageClass::LOCK_PAGE;
		$w->put( $this->titles->lock( $prefix ), PageTexts::lock( $prefix, null, null, null, null ) );
		$this->page = PageClass::INDEX_AND_BADGE;
		$w->put( $this->titles->index( $prefix ), PageTexts::badge( $prefix, [
			'last_push' => $badge->last_push, 'last_release' => $stamp,
			'calculator_version' => $badge->calculator_version, 'calculator_digest' => $badge->calculator_digest,
			'record_count' => $badge->record_count, 'research_assembly' => $badge->research_assembly,
		], false, $volume, $structure ) );
		$this->page = null;
		$w->commit();
		return [ 'released' => $stamp, 'block' => $lock->block ];
	}

	/** HEARTBEAT: the holder's lock, within its lease, extended by the lease from now; its grant and block kept. */
	private function heartbeat( PageWriter $w, array $row, int $now ): array {
		$prefix = (string)$row['prefix'];
		[ $badgeText ] = $this->live( $w, $prefix );
		$lock = $this->lock( $w, $prefix );
		$stamp = self::stamp( $now );
		if ( $lock->holder !== (string)$row['account'] || strcmp( (string)$lock->expires_at, $stamp ) <= 0 ) {
			throw new LandRefused( 'NOT HOLDER', 'a HEARTBEAT is the lock holder\'s, within its lease' );
		}
		$expires = self::stamp( $now + (int)$this->conf['lease'] );
		$this->page = PageClass::LOCK_PAGE;
		$w->put( $this->titles->lock( $prefix ), PageTexts::lock( $prefix, (string)$lock->holder, (string)$lock->granted_at, $expires, (string)$lock->block,
			$this->lockText( ... ) ) );
		// The badge last, unchanged: every landing's saves end with it (PageWriter).
		$this->page = PageClass::INDEX_AND_BADGE;
		$w->put( $this->titles->index( $prefix ), $badgeText );
		$this->page = null;
		$w->commit();
		return [ 'heartbeat' => $stamp, 'expires' => $expires, 'block' => $lock->block ];
	}

	/**
	 * The block a PUSH lands under: the one the lock of the ticket's UWC was granted for, read from
	 * the lock page. The ticket's account must hold the lock within its lease, and a request that
	 * names a block must name that one; else NOT HOLDER. The lock is not written by a PUSH, so it
	 * is read from the store before the landing opens under the granted block.
	 */
	private function granted( array $row, stdClass $req, int $now ): string {
		$prefix = (string)$row['prefix'];
		$this->page = PageClass::LOCK_PAGE;
		$lock = $this->lockOf( $this->store->get( $this->titles->lock( $prefix ) ), $prefix );
		if ( $lock->holder !== (string)$row['account'] || strcmp( (string)$lock->expires_at, self::stamp( $now ) ) <= 0 ) {
			throw new LandRefused( 'NOT HOLDER', 'a PUSH is the lock holder\'s, within its lease' );
		}
		if ( !is_string( $lock->block ?? null ) ) {
			throw new LandRefused( 'UWC', "the lock of $prefix names no block" );
		}
		if ( property_exists( $req, 'block' ) && $req->block !== $lock->block ) {
			throw new LandRefused( 'NOT HOLDER', "the lock of $prefix was granted for the block {$lock->block}, not the block the PUSH names; nothing is landed" );
		}
		return $lock->block;
	}

	private function push( PageWriter $w, array $row, string $block, array $records, int $now ): array {
		$prefix = (string)$row['prefix'];
		$account = (string)$row['account'];
		[ $badgeText, $badge, $volume ] = $this->live( $w, $prefix );
		$structure = PageTexts::readStructure( $badgeText );
		// The policy governs future writes (TPS 5.16.7): a holder taken off the list, or a UWC closed, lands nothing more.
		$this->access( $w, $prefix, $account, 'HOLDER', 'REGISTER OPEN', 'WRITE' );
		$stamp = self::stamp( $now );
		foreach ( [ 'tps', 'd_is', 'digest' ] as $k ) {
			if ( !is_string( $this->conf[$k] ) || $this->conf[$k] === '' ) {
				throw new LandRefused( 'CONFIGURATION', "the configuration names no $k; nothing is landed" );
			}
		}

		[ $tfk, $digest ] = $this->assembly( $w, $prefix, $badge );

		$setting = $this->setting( $w, $prefix );

		// Every record checked before anything is filled: all or nothing.
		$problems = [];
		$views = [];
		foreach ( $records as $i => $r ) {
			if ( !$r instanceof stdClass ) {
				$problems[] = [ 'index' => $i, 'answer' => [ 'REFUSED', [ [ 'REC-01', '-', 'the record is not an object' ] ] ] ];
				continue;
			}
			$rt = self::json( $r );
			$c = $this->askText( 'record', 'record_check', '{"record":' . $rt . ',"setting":' . $setting . ',"stage":"PUSH","tfk":' . $tfk . '}', 'the record check' );
			if ( $c !== [ 'OK' ] ) {
				$problems[] = [ 'index' => $i, 'answer' => $c ];
				continue;
			}
			$v = $this->askText( 'record', 'record_view', '{"grade":null,"record":' . $rt . ',"view":"HOLD"}', 'the record\'s view' );
			$kind = is_array( $v ) && ( $v[0] ?? null ) === 'OK' ? ( $v[1]['kind'] ?? null ) : null;
			$id = is_array( $v ) && ( $v[0] ?? null ) === 'OK' ? ( $v[1]['id'] ?? null ) : null;
			if ( !is_string( $kind ) || !is_string( $id ) ) {
				$problems[] = [ 'index' => $i, 'answer' => $v ];
				continue;
			}
			if ( !in_array( $kind, self::LANDS, true ) ) {
				$problems[] = [ 'index' => $i, 'answer' => [ 'REFUSED', [ [ 'LANDS', 'CLASS', "a $kind record is not landed by this Custos yet" ] ] ] ];
				continue;
			}
			// The withdrawal SUPERSEDES calls for is not built: a record carrying the member is refused
			// whatever it names (fail closed), never landed with nothing withdrawn.
			if ( property_exists( $r, 'SUPERSEDES' ) ) {
				$problems[] = [ 'index' => $i, 'answer' => [ 'REFUSED', [ [ 'WITHDRAWAL', 'SUPERSEDES', 'a record carrying SUPERSEDES is not landed by this Custos yet: the withdrawal is not built' ] ] ] ];
				continue;
			}
			$more = [];
			if ( $kind === 'RESULT' || $kind === 'ASSUMPTION' ) {
				$more[] = 'record_form_check';
			}
			if ( $kind === 'RESULT' ) {
				$more[] = 'domain_check';
			}
			foreach ( $more as $fn ) {
				$a = $this->askText( 'record', $fn, '{"record":' . $rt . ',"tfk":' . $tfk . '}', "the record's $fn" );
				if ( $a !== [ 'OK' ] ) {
					$problems[] = [ 'index' => $i, 'answer' => $a ];
					continue 2;
				}
			}
			$views[$i] = [ $kind, $id ];
		}
		if ( $problems !== [] ) {
			throw new LandRefused( 'RECORD CHECK', count( $problems ) . ' of ' . count( $records ) . ' records refused; nothing is landed',
				[ 'problems' => $problems ] );
		}

		// The open register volume, its identifiers, and no identifier landed twice.
		[ $regTitle, $regPayload ] = $this->registerText( $w, $prefix, $volume );
		$register = $this->read( $regPayload, 'the register' );
		if ( !is_array( $register ) ) {
			throw new LandRefused( 'REGISTER', 'the register is not a list' );
		}
		$taken = [];
		foreach ( $register as $old ) {
			$v = $this->askText( 'record', 'record_view', '{"grade":null,"record":' . self::json( $old ) . ',"view":"HOLD"}', 'a landed record\'s view' );
			if ( is_array( $v ) && is_string( $v[1]['id'] ?? null ) ) {
				$taken[$v[1]['id']] = true;
			}
		}
		foreach ( $views as $i => [ , $id ] ) {
			if ( isset( $taken[$id] ) ) {
				throw new LandRefused( 'RECORD CHECK', "the record at index $i carries an identifier landed already or twice in the batch; nothing is landed" );
			}
			$taken[$id] = true;
		}
		// Identifiers are taken in sequence (v1): each record's the next free one after the register's
		// records and the batch's before it, under the UWC's own prefix (the records' prefix is the
		// UWC's, as v1's), the identifier formed by the Calculator's allocation and compared whole. A
		// prefix the allocation refuses refuses the push. The count covers the open volume alone: a UWC
		// whose open volume is not the first is refused above until the volume roll is built.
		$next = count( $register ) + 1;
		foreach ( $views as $i => [ , $id ] ) {
			$al = $this->ask( 'hold', 'allocate_identifiers', [ 'range' => [ 'prefix' => $prefix, 'low' => 1, 'high' => self::ID_HIGH, 'next' => $next ] ],
				'the next free identifier' );
			if ( !is_array( $al ) || ( $al[0] ?? null ) !== 'OK' || !is_string( $al[1] ?? null ) || !is_int( $al[2][3] ?? null ) ) {
				throw new LandRefused( 'RECORD CHECK', "the UWC's prefix forms no record identifier; nothing is landed", [ 'problems' => [ [ 'index' => $i, 'answer' => $al ] ] ] );
			}
			if ( $id !== $al[1] ) {
				throw new LandRefused( 'RECORD CHECK', "the record at index $i is not the next free identifier, {$al[1]}; nothing is landed",
					[ 'problems' => [ [ 'index' => $i, 'answer' => [ 'REFUSED', [ [ 'SEQUENCE', 'ID', "ID must be the next free identifier {$al[1]}" ] ] ] ] ] ] );
			}
			$next = $al[2][3];
		}

		// The fields Custos owns, the class, the digest, and the check at LANDED.
		$ra = $this->read( $tfk, 'the Research Assembly' );
		$tpk = self::json( $ra instanceof stdClass && isset( $ra->TPK ) ? $ra->TPK : new stdClass() );
		$landed = [];
		$filled = [];
		foreach ( $records as $i => $r ) {
			[ $kind, $id ] = $views[$i];
			$r->BLOCK = $block;
			$r->AUTHOR = $account;
			$r->LANDED_BY = 'Custos';
			$r->LANDED = $stamp;
			$r->GRADE = $this->first( 'grade_values', $kind );
			$r->STATUS = $this->first( 'status_values', $kind );
			$r->TPS = $this->conf['tps'];
			$r->D_IS = $this->conf['d_is'];
			unset( $r->DIGEST );
			$class = null;
			if ( $kind === 'RESULT' ) {
				// An unchecked derivation earns nothing: a credit the Calculator refuses or owes is INSPECTION.
				$cr = $this->calc->call( 'derivation', 'credit_record',
					'{"record":' . self::json( $r ) . ',"register":' . $regPayload . ',"starting_set":' . $tpk . '}' );
				$class = $cr['exit'] === 0 && is_string( $cr['value']['CLASS'] ?? null ) ? $cr['value']['CLASS'] : 'INSPECTION';
				// The PMA row: written before the digest, so record_digest covers it and the
				// check at LANDED reads it (REC-43); a record of another kind carries no such row.
				$r->DERIVATION_CLASS = $class;
			}
			// Its CITES and ASSUMPTIONS resolve and stand in the register as read and the batch before it
			// (REC-57 to REC-61); no bibliography entry is landed yet, so a LITERATURE member is refused.
			$cc = $this->askText( 'record', 'citation_check', '{"entries":[],"record":' . self::json( $r ) . ',"register":'
				. self::json( array_merge( $register, $filled ) ) . ',"supersede_decided":false}', 'the record\'s citation check' );
			if ( $cc !== [ 'OK' ] ) {
				throw new LandRefused( 'RECORD CHECK', "the record at index $i is refused by the citation check; nothing is landed", [ 'problems' => [ [ 'index' => $i, 'answer' => $cc ] ] ] );
			}
			$d = $this->askText( 'record', 'record_digest', '{"record":' . self::json( $r ) . '}', 'the record\'s digest' );
			if ( !is_array( $d ) || ( $d[0] ?? null ) !== 'OK' || !is_string( $d[1] ?? null ) ) {
				throw new LandRefused( 'RECORD CHECK', "the record $id has no digest; nothing is landed", [ 'problems' => [ [ 'index' => $i, 'answer' => $d ] ] ] );
			}
			$r->DIGEST = $d[1];
			$c = $this->askText( 'record', 'record_check', '{"record":' . self::json( $r ) . ',"setting":' . $setting . ',"stage":"LANDED","tfk":' . $tfk . '}',
				'the landed record\'s check' );
			if ( $c !== [ 'OK' ] ) {
				throw new LandRefused( 'RECORD CHECK', "the record $id as landed is refused; nothing is landed", [ 'problems' => [ [ 'index' => $i, 'answer' => $c ] ] ] );
			}
			$filled[] = $r;
			$landed[] = [ 'id' => $id, 'digest' => $d[1], 'derivation_class' => $class ];
		}

		// The strike screen: SR3's mechanical tests (`landing strike_screen`) over the register as it
		// would stand, between each record of the batch, and each record its CITES and ASSUMPTIONS
		// reach, and the register with the batch before and after it. The strike is not written at
		// landing yet, so a batch the strike rule would strike, or one citing a record it would
		// strike, is refused whole, STRIKE OWED; a pair the test cannot clear is refused as one it
		// strikes (fail closed).
		$all = array_merge( $register, $filled );
		$at = [];
		foreach ( $views as $i => [ , $id ] ) {
			$at[$id] = $i;
		}
		$sc = $this->askText( 'landing', 'strike_screen', '{"incoming":' . self::json( array_keys( $at ) ) . ',"records":' . self::json( $all )
			. ',"tfk":' . $tfk . '}', 'the strike screen' );
		if ( $sc !== [ 'OK', [] ] ) {
			$held = is_array( $sc ) && ( $sc[0] ?? null ) === 'OK' && is_array( $sc[1] ?? null ) ? $sc[1] : null;
			if ( $held === null ) {
				throw new LandRefused( 'RECORD CHECK', 'the strike screen refuses the register; nothing is landed', [ 'problems' => [ [ 'index' => null, 'answer' => $sc ] ] ] );
			}
			$problems = [];
			foreach ( $held as $p ) {
				[ $a, $b, $word, $via ] = is_array( $p ) && count( $p ) === 4 ? array_map( 'strval', $p ) : [ '?', '?', '?', '?' ];
				$problems[] = [ 'index' => $at[$via] ?? null, 'answer' => [ 'REFUSED', [ [ 'STRIKE OWED', 'ID',
					"the strike rule's test holds $a and $b ($word), reached by $via; the strike is not written at landing yet" ] ] ] ];
			}
			throw new LandRefused( 'RECORD CHECK', count( $held ) . ' pairs the strike rule would strike are reached by the batch (STRIKE OWED); nothing is landed',
				[ 'problems' => $problems ] );
		}

		// The register rewritten, the badge last.
		$text = $this->askText( 'canonical', 'canonical_json', '{"value":' . self::json( $all ) . '}', 'the register\'s text' );
		if ( !is_string( $text ) ) {
			throw new LandRefused( 'REGISTER', 'the register\'s text is not a string' );
		}
		$this->page = PageClass::REGISTER_OPEN;
		$w->put( $regTitle, PageTexts::register( $prefix, $volume, $text ) );
		$this->page = PageClass::INDEX_AND_BADGE;
		$w->put( $this->titles->index( $prefix ), PageTexts::badge( $prefix, [
			'last_push' => $stamp, 'last_release' => $badge->last_release,
			'calculator_version' => $this->calc->version(), 'calculator_digest' => $this->conf['digest'],
			'record_count' => count( $all ), 'research_assembly' => $digest,
		], false, $volume, $structure ) );
		$this->page = null;
		$w->commit();
		if ( $this->afterPush !== null ) {
			// The structure test after every landing (TPS 5.3.47 (i), its superset): the job pushed for the
			// UWC, deduplicated. A push that throws is reported; the landing stands, and the next one pushes it.
			try {
				( $this->afterPush )( $prefix );
			} catch ( Throwable $e ) {
				$this->report( (int)$row['id'], $e );
			}
		}
		return [ 'landed' => $landed, 'block' => $block, 'record_count' => count( $all ) ];
	}

	/**
	 * The DIGEST GATE: the three Research Assembly pages carry one text, digested by the Calculator to
	 * the badge's. @return array{0: string, 1: string} the Research Assembly's text and its digest
	 */
	private function assembly( PageWriter $w, string $prefix, stdClass $badge ): array {
		$texts = [];
		$this->page = PageClass::RESEARCH_ASSEMBLY;
		foreach ( PageTitles::ZONES as $zone ) {
			$p = Blocks::one( $w->read( $this->titles->researchAssembly( $prefix, $zone ) ), 'assembly' );
			if ( $p === null ) {
				throw new LandRefused( 'DIGEST GATE', "the Research Assembly page $zone carries no assembly" );
			}
			$texts[] = $p;
		}
		if ( count( array_unique( $texts ) ) !== 1 ) {
			throw new LandRefused( 'DIGEST GATE', 'the three Research Assembly pages do not carry one Research Assembly' );
		}
		$tfk = $texts[0];
		$digest = $this->askText( 'zone', 'digest_research_assembly_of', '{"tfk":' . $tfk . '}', 'the Research Assembly\'s digest' );
		if ( $digest !== $badge->research_assembly ) {
			throw new LandRefused( 'DIGEST GATE', 'the Research Assembly digests to ' . $digest . ', not the badge\'s '
				. $badge->research_assembly . '; nothing is landed' );
		}
		return [ $tfk, $digest ];
	}

	/**
	 * The open register volume's title and its records' text, carried through. The volume roll is not
	 * built: the sequence counts the first volume alone, so a later open volume refuses (fail closed).
	 * @return array{0: string, 1: string}
	 */
	private function registerText( PageWriter $w, string $prefix, int $volume ): array {
		if ( $volume !== 1 ) {
			throw new LandRefused( 'REGISTER', "the open register volume is $volume; this Custos reads volume 1 only until the volume roll is built; nothing is landed or written" );
		}
		$this->page = PageClass::REGISTER_OPEN;
		$regTitle = $this->titles->registerVolume( $prefix, $volume );
		$regPayload = PageTexts::readRegister( $w->read( $regTitle ) );
		if ( $regPayload === null ) {
			throw new LandRefused( 'REGISTER', "the open register volume $volume carries no register" );
		}
		return [ $regTitle, $regPayload ];
	}

	// ---- the structure test with register (TPS 5.3.47) ---------------------------------------

	/** STRUCTURE_TEST: the lock's holder within its lease, else NOT HOLDER; the test run and its line written when it changes. */
	private function structureOp( PageWriter $w, array $row, int $now ): array {
		$prefix = (string)$row['prefix'];
		[ $badgeText, $badge, $volume ] = $this->live( $w, $prefix );
		$lock = $this->lock( $w, $prefix );
		if ( $lock->holder !== (string)$row['account'] || strcmp( (string)$lock->expires_at, self::stamp( $now ) ) <= 0 ) {
			throw new LandRefused( 'NOT HOLDER', 'a STRUCTURE_TEST is the lock holder\'s, within its lease; nothing is written' );
		}
		return $this->structure( $w, $prefix, $badgeText, $badge, $volume, $now );
	}

	/**
	 * The job custosStructureTest's work on the UWC $prefix (no ticket, no account): admitted through
	 * `governor admit` as STRUCTURE TEST JOB (lane 5: refused by pressure alone, no seats, no charge),
	 * then the test and its line, written only when it changes. A refusal (the admission's, the UWC's,
	 * the Calculator's answer, a PAGE FAULT) is answered with nothing written; a fault is reported to
	 * the error channel and rethrown, for the job's setLastError.
	 */
	public function structureJob( string $prefix ): array {
		$this->page = null;
		$now = ( $this->clock )();
		try {
			$this->admitJob( 'STRUCTURE TEST JOB', $now );
			$w = new PageWriter( $this->store, $this->titles );
			$this->page = PageClass::INDEX_AND_BADGE;
			$w->begin( $prefix, 'structure-test' );
			[ $badgeText, $badge, $volume ] = $this->live( $w, $prefix );
			return $this->structure( $w, $prefix, $badgeText, $badge, $volume, $now );
		} catch ( LandRefused $e ) {
			return Refusal::detail( $e );
		} catch ( PageFault $e ) {
			$this->report( 0, $e );
			return Refusal::detail( $e, $this->page );
		} catch ( Throwable $e ) {
			$this->report( 0, $e );
			throw $e;
		}
	}

	/**
	 * A job's admission (no account, no ticket): the MeteredState of an account with no seats, no
	 * traffic record and none in flight, the lanes' tickets in flight, the budget's level and use;
	 * anything but ADMITTED refused ADMISSION. A lane that charges is a fault: a job pays no seats.
	 */
	private function admitJob( string $kind, int $now ): void {
		[ , , $finishing, $starting ] = $this->inFlight( null, '' );
		$budget = $this->meter->budget();
		$state = [
			'now' => $now, 'agent_stop' => (bool)$this->conf['agent_stop'], 'suspended' => false,
			'governor_off' => (bool)$this->conf['governor_off'], 'agent_seats' => [ 0, $now ], 'sponsor_seats' => [ 0, $now ],
			'agent_in_flight' => 0, 'sponsor_in_flight' => 0, 'finishing_in_flight' => $finishing, 'starting_in_flight' => $starting,
			'pressure' => (string)$budget['kept'], 'use' => $budget['use'],
		];
		$seats = $this->ask( 'governor', 'seat_cost', [ 'kind' => $kind, 'records' => 0, 'rows' => 0 ], 'the seats' );
		$d = $this->ask( 'governor', 'admit', [ 'state' => $state, 'request' => [ 'kind' => $kind, 'seats' => $seats, 'draw' => ( $this->draw )() ] ],
			'the admission' );
		if ( !is_array( $d ) || ( $d['decision'] ?? null ) !== 'ADMITTED' ) {
			$extra = [ 'decision' => $d ];
			if ( is_array( $d ) && is_int( $d['retry_after'] ?? null ) ) {
				$extra['poll_after'] = $d['retry_after'];
			}
			throw new LandRefused( 'ADMISSION', 'the governor did not admit the job: ' . ( is_array( $d ) ? (string)( $d['decision'] ?? '' ) : '' )
				. '; nothing is written', $extra );
		}
		if ( ( $d['charge'] ?? null ) !== null ) {
			throw new CalculatorFault( 'the governor charged a job: ' . self::cut( self::json( $d['charge'] ) ), CalculatorFault::ANSWER_FORM, 'governor', 'admit' );
		}
	}

	/**
	 * The structure test with register over the UWC's Research Assembly and open register volume, one
	 * Calculator call; the line composed from its answer alone and written, through the writer opened
	 * on the UWC, only when what it says changes (the badge's rule: one save, the INDEX AND BADGE page).
	 */
	private function structure( PageWriter $w, string $prefix, string $badgeText, stdClass $badge, int $volume, int $now ): array {
		[ $tfk ] = $this->assembly( $w, $prefix, $badge );
		[ , $regPayload ] = $this->registerText( $w, $prefix, $volume );
		$a = $this->askText( 'eom', 'eom_register_test', '{"tfk":' . $tfk . ',"records":' . $regPayload . '}', 'the structure test' );
		$line = self::structureLine( $a, gmdate( 'Y-m-d', $now ) );
		$this->page = PageClass::INDEX_AND_BADGE;
		$was = PageTexts::readStructure( $badgeText );
		if ( $was !== null && PageTexts::structureSays( $was ) === PageTexts::structureSays( $line ) ) {
			// Unchanged beside its date: nothing written, the line as it stands answered.
			$this->page = null;
			return [ 'structure_test' => $was, 'written' => false ];
		}
		$w->put( $this->titles->index( $prefix ), PageTexts::badge( $prefix, [
			'last_push' => $badge->last_push, 'last_release' => $badge->last_release,
			'calculator_version' => $badge->calculator_version, 'calculator_digest' => $badge->calculator_digest,
			'record_count' => $badge->record_count, 'research_assembly' => $badge->research_assembly,
		], false, $volume, $line ) );
		$this->page = null;
		$w->commit();
		return [ 'structure_test' => $line, 'written' => true ];
	}

	/**
	 * The STRUCTURE TEST LINE of an answer of `eom eom_register_test` on $date (YYYY-MM-DD), read
	 * from the answer alone: ["OK", report, findings, ["USED", ids], ["SETTLED", ...], ["OPEN", ...]].
	 * ["REFUSED", reason] is refused STRUCTURE TEST; any other form is a CALCULATOR FAULT.
	 */
	public static function structureLine( mixed $a, string $date ): string {
		if ( is_array( $a ) && array_is_list( $a ) && count( $a ) === 2 && ( $a[0] ?? null ) === 'REFUSED' && is_string( $a[1] ) ) {
			throw new LandRefused( 'STRUCTURE TEST', 'the Calculator refuses the structure test with register: ' . self::cut( $a[1] ) . '; nothing is written',
				[ 'calculator' => $a ] );
		}
		$ok = is_array( $a ) && array_is_list( $a ) && count( $a ) === 6 && $a[0] === 'OK' && is_array( $a[2] ) && array_is_list( $a[2] )
			&& is_array( $a[3] ) && array_is_list( $a[3] ) && count( $a[3] ) === 2 && $a[3][0] === 'USED' && is_array( $a[3][1] ) && array_is_list( $a[3][1] )
			&& array_filter( $a[3][1], static fn ( $i ): bool => is_string( $i ) && preg_match( '/\A[^\s,]+\z/', $i ) === 1 ) === $a[3][1];
		if ( !$ok ) {
			throw new CalculatorFault( 'the structure test\'s answer is not of the form ["OK", report, findings, ["USED", ids], ...]',
				CalculatorFault::ANSWER_FORM, 'eom', 'eom_register_test' );
		}
		$findings = $a[2];
		$result = $findings === [] ? 'structurally regular with register'
			: 'FINDINGS ' . implode( ' ', array_map( static fn ( $f ): string => self::json( $f ), $findings ) );
		$ids = $a[3][1] === [] ? '-' : implode( ', ', $a[3][1] );
		return "STRUCTURE TEST $date $result WITH $ids";
	}

	// ---- reading -----------------------------------------------------------------------------

	/** The UWC's badge page: its text, the badge read, the open volume; a UWC not LIVE is refused. */
	private function live( PageWriter $w, string $prefix ): array {
		$this->page = PageClass::INDEX_AND_BADGE;
		$text = $w->read( $this->titles->index( $prefix ) );
		$facts = PageTexts::facts( $text );
		if ( ( $facts['retired'] ?? true ) !== false || !isset( $facts['open_volume'] ) ) {
			throw new LandRefused( 'UWC', "there is no LIVE UWC $prefix with an open register volume" );
		}
		$payload = PageTexts::readBadge( $text );
		$badge = $payload === null ? null : $this->read( $payload, 'the badge' );
		if ( !$badge instanceof stdClass || !isset( $badge->research_assembly ) ) {
			throw new LandRefused( 'UWC', "the UWC $prefix carries no badge" );
		}
		return [ $text, $badge, $facts['open_volume'] ];
	}

	private function lock( PageWriter $w, string $prefix ): stdClass {
		$this->page = PageClass::LOCK_PAGE;
		return $this->lockOf( $w->read( $this->titles->lock( $prefix ) ), $prefix );
	}

	/**
	 * A held lock's payload: the Calculator's canonical JSON of its members (`canonical
	 * canonical_json`, in the job, as the register's text is written), so an account name of any
	 * spelling MediaWiki admits is carried exactly; PageTexts::lock checks the members first.
	 */
	private function lockText( array $members ): string {
		$text = $this->askText( 'canonical', 'canonical_json', '{"value":' . self::json( $members ) . '}', 'the lock\'s text' );
		if ( !is_string( $text ) ) {
			throw new LandRefused( 'UWC', 'the lock\'s text is not a string' );
		}
		return $text;
	}

	/** The lock page's text $text read: its payload through the Calculator. */
	private function lockOf( ?string $text, string $prefix ): stdClass {
		$payload = PageTexts::readLock( $text );
		$lock = $payload === null ? null : $this->read( $payload, 'the lock' );
		if ( !$lock instanceof stdClass || !property_exists( $lock, 'holder' ) ) {
			throw new LandRefused( 'UWC', "the UWC $prefix carries no lock" );
		}
		return $lock;
	}

	/**
	 * The UWC's ACCESS POLICY (TPS 5.16) asked of the Calculator for the asker's write: the policy is
	 * the DRAFT UWC page's block pma-policy, one word, OPEN or CLOSED, read by comparing the whole
	 * payload, as setting() reads its word; a page that states none is OPEN (v1 read an absent policy
	 * as OPEN). Another word is refused UWC. Under CLOSED the ACCESS LIST page's block pma-access,
	 * a list of account names read by the Calculator, says whether the account is listed (a whole
	 * name compared); a list that is absent or cannot be read refuses (fail closed). The decision
	 * is `permissions permits` (the CLOSED PREDICATE, TPS 5.13.4) for the asker's lock state, the
	 * page class and the operation; anything but PERMITTED is refused ACCESS.
	 */
	private function access( PageWriter $w, string $prefix, string $account, string $asker, string $class, string $op ): void {
		$this->page = PageClass::DRAFT_UWC;
		$policy = Blocks::one( $w->read( $this->titles->draft( $prefix ) ), self::POLICY ) ?? self::POLICY_DEFAULT;
		if ( !in_array( $policy, self::POLICIES, true ) ) {
			throw new LandRefused( 'UWC', "the DRAFT UWC page of $prefix states an access policy other than "
				. implode( ', ', self::POLICIES ) . '; nothing is landed' );
		}
		$context = [ $policy ];
		if ( $policy === 'CLOSED' ) {
			$this->page = PageClass::ACCESS_LIST;
			$payload = Blocks::one( $w->read( $this->titles->accessList( $prefix ) ), self::ACCESS );
			if ( $payload === null ) {
				throw new LandRefused( 'ACCESS', "the UWC $prefix is CLOSED and its access list cannot be read; nothing is granted or landed" );
			}
			$list = $this->read( $payload, 'the access list' );
			if ( !is_array( $list ) || !array_is_list( $list ) || array_filter( $list, 'is_string' ) !== $list ) {
				throw new LandRefused( 'ACCESS', "the UWC $prefix is CLOSED and its access list is not a list of account names; nothing is granted or landed" );
			}
			if ( in_array( $account, $list, true ) ) {
				$context[] = 'LISTED';
			}
		}
		$p = $this->ask( 'permissions', 'permits', [ 'asker' => $asker, 'class' => $class, 'op' => $op, 'context' => $context ], 'the access policy' );
		if ( $p !== 'PERMITTED' ) {
			throw new LandRefused( 'ACCESS', "the access policy of $prefix ($policy) refuses the account; nothing is granted or landed" );
		}
	}

	/**
	 * The UWC's BIBLIOGRAPHY SETTING (TPS 5.21.1), the `setting` of `record record_check` (REC-30:
	 * no LITERATURE under OFF; REC-31: a VERIFICATION's SOURCE in its LITERATURE under ON or
	 * CLOSED), as the JSON string the request carries. It is declared per UWC and stated on its
	 * DRAFT UWC page (version 1's candidate certificate carried it there) as the block pma-setting,
	 * one word, read by comparing the whole payload with OFF, ON and CLOSED, as PageTexts::facts
	 * reads a state. A DRAFT page that states none takes the fleet default, OFF
	 * (`bibliographySettingDefault`, Principia/Parameters.lean). A payload that is not one of the
	 * three is refused: never null, under which the Calculator checks neither rule.
	 */
	private function setting( PageWriter $w, string $prefix ): string {
		$this->page = PageClass::DRAFT_UWC;
		$word = Blocks::one( $w->read( $this->titles->draft( $prefix ) ), self::SETTING );
		$word ??= self::SETTING_DEFAULT;
		if ( !in_array( $word, self::SETTINGS, true ) ) {
			throw new LandRefused( 'UWC', "the DRAFT UWC page of $prefix states a bibliography setting other than "
				. implode( ', ', self::SETTINGS ) . '; nothing is landed' );
		}
		return '"' . $word . '"';
	}

	/** The first of a class's grade or status values: the record table's initial value. */
	private function first( string $fn, string $kind ): string {
		$a = $this->ask( 'record', $fn, [ 'class' => $kind ], "the $fn of $kind" );
		if ( !is_array( $a ) || ( $a[0] ?? null ) !== 'OK' || !is_string( $a[1][0] ?? null ) ) {
			throw new LandRefused( 'RECORD CHECK', "no $fn for $kind" );
		}
		return $a[1][0];
	}

	/**
	 * A text read by the Calculator (`canonical canonical_json`) and its canonical answer decoded,
	 * objects as objects. A text the Calculator refuses is the ticket's answer. The value decoded is
	 * written again with the job's own flags (PHP's text) and compared with the canonical text byte for
	 * byte. Where the two differ, PHP's text goes through `canonical canonical_json` once more and the
	 * value is held only where that canonical text is the first byte for byte; else it is refused NOT
	 * READ (detail HOLD) before any check reads it, nothing landed. PHP decodes an integer outside
	 * PHP_INT_MIN..PHP_INT_MAX to a float, which it writes with a fraction or an exponent, so the
	 * Calculator reads it as a number, never the integer: refused. A number the canonical text spells
	 * otherwise than PHP's encoder (`1e-05`, PHP `1.0e-5`) and a string holding U+2028 or U+2029
	 * (which PHP escapes) are held: the canonical text is the same. PHP's text is its shortest
	 * (run sets serialize_precision -1), so a held number's text is the canonical value exactly. A number PHP decodes to INF
	 * cannot be written: refused. Every text the job reads passes here.
	 */
	private function read( string $text, string $what ): mixed {
		$canonical = (string)$this->askText( 'canonical', 'canonical_json', '{"value":' . $text . '}', $what, 'NOT READ' );
		try {
			$value = json_decode( $canonical, false, 512, JSON_THROW_ON_ERROR );
		} catch ( JsonException $e ) {
			throw new CalculatorFault( "the Calculator's canonical text of $what does not decode", CalculatorFault::ANSWER_FORM,
				'canonical', 'canonical_json' );
		}
		try {
			$again = self::json( $value );
		} catch ( JsonException $e ) {
			// An integer past binary64's range decodes to INF, which PHP's encoder refuses to write.
			// Reached by an integer (L108): the Calculator reads an integer at any size and refuses only a
			// number literal past binary64's range; the branch also guards a later change of that rule.
			$again = null;
		}
		if ( $again === null ) {
			throw new LandRefused( 'NOT READ', "$what: " . self::HOLD );
		}
		if ( $again !== $canonical ) {
			// PHP's spelling differs (an exponent, an escaped U+2028): the Calculator reads PHP's text once more,
			// and the value is held only where its canonical text is the first, byte for byte.
			$twice = $this->askText( 'canonical', 'canonical_json', '{"value":' . $again . '}', $what, 'NOT READ' );
			if ( $twice !== $canonical ) {
				throw new LandRefused( 'NOT READ', "$what: " . self::HOLD );
			}
		}
		return $value;
	}

	/** @return mixed the Calculator's answer to a request PHP builds from its own values */
	private function ask( string $family, string $fn, array $request, string $what ): mixed {
		return $this->askText( $family, $fn, self::json( $request ), $what );
	}

	/** @return mixed the Calculator's answer; its refusal is the ticket's answer */
	private function askText( string $family, string $fn, string $json, string $what, string $word = 'CALCULATOR REFUSED' ): mixed {
		$r = $this->calc->call( $family, $fn, $json );
		if ( $r['exit'] !== 0 ) {
			throw new LandRefused( $word, "$what: " . $r['refused'] . ': ' . $r['detail'],
				[ 'calculator' => [ 'refused' => $r['refused'], 'detail' => $r['detail'] ] ] );
		}
		return $r['value'];
	}

	private static function json( mixed $v ): string {
		return json_encode( $v, self::JSON );
	}

	private static function stamp( int $t ): string {
		return gmdate( 'Y-m-d\TH:i:s\Z', $t );
	}

	private static function cut( string $s ): string {
		return mb_substr( $s, 0, 500 );
	}
}
