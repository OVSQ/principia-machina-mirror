<?php
/**
 * The scenarios' driver: a UWC seeded as Custos:SeedUwc writes it, over FileStore, FileTicketStore,
 * FileSeatStore, FileNonceStore and FileCertificateStore, run by the landing job on the built pcalc; each op a ticket as
 * Ops writes it, run by Landing, its answer read back. A stepping clock (whole seconds).
 *
 * The wiki run (SCW::$wiki, scenarios.php under maintenance/run.php on the rehearsal wiki): the same
 * scenarios over the wiki's own stores, MwStore, DbTicketStore, DbSeatStore and DbNonceStore, each op's
 * ticket written by Ops with the API's enqueue (a LandJob pushed to the job queue) and run by the job
 * runner (JobRunner, type custosLand, as runJobs runs it), its answer read back from the ticket. Each
 * UWC under a title root of its own ($wgCustosUwcRoot set for its jobs); the prefix and the accounts
 * are the scenarios' own, so the tables custos_nonce and custos_seat, keyed by account (and prefix),
 * are shared by every UWC of the run. The nonce a PUSH answers is the one the last answer to that
 * account on that prefix carried (a grant, or any answer after the challenge), never a read of the
 * table (DbNonceStore has take, no peek). LandJob reads the wall clock: a step of a UWC's clock moves
 * that UWC's stored times back by the step (ScWikiLanding::shift: its lock's stamps, its rows of
 * custos_ticket, custos_nonce and custos_seat), so its assertions after the step run on the wiki; a UWC
 * whose landing job is rebuilt, which is forked or whose nonce store is set carries that cause
 * (ScUwc::taint), and a read of its nonce store marks the reads after it in that case (SCW::cause).
 * Each assertion records, when it is made, the UWCs it reads (those read since the assertion before
 * it; with none, that assertion's when it is of the same case) and the cause any of them carried when read: a PASS or a
 * DIVERGENT so recorded counts wiki-divergent with that cause (scenarios.php SC::tally); a FAIL or a
 * DEFECT is never relabelled, and a ticket the job runner leaves unanswered, or a land job that
 * fails, is a FAIL (SCW::answer), never a refusal. The plan run (SCW::$plan, scenarios.php
 * --wiki-plan) traces the same causes over the file-backed stores, so the wiki-only rows of
 * DIVERGENCES.md are written and checked without MediaWiki.
 */

declare( strict_types=1 );
require_once __DIR__ . '/bootstrap.php';

use Custos\Blocks;
use Custos\Calculator;
use Custos\CertificateStore;
use Custos\Challenge;
use Custos\Landing;
use Custos\MemMeterStore;
use Custos\NonceStore;
use Custos\Ops;
use Custos\PageStore;
use Custos\PageTexts;
use Custos\PageTitles;
use Custos\PageWriter;
use Custos\Tests\AnyResidence;
use Custos\Tests\FileCertificateStore;
use Custos\Tests\FileNonceStore;
use Custos\Tests\FileSeatStore;
use Custos\Tests\FileStore;
use Custos\Tests\FileTicketStore;
use Custos\Tests\ProcRunner;

const SC_JSON = JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_PRESERVE_ZERO_FRACTION | JSON_THROW_ON_ERROR;

/** The clone's root, the built pcalc, the scratch folder (the run's own, made at its first use, cleared at its end). */
function sc_root(): string {
	return dirname( __DIR__, 2 );
}

function sc_built(): string {
	return sc_root() . '/.lake/build/bin/pcalc';
}

function sc_scratch(): string {
	static $s = null;
	if ( $s === null ) {
		$s = sys_get_temp_dir() . '/custos-scenarios-' . getmypid();
		if ( !is_dir( $s ) && !mkdir( $s, 0700, true ) && !is_dir( $s ) ) {
			throw new RuntimeException( "the scenarios' scratch folder $s cannot be made" );
		}
		register_shutdown_function( static fn () => sc_clear( $s ) );
	}
	return $s;
}

function sc_clear( string $p ): void {
	if ( is_link( $p ) || is_file( $p ) ) {
		unlink( $p );
	} elseif ( is_dir( $p ) ) {
		foreach ( scandir( $p ) ?: [] as $e ) {
			if ( $e !== '.' && $e !== '..' ) {
				sc_clear( "$p/$e" );
			}
		}
		rmdir( $p );
	}
}

/** The Calculator over the built pcalc, made once. */
function sc_calc(): Calculator {
	static $c = null;
	if ( $c === null ) {
		$basic = (string)file_get_contents( sc_root() . '/Principia/Basic.lean' );
		$version = preg_match( '/^def version : String := "([^"]+)"$/m', $basic, $m ) ? $m[1] : '';
		$c = new Calculator( sc_built(), [ 'version' => $version, 'digest' => Calculator::digestOf( sc_built() ) ],
			new ProcRunner(), 'cli', new AnyResidence() );
	}
	return $c;
}

function sc_titles(): PageTitles {
	static $t = null;
	if ( SCW::$wiki ) {
		// the titles under the root of the UWC last read (SCW::read)
		return SCW::titles( SCW::$cur !== null ? SCW::$cur->root() : SCW::ROOT );
	}
	return $t ??= new PageTitles( SCW::ROOT, 'Principia Machina' );
}

/** The spring draft of version 1's examples. */
function sc_draft(): string {
	return (string)file_get_contents( sc_root() . '/docs/v1/tpx/TPX/examples/spring_draft.json' );
}

/**
 * A fresh UWC: the spring draft seeded under $px (DRAFT UWC page, the three Research Assembly pages,
 * register volume 1 empty, the lock free, the badge), the stores of its own, the clock at 2026-10-05.
 * The first seed of a prefix is written by PageWriter as Custos:SeedUwc writes it; later ones are
 * copies of its files (the same bytes), to spare the Calculator's calls.
 * $master (FIXTURE): version 1's register opened with the MASTER record <px>-1, so its gates number
 * the first pushed record <px>-2; Custos seeds no MASTER and allocates from <px>-1. The stand-in, an
 * ASSUMPTION landed as <px>-1 by Agent M through PETITION, PUSH and RELEASE a minute before the clock
 * starts, keeps version 1's identifiers for every later step. $access: the UWC CLOSED (the DRAFT UWC
 * page's block pma-policy) with that ACCESS LIST (pma-access), written with the seed.
 */
function sc_uwc( string $tag, string $px = 'SPR', bool $master = true, ?array $access = null ): stdClass {
	static $seeded = [];
	$dir = sc_scratch() . "/$tag";
	if ( SCW::$wiki ) {
		return sc_uwc_wiki( $dir, $px, $master, $access );
	}
	$form = $px . ( $master ? '-m' : '' ) . ( $access === null ? '' : '-closed-' . md5( json_encode( $access ) ) );
	$start = SCW::START;
	if ( !isset( $seeded[$form] ) ) {
		$seeded[$form] = sc_scratch() . "/seed-$form";
		sc_seed( new FileStore( $seeded[$form] . '/pages' ), sc_titles(), $px, $access );
		if ( $master ) {
			sc_master( sc_open( $seeded[$form], $px, $start - 60 ), $px );
		}
	}
	sc_copy( $seeded[$form], $dir );
	return sc_open( $dir, $px, $start );
}

/** The seed as Custos:SeedUwc writes it: the spring draft under $px, its pages through PageWriter. */
function sc_seed( PageStore $store, PageTitles $pt, string $px, ?array $access ): void {
	static $canon = null, $ra = null;
	$calc = sc_calc();
	$draft = sc_draft();
	$canon ??= $calc->call( 'canonical', 'canonical_json', '{"value":' . $draft . '}' )['value'];
	$ra ??= $calc->call( 'zone', 'digest_research_assembly_of', '{"tfk":' . $draft . '}' )['value'];
	$seed = new PageWriter( $store, $pt );
	$seed->begin( $px, 'seed' );
	$seed->put( $pt->draft( $px ), Blocks::render( 'draft', $canon ) . "\n"
		. ( $access === null ? '' : Blocks::render( Landing::POLICY, 'CLOSED' ) . "\n" ) );
	foreach ( PageTitles::ZONES as $zone ) {
		$seed->put( $pt->researchAssembly( $px, $zone ), Blocks::render( 'assembly', $canon ) . "\n" );
	}
	$seed->put( $pt->registerVolume( $px, 1 ), PageTexts::register( $px, 1, '[]' ) );
	$seed->put( $pt->lock( $px ), PageTexts::lock( $px, null, null, null, null ) );
	$seed->put( $pt->index( $px ), PageTexts::badge( $px, [ 'last_push' => null, 'last_release' => null,
		'calculator_version' => sc_calc_version(), 'calculator_digest' => Calculator::digestOf( sc_built() ), 'record_count' => 0,
		'research_assembly' => $ra ], false, 1 ) );
	$seed->commit();
	if ( $access !== null ) {
		// The ACCESS LIST is not a page a landing writes (PageWriter's fence): the seed puts it in the store itself.
		$store->put( $pt->accessList( $px ), Blocks::render( Landing::ACCESS, json_encode( $access, SC_JSON ) ) . "\n", 'seed' );
	}
}

/** The MASTER's stand-in on $m: <px>-1 landed by Agent M through PETITION, PUSH and RELEASE. */
function sc_master( stdClass $m, string $px ): void {
	$a = sc_push( $m, [ sc_arec( "$px-1", 'The place of version 1\'s MASTER record.' ) ], 'Agent M', 'B0' );
	$r = sc_op( $m, 'RELEASE', 'Agent M', [ 'block' => 'B0' ] );
	if ( array_column( $a['landed'] ?? [], 'id' ) !== [ "$px-1" ] || !isset( $r['released'] ) ) {
		throw new RuntimeException( "the MASTER's stand-in did not land on $px: " . json_encode( [ $a, $r ] ) );
	}
}

/** sc_uwc on the wiki: a title root of its own, seeded through MwStore, the MASTER's stand-in by the job. */
function sc_uwc_wiki( string $dir, string $px, bool $master, ?array $access ): ScUwc {
	SCW::fresh( $dir );
	$u = sc_open( $dir, $px, SCW::START - 60 );
	sc_seed( $u->store, SCW::titles( $u->root() ), $px, $access );
	if ( $master ) {
		sc_master( $u, $px );
	}
	$u->at( SCW::START );
	return $u;
}

/**
 * A copy of $u under $tag: its pages, tickets, seats and nonces, its clock. On the wiki the pages alone
 * are copied (to the fork's title root); the tables are the wiki's, shared by the fork and its source,
 * so both are traced (SCW::taint), save a $template's fork (its source is never asserted on again).
 */
function sc_fork( stdClass $u, string $tag, bool $template = false ): stdClass {
	$dir = sc_scratch() . "/$tag";
	sc_copy( $u->dir, $dir );
	$f = sc_open( $dir, $u->px, $u->now );
	if ( $u instanceof ScUwc && $f instanceof ScUwc ) {
		// the copy's reads of the source are not an assertion's: the fork's own reads are
		SCW::forget( $u );
		$u->taint( SCW::FORK );
		if ( !$template ) {
			$f->taint( SCW::FORK );
		}
	}
	return $f;
}

function sc_copy( string $from, string $to ): void {
	if ( SCW::$wiki ) {
		// the pages under the title root of $from, written under the title root of $to
		$fr = SCW::root( $from );
		$tr = SCW::root( $to );
		$src = new ScStore( new \Custos\MwStore(), $fr );
		$dst = new \Custos\MwStore();
		foreach ( $src->titles() as $t ) {
			$dst->put( $tr . substr( $t, strlen( $fr ) ), (string)$src->get( $t ), 'scenario copy' );
		}
		return;
	}
	if ( is_dir( $from ) ) {
		if ( !is_dir( $to ) ) {
			mkdir( $to, 0777, true );
		}
		foreach ( scandir( $from ) ?: [] as $e ) {
			if ( $e !== '.' && $e !== '..' ) {
				sc_copy( "$from/$e", "$to/$e" );
			}
		}
	} elseif ( is_file( $from ) ) {
		copy( $from, $to );
	}
}

/**
 * The certificates admission reads, in $file: every agent account the scenarios use (Agent A to
 * Agent Z) certified ACTIVE, each bound to a Sponsor of its own (Sponsor A to Sponsor Z), so each
 * Sponsor's bucket is its one agent's. Version 1 had no certificate; admission passes them as it
 * passed every account there. Written once; a folder copied keeps its file.
 */
function sc_certs( string $file ): FileCertificateStore {
	$certs = new FileCertificateStore( $file );
	if ( !is_file( $file ) ) {
		sc_certify( $certs );
	}
	return $certs;
}

/**
 * Agent A to Agent Z certified ACTIVE in $certs, each to a Sponsor of its own, unless Agent A is
 * already there: the file run's rows (sc_certs) and, on the wiki run, the rows of the wiki's own
 * table custos_certificate (DbCertificateStore, which the wiki's LandJob reads), written as the
 * scenario's own act where the Operator's Custos:Certify writes them on a live wiki.
 */
function sc_certify( CertificateStore $certs ): CertificateStore {
	if ( $certs->get( 'Agent A' ) === null ) {
		foreach ( range( 'A', 'Z' ) as $k ) {
			$certs->put( [ 'agent' => "Agent $k", 'sponsor' => "Sponsor $k", 'd_is' => str_repeat( 'd', 64 ), 'd_prompt' => str_repeat( 'e', 64 ),
				'family' => 'test family', 'model' => 'test model', 'state' => CertificateStore::ACTIVE ] );
		}
	}
	return $certs;
}

/** The stores, the landing job and the ops over the files under $dir. */
function sc_open( string $dir, string $px, int $now ): stdClass {
	if ( SCW::$wiki ) {
		return sc_open_wiki( $dir, $px, $now );
	}
	if ( SCW::$plan ) {
		return sc_open_plan( $dir, $px, $now );
	}
	$u = new stdClass();
	$u->dir = $dir;
	$u->px = $px;
	$u->now = $now;
	$u->store = new FileStore( "$dir/pages" );
	$u->tickets = new FileTicketStore( "$dir/tickets" );
	$u->seats = new FileSeatStore( "$dir/seats.json" );
	$u->nonces = new FileNonceStore( "$dir/nonces.json" );
	$u->certs = sc_certs( "$dir/certs.json" );
	$conf = sc_conf();
	$u->landing = new Landing( sc_calc(), $u->store, sc_titles(), $u->tickets, $u->seats, $u->certs, $conf, static function () use ( $u ): int {
		return $u->now;
	}, static fn (): array => [ 0, 1 ], nonces: $u->nonces, meter: new MemMeterStore() );
	$u->ops = new Ops( $u->tickets, static function ( int $id ): void {
	} );
	return $u;
}

/** The landing job's configuration in the scenarios: the governor off, a fixed D_IS, the built pcalc's digest. */
function sc_conf(): array {
	return [ 'tps' => '0.4.0', 'd_is' => str_repeat( 'd', 64 ), 'digest' => Calculator::digestOf( sc_built() ), 'poll_after' => 30,
		'governor_off' => true ];
}

/** sc_open in the plan run: the file-backed stores, the UWC traced (ScUwc). */
function sc_open_plan( string $dir, string $px, int $now ): ScUwc {
	$u = new ScUwc( [ 'dir' => $dir, 'px' => $px, 'now' => $now ] );
	$store = new FileStore( "$dir/pages" );
	$tickets = new FileTicketStore( "$dir/tickets" );
	$seats = new FileSeatStore( "$dir/seats.json" );
	$nonces = new FileNonceStore( "$dir/nonces.json" );
	$certs = sc_certs( "$dir/certs.json" );
	$u->init( [ 'store' => new ScStore( $store ), 'tickets' => $tickets, 'seats' => $seats, 'nonces' => new ScNonces( $nonces ), 'certs' => $certs,
		'landing' => new Landing( sc_calc(), $store, sc_titles(), $tickets, $seats, $certs, sc_conf(), static fn (): int => $u->clock(),
			static fn (): array => [ 0, 1 ], nonces: $nonces, meter: new MemMeterStore() ),
		'ops' => new Ops( $tickets, static function ( int $id ): void {
		} ) ] );
	return $u;
}

/**
 * sc_open on the wiki: the UWC under the title root of $dir (SCW::root), its stores the wiki's, its ops'
 * tickets enqueued as the API enqueues them (a LandJob each) and run by the job runner (ScWikiLanding).
 */
function sc_open_wiki( string $dir, string $px, int $now ): ScUwc {
	$root = SCW::root( $dir );
	$u = new ScUwc( [ 'dir' => $dir, 'px' => $px, 'now' => $now, 'root' => $root ] );
	$tickets = new \Custos\DbTicketStore();
	$land = new ScWikiLanding( $u );
	$u->init( [ 'store' => new ScStore( new \Custos\MwStore(), $root ), 'tickets' => $tickets, 'seats' => new \Custos\DbSeatStore(),
		'nonces' => new ScNonces( null, new \Custos\DbNonceStore() ), 'certs' => sc_certify( new \Custos\DbCertificateStore() ),
		'landing' => $land, 'wiki' => $land,
		'ops' => new Ops( $tickets, static function ( int $id ): void {
			// the API's enqueue (ApiPma): one deduplicated job per ticket
			\MediaWiki\MediaWikiServices::getInstance()->getJobQueueGroup()->push( new \Custos\LandJob( [ 'ticket' => $id ] ) );
		} ) ] );
	return $u;
}

/** The Calculator's canonical JSON of a held lock's members: the writer PageTexts::lock takes, as Landing::lockText supplies it. */
function sc_canon(): callable {
	return static fn ( array $m ): string => (string)sc_calc()->call( 'canonical', 'canonical_json',
		'{"value":' . json_encode( $m, JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_THROW_ON_ERROR ) . '}' )['value'];
}

function sc_calc_version(): string {
	$basic = (string)file_get_contents( sc_root() . '/Principia/Basic.lean' );
	return preg_match( '/^def version : String := "([^"]+)"$/m', $basic, $m ) ? $m[1] : '';
}

/**
 * One op as an agent sends it: the ticket Ops writes, run by the landing job, its answer. A PUSH with
 * no challenge_response answers the account's outstanding nonce through the Calculator, as an agent
 * that executes does. A refusal by Ops (GA1) is answered ["refused" => "OPS", "code" => ..].
 */
function sc_op( stdClass $u, string $op, string $account, array $params = [] ): array {
	$nonce = sc_nonce( $u, $account );
	if ( $op === 'PUSH' && !array_key_exists( 'challenge_response', $params ) && $nonce !== null ) {
		$params['challenge_response'] = Challenge::response( sc_calc(), $nonce )[1];
	}
	try {
		$id = $u->ops->run( $op, $u->px, $account, $params )['ticket'];
	} catch ( \Custos\Refusal $e ) {
		return [ 'refused' => 'OPS', 'code' => $e->what, 'detail' => $e->getMessage() ];
	}
	sc_tick( $u );
	return $u->landing->run( $id );
}

/** The account's outstanding nonce on $u's prefix as an agent knows it (on the wiki: from the answers). */
function sc_nonce( stdClass $u, string $account ): ?string {
	return $u->nonces instanceof ScNonces ? $u->nonces->known( $account, $u->px ) : $u->nonces->peek( $account, $u->px );
}

/** One op's second on the scenario's clock (not a step of it). */
function sc_tick( stdClass $u ): void {
	if ( $u instanceof ScUwc ) {
		$u->tick();
	} else {
		$u->now++;
	}
}

/** The lock as the page holds it. */
function sc_lock( stdClass $u ): array {
	return (array)json_decode( (string)PageTexts::readLock( (string)$u->store->get( sc_titles()->lock( $u->px ) ) ), true );
}

function sc_badge( stdClass $u ): array {
	return (array)json_decode( (string)PageTexts::readBadge( (string)$u->store->get( sc_titles()->index( $u->px ) ) ), true );
}

/** The register's records, volume 1. */
function sc_register( stdClass $u ): array {
	return (array)json_decode( (string)PageTexts::readRegister( (string)$u->store->get( sc_titles()->registerVolume( $u->px, 1 ) ) ), true );
}

/** Every page's text, for "nothing written". */
function sc_snap( stdClass $u ): array {
	$o = [];
	foreach ( $u->store->titles() as $t ) {
		$o[$t] = $u->store->get( $t );
	}
	return $o;
}

/**
 * Version 1's gpush: as if $account had petitioned and been granted the lock (FIXTURE: a lock held by
 * another account is let run past its lease first), then the PUSH of $records under that grant.
 */
function sc_push( stdClass $u, array $records, string $account, string $block = 'B1' ): array {
	$g = sc_grant( $u, $account, $block );
	if ( $g !== null ) {
		return [ 'refused' => 'PETITION', 'petition' => $g ];
	}
	return sc_op( $u, 'PUSH', $account, [ 'records' => json_encode( $records, SC_JSON ) ] );
}

/**
 * gpush's grant alone: $account made the lock's holder unless it is (a lock held by another account
 * let run past its lease first); null, or the PETITION's refusal. A refused push is compared with
 * the pages after this, so the grant's own write is not counted as the push's.
 */
function sc_grant( stdClass $u, string $account, string $block = 'B1' ): ?array {
	$lk = sc_lock( $u );
	if ( ( $lk['holder'] ?? null ) === $account ) {
		return null;
	}
	if ( ( $lk['holder'] ?? null ) !== null ) {
		$u->now += Landing::LEASE + 1;
	}
	$g = sc_op( $u, 'PETITION', $account, [ 'block' => $block ] );
	return isset( $g['grant'] ) ? null : $g;
}

/** An ASSUMPTION record (no SITUATION), version 1's arec. */
function sc_arec( string $id, string $prop ): array {
	return [ 'ID' => $id, 'CLASS' => 'ASSUMPTION', 'CITES' => [], 'ASSUMPTIONS' => [], 'PROPOSITION' => $prop, 'REFS' => [] ];
}

/**
 * Version 1's examples/spring/push_1 restated (the file lived outside the archive): SPR-2 the
 * release ASSUMPTION, SPR-3 the RESULT that divides EOM_X by m, SPR-4 the RESULT on the release
 * displacement assuming SPR-2.
 */
function sc_push1(): array {
	return [
		[ 'ID' => 'SPR-2', 'CLASS' => 'ASSUMPTION', 'CITES' => [], 'ASSUMPTIONS' => [],
			'PROPOSITION' => 'At t = 0 the mass is released at rest at x = 0.02 m.', 'REFS' => [ 'x', 't' ] ],
		[ 'ID' => 'SPR-3', 'CLASS' => 'RESULT', 'CITES' => [], 'ASSUMPTIONS' => [],
			'STATEMENT' => 'Dividing EOM_X by m (positive by A_mpos) gives dv/dt = -(k_s/m) x.', 'REGIME' => 'L',
			'EQUATION' => 'm * D(v, t) = -k_s * x',
			'DERIVATION' => [ 'STEPS' => 1, 'TEXT' => 'Divide EOM_X by m.' ],
			'FALSIFIER' => 'A trajectory off the law.', 'FALSIFIER_CLASS' => 'F2', 'REFS' => [ 'm', 'v', 't', 'k_s', 'x' ] ],
		[ 'ID' => 'SPR-4', 'CLASS' => 'RESULT', 'CITES' => [], 'ASSUMPTIONS' => [ 'SPR-2' ],
			'STATEMENT' => 'The displacement at release is 0.02 m.', 'REGIME' => 'L',
			'DERIVATION' => [ 'STEPS' => 1, 'TEXT' => 'Read from SPR-2.' ],
			'FALSIFIER' => 'A release displacement other than 0.02 m.', 'FALSIFIER_CLASS' => 'F3', 'REFS' => [ 'x', 't' ] ],
	];
}

// ================================ the wiki run ================================================

/** The wiki run's state: the mode, the title roots, the UWCs each assertion reads, the causes it traces. */
final class SCW {
	public const ROOT = 'Principia Machina/UWC';
	/** The scenarios' clock starts at 2026-10-05 00:00:00 UTC. */
	public const START = 1791158400;
	/** Not traced since the wiki run's clock step moves the UWC's stored times back (ScWikiLanding::shift); kept for a cause the shift does not cover. */
	public const CLOCK = 'steps the clock; LandJob reads the wall clock';
	public const LANDING = 'rebuilds the landing job (another Calculator, page store or lease); LandJob builds its own from the configuration';
	public const NONCE = 'reads or sets the nonce store; DbNonceStore has take, no peek, and an agent knows its nonce from the answers';

	public const FORK = 'forks a UWC; custos_nonce, custos_seat and custos_ticket are the wiki\'s tables, one for the fork and its source';
	/** The stores are the wiki's. */
	public static bool $wiki = false;
	/** The stores are the files, the wiki run's causes traced. */
	public static bool $plan = false;
	/** The UWC last read (its title root names the pages sc_titles reads). */
	public static ?ScUwc $cur = null;
	/** @var array<int, array{0:ScUwc, 1:?string}> the UWCs read since the last assertion, each with the cause it carried when read */
	public static array $read = [];
	/** @var array<int, array{0:ScUwc, 1:?string}> the reads the last assertion stood on; an assertion of its case that reads no UWC stands on them */
	public static array $last = [];
	/** The last assertion's "<gate> <case>". */
	public static string $lastCase = '';
	/** A read of a nonce store's inside, [the cause, its UWC]: it marks the next assertion's case (SCW::cause). */
	public static ?array $peek = null;
	/** @var array<string, array{0:string, 1:ScUwc}> "<gate> <case>" => the cause of a read of a nonce store's inside in that case, and its UWC */
	public static array $peeked = [];
	/** The run's mark in its title roots. */
	public static string $run = 'R0';
	/** @var array<string, string> a UWC's folder => its title root */
	public static array $roots = [];
	private static int $n = 0;
	/** @var array<string, PageTitles> */
	private static array $titles = [];

	public static function on(): bool {
		return self::$wiki || self::$plan;
	}

	/** A read of $u: recorded for the next assertion with the cause $u carries now. */
	public static function read( ScUwc $u ): void {
		self::$cur = $u;
		self::$read[spl_object_id( $u )] = [ $u, $u->taint ];
	}

	/** The reads of $u since the last assertion, dropped (a fork's copy of its source). */
	public static function forget( ScUwc $u ): void {
		unset( self::$read[spl_object_id( $u )] );
	}

	/** A gate's end: no read stands for the next gate's first assertion. */
	public static function reset(): void {
		self::$cur = null;
		self::$read = self::$last = [];
		self::$lastCase = '';
		self::$peek = null;
	}

	/**
	 * The cause the assertion $id of gate $g carries, recorded when it is made: the first cause one of
	 * the UWCs it reads carried when read (the UWCs read since the assertion before it; with none, the
	 * ones that assertion read when it is of the same case, else none), else the cause of a read of a nonce store's inside made earlier in the
	 * same case on one of those UWCs. Null: the assertion stands on the wiki. The reads are reset.
	 */
	public static function cause( string $g, string $id ): ?string {
		$case = "$g " . SC::caseOf( $id );
		$set = self::$read !== [] ? self::$read : ( $case === self::$lastCase ? self::$last : [] );
		self::$last = $set;
		self::$lastCase = $case;
		self::$read = [];
		if ( self::$peek !== null ) {
			self::$peeked[$case] ??= self::$peek;
			self::$peek = null;
		}
		foreach ( $set as [ , $c ] ) {
			if ( $c !== null ) {
				return $c;
			}
		}
		$p = self::$peeked[$case] ?? null;
		return $p !== null && ( $set[spl_object_id( $p[1] )][0] ?? null ) === $p[1] ? $p[0] : null;
	}

	/**
	 * The answer the wiki run reads back for the ticket $id: its row after the job runner ran, $ran the
	 * runner's response. A ticket left unanswered, or any land job the runner failed (a throw inside
	 * LandJob, a JOB CONTEXT refusal), is a FAIL recorded here, and the answer ["not_run" => why] carries
	 * no refusal, so no scenario reads it as Custos refusing.
	 */
	public static function answer( int $id, ?array $row, array $ran ): array {
		$failed = array_values( array_filter( (array)( $ran['jobs'] ?? [] ), static fn ( $j ): bool => ( $j['status'] ?? '' ) !== 'ok' ) );
		$a = is_array( $row ) && is_string( $row['answer'] ?? null ) ? json_decode( $row['answer'], true ) : null;
		if ( is_array( $a ) && $failed === [] ) {
			return $a;
		}
		$why = is_array( $a ) ? "a land job failed while the job runner ran the ticket $id" : "the ticket $id has no answer after the job runner ran";
		SC::ok( "NOT-RUN.t$id", false, "the wiki's job runner answers the ticket ($why)", json_encode( [ 'ticket' => $row, 'failed' => $failed ] ) );
		return [ 'not_run' => $why, 'detail' => json_encode( $row ) ];
	}

	/** The title root of the folder $dir, a new one the first time. */
	public static function root( string $dir ): string {
		return self::$roots[$dir] ??= self::next();
	}

	/** A new title root for the folder $dir (a UWC seeded again under a folder already used). */
	public static function fresh( string $dir ): string {
		return self::$roots[$dir] = self::next();
	}

	private static function next(): string {
		return 'Principia Machina/Scenarios/' . self::$run . '/U' . ( ++self::$n );
	}

	public static function titles( string $root ): PageTitles {
		return self::$titles[$root] ??= new PageTitles( $root, 'Principia Machina' );
	}
}

/**
 * A UWC of the wiki run and the plan run: its members as sc_open's, read through __get (which makes it
 * a read for the next assertion, SCW::read) and set through __set; setting its landing job traces the
 * cause. A step of its clock is no cause: on the wiki run it moves the UWC's stored times back by the
 * step (ScWikiLanding::shift, the member "wiki"), so the landing job, which reads the wall clock, sees
 * them as the step intends; a landing job the scenario rebuilt reads the scenario's clock, so nothing
 * is moved while it is the UWC's; in the plan run the clock is the landing job's.
 */
final class ScUwc extends stdClass {
	/** The first cause traced on this UWC, or null. */
	public ?string $taint = null;
	private array $m;

	public function __construct( array $m ) {
		$this->m = $m;
	}

	/** The stores, the landing job and the ops, set once by sc_open. */
	public function init( array $m ): void {
		$this->m = $m + $this->m;
		foreach ( [ 'store', 'nonces' ] as $k ) {
			$x = $this->m[$k] ?? null;
			if ( $x instanceof ScStore || $x instanceof ScNonces ) {
				$this->m[$k]->u = $this;
			}
		}
	}

	public function __get( string $k ): mixed {
		SCW::read( $this );
		return $this->m[$k] ?? null;
	}

	public function __set( string $k, mixed $v ): void {
		SCW::$cur = $this;
		if ( $k === 'now' ) {
			// the wiki's landing job alone reads the wall clock: one the scenario rebuilt reads this clock
			$w = $this->m['wiki'] ?? null;
			if ( $w instanceof ScWikiLanding && ( $this->m['landing'] ?? null ) === $w ) {
				$w->shift( (int)$v - (int)$this->m['now'] );
			}
		} elseif ( $k === 'landing' ) {
			$this->taint( SCW::LANDING );
		}
		$this->m[$k] = $v;
	}

	public function __isset( string $k ): bool {
		return isset( $this->m[$k] );
	}

	/** A cause on this UWC: the reads of it from now on carry it (SCW::read). */
	public function taint( string $cause ): void {
		$this->taint ??= $cause;
		SCW::$cur = $this;
	}

	/** One op's second (sc_tick), not a step of the clock. */
	public function tick(): void {
		$this->m['now']++;
	}

	/** The clock set by the scenarios' driver (the seed's minute before the start), not a step. */
	public function at( int $now ): void {
		$this->m['now'] = $now;
	}

	/** The clock as the plan run's landing job reads it. */
	public function clock(): int {
		return $this->m['now'];
	}

	public function root(): string {
		return $this->m['root'] ?? SCW::ROOT;
	}
}

/** The page store of a traced UWC: the store it wraps, its titles listed, its inside traced. */
final class ScStore implements PageStore {
	public ?ScUwc $u = null;

	public function __construct( private PageStore $in, private string $root = '' ) {
	}

	public function get( string $title ): ?string {
		$this->u !== null && SCW::read( $this->u );
		return $this->in->get( $title );
	}

	public function exists( string $title ): bool {
		$this->u !== null && SCW::read( $this->u );
		return $this->in->exists( $title );
	}

	public function put( string $title, string $text, string $summary ): void {
		$this->in->put( $title, $text, $summary );
	}

	public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
		return $this->in->casPut( $title, $expected, $text, $summary, $actor );
	}

	public function appendAs( string $title, string $line, string $summary, string $actor ): string {
		return $this->in->appendAs( $title, $line, $summary, $actor );
	}

	/** Every title the store holds; on the wiki, every page under the UWC's title root, from the primary. */
	public function titles(): array {
		$this->u !== null && SCW::read( $this->u );
		if ( !( $this->in instanceof \Custos\MwStore ) ) {
			return $this->in->titles();
		}
		$db = \MediaWiki\MediaWikiServices::getInstance()->getConnectionProvider()->getPrimaryDatabase();
		$key = str_replace( ' ', '_', $this->root ) . '/';
		$rows = $db->newSelectQueryBuilder()->select( 'page_title' )->from( 'page' )
			->where( [ 'page_namespace' => 0, $db->expr( 'page_title', \Wikimedia\Rdbms\IExpression::LIKE,
				new \Wikimedia\Rdbms\LikeValue( $key, $db->anyString() ) ) ] )
			->orderBy( 'page_title' )->caller( __METHOD__ )->fetchFieldValues();
		return array_map( static fn ( $t ): string => str_replace( '_', ' ', (string)$t ), $rows );
	}

	/** A hand edit of $title: on the wiki a save by Custos, of the same text. */
	public function tamper( string $title, string $text ): void {
		if ( $this->in instanceof \Custos\MwStore ) {
			$this->in->put( $title, $text, 'a hand edit' );
		} else {
			$this->in->tamper( $title, $text );
		}
	}

	public function __isset( string $k ): bool {
		return $k === 'revisions';
	}

	/** FileStore's revisions; on the wiki each page's revisions, oldest first, read from MediaWiki (ScRevisions). */
	public function __get( string $k ): mixed {
		if ( $k !== 'revisions' ) {
			return null;
		}
		$this->u !== null && SCW::read( $this->u );
		return $this->in instanceof \Custos\MwStore ? new ScRevisions() : $this->in->revisions;
	}
}

/** A wiki page's revisions as FileStore lists them: per title, [ "actor" => the user's name, "summary" => its comment ], oldest first. */
final class ScRevisions implements ArrayAccess {
	public function offsetExists( mixed $title ): bool {
		return $this->offsetGet( $title ) !== [];
	}

	public function offsetGet( mixed $title ): array {
		$services = \MediaWiki\MediaWikiServices::getInstance();
		$page = $services->getPageStore()->getPageByText( (string)$title );
		if ( $page === null || !$page->exists() ) {
			return [];
		}
		$db = $services->getConnectionProvider()->getPrimaryDatabase();
		$rows = $db->newSelectQueryBuilder()->select( [ 'actor_name', 'comment_text' ] )->from( 'revision' )
			->join( 'actor', null, 'actor_id = rev_actor' )->join( 'comment', null, 'comment_id = rev_comment_id' )
			->where( [ 'rev_page' => $page->getId() ] )->orderBy( 'rev_id' )->caller( __METHOD__ )->fetchResultSet();
		$o = [];
		foreach ( $rows as $r ) {
			$o[] = [ 'actor' => (string)$r->actor_name, 'summary' => (string)$r->comment_text ];
		}
		return $o;
	}

	public function offsetSet( mixed $title, mixed $v ): void {
		throw new LogicException( 'the wiki\'s revisions are read only' );
	}

	public function offsetUnset( mixed $title ): void {
		throw new LogicException( 'the wiki\'s revisions are read only' );
	}
}

/**
 * The nonces of a traced UWC as an agent knows them: on the wiki the nonce the last answer to the
 * account on the prefix carried (ScNonces::saw; the table custos_nonce, keyed as these are, is the
 * landing job's); in the plan run the file store's. A read of the store (peek) or a set (tamper) is traced.
 * A set or a take by a landing job the scenario rebuilt in its own process (sc_reland, ic_reland) is the
 * scenario's own act on the store: on the wiki it goes to the wiki's table ($db, DbNonceStore), the
 * nonce it puts is the one that landing's answer carries (known), and it taints the UWC with the nonce
 * cause (SCW::NONCE), as it does in the plan run; it throws nothing.
 */
final class ScNonces implements NonceStore {
	public ?ScUwc $u = null;
	/** @var array<string, string> "<account>\n<prefix>" => the nonce the last answer carried */
	private static array $seen = [];

	public function __construct( private ?FileNonceStore $in, private ?NonceStore $db = null ) {
	}

	public function put( string $account, string $prefix, string $nonce, int $issued ): void {
		$this->u?->taint( SCW::NONCE );
		if ( $this->in !== null ) {
			$this->in->put( $account, $prefix, $nonce, $issued );
			return;
		}
		$this->db?->put( $account, $prefix, $nonce, $issued );
		self::$seen["$account\n$prefix"] = $nonce;
	}

	public function take( string $account, string $prefix ): ?string {
		$this->u?->taint( SCW::NONCE );
		if ( $this->in !== null ) {
			return $this->in->take( $account, $prefix );
		}
		unset( self::$seen["$account\n$prefix"] );
		return $this->db?->take( $account, $prefix );
	}

	/** The nonce an agent answers with (not traced). */
	public function known( string $account, string $prefix ): ?string {
		return $this->in !== null ? $this->in->peek( $account, $prefix ) : ( self::$seen["$account\n$prefix"] ?? null );
	}

	/** An answer to $account on $prefix: the nonce it carries, the next one known. */
	public static function saw( string $account, string $prefix, array $answer ): void {
		if ( is_string( $answer['challenge'] ?? null ) ) {
			self::$seen["$account\n$prefix"] = $answer['challenge'];
		}
	}

	/** A read of the store (traced: the reads of this UWC after it, in the case of the next assertion; on the wiki the nonce the answers carried). */
	public function peek( string $account, string $prefix ): ?string {
		if ( $this->u !== null ) {
			SCW::read( $this->u );
			SCW::$peek ??= [ SCW::NONCE, $this->u ];
		}
		return $this->known( $account, $prefix );
	}

	/**
	 * The nonce the store itself holds for $account on $prefix, traced as peek is: on the wiki the row of
	 * custos_nonce (read, never taken), where peek answers the nonce the answers carried; off the wiki the file.
	 */
	public function stored( string $account, string $prefix ): ?string {
		if ( $this->u !== null ) {
			SCW::read( $this->u );
			SCW::$peek ??= [ SCW::NONCE, $this->u ];
		}
		if ( $this->in !== null ) {
			return $this->in->peek( $account, $prefix );
		}
		if ( $this->db === null ) {
			return null;
		}
		$nonce = \MediaWiki\MediaWikiServices::getInstance()->getDBLoadBalancer()
			->getConnection( \Wikimedia\Rdbms\ILoadBalancer::DB_PRIMARY, [], false, \Wikimedia\Rdbms\ILoadBalancer::CONN_TRX_AUTOCOMMIT )
			->newSelectQueryBuilder()
			->select( 'cn_nonce' )
			->from( 'custos_nonce' )
			->where( [ 'cn_account' => $account, 'cn_prefix' => $prefix ] )
			->caller( __METHOD__ )
			->fetchField();
		return is_string( $nonce ) ? $nonce : null;
	}

	public function tamper( string $account, string $prefix, string $nonce ): void {
		$this->u?->taint( SCW::NONCE );
		if ( $this->in !== null ) {
			$this->in->tamper( $account, $prefix, $nonce );
		}
	}
}

/**
 * The landing job of a wiki run's UWC: the ticket's LandJob, pushed by Ops, run by the job runner as
 * runJobs --type custosLand runs it (in this process: JobRunner::run), with $wgCustosUwcRoot the UWC's
 * title root; the ticket's answer read back from custos_ticket (SCW::answer: unanswered, or a job failed, is a FAIL).
 * A step of the UWC's clock (shift) moves its stored times back by the step: production code reads the
 * wall clock, untouched.
 */
final class ScWikiLanding {
	/** @var array<int, string> the tickets this UWC's ops wrote, each with its account */
	private array $tickets = [];
	/** @var ?Closure(string, array): int a statement over the tables, "{<table>}" its table and "?" its parameters; null: the wiki's */
	private ?Closure $exec;

	public function __construct( private ScUwc $u, ?Closure $exec = null ) {
		$this->exec = $exec;
	}

	public function run( int $id ): array {
		$GLOBALS['wgCustosUwcRoot'] = $this->u->root();
		$ran = \MediaWiki\MediaWikiServices::getInstance()->getJobRunner()->run( [ 'type' => \Custos\LandJob::TYPE, 'maxJobs' => 100, 'maxTime' => 600 ] );
		$row = ( new \Custos\DbTicketStore() )->get( $id );
		if ( is_array( $row ) ) {
			$this->saw( $id, (string)$row['account'] );
		}
		$a = SCW::answer( $id, is_array( $row ) ? $row : null, is_array( $ran ) ? $ran : [] );
		if ( !isset( $a['not_run'] ) ) {
			ScNonces::saw( (string)$row['account'], (string)$row['prefix'], $a );
		}
		return $a;
	}

	/** The ticket $id written by this UWC's op for $account. */
	public function saw( int $id, string $account ): void {
		$this->tickets[$id] = $account;
	}

	/**
	 * The UWC's clock stepped by $seconds: its stored times moved back by $seconds, for this UWC alone
	 * (its title root, its tickets, the accounts of its tickets on its prefix): the lock page's grant
	 * and expiry (a held lock, rewritten by PageTexts::lock with the same holder and block), and its
	 * rows of custos_ticket (ct_created, ct_done where set), custos_nonce (cn_issued) and custos_seat
	 * (cs_since where set), one statement per table. custos_nonce and custos_seat are keyed by account
	 * (and prefix), so a row an account shares with another UWC moves with it (the fork's cause).
	 */
	public function shift( int $seconds ): void {
		if ( $seconds === 0 ) {
			return;
		}
		if ( $seconds < 0 ) {
			throw new LogicException( 'the scenario clock steps forward only: a shift moves stored times back by a positive step, not ' . $seconds );
		}
		$px = (string)$this->u->px;
		$store = $this->u->store;
		$title = SCW::titles( $this->u->root() )->lock( $px );
		$text = $store->get( $title );
		$lk = $text === null ? null : json_decode( (string)PageTexts::readLock( $text ), true );
		if ( is_array( $lk ) && ( $lk['holder'] ?? null ) !== null ) {
			$back = static fn ( string $t ): string => gmdate( 'Y-m-d\TH:i:s\Z', (int)strtotime( $t ) - $seconds );
			$store->put( $title, PageTexts::lock( $px, (string)$lk['holder'], $back( (string)$lk['granted_at'] ), $back( (string)$lk['expires_at'] ),
				(string)$lk['block'], sc_canon() ), 'the scenario\'s clock stepped' );
		}
		$exec = $this->exec ?? self::wiki();
		$s = $seconds;
		$ids = array_keys( $this->tickets );
		$accounts = array_values( array_unique( $this->tickets ) );
		if ( $ids !== [] ) {
			// ct_created and ct_done are MediaWiki timestamps (YYYYMMDDHHMMSS); SQLite's strftime moves them
			$at = static fn ( string $c ): string => "strftime('%Y%m%d%H%M%S', substr($c, 1, 4) || '-' || substr($c, 5, 2) || '-' || substr($c, 7, 2) || ' ' || "
				. "substr($c, 9, 2) || ':' || substr($c, 11, 2) || ':' || substr($c, 13, 2), ?)";
			$mod = sprintf( '%+d seconds', -$s );
			$exec( 'UPDATE {custos_ticket} SET ct_created = ' . $at( 'ct_created' ) . ', ct_done = CASE WHEN ct_done IS NULL THEN NULL ELSE '
				. $at( 'ct_done' ) . ' END WHERE ct_id IN (' . implode( ', ', array_map( 'intval', $ids ) ) . ')', [ $mod, $mod ] );
		}
		if ( $accounts !== [] ) {
			$in = implode( ', ', array_fill( 0, count( $accounts ), '?' ) );
			$exec( "UPDATE {custos_nonce} SET cn_issued = cn_issued - $s WHERE cn_prefix = ? AND cn_account IN ($in) AND cn_issued >= $s",
				array_merge( [ $px ], $accounts ) );
			$exec( "UPDATE {custos_seat} SET cs_since = cs_since - $s WHERE cs_account IN ($in) AND cs_since > 0 AND cs_since >= $s", $accounts );
		}
	}

	/** The statement over the wiki's tables: the primary's autocommit connection, as DbNonceStore's; SQLite (the rehearsal wiki) alone. */
	private static function wiki(): Closure {
		$db = \MediaWiki\MediaWikiServices::getInstance()->getDBLoadBalancer()
			->getConnection( \Wikimedia\Rdbms\ILoadBalancer::DB_PRIMARY, [], false, \Wikimedia\Rdbms\ILoadBalancer::CONN_TRX_AUTOCOMMIT );
		if ( $db->getType() !== 'sqlite' ) {
			throw new LogicException( 'the scenario clock\'s shift is written for SQLite, the rehearsal wiki\'s database, not ' . $db->getType() );
		}
		return static function ( string $sql, array $params ) use ( $db ): int {
			$sql = (string)preg_replace_callback( '/\{(\w+)\}/', static fn ( array $m ): string => $db->tableName( $m[1] ), $sql );
			$i = 0;
			$sql = (string)preg_replace_callback( '/\?/', static function () use ( $db, $params, &$i ): string {
				return (string)$db->addQuotes( $params[$i++] );
			}, $sql );
			$db->query( $sql, __METHOD__ );
			return $db->affectedRows();
		};
	}

	/** The statement over a PDO handle (the self-test's SQLite tables, made from sql/sqlite/). */
	public static function pdo( PDO $pdo ): Closure {
		return static function ( string $sql, array $params ) use ( $pdo ): int {
			$st = $pdo->prepare( (string)preg_replace( '/\{(\w+)\}/', '$1', $sql ) );
			$st->execute( $params );
			return $st->rowCount();
		};
	}
}
