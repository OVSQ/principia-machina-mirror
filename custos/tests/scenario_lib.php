<?php
/**
 * The scenarios' driver: a UWC seeded as Custos:SeedUwc writes it, over FileStore, FileTicketStore,
 * FileSeatStore, FileNonceStore and FileCertificateStore, run by the landing job on the built pcalc; each op a ticket as
 * Ops writes it, run by Landing, its answer read back. A stepping clock (whole seconds).
 */

declare( strict_types=1 );
require_once __DIR__ . '/bootstrap.php';

use Custos\Blocks;
use Custos\Calculator;
use Custos\CertificateStore;
use Custos\Challenge;
use Custos\Landing;
use Custos\MemMeterStore;
use Custos\Ops;
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

/** The clone's root, the built pcalc, the scratch folder. */
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
	return $t ??= new PageTitles( 'Principia Machina/UWC', 'Principia Machina' );
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
	$form = $px . ( $master ? '-m' : '' ) . ( $access === null ? '' : '-closed-' . md5( json_encode( $access ) ) );
	$start = 1791158400;
	if ( !isset( $seeded[$form] ) ) {
		$seeded[$form] = sc_scratch() . "/seed-$form";
		$calc = sc_calc();
		$pt = sc_titles();
		$draft = sc_draft();
		$canon = $calc->call( 'canonical', 'canonical_json', '{"value":' . $draft . '}' )['value'];
		$ra = $calc->call( 'zone', 'digest_research_assembly_of', '{"tfk":' . $draft . '}' )['value'];
		$seedStore = new FileStore( $seeded[$form] . '/pages' );
		$seed = new PageWriter( $seedStore, $pt );
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
			$seedStore->put( $pt->accessList( $px ), Blocks::render( Landing::ACCESS, json_encode( $access, SC_JSON ) ) . "\n", 'seed' );
		}
		if ( $master ) {
			$m = sc_open( $seeded[$form], $px, $start - 60 );
			$a = sc_push( $m, [ sc_arec( "$px-1", 'The place of version 1\'s MASTER record.' ) ], 'Agent M', 'B0' );
			$r = sc_op( $m, 'RELEASE', 'Agent M', [ 'block' => 'B0' ] );
			if ( array_column( $a['landed'] ?? [], 'id' ) !== [ "$px-1" ] || !isset( $r['released'] ) ) {
				throw new RuntimeException( "the MASTER's stand-in did not land on $px: " . json_encode( [ $a, $r ] ) );
			}
		}
	}
	sc_copy( $seeded[$form], $dir );
	return sc_open( $dir, $px, $start );
}

/** A copy of $u under $tag: its pages, tickets, seats and nonces, its clock. */
function sc_fork( stdClass $u, string $tag ): stdClass {
	$dir = sc_scratch() . "/$tag";
	sc_copy( $u->dir, $dir );
	return sc_open( $dir, $u->px, $u->now );
}

function sc_copy( string $from, string $to ): void {
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
		foreach ( range( 'A', 'Z' ) as $k ) {
			$certs->put( [ 'agent' => "Agent $k", 'sponsor' => "Sponsor $k", 'd_is' => str_repeat( 'd', 64 ), 'd_prompt' => str_repeat( 'e', 64 ),
				'family' => 'test family', 'model' => 'test model', 'state' => CertificateStore::ACTIVE ] );
		}
	}
	return $certs;
}

/** The stores, the landing job and the ops over the files under $dir. */
function sc_open( string $dir, string $px, int $now ): stdClass {
	$u = new stdClass();
	$u->dir = $dir;
	$u->px = $px;
	$u->now = $now;
	$u->store = new FileStore( "$dir/pages" );
	$u->tickets = new FileTicketStore( "$dir/tickets" );
	$u->seats = new FileSeatStore( "$dir/seats.json" );
	$u->nonces = new FileNonceStore( "$dir/nonces.json" );
	$u->certs = sc_certs( "$dir/certs.json" );
	$conf = [ 'tps' => '0.4.0', 'd_is' => str_repeat( 'd', 64 ), 'digest' => Calculator::digestOf( sc_built() ), 'poll_after' => 30,
		'governor_off' => true ];
	$u->landing = new Landing( sc_calc(), $u->store, sc_titles(), $u->tickets, $u->seats, $u->certs, $conf, static function () use ( $u ): int {
		return $u->now;
	}, static fn (): array => [ 0, 1 ], nonces: $u->nonces, meter: new MemMeterStore() );
	$u->ops = new Ops( $u->tickets, static function ( int $id ): void {
	} );
	return $u;
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
	$nonce = $u->nonces->peek( $account, $u->px );
	if ( $op === 'PUSH' && !array_key_exists( 'challenge_response', $params ) && $nonce !== null ) {
		$params['challenge_response'] = Challenge::response( sc_calc(), $nonce )[1];
	}
	try {
		$id = $u->ops->run( $op, $u->px, $account, $params )['ticket'];
	} catch ( \Custos\Refusal $e ) {
		return [ 'refused' => 'OPS', 'code' => $e->what, 'detail' => $e->getMessage() ];
	}
	$u->now++;
	return $u->landing->run( $id );
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
