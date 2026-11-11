<?php
/**
 * scenarios.php: version 1's landing gates a1, a2, b1, b1-fault, b1-range, b1-inc4 and b1-repro
 * replayed as Custos scenarios, over FileStore, FileTicketStore, FileSeatStore, FileNonceStore and
 * the built pcalc (scenario_lib.php).
 *
 *   php custos/tests/scenarios.php [a1|a2|b1|b1-fault|b1-range|b1-inc4|b1-repro ...]
 *
 * Each of version 1's assertions keeps its place, numbered as version 1 numbered it (a1 by its own
 * numbers; a2, b1, b1-fault, b1-range, b1-inc4 and b1-repro by case and order within the case,
 * A.1, L3.4, FS-4.2, R2.6, I3.4, R5.12). Each is one of:
 *   PASS       version 1's expectation met, its words differing only in spelling (a grant is a time,
 *              not a count; "verify" is each landed record's record_check at stage LANDED, which
 *              recomputes its digest, and the badge's Research Assembly digest recomputed; the
 *              accounts are Agent A, B, C where version 1 named its test accounts);
 *   DIVERGENT  an expectation Custos does not meet, by a cause listed in DIVERGENCES.md with Custos's
 *              answer; the scenario checks that Custos still answers so, and a row that stops
 *              applying fails;
 *   DEFECT     a landing version 1 refused that Custos accepts: a soundness defect, never recorded
 *              as a divergence; counted as a failure;
 *   FAIL       anything else.
 * Prints each gate's line "<gate>: <p>/<n>, <d> divergent[, <x> defects]" and
 * "scenarios: ALL PASS <p>/<n>, <d> divergent" (or FAIL), the divergent count compared row for row
 * with DIVERGENCES.md. Skipped with its reason when the clone has no built pcalc.
 *
 *   php custos/tests/scenarios.php --wiki-plan [<gate> ...]
 *   php maintenance/run.php <clone>/custos/tests/scenarios.php     (the rehearsal wiki: rehearsal.sh)
 *
 * The wiki run (scenario_lib.php, SCW) replays the same gates over the wiki's stores with real jobs and
 * prints "scenarios-wiki: ALL PASS <p>/<n>, <d> divergent (<w> wiki-only)": a PASS or a DIVERGENT
 * assertion made on a UWC traced off the wiki (its landing job rebuilt, its nonce store set or read
 * earlier in the case, the UWC forked; a step of its clock moves its stored times back instead,
 * ScWikiLanding::shift), the cause recorded at the assertion from the
 * UWCs it reads, is WIKI-DIV, counted in d and in w, its case a wiki-only row of DIVERGENCES.md with
 * its count; a FAIL or a DEFECT is never relabelled, and a ticket the wiki's job runner leaves
 * unanswered is a FAIL. The plan run (--wiki-plan) traces the same causes over the file-backed
 * stores and prints the wiki-only rows, "scenarios-plan: ...".
 *
 *   php custos/tests/scenarios.php --self-test
 *
 * The tracing's own checks, no wiki needed (the built pcalc writes S5's and S7's held locks): "scenarios-self-test: ALL PASS <p>/<n>".
 */

declare( strict_types=1 );
require_once __DIR__ . '/scenario_lib.php';

use Custos\Blocks;
use Custos\Landing;
use Custos\PageTexts;
use Custos\PageTitles;
use Custos\PageWriter;

/** The gates replayed, in order. */
const SC_GATES = [ 'a1', 'a2', 'b1', 'b1-fault', 'b1-range', 'b1-inc4', 'b1-repro' ];
/**
 * Each gate's number of assertions, the same in every run (file-backed, plan and wiki): a gate whose run counts
 * another number made an assertion that never ran (a conditional path, a return inside a gate) or one not
 * recorded here, and fails the report whatever its PASS and DIVERGENT counts. A changed gate updates its line.
 */
const SC_COUNTS = [ 'a1' => 30, 'a2' => 123, 'b1' => 69, 'b1-fault' => 63, 'b1-range' => 28, 'b1-inc4' => 54, 'b1-repro' => 104 ];

/** The scenarios' tally: per gate, passes, divergences, defects, failures. */
final class SC {
	public static string $gate = '';
	/** @var array<string, array{pass:int, div:int, defect:int, fail:int}> */
	public static array $n = [];
	/** @var string[] */
	public static array $log = [];
	/** @var string[] the divergent assertions, "<gate> <id>" */
	public static array $divs = [];
	/** The gates a run was asked for (sc_run), so a gate that never registered is counted, not lost. */
	public static array $asked = [];
	/** @var array<int, array{0:string, 1:string, 2:string, 3:int, 4:string, 5:?string}> the wiki run's and the plan run's assertions: gate, id, kind, log line, what, the cause recorded at it */
	public static array $rec = [];

	public static function gate( string $g ): void {
		self::$gate = $g;
		self::$n[$g] = [ 'pass' => 0, 'div' => 0, 'defect' => 0, 'fail' => 0 ];
	}

	private static function line( string $kind, string $id, string $what, string $detail = '' ): void {
		self::$log[] = sprintf( '%-9s %s %s %s', $kind, self::$gate, $id, $what ) . ( $detail !== '' ? "\n          $detail" : '' );
		if ( SCW::on() ) {
			// the cause of the UWCs this assertion reads, recorded now, never later
			self::$rec[] = [ self::$gate, $id, $kind, count( self::$log ) - 1, $what, SCW::cause( self::$gate, $id ) ];
		}
	}

	/** How an assertion of $kind with the cause $cause recorded at it is shown: a PASS or a DIVERGENT traced off the wiki is WIKI-DIV; a FAIL or a DEFECT never. */
	public static function shown( string $kind, ?string $cause ): string {
		return $cause !== null && ( $kind === 'PASS' || $kind === 'DIVERGENT' ) ? 'WIKI-DIV' : $kind;
	}

	/**
	 * The wiki run's and the plan run's tally from SC::$rec: each gate's counts (SC::$n) with its
	 * wiki-only count, each WIKI-DIV line relabelled with its cause. Returns the wiki-only cases,
	 * "<gate> <case>" => [n, cause], and the assertions shown WIKI-DIV, "<gate> <id>" => true.
	 */
	public static function tally(): array {
		$kinds = [ 'PASS' => 'pass', 'DIVERGENT' => 'div', 'DEFECT' => 'defect', 'FAIL' => 'fail' ];
		foreach ( self::$n as $g => $_ ) {
			self::$n[$g] = [ 'pass' => 0, 'div' => 0, 'defect' => 0, 'fail' => 0, 'wiki' => 0 ];
		}
		$wcases = $off = [];
		foreach ( self::$rec as [ $g, $id, $kind, $li, $what, $cause ] ) {
			if ( self::shown( $kind, $cause ) !== 'WIKI-DIV' ) {
				self::$n[$g][$kinds[$kind]]++;
				continue;
			}
			$case = self::caseOf( $id );
			self::$n[$g]['wiki']++;
			$wcases["$g $case"] = [ 'n' => ( $wcases["$g $case"]['n'] ?? 0 ) + 1, 'cause' => $wcases["$g $case"]['cause'] ?? $cause ];
			$off["$g $id"] = true;
			self::$log[$li] = sprintf( '%-9s %s %s %s', 'WIKI-DIV', $g, $id, $what ) . "\n          cause: not run on the wiki: $cause";
		}
		return [ $wcases, $off ];
	}

	/** An assertion's case: its number up to the last dot (L3.4 -> L3, FS-4.2 -> FS-4, 3.2m -> 3). */
	public static function caseOf( string $id ): string {
		$i = strrpos( $id, '.' );
		return $i === false ? $id : substr( $id, 0, $i );
	}

	/** A gate stopped by a throw (the wiki run goes on with the next gate). */
	public static function thrown( Throwable $e ): void {
		self::ok( 'THROWN', false, 'the gate stopped', get_class( $e ) . ': ' . $e->getMessage() . ' at ' . basename( $e->getFile() ) . ':' . $e->getLine() );
	}

	/** Version 1's expectation, met. */
	public static function ok( string $id, bool $c, string $what, string $detail = '' ): void {
		self::$n[self::$gate][$c ? 'pass' : 'fail']++;
		self::line( $c ? 'PASS' : 'FAIL', $id, $what, $c ? '' : $detail );
	}

	/**
	 * Version 1's expectation, not met by Custos for $cause; $still: Custos answers as DIVERGENCES.md
	 * records. A row that no longer applies is a failure.
	 */
	public static function div( string $id, bool $still, string $what, string $cause, string $detail = '' ): void {
		if ( !$still ) {
			self::ok( $id, false, "$what (the divergence no longer applies: $cause)", $detail );
			return;
		}
		self::$n[self::$gate]['div']++;
		self::$divs[] = self::$gate . ' ' . $id;
		self::line( 'DIVERGENT', $id, $what, "cause: $cause" );
	}

	/** A landing version 1 refused, which Custos accepts. */
	public static function defect( string $id, string $what, string $detail ): void {
		self::$n[self::$gate]['defect']++;
		self::line( 'DEFECT', $id, $what, $detail );
	}

	/**
	 * Version 1 refused the request: Custos refusing it, nothing written, meets it (the refusal's words
	 * may differ); Custos landing it is a DEFECT. $snap: the pages before the request.
	 */
	public static function refused( string $id, array $a, array $before, array $after, string $what ): void {
		if ( isset( $a['landed'] ) ) {
			self::defect( $id, $what, 'Custos landed it: ' . json_encode( $a['landed'] ) );
			return;
		}
		self::ok( $id, isset( $a['refused'] ) && $before === $after, $what . ' [Custos: ' . ( $a['refused'] ?? '?' ) . ']', json_encode( $a ) );
	}

	/**
	 * The lines, each gate's count and the result. $rows: DIVERGENCES.md's rows "<gate> <id>"; $wikiRows:
	 * its wiki-only rows "<gate> <case> <count>", checked in the wiki run and the plan run, where a PASS
	 * or a DIVERGENT assertion traced off the wiki when it was made counts divergent (wiki-only) and a
	 * FAIL or a DEFECT counts as itself (SC::tally).
	 */
	/**
	 * The gates whose count of assertions differs from SC_COUNTS, each "<gate> <counted> of <recorded>";
	 * a gate SC_COUNTS does not name (the self-test's) is not checked.
	 */
	public static function countsOff( array $n, array $want = SC_COUNTS, array $asked = [] ): array {
		$off = [];
		foreach ( $asked as $g ) {
			if ( !isset( $n[$g] ) && isset( $want[$g] ) ) {
				$off[] = "$g 0 of {$want[$g]}";
			}
		}
		foreach ( $n as $g => $c ) {
			$gn = $c['pass'] + $c['div'] + $c['defect'] + $c['fail'] + ( $c['wiki'] ?? 0 );
			if ( isset( $want[$g] ) && $gn !== $want[$g] ) {
				$off[] = "$g $gn of {$want[$g]}";
			}
		}
		return $off;
	}

	public static function report( array $rows, array $wikiRows = [] ): int {
		$on = SCW::on();
		$label = SCW::$wiki ? 'scenarios-wiki' : ( SCW::$plan ? 'scenarios-plan' : 'scenarios' );
		$wcases = [];
		if ( $on ) {
			[ $wcases, $offs ] = self::tally();
			$off = static fn ( string $r ): bool => !isset( $offs[$r] );
			self::$divs = array_values( array_filter( self::$divs, $off ) );
			$rows = array_values( array_filter( $rows, $off ) );
		}
		foreach ( self::$log as $l ) {
			echo $l, "\n";
		}
		$p = $n = $d = $x = $w = 0;
		$parts = [];
		foreach ( self::$n as $g => $c ) {
			$cw = $c['wiki'] ?? 0;
			$gn = $c['pass'] + $c['div'] + $c['defect'] + $c['fail'] + $cw;
			echo "$g: {$c['pass']}/$gn, ", $c['div'] + $cw, ' divergent', $on ? " ($cw wiki-only)" : '', $c['defect'] > 0 ? ", {$c['defect']} defects" : '',
				$c['fail'] > 0 ? ", {$c['fail']} failed" : '', "\n";
			$parts[] = "$g {$c['pass']}/$gn";
			$p += $c['pass'];
			$n += $gn;
			$d += $c['div'] + $cw;
			$w += $cw;
			$x += $c['defect'] + $c['fail'];
		}
		// Each gate's count of assertions as recorded (SC_COUNTS): an assertion that never ran lowers n and p together.
		$short = self::countsOff( self::$n, SC_COUNTS, self::$asked );
		if ( $short !== [] ) {
			echo 'assertions counted other than recorded (SC_COUNTS): ', implode( '; ', $short ), "\n";
		}
		// DIVERGENCES.md: one row per divergent assertion of the gates run, and no other.
		$want = array_values( array_filter( $rows, static fn ( string $r ): bool => isset( self::$n[explode( ' ', $r )[0]] ) ) );
		$have = self::$divs;
		sort( $want );
		sort( $have );
		$rowsOk = $want === $have;
		if ( !$rowsOk ) {
			echo 'DIVERGENCES.md rows not divergent here: ', implode( '; ', array_diff( $want, $have ) ) ?: 'none', "\n";
			echo 'divergent here, no row in DIVERGENCES.md: ', implode( '; ', array_diff( $have, $want ) ) ?: 'none', "\n";
		}
		if ( $on ) {
			// the wiki-only rows: one per case traced off the wiki, with its count of assertions
			ksort( $wcases );
			$haveW = [];
			foreach ( $wcases as $k => $c ) {
				$haveW[] = "$k {$c['n']}";
				if ( SCW::$plan ) {
					[ $g, $case ] = explode( ' ', $k, 2 );
					echo "| wiki | $g | $case | {$c['n']} | {$c['cause']} |\n";
				}
			}
			$wantW = array_values( array_filter( $wikiRows, static fn ( string $r ): bool => isset( self::$n[explode( ' ', $r )[0]] ) ) );
			sort( $wantW );
			sort( $haveW );
			if ( $wantW !== $haveW ) {
				$rowsOk = false;
				echo 'DIVERGENCES.md wiki-only rows not traced here: ', implode( '; ', array_diff( $wantW, $haveW ) ) ?: 'none', "\n";
				echo 'traced here, no wiki-only row in DIVERGENCES.md: ', implode( '; ', array_diff( $haveW, $wantW ) ) ?: 'none', "\n";
			}
		}
		echo "$label: ", implode( ' ', $parts ), ", $d divergent\n";
		$all = $x === 0 && $rowsOk && $short === [];
		echo "$label: ", $all ? 'ALL PASS' : 'FAIL', " $p/$n, $d divergent", $on ? " ($w wiki-only)" : '', $all ? '' : ", $x defects or failures",
			$rowsOk ? '' : ', DIVERGENCES.md rows differ', $short === [] ? '' : ', assertions not run as recorded', "\n";
		return $all ? 0 : 1;
	}
}

/** DIVERGENCES.md's rows, "<gate> <number>", from its table. */
function sc_rows(): array {
	$t = (string)@file_get_contents( __DIR__ . '/DIVERGENCES.md' );
	preg_match_all( '/^\| (a1|a2|b1|b1-fault|b1-range|b1-inc4|b1-repro) \| ([A-Za-z0-9.-]+) \|/m', $t, $m, PREG_SET_ORDER );
	return array_map( static fn ( array $x ): string => $x[1] . ' ' . $x[2], $m );
}

/** DIVERGENCES.md's wiki-only rows, "<gate> <case> <count>", from its table of the wiki run. */
function sc_wiki_rows(): array {
	$t = (string)@file_get_contents( __DIR__ . '/DIVERGENCES.md' );
	preg_match_all( '/^\| wiki \| (a1|a2|b1|b1-fault|b1-range|b1-inc4|b1-repro) \| ([A-Za-z0-9.-]+) \| ([0-9]+) \|/m', $t, $m, PREG_SET_ORDER );
	return array_map( static fn ( array $x ): string => $x[1] . ' ' . $x[2] . ' ' . $x[3], $m );
}

/**
 * Version 1's verify, restated: every landed record's record_check at stage LANDED (its digest
 * recomputed by the Calculator), the badge's count the register's, the Research Assembly pages
 * digesting to the badge's digest.
 */
function sc_verify( stdClass $u ): bool {
	$c = sc_calc();
	foreach ( sc_register( $u ) as $r ) {
		$a = $c->call( 'record', 'record_check', json_encode( [ 'record' => $r, 'setting' => 'OFF', 'stage' => 'LANDED', 'tfk' => json_decode( sc_draft() ) ], SC_JSON ) );
		if ( ( $a['value'] ?? null ) !== [ 'OK' ] ) {
			return false;
		}
	}
	$b = sc_badge( $u );
	$ra = Blocks::one( (string)$u->store->get( sc_titles()->researchAssembly( $u->px, PageTitles::ZONES[0] ) ), 'assembly' );
	$d = $c->call( 'zone', 'digest_research_assembly_of', '{"tfk":' . $ra . '}' )['value'] ?? null;
	return ( $b['record_count'] ?? -1 ) === count( sc_register( $u ) ) && $d === ( $b['research_assembly'] ?? '' );
}

function sc_ids( array $a ): array {
	return array_column( $a['landed'] ?? [], 'id' );
}

/** The register's records by ID. */
function sc_by( stdClass $u ): array {
	$o = [];
	foreach ( sc_register( $u ) as $r ) {
		$o[$r['ID']] = $r;
	}
	return $o;
}

const CORNER_SCREEN = 'corner: the screen (SR3, SR5, SR6, SR7, the contradiction ledger, the audit blocks) is not run at landing; Custos lands RESULT, ASSUMPTION and ENTRY_STATUS and writes no record of its own';
const CORNER_WITHDRAW = 'corner: the withdrawal (WITHDRAWAL records, SUPERSEDES carried out, the cascade) is not built; a record carrying SUPERSEDES is refused (RECORD CHECK, problem WITHDRAWAL), nothing written, and no record is superseded';
const CORNER_REQUEST = 'corner: the author\'s withdrawal request is not an op of action=pma; GA1 refuses the parameter (custos-unknown-param), nothing landed';
const CORNER_PROMOTION = 'corner: promotion (PROMOTION records, ESTABLISHED) is not built';
const CORNER_VERIFICATION = 'corner: VERIFICATION is not a class Custos lands (RECORD CHECK, LANDS)';
const CORNER_VIEWS = 'corner: the reading views (the register view, GAP VIEW, ENTRY VIEW, the control panel\'s links) are generated pages not yet built';
const CORNER_CHAIN = 'corner: the declarations and build chains are version 1 pages Custos does not write; the ticket\'s answer and the page revisions carry the landing';
const CORNER_MASTER = 'corner: Custos seeds a UWC with an empty register (SeedUwc, the Operator\'s act); no MASTER record, no CANDIDATE or DECLARED state on the wiki';
const CORNER_SEED = 'corner: the seeding is the Operator\'s maintenance script SeedUwc, which refuses a UWC any of whose pages exists; it runs only under MediaWiki';
const CORNER_SESSION = 'corner: the agent\'s session fields (D(IS), TPS, CAPABILITY, HARNESS MODE) are not parameters of action=pma; GA1 refuses them (custos-unknown-param); the record\'s D_IS and TPS come from configuration and execution is attested by the challenge';
const CORNER_COLLAB = 'corner: the collaboration page and its rows (WAITING, ASSIGNED, NEEDS RECERTIFICATION, the attested mode) are not written';
const CORNER_QUEUE = 'corner: the lock has no queue and no ACQUIRE op: a PETITION on a free or expired lock is granted at once, else refused LOCK HELD with when to poll; the grant is a time, not a count';
const CORNER_ACTOR = 'corner: every page is written by the landing job as Custos, never as the petitioner\'s own revision';
const CORNER_LEASE = 'corner: the lock\'s lease is one configured span ($wgCustosLockLease, 3600 s) from the grant, extended by HEARTBEAT to now plus the lease; no NO-PROGRESS LIMIT, EXPIRY STEP or 24 h ceiling';
const CORNER_RELEASE_PUSH = 'corner: RELEASE does not require a push in the grant';
const CORNER_LOCKVIEW = 'corner: the lock view (HOLDER SILENT, place and time) is not an op; STATUS does not carry the lock\'s state yet';
const CORNER_BADGE_HOLDER = 'corner: the badge carries no holder, grant or expiry; the lock page alone does';
const CORNER_V050 = 'corner: version 1\'s 0.5.0 lock page form is not read; Custos reads its own lock page form only';
const CORNER_ACCOUNT_PARAM = 'GA1: an account parameter is refused even when it names the authenticated account (custos-account)';
const CORNER_REGRANT = 'corner: a PETITION by the holder within its lease renews its grant (a new grant time, expiry, block and nonce)';
const DESIGN_STRIKE = 'Custos\'s design: the strike is not written at landing yet; Custos refuses at landing what version 1 landed and struck (RECORD CHECK, problem STRIKE OWED), nothing written';
const CORNER_CLEARS = 'corner: the strike screen clears at most what SR3\'s mechanical tests clear; a pair it cannot clear is refused as struck (RECORD CHECK, problem STRIKE OWED), nothing written';
const CORNER_NEXT = 'corner: the landing answers the register\'s count, not a next identifier';
const CORNER_NUMBERING = 'corner: Custos seeds no MASTER record, so a UWC\'s first record is <prefix>-1 and version 1\'s push_1 (from SPR-2) is refused SEQUENCE, nothing written; the replay lands a stand-in ASSUMPTION as SPR-1 first (FIXTURE) and keeps version 1\'s numbers after it';

/** The pages, a request, the pages again: the answer and both snapshots. */
function sc_try( stdClass $u, callable $fn ): array {
	$before = sc_snap( $u );
	$a = $fn();
	return [ $a, $before, sc_snap( $u ) ];
}

// ================================ a1 ==========================================================

function gate_a1(): void {
	SC::gate( 'a1' );
	$c = sc_calc();
	$draft = sc_draft();
	$z = json_decode( $draft, true );
	$wf = [];
	foreach ( [ [ 'starting_set_well_formed', [ 'tpk' => $z['TPK'] ] ], [ 'correspondence_table_well_formed', [ 'trm' => $z['TrM'], 'tpk' => $z['TPK'] ] ],
		[ 'criteria_set_well_formed', [ 'tms' => $z['TMS'] ] ] ] as [ $f, $args ] ) {
		$wf[$f] = $c->call( 'zone', $f, json_encode( $args, SC_JSON ) )['value'] ?? null;
	}
	SC::ok( '1.1', array_values( array_unique( array_map( 'json_encode', $wf ) ) ) === [ json_encode( [ true, [] ] ) ],
		'the spring draft passes the new-UWC checks: the three zones well formed', json_encode( $wf ) );
	$d = $c->call( 'zone', 'digest_research_assembly_of', '{"tfk":' . $draft . '}' )['value'] ?? '';
	SC::ok( '1.2', $d === '46db0af2a3f5fd6e86447bd1764cd5b934cf0f0be3c9f91d16fd47aa435afe5b', 'D(TFK) of the spring draft equals the live SPR\'s 46db0af2...', $d );
	SC::div( '1.3', true, 'CANDIDATE, structurally regular (no IC2, no UNDER)', CORNER_MASTER );
	SC::div( '1.4', true, 'a used prefix is refused', CORNER_SEED );
	// 1.5: no push before the UWC exists.
	$none = sc_uwc_empty( 'a1-empty' );
	[ $a, $b0, $b1 ] = sc_try( $none, static fn () => sc_push( $none, [ sc_arec( 'SPR-2', 'x' ) ], 'Agent A' ) );
	SC::refused( '1.5', $a, $b0, $b1, 'no push before the UWC is seeded' );

	$u = sc_uwc( 'a1' );
	SC::div( '2.1', true, 'MASTER SPR-1, no gaps, next SPR-2', CORNER_MASTER );
	SC::div( '2.2', true, 'DECLARED; register holds the MASTER', CORNER_MASTER );
	SC::ok( '2.3', ( sc_badge( $u )['research_assembly'] ?? '' ) === $d, 'the UWC carries D(TFK): the badge\'s Research Assembly digest' );
	SC::ok( '2.4', sc_verify( $u ), 'verify after seeding' );
	SC::div( '2.5', true, 'DECLARATIONS: genesis, two D-ACTS lines, the certificate', CORNER_CHAIN );
	SC::div( '2.6', true, 'a second declaration is refused', CORNER_MASTER );

	// 3 landing
	sc_grant( $u, 'Agent A' );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ sc_arec( 'SPR-3', 'Not the next free identifier.' ) ], 'Agent A' ) );
	SC::refused( '3.1', $a, $b0, $b1, 'a wrong identifier (SPR-3 where the next free is SPR-2) is refused' );
	// 3.2 on the register as Custos seeds it (no MASTER): SPR-1 is the next free identifier.
	$bare = sc_uwc( 'a1-bare', 'SPR', false );
	sc_grant( $bare, 'Agent A' );
	[ $a, $b0, $b1 ] = sc_try( $bare, static fn () => sc_push( $bare, sc_push1(), 'Agent A' ) );
	SC::div( '3.2', ( $a['refused'] ?? '' ) === 'RECORD CHECK' && str_contains( json_encode( $a['problems'] ?? [] ), 'SEQUENCE' )
		&& str_contains( (string)( $a['detail'] ?? '' ), 'SPR-1' ) && $b0 === $b1, 'push_1 lands SPR-2..SPR-4', CORNER_NUMBERING, json_encode( $a ) );
	$u = sc_uwc( 'a1b' );
	$p = sc_push( $u, sc_push1(), 'Agent A' );
	SC::ok( '3.2m', sc_ids( $p ) === [ 'SPR-2', 'SPR-3', 'SPR-4' ], 'push_1 lands SPR-2..SPR-4 after the MASTER\'s stand-in SPR-1', json_encode( $p ) );
	SC::div( '3.2n', !isset( $p['next_id'] ) && ( $p['record_count'] ?? 0 ) === 4, 'the push answers next SPR-5', CORNER_NEXT );
	$by = sc_by( $u );
	SC::ok( '3.3', ( $by['SPR-2']['GRADE'] ?? '' ) === 'PROVISIONAL' && ( $by['SPR-3']['GRADE'] ?? '' ) === 'PROVISIONAL' && ( $by['SPR-4']['GRADE'] ?? '' ) === 'PROVISIONAL', 'landed PROVISIONAL' );
	$ok = true;
	foreach ( sc_register( $u ) as $r ) {
		$dg = $c->call( 'record', 'record_digest', json_encode( [ 'record' => $r ], SC_JSON ) )['value'] ?? null;
		$ok = $ok && ( $dg[1] ?? '' ) === $r['DIGEST'];
	}
	SC::ok( '3.4', $ok, 'every record\'s digest recomputes from the page text' );
	SC::ok( '3.5', sc_verify( $u ), 'verify after the push' );
	$cite = [ 'ID' => 'SPR-5', 'CLASS' => 'RESULT', 'CITES' => [ 'SPR-99' ], 'ASSUMPTIONS' => [], 'STATEMENT' => 'x', 'REGIME' => 'L',
		'DERIVATION' => [ 'STEPS' => 1, 'TEXT' => 'x' ], 'FALSIFIER' => 'x', 'FALSIFIER_CLASS' => 'F1' ];
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ $cite ], 'Agent A' ) );
	SC::refused( '3.6', $a, $b0, $b1, 'a citation of a record not in the register is refused (REC-58)' );
	$u = sc_uwc( 'a1c' );
	sc_push( $u, sc_push1(), 'Agent A' );
	$ver = [ 'ID' => 'SPR-5', 'CLASS' => 'VERIFICATION', 'CITES' => [], 'ASSUMPTIONS' => [], 'REGIME' => 'M', 'TARGET' => 'SPR-4',
		'EXTERNAL' => [ 'VALUE' => '0.0201', 'U_C' => '0.0002', 'UNIT' => 'm', 'QUANTITY' => 'E_x' ], 'SOURCE' => 'Bench.', 'AT' => [] ];
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ $ver ], 'Agent A' ) );
	SC::refused( '3.7', $a, $b0, $b1, 'VERIFICATION is refused to a later stage (Custos: a class not landed yet)' );
	$sup = sc_push1()[2];
	$sup['ID'] = 'SPR-5';
	$sup['SUPERSEDES'] = 'SPR-4';
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ $sup ], 'Agent A' ) );
	SC::refused( '3.8', $a, $b0, $b1, 'SUPERSEDES is refused to a later stage' );

	// 4 the lock
	$u = sc_uwc( 'a1d' );
	sc_push( $u, sc_push1(), 'Agent A' );
	sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B1' ] );
	$g = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B4' ] );
	SC::div( '4.1', isset( $g['grant'] ) && preg_match( '/\A[0-9a-f]{32}\z/', (string)( $g['challenge'] ?? '' ) ) === 1,
		'petition queues WAITING at position 1, with a challenge nonce', CORNER_QUEUE );
	SC::div( '4.2', isset( $g['grant'] ) && !is_int( $g['grant'] ), 'the queue head acquires, grant 4 (previous + 1)', CORNER_QUEUE );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_op( $u, 'PETITION', 'Agent B', [ 'block' => 'B9' ] ) );
	SC::ok( '4.3', ( $a['refused'] ?? '' ) === 'LOCK HELD' && $b0 === $b1, 'a second acquisition is refused while held [Custos: LOCK HELD]', json_encode( $a ) );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-5', 'x' ) ] ), 'block' => 'B7' ] ) );
	SC::refused( '4.4', $a, $b0, $b1, 'fencing: a stale grant (another block) is refused' );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_op( $u, 'PUSH', 'Agent B', [ 'records' => json_encode( [ sc_arec( 'SPR-5', 'x' ) ] ), 'block' => 'B4' ] ) );
	SC::refused( '4.5', $a, $b0, $b1, 'fencing: a non-holder is refused' );
	$r = sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B4' ] );
	SC::div( '4.6', isset( $r['released'] ), 'a release before a push in the grant is refused', CORNER_RELEASE_PUSH, json_encode( $r ) );
	sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B4' ] );
	$pp = sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ [ 'ID' => 'SPR-5', 'CLASS' => 'ASSUMPTION', 'CITES' => [], 'ASSUMPTIONS' => [],
		'PROPOSITION' => 'The gate\'s lock case holds.', 'REFS' => [] ] ] ) ] );
	$rel = sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B4' ] );
	SC::ok( '4.7', sc_ids( $pp ) === [ 'SPR-5' ] && isset( $rel['released'] ), 'a push under the grant lands; the holder then releases', json_encode( [ $pp, $rel ] ) );

	// 5 one write per page; tamper
	$t = sc_titles()->registerVolume( $u->px, 1 );
	$revs = count( $u->store->revisions[$t] ?? [] );
	$w = new PageWriter( $u->store, sc_titles() );
	$w->begin( $u->px, 'noop' );
	$w->put( $t, (string)$u->store->get( $t ) );
	$ix = sc_titles()->index( $u->px );
	$w->put( $ix, (string)$u->store->get( $ix ) );
	$w->commit();
	SC::ok( '5.1', count( $u->store->revisions[$t] ?? [] ) === $revs, 'an unchanged page is not saved again' );
	$u->store->tamper( $t, str_replace( 'Dividing EOM_X by m', 'Dividing EOM_X by 2m', (string)$u->store->get( $t ) ) );
	SC::ok( '5.2', !sc_verify( $u ), 'a record edited by hand fails verify' );
}

/** A prefix with no page: no UWC seeded. */
function sc_uwc_empty( string $tag ): stdClass {
	return sc_open( sc_scratch() . "/$tag", 'SPZ', 1791158400 );
}

// ================================ a2 ==========================================================

function arec( string $id, string $prop ): array {
	return sc_arec( $id, $prop );
}

function mrec( string $id, string $value, string $uc, array $asm, string $q = 'E_x', int $steps = 1 ): array {
	$r = [ 'ID' => $id, 'CLASS' => 'RESULT', 'CITES' => [], 'ASSUMPTIONS' => $asm, 'STATEMENT' => "Measured $q: $value m.", 'REGIME' => 'M',
		'DERIVATION' => [ 'STEPS' => $steps, 'TEXT' => 'Read from the bench gauge.' ],
		'FALSIFIER' => 'A repeat reading outside the stated uncertainty.', 'FALSIFIER_CLASS' => 'F3',
		'QUANTITY' => $q, 'VALUE' => $value, 'UNIT' => 'm', 'U_C' => $uc,
		'BUDGET' => [ [ 'NAME' => 'gauge', 'U' => $uc, 'UNIT' => 'm', 'EVALUATION' => 'B', 'BASIS' => 'manufacturer\'s specification' ] ],
		'CORRELATED' => false ];
	if ( $q === 'E_x' ) {
		$r['AT'] = [ [ 'DOF' => 't', 'VALUE' => '0', 'UNIT' => 's' ] ];
	}
	return $r;
}

function lrec_z( string $id, string $value, array $asm = [], int $steps = 1 ): array {
	return [ 'ID' => $id, 'CLASS' => 'RESULT', 'CITES' => [], 'ASSUMPTIONS' => $asm, 'STATEMENT' => "z is $value m on the axis.", 'REGIME' => 'L',
		'DERIVATION' => [ 'STEPS' => $steps, 'TEXT' => 'C_NOZ fixes z.' ], 'FALSIFIER' => 'Motion off the axis.', 'FALSIFIER_CLASS' => 'F3',
		'QUANTITY' => 'E_z', 'VALUE' => $value, 'UNIT' => 'm' ];
}

function lcite( string $id, array $cites ): array {
	return [ 'ID' => $id, 'CLASS' => 'RESULT', 'CITES' => $cites, 'ASSUMPTIONS' => [], 'STATEMENT' => 'A consequence of ' . implode( ', ', $cites ) . '.',
		'REGIME' => 'L', 'DERIVATION' => [ 'STEPS' => 1, 'TEXT' => 'Restate.' ], 'FALSIFIER' => 'As cited.', 'FALSIFIER_CLASS' => 'F3' ];
}

function p1( string $id, string $newId, ?string $old = null, array $set = [] ): array {
	foreach ( sc_push1() as $r ) {
		if ( $r['ID'] === $id ) {
			$r['ID'] = $newId;
			if ( $old !== null ) {
				$r['SUPERSEDES'] = $old;
			}
			return array_merge( $r, $set );
		}
	}
	throw new RuntimeException( "no $id" );
}

/** A case's UWC with push_1 landed by Agent A. */
function fresh( string $case ): stdClass {
	static $tpl = null;
	if ( $tpl === null ) {
		$tpl = sc_uwc( 'a2-push1' );
		sc_push( $tpl, sc_push1(), 'Agent A' );
	}
	return sc_fork( $tpl, "a2-$case", true );
}

/** A VERIFICATION of $target (the corner: its DIFFERENCE left as presented). */
function ver( string $id, string $target, string $value, string $uc ): array {
	return [ 'ID' => $id, 'CLASS' => 'VERIFICATION', 'CITES' => [], 'ASSUMPTIONS' => [], 'REGIME' => 'M', 'TARGET' => $target,
		'EXTERNAL' => [ 'VALUE' => $value, 'U_C' => $uc, 'UNIT' => 'm', 'QUANTITY' => 'E_x' ], 'SOURCE' => 'Bench measurement.', 'AT' => [],
		'DIFFERENCE' => [ 'VALUE' => '0', 'U' => '0', 'ZETA' => '0' ] ];
}

/**
 * A case whose version 1 assertions are a corner: the push run, Custos's answer checked against $land
 * (the identifiers it lands, or null: refused, nothing written), each assertion divergent by $cause.
 */
function sc_case( string $case, stdClass $u, array $records, ?array $land, array $whats, string $cause, ?array $lands = null ): array {
	$land = $lands ?? $land;
	$account = 'Agent A';
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, $records, $account ) );
	$still = $land === null ? ( isset( $a['refused'] ) && $b0 === $b1 ) : sc_ids( $a ) === $land;
	$k = 0;
	foreach ( $whats as $what ) {
		SC::div( "$case." . ++$k, $still, $what, $cause, json_encode( $a ) );
	}
	return $a;
}

/** Custos refused the request whole, each problem STRIKE OWED, nothing written. */
function sc_strike_owed( array $a, array $before, array $after ): bool {
	if ( ( $a['refused'] ?? '' ) !== 'RECORD CHECK' || $before !== $after || empty( $a['problems'] ) ) {
		return false;
	}
	foreach ( $a['problems'] as $p ) {
		foreach ( $p['answer'][1] ?? [] as $x ) {
			if ( ( $x[0] ?? '' ) !== 'STRIKE OWED' ) {
				return false;
			}
		}
		if ( empty( $p['answer'][1] ) ) {
			return false;
		}
	}
	return true;
}

/**
 * A case whose batch the strike screen holds: the push run, Custos's answer checked to be the whole
 * refusal STRIKE OWED with nothing written; each of version 1's assertions divergent by its cause
 * ($causes: one string, or one per assertion). Version 1 landed the batch; Custos landing it would
 * make the divergence fail, and the strike written at landing makes it fail too.
 */
function sc_owed( string $case, stdClass $u, array $records, array $whats, $causes ): array {
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, $records, 'Agent A' ) );
	if ( isset( $a['landed'] ) ) {
		SC::defect( "$case.1", $whats[0], 'Custos landed a batch the strike screen holds: ' . json_encode( $a['landed'] ) );
		return $a;
	}
	$still = sc_strike_owed( $a, $b0, $b1 );
	$k = 0;
	foreach ( $whats as $what ) {
		$cause = is_array( $causes ) ? $causes[$k] : $causes;
		SC::div( "$case." . ++$k, $still, $what, $cause, json_encode( $a ) );
	}
	return $a;
}

function gate_a2(): void {
	SC::gate( 'a2' );
	// A-G: the screen.
	$ua = fresh( 'A' );
	sc_case( 'A', $ua, [ arec( 'SPR-5', 'The release gauge reads true.' ), mrec( 'SPR-6', '0.03', '0.001', [ 'SPR-2', 'SPR-5' ] ) ], [ 'SPR-5', 'SPR-6' ], [
		'nothing written, nothing struck; SPR-4 and SPR-6 stand', 'next SPR-7; no audit block', 'the pair is listed for INSPECTION, once',
		'rating: d(SPR-4) = (1, 1); d(SPR-6) = (2, 1)', 'rating: SR3 figures in SI, S = 1, z above k', 'rating: SR5 alone would strike SPR-6',
		'rating: SR7 alone would write SR7_ASSUMPTIONS against SPR-2', 'rating: SR6 counts 1 and 1 against N_x = 2', 'the ledger keeps the same rating',
		'the push result carries the readable sheet' ], CORNER_SCREEN );
	SC::ok( 'A.11', sc_verify( $ua ), 'verify' );
	SC::div( 'A.12', true, 'the next push lists nothing new and may cite SPR-6', CORNER_SCREEN );
	sc_case( 'B', fresh( 'B' ), [ mrec( 'SPR-5', '0.03', '0.001', [ 'SPR-2' ] ) ], [ 'SPR-5' ], [
		'nothing written, no audit block', 'rating: equal d; SR5 alone would open an audit block', 'rating: SR7 alone against SPR-2', 'both stand' ], CORNER_SCREEN );
	sc_owed( 'C', fresh( 'C' ), [ lrec_z( 'SPR-5', '0' ), mrec( 'SPR-6', '0.01', '0.001', [], 'E_z' ) ], [
		'nothing written; SR7 alone would write SR7_DOMAIN', 'rating carries the pair\'s CONDITIONS; equal d' ], CORNER_CLEARS );
	sc_owed( 'C2', fresh( 'C2' ), [ arec( 'SPR-5', 'The axis is level.' ), lrec_z( 'SPR-6', '0', [ 'SPR-5' ] ), mrec( 'SPR-7', '0.01', '0.001', [], 'E_z' ),
		lcite( 'SPR-8', [ 'SPR-6' ] ) ], [
		'nothing written; the L record stands', 'rating: SR5 alone would strike SPR-6, which SR7 forbids', 'rating: SR7 alone against SPR-5' ], CORNER_CLEARS );
	$recs = [ arec( 'SPR-5', 'The second gauge reads true.' ) ];
	for ( $i = 6; $i <= 15; $i++ ) {
		$recs[] = mrec( "SPR-$i", '0', '0.001', [], 'E_z' );
	}
	$recs[] = mrec( 'SPR-16', '0.01', '0.001', [ 'SPR-5' ], 'E_z' );
	$dIds = array_column( $recs, 'ID' );
	$ud = fresh( 'D' );
	sc_owed( 'D', $ud, $recs, [ 'the outlier SPR-16 struck by SPR-10', 'locus SPR-5 in NAMED_GAP SPR-18', 'exactly one record REFUTED' ], DESIGN_STRIKE );
	SC::div( 'D.4', true, 'records past 10 land on Volume 2', 'corner: Custos keeps one open register volume (Volume 1) until the volume roll is built' );
	SC::ok( 'D.5', sc_verify( $ud ), 'verify' );
	$recs = [];
	for ( $i = 5; $i <= 14; $i++ ) {
		$recs[] = mrec( "SPR-$i", '0', '0.001', [], 'E_z' );
	}
	$recs[] = mrec( 'SPR-15', '0.01', '0.001', [], 'E_z' );
	sc_owed( 'E', fresh( 'E' ), $recs, [ 'nothing struck, no record written', 'ten SR5_EQUAL_D audit blocks', 'SR6: one SR6_NX audit block',
		'audit blocks are not opened twice' ], CORNER_CLEARS );
	sc_case( 'F', fresh( 'F' ), [ arec( 'SPR-5', 'Gauge A reads true.' ), arec( 'SPR-6', 'Gauge B reads true.' ), mrec( 'SPR-7', '0.03', '0.001', [ 'SPR-2', 'SPR-5' ] ),
		mrec( 'SPR-8', '0.03', '0.001', [ 'SPR-2', 'SPR-6' ] ) ], [ 'SPR-5', 'SPR-6', 'SPR-7', 'SPR-8' ], [ 'nothing struck or written; two L-M items listed',
		'SR6 reaches N_x on SPR-4', 'each rating shows SPR-4\'s two contradictions', 'reaching N_x strikes nothing' ], CORNER_SCREEN );
	$recs = [ arec( 'SPR-5', 'The second gauge reads true.' ) ];
	for ( $i = 6; $i <= 15; $i++ ) {
		$recs[] = mrec( "SPR-$i", '0', '0.001', [], 'E_z' );
	}
	$recs[] = mrec( 'SPR-16', '0.01', '0.001', [ 'SPR-5' ], 'E_z' );
	$recs[] = lcite( 'SPR-17', [ 'SPR-16' ] );
	$g = fresh( 'G' );
	sc_owed( 'G', $g, $recs, [ 'WITHDRAWAL SPR-18 carries the cascade', 'SPR-16 REFUTED; SPR-17 WITHDRAWN by the cascade' ], DESIGN_STRIKE );
	// The batch is refused, so G.3's record is re-seeded: two records the strike screen clears (no pair
	// of them contradicts), landed before the edit; the edit is version 1's, on a landed record.
	sc_push( $g, [ arec( 'SPR-5', 'The second gauge reads true.' ), mrec( 'SPR-6', '0', '0.001', [], 'E_z' ) ], 'Agent A' );
	$seeded = sc_verify( $g ) && count( sc_register( $g ) ) === 6;
	$t = sc_titles()->registerVolume( $g->px, 1 );
	$g->store->tamper( $t, preg_replace( '/"SPR-6"/', '"SPR-66"', (string)$g->store->get( $t ), 1 ) );
	SC::ok( 'G.3', $seeded && !sc_verify( $g ), 'a record edited by hand fails verify' );

	// H-J: the withdrawals.
	$h = fresh( 'H' );
	sc_case( 'H', $h, [ p1( 'SPR-3', 'SPR-5', 'SPR-3', [ 'STATEMENT' => 'Dividing EOM_X by m (positive by A_mpos) gives dv/dt = -(k_s/m) x; restated.' ] ) ], null, [
		'SPR-5 SUPERSEDES SPR-3: WITHDRAWAL SPR-6, cause SUPERSEDED', 'SPR-3 WITHDRAWN by the record; SPR-5 stands', 'the pushed record takes the next free identifier; the WITHDRAWAL follows it',
		'the BUILD CHAIN push line names the withdrawal' ], CORNER_WITHDRAW );
	SC::ok( 'H.5', sc_verify( $h ), 'verify' );
	// No record is superseded (H was refused), so SPR-3 stands and a citation of it is sound.
	$a = sc_push( $h, [ lcite( 'SPR-5', [ 'SPR-3' ] ) ], 'Agent A' );
	SC::div( 'H.6', sc_ids( $a ) === [ 'SPR-5' ], 'a record citing the superseded SPR-3 is refused (REC-59)', CORNER_WITHDRAW, json_encode( $a ) );
	[ $a, $b0, $b1 ] = sc_try( $h, static fn () => sc_push( $h, [ p1( 'SPR-3', 'SPR-6', 'SPR-3' ) ], 'Agent A' ) );
	SC::refused( 'H.7', $a, $b0, $b1, 'SPR-3 cannot be superseded again' );
	sc_case( 'H2', fresh( 'H2' ), [ p1( 'SPR-2', 'SPR-5', 'SPR-2', [ 'PROPOSITION' => 'At t = 0 the mass is released at x = 0.025 m.' ] ) ], null, [
		'WITHDRAWAL SPR-6 withdraws SPR-2 with cascade SPR-4', 'the push result says so', 'verify' ], CORNER_WITHDRAW );
	sc_case( 'H3', fresh( 'H3' ), [ array_merge( lcite( 'SPR-5', [ 'SPR-3' ] ), [ 'SUPERSEDES' => 'SPR-3' ] ) ], null, [
		'SPR-5 cites SPR-3 and supersedes it: the cascade takes SPR-5 too', 'the push result names the push\'s own record in the cascade' ], CORNER_WITHDRAW );
	sc_case( 'H4', fresh( 'H4' ), [ p1( 'SPR-3', 'SPR-5', 'SPR-3' ), p1( 'SPR-3', 'SPR-6', 'SPR-5', [ 'STATEMENT' => 'Second correction.' ] ) ], null, [
		'a chain of supersessions in one push; SPR-6 stands', 'verify' ], CORNER_WITHDRAW );
	$i = fresh( 'I' );
	$refs = [
		'I.1' => [ [ p1( 'SPR-3', 'SPR-5', 'SPR-3' ) ], 'Agent B', 'a supersession of another account\'s record is refused (REC-60)' ],
		'I.2' => [ [ p1( 'SPR-3', 'SPR-5', 'SPR-2' ) ], 'Agent A', 'SUPERSEDES naming a record of another CLASS is refused (REC-58)' ],
		'I.3' => [ [ p1( 'SPR-3', 'SPR-5', 'SPR-99' ) ], 'Agent A', 'SUPERSEDES naming no record is refused (REC-58)' ],
		'I.4' => [ [ p1( 'SPR-3', 'SPR-5', 'SPR-3' ), p1( 'SPR-3', 'SPR-6', 'SPR-3' ) ], 'Agent A', 'two records of one push superseding SPR-3 are refused whole' ],
		'I.5' => [ [ [ 'ID' => 'SPR-5', 'CLASS' => 'ENTRY_STATUS', 'CITES' => [], 'ASSUMPTIONS' => [], 'ENTRY' => 'E_x', 'NOTE' => 'Restated.', 'SUPERSEDES' => 'SPR-3' ] ],
			'Agent A', 'an ENTRY_STATUS carries no SUPERSEDES' ],
	];
	foreach ( $refs as $id => [ $recs, $acct, $what ] ) {
		$iu = fresh( 'I' . $id );
		sc_grant( $iu, $acct );
		[ $a, $b0, $b1 ] = sc_try( $iu, static fn () => sc_push( $iu, $recs, $acct ) );
		SC::refused( $id, $a, $b0, $b1, $what );
	}
	SC::ok( 'I.6', count( sc_register( $i ) ) === 4, 'the register unchanged by the refusals (the MASTER\'s stand-in and push_1)' );
	$j = fresh( 'J' );
	$wd = static fn ( string $acct, array $ids ) => sc_op( $j, 'PUSH', $acct, [ 'records' => '[]', 'withdraw' => json_encode( $ids ) ] );
	$k = 0;
	foreach ( [ 'WITHDRAW SPR-3 by its AUTHOR: WITHDRAWAL SPR-5, cause AUTHOR', 'a push carrying only the request lands no record; next SPR-6; verify' ] as $what ) {
		$a = $wd( 'Agent A', [ 'SPR-3' ] );
		SC::div( 'J.' . ++$k, ( $a['refused'] ?? '' ) === 'OPS', $what, CORNER_REQUEST, json_encode( $a ) );
	}
	foreach ( [ [ [ 'SPR-3' ], 'a WITHDRAWN record is not withdrawn again' ], [ [ 'SPR-4' ], 'another account\'s record is refused' ], [ [ 'SPR-1' ], 'the MASTER is not withdrawn' ],
		[ [ 'SPR-99' ], 'an identifier with no record is refused' ], [ [ 'SPR-4', 'SPR-4' ], 'a request naming one record twice is refused' ],
		[ [ 'SPR-4x' ], 'a request that is not an identifier is refused' ] ] as [ $ids, $what ] ) {
		[ $a, $b0, $b1 ] = sc_try( $j, static fn () => $wd( 'Agent A', $ids ) );
		SC::refused( 'J.' . ++$k, $a, $b0, $b1, $what );
	}
	[ $a, $b0, $b1 ] = sc_try( $j, static fn () => sc_op( $j, 'PUSH', 'Agent A', [ 'records' => '[]' ] ) );
	SC::refused( 'J.' . ++$k, $a, $b0, $b1, 'an empty push is refused' );
	SC::ok( 'J.' . ++$k, count( sc_register( $j ) ) === 4, 'the refusals left the register as it was' );
	$a = $wd( 'Agent A', [ 'SPR-2' ] );
	SC::div( 'J.' . ++$k, ( $a['refused'] ?? '' ) === 'OPS', 'WITHDRAW SPR-2: its cascade takes SPR-4', CORNER_REQUEST, json_encode( $a ) );
	$j2 = fresh( 'J2' );
	$a = sc_op( $j2, 'PUSH', 'Agent A', [ 'records' => json_encode( [ lcite( 'SPR-5', [ 'SPR-3' ] ), arec( 'SPR-6', 'Unrelated.' ) ] ), 'withdraw' => '["SPR-3"]' ] );
	SC::div( 'J2.1', ( $a['refused'] ?? '' ) === 'OPS', 'SPR-5 and SPR-6 land, then WITHDRAWAL SPR-7 withdraws SPR-3 and its cascade', CORNER_REQUEST );
	SC::div( 'J2.2', ( $a['refused'] ?? '' ) === 'OPS', 'the push result names it', CORNER_REQUEST );
	$recs = [ arec( 'SPR-5', 'The third gauge reads true.' ), mrec( 'SPR-6', '0', '0.001', [], 'E_z' ), mrec( 'SPR-7', '0', '0.001', [], 'E_z' ),
		mrec( 'SPR-8', '0.01', '0.001', [ 'SPR-5' ], 'E_z' ), mrec( 'SPR-9', '0.01', '0.001', [ 'SPR-5' ], 'E_z' ) ];
	sc_owed( 'K', fresh( 'K' ), $recs, [ 'a 2-2 split on E_z: no contradiction', 'withdrawing SPR-9 leaves the pair one other record: SPR-8 struck',
		'locus SPR-5 in NAMED_GAP SPR-12', 'verify' ], [ CORNER_CLEARS, DESIGN_STRIKE, DESIGN_STRIKE, DESIGN_STRIKE ] );

	// L: the acting account.
	$l = fresh( 'L' );
	SC::div( 'L.1', true, 'no account parameter, an empty one, or the authenticated name: the authenticated account', CORNER_ACCOUNT_PARAM );
	try {
		$l->ops->run( 'PETITION', $l->px, 'Agent A', [ 'block' => 'B2', 'account' => 'Agent B' ] );
		SC::defect( 'L.2', 'an account parameter naming another account is refused', 'accepted' );
	} catch ( \Custos\Refusal $e ) {
		SC::ok( 'L.2', $e->what === 'custos-account', 'an account parameter naming another account is refused [Custos: custos-account]', $e->what );
	}

	// M: promotion.
	sc_case( 'M', sc_uwc( 'a2-M' ), sc_push1(), [ 'SPR-2', 'SPR-3', 'SPR-4' ], [ 'PROMOTION SPR-5 promotes SPR-3', 'SPR-3 ESTABLISHED by the record',
		'the BUILD CHAIN push line names the promotion', 'a landing that makes nothing eligible writes no PROMOTION' ], CORNER_PROMOTION );
	$m2 = sc_push1();
	$m2[] = array_merge( $m2[1], [ 'ID' => 'SPR-5', 'CITES' => [ 'SPR-3' ], 'STATEMENT' => 'A consequence of SPR-3, restated.' ] );
	sc_case( 'M2', sc_uwc( 'a2-M2' ), $m2, [ 'SPR-2', 'SPR-3', 'SPR-4', 'SPR-5' ], [ 'one PROMOTION SPR-6 lists SPR-3 and SPR-5' ], CORNER_PROMOTION );
	$s3 = sc_push1()[1];
	sc_case( 'M3', fresh( 'M3' ), [ array_merge( $s3, [ 'ID' => 'SPR-5', 'FALSIFIER_CLASS' => 'F1', 'STATEMENT' => 'Below the floor.' ] ),
		array_merge( $s3, [ 'ID' => 'SPR-6', 'CITES' => [ 'SPR-3' ], 'STATEMENT' => 'Cites SPR-3.' ] ), array_merge( $s3, [ 'ID' => 'SPR-7', 'STATEMENT' => 'Eligible on its own.' ] ) ],
		[ 'SPR-5', 'SPR-6', 'SPR-7' ], [ 'the bars: SPR-5 and SPR-6 stay PROVISIONAL; SPR-7 alone is promoted' ], CORNER_PROMOTION );
	$mdom = static fn ( string $id, string $v ): array => array_merge( mrec( $id, $v, '0.001', [], 'E_z' ),
		[ 'DOMAIN' => '|z| < x_max', 'DOMAIN_CONDITION' => 'abs(z) < x_max', 'REFS' => [ 'z', 'x_max' ], 'ENTRIES' => [ 'E_z' ] ] );
	$recs = [];
	for ( $n = 5; $n <= 15; $n++ ) {
		$recs[] = $mdom( "SPR-$n", $n === 15 ? '0.01' : '0' );
	}
	sc_owed( 'M4', fresh( 'M4' ), $recs, [ 'an open audit block bars promotion', 'control: the ten agreeing records are promoted by one PROMOTION' ], CORNER_CLEARS );
	sc_case( 'M5', sc_uwc( 'a2-M5' ), $m2, [ 'SPR-2', 'SPR-3', 'SPR-4', 'SPR-5' ], [ 'SPR-7 supersedes the ESTABLISHED SPR-5', 'WITHDRAW SPR-3 (ESTABLISHED): its cascade', 'verify' ], CORNER_PROMOTION );

	// V: the reading views.
	$k = 0;
	foreach ( [ 'setup: SPR-17 struck, locus gap SPR-21', 'register view', 'GAP VIEW SPR-21', 'ENTRY VIEW E_x', 'Special:TpmRegister paths render the three views',
		'a GAP VIEW of a record that is not a gap is refused', 'an ENTRY VIEW of no Correspondence Table entry is refused (REC-74)', 'an unknown path is refused' ] as $what ) {
		SC::div( 'V.' . ++$k, true, $what, CORNER_VIEWS );
	}
	$v = fresh( 'V' );
	try {
		$v->ops->run( 'PETITION', '[[x]]', 'Agent A', [ 'block' => 'B2' ] );
		SC::ok( 'V.9', false, 'a prefix that is not an identifier is refused before any read' );
	} catch ( \Custos\Refusal $e ) {
		SC::ok( 'V.9', $e->what === 'custos-prefix', 'a prefix that is not an identifier is refused before any read [Custos: custos-prefix]' );
	}
	SC::div( 'V.10', true, 'the control panel links the register, each GAP VIEW and each ENTRY VIEW', CORNER_VIEWS );

	// N: the VERIFICATION.
	$n = fresh( 'N' );
	sc_case( 'N', $n, [ ver( 'SPR-5', 'SPR-4', '0.0201', '0.0002' ) ], null, [ 'push_2\'s VERIFICATION lands PROVISIONAL, DIFFERENCE recomputed, within k',
		'the push result says so; the ledger untouched; the ENTRY VIEW lists it; verify', 'within k: no rating, nothing listed for INSPECTION' ], CORNER_VERIFICATION );
	$k = 0;
	foreach ( [ 'a VERIFICATION in its TARGET\'s push is refused (REC-91)', 'a DIFFERENCE that is not the recomputed one is refused (REC-96)',
		'an EXTERNAL of another QUANTITY is refused (REC-93)', 'an AT that is not the TARGET\'s is refused (REC-94)', 'an EXTERNAL in a unit of another dimension is refused',
		'a TARGET that is no record is refused (REC-58)' ] as $what ) {
		$nu = fresh( 'N2-' . ++$k );
		[ $a, $b0, $b1 ] = sc_try( $nu, static fn () => sc_push( $nu, [ ver( 'SPR-5', $k === 6 ? 'SPR-99' : 'SPR-4', '0.0199', '0.0002' ) ], 'Agent A' ) );
		SC::refused( "N2.$k", $a, $b0, $b1, $what );
	}
	SC::ok( 'N2.7', count( sc_register( $n ) ) === 4, 'after the refusals the register is unchanged' );
	foreach ( [ 'N3' => [ 'an L TARGET outside k: SR7_ASSUMPTIONS gap, SPR-4 stands', 'its GAP VIEW; no audit block; verify', 'rating: the VERIFICATION, the EXTERNAL, the DIFFERENCE',
		'rating: the TARGET', 'rating: SR7 alone writes the gap', 'the rating listed, kept and written as a sheet' ],
		'N4' => [ 'a(SPR-5) = 0: SR7_DOMAIN gap', 'rating: d = (0, 1)' ], 'N5' => [ 'an M TARGET outside k: two VERIFICATION_M audit blocks', 'rating of an M TARGET', 'each rating names the other VERIFICATION' ],
		'N6' => [ 'a superseding VERIFICATION is checked again; none promoted', 'within k: no rating', 'the author withdraws SPR-7' ],
		'N7' => [ 'the rating names what rests on the TARGET', 'a second failed VERIFICATION names the first' ] ] as $case => $whats ) {
		sc_case( $case, fresh( $case ), [ ver( 'SPR-5', 'SPR-4', '0.03', '0.001' ) ], null, $whats, CORNER_VERIFICATION );
	}
}

// ================================ b1 ==========================================================

function gate_b1(): void {
	SC::gate( 'b1' );
	$hex = static fn ( $s ): bool => is_string( $s ) && preg_match( '/\A[0-9a-f]{32}\z/', $s ) === 1;
	$lockTitle = static fn ( stdClass $u ): string => sc_titles()->lock( $u->px );

	// L1 PETITION: the session fields.
	$u = sc_uwc( 'b1-L1' );
	$k = 0;
	foreach ( [ [ 'd_is', '', 'a petition without D(IS) is refused' ], [ 'd_is', str_repeat( '0', 64 ), 'a petition with another D(IS) is refused (CR9)' ] ] as [ $p, $v, $what ] ) {
		$a = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1', $p => $v ] );
		SC::div( 'L1.' . ++$k, ( $a['refused'] ?? '' ) === 'OPS', $what, CORNER_SESSION, json_encode( $a ) );
	}
	SC::div( 'L1.' . ++$k, true, 'the account\'s PETITION row is marked NEEDS RECERTIFICATION', CORNER_COLLAB );
	foreach ( [ [ 'tps', 'a petition naming another TPS version is refused' ], [ 'capability', 'a petition without CAPABILITY is refused' ],
		[ 'capability', 'an unknown CAPABILITY key is refused' ], [ 'capability', 'a REASONED agent does not petition' ], [ 'harness_mode', 'an unknown HARNESS MODE is refused' ] ] as [ $p, $what ] ) {
		$a = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1', $p => 'x' ] );
		SC::div( 'L1.' . ++$k, ( $a['refused'] ?? '' ) === 'OPS', $what, CORNER_SESSION, json_encode( $a ) );
	}
	$pe = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	SC::div( 'L1.' . ++$k, isset( $pe['grant'] ) && $hex( $pe['challenge'] ?? null ), 'a petition queues at position 1 and carries a challenge nonce', CORNER_QUEUE, json_encode( $pe ) );
	SC::div( 'L1.' . ++$k, ( array_slice( $u->store->revisions[$lockTitle( $u )], -1 )[0] ?? [] )['actor'] === 'Custos', 'the queue edit is the petitioner\'s own revision of the lock page', CORNER_ACTOR );
	SC::div( 'L1.' . ++$k, true, 'the PETITION row is the petitioner\'s own revision of the collaboration page', CORNER_COLLAB );
	SC::div( 'L1.' . ++$k, true, 'one WAITING petition per account per UWC', CORNER_QUEUE );

	// L2 ACQUIRE.
	SC::div( 'L2.1', true, 'an account not in the queue does not acquire', CORNER_QUEUE );
	$lk = sc_lock( $u );
	SC::ok( 'L2.2', ( $lk['holder'] ?? '' ) === 'Agent A' && $hex( $pe['challenge'] ?? null ), 'the petitioner holds the lock, with a fresh nonce (grant 1 is a time)', json_encode( $lk ) );
	SC::div( 'L2.3', ( strtotime( (string)$lk['expires_at'] ) - strtotime( (string)$lk['granted_at'] ) ) === Landing::LEASE, 'the first expiry is the grant time + 6 h', CORNER_LEASE, json_encode( $lk ) );
	SC::div( 'L2.4', true, 'the acquisition is the holder\'s own revision; the row reads ASSIGNED', CORNER_ACTOR );
	SC::div( 'L2.5', true, 'the badge carries the holder, the grant and the expiry', CORNER_BADGE_HOLDER );
	$a = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	// The renewal itself, not a changed second: a grant time is written to the second, and the wiki run's two calls can share one.
	SC::div( 'L2.6', isset( $a['grant'] ) && ( $a['challenge'] ?? null ) !== ( $pe['challenge'] ?? null ) && $a['grant'] >= $pe['grant'],
		'a holder does not acquire again', CORNER_REGRANT, json_encode( $a ) );
	SC::ok( 'L2.7', isset( $a['grant'] ) && $hex( $a['challenge'] ?? null ) && $a['challenge'] !== $pe['challenge'],
		'a petition by the holder answers it as the holder, with a fresh nonce [Custos: its grant renewed]', json_encode( $a ) );
	$pe = $a;

	// L3 the challenge on PUSH.
	$nonces = [ $pe['challenge'] ];
	$push = static fn ( array $p ) => sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'A.' ) ] ) ] + $p );
	$n0 = $u->nonces->peek( 'Agent A', $u->px );
	[ $e, $b0, $b1 ] = sc_try( $u, static fn () => $push( [ 'challenge_response' => '' ] ) );
	SC::ok( 'L3.1', ( $e['refused'] ?? '' ) === 'CHALLENGE' && $hex( $e['challenge'] ?? null ) && $b0 === $b1,
		'a push without an answer is refused and the refusal carries the next nonce', json_encode( $e ) );
	$nonces[] = $e['challenge'] ?? '';
	[ $e, $b0, $b1 ] = sc_try( $u, static fn () => $push( [ 'challenge_response' => \Custos\Challenge::response( sc_calc(), (string)$n0 )[1] ] ) );
	SC::ok( 'L3.2', ( $e['refused'] ?? '' ) === 'CHALLENGE' && $hex( $e['challenge'] ?? null ) && $b0 === $b1, 'the answer to a consumed nonce is refused', json_encode( $e ) );
	$nonces[] = $e['challenge'] ?? '';
	[ $e, $b0, $b1 ] = sc_try( $u, static fn () => $push( [ 'challenge_response' => str_repeat( 'ab', 32 ) ] ) );
	SC::ok( 'L3.3', ( $e['refused'] ?? '' ) === 'CHALLENGE' && $b0 === $b1, 'a well-formed but wrong answer is refused', json_encode( $e ) );
	$nonces[] = $e['challenge'] ?? '';
	SC::div( 'L3.4', true, 'a push declaring REASONED is refused even with a right answer', CORNER_SESSION );
	SC::div( 'L3.5', true, 'a push with another D(IS) is refused, the row marked NEEDS RECERTIFICATION', CORNER_SESSION );
	SC::ok( 'L3.6', count( array_unique( $nonces ) ) === count( $nonces ) && count( $nonces ) === 4, 'every nonce issued is fresh' );
	$last = (string)$u->nonces->peek( 'Agent A', $u->px );
	$answer = \Custos\Challenge::response( sc_calc(), $last )[1];
	$p = $push( [ 'challenge_response' => $answer ] );
	SC::ok( 'L3.7', sc_ids( $p ) === [ 'SPR-2' ] && ( $p['execution'] ?? '' ) === 'EXECUTED' && $hex( $p['challenge'] ?? null ) && $p['challenge'] !== $last,
		'the right answer to the outstanding nonce lands the push, attested EXECUTED, with the next nonce', json_encode( $p ) );
	SC::div( 'L3.8', true, 'the row carries the push\'s CAPABILITY and the attested mode', CORNER_COLLAB );
	SC::div( 'L3.9', true, 'the BUILD CHAIN push line records the attestation', CORNER_CHAIN );
	[ $e, $b0, $b1 ] = sc_try( $u, static fn () => sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-3', 'B.' ) ] ), 'challenge_response' => $answer ] ) );
	SC::ok( 'L3.10', ( $e['refused'] ?? '' ) === 'CHALLENGE' && $b0 === $b1, 'an answer is single-use: replaying it is refused', json_encode( $e ) );
	$held = $u->nonces->peek( 'Agent A', $u->px );
	[ $e, $b0, $b1 ] = sc_try( $u, static fn () => sc_op( $u, 'PUSH', 'Agent B', [ 'records' => json_encode( [ sc_arec( 'SPR-3', 'B.' ) ] ), 'challenge_response' => 'x' ] ) );
	SC::ok( 'L3.11', ( $e['refused'] ?? '' ) === 'NOT HOLDER' && $b0 === $b1 && $u->nonces->peek( 'Agent A', $u->px ) === $held,
		'another account\'s push is refused by fencing before any nonce is read', json_encode( $e ) );
	$p2 = sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-3', 'The axis is level.' ) ] ) ] );
	SC::ok( 'L3.12', sc_ids( $p2 ) === [ 'SPR-3' ], 'the holder\'s nonce still stands after another account\'s refused push', json_encode( $p2 ) );
	SC::ok( 'L3.13', sc_verify( $u ), 'verify' );

	// L4 fencing.
	$u = sc_uwc( 'b1-L4' );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'A.' ) ] ) ] ) );
	SC::refused( 'L4.1', $a, $b0, $b1, 'an unlocked push is refused' );
	sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'A.' ) ] ), 'block' => 'B2' ] ) );
	SC::refused( 'L4.2', $a, $b0, $b1, 'a push under another grant (another block) is refused' );
	SC::div( 'L4.3', true, 'a push with no grant is refused', 'Custos\'s design: the block is optional; a PUSH naming none lands under the lock\'s grant (harness section L, L61)' );
	$u->now += Landing::LEASE + 5;
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'A.' ) ] ) ] ) );
	SC::refused( 'L4.4', $a, $b0, $b1, 'a push after the expiry is refused' );
	SC::div( 'L4.5', true, 'the lock view reads HOLDER SILENT past the expiry', CORNER_LOCKVIEW );
	$a = sc_op( $u, 'HEARTBEAT', 'Agent A', [ 'block' => 'B1' ] );
	SC::ok( 'L4.6', ( $a['refused'] ?? '' ) === 'NOT HOLDER', 'a heartbeat after the expiry is refused', json_encode( $a ) );
	$a = sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B1' ] );
	SC::div( 'L4.7', isset( $a['released'] ), 'a release after the expiry is refused', 'corner: RELEASE checks the holder, not the lease; the released lock is free either way', json_encode( $a ) );
	sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$u->now += Landing::LEASE + 5;
	$c = sc_op( $u, 'PETITION', 'Agent B', [ 'block' => 'B2' ] );
	SC::ok( 'L4.8', isset( $c['grant'] ) && ( sc_lock( $u )['holder'] ?? '' ) === 'Agent B', 'another account takes an expired lock at once', json_encode( $c ) );

	// L5 HEARTBEAT.
	$u = sc_uwc( 'b1-L5' );
	sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	foreach ( [ 'a heartbeat that does not reach the next EXPIRY STEP writes nothing', 'a heartbeat 40 min in moves the expiry one EXPIRY STEP',
		'the lock page and the badge carry exactly the new expiry' ] as $i => $what ) {
		SC::div( 'L5.' . ( $i + 1 ), true, $what, CORNER_LEASE );
	}
	$u->now += 600;
	$h = sc_op( $u, 'HEARTBEAT', 'Agent A', [ 'block' => 'B2' ] );
	SC::div( 'L5.4', isset( $h['heartbeat'] ), 'a heartbeat under another grant is refused', 'corner: HEARTBEAT keeps the lock\'s block and reads none from the request', json_encode( $h ) );
	$h = sc_op( $u, 'HEARTBEAT', 'Agent B', [ 'block' => 'B1' ] );
	SC::ok( 'L5.5', ( $h['refused'] ?? '' ) === 'NOT HOLDER', 'a heartbeat by another account is refused', json_encode( $h ) );
	SC::div( 'L5.6', true, 'with no push for more than 6 h the heartbeat is refused', CORNER_LEASE );
	SC::div( 'L5.7', true, 'after a push the heartbeat extends again to within one step of now + 6 h', CORNER_LEASE );
	$ok = true;
	for ( $i = 0; $i < 6; $i++ ) {
		$u->now += 1800;
		$pp = sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-' . ( 2 + $i ), "Work $i." ) ] ) ] );
		$hh = sc_op( $u, 'HEARTBEAT', 'Agent A', [] );
		$ok = $ok && sc_ids( $pp ) === [ 'SPR-' . ( 2 + $i ) ] && isset( $hh['heartbeat'] );
	}
	SC::div( 'L5.8', $ok, 'a working lock reaches the 24 h ceiling from the grant and no further', CORNER_LEASE );
	SC::div( 'L5.9', true, 'at the ceiling a heartbeat writes nothing', CORNER_LEASE );
	SC::div( 'L5.10', true, 'past the ceiling the lock has expired', CORNER_LEASE );
	SC::ok( 'L5.11', sc_verify( $u ) && count( sc_register( $u ) ) === 7, 'verify after six pushes (seven records with the MASTER\'s stand-in)' );

	// L6 RELEASE.
	$u = sc_uwc( 'b1-L6' );
	sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$r = sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B1' ] );
	SC::div( 'L6.1', isset( $r['released'] ), 'a release before a push in the grant is refused', CORNER_RELEASE_PUSH, json_encode( $r ) );
	sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'A.' ) ] ) ] );
	$r = sc_op( $u, 'RELEASE', 'Agent B', [ 'block' => 'B1' ] );
	SC::ok( 'L6.2', ( $r['refused'] ?? '' ) === 'NOT HOLDER', 'another account does not release' );
	$u->now += 5;
	$rl = sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B1' ] );
	$lk = sc_lock( $u );
	SC::ok( 'L6.3', isset( $rl['released'] ) && array_key_exists( 'holder', $lk ) && $lk['holder'] === null, 'the holder releases; the lock is free', json_encode( [ $rl, $lk ] ) );
	$bd = sc_badge( $u );
	SC::ok( 'L6.4', strcmp( (string)$bd['last_push'], (string)$bd['last_release'] ) <= 0 && $bd['last_release'] === $rl['released'], 'the badge: LAST RELEASE after LAST PUSH', json_encode( $bd ) );
	$r = sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B1' ] );
	SC::ok( 'L6.5', ( $r['refused'] ?? '' ) === 'NOT HOLDER', 'a second release is refused' );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-3', 'B.' ) ] ) ] ) );
	SC::refused( 'L6.6', $a, $b0, $b1, 'after the release a push is refused' );
	$g = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B2' ] );
	SC::ok( 'L6.7', isset( $g['grant'] ), 'the same account petitions and is granted again' );

	// L7 the queue and the acquisition window.
	$u = sc_uwc( 'b1-L7' );
	sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$pB = sc_op( $u, 'PETITION', 'Agent B', [ 'block' => 'B2' ] );
	SC::div( 'L7.1', ( $pB['refused'] ?? '' ) === 'LOCK HELD', 'B and C wait at positions 1 and 2 in petition order', CORNER_QUEUE );
	SC::ok( 'L7.2', ( $pB['refused'] ?? '' ) === 'LOCK HELD', 'the head does not acquire while the lock is held [Custos: LOCK HELD]' );
	foreach ( [ 'inside the head\'s ACQUISITION WINDOW the second waiter is refused', 'the lock view tells C its place and its time',
		'once the head\'s window has passed the next waiter acquires; the head keeps its place', 'the head acquires next, grant 3' ] as $i => $what ) {
		SC::div( 'L7.' . ( $i + 3 ), true, $what, CORNER_QUEUE );
	}
	SC::ok( 'L7.7', sc_verify( $u ), 'verify' );

	// L8 CLOSED.
	// The UWC CLOSED with Agent A alone on its ACCESS LIST (no MASTER's stand-in: Agent M is not on it).
	$u = sc_uwc( 'b1-L8', 'SPC', false, [ 'Agent A' ] );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_op( $u, 'PETITION', 'Agent B', [ 'block' => 'B1' ] ) );
	if ( isset( $a['grant'] ) ) {
		$p = sc_op( $u, 'PUSH', 'Agent B', [ 'records' => json_encode( [ sc_arec( 'SPC-1', 'Off the access list.' ) ] ) ] );
		SC::defect( 'L8.1', 'under CLOSED an account off the access list does not petition', 'granted, then landed ' . json_encode( sc_ids( $p ) ) );
	} else {
		SC::ok( 'L8.1', ( $a['refused'] ?? '' ) === 'ACCESS' && $b0 === $b1, 'under CLOSED an account off the access list does not petition [Custos: ACCESS]', json_encode( $a ) );
	}
	$u = sc_uwc( 'b1-L8b', 'SPC', false, [ 'Agent A' ] );
	SC::ok( 'L8.2', isset( sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] )['grant'] ), 'an account on the list petitions' );

	// L9 version 1's 0.5.0 lock page.
	SC::div( 'L9.1', true, 'on a 0.5.0 lock page a new petitioner queues behind the old entry', CORNER_V050 );
	SC::div( 'L9.2', true, 'a lock never held has no window to lose', CORNER_V050 );
}

// ================================ b1-fault ====================================================

const CORNER_RANGE = 'corner: Custos writes no record of its own (the strike, the locus gap, the promotion, the withdrawals and the failed VERIFICATION\'s gap are corners), so it holds no reserved range: a UWC\'s identifiers run in one series from <prefix>-1, each the next free one and each an author\'s record; no range, segment, range volume, MANIFEST or INSTANTIATE line is written';
const CORNER_RANGE_R8 = CORNER_RANGE . '; the refusal is sound while Custos writes no record of its own, and the unit that first writes a server record brings back the reserved range and this refusal';
const CORNER_VOLUME = 'corner: Custos keeps one open register volume (Volume 1) until the volume roll is built';

/** A store that lets another writer save $raceTitle once, between a landing's read of it and its save. */
final class ScRacingStore implements \Custos\PageStore {
	public ?string $raceTitle = null;
	public ?string $raceText = null;
	public int $raced = 0;

	public function __construct( public \Custos\PageStore $inner ) {
	}

	public function get( string $title ): ?string {
		$t = $this->inner->get( $title );
		if ( $this->raceTitle === $title && $this->raceText !== null ) {
			$other = $this->raceText;
			$this->raceText = null;
			$this->raced++;
			$this->inner->casPut( $title, $t, $other, 'another request\'s concurrent write', 'Agent B' );
		}
		return $t;
	}

	public function exists( string $title ): bool {
		return $this->inner->exists( $title );
	}

	public function put( string $title, string $text, string $summary ): void {
		$this->inner->put( $title, $text, $summary );
	}

	public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
		return $this->inner->casPut( $title, $expected, $text, $summary, $actor );
	}

	public function appendAs( string $title, string $line, string $summary, string $actor ): string {
		return $this->inner->appendAs( $title, $line, $summary, $actor );
	}
}

/**
 * $u's landing job again, over $store (null: $u's own) with the lock's lease $lease: version 1's TEST
 * LEASE of 120 s is Custos's configured lease ($wgCustosLockLease) set to 120 s.
 */
function sc_reland( stdClass $u, ?\Custos\PageStore $store = null, int $lease = Landing::LEASE ): void {
	$conf = [ 'tps' => '0.4.0', 'd_is' => str_repeat( 'd', 64 ), 'digest' => \Custos\Calculator::digestOf( sc_built() ), 'poll_after' => 30,
		'governor_off' => true, 'lease' => $lease ];
	$u->landing = new Landing( sc_calc(), $store ?? $u->store, sc_titles(), $u->tickets, $u->seats, $u->certs, $conf, static function () use ( $u ): int {
		return $u->now;
	}, static fn (): array => [ 0, 1 ], nonces: $u->nonces, meter: new \Custos\MemMeterStore() );
}

/** The answer to $nonce, as an agent that executes computes it. */
function sc_answer( string $nonce ): string {
	return \Custos\Challenge::response( sc_calc(), $nonce )[1];
}

/** A PUSH of $records by $account answering $nonce, naming $block when given. */
function sc_pushn( stdClass $u, string $account, array $records, string $nonce, ?string $block = null ): array {
	$p = [ 'records' => json_encode( $records, SC_JSON ), 'challenge_response' => sc_answer( $nonce ) ];
	if ( $block !== null ) {
		$p['block'] = $block;
	}
	return sc_op( $u, 'PUSH', $account, $p );
}

/** Version 1's fault gate's VERIFICATION $id of $target. */
function fs_ver( string $id, string $target ): array {
	return [ 'ID' => $id, 'CLASS' => 'VERIFICATION', 'CITES' => [], 'ASSUMPTIONS' => [], 'REGIME' => 'M', 'TARGET' => $target,
		'EXTERNAL' => [ 'VALUE' => '0.0201', 'U_C' => '0.0002', 'UNIT' => 'm', 'QUANTITY' => 'E_x' ],
		'SOURCE' => 'Bench measurement, lab notebook (gate example).', 'AT' => [ [ 'DOF' => 't', 'VALUE' => '0', 'UNIT' => 's' ] ],
		'DIFFERENCE' => [ 'VALUE' => '-1e-4', 'U' => '2.82842712475e-4', 'ZETA' => '-3.53553390593e-1' ] ];
}

/**
 * Version 1's B1 fault suite, the server's side (FS-1 to FS-12; FS-9 has no server side), under its
 * invariants: I1 one holder, a grant issued once; I2 nothing landed twice, nothing by a non-holder;
 * I3 a lost answer changes no committed record; I4 a stale grant lands, releases and extends
 * nothing; I5 a refused request writes nothing. Numbered by scenario and order, FS-1.1.
 */
function gate_b1_fault(): void {
	SC::gate( 'b1-fault' );
	$hex = static fn ( $s ): bool => is_string( $s ) && preg_match( '/\A[0-9a-f]{32}\z/', $s ) === 1;
	$regOf = static fn ( stdClass $u ): ?string => $u->store->get( sc_titles()->registerVolume( $u->px, 1 ) );
	$pick = static fn ( stdClass $u, string $id ): array => array_intersect_key( sc_by( $u )[$id] ?? [], [ 'ID' => 1, 'CLASS' => 1, 'DIGEST' => 1 ] );

	// FS-1 a duplicate PUSH after a lost answer (I2, I3).
	$u = sc_uwc( 'bf-FS1' );
	$g = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$req = [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'First.' ) ], SC_JSON ), 'block' => 'B1', 'challenge_response' => sc_answer( (string)$g['challenge'] ) ];
	$p1 = sc_op( $u, 'PUSH', 'Agent A', $req );
	$reg1 = $regOf( $u );
	$snap1 = sc_snap( $u );
	SC::ok( 'FS-1.1', sc_ids( $p1 ) === [ 'SPR-2' ] && preg_match( '/\A[0-9a-f]{64}\z/', (string)( $p1['landed'][0]['digest'] ?? '' ) ) === 1,
		'the push lands SPR-2 (its answer is then lost on the wire)', json_encode( $p1 ) );
	$e = sc_op( $u, 'PUSH', 'Agent A', $req );
	SC::ok( 'FS-1.2', ( $e['refused'] ?? '' ) === 'CHALLENGE' && str_contains( (string)( $e['detail'] ?? '' ), 'challenge' ),
		'the identical re-send is refused: its answer no longer matches the nonce now outstanding [Custos: CHALLENGE]', json_encode( $e ) );
	SC::ok( 'FS-1.3', $regOf( $u ) === $reg1, 'I2 nothing landed twice: the register is as after the first push' );
	SC::ok( 'FS-1.4', sc_snap( $u ) === $snap1, 'I5 the refused re-send wrote nothing at all' );
	SC::ok( 'FS-1.5', isset( sc_by( $u )['SPR-2'] ) && ( sc_badge( $u )['record_count'] ?? 0 ) === 2 && ( sc_badge( $u )['last_push'] ?? null ) !== null,
		'the recovery reads the record landed and the push counted [Custos: the badge\'s count 2 with the MASTER\'s stand-in, its LAST PUSH set]', json_encode( sc_badge( $u ) ) );
	SC::ok( 'FS-1.6', $hex( $e['challenge'] ?? null ), 'the refusal carried the next nonce, so the next push needs no new petition', json_encode( $e ) );
	$p2 = sc_pushn( $u, 'Agent A', [ sc_arec( 'SPR-3', 'Second.' ) ], (string)( $e['challenge'] ?? '' ) );
	SC::ok( 'FS-1.7', sc_ids( $p2 ) === [ 'SPR-3' ], 'the next push lands the next identifier', json_encode( $p2 ) );
	$u0 = sc_uwc( 'bf-FS1-clean' );
	$g0 = sc_op( $u0, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	sc_pushn( $u0, 'Agent A', [ sc_arec( 'SPR-2', 'First.' ) ], (string)$g0['challenge'], 'B1' );
	// The two landings' LANDED stamps are their clocks' (on the wiki LandJob's wall clock, a second apart or
	// more), and record_digest covers LANDED: the clean record is compared field by field but LANDED and
	// DIGEST, and digested again with the lost answer's stamp, which must give the lost answer's DIGEST.
	$lost = sc_by( $u )['SPR-2'] ?? [];
	$clean = sc_by( $u0 )['SPR-2'] ?? [];
	$sorted = static function ( array $r ) use ( &$sorted ): array {
		ksort( $r );
		foreach ( $r as $k => $v ) {
			$r[$k] = is_array( $v ) ? $sorted( $v ) : $v;
		}
		return $r;
	};
	$bare = static function ( array $r ) use ( $sorted ): array {
		unset( $r['LANDED'], $r['DIGEST'] );
		return $sorted( $r );
	};
	$at = $clean;
	unset( $at['DIGEST'] );
	$at['LANDED'] = $lost['LANDED'] ?? null;
	$redigest = $clean !== [] ? ( sc_calc()->call( 'record', 'record_digest', json_encode( [ 'record' => $at ], SC_JSON ) )['value'][1] ?? null ) : null;
	// Off the wiki both clocks are the scenario's, so the whole record must match, LANDED and DIGEST included,
	// as before the wiki run; on the wiki the stamp is LandJob's wall clock and only the digest is recomputed.
	$stamped = is_string( $lost['LANDED'] ?? null ) && ( $lost['LANDED'] ?? '' ) !== '';
	$same = SCW::$wiki || $sorted( $lost ) === $sorted( $clean );
	SC::ok( 'FS-1.8', $pick( $u, 'SPR-2' ) !== [] && $stamped && $same && $bare( $lost ) === $bare( $clean )
		&& is_string( $redigest ) && preg_match( '/\A[0-9a-f]{64}\z/', $redigest ) === 1 && $redigest === ( $lost['DIGEST'] ?? null ),
		'I3 the record\'s identity and digest after the lost answer equal a clean push\'s [Custos: the record but its LANDED stamp, the digest over the lost answer\'s stamp]',
		json_encode( [ $pick( $u, 'SPR-2' ), $pick( $u0, 'SPR-2' ), $lost['LANDED'] ?? null, $clean['LANDED'] ?? null, $redigest ] ) );

	// FS-2 a repeated RELEASE (I4, I5).
	$u = sc_uwc( 'bf-FS2' );
	sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'First.' ) ] ) ] );
	$r1 = sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B1' ] );
	$snap = sc_snap( $u );
	$lk = sc_lock( $u );
	SC::ok( 'FS-2.1', isset( $r1['released'] ) && array_key_exists( 'holder', $lk ) && $lk['holder'] === null, 'the release frees the lock', json_encode( [ $r1, $lk ] ) );
	$r2 = sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B1' ] );
	SC::ok( 'FS-2.2', ( $r2['refused'] ?? '' ) === 'NOT HOLDER', 'the same RELEASE re-sent (its answer lost) is refused: no holder [Custos: NOT HOLDER]', json_encode( $r2 ) );
	SC::ok( 'FS-2.3', sc_snap( $u ) === $snap, 'I5 the refused release wrote nothing' );
	SC::ok( 'FS-2.4', sc_lock( $u ) === $lk, 'I1 the grant counter is unchanged [Custos: the lock as the release left it, free, no grant]' );

	// FS-3 two accounts petitioning at once: one compare and set wins (I1).
	$u = sc_uwc( 'bf-FS3' );
	$q = sc_fork( $u, 'bf-FS3-queue' );
	$qa = sc_op( $q, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$qb = sc_op( $q, 'PETITION', 'Agent B', [ 'block' => 'B2' ] );
	SC::div( 'FS-3.1', isset( $qa['grant'] ) && ( $qb['refused'] ?? '' ) === 'LOCK HELD', 'both accounts WAITING, Agent A at the head', CORNER_QUEUE, json_encode( [ $qa, $qb ] ) );
	$race = new ScRacingStore( $u->store );
	sc_reland( $u, $race );
	$lt = sc_titles()->lock( $u->px );
	$race->raceTitle = $lt;
	// A benign concurrent write of the lock page (the free lock, a line of prose added below its block): a
	// change of text MediaWiki keeps (a trailing newline alone is trimmed on save, a null edit that moves no base).
	$race->raceText = (string)$u->store->get( $lt ) . "\nTouched by another request.\n";
	// The nonce known for Agent A on this UWC just before the losing request: none over the files; on the
	// wiki the fork bf-FS3-queue's grant left one in the custos_nonce row it shares with its source.
	// Read from the store itself, so on the wiki a losing PETITION that wrote a nonce row is seen (ScNonces::stored
	// reads custos_nonce there); over the files the store's own peek is that read.
	$stored = static fn ( stdClass $u ): ?string => $u->nonces instanceof ScNonces ? $u->nonces->stored( 'Agent A', $u->px ) : $u->nonces->peek( 'Agent A', $u->px );
	$before = $stored( $u );
	$e = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	SC::ok( 'FS-3.2', ( $e['refused'] ?? '' ) === 'PAGE FAULT' && str_contains( (string)( $e['detail'] ?? '' ), 'base moved' ) && $race->raced === 1,
		'the acquisition whose base moved under it loses the compare and set: refused, retry [Custos: PAGE FAULT, base moved]', json_encode( $e ) );
	$lk = sc_lock( $u );
	SC::ok( 'FS-3.3', array_key_exists( 'holder', $lk ) && $lk['holder'] === null && !isset( $e['grant'] ) && $stored( $u ) === $before,
		'I1 no holder and no grant issued by the losing request [Custos: the nonce as it stood before the request]', json_encode( [ $lk, $before, $u->nonces->peek( 'Agent A', $u->px ) ] ) );
	$race->raceTitle = null;
	$a = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	SC::ok( 'FS-3.4', isset( $a['grant'] ) && ( sc_lock( $u )['holder'] ?? '' ) === 'Agent A', 'the retry acquires the lock [Custos: its grant a time]', json_encode( $a ) );
	$b = sc_op( $u, 'PETITION', 'Agent B', [ 'block' => 'B2' ] );
	SC::ok( 'FS-3.5', ( $b['refused'] ?? '' ) === 'LOCK HELD', 'I1 the other account cannot acquire while the lock is held [Custos: LOCK HELD]', json_encode( $b ) );
	SC::ok( 'FS-3.6', ( sc_lock( $u )['granted_at'] ?? '' ) === ( $a['grant'] ?? null ) && ( sc_lock( $u )['holder'] ?? '' ) === 'Agent A',
		'I1 exactly one grant issued [Custos: the lock carries the retry\'s grant alone]', json_encode( sc_lock( $u ) ) );

	// FS-4 a delayed PUSH after release and re-grant (I2, I4).
	$u = sc_uwc( 'bf-FS4' );
	$g1 = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$p = sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'First.' ) ] ) ] );
	$n1b = (string)( $p['challenge'] ?? '' );
	sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B1' ] );
	$g2 = sc_op( $u, 'PETITION', 'Agent B', [ 'block' => 'B2' ] );
	SC::ok( 'FS-4.1', isset( $g2['grant'] ) && strcmp( (string)$g2['grant'], (string)$g1['grant'] ) > 0, 'the second account holds the next grant [Custos: a later grant time, block B2]', json_encode( $g2 ) );
	$snap = sc_snap( $u );
	$delayed = [ sc_arec( 'SPR-3', 'Delayed.' ) ];
	$e = sc_pushn( $u, 'Agent A', $delayed, $n1b, 'B1' );
	SC::ok( 'FS-4.2', ( $e['refused'] ?? '' ) === 'NOT HOLDER', 'I4 the first account\'s delayed push under its old grant is refused by fencing [Custos: NOT HOLDER]', json_encode( $e ) );
	SC::ok( 'FS-4.3', sc_snap( $u ) === $snap, 'I5 nothing written' );
	$e = sc_pushn( $u, 'Agent A', $delayed, $n1b, 'B2' );
	SC::ok( 'FS-4.4', ( $e['refused'] ?? '' ) === 'NOT HOLDER', 'I2 ... nor under the current grant, which it does not hold', json_encode( $e ) );
	SC::ok( 'FS-4.5', sc_snap( $u ) === $snap, 'I5 nothing written' );
	$p = sc_op( $u, 'PUSH', 'Agent B', [ 'records' => json_encode( [ sc_arec( 'SPR-3', 'By the holder.' ) ] ) ] );
	SC::ok( 'FS-4.6', sc_ids( $p ) === [ 'SPR-3' ], 'the holder\'s push lands', json_encode( $p ) );
	sc_op( $u, 'RELEASE', 'Agent B', [ 'block' => 'B2' ] );
	$g3 = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B3' ] );
	SC::ok( 'FS-4.7', isset( $g3['grant'] ) && strcmp( (string)$g3['grant'], (string)$g2['grant'] ) > 0, 'the first account holds again, a third grant [Custos: a later grant time, block B3]', json_encode( $g3 ) );
	$n3 = (string)( $g3['challenge'] ?? '' );
	$snap = sc_snap( $u );
	$delayed2 = [ sc_arec( 'SPR-4', 'Delayed, same holder, old grant.' ) ];
	$e = sc_pushn( $u, 'Agent A', $delayed2, $n3, 'B1' );
	SC::ok( 'FS-4.8', ( $e['refused'] ?? '' ) === 'NOT HOLDER' && str_contains( (string)( $e['detail'] ?? '' ), 'granted for the block B3' ),
		'I4 the same account\'s delayed push under its OLD grant is refused: the grant does not match the current one', json_encode( $e ) );
	SC::ok( 'FS-4.9', sc_snap( $u ) === $snap, 'I5 nothing written' );
	SC::ok( 'FS-4.10', !isset( $e['challenge'] ) && $u->nonces->peek( 'Agent A', $u->px ) === $n3, 'the fencing refusal precedes the challenge, so the outstanding nonce is kept', json_encode( $e ) );
	$p = sc_pushn( $u, 'Agent A', $delayed2, $n3, 'B3' );
	SC::ok( 'FS-4.11', sc_ids( $p ) === [ 'SPR-4' ], '... under the current grant, answering that nonce, it lands', json_encode( $p ) );

	// FS-5 a replayed challenge answer (I5).
	$u = sc_uwc( 'bf-FS5' );
	$g = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$ans = sc_answer( (string)$g['challenge'] );
	sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'First.' ) ] ), 'challenge_response' => $ans ] );
	$snap = sc_snap( $u );
	$e = sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-3', 'Replayed.' ) ] ), 'challenge_response' => $ans ] );
	SC::ok( 'FS-5.1', ( $e['refused'] ?? '' ) === 'CHALLENGE' && str_contains( (string)( $e['detail'] ?? '' ), 'wrong' ) && str_contains( (string)( $e['detail'] ?? '' ), 'REASONED' ),
		'a push replaying the last accepted answer is refused: the answer is wrong for the nonce now outstanding, attested REASONED', json_encode( $e ) );
	SC::ok( 'FS-5.2', sc_snap( $u ) === $snap, 'I5 nothing written' );
	$e2 = sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-3', 'Replayed again.' ) ] ), 'challenge_response' => $ans ] );
	SC::ok( 'FS-5.3', ( $e2['refused'] ?? '' ) === 'CHALLENGE' && $hex( $e['challenge'] ?? null ) && sc_answer( (string)$e['challenge'] ) !== $ans
		&& $hex( $e2['challenge'] ?? null ) && $e2['challenge'] !== $e['challenge'], 'every refusal issues a fresh nonce; the old answer never fits again', json_encode( [ $e, $e2 ] ) );
	$p = sc_pushn( $u, 'Agent A', [ sc_arec( 'SPR-3', 'Answered afresh.' ) ], (string)( $e2['challenge'] ?? '' ) );
	SC::ok( 'FS-5.4', sc_ids( $p ) === [ 'SPR-3' ], 'the push answering the nonce last issued lands', json_encode( $p ) );

	// FS-6 the session cookie invalidated mid-block: the same account, the same grant (the server's side).
	$u = sc_uwc( 'bf-FS6' );
	$g = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$p = sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'Before the cookie died.' ) ] ) ] );
	$p2 = sc_pushn( $u, 'Agent A', [ sc_arec( 'SPR-3', 'After re-login.' ) ], (string)( $p['challenge'] ?? '' ), 'B1' );
	$lk = sc_lock( $u );
	SC::ok( 'FS-6.1', sc_ids( $p2 ) === [ 'SPR-3' ] && ( $lk['holder'] ?? '' ) === 'Agent A' && ( $lk['granted_at'] ?? '' ) === $g['grant'],
		'after re-login the same account pushes under the same grant with the nonce last issued; the lock is untouched (the session is MediaWiki\'s, the grant Custos\'s)', json_encode( [ $p2, $lk ] ) );
	SC::ok( 'FS-6.2', isset( sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B1' ] )['released'] ), '... and releases' );

	// FS-7 HEARTBEAT after the NO-PROGRESS LIMIT, under a lease of 120 s (I4).
	$u = sc_uwc( 'bf-FS7' );
	sc_reland( $u, null, 120 );
	sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$lk = sc_lock( $u );
	SC::ok( 'FS-7.1', strtotime( (string)( $lk['expires_at'] ?? '' ) ) - strtotime( (string)( $lk['granted_at'] ?? '' ) ) === 120,
		'under the lease the first expiry is 120 s from the grant [Custos: the configured lease set to 120 s]', json_encode( $lk ) );
	$u->now += 30;
	sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'Progress.' ) ] ) ] );
	$u->now += 30;
	$h = sc_op( $u, 'HEARTBEAT', 'Agent A', [] );
	SC::ok( 'FS-7.2', isset( $h['heartbeat'] ), 'a heartbeat 30 s after the push extends the lease', json_encode( $h ) );
	$lk = sc_lock( $u );
	$u->now += 100;
	$h = sc_op( $u, 'HEARTBEAT', 'Agent A', [] );
	SC::div( 'FS-7.3', isset( $h['heartbeat'] ), 'a heartbeat more than 120 s after the last push is refused (NO-PROGRESS LIMIT)', CORNER_LEASE, json_encode( $h ) );
	SC::div( 'FS-7.4', ( sc_lock( $u )['expires_at'] ?? '' ) !== ( $lk['expires_at'] ?? '' ), 'I4 the refused heartbeat extended nothing; I5 nothing written', CORNER_LEASE );

	// FS-8 the holder's crash: no heartbeat until expiry; the next waiter acquires (I1, I4).
	$u = sc_uwc( 'bf-FS8' );
	sc_reland( $u, null, 120 );
	$g = sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$p = sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-2', 'Then the holder crashes.' ) ] ) ] );
	$b = sc_op( $u, 'PETITION', 'Agent B', [ 'block' => 'B2' ] );
	$c = sc_op( $u, 'PETITION', 'Agent C', [ 'block' => 'B3' ] );
	SC::ok( 'FS-8.1', ( $b['refused'] ?? '' ) === 'LOCK HELD' && ( $c['refused'] ?? '' ) === 'LOCK HELD', 'I1 while the crashed holder\'s lease runs, nobody acquires [Custos: LOCK HELD]', json_encode( [ $b, $c ] ) );
	$u->now += 125;
	SC::div( 'FS-8.2', !str_contains( (string)json_encode( [ sc_lock( $u ), sc_badge( $u ) ] ), 'SILENT' ), 'past the lease with no heartbeat the lock is HOLDER SILENT', CORNER_LOCKVIEW );
	$snap = sc_snap( $u );
	$late = [ sc_arec( 'SPR-3', 'Late.' ) ];
	$e = sc_pushn( $u, 'Agent A', $late, (string)( $p['challenge'] ?? '' ), 'B1' );
	SC::ok( 'FS-8.3', ( $e['refused'] ?? '' ) === 'NOT HOLDER', 'I4 the crashed holder\'s late push under its grant is refused: expired [Custos: NOT HOLDER, within its lease]', json_encode( $e ) );
	SC::ok( 'FS-8.4', sc_snap( $u ) === $snap, 'I5 nothing written' );
	$q = sc_fork( $u, 'bf-FS8-queue' );
	sc_reland( $q, null, 120 );
	$qc = sc_op( $q, 'PETITION', 'Agent C', [ 'block' => 'B3' ] );
	SC::div( 'FS-8.5', isset( $qc['grant'] ), 'the second waiter may not take it before the head\'s ACQUISITION WINDOW passes', CORNER_QUEUE, json_encode( $qc ) );
	$a = sc_op( $u, 'PETITION', 'Agent B', [ 'block' => 'B2' ] );
	SC::ok( 'FS-8.6', isset( $a['grant'] ) && strcmp( (string)$a['grant'], (string)$g['grant'] ) > 0 && ( sc_lock( $u )['holder'] ?? '' ) === 'Agent B',
		'the head acquires at once after the expiry: the next grant, issued once (I1)', json_encode( $a ) );
	$e = sc_pushn( $u, 'Agent A', $late, (string)( $p['challenge'] ?? '' ), 'B1' );
	SC::ok( 'FS-8.7', ( $e['refused'] ?? '' ) === 'NOT HOLDER', 'I4 the old holder\'s grant lands nothing after the re-grant either', json_encode( $e ) );
	$e = sc_op( $u, 'HEARTBEAT', 'Agent A', [] );
	SC::ok( 'FS-8.8', ( $e['refused'] ?? '' ) === 'NOT HOLDER', 'I4 ... and extends nothing', json_encode( $e ) );
	$e = sc_op( $u, 'RELEASE', 'Agent A', [ 'block' => 'B1' ] );
	SC::ok( 'FS-8.9', ( $e['refused'] ?? '' ) === 'NOT HOLDER', 'I4 ... and releases nothing', json_encode( $e ) );
	$q = sc_fork( $u, 'bf-FS8-release' );
	sc_reland( $q, null, 120 );
	$r = sc_op( $q, 'RELEASE', 'Agent B', [ 'block' => 'B2' ] );
	SC::div( 'FS-8.10', isset( $r['released'] ), 'a release before a push is refused; the holder keeps the lock until it pushes or its lease ends', CORNER_RELEASE_PUSH, json_encode( $r ) );
	$u->now += 125;
	$a2 = sc_op( $u, 'PETITION', 'Agent C', [ 'block' => 'B3' ] );
	SC::ok( 'FS-8.11', isset( $a2['grant'] ) && strcmp( (string)$a2['grant'], (string)$a['grant'] ) > 0 && ( sc_lock( $u )['holder'] ?? '' ) === 'Agent C',
		'after the second lease lapses, the remaining waiter acquires at once; every grant issued once (I1)', json_encode( $a2 ) );

	// FS-10 a PUSH carrying a field the server writes (I5).
	$u = sc_uwc( 'bf-FS10' );
	sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$bad = sc_arec( 'SPR-2', 'With a server field.' ) + [ 'GRADE' => 'ESTABLISHED', 'LANDED_BY' => 'Custos' ];
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ $bad ], 'Agent A' ) );
	SC::refused( 'FS-10.1', $a, $b0, $b1, 'a record carrying GRADE and LANDED_BY is refused at PUSH (REC-07: a field the server writes)' );
	SC::ok( 'FS-10.2', $b0 === $b1, 'I5 nothing written' );
	$bad2 = sc_arec( 'SPR-2', 'With a digest.' ) + [ 'DIGEST' => str_repeat( '0', 64 ) ];
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ $bad2 ], 'Agent A' ) );
	SC::refused( 'FS-10.3', $a, $b0, $b1, '... a pushed DIGEST likewise' );

	// FS-11 a VERIFICATION pushed before its TARGET (I5). Custos refuses the class itself (LANDS), so
	// the refusals below are not version 1's (the TARGET does not resolve; REC-91): divergent, not passes.
	$lands = static fn ( array $a ): bool => ( $a['refused'] ?? '' ) === 'RECORD CHECK' && str_contains( (string)json_encode( $a['problems'] ?? [] ), '"LANDS"' );
	$u = sc_uwc( 'bf-FS11' );
	sc_op( $u, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ fs_ver( 'SPR-2', 'SPR-3' ) ], 'Agent A' ) );
	if ( isset( $a['landed'] ) ) {
		SC::defect( 'FS-11.1', 'a VERIFICATION whose TARGET has not landed is refused (the TARGET does not resolve)', 'Custos landed it: ' . json_encode( $a['landed'] ) );
	} else {
		SC::div( 'FS-11.1', $lands( $a ) && $b0 === $b1, 'a VERIFICATION whose TARGET has not landed is refused (the TARGET does not resolve) [Custos: the class is refused, LANDS]', CORNER_VERIFICATION, json_encode( $a ) );
	}
	SC::ok( 'FS-11.2', $b0 === $b1, 'I5 nothing written' );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ mrec( 'SPR-2', '0.0200', '0.0002', [] ), fs_ver( 'SPR-3', 'SPR-2' ) ], 'Agent A' ) );
	if ( isset( $a['landed'] ) ) {
		SC::defect( 'FS-11.3', 'a VERIFICATION in its TARGET\'s own push is refused (REC-91)', 'Custos landed it: ' . json_encode( $a['landed'] ) );
	} else {
		SC::div( 'FS-11.3', $lands( $a ) && $b0 === $b1, 'a VERIFICATION in its TARGET\'s own push is refused (REC-91) [Custos: the class is refused, LANDS]', CORNER_VERIFICATION, json_encode( $a ) );
	}
	$p = sc_push( $u, [ mrec( 'SPR-2', '0.0200', '0.0002', [] ) ], 'Agent A' );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ fs_ver( 'SPR-3', 'SPR-2' ) ], 'Agent A' ) );
	SC::div( 'FS-11.4', sc_ids( $p ) === [ 'SPR-2' ] && $lands( $a ) && $b0 === $b1, 'pushed after its TARGET\'s push, the VERIFICATION lands', CORNER_VERIFICATION, json_encode( [ $p, $a ] ) );

	// FS-12 citing a REFUTED or HELD record (I5). Version 1 landed the two M records and struck the
	// farther; the strike screen refuses the batch whole, STRIKE OWED (a design row), so no struck record
	// exists to cite. The refusal of a citation is tested over a register that holds the pair, set in
	// place by fixture, as the strike would have met it.
	$u = sc_uwc( 'bf-FS12' );
	sc_push( $u, [ sc_arec( 'SPR-2', 'The gauge reads true.' ) ], 'Agent A' );
	[ $p, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ mrec( 'SPR-3', '0', '0.001', [] ), mrec( 'SPR-4', '1', '0.001', [ 'SPR-2' ] ) ], 'Agent A' ) );
	if ( isset( $p['landed'] ) ) {
		SC::defect( 'FS-12.1', 'two M records 1000 u apart: the farther is struck, REFUTED', 'Custos landed a batch the strike screen holds: ' . json_encode( $p['landed'] ) );
	} else {
		SC::div( 'FS-12.1', sc_strike_owed( $p, $b0, $b1 ), 'two M records 1000 u apart: the farther is struck, REFUTED [Custos: refused STRIKE OWED, nothing written]', DESIGN_STRIKE, json_encode( $p ) );
	}
	// The pair within k u of each other lands; the fixture then moves SPR-4 to 1000 u, as the strike would have met it.
	$p = sc_push( $u, [ mrec( 'SPR-3', '0', '0.001', [] ), mrec( 'SPR-4', '0.002', '0.001', [ 'SPR-2' ] ) ], 'Agent A' );
	$pairLanded = sc_ids( $p ) === [ 'SPR-3', 'SPR-4' ];
	$f = sc_fork( $u, 'bf-FS12-cite' );
	// The register's title is $x's own: on the wiki each UWC has its title root, and sc_titles() names the
	// pages of the UWC last read, so $x is read (its prefix) before its title is taken.
	$setIn = static function ( stdClass $x, string $id, string $field, string $to ): void {
		$px = $x->px;
		$t = sc_titles()->registerVolume( $px, 1 );
		$reg = sc_register( $x );
		foreach ( $reg as &$r ) {
			if ( $r['ID'] === $id ) {
				$r[$field] = $to;
			}
		}
		unset( $r );
		$text = sc_calc()->call( 'canonical', 'canonical_json', json_encode( [ 'value' => $reg ], SC_JSON ) )['value'];
		$x->store->tamper( $t, PageTexts::register( $x->px, 1, $text ) );
	};
	$setIn( $f, 'SPR-4', 'VALUE', '1' );
	[ $a, $b0, $b1 ] = sc_try( $f, static fn () => sc_push( $f, [ lcite( 'SPR-5', [ 'SPR-4' ] ) ], 'Agent A' ) );
	$owed = sc_strike_owed( $a, $b0, $b1 );
	if ( isset( $a['landed'] ) || $owed ) {
		SC::refused( 'FS-12.2', $a, $b0, $b1, 'a record citing the REFUTED record is refused (SR2) [the strike rule would strike it: STRIKE OWED]' );
	} else {
		SC::ok( 'FS-12.2', false, 'a record citing the REFUTED record is refused (SR2) [the strike rule would strike it: STRIKE OWED], by the strike screen', json_encode( $a ) );
	}
	SC::ok( 'FS-12.3', $b0 === $b1, 'I5 nothing written' );
	// A HELD record: set by fixture, in place, as version 1 set it (it had no HOLD writer either). The
	// register is checked to verify after it, so the refusal below names the citation and not a failed verify.
	$setIn( $u, 'SPR-3', 'STATUS', 'HELD' );
	SC::ok( 'FS-12.4', $pairLanded && ( sc_by( $u )['SPR-3']['STATUS'] ?? '' ) === 'HELD' && sc_verify( $u ), 'FIXTURE: SPR-3 set HELD in place; the register verifies' );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ lcite( 'SPR-5', [ 'SPR-3' ] ) ], 'Agent A' ) );
	$named = str_contains( (string)json_encode( $a['problems'] ?? [] ), 'does not stand (HELD)' );
	if ( isset( $a['landed'] ) || $named ) {
		SC::refused( 'FS-12.5', $a, $b0, $b1, 'a record citing the HELD record is refused (SR2: a HELD record does not stand)' );
	} else {
		SC::ok( 'FS-12.5', false, 'a record citing the HELD record is refused (SR2: a HELD record does not stand), by the citation check', json_encode( $a ) );
	}
	SC::ok( 'FS-12.6', $b0 === $b1, 'I5 nothing written' );
}


// ================================ b1-range ====================================================

/**
 * Version 1's B1 reserved range (R1 to R8): the identifiers version 1's own writers (the strike and
 * its locus gap, promotion, the withdrawals, the failed VERIFICATION's gap) took from a range kept
 * apart from the authors' series. Numbered by case and order, R2.1.
 */
function gate_b1_range(): void {
	SC::gate( 'b1-range' );
	$vol = static fn ( stdClass $u, int $v ): bool => $u->store->exists( sc_titles()->registerVolume( $u->px, $v ) );
	$classes = static fn ( stdClass $u ): array => array_values( array_unique( array_column( sc_register( $u ), 'CLASS' ) ) );
	// Nothing of the range is observable: the badge (Custos's meta) names none, no record has an identifier
	// of the range (SPR-1000001 up) and its first volume (100001) does not exist.
	$noRange = static fn ( stdClass $u ): bool => !str_contains( (string)json_encode( sc_badge( $u ) ), 'range' )
		&& preg_grep( '/-100\d{4}\z/', array_column( sc_register( $u ), 'ID' ) ) === []
		&& !$u->store->exists( sc_titles()->registerVolume( $u->px, 100001 ) );
	$noView = static fn ( stdClass $u ): bool => !$u->store->exists( sc_titles()->reading( $u->px ) )
		&& !$u->store->exists( sc_titles()->controlPanel( $u->px ) );

	// R1 instantiation fixes the range.
	$u = sc_uwc( 'br-R1' );
	SC::div( 'R1.1', $noRange( $u ) && count( sc_register( $u ) ) === 1,
		'a UWC instantiated holds the range 1,000,001-1,001,000 in its meta and on its INSTANTIATE line', CORNER_RANGE );

	// R2 the SR5 strike and its locus gap from the range.
	$u = fresh( 'br-R2' );
	$recs = [ arec( 'SPR-5', 'The second gauge reads true.' ) ];
	for ( $i = 6; $i <= 15; $i++ ) {
		$recs[] = mrec( "SPR-$i", '0', '0.001', [], 'E_z' );
	}
	$recs[] = mrec( 'SPR-16', '0.01', '0.001', [ 'SPR-5' ], 'E_z' );
	// Version 1 landed the batch and struck SPR-16; the strike screen refuses it whole, STRIKE OWED.
	[ $p, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, $recs, 'Agent A' ) );
	if ( isset( $p['landed'] ) ) {
		SC::defect( 'R2.1', 'SPR-16 struck by SR5', 'Custos landed a batch the strike screen holds: ' . json_encode( $p['landed'] ) );
	}
	$owed = sc_strike_owed( $p, $b0, $b1 );
	SC::div( 'R2.1', $owed, 'SPR-16 struck by SR5; its WITHDRAWAL is SPR-1000001, the first reserved identifier', DESIGN_STRIKE, json_encode( $p ) );
	SC::div( 'R2.2', $owed, 'the SR5_LOCUS gap is SPR-1000002, TRIGGER the withdrawal', DESIGN_STRIKE, json_encode( $p ) );
	SC::div( 'R2.3', $owed, 'the main series is not consumed: next SPR-17; SPR-16 REFUTED', DESIGN_STRIKE, json_encode( $p ) );
	SC::div( 'R2.4', $noRange( $u ), 'the meta\'s segment advanced to next 1,000,003', CORNER_RANGE );
	SC::div( 'R2.5', !$vol( $u, 100001 ), 'the two records of the range live on Volume 100001 (OPEN), the range\'s first volume; no VOID is written there', CORNER_RANGE );
	SC::ok( 'R2.6', !$vol( $u, 3 ) && !$vol( $u, 100000 ), 'no other volume is created: none between the main series and the range' );
	SC::div( 'R2.7', $owed && !$vol( $u, 2 ) && count( sc_register( $u ) ) === 4, 'Volume 2 holds the main series only (SPR-11 to SPR-16), no VOID', DESIGN_STRIKE );
	SC::div( 'R2.8', !$vol( $u, 100001 ), 'the MANIFEST lists the range\'s volume with its content digest', CORNER_RANGE );
	SC::ok( 'R2.9', sc_verify( $u ), 'verify: every record (the range\'s included) and both chains [Custos: every record of the register]' );
	SC::div( 'R2.10', !$u->store->exists( sc_titles()->buildChainHead() ) && !str_contains( (string)json_encode( $p ), 'BUILD CHAIN' ), 'the BUILD CHAIN push line names the server\'s writes by their reserved identifiers', CORNER_CHAIN );
	SC::div( 'R2.11', $noView( $u ), 'the register view lists the range\'s records', CORNER_VIEWS );

	// R3 promotion from the range.
	$u = fresh( 'br-R3' );
	SC::div( 'R3.1', !in_array( 'PROMOTION', $classes( $u ), true ) && count( sc_register( $u ) ) === 4, 'the PROMOTION of SPR-3 is SPR-1000001', CORNER_PROMOTION );
	$p = sc_push( $u, [ arec( 'SPR-5', 'Unrelated.' ) ], 'Agent A' );
	SC::ok( 'R3.2', sc_ids( $p ) === [ 'SPR-5' ] && !isset( $p['promotion'] ), 'the next pushed record takes SPR-5: no promotion took a main-series identifier', json_encode( $p ) );

	// R4 the supersession and the author's withdrawal from the range.
	$u = fresh( 'br-R4' );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ p1( 'SPR-3', 'SPR-5', 'SPR-3', [ 'STATEMENT' => 'Dividing EOM_X by m (positive by A_mpos) gives dv/dt = -(k_s/m) x; restated.' ] ) ], 'Agent A' ) );
	SC::div( 'R4.1', ( $a['refused'] ?? '' ) === 'RECORD CHECK' && $b0 === $b1, 'the supersession\'s WITHDRAWAL is SPR-1000001', CORNER_WITHDRAW, json_encode( $a ) );
	$a = sc_op( $u, 'PUSH', 'Agent A', [ 'records' => '[]', 'withdraw' => '["SPR-4"]' ] );
	SC::div( 'R4.2', ( $a['refused'] ?? '' ) === 'OPS', 'the author\'s WITHDRAWAL is SPR-1000002; the main series stays at SPR-6', CORNER_REQUEST, json_encode( $a ) );
	SC::ok( 'R4.3', sc_verify( $u ), 'verify' );

	// R5 a failed VERIFICATION's SR7 gap from the range.
	$u = fresh( 'br-R5' );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, [ ver( 'SPR-5', 'SPR-4', '0.03', '0.001' ) ], 'Agent A' ) );
	SC::div( 'R5.1', isset( $a['refused'] ) && $b0 === $b1, 'the SR7_ASSUMPTIONS gap a failed VERIFICATION writes is SPR-1000001', CORNER_VERIFICATION, json_encode( $a ) );
	SC::div( 'R5.2', $noView( $u ), 'its GAP VIEW reads from the range\'s volume', CORNER_VIEWS );

	// R6 a UWC instantiated before the range takes it at its first landing under it.
	$u = fresh( 'br-R6' );
	SC::div( 'R6.1', !in_array( 'PROMOTION', $classes( $u ), true ), 'the UWC of version 1\'s earlier form: no range in its meta; its PROMOTION is SPR-5 (main series)', CORNER_PROMOTION );
	// No PROMOTION took SPR-5, so the push's identifiers run one below version 1's (SPR-5 to SPR-16).
	$recs = [ arec( 'SPR-5', 'The second gauge reads true.' ) ];
	for ( $i = 6; $i <= 15; $i++ ) {
		$recs[] = mrec( "SPR-$i", '0', '0.001', [], 'E_z' );
	}
	$recs[] = mrec( 'SPR-16', '0.01', '0.001', [ 'SPR-5' ], 'E_z' );
	[ $p, $b0, $b1 ] = sc_try( $u, static fn () => sc_push( $u, $recs, 'Agent A' ) );
	if ( isset( $p['landed'] ) ) {
		SC::defect( 'R6.2', 'its first landing under the range', 'Custos landed a batch the strike screen holds: ' . json_encode( $p['landed'] ) );
	}
	$owed = sc_strike_owed( $p, $b0, $b1 );
	SC::div( 'R6.2', $owed && $noRange( $u ), 'its first landing under the range sets the range and says so on the push\'s BUILD CHAIN line', DESIGN_STRIKE, json_encode( $p ) );
	SC::div( 'R6.3', $owed && !isset( sc_by( $u )['SPR-1000001'] ), 'the strike takes SPR-1000001; the earlier PROMOTION keeps SPR-5', DESIGN_STRIKE );
	// The batch is refused, so the next step's register is re-seeded by the same identifiers in a batch the
	// strike screen clears (SPR-16 agrees with the rest); the step then tests what version 1 tested.
	$recs[11] = mrec( 'SPR-16', '0', '0.001', [ 'SPR-5' ], 'E_z' );
	sc_push( $u, $recs, 'Agent A' );
	$p = sc_push( $u, [ arec( 'SPR-17', 'More.' ) ], 'Agent A' );
	SC::div( 'R6.4', sc_ids( $p ) === [ 'SPR-17' ] && $noRange( $u ), 'the range is set once: the next push line carries none', CORNER_RANGE, json_encode( $p ) );
	SC::ok( 'R6.5', sc_verify( $u ), 'verify across the main series and the range [Custos: the main series alone]' );

	// R7 a spent segment.
	SC::div( 'R7.1', $noRange( $u ) && !isset( sc_by( $u )['SPR-1000003'] ), 'a two-identifier segment spent after SPR-1000002: SPR-1000003 opens the next, named on the push line', CORNER_RANGE );
	SC::div( 'R7.2', $noRange( $u ) && !isset( sc_by( $u )['SPR-1000003'] ) && sc_verify( $u ), 'verify; the record of the second segment loads', CORNER_RANGE );

	// R8 the main series never enters the range.
	$u = fresh( 'br-R8' );
	$recs = [];
	for ( $i = 5; $i <= 20; $i++ ) {
		$recs[] = arec( "SPR-$i", "Item $i." );
	}
	$p = sc_push( $u, $recs, 'Agent A' );
	SC::ok( 'R8.1', count( sc_ids( $p ) ) === 16 && ( $p['record_count'] ?? 0 ) === 20, 'the main series fills up to SPR-20 [Custos: the register\'s count 20, SPR-21 its next free identifier]', json_encode( $p ) );
	$p = sc_push( $u, [ arec( 'SPR-21', 'One too many.' ) ], 'Agent A' );
	SC::div( 'R8.2', sc_ids( $p ) === [ 'SPR-21' ], 'a push that would reach the range (set low, at SPR-21, for the test) is refused', CORNER_RANGE_R8, json_encode( $p ) );
}

// ================================ b1-inc4 =====================================================

const CORNER_AUDIT = 'corner: the audit trigger (AUTOMATIC or ON REQUEST), the audit blocks and the dispute rule are not built; a UWC\'s pages carry no AUDIT_TRIGGER';
const CORNER_FLEET = 'corner: the fleet is not modelled: no UWC index page is written (its title, the UWC root\'s Index, is reserved) and there is no fleet cap on WAITING petitions; a PETITION is answered for its own UWC alone (granted on a free or expired lock, else LOCK HELD)';
const CORNER_STATUS = 'corner: STATUS carries the Calculator\'s version and digest as configured ($wgCustosBuild) and the governor\'s level; no computed digest, consistency flag, binding (TPS, D(IS)) or test lease';
const DESIGN_TREE = 'Custos\'s design: the integrity check digests the Calculator\'s binary (Calculator::digestOf, its SHA-256, pinned by $wgCustosBuild) before every start, not the extension\'s deployed tree; no BUILD.json is read';
const DESIGN_HALT = 'Custos\'s design: the INTEGRITY HALT answers the words "digest mismatch" alone (Refusal::TABLE), the digests going to the error channel only; it digests the Calculator\'s binary, not the extension\'s tree';
const DESIGN_ALWAYS = 'Custos\'s design: the digest check always runs; a Calculator with no pinned digest makes no call (CALCULATOR FAULT), so there is no landing without the check';
const CORNER_OPS = 'corner: action=pma\'s ops are PETITION, POLL, PUSH, RELEASE, HEARTBEAT, STATUS, INQUIRE and STRUCTURE_TEST: no NEWUWC (the seeding is the Operator\'s SeedUwc), ACQUIRE or RETURN, and STATUS is the site\'s part, taking no prefix';
const CORNER_TPCRUN = 'corner: the Calculator is not an op of action=pma (no TPCRUN): it is called by the landing job alone; GA1 refuses the op (custos-op)';
const DESIGN_SCRUB = 'Custos\'s design: a fault\'s answer carries a fixed word and a detail from a closed set (Refusal::TABLE), never the message, so there is nothing to scrub and no words of the error are kept';
const CORNER_PREFIX_LONG = 'corner: a prefix is bounded at 255 bytes (the column ct_prefix), not 64 characters, so a prefix of 65 letters is taken; SP-R, 1SPR, "SPR R" and ../x are refused custos-prefix';
const CORNER_PREFIX_EDGE = 'Custos\'s design: a prefix that begins or ends with an underscore is refused custos-prefix (its title segment would begin or end with a space), so _a9 is refused; SPR passes';
const CORNER_TESTLEASE = 'corner: the lock\'s lease is one configured span for the site ($wgCustosLockLease), not a TEST LEASE per UWC; version 1\'s 120 s lease is that span set to 120 s';

/** $u's landing job over $calc (a Calculator over another binary), the lease $lease. */
function ic_reland( stdClass $u, \Custos\Calculator $calc, int $lease = Landing::LEASE ): void {
	$conf = [ 'tps' => '0.4.0', 'd_is' => str_repeat( 'd', 64 ), 'digest' => \Custos\Calculator::digestOf( sc_built() ), 'poll_after' => 30,
		'governor_off' => true, 'lease' => $lease ];
	$u->landing = new Landing( $calc, $u->store, sc_titles(), $u->tickets, $u->seats, $u->certs, $conf, static function () use ( $u ): int {
		return $u->now;
	}, static fn (): array => [ 0, 1 ], nonces: $u->nonces, meter: new \Custos\MemMeterStore() );
}

/** A Calculator over a copy of the built pcalc with one byte appended, pinned to the true binary's digest. */
function ic_tampered(): \Custos\Calculator {
	$p = sc_scratch() . '/pcalc-tampered';
	if ( !is_file( $p ) ) {
		copy( sc_built(), $p );
		file_put_contents( $p, "\0", FILE_APPEND );
		chmod( $p, 0755 );
	}
	return new \Custos\Calculator( $p, [ 'version' => sc_calc_version(), 'digest' => \Custos\Calculator::digestOf( sc_built() ) ],
		new \Custos\Tests\ProcRunner(), 'cli', new \Custos\Tests\AnyResidence() );
}

/** sc_op, a fault the landing job rethrows read back from the ticket's answer ("thrown": its class). */
function ic_op( stdClass $u, string $op, string $account, array $params = [] ): array {
	$nonce = sc_nonce( $u, $account );
	if ( $op === 'PUSH' && !array_key_exists( 'challenge_response', $params ) && $nonce !== null ) {
		$params['challenge_response'] = sc_answer( $nonce );
	}
	$id = $u->ops->run( $op, $u->px, $account, $params )['ticket'];
	sc_tick( $u );
	try {
		return $u->landing->run( $id );
	} catch ( \Throwable $e ) {
		return (array)json_decode( (string)( $u->tickets->get( $id )['answer'] ?? 'null' ), true ) + [ 'thrown' => \Custos\Refusal::faultClass( $e ) ];
	}
}

/** A refusal by Ops (GA1) of $fn, or null. */
function ic_ops( callable $fn ): ?\Custos\Refusal {
	try {
		$fn();
		return null;
	} catch ( \Custos\Refusal $e ) {
		return $e;
	}
}

/**
 * Version 1's B1 increment 4 (I1 to I7), 54 assertions, numbered by section and order (I3.4). Version 1's
 * accounts Gemini and Claude are Agent A and Agent B; its UWC index and fleet run over four UWCs whose
 * pages, tickets, seats and nonces share one folder.
 */
function gate_b1_inc4(): void {
	SC::gate( 'b1-inc4' );
	$noPage = static function ( stdClass $u, string $needle ): bool {
		foreach ( sc_snap( $u ) as $t ) {
			if ( str_contains( (string)$t, $needle ) ) {
				return false;
			}
		}
		return true;
	};

	// I1 the AUDIT TRIGGER's default.
	$u = sc_uwc( 'ic-I1', 'SPA', false );
	$none = $noPage( $u, 'AUDIT' );
	SC::div( 'I1.1', $none, 'a new UWC with nothing chosen takes AUDIT TRIGGER AUTOMATIC; ACCESS CLOSED and BIBLIOGRAPHY OFF as before', CORNER_AUDIT );
	SC::div( 'I1.2', $none, 'ON REQUEST chosen is kept', CORNER_AUDIT );
	SC::div( 'I1.3', $none, 'another value is refused', CORNER_AUDIT );
	SC::div( 'I1.4', $none, 'the declared UWC\'s control panel shows AUDIT_TRIGGER AUTOMATIC', CORNER_VIEWS );

	// I2 the UWC index and the fleet cap: four UWCs in one folder.
	$dir = sc_scratch() . '/ic-I2';
	$fleet = [];
	foreach ( [ 'SPR', 'SPB', 'SPC', 'SPD' ] as $px ) {
		sc_uwc( "ic-I2-$px", $px, false );
		sc_copy( sc_scratch() . "/ic-I2-$px", $dir );
	}
	foreach ( [ 'SPR', 'SPB', 'SPC', 'SPD' ] as $px ) {
		$fleet[$px] = sc_open( $dir, $px, 1791158400 );
	}
	$noIndex = !in_array( sc_titles()->fleetIndex(), $fleet['SPR']->store->titles(), true );
	SC::div( 'I2.1', $noIndex, 'the UWC index names every instantiated UWC, sorted', CORNER_FLEET );
	$g = [];
	foreach ( [ 'SPR', 'SPB', 'SPC' ] as $px ) {
		$g[$px] = sc_op( $fleet[$px], 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	}
	$three = isset( $g['SPR']['grant'], $g['SPB']['grant'], $g['SPC']['grant'] );
	SC::div( 'I2.2', $three, 'Agent A WAITING on three UWCs [Custos: the holder of three]', CORNER_QUEUE, json_encode( $g ) );
	$d = sc_op( $fleet['SPD'], 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	SC::div( 'I2.3', isset( $d['grant'] ), 'a fourth WAITING petition across the fleet is refused, naming the three', CORNER_FLEET, json_encode( $d ) );
	SC::div( 'I2.4', ( sc_lock( $fleet['SPD'] )['holder'] ?? '' ) === 'Agent A', '... and SPD\'s queue is untouched', CORNER_FLEET );
	$again = sc_op( $fleet['SPR'], 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	SC::div( 'I2.5', isset( $again['grant'] ), 'the per-UWC rule still holds: a second WAITING petition on SPR is refused', CORNER_REGRANT, json_encode( $again ) );
	$b = sc_op( $fleet['SPD'], 'PETITION', 'Agent B', [ 'block' => 'B2' ] );
	SC::div( 'I2.6', ( $b['refused'] ?? '' ) === 'LOCK HELD', 'another account petitions SPD (the cap is per account) and queues', CORNER_QUEUE, json_encode( $b ) );
	SC::div( 'I2.7', ( sc_lock( $fleet['SPR'] )['holder'] ?? '' ) === 'Agent A', 'acquiring SPR takes Agent A\'s SPR row to ASSIGNED: WAITING on two', CORNER_QUEUE );
	SC::div( 'I2.8', isset( $d['grant'] ), '... so the SPD petition is accepted, at position 2', CORNER_QUEUE );
	SC::div( 'I2.9', $noIndex, 'FIXTURE: SPC dropped from the index (a UWC instantiated before 0.6.0)', CORNER_FLEET );
	SC::div( 'I2.10', $noIndex, '... the count no longer sees SPC', CORNER_FLEET );
	$c = sc_op( $fleet['SPC'], 'PETITION', 'Agent B', [ 'block' => 'B2' ] );
	SC::div( 'I2.11', ( $c['refused'] ?? '' ) === 'LOCK HELD' && !in_array( sc_titles()->fleetIndex(), $fleet['SPC']->store->titles(), true ),
		'a PETITION on SPC puts it back into the index', CORNER_FLEET, json_encode( $c ) );
	SC::div( 'I2.12', $noIndex, '... and the count sees Agent A\'s SPC row again', CORNER_FLEET );

	// I3 the BUILD LINE and the INTEGRITY HALT: the Calculator's binary changed under Custos.
	$u = sc_uwc( 'ic-I3' );
	SC::div( 'I3.1', true, 'the first landing under a build appends one DEPLOYED line after the genesis and before its own line', CORNER_CHAIN );
	$p = sc_push( $u, [ sc_arec( 'SPR-2', 'First.' ) ], 'Agent A' );
	SC::div( 'I3.2', sc_ids( $p ) === [ 'SPR-2' ], 'a second landing under the same build appends no second DEPLOYED line', CORNER_CHAIN, json_encode( $p ) );
	$build = [ 'version' => sc_calc_version(), 'digest' => \Custos\Calculator::digestOf( sc_built() ) ];
	$st = ( new \Custos\Ops( $u->tickets, static function ( int $id ): void {
	}, build: $build ) )->status( [], 'Agent A' );
	SC::div( 'I3.3', ( $st['build'] ?? null ) === $build, 'STATUS carries the build declared and computed, consistent, and the binding', CORNER_STATUS, json_encode( $st ) );
	ic_reland( $u, ic_tampered() );
	$n0 = $u->nonces->peek( 'Agent A', $u->px );
	[ $e, $b0, $b1 ] = sc_try( $u, static fn () => ic_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-3', 'Second.' ) ] ) ] ) );
	SC::div( 'I3.4', ( $e['refused'] ?? '' ) === 'INTEGRITY HALT' && ( $e['detail'] ?? '' ) === 'digest mismatch',
		'a push under a tree that is not the build\'s is refused: INTEGRITY HALT, naming both digests', DESIGN_HALT, json_encode( $e ) );
	SC::ok( 'I3.5', ( $e['refused'] ?? '' ) === 'INTEGRITY HALT' && $b0 === $b1, '... and nothing was written (the register, the lock, the badge unchanged)', json_encode( $e ) );
	SC::ok( 'I3.6', $u->nonces->peek( 'Agent A', $u->px ) === $n0 && !isset( $e['challenge'] ),
		'... the halt precedes the session checks, so no nonce was consumed and none is issued', json_encode( $e ) );
	SC::div( 'I3.7', true, 'a declaration is refused the same way; no register is created', CORNER_SEED );
	SC::div( 'I3.8', true, 'STATUS reports the inconsistency', CORNER_STATUS );
	sc_reland( $u );
	$p = sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-3', 'Second.' ) ] ) ] );
	SC::div( 'I3.9', sc_ids( $p ) === [ 'SPR-3' ], 'the tree restored, the push lands; still one DEPLOYED line', CORNER_CHAIN, json_encode( $p ) );
	SC::div( 'I3.10', true, '... and the declaration too', CORNER_SEED );
	$p = sc_op( $u, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-4', 'Third.' ) ] ) ] );
	SC::div( 'I3.11', sc_ids( $p ) === [ 'SPR-4' ], 'a new build\'s first landing appends its own DEPLOYED line: one line per deployed build', CORNER_CHAIN, json_encode( $p ) );
	SC::ok( 'I3.12', sc_verify( $u ), 'the chain verifies from genesis through the DEPLOYED lines [Custos: verify over the register; no chain]' );
	$unpinned = new \Custos\Calculator( sc_built(), [ 'version' => sc_calc_version(), 'digest' => '' ], new \Custos\Tests\ProcRunner(), 'cli', new \Custos\Tests\AnyResidence() );
	$f = sc_fork( $u, 'ic-I3-unpinned' );
	ic_reland( $f, $unpinned );
	[ $e, $b0, $b1 ] = sc_try( $f, static fn () => ic_op( $f, 'PUSH', 'Agent A', [ 'records' => json_encode( [ sc_arec( 'SPR-5', 'Unpinned.' ) ] ) ] ) );
	SC::div( 'I3.13', ( $e['refused'] ?? '' ) === 'CALCULATOR FAULT' && $b0 === $b1,
		'a Recorder with no BUILD.json writes no DEPLOYED line and runs no integrity check', DESIGN_ALWAYS, json_encode( $e ) );
	SC::ok( 'I3.14', ( $e['refused'] ?? '' ) === 'CALCULATOR FAULT' && $b0 === $b1,
		'a build in force with no digest function halts (nothing is assumed) [Custos: no pinned digest, no call: CALCULATOR FAULT, nothing written]', json_encode( $e ) );
	SC::div( 'I3.15', true, 'buildFields: the four fields required, each a non-empty string, tree 64 lowercase hex; an extra key is ignored', DESIGN_TREE );

	// I4 the deployed tree's digest.
	SC::div( 'I4.1', true, 'BUILD.json beside the files does not enter the tree digest', DESIGN_TREE );
	$sh = trim( (string)shell_exec( 'sha256sum ' . escapeshellarg( sc_built() ) . ' 2>/dev/null | cut -c1-64' ) );
	SC::div( 'I4.2', $sh === '' || $sh === \Custos\Calculator::digestOf( sc_built() ),
		'the PHP digest equals the host\'s shell formula (find | LC_ALL=C sort | xargs sha256sum | sha256sum) [Custos: the binary\'s digest equals sha256sum\'s]', DESIGN_TREE );
	SC::div( 'I4.3', true, 'readBuild reads BUILD.json\'s four fields', DESIGN_TREE );
	SC::div( 'I4.4', true, 'a malformed BUILD.json throws; no BUILD.json reads as null', DESIGN_TREE );
	SC::div( 'I4.5', true, 'the extension\'s own tree digests', DESIGN_TREE );

	// I5 the VERIFICATION row's WHAT text.
	SC::div( 'I5.1', true, 'the register view\'s WHAT for a VERIFICATION names the TARGET, the SOURCE, the external value and zeta', CORNER_VERIFICATION );
	SC::div( 'I5.2', true, '... and the rendered register text shows it', CORNER_VIEWS );

	// I6 the request's rules: the prefix, the op table, the fault's words.
	$ops = $u->ops;
	$e = ic_ops( static fn () => $ops->run( 'PETITION', null, 'Agent A', [ 'block' => 'B1' ] ) );
	$e2 = ic_ops( static fn () => $ops->run( 'PETITION', '', 'Agent A', [ 'block' => 'B1' ] ) );
	SC::ok( 'I6.1', $e !== null && $e->what === 'custos-prefix' && $e2 !== null && str_contains( $e2->getMessage(), 'needs a prefix' ),
		'a missing prefix is a problem stated in words [Custos: custos-prefix, "needs a prefix"]', $e ? $e->getMessage() : 'not refused' );
	$bad = [];
	foreach ( [ 'SP-R', '1SPR', 'SPR R', str_repeat( 'S', 65 ), '../x' ] as $x ) {
		$r = ic_ops( static fn () => $ops->run( 'PETITION', $x, 'Agent A', [ 'block' => 'B1' ] ) );
		if ( $r === null || $r->what !== 'custos-prefix' ) {
			$bad[] = $x;
		}
	}
	SC::div( 'I6.2', $bad === [ str_repeat( 'S', 65 ) ], 'a malformed prefix is a problem', CORNER_PREFIX_LONG, 'not refused custos-prefix: ' . json_encode( $bad ) );
	SC::div( 'I6.3', \Custos\PageTitles::isBuildablePrefix( 'SPR' ) && !\Custos\PageTitles::isBuildablePrefix( '_a9' ), 'an identifier passes (SPR, _a9)', CORNER_PREFIX_EDGE );
	SC::div( 'I6.4', \Custos\Ops::OPS === [ 'PETITION', 'POLL', 'PUSH', 'RELEASE', 'HEARTBEAT', 'STATUS', 'INQUIRE', 'STRUCTURE_TEST' ],
		'every op that takes a prefix is listed (STATUS among them)', CORNER_OPS );
	$t = ic_ops( static fn () => $ops->run( 'TPCRUN', 'SPR', 'Agent A', [ 'fn' => 'record_digest' ] ) );
	SC::div( 'I6.5', !in_array( 'TPCRUN', \Custos\Ops::OPS, true ) && $t !== null, 'TPCRUN\'s function table is tpc_record\'s', CORNER_TPCRUN, $t ? $t->what : 'not refused' );
	SC::div( 'I6.6', $t !== null && $t->what === 'custos-op', 'an unknown function is refused by name with the known list', CORNER_TPCRUN, $t ? $t->what : 'not refused' );
	$msg = 'TypeError: foo() in /home/x/public_html/extensions/Custos/includes/Landing.php on line 1234; also C:\\www\\x.php at line 7';
	$ans = json_encode( \Custos\Refusal::detail( new \RuntimeException( $msg ) ) );
	SC::div( 'I6.7', !str_contains( $ans, '/home' ) && !str_contains( $ans, 'public_html' ) && !str_contains( $ans, 'line 1234' ) && !str_contains( $ans, 'TypeError: foo()' ),
		'scrub removes every path and line reference and keeps the error\'s words', DESIGN_SCRUB, $ans );
	$ans = json_encode( \Custos\Refusal::detail( new \RuntimeException( str_repeat( 'x ', 400 ) ) ) );
	SC::div( 'I6.8', mb_strlen( $ans ) <= 300, 'scrub bounds the message at 300 characters', DESIGN_SCRUB, $ans );

	// I7 the TEST LEASE: SPB under a 120 s lease, SPR under the configured one.
	$r = sc_uwc( 'ic-I7-SPR', 'SPR', false );
	$s = sc_uwc( 'ic-I7-SPB', 'SPB', false );
	sc_reland( $s, null, 120 );
	SC::div( 'I7.1', true, 'the lease is read for SPB alone; a non-numeric or zero lease is ignored', CORNER_TESTLEASE );
	SC::div( 'I7.2', true, 'STATUS shows the lease on SPB and none on SPR', CORNER_STATUS );
	sc_op( $r, 'PETITION', 'Agent A', [ 'block' => 'B1' ] );
	$lkR = sc_lock( $r );
	$span = static fn ( array $lk ): int => (int)strtotime( (string)$lk['expires_at'] ) - (int)strtotime( (string)$lk['granted_at'] );
	SC::div( 'I7.3', $span( $lkR ) === Landing::LEASE, 'SPR\'s first expiry is the NO-PROGRESS LIMIT, 6 h, as before', CORNER_LEASE, json_encode( $lkR ) );
	$lockR = $r->store->get( sc_titles()->lock( $r->px ) );
	sc_op( $s, 'PETITION', 'Agent B', [ 'block' => 'B1' ] );
	$lkB = sc_lock( $s );
	SC::ok( 'I7.4', $span( $lkB ) === 120, 'SPB\'s first expiry is the lease, 120 s', json_encode( $lkB ) );
	$s->now += 40;
	$pp = sc_op( $s, 'PUSH', 'Agent B', [ 'records' => json_encode( [ sc_arec( 'SPB-1', 'Under the lease.' ) ] ) ] );
	$s->now += 20;
	$h = sc_op( $s, 'HEARTBEAT', 'Agent B', [] );
	$lkB2 = sc_lock( $s );
	SC::div( 'I7.5', sc_ids( $pp ) === [ 'SPB-1' ] && isset( $h['heartbeat'] ) && strcmp( (string)$lkB2['expires_at'], (string)$lkB['expires_at'] ) > 0,
		'a heartbeat after a push extends SPB\'s expiry in 30 s steps (a quarter of the lease)', CORNER_LEASE, json_encode( [ $pp, $h, $lkB2 ] ) );
	$s->now += 100;
	$h = sc_op( $s, 'HEARTBEAT', 'Agent B', [] );
	SC::div( 'I7.6', isset( $h['heartbeat'] ), 'more than 120 s after the push, before the expiry, a heartbeat on SPB is refused: past the lease', CORNER_LEASE, json_encode( $h ) );
	$s->now = (int)strtotime( (string)sc_lock( $s )['expires_at'] ) + 1;
	$h = sc_op( $s, 'HEARTBEAT', 'Agent B', [] );
	SC::ok( 'I7.7', ( $h['refused'] ?? '' ) === 'NOT HOLDER', '... and past the expiry the lock is free [Custos: NOT HOLDER past the expiry its last heartbeat set]', json_encode( $h ) );
	SC::ok( 'I7.8', $r->store->get( sc_titles()->lock( $r->px ) ) === $lockR && ( sc_lock( $r )['holder'] ?? '' ) === 'Agent A',
		'SPR\'s lock is untouched by SPB\'s lease [Custos: held, its lease the configured span]' );
}

// ================================ b1-repro ====================================================

const CORNER_REPRO = 'corner: the named reproduction is not built (a PUSH of kind REPRODUCTION with its derivation, the CORROBORATION record, the reproduction log, NON-CORROBORATION with its PENDING pairs, INDEPENDENCE, SAME-MODEL and SAME-SPONSOR): GA1 refuses the parameters kind, derivation and capability (custos-unknown-param), and CORROBORATION is not a class Custos lands (RECORD CHECK, LANDS); nothing is written';

/** Version 1's accounts of the reproduction gate, as the scenarios name them. */
const RP_ACC = [ 'DeltaS Zero' => 'Agent A', 'CH7 AZ' => 'Agent B', 'Phoenix 480' => 'Agent C', 'Prime AI' => 'Agent D', 'Nobody' => 'Agent E' ];

function rp_mrec( string $id, string $value, string $uc, array $asm, string $unit = 'm', bool $at = true ): array {
	$r = [ 'ID' => $id, 'CLASS' => 'RESULT', 'CITES' => [], 'ASSUMPTIONS' => $asm, 'STATEMENT' => "Measured E_x: $value $unit.", 'REGIME' => 'M',
		'DERIVATION' => [ 'STEPS' => 1, 'TEXT' => 'Read from the bench gauge.' ],
		'FALSIFIER' => 'A repeat reading outside the stated uncertainty.', 'FALSIFIER_CLASS' => 'F3',
		'QUANTITY' => 'E_x', 'VALUE' => $value, 'UNIT' => $unit, 'U_C' => $uc,
		'BUDGET' => [ [ 'NAME' => 'gauge', 'U' => $uc, 'UNIT' => $unit, 'EVALUATION' => 'B', 'BASIS' => 'manufacturer\'s specification' ] ],
		'CORRELATED' => false ];
	if ( $at ) {
		$r['AT'] = [ [ 'DOF' => 't', 'VALUE' => '0', 'UNIT' => 's' ] ];
	}
	return $r;
}

function rp_corr( string $id, string $target, array $asm = [], array $set = [] ): array {
	return array_merge( [ 'ID' => $id, 'CLASS' => 'CORROBORATION', 'TARGET' => $target, 'CITES' => [], 'ASSUMPTIONS' => $asm ], $set );
}

/** Version 1's examples/spring/reproduction.json restated (it lived outside the archive): SPR-3's derivation, no ID. */
function rp_lderiv( string $eq = 'D(v,t) = -k_s/m*x' ): array {
	$d = sc_push1()[1];
	unset( $d['ID'] );
	$d['EQUATION'] = $eq;
	return $d;
}

function rp_vderiv( string $value, string $unit = 'm' ): array {
	return [ 'CLASS' => 'RESULT', 'CITES' => [], 'ASSUMPTIONS' => [ 'SPR-2' ],
		'STATEMENT' => "From SPR-2 the displacement at t = 0 is $value $unit.", 'REGIME' => 'L',
		'DERIVATION' => [ 'STEPS' => 1, 'TEXT' => 'Read x at t = 0 from SPR-2.' ],
		'FALSIFIER' => 'A measured displacement at release different from the value.', 'FALSIFIER_CLASS' => 'F3',
		'QUANTITY' => 'E_x', 'VALUE' => $value, 'UNIT' => $unit, 'AT' => [ [ 'DOF' => 't', 'VALUE' => '0', 'UNIT' => 's' ] ] ];
}

function rp_mderiv( string $value, string $uc, string $unit = 'm', bool $at = true ): array {
	$d = rp_mrec( 'X', $value, $uc, [], $unit, $at );
	unset( $d['ID'] );
	$d['STATEMENT'] = "Remeasured E_x: $value $unit.";
	return $d;
}

/** A fresh spring UWC with push_1 (SPR-2 to SPR-4) landed by DeltaS Zero (Agent A) in block B1. */
function rp_fresh( string $case ): stdClass {
	$u = sc_uwc( "rp-$case" );
	$p = sc_push( $u, sc_push1(), RP_ACC['DeltaS Zero'], 'B1' );
	if ( sc_ids( $p ) !== [ 'SPR-2', 'SPR-3', 'SPR-4' ] ) {
		throw new RuntimeException( "push_1 did not land on rp-$case: " . json_encode( $p ) );
	}
	return $u;
}

/**
 * Version 1's rpush as Custos meets it: the lock granted to $account (gpush's fixture), then the PUSH of
 * $records; a push of another kind than WORK carries kind, a derivation carries derivation, a CAPABILITY
 * overridden carries capability (version 1's session fields otherwise not sent: CORNER_SESSION).
 */
function rp_push( stdClass $u, array $records, string $who, string $kind = 'WORK', ?array $deriv = null, array $capOver = [], string $block = 'B' ): array {
	$account = RP_ACC[$who];
	$g = sc_grant( $u, $account, $block );
	if ( $g !== null ) {
		return [ 'refused' => 'PETITION', 'petition' => $g ];
	}
	$params = [ 'records' => json_encode( $records, SC_JSON ) ];
	if ( $kind !== 'WORK' ) {
		$params['kind'] = $kind;
	}
	if ( $deriv !== null ) {
		$params['derivation'] = json_encode( $deriv, SC_JSON );
	}
	if ( $capOver !== [] ) {
		$params['capability'] = json_encode( $capOver, SC_JSON );
	}
	return sc_op( $u, 'PUSH', $account, $params );
}

/**
 * A reproduction as Custos meets it: the push with kind and derivation refused by GA1, then its
 * CORROBORATION pushed alone refused RECORD CHECK, the pages unchanged by either. True when both hold.
 */
function rp_repro( stdClass $u, array $corr, string $who, ?array $deriv, string $block ): bool {
	sc_grant( $u, RP_ACC[$who], $block );
	$before = sc_snap( $u );
	$a = rp_push( $u, [ $corr ], $who, 'REPRODUCTION', $deriv, [], $block );
	$b = rp_push( $u, [ $corr ], $who, 'WORK', null, [], $block );
	return ( $a['refused'] ?? '' ) === 'OPS' && ( $a['code'] ?? '' ) === 'custos-unknown-param'
		&& ( $b['refused'] ?? '' ) === 'RECORD CHECK' && sc_snap( $u ) === $before && !isset( sc_by( $u )[$corr['ID']] );
}

/**
 * Version 1's B1 increment 3, the named reproduction (R1 to R7), 104 assertions, numbered by case and
 * order (R5.12); a step the cases rest on is an assertion, as version 1 counted it. Its accounts are
 * RP_ACC's; its sponsors and models are session fields Custos does not take (CORNER_SESSION).
 */
function gate_b1_repro(): void {
	SC::gate( 'b1-repro' );
	$grade = static fn ( stdClass $u, string $id ): string => (string)( sc_by( $u )[$id]['GRADE'] ?? '' );

	// R1 an L MATCH: the first CORROBORATION.
	$u = rp_fresh( 'R1' );
	SC::div( 'R1.1', !array_key_exists( 'MODEL', sc_by( $u )['SPR-3'] ?? [] ), 'the landing of SPR-3 keeps the pusher\'s declared model and vendor; the MASTER none', CORNER_SESSION );
	SC::div( 'R1.2', $grade( $u, 'SPR-3' ) !== 'ESTABLISHED', 'SPR-3 is ESTABLISHED (promoted at its landing)', CORNER_PROMOTION );
	$still = rp_repro( $u, rp_corr( 'SPR-5', 'SPR-3' ), 'CH7 AZ', rp_lderiv(), 'B2' );
	SC::div( 'R1.3', $still, 'step 1: CH7 AZ\'s REPRODUCTION of SPR-3 is answered', CORNER_REPRO );
	foreach ( [ 'the reproduction of SPR-3 is a MATCH; CORROBORATION SPR-5 lands',
		'SPR-5: AUTHOR the reproducer, TARGET SPR-3, MATCH, no DIFFERENCE, PROVISIONAL, UNMARKED, TARGET_STATUS ESTABLISHED',
		'INDEPENDENCE: account, snapshot and vendor as declared, the implementation, REPRODUCTION BLOCK, not served before, not SAME-SPONSOR, not SAME-MODEL',
		'SPR-5\'s DIGEST is the Calculator\'s record_digest and it passes record_check at LANDED',
		'5.3.11: the meta log keeps the derivation, its content hash and the server time stamped before the judgment',
		'the comparison is over the EQUATION\'s canonical spelling (l_finding_pair)' ] as $i => $what ) {
		SC::div( 'R1.' . ( $i + 4 ), $still, $what, CORNER_REPRO );
	}
	SC::div( 'R1.10', $still, 'the BUILD CHAIN push line carries the reproduction', CORNER_CHAIN );
	SC::div( 'R1.11', $still && count( sc_register( $u ) ) === 4, 'next SPR-6; SPR-5\'s landing keeps CH7 AZ\'s model', CORNER_REPRO );
	SC::div( 'R1.12', $still, 'the register view reads it', CORNER_VIEWS );
	SC::div( 'R1.13', $still, 'the answer says the model facts are self-reported in B1 (J5)', CORNER_REPRO );

	// R2 an L NON-CORROBORATION.
	$still = rp_repro( $u, rp_corr( 'SPR-6', 'SPR-4', [ 'SPR-2' ] ), 'CH7 AZ', rp_vderiv( '0.03' ), 'B3' );
	SC::div( 'R2.1', $still, 'step 2: CH7 AZ\'s REPRODUCTION of SPR-4 is answered', CORNER_REPRO );
	SC::div( 'R2.2', $still && count( sc_register( $u ) ) === 4, 'a mismatch lands nothing; SPR-6 is not taken (next SPR-6)', CORNER_REPRO );
	SC::ok( 'R2.3', $still, 'the register page is unchanged' );
	SC::div( 'R2.4', $still, 'NC-1 logged with the difference, PENDING against both parties, no audit under ON REQUEST', CORNER_REPRO );
	SC::div( 'R2.5', $still, 'the push counts; the log names NC-1; the answer carries the pending pair', CORNER_REPRO );
	$q = sc_op( $u, 'RELEASE', RP_ACC['CH7 AZ'], [ 'block' => 'B3' ] );
	SC::ok( 'R2.6', isset( $q['released'] ), 'a release after a NON-CORROBORATION push is valid [Custos: RELEASE asks no push in the grant]', json_encode( $q ) );
	SC::ok( 'R2.7', $grade( $u, 'SPR-4' ) === 'PROVISIONAL' && ( sc_by( $u )['SPR-4']['STATUS'] ?? '' ) === 'UNMARKED',
		'SPR-4 keeps standing under SR2 [Custos: GRADE PROVISIONAL, STATUS UNMARKED]', json_encode( sc_by( $u )['SPR-4'] ?? null ) );

	// R3 SAME-MODEL and SAME-SPONSOR.
	$u = rp_fresh( 'R3' );
	$still = rp_repro( $u, rp_corr( 'SPR-5', 'SPR-3' ), 'Prime AI', rp_lderiv(), 'B2' );
	SC::div( 'R3.1', $still, 'step 3: Prime AI\'s REPRODUCTION of SPR-3 is answered', CORNER_REPRO );
	SC::div( 'R3.2', $still, 'Prime AI on DeltaS Zero\'s model: the corroboration lands marked SAME-MODEL (3.3.10)', CORNER_REPRO );
	SC::div( 'R3.3', $still, 'the view marks SAME-MODEL', CORNER_VIEWS );
	$y = rp_lderiv();
	unset( $y['EQUATION'] );
	$y['STATEMENT'] = 'Blue team: v is constant.';
	$y = [ 'ID' => 'SPR-5' ] + $y;
	$p = rp_push( $u, [ $y ], 'CH7 AZ', 'WORK', null, [], 'B3' );
	SC::ok( 'R3.4', sc_ids( $p ) === [ 'SPR-5' ], 'step 4: a RESULT by CH7 AZ lands [Custos: SPR-5, no CORROBORATION took it]', json_encode( $p ) );
	$z = $y;
	unset( $z['ID'] );
	$still = rp_repro( $u, rp_corr( 'SPR-6', 'SPR-5' ), 'Phoenix 480', $z, 'B4' );
	SC::div( 'R3.5', $still, 'step 5: Phoenix 480\'s REPRODUCTION of CH7 AZ\'s record is answered', CORNER_REPRO );
	SC::div( 'R3.6', $still, 'Phoenix 480 on CH7 AZ\'s record (both PHX_480): the corroboration lands marked SAME-SPONSOR (3.3.8)', CORNER_REPRO );
	SC::div( 'R3.7', $still, 'TARGET_STATUS PROVISIONAL for a target not promoted', CORNER_REPRO );

	// R4 M: MATCH, MATCH WITH DIFFERENCE NOTED, a scaled unit, a mismatch.
	$u = rp_fresh( 'R4' );
	$p = rp_push( $u, [ rp_mrec( 'SPR-5', '0.0200', '0.0002', [] ) ], 'DeltaS Zero', 'WORK', null, [], 'B2' );
	SC::ok( 'R4.1', sc_ids( $p ) === [ 'SPR-5' ], 'step 6: SPR-5, E_x 0.0200 m at t = 0, lands', json_encode( $p ) );
	$still = rp_repro( $u, rp_corr( 'SPR-6', 'SPR-5' ), 'CH7 AZ', rp_mderiv( '0.0201', '0.0002' ), 'B3' );
	SC::div( 'R4.2', $still, 'step 7: CH7 AZ\'s REPRODUCTION of SPR-5 is answered', CORNER_REPRO );
	SC::div( 'R4.3', $still, 'M within SR3 at k: MATCH', CORNER_REPRO );
	SC::div( 'R4.4', $still, 'the M comparison renders both values and u_c in coherent SI', CORNER_REPRO );
	$still = rp_repro( $u, rp_corr( 'SPR-6', 'SPR-5', [], [ 'SELF_REPORTED' => 'bench B, seed 42' ] ), 'Phoenix 480', rp_mderiv( '0.0201', '0.0005' ), 'B4' );
	SC::div( 'R4.5', $still, 'step 8: Phoenix 480\'s REPRODUCTION of SPR-5 is answered', CORNER_REPRO );
	SC::div( 'R4.6', $still, 'the reproducer\'s SELF_REPORTED lands as given, consumed by no rule (3.3.9)', CORNER_REPRO );
	SC::div( 'R4.7', $still, 'u_c 0.0005 against 0.0002 (ratio 2.5): MATCH WITH DIFFERENCE NOTED with its DIFFERENCE', CORNER_REPRO );
	$still = rp_repro( $u, rp_corr( 'SPR-6', 'SPR-5' ), 'Prime AI', rp_mderiv( '20.1', '0.2', 'mm' ), 'B5' );
	SC::div( 'R4.8', $still, 'step 9: Prime AI\'s REPRODUCTION of SPR-5 in mm is answered', CORNER_REPRO );
	SC::div( 'R4.9', $still, '20.1 mm, u 0.2 mm, normalized to coherent SI before the comparison: MATCH', CORNER_REPRO );
	$still = rp_repro( $u, rp_corr( 'SPR-6', 'SPR-5' ), 'CH7 AZ', rp_mderiv( '0.0300', '0.0002' ), 'B6' );
	SC::div( 'R4.10', $still, 'step 10: CH7 AZ\'s second REPRODUCTION of SPR-5 is answered', CORNER_REPRO );
	SC::div( 'R4.11', $still, '0.0300 m against 0.0200 m: NON-CORROBORATION, its finding kept for the dispute rule', CORNER_REPRO );
	SC::div( 'R4.12', $still, 'the NON-CORROBORATION carries both values, both u_c, S and the statistic', CORNER_REPRO );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => rp_push( $u, [ rp_corr( 'SPR-6', 'SPR-5' ) ], 'CH7 AZ', 'REPRODUCTION', rp_mderiv( '0.0201', '0.0002', 'm', false ), [], 'B7' ) );
	SC::refused( 'R4.13', $a, $b0, $b1, 'a derivation without the TARGET\'s AT is refused (CONDITIONS), not called a mismatch' );
	$x = rp_mderiv( '0.0201', '0.0002' );
	$x['QUANTITY'] = 'E_v';
	$x['UNIT'] = 'm s-1';
	$x['BUDGET'][0]['UNIT'] = 'm s-1';
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => rp_push( $u, [ rp_corr( 'SPR-6', 'SPR-5' ) ], 'CH7 AZ', 'REPRODUCTION', $x, [], 'B7' ) );
	SC::refused( 'R4.14', $a, $b0, $b1, 'another QUANTITY is refused (SR3\'s cross-entry rule)' );

	// R4b SR8: the other records of the TARGET's group scale u_c before the test.
	$u = rp_fresh( 'R4b' );
	$p = rp_push( $u, [ rp_mrec( 'SPR-5', '0.0200', '0.0002', [] ), rp_mrec( 'SPR-6', '0.0204', '0.0002', [] ) ], 'DeltaS Zero', 'WORK', null, [], 'B2' );
	SC::ok( 'R4b.1', sc_ids( $p ) === [ 'SPR-5', 'SPR-6' ], 'step 11: two M records of E_x at t = 0, 0.0004 apart, land', json_encode( $p ) );
	SC::ok( 'R4b.2', $grade( $u, 'SPR-5' ) === 'PROVISIONAL' && $grade( $u, 'SPR-6' ) === 'PROVISIONAL',
		'neither struck and no audit block: a pair with no other record is tested raw, 0.0004 inside 2 * 0.000283 [Custos: both PROVISIONAL; it writes no audit block]' );
	$still = rp_repro( $u, rp_corr( 'SPR-7', 'SPR-5' ), 'CH7 AZ', rp_mderiv( '0.0209', '0.0002' ), 'B3' );
	SC::div( 'R4b.3', $still, 'step 12: CH7 AZ\'s REPRODUCTION of SPR-5 is answered', CORNER_REPRO );
	SC::div( 'R4b.4', $still, '0.0209 against 0.0200: SPR-5 left out, one other record (SPR-6), S = 1, statistic 3.18 > k = 2: NON-CORROBORATION', CORNER_REPRO );
	SC::div( 'R4b.5', $still, 'the log names the others the factor was computed over: SPR-6, not the TARGET', CORNER_REPRO );
	sc_grant( $u, RP_ACC['DeltaS Zero'], 'B4' );
	[ $p, $b0, $b1 ] = sc_try( $u, static fn () => rp_push( $u, [ rp_mrec( 'SPR-7', '0.0210', '0.0002', [] ), rp_mrec( 'SPR-8', '0.0210', '0.0002', [] ) ], 'DeltaS Zero', 'WORK', null, [], 'B4' ) );
	if ( isset( $p['landed'] ) ) {
		SC::ok( 'R4b.6', sc_ids( $p ) === [ 'SPR-7', 'SPR-8' ], 'step 12b: two records at 0.0210 land', json_encode( $p ) );
		$four = $grade( $u, 'SPR-5' ) === 'PROVISIONAL' && $grade( $u, 'SPR-6' ) === 'PROVISIONAL' && $grade( $u, 'SPR-7' ) === 'PROVISIONAL' && $grade( $u, 'SPR-8' ) === 'PROVISIONAL';
		SC::ok( 'R4b.7', $four, 'the four stand: each pair is scaled by the two others, no contradiction' );
	} else {
		$owed = sc_strike_owed( $p, $b0, $b1 );
		SC::div( 'R4b.6', $owed, 'step 12b: two records at 0.0210 land', CORNER_CLEARS, json_encode( $p ) );
		SC::div( 'R4b.7', $owed && count( sc_register( $u ) ) === 6, 'the four stand: each pair is scaled by the two others, no contradiction', CORNER_CLEARS );
	}
	$still = rp_repro( $u, rp_corr( 'SPR-9', 'SPR-5' ), 'CH7 AZ', rp_mderiv( '0.0209', '0.0002' ), 'B5' );
	SC::div( 'R4b.8', $still, 'step 12c: CH7 AZ\'s REPRODUCTION of SPR-5 against three others is answered', CORNER_REPRO );
	SC::div( 'R4b.9', $still, 'S = sqrt(3) over the three others, allowance 0.00098 > 0.0009: MATCH, the CORROBORATION SPR-9 lands', CORNER_REPRO );
	SC::div( 'R4b.10', $still, 'the log names the three others', CORNER_REPRO );

	// R5 the refusals: each lands nothing.
	$u = rp_fresh( 'R5' );
	$n0 = count( sc_register( $u ) );
	$l = rp_lderiv();
	$cases = [
		[ 'a CORROBORATION in a WORK push', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'WORK', null, [] ],
		[ 'two records in a REPRODUCTION push', [ rp_corr( 'SPR-5', 'SPR-3' ), sc_arec( 'SPR-6', 'x' ) ], 'CH7 AZ', 'REPRODUCTION', $l, [] ],
		[ 'a REPRODUCTION push of another class', [ sc_arec( 'SPR-5', 'x' ) ], 'CH7 AZ', 'REPRODUCTION', $l, [] ],
		[ 'no derivation', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'REPRODUCTION', null, [] ],
		[ 'a derivation in a WORK push', [ sc_arec( 'SPR-5', 'x' ) ], 'CH7 AZ', 'WORK', $l, [] ],
		[ 'a pushed OUTCOME', [ rp_corr( 'SPR-5', 'SPR-3', [], [ 'OUTCOME' => 'MATCH' ] ) ], 'CH7 AZ', 'REPRODUCTION', $l, [] ],
		[ 'a pushed INDEPENDENCE', [ rp_corr( 'SPR-5', 'SPR-3', [], [ 'INDEPENDENCE' => [ 'ACCOUNT' => 'x' ] ] ) ], 'CH7 AZ', 'REPRODUCTION', $l, [] ],
		[ 'the next identifier', [ rp_corr( 'SPR-6', 'SPR-3' ) ], 'CH7 AZ', 'REPRODUCTION', $l, [] ],
		[ 'a TARGET that is an ASSUMPTION', [ rp_corr( 'SPR-5', 'SPR-2' ) ], 'CH7 AZ', 'REPRODUCTION', $l, [] ],
		[ 'a TARGET not in the register', [ rp_corr( 'SPR-5', 'SPR-40' ) ], 'CH7 AZ', 'REPRODUCTION', $l, [] ],
		[ 'the author\'s own record', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'DeltaS Zero', 'REPRODUCTION', $l, [] ],
		[ 'the derivation\'s ASSUMPTIONS not the CORROBORATION\'s', [ rp_corr( 'SPR-5', 'SPR-4', [ 'SPR-2' ] ) ], 'CH7 AZ', 'REPRODUCTION', array_merge( rp_vderiv( '0.02' ), [ 'ASSUMPTIONS' => [] ] ), [] ],
		[ 'a derivation citing its TARGET', [ rp_corr( 'SPR-5', 'SPR-3', [], [ 'CITES' => [ 'SPR-3' ] ] ) ], 'CH7 AZ', 'REPRODUCTION', array_merge( $l, [ 'CITES' => [ 'SPR-3' ] ] ), [] ],
		[ 'a derivation of another ID', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'REPRODUCTION', array_merge( $l, [ 'ID' => 'SPR-9' ] ), [] ],
		[ 'a derivation that is no object', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'REPRODUCTION', [ $l ], [] ],
		[ 'a derivation of another class', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'REPRODUCTION', sc_arec( 'SPR-5', 'x' ), [] ],
		[ 'a derivation missing FALSIFIER', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'REPRODUCTION', array_diff_key( $l, [ 'FALSIFIER' => 1 ] ), [] ],
		[ 'a derivation carrying SUPERSEDES', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'REPRODUCTION', array_merge( $l, [ 'SUPERSEDES' => 'SPR-3' ] ), [] ],
		[ 'a derivation in the other REGIME', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'REPRODUCTION', rp_mderiv( '0.02', '0.0002' ), [] ],
		[ 'a derivation whose form fails', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'REPRODUCTION', rp_lderiv( 'D(v, t) = -k_s / m * nowhere' ), [] ],
		[ 'a CAPABILITY without MODEL', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'REPRODUCTION', $l, [ 'MODEL' => '' ] ],
		[ 'a CAPABILITY without PRB_DIGEST', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'REPRODUCTION', $l, [ 'PRB_DIGEST' => '' ] ],
		[ 'an account without a sponsor', [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'Nobody', 'REPRODUCTION', $l, [] ],
		[ 'a value in a unit of another dimension', [ rp_corr( 'SPR-5', 'SPR-4', [ 'SPR-2' ] ) ], 'CH7 AZ', 'REPRODUCTION', rp_vderiv( '0.02', 's' ), [] ],
	];
	foreach ( $cases as $i => [ $what, $recs, $who, $kind, $deriv, $cap ] ) {
		// The grant first (gpush's fixture), so the push's refusal is compared with the pages after it.
		sc_grant( $u, RP_ACC[$who], 'B' . ( $i + 2 ) );
		[ $a, $b0, $b1 ] = sc_try( $u, static fn () => rp_push( $u, $recs, $who, $kind, $deriv, $cap, 'B' . ( $i + 2 ) ) );
		SC::refused( 'R5.' . ( $i + 1 ), $a, $b0, $b1, "refused: $what" );
	}
	SC::ok( 'R5.25', count( sc_register( $u ) ) === $n0 && !isset( sc_by( $u )['SPR-5'] ), 'after every refusal: nothing landed, nothing logged, the register\'s count unchanged' );
	sc_grant( $u, RP_ACC['CH7 AZ'], 'B30' );
	$n = (string)$u->nonces->peek( RP_ACC['CH7 AZ'], $u->px );
	$a = rp_push( $u, [ rp_corr( 'SPR-5', 'SPR-3' ) ], 'CH7 AZ', 'WORK', null, [], 'B30' );
	SC::ok( 'R5.26', ( $a['refused'] ?? '' ) === 'RECORD CHECK' && is_string( $a['challenge'] ?? null ) && strlen( $a['challenge'] ) === 32 && $a['challenge'] !== $n,
		'a refusal after the challenge was consumed answers the next nonce [Custos: the RECORD CHECK refusal of a CORROBORATION]', json_encode( $a ) );
	$u = rp_fresh( 'R5b' );
	$p = rp_push( $u, [ array_merge( [ 'ID' => 'SPR-5' ], rp_vderiv( '0.02' ) ) ], 'DeltaS Zero', 'WORK', null, [], 'B9' );
	SC::div( 'R5.27', sc_ids( $p ) === [ 'SPR-5' ], 'SPR-5 lands with no MODEL declared', CORNER_SESSION, json_encode( $p ) );
	sc_grant( $u, RP_ACC['CH7 AZ'], 'B10' );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => rp_push( $u, [ rp_corr( 'SPR-6', 'SPR-5', [ 'SPR-2' ] ) ], 'CH7 AZ', 'REPRODUCTION', rp_vderiv( '0.02' ), [], 'B10' ) );
	SC::refused( 'R5.28', $a, $b0, $b1, 'refused: a TARGET whose landing left no model' );
	$t = sc_titles()->registerVolume( $u->px, 1 );
	$reg = sc_register( $u );
	foreach ( $reg as &$r ) {
		if ( $r['ID'] === 'SPR-4' ) {
			$r['STATUS'] = 'HELD';
		}
	}
	unset( $r );
	$u->store->tamper( $t, PageTexts::register( $u->px, 1, sc_calc()->call( 'canonical', 'canonical_json', json_encode( [ 'value' => $reg ], SC_JSON ) )['value'] ) );
	SC::ok( 'R5.29', ( sc_by( $u )['SPR-4']['STATUS'] ?? '' ) === 'HELD', 'FIXTURE SPR-4 HELD as a hold would mark it' );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => rp_push( $u, [ rp_corr( 'SPR-6', 'SPR-4', [ 'SPR-2' ] ) ], 'CH7 AZ', 'REPRODUCTION', rp_vderiv( '0.02' ), [], 'B11' ) );
	SC::refused( 'R5.30', $a, $b0, $b1, 'refused: a HELD TARGET (its reproduction is RELEASE\'s, B2)' );

	// R6 AUDIT TRIGGER AUTOMATIC: the dispute rule.
	$u = rp_fresh( 'R6' );
	$ok = true;
	foreach ( [ [ 'CH7 AZ', '0.03', 'B2' ], [ 'CH7 AZ', '0.03', 'B3' ], [ 'Phoenix 480', '0.04', 'B4' ], [ 'Prime AI', '0.03', 'B5' ] ] as $i => [ $who, $v, $b ] ) {
		$s = rp_repro( $u, rp_corr( 'SPR-5', 'SPR-4', [ 'SPR-2' ] ), $who, rp_vderiv( $v ), $b );
		SC::div( 'R6.' . ( $i + 1 ), $s, 'step ' . ( 13 + $i ) . ": $who's REPRODUCTION of SPR-4 at $v m is answered", CORNER_REPRO );
		$ok = $ok && $s;
	}
	SC::div( 'R6.5', $ok, 'no audit block for one account twice, or for a disagreeing second account', CORNER_AUDIT );
	SC::div( 'R6.6', $ok, 'Prime AI\'s agreeing, independent NON-CORROBORATION makes two: AUDIT-1 (DISPUTE) opens on SPR-4 with NC-1 and NC-4', CORNER_AUDIT );
	SC::div( 'R6.7', $ok, 'NC-4 names its audit block; the decision item is the Declarer\'s', CORNER_AUDIT );
	$s = rp_repro( $u, rp_corr( 'SPR-5', 'SPR-4', [ 'SPR-2' ] ), 'Phoenix 480', rp_vderiv( '0.03' ), 'B6' );
	SC::div( 'R6.8', $s, 'step 17: Phoenix 480\'s second REPRODUCTION of SPR-4 is answered', CORNER_REPRO );
	SC::div( 'R6.9', $s, 'no second DISPUTE block while one is OPEN on SPR-4', CORNER_AUDIT );
	SC::div( 'R6.10', $s, 'the chain line names NC-5; nothing landed', CORNER_CHAIN );
	$u = rp_fresh( 'R6b' );
	$ok = true;
	foreach ( [ [ 'CH7 AZ', 'B2' ], [ 'Prime AI', 'B3' ] ] as $i => [ $who, $b ] ) {
		$s = rp_repro( $u, rp_corr( 'SPR-5', 'SPR-4', [ 'SPR-2' ] ), $who, rp_vderiv( '0.03' ), $b );
		SC::div( 'R6.' . ( 11 + $i ), $s, "$who reproduces SPR-4 under ON REQUEST", CORNER_REPRO );
		$ok = $ok && $s;
	}
	SC::div( 'R6.13', $ok, 'under ON REQUEST two agreeing non-corroborations open nothing (4.1.6)', CORNER_AUDIT );
	$u = rp_fresh( 'R6c' );
	$p = rp_push( $u, [ rp_mrec( 'SPR-5', '0.0200', '0.0002', [] ) ], 'DeltaS Zero', 'WORK', null, [], 'B2' );
	SC::ok( 'R6.14', sc_ids( $p ) === [ 'SPR-5' ], 'step 18: SPR-5, E_x 0.0200 m, lands', json_encode( $p ) );
	$s1 = rp_repro( $u, rp_corr( 'SPR-6', 'SPR-5' ), 'CH7 AZ', rp_mderiv( '0.0300', '0.0002' ), 'B3' );
	SC::div( 'R6.15', $s1, 'step 19: CH7 AZ\'s REPRODUCTION of SPR-5 at 0.0300 m is answered', CORNER_REPRO );
	$s2 = rp_repro( $u, rp_corr( 'SPR-6', 'SPR-5' ), 'Phoenix 480', rp_mderiv( '0.0301', '0.0002' ), 'B4' );
	SC::div( 'R6.16', $s2, 'step 20: Phoenix 480\'s REPRODUCTION of SPR-5 at 0.0301 m is answered', CORNER_REPRO );
	SC::div( 'R6.17', $s1 && $s2, 'M: 0.0300 and 0.0301 agree with each other at k and both miss 0.0200: a DISPUTE block on SPR-5', CORNER_AUDIT );

	// R7 the whole lock path.
	$u = rp_fresh( 'R7' );
	sc_op( $u, 'RELEASE', RP_ACC['DeltaS Zero'], [ 'block' => 'B1' ] );
	$pt = sc_op( $u, 'PETITION', RP_ACC['CH7 AZ'], [ 'block' => 'B2' ] );
	SC::ok( 'R7.1', isset( $pt['grant'] ), 'step 21: CH7 AZ petitions [Custos: granted at once, the lock free]', json_encode( $pt ) );
	SC::div( 'R7.2', isset( $pt['grant'] ) && is_string( $pt['challenge'] ?? null ), 'step 22: CH7 AZ acquires, the acquiring POLL carrying the challenge', CORNER_QUEUE, json_encode( $pt ) );
	$before = sc_snap( $u );
	$p = sc_op( $u, 'PUSH', RP_ACC['CH7 AZ'], [ 'records' => json_encode( [ rp_corr( 'SPR-5', 'SPR-3' ) ], SC_JSON ), 'kind' => 'REPRODUCTION',
		'derivation' => json_encode( rp_lderiv(), SC_JSON ) ] );
	$still = ( $p['refused'] ?? '' ) === 'OPS' && sc_snap( $u ) === $before;
	SC::div( 'R7.3', $still, 'step 23: CH7 AZ\'s REPRODUCTION under its grant, answering the challenge, is answered', CORNER_REPRO, json_encode( $p ) );
	SC::div( 'R7.4', $still, 'CH7 AZ petitions, acquires, answers the challenge and lands its CORROBORATION (attested EXECUTED)', CORNER_REPRO );
	$rl = sc_op( $u, 'RELEASE', RP_ACC['CH7 AZ'], [ 'block' => 'B2' ] );
	SC::ok( 'R7.5', isset( $rl['released'] ) && array_key_exists( 'holder', sc_lock( $u ) ) && sc_lock( $u )['holder'] === null, 'then releases', json_encode( $rl ) );
	[ $a, $b0, $b1 ] = sc_try( $u, static fn () => sc_op( $u, 'PUSH', RP_ACC['CH7 AZ'], [ 'records' => json_encode( [ rp_corr( 'SPR-6', 'SPR-3' ) ], SC_JSON ), 'block' => 'B3' ] ) );
	SC::refused( 'R7.6', $a, $b0, $b1, 'a reproduction after the release is refused by fencing [Custos: ' . ( $a['refused'] ?? '?' ) . ']' );
}

// ================================ main ========================================================

/** The gates $want, in order; in the wiki run and the plan run a throw stops its gate alone. */
function sc_run( array $want ): void {
	SC::$asked = $want;
	foreach ( $want as $g ) {
		if ( !SCW::on() ) {
			( 'gate_' . str_replace( '-', '_', $g ) )();
			continue;
		}
		try {
			( 'gate_' . str_replace( '-', '_', $g ) )();
		} catch ( Throwable $e ) {
			SC::thrown( $e );
		}
		SCW::reset();
	}
}

/**
 * The wiki run, under maintenance/run.php on the rehearsal wiki (rehearsal.sh): the landing job's
 * configuration as the file-backed run's (the governor off, its D_IS) and each UWC's title root set
 * for its jobs; checked first that the configuration MediaWiki reads follows those settings.
 */
function sc_wiki_main(): int {
	SCW::$wiki = true;
	SCW::$run = 'R' . gmdate( 'YmdHis' ) . getmypid();
	$GLOBALS['wgCustosGovernorOff'] = true;
	$GLOBALS['wgCustosDIs'] = str_repeat( 'd', 64 );
	$GLOBALS['wgCustosTps'] = '0.4.0';
	$GLOBALS['wgCustosPollAfter'] = 30;
	$config = \MediaWiki\MediaWikiServices::getInstance()->getMainConfig();
	$probe = SCW::root( sc_scratch() . '/probe' );
	$GLOBALS['wgCustosUwcRoot'] = $probe;
	if ( $config->get( 'CustosUwcRoot' ) !== $probe || $config->get( 'CustosGovernorOff' ) !== true ) {
		echo "scenarios-wiki: cannot run: the configuration MediaWiki reads does not follow \$GLOBALS (CustosUwcRoot, CustosGovernorOff)\n";
		return 2;
	}
	if ( \Custos\Calculator::digestOf( sc_built() ) !== \Custos\Landing::confFrom( $config )['digest'] ) {
		echo "scenarios-wiki: cannot run: the wiki's \$wgCustosBuild digest is not the built pcalc's\n";
		return 2;
	}
	sc_run( SC_GATES );
	return SC::report( sc_rows(), sc_wiki_rows() );
}

if ( defined( 'RUN_MAINTENANCE_IF_MAIN' ) ) {
	if ( !class_exists( 'CustosScenarios', false ) ) {
		/** The maintenance script maintenance/run.php runs: the wiki run. */
		final class CustosScenarios extends \MediaWiki\Maintenance\Maintenance {
			public function __construct() {
				parent::__construct();
				$this->addDescription( 'Version 1\'s landing gates replayed as Custos scenarios over this wiki\'s stores and job runner' );
			}

			public function execute() {
				if ( !is_file( sc_built() ) || !is_executable( sc_built() ) ) {
					echo "scenarios-wiki: skipped: no built pcalc in this clone (.lake/build/bin/pcalc)\n";
					exit( 0 );
				}
				exit( sc_wiki_main() );
			}
		}
	}
	return CustosScenarios::class;
}

/**
 * The tracing's own checks over the plan run's UWCs, no wiki (the built pcalc writes the held locks of S5 and S7): S1 a ticket the job
 * runner leaves unanswered, or a land job it fails, is a FAIL and never a refusal; S2 a FAIL is never
 * relabelled, before or after its case is traced, and only an assertion made after the cause may be
 * WIKI-DIV; S3 an assertion on a clean UWC made right after one on a traced UWC, in the same case, is
 * counted as it came out; S4 a wiki run's nonce set and take go through the table; S5 a wiki run's
 * clock step moves back its UWC's stored times alone and traces no cause. Prints each check and "scenarios-self-test: ALL PASS <p>/<n>" (or FAIL).
 */
function sc_self_test(): int {
	SCW::$plan = true;
	$dir = sc_scratch() . '/self-test';
	$uwc = static function ( string $tag ) use ( $dir ): ScUwc {
		$u = new ScUwc( [ 'dir' => "$dir/$tag", 'px' => 'SPR', 'now' => SCW::START ] );
		@mkdir( "$dir/$tag", 0777, true );
		$u->init( [ 'store' => new ScStore( new \Custos\Tests\FileStore( "$dir/$tag/pages" ) ), 'nonces' => new ScNonces( new \Custos\Tests\FileNonceStore( "$dir/$tag/nonces.json" ) ) ] );
		return $u;
	};
	$shown = static fn ( string $g ): array => array_column( array_map( static fn ( array $r ): array => [ $r[1], SC::shown( $r[2], $r[5] ) ],
		array_values( array_filter( SC::$rec, static fn ( array $r ): bool => $r[0] === $g ) ) ), 1, 0 );
	$checks = [];

	// S1: an unanswered ticket, then an answered ticket whose land job failed (JOB CONTEXT answers and fails the job).
	SC::gate( 'self-1' );
	$a = SCW::answer( 7, [ 'id' => 7, 'account' => 'Agent A', 'prefix' => 'SPR', 'answer' => null ], [ 'jobs' => [] ] );
	SC::refused( 'S1.1', $a, [], [], 'an unanswered ticket is not Custos refusing' );
	$b = SCW::answer( 8, [ 'id' => 8, 'account' => 'Agent A', 'prefix' => 'SPR', 'answer' => json_encode( [ 'refused' => 'JOB CONTEXT', 'detail' => 'x' ] ) ],
		[ 'jobs' => [ [ 'type' => 'custosLand', 'status' => 'failed', 'error' => 'thrown inside LandJob' ] ] ] );
	SC::refused( 'S1.2', $b, [], [], 'a failed land job is not Custos refusing' );
	$c = SCW::answer( 9, [ 'id' => 9, 'account' => 'Agent A', 'prefix' => 'SPR', 'answer' => json_encode( [ 'refused' => 'LOCK HELD' ] ) ],
		[ 'jobs' => [ [ 'type' => 'custosLand', 'status' => 'ok', 'error' => null ] ] ] );
	$checks['S1 a ticket the job runner leaves unanswered, or a land job it fails, is a FAIL, never a refusal'] =
		$shown( 'self-1' ) === [ 'NOT-RUN.t7' => 'FAIL', 'S1.1' => 'FAIL', 'NOT-RUN.t8' => 'FAIL', 'S1.2' => 'FAIL' ]
		&& !isset( $a['refused'] ) && !isset( $b['refused'] ) && $c === [ 'refused' => 'LOCK HELD' ];

	// S2: a FAIL before its case is traced (by a read of the nonce store), a PASS after it, a FAIL after the clock is stepped (no cause).
	SC::gate( 'self-2' );
	$t = $uwc( 'S2' );
	SC::ok( 'S2.1', $t->px === 'x', 'a FAIL before the case is traced' );
	$t->nonces->peek( 'Agent A', $t->px );
	SC::ok( 'S2.2', $t->px === 'SPR', 'a PASS after the nonce store is read' );
	$t->now = SCW::START + 3600;
	SC::ok( 'S2.3', $t->px === 'x', 'a FAIL after the clock is stepped' );
	SC::defect( 'S2.4', $t->px . ' landed', 'a DEFECT after the clock is stepped' );
	SC::tally();
	$checks['S2 a FAIL or a DEFECT is never relabelled; only an assertion made after its cause is WIKI-DIV'] =
		$shown( 'self-2' ) === [ 'S2.1' => 'FAIL', 'S2.2' => 'WIKI-DIV', 'S2.3' => 'FAIL', 'S2.4' => 'DEFECT' ]
		&& SC::$n['self-2'] === [ 'pass' => 0, 'div' => 0, 'defect' => 1, 'fail' => 2, 'wiki' => 1 ];

	// S3: a traced UWC's assertion, then a clean UWC's in the same case, then one reading no UWC (it stands on the clean one).
	SC::gate( 'self-3' );
	$tr = $uwc( 'S3t' );
	$cl = $uwc( 'S3c' );
	$tr->taint( SCW::LANDING );
	SC::ok( 'S3.1', $tr->px === 'SPR', 'a PASS on the traced UWC' );
	SC::ok( 'S3.2', $cl->store->get( 'Nothing' ) === null, 'a PASS on the clean UWC right after' );
	SC::ok( 'S3.3', $cl->px === 'x', 'a FAIL on the clean UWC' );
	SC::div( 'S3.4', true, 'a DIVERGENT reading no UWC after the clean one', 'self-test' );
	SC::tally();
	$checks['S3 an assertion on a clean UWC after one on a traced UWC is counted as it came out'] =
		$shown( 'self-3' ) === [ 'S3.1' => 'WIKI-DIV', 'S3.2' => 'PASS', 'S3.3' => 'FAIL', 'S3.4' => 'DIVERGENT' ]
		&& SC::$n['self-3'] === [ 'pass' => 1, 'div' => 1, 'defect' => 0, 'fail' => 1, 'wiki' => 1 ];

	// S4: a wiki run's UWC (no file store, the wiki's table stood in for by MemNonceStore): a landing job the
	// scenario rebuilt sets and takes its nonce through the table, the UWC taints with the nonce cause, nothing thrown.
	SC::gate( 'self-4' );
	$w = new ScUwc( [ 'dir' => "$dir/S4", 'px' => 'SPR', 'now' => SCW::START ] );
	$table = new \Custos\MemNonceStore();
	$w->init( [ 'store' => new ScStore( new \Custos\Tests\FileStore( "$dir/S4/pages" ) ), 'nonces' => new ScNonces( null, $table ) ] );
	$nonce = str_repeat( 'ab', 16 );
	$thrown = null;
	$taken = null;
	try {
		$w->nonces->put( 'Agent A', 'SPR', $nonce, SCW::START );
		$tainted = $w->taint;
		$known = $w->nonces->known( 'Agent A', 'SPR' );
		$taken = $w->nonces->take( 'Agent A', 'SPR' );
	} catch ( \Throwable $e ) {
		$thrown = $e::class;
	}
	SC::ok( 'S4.1', $w->px === 'SPR', 'a PASS on the UWC after its nonce was set' );
	SC::tally();
	$checks['S4 a wiki run\'s nonce set and take go through the table, taint the UWC with the nonce cause and throw nothing'] =
		$thrown === null && ( $tainted ?? null ) === SCW::NONCE && ( $known ?? null ) === $nonce && $taken === $nonce
		&& $w->nonces->known( 'Agent A', 'SPR' ) === null && $table->take( 'Agent A', 'SPR' ) === null
		&& $shown( 'self-4' ) === [ 'S4.1' => 'WIKI-DIV' ];

	// S5: a wiki run's clock step: two UWCs side by side, their pages in files and the wiki's tables stood in for
	// by SQLite tables made from sql/sqlite/; a step of the first moves back its lock's stamps and its rows of
	// custos_ticket, custos_nonce and custos_seat by the step, nothing of the second, and traces no cause.
	SCW::reset();
	SC::gate( 'self-5' );
	$pdo = new PDO( 'sqlite::memory:' );
	$pdo->setAttribute( PDO::ATTR_ERRMODE, PDO::ERRMODE_EXCEPTION );
	foreach ( [ 'custos_ticket', 'custos_nonce', 'custos_seat' ] as $tb ) {
		$pdo->exec( str_replace( '/*_*/', '', (string)file_get_contents( dirname( __DIR__ ) . "/sql/sqlite/$tb.sql" ) ) );
	}
	$g0 = '2026-10-05T00:00:00Z';
	$e0 = '2026-10-05T01:00:00Z';
	$ts0 = '20261005000000';
	$side = [];
	foreach ( [ 'A' => 'Agent A', 'B' => 'Agent B' ] as $k => $acct ) {
		$v = new ScUwc( [ 'dir' => "$dir/S5$k", 'px' => 'SPR', 'now' => SCW::START, 'root' => "Principia Machina/Scenarios/S5/$k" ] );
		@mkdir( "$dir/S5$k", 0777, true );
		$land = new ScWikiLanding( $v, ScWikiLanding::pdo( $pdo ) );
		$v->init( [ 'store' => new ScStore( new \Custos\Tests\FileStore( "$dir/S5$k/pages" ) ), 'landing' => $land, 'wiki' => $land ] );
		$v->store->put( SCW::titles( $v->root() )->lock( 'SPR' ), PageTexts::lock( 'SPR', $acct, $g0, $e0, 'B1', sc_canon() ), 'seed' );
		$pdo->prepare( 'INSERT INTO custos_ticket (ct_op, ct_account, ct_prefix, ct_request, ct_state, ct_answer, ct_created, ct_done) VALUES (?, ?, ?, ?, ?, ?, ?, ?)' )
			->execute( [ 'PUSH', $acct, 'SPR', '{}', 'DONE', '{}', $ts0, $ts0 ] );
		$land->saw( (int)$pdo->lastInsertId(), $acct );
		$pdo->prepare( 'INSERT INTO custos_ticket (ct_op, ct_account, ct_prefix, ct_request, ct_state, ct_answer, ct_created, ct_done) VALUES (?, ?, ?, ?, ?, ?, ?, NULL)' )
			->execute( [ 'PETITION', $acct, 'SPR', '{}', 'QUEUED', null, $ts0 ] );
		$land->saw( (int)$pdo->lastInsertId(), $acct );
		$pdo->prepare( 'INSERT INTO custos_nonce (cn_account, cn_prefix, cn_nonce, cn_issued) VALUES (?, ?, ?, ?)' )->execute( [ $acct, 'SPR', str_repeat( 'ab', 16 ), SCW::START ] );
		$pdo->prepare( 'INSERT INTO custos_seat (cs_account, cs_kind, cs_level, cs_since) VALUES (?, ?, ?, ?)' )->execute( [ $acct, 'agent', 3, SCW::START ] );
		$side[$k] = $v;
	}
	$read = static function ( ScUwc $v, string $acct ) use ( $pdo ): array {
		$lk = (array)json_decode( (string)PageTexts::readLock( (string)$v->store->get( SCW::titles( $v->root() )->lock( 'SPR' ) ) ), true );
		$q = static fn ( string $sql ): array => array_map( 'array_values', $pdo->query( $sql )->fetchAll( PDO::FETCH_ASSOC ) );
		$a = $pdo->quote( $acct );
		return [ 'lock' => [ $lk['holder'] ?? null, $lk['granted_at'] ?? null, $lk['expires_at'] ?? null, $lk['block'] ?? null ],
			'tickets' => $q( "SELECT ct_created, ct_done FROM custos_ticket WHERE ct_account = $a ORDER BY ct_id" ),
			'nonce' => $q( "SELECT cn_nonce, cn_issued FROM custos_nonce WHERE cn_account = $a" ),
			'seat' => $q( "SELECT cs_level, cs_since FROM custos_seat WHERE cs_account = $a" ) ];
	};
	$beforeB = $read( $side['B'], 'Agent B' );
	$thrown = null;
	try {
		$side['A']->now += Landing::LEASE + 1;
	} catch ( \Throwable $e ) {
		$thrown = $e::class . ': ' . $e->getMessage();
	}
	SC::ok( 'S5.1', $side['A']->px === 'SPR', 'a PASS on the UWC after its clock was stepped' );
	SC::tally();
	$st = Landing::LEASE + 1;
	$movedA = [ 'lock' => [ 'Agent A', gmdate( 'Y-m-d\TH:i:s\Z', (int)strtotime( $g0 ) - $st ), gmdate( 'Y-m-d\TH:i:s\Z', (int)strtotime( $e0 ) - $st ), 'B1' ],
		'tickets' => [ [ gmdate( 'YmdHis', SCW::START - $st ), gmdate( 'YmdHis', SCW::START - $st ) ], [ gmdate( 'YmdHis', SCW::START - $st ), null ] ],
		'nonce' => [ [ str_repeat( 'ab', 16 ), SCW::START - $st ] ], 'seat' => [ [ 3, SCW::START - $st ] ] ];
	$afterA = $read( $side['A'], 'Agent A' );
	// a landing job the scenario rebuilt reads the scenario's clock: a step under it moves nothing
	$side['B']->landing = 'rebuilt';
	$side['B']->now += Landing::LEASE + 1;
	$checks['S5 a wiki run\'s clock step moves back exactly its UWC\'s lock stamps and its rows of custos_ticket, custos_nonce and custos_seat, nothing of a second UWC, and traces no cause'] =
		$thrown === null && $afterA === $movedA && $read( $side['B'], 'Agent B' ) === $beforeB
		&& $side['A']->taint === null && $side['A']->clock() === SCW::START + $st && $shown( 'self-5' ) === [ 'S5.1' => 'PASS' ];
	if ( $thrown !== null || $afterA !== $movedA ) {
		fwrite( STDERR, 'S5: ' . ( $thrown ?? json_encode( [ 'after' => $afterA, 'want' => $movedA ] ) ) . "\n" );
	}

	// S7: the shift's edges, over its own SQLite tables and a recording statement runner: no step changes nothing and
	// runs no statement; a negative step is refused; a free lock, a missing lock page and a UWC with no tickets write
	// nothing to the lock and run no statement; a nonce row issued before the step and a seat row with no time
	// (cs_since 0) or one before the step are left as they are, while the rows at or after the step move back.
	$pdo7 = new PDO( 'sqlite::memory:' );
	$pdo7->setAttribute( PDO::ATTR_ERRMODE, PDO::ERRMODE_EXCEPTION );
	foreach ( [ 'custos_ticket', 'custos_nonce', 'custos_seat' ] as $tb ) {
		$pdo7->exec( str_replace( '/*_*/', '', (string)file_get_contents( dirname( __DIR__ ) . "/sql/sqlite/$tb.sql" ) ) );
	}
	$ran = 0;
	$run7 = ScWikiLanding::pdo( $pdo7 );
	$count7 = static function ( string $sql, array $params ) use ( $run7, &$ran ): int {
		$ran++;
		return $run7( $sql, $params );
	};
	$mk7 = static function ( string $tag, ?string $lockText ) use ( $dir, $count7 ): array {
		$v = new ScUwc( [ 'dir' => "$dir/S7$tag", 'px' => 'SPR', 'now' => SCW::START, 'root' => "Principia Machina/Scenarios/S7/$tag" ] );
		@mkdir( "$dir/S7$tag", 0777, true );
		$land = new ScWikiLanding( $v, $count7 );
		$v->init( [ 'store' => new ScStore( new \Custos\Tests\FileStore( "$dir/S7$tag/pages" ) ), 'landing' => $land, 'wiki' => $land ] );
		if ( $lockText !== null ) {
			$v->store->put( SCW::titles( $v->root() )->lock( 'SPR' ), $lockText, 'seed' );
		}
		return [ $v, $land ];
	};
	$lockOf = static fn ( ScUwc $v ): ?string => $v->store->get( SCW::titles( $v->root() )->lock( 'SPR' ) );
	$held7 = PageTexts::lock( 'SPR', 'Agent A', '2026-10-05T00:00:00Z', '2026-10-05T01:00:00Z', 'B1', sc_canon() );
	[ $z, $zl ] = $mk7( 'zero', $held7 );
	$zl->saw( 1, 'Agent A' );
	$zl->shift( 0 );
	$zeroOk = $ran === 0 && $lockOf( $z ) === $held7;
	$negOk = false;
	try {
		$zl->shift( -5 );
	} catch ( LogicException $e ) {
		$negOk = str_contains( $e->getMessage(), 'forward only' ) && $lockOf( $z ) === $held7;
	}
	$free7 = PageTexts::lock( 'SPR', null, null, null, null );
	[ $f, $fl ] = $mk7( 'free', $free7 );
	$fl->shift( 60 );
	[ $m, $ml ] = $mk7( 'none', null );
	$ml->shift( 60 );
	$quietOk = $ran === 0 && $lockOf( $f ) === $free7 && $lockOf( $m ) === null;
	$pdo7->exec( "INSERT INTO custos_nonce (cn_account, cn_prefix, cn_nonce, cn_issued) VALUES ('Agent A', 'SPR', 'n1', 1000), ('Agent A', 'XYZ', 'n2', 1000), ('Agent B', 'SPR', 'n3', 30)" );
	$pdo7->exec( "INSERT INTO custos_seat (cs_account, cs_kind, cs_level, cs_since) VALUES ('Agent A', 'agent', 1, 0), ('Agent B', 'agent', 1, 30), ('Agent C', 'agent', 1, 1000)" );
	[ $g, $gl ] = $mk7( 'guards', $free7 );
	$gl->saw( 1, 'Agent A' );
	$gl->saw( 2, 'Agent B' );
	$gl->saw( 3, 'Agent C' );
	$gl->shift( 60 );
	$rows7 = static fn ( string $sql ): array => array_map( 'array_values', $pdo7->query( $sql )->fetchAll( PDO::FETCH_ASSOC ) );
	$guardOk = $rows7( "SELECT cn_account, cn_prefix, cn_issued FROM custos_nonce ORDER BY cn_account, cn_prefix" ) === [ [ 'Agent A', 'SPR', 940 ], [ 'Agent A', 'XYZ', 1000 ], [ 'Agent B', 'SPR', 30 ] ]
		&& $rows7( "SELECT cs_account, cs_since FROM custos_seat ORDER BY cs_account" ) === [ [ 'Agent A', 0 ], [ 'Agent B', 30 ], [ 'Agent C', 940 ] ];
	$checks['S7 the clock\'s shift: no step changes nothing; a negative step is refused; a free or missing lock and no tickets run nothing; a row before the step or with no time stays'] =
		$zeroOk && $negOk && $quietOk && $guardOk;
	if ( !( $zeroOk && $negOk && $quietOk && $guardOk ) ) {
		fwrite( STDERR, 'S7: ' . json_encode( [ 'zero' => $zeroOk, 'negative' => $negOk, 'quiet' => $quietOk, 'guards' => $guardOk, 'ran' => $ran,
			'nonce' => $rows7( 'SELECT cn_prefix, cn_issued FROM custos_nonce' ), 'seat' => $rows7( 'SELECT cs_account, cs_since FROM custos_seat' ) ] ) . "\n" );
	}

	// S6: a gate whose count of assertions differs from the recorded one is named, either way; a gate not recorded is not.
	$cnt = static fn ( int $pass, int $div, int $wiki = 0 ): array => [ 'pass' => $pass, 'div' => $div, 'defect' => 0, 'fail' => 0, 'wiki' => $wiki ];
	$checks['S6 a gate whose count of assertions differs from SC_COUNTS fails the report, short or long, or asked and never registered; an unrecorded gate is not checked'] =
		SC::countsOff( [ 'a1' => $cnt( 10, 15, 5 ), 'self-1' => $cnt( 1, 0 ) ] ) === []
		&& SC::countsOff( [ 'a1' => $cnt( 10, 15, 4 ) ] ) === [ 'a1 29 of 30' ]
		&& SC::countsOff( [ 'b1-repro' => $cnt( 3, 102 ) ] ) === [ 'b1-repro 105 of 104' ]
		&& SC::countsOff( [ 'a1' => $cnt( 10, 15, 5 ) ], SC_COUNTS, [ 'a1', 'b1' ] ) === [ 'b1 0 of 69' ]
		&& array_sum( SC_COUNTS ) === 471 && array_keys( SC_COUNTS ) === SC_GATES;

	$p = 0;
	foreach ( $checks as $what => $ok ) {
		echo $ok ? 'PASS' : 'FAIL', "      self-test $what\n";
		$p += $ok ? 1 : 0;
	}
	$n = count( $checks );
	echo 'scenarios-self-test: ', $p === $n ? 'ALL PASS' : 'FAIL', " $p/$n\n";
	return $p === $n ? 0 : 1;
}

if ( realpath( $_SERVER['SCRIPT_FILENAME'] ?? '' ) === realpath( __FILE__ ) ) {
	if ( ( $argv[1] ?? '' ) === '--self-test' ) {
		exit( sc_self_test() );
	}
	if ( !is_file( sc_built() ) || !is_executable( sc_built() ) ) {
		echo "scenarios: skipped: no built pcalc in this clone (.lake/build/bin/pcalc)\n";
		exit( 0 );
	}
	$want = array_slice( $argv, 1 );
	if ( ( $want[0] ?? '' ) === '--wiki-plan' ) {
		// the wiki run's causes traced over the file-backed stores: its counts and its wiki-only rows
		SCW::$plan = true;
		array_shift( $want );
	}
	$want = $want ?: SC_GATES;
	foreach ( $want as $g ) {
		if ( !in_array( $g, SC_GATES, true ) ) {
			fwrite( STDERR, "scenarios: not a gate: $g\n" );
			exit( 2 );
		}
	}
	sc_run( $want );
	exit( SC::report( sc_rows(), sc_wiki_rows() ) );
}
