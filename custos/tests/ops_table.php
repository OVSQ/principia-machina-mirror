<?php
/**
 * ops_table.php: the tests of the op table and the job's dispatch, their own file.
 *
 *   php custos/tests/ops_table.php
 *
 * The shape table of Ops (every op in it once, PARAMS and REQUIRED read from it, the prefix flag), the
 * dispatch of Ops::run (an unknown op word refused as before, a read op refusing a prefix, a write op
 * writing its ticket), the job's handler table (one handler per write op) and the one mapping from a
 * ticket to the governor's request (its kind, records and result rows), and PageWriter::commitOne (one
 * page saved with the summary of a landing; refused without exactly one page, with the badge, on a moved
 * base). Prints one line per case and "ops_table: ALL PASS <n>/<n>". Command line only; it touches no
 * wiki and needs no pcalc.
 */

declare( strict_types=1 );

require_once __DIR__ . '/bootstrap.php';

use Custos\Landing;
use Custos\Ops;
use Custos\PageFault;
use Custos\PageTexts;
use Custos\PageTitles;
use Custos\PageWriter;
use Custos\Refusal;
use Custos\Tests\FileStore;
use Custos\Tests\FileTicketStore;

$scratch = sys_get_temp_dir() . '/custos-ops-table-' . getmypid();
@mkdir( $scratch, 0700, true );
register_shutdown_function( static function () use ( $scratch ): void {
	$clear = static function ( string $p ) use ( &$clear ): void {
		foreach ( scandir( $p ) ?: [] as $e ) {
			if ( $e === '.' || $e === '..' ) {
				continue;
			}
			is_dir( "$p/$e" ) ? $clear( "$p/$e" ) : @unlink( "$p/$e" );
		}
		@rmdir( $p );
	};
	$clear( $scratch );
} );

/** The refusal's code, or "none". */
function t_code( callable $fn ): string {
	try {
		$fn();
	} catch ( Refusal $e ) {
		return $e->what;
	}
	return 'none';
}

// ---- the shape table --------------------------------------------------------------------------

$words = array_keys( Ops::SHAPES );
$sorted = static function ( array $a ): array {
	sort( $a );
	return $a;
};
G::ok( $sorted( $words ) === $sorted( Ops::OPS ), 'T1 the shape table holds every op word of Ops::OPS, once', json_encode( $words ) );
G::ok( count( Ops::OPS ) === count( array_unique( Ops::OPS ) ) && array_merge( Ops::WRITE_OPS, Ops::READ_OPS ) !== []
	&& array_diff( Ops::OPS, Ops::WRITE_OPS, Ops::READ_OPS ) === [] && array_diff( array_merge( Ops::WRITE_OPS, Ops::READ_OPS ), Ops::OPS ) === []
	&& array_intersect( Ops::WRITE_OPS, Ops::READ_OPS ) === [], 'T2 every op is a write op or a read op, never both' );
$same = true;
foreach ( Ops::SHAPES as $op => $shape ) {
	$same = $same && array_keys( $shape ) === [ 'params', 'required', 'prefix' ] && Ops::PARAMS[$op] === $shape['params']
		&& ( Ops::REQUIRED[$op] ?? [] ) === $shape['required'] && is_bool( $shape['prefix'] );
}
G::ok( $same && $sorted( array_keys( Ops::PARAMS ) ) === $sorted( Ops::OPS ) && array_keys( Ops::REQUIRED ) === [ 'PUSH', 'POLL' ],
	'T3 PARAMS and REQUIRED are read from the shape table: each op\'s params, required parameters and prefix flag agree' );
$flags = [];
foreach ( Ops::SHAPES as $op => $shape ) {
	$flags[$op] = $shape['prefix'];
}
G::ok( $flags === [ 'PETITION' => true, 'PUSH' => true, 'RELEASE' => true, 'HEARTBEAT' => true, 'STRUCTURE_TEST' => true,
	'POLL' => false, 'STATUS' => false, 'INQUIRE' => false ], 'T4 the write ops take a prefix and the read ops take none', json_encode( $flags ) );

// ---- Ops::run ---------------------------------------------------------------------------------

$enqueued = [];
$ops = new Ops( new FileTicketStore( "$scratch/tickets" ), static function ( int $id ) use ( &$enqueued ): void {
	$enqueued[] = $id;
}, 30, 4096 );
G::ok( t_code( static fn () => $ops->run( 'TPCRUN', 'TST', 'Agent A', [] ) ) === 'custos-op'
	&& t_code( static fn () => $ops->run( '', null, 'Agent A', [] ) ) === 'custos-op' && $enqueued === [],
	'T5 an op word outside the table is refused custos-op and writes no ticket' );
$bad = [];
foreach ( [ 'POLL' => [ 'ticket' => '1' ], 'STATUS' => [], 'INQUIRE' => [] ] as $op => $params ) {
	if ( t_code( static fn () => $ops->run( $op, 'TST', 'Agent A', $params ) ) !== 'custos-unknown-param' ) {
		$bad[] = $op;
	}
}
G::ok( $bad === [], 'T6 a read op given a prefix is refused custos-unknown-param, as the table says it takes none', json_encode( $bad ) );
$bad = [];
foreach ( [ 'PETITION' => [], 'PUSH' => [ 'records' => '[{"a":1}]' ], 'RELEASE' => [], 'HEARTBEAT' => [], 'STRUCTURE_TEST' => [] ] as $op => $params ) {
	$before = count( $enqueued );
	$a = $ops->run( $op, 'TST', 'Agent A', $params );
	if ( !is_int( $a['ticket'] ?? null ) || ( $a['state'] ?? null ) !== 'QUEUED' || count( $enqueued ) !== $before + 1
		|| t_code( static fn () => $ops->run( $op, null, 'Agent A', $params ) ) !== 'custos-prefix'
		|| t_code( static fn () => $ops->run( $op, 'TST', 'Agent A', [ 'nonesuch' => 'x' ] + $params ) ) !== 'custos-unknown-param' ) {
		$bad[] = $op;
	}
}
G::ok( $bad === [], 'T7 each write op by its word writes its ticket and enqueues it; no prefix is custos-prefix, a parameter outside its row is refused', json_encode( $bad ) );
G::ok( t_code( static fn () => $ops->run( 'PUSH', 'TST', 'Agent A', [] ) ) === 'custos-missing-param'
	&& t_code( static fn () => $ops->run( 'POLL', null, 'Agent A', [] ) ) === 'custos-missing-param',
	'T8 a required parameter missing is refused custos-missing-param (PUSH records, POLL ticket)' );

// ---- the job's handler table and the governor's request -----------------------------------------

$landing = ( new ReflectionClass( Landing::class ) )->newInstanceWithoutConstructor();
$handled = $landing->handled();
G::ok( $handled === Ops::WRITE_OPS, 'T9 the job has one handler per write op word and none for a read op', json_encode( $handled ) );
G::ok( !in_array( 'TPCRUN', $handled, true ) && !in_array( 'POLL', $handled, true ) && !in_array( 'STATUS', $handled, true ),
	'T10 an op word with no handler (an unknown word, a read op) is not in the handler table: the job refuses it REQUEST' );
$bad = [];
foreach ( Ops::WRITE_OPS as $op ) {
	$g = Landing::governed( $op, $op === 'PUSH' ? 3 : 0 );
	if ( $g !== [ 'kind' => $op, 'records' => $op === 'PUSH' ? 3 : 0, 'rows' => 0 ] || array_keys( $g ) !== [ 'kind', 'records', 'rows' ] ) {
		$bad[] = $op;
	}
}
G::ok( $bad === [], 'T11 each write op\'s ticket maps to the governor kind of its word, its records counted and no result rows', json_encode( $bad ) );

// ---- PageWriter::commitOne ----------------------------------------------------------------------

$pt = new PageTitles( 'Principia Machina/UWC', 'Principia Machina' );
$fs = new FileStore( "$scratch/pages" );
$w = new PageWriter( $fs, $pt );
$tReg = $pt->registerVolume( 'TST', 1 );
$tLock = $pt->lock( 'TST' );
$tIdx = $pt->index( 'TST' );
$reg = PageTexts::register( 'TST', 1, '[{"ID":"TST-1"}]' );
$badge = PageTexts::badge( 'TST', [ 'last_push' => '2026-10-24T05:00:00Z', 'last_release' => null, 'calculator_version' => '0.1.0',
	'calculator_digest' => str_repeat( 'a', 64 ), 'record_count' => 1, 'research_assembly' => str_repeat( 'b', 64 ) ], false, 1 );
G::refuses( static fn () => $w->commitOne(), PageFault::class, 'no landing is open', 'T12 commitOne before begin is refused' );
$w->begin( 'TST', 'b1' );
G::refuses( static fn () => $w->commitOne(), PageFault::class, 'exactly one page, not 0', 'T13 commitOne with no page collected is refused, nothing saved' );
$w->begin( 'TST', 'b1' );
$w->put( $tReg, $reg );
$w->put( $tLock, PageTexts::lock( 'TST', null, null, null, null ) );
G::refuses( static fn () => $w->commitOne(), PageFault::class, 'exactly one page, not 2', 'T14 commitOne with two pages collected is refused (the badge is their marker)' );
G::ok( $fs->get( $tReg ) === null && $fs->get( $tLock ) === null, 'T15 the refused one-page landing saved nothing, and the landing is closed' );
$w->begin( 'TST', 'b1' );
$w->put( $tIdx, $badge );
G::refuses( static fn () => $w->commitOne(), PageFault::class, 'INDEX AND BADGE', 'T16 commitOne with the badge as its page is refused: commit() writes the badge' );
G::ok( $fs->get( $tIdx ) === null, 'T17 the badge was not saved by commitOne' );
$w->begin( 'TST', 'b1' );
$w->put( $tReg, $reg );
$fs->tamper( $tReg, 'moved' );
G::refuses( static fn () => $w->commitOne(), PageFault::class, 'BASE MOVED', 'T18 commitOne on a base that moved is refused BASE MOVED' );
G::ok( $fs->get( $tReg ) === 'moved' && count( $fs->revisions[$tReg] ?? [] ) <= 1, 'T19 the moved page is as it was, nothing saved over it' );
$fs->tamper( $tReg, $reg );
$w->begin( 'TST', 'b2' );
$w->put( $tReg, $reg . "\n" );
$saved = $w->commitOne();
$last = $fs->revisions[$tReg][count( $fs->revisions[$tReg] ) - 1] ?? null;
G::ok( $saved === $tReg && $fs->get( $tReg ) === $reg . "\n" && $last !== null && $last['summary'] === sprintf( PageWriter::SUMMARY, 'b2', 'TST' )
	&& $fs->get( $tIdx ) === null, 'T20 commitOne saves the one page under a landing\'s summary, writes no badge, answers its title',
	json_encode( $last ) );
G::refuses( static fn () => $w->commitOne(), PageFault::class, 'no landing is open', 'T21 the landing is closed after a one-page save' );
$w->begin( 'TST', 'b3' );
$outside = $pt->lock( 'OTH' );
G::refuses( static fn () => $w->put( $outside, 'x' ), PageFault::class, 'FENCE', 'T22 the fence holds for a one-page landing: a page of another UWC is refused at put' );

exit( G::report( 'ops_table' ) );
