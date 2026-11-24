<?php
/**
 * assignments.php: Assignments's own test, on the built Calculator (.lake/build/bin/pcalc).
 *
 *   php custos/tests/assignments.php
 *
 * A written block read back equal; a live and an expired row; the row ending at the server time
 * (live); each of the Calculator's words (MALFORMED, TIME, HOLDER, DUPLICATE, with the index) and
 * its refusal of the call passed through; NO ASSIGNMENT, NOT ASSIGNEE and EXPIRED; a block PHP
 * could read and the Calculator refuses, refused with its word (no row parsed in PHP); a page with
 * no block, a page whose blocks are not in form. Prints one line per case and
 * "assignments: ALL PASS <n>/<n>". Without a built pcalc every case is skipped (the check fails
 * on a skip). Command line only; it touches no wiki.
 */

declare( strict_types=1 );

require_once __DIR__ . '/bootstrap.php';

use Custos\Assignments;
use Custos\Blocks;
use Custos\Calculator;
use Custos\PageFault;
use Custos\Tests\AnyResidence;
use Custos\Tests\ProcRunner;

$root = dirname( __DIR__, 2 );
$built = "$root/.lake/build/bin/pcalc";
if ( !is_file( $built ) || !is_executable( $built ) ) {
	G::skip( 'S1-S26 the assignment block through the Calculator', 'no built pcalc in this clone' );
	exit( G::report( 'assignments' ) === 0 ? 0 : 1 );
}
$basic = (string)file_get_contents( "$root/Principia/Basic.lean" );
$version = preg_match( '/^def version : String := "([^"]+)"$/m', $basic, $m ) ? $m[1] : '';
$runner = new ProcRunner();
$calc = new Calculator( $built, [ 'version' => $version, 'digest' => Calculator::digestOf( $built ) ], $runner, 'cli', new AnyResidence() );

$holder = 'Lead agent';
$now = '2026-11-15T12:00:00Z';
$row = static fn ( string $block, string $who, string $ends, string $kind = 'RESULT' ): array =>
	[ 'block' => $block, 'assignee' => $who, 'grant' => 3, 'kind' => $kind, 'ends' => $ends, 'range' => null ];
/** A collaboration page around a block's payload as written (not through block()). */
$page = static fn ( string $payload ): string => "The collaboration page.\n\n" . Blocks::render( 'assignments', $payload ) . "\n";

// The writer.
$live = $row( 'B-1', 'Coworker one', '2026-11-16T00:00:00Z' );
$gone = $row( 'B-2', 'Coworker two', '2026-11-15T11:59:59Z', 'REPRODUCTION' );
$edge = $row( 'B-3', 'Coworker one', $now, 'EOM-0' );
$text = Assignments::block( [ $live, $gone, $edge ] );
G::ok( preg_match( '/\A<pre class="pma-assignments">\n\[.*\]\n<\/pre>\z/s', $text ) === 1 && substr_count( $text, "\n" ) === 2,
	'S1 the block is one pma-assignments block, its payload one line', $text );
G::ok( Blocks::one( "intro\n$text\n", 'assignments' ) === substr( $text, strlen( "<pre class=\"pma-assignments\">\n" ), -strlen( "\n</pre>" ) ),
	'S2 the page\'s block yields the payload the writer wrote' );
G::refuses( static fn () => Assignments::block( [ [ 'block' => 'B-1' ] ] ), PageFault::class, 'assignment row 0',
	'S3 a row lacking members is no row and is not written' );
G::refuses( static fn () => Assignments::block( [ 'a' => $live ] ), PageFault::class, 'list of rows', 'S4 rows keyed by a name are not a list' );
G::refuses( static fn () => Assignments::block( [ $row( 'B-1', 'a<pre>b', $now ) ] ), PageFault::class, '<pre>',
	'S5 a row that would open a block is refused by the block form' );

// The reader, on the built Calculator.
$starts = $runner->starts;
$r = Assignments::read( $calc, "x\n$text\n", $holder, $now );
$rows = [ [ 'account' => 'Coworker one', 'block' => 'B-1', 'ends' => '2026-11-16T00:00:00Z', 'kind' => 'RESULT', 'state' => 'LIVE' ],
	[ 'account' => 'Coworker two', 'block' => 'B-2', 'ends' => '2026-11-15T11:59:59Z', 'kind' => 'REPRODUCTION', 'state' => 'EXPIRED' ],
	[ 'account' => 'Coworker one', 'block' => 'B-3', 'ends' => $now, 'kind' => 'EOM-0', 'state' => 'LIVE' ] ];
G::ok( $r === [ 'rows' => $rows ], 'S6 a written block read back equal: the rows, in order, each live or expired', json_encode( $r ) );
G::ok( $r['rows'][0]['state'] === 'LIVE' && $r['rows'][1]['state'] === 'EXPIRED', 'S7 a live row and an expired row' );
G::ok( $r['rows'][2]['state'] === 'LIVE', 'S8 a row ending at the server time is live' );
G::ok( $runner->starts - $starts === 2 && $calc->starts === $runner->starts, 'S9 the read started the Calculator once (and its version once): no row read in PHP',
	(string)( $runner->starts - $starts ) );
G::ok( Assignments::read( $calc, "x\n$text\n", $holder, '2026-11-15T11:59:59Z' )['rows'][1]['state'] === 'LIVE',
	'S10 the state follows the server time given' );

// The lookup.
G::ok( Assignments::find( $r, 'Coworker one', 'B-1' ) === [ 'row' => $rows[0] ], 'S11 a live row for the account and the block is the answer' );
G::ok( Assignments::find( $r, 'Coworker one', 'B-9' ) === [ 'refused' => 'NO ASSIGNMENT' ], 'S12 no row for the block: NO ASSIGNMENT' );
G::ok( Assignments::find( $r, 'Coworker two', 'B-1' ) === [ 'refused' => 'NOT ASSIGNEE' ], 'S13 a row naming another account: NOT ASSIGNEE' );
G::ok( Assignments::find( $r, 'Coworker two', 'B-2' ) === [ 'refused' => 'EXPIRED' ], 'S14 an expired row of the account: EXPIRED' );
G::ok( Assignments::find( $r, 'Coworker one', 'B-2' ) === [ 'refused' => 'NOT ASSIGNEE' ], 'S15 an expired row of another account: NOT ASSIGNEE before EXPIRED' );
G::ok( Assignments::find( $r, 'Coworker one', 'B-3' ) === [ 'row' => $rows[2] ], 'S16 the row ending at the server time answers' );

// A page without the block.
foreach ( [ 'null page' => null, 'empty page' => '', 'page without the block' => "text only\n" ] as $what => $p ) {
	$n = $runner->starts;
	$e = Assignments::read( $calc, $p, $holder, $now );
	G::ok( $e === [ 'rows' => [] ] && $runner->starts === $n && Assignments::find( $e, 'Coworker one', 'B-1' ) === [ 'refused' => 'NO ASSIGNMENT' ],
		"S17 a $what has no rows and starts nothing: NO ASSIGNMENT" );
}
$empty = Assignments::read( $calc, $page( '[]' ), $holder, $now );
G::ok( $empty === [ 'rows' => [] ], 'S18 an empty block has no rows', json_encode( $empty ) );

// The Calculator's refusals, each word passed through.
$cases = [
	'S19 DUPLICATE with the second row\'s index (the text is JSON PHP could read)' => [ [ $live, $row( 'B-1', 'Coworker two', $now ) ], 'DUPLICATE', 1 ],
	'S20 HOLDER with the row\'s index' => [ [ $live, $row( 'B-4', $holder, $now ) ], 'HOLDER', 1 ],
	'S21 TIME with the row\'s index' => [ [ $row( 'B-1', 'Coworker one', '2026-02-30T00:00:00Z' ) ], 'TIME', 0 ],
	'S22 MALFORMED with the row\'s index (an account with an underscore)' => [ [ $row( 'B-1', 'Coworker_one', $now ) ], 'MALFORMED', 0 ],
];
foreach ( $cases as $what => [ $list, $word, $index ] ) {
	$e = Assignments::read( $calc, $page( json_encode( $list, JSON_THROW_ON_ERROR ) ), $holder, $now );
	G::ok( $e === [ 'refused' => $word, 'index' => $index ], $what, json_encode( $e ) );
}
$e = Assignments::read( $calc, $page( '[{"block": ' ), $holder, $now );
G::ok( $e === [ 'refused' => 'MALFORMED', 'index' => null ], 'S23 text that is not JSON: MALFORMED, no index', json_encode( $e ) );
$e = Assignments::read( $calc, $page( json_encode( [ $live, $row( 'B-1', 'Coworker two', $now ) ] ) ), $holder, $now );
G::ok( Assignments::find( $e, 'Coworker one', 'B-1' ) === $e && Assignments::find( $e, 'Coworker one', 'B-7' ) === $e,
	'S24 a refused block answers every lookup with its word, though the first row is a live one of the account' );
$e = Assignments::read( $calc, $page( json_encode( [ $live ] ) ), 'Lead_agent', $now );
G::ok( ( $e['refused'] ?? '' ) === 'BAD_ARGUMENT' && is_string( $e['detail'] ?? null ) && $e['index'] === null,
	'S25 a Holder that is no account: the Calculator\'s refusal of the call, its code and sentence', json_encode( $e ) );
$e = Assignments::read( $calc, $page( json_encode( [ $live ] ) ), $holder, '2026-11-15 12:00:00' );
G::ok( ( $e['refused'] ?? '' ) === 'BAD_ARGUMENT', 'S26 a server time outside the record\'s form: the Calculator\'s refusal of the call', json_encode( $e ) );

// The page's own form.
G::refuses( static fn () => Assignments::read( $calc, $text . "\n" . $text, $holder, $now ), PageFault::class, 'blocks pma-assignments',
	'S27 two assignment blocks on a page are refused' );
G::refuses( static fn () => Assignments::read( $calc, "<pre class=\"pma-assignments\">\n[]", $holder, $now ), PageFault::class, 'does not close',
	'S28 a block that does not close is refused' );

exit( G::report( 'assignments' ) === 0 ? 0 : 1 );
