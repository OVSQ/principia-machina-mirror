<?php
/**
 * harness.php: Custos's tests that need no MediaWiki.
 *
 *   php custos/tests/harness.php
 *
 * S: the store seam's contract, on FileStore.
 * C: the Calculator over the stand-in binary (fake_pcalc.sh, its digest in fake_pcalc.sha256):
 *    the digest checked before every start, the version read once, the answer and the
 *    refusal read, every fault refused.
 * U: the routes around the permission hook (RestrictedRoutes): the restricted title (the namespace, the
 *    next number, a restricted class, an unreadable title); transclusion and the parser's reads of another
 *    page refused; the settings (non-includable, not searched); search; a text naming the namespace; the
 *    API's namespace parameters refused and its query result scrubbed; the lists' query conditions (fail
 *    closed); the link tables; the routes core closes by its read check; every handler wired.
 * R: the same calls on the built pcalc, when .lake/build/bin/pcalc exists in the clone; its
 *    version must be the one Principia/Basic.lean defines.
 * C and R run the Calculator with AnyResidence, so its binary may sit in the scratch folder.
 * H: the residence check (ResidenceCheck, D10), before the digest check: a residence outside
 *    /opt and /usr, a writable binary, a writable folder, a symbolic link in the chain, a
 *    binary not owned by root, a binary the running user can write, each refused with
 *    UNSAFE RESIDENCE and never started; the safe residence accepted under a fake root the
 *    harness builds. A case this user cannot set up is skipped with its reason, never passed.
 * P: the page classes: the 40 wire words against Principia/Permissions.lean and the permits
 *    vectors; every title form v1 fixes built and read back as its class; the facts a title
 *    cannot carry (OPEN, RETIRED) refusing when absent; a governed title in no form refused.
 * B: the content model: named preformatted blocks written and read, and every page or
 *    payload that would make a block ambiguous refused.
 * Q: the review of the page classes: titles read as MediaWiki reads them before the governed test; roots
 *    in canonical form; the retired fact required; refused prefixes never classed; comments and
 *    unparsed tags refused; a failed pattern match refused.
 * T: the ticket store's contract, on FileTicketStore: create, get, answer once, claim in id
 *    order, a second claim empty, the count in each state.
 * O: the ops of action=pma: each op's GA1 refusals (a missing prefix, a prefix in no form, an
 *    account parameter, records past the byte bound, an unknown parameter, a parameter not one
 *    string), each op's answer form and its ticket and job; POLL of a queued, a done, an
 *    unknown and another account's ticket; a prefix past 255 bytes; scrub of a known root with
 *    a space in it; custos-internal carrying no message and custos-blocked, read in ApiPma's code.
 *    The sweep: POLL of the account's own QUEUED ticket at least the sweep age old pushes its job
 *    again, a younger one, another account's, an IN WORK or a DONE ticket never; POLL's answer keeps
 *    its form; the 202's poll_after the configured constant, Ops naming no Calculator; LandJob
 *    deduplicated, a duplicate ending without error.
 * F: what a ticket's refusal may say (Refusal::detail): INTEGRITY HALT "digest mismatch" alone; an
 *    UNSAFE RESIDENCE the check that failed by name (each of ResidenceCheck's properties in the closed
 *    set); CALCULATOR FAULT the fault's name and the call's family and function; PAGE FAULT the page's
 *    class and the fault's name; JOB FAULT the short class; each fault built with a path, a file name, a
 *    host name and stderr text, none of which reaches the answer.
 * W: the page writer: one save per page per landing, the INDEX AND BADGE page last, a base moved
 *    since it was read refusing the whole landing (BASE MOVED), a save failed before the badge
 *    leaving no badge.
 * X: the three page texts of the path (the lock, a register volume, the index and badge) written
 *    and read back byte for byte through Blocks; every value outside its form refused; the
 *    objects PHP writes the Calculator's canonical JSON of themselves (the built pcalc).
 * K: the permission hook over fake accounts and titles: each governed class and write-class
 *    action, the system user admitted; the restricted classes and namespace refused but for the
 *    Declarer's and the Operator's groups; an unclassifiable governed title refused; an
 *    ungoverned title untouched; and every cell of vectors/permissions.json: the hook admits
 *    nothing permits refuses.
 * L: the landing job (Landing) on the built pcalc over FileStore, FileTicketStore and
 *    FileSeatStore: a PETITION granted and a second refused LOCK HELD; PUSHes refused (not the
 *    holder, a record record_check refuses, records not JSON, a class not landed, the DIGEST GATE)
 *    writing nothing; the spring UWC's first RESULT and ASSUMPTION landed, the badge last; the
 *    admission refused by the seat table with the charge untouched; RELEASE; the integrity halt
 *    on a tampered binary; the job's context. A PUSH naming a block other than the lock's
 *    grant refused NOT HOLDER, one naming none landed under it. record_check's setting the DRAFT
 *    UWC page's: OFF when it states none (LITERATURE refused REC-30), a word not OFF, ON or CLOSED
 *    refused, ON landing it. Any other fault: the ticket answered JOB FAULT with the exception's short
 *    class name and nothing of its message, the class and message given to the error channel (a
 *    sink; by default wfDebugLog's `Custos`), the fault rethrown; a channel that fails stops nothing.
 *    An admission's charge not in admit's form faulting the job; none with the governor off.
 *    A record, a register or a lock carrying an integer PHP cannot hold refused NOT READ, nothing
 *    landed, and so the request, the badge and the access list; a 400-digit integer (INF to PHP)
 *    refused NOT READ, not JOB FAULT; a 20-digit decimal read as its twelve-digit form; the spring records' digests the
 *    Calculator's on the pushed text.
 *    The job's waits (LOCK HELD, PAGE FAULT, an ADMISSION refusal without retry_after) the base plus
 *    `governor jitter` for the draw, within 10 per cent under the default draw; a ticket's job pushed
 *    twice (the enqueue and the sweep) landing it once, the second run writing nothing.
 *    The strike screen: two M records SR3's test finds in contradiction refused STRIKE OWED, and a
 *    record citing a member of such a pair, nothing written; two the test clears landed.
 *    Each refusal through the job (CALCULATOR FAULT from pcalc's stderr, an UNSAFE RESIDENCE, INTEGRITY
 *    HALT, PAGE FAULT, JOB FAULT), its raw answer carrying no "/", no ".php", no host name and no stderr
 *    text, the error channel given the message; the same for a seat charge or a seat unlock faulting
 *    with a query, a path and a host name in its message.
 *    The certificate (FileCertificateStore): an agent with no certificate, or one SUSPENDED or
 *    REVOKED, refused ADMISSION "the account has no certificate in force" before the governor is asked,
 *    no seat lock taken, nothing charged; an ACTIVE one charging the Sponsor's bucket on the Sponsor's
 *    account under both seat locks taken in the order of their names; two agents of one Sponsor sharing
 *    its seat cap (the second refused RATE, payer SPONSOR) and its slots (every bound agent's tickets in
 *    flight counted, a third refused SLOTS).
 *    The Sponsor's seat lock held by another job: the agent's lock released, ADMISSION naming "the account's
 *    sponsor's seat lock", nothing charged; a certificate store whose get() throws: the job faulted, no lock, no
 *    charge; two agents of one Sponsor racing in two processes for its last seat: exactly one admitted.
 *    Skipped with its reason without a built pcalc.
 * JB: the batch jobs' frame (BatchJob) over FileJobRunStore and a scripted governor: the run store's contract; each job answering
 *    NOT BUILT after one `governor admit` of its kind (DEFERRABLE JOB, the recheck BIBLIOGRAPHY RECHECK JOB) at the level CLEAR; lane 5
 *    refused at STRAINED and OVERLOADED (DEFERRED, the retry-after, the body not run) and admitted at BUSY; a refusal with no retry-after
 *    answering defer_wait; JOB CONTEXT with the binary never started; a digest mismatch INTEGRITY HALT; a fault FAULT with no path, host
 *    name or stderr text in the record; a body's outcome and counts recorded, an outcome outside the closed set a FAULT, an unknown job
 *    refused; no fetch and no timer; the job classes and CustosBatch registered.
 * Z: the structure test with register (TPS 5.3.47): the op STRUCTURE_TEST's GA1 refusals and its ticket and
 *    job; the STRUCTURE TEST LINE's form, and its composition from the Calculator's answer alone (findings in
 *    its order, USED in its order, "-" when none, a REFUSED answer refused STRUCTURE TEST); on the built pcalc,
 *    "STRUCTURE TEST none" after the seed, a STRUCTURE_TEST refused NOT HOLDER from a non-holder with nothing
 *    written, the holder's answered with the line, equal to the line of pcalc's own answer for the same
 *    Research Assembly and records, one save; the line unchanged beside its date leaving the page unsaved;
 *    the job refused in lane 5 under pressure writing nothing; a landing pushing one job for its UWC; the
 *    line carried through a PUSH and a RELEASE.
 * Prints the log and "harness: ALL PASS <n>/<n>"; exit 0 only then.
 */

declare( strict_types=1 );

require_once __DIR__ . '/bootstrap.php';

use Custos\BatchJob;
use Custos\Blocks;
use Custos\Budget;
use Custos\MemMeterStore;
use Custos\MeterStore;
use Custos\Meter;
use Custos\Calculator;
use Custos\CertificateStore;
use Custos\Challenge;
use Custos\CalculatorFault;
use Custos\DigestMismatch;
use Custos\JobContext;
use Custos\Landing;
use Custos\PageClass;
use Custos\PageFault;
use Custos\PageStore;
use Custos\PageTexts;
use Custos\PageWriter;
use Custos\PermissionHook;
use Custos\Permits;
use Custos\Ops;
use Custos\PageTitles;
use Custos\Refusal;
use Custos\ResidenceCheck;
use Custos\RestrictedRoutes;
use Custos\SeatStore;
use Custos\ShellRunner;
use Custos\TicketStore;
use Custos\UnsafeResidence;
use Custos\Tests\AnyResidence;
use Custos\Tests\FileCertificateStore;
use Custos\Tests\FileJobRunStore;
use Custos\Tests\FileNonceStore;
use Custos\Tests\FileSeatStore;
use Custos\Tests\FileStore;
use Custos\Tests\FileTicketStore;
use Custos\Tests\ProcRunner;
use Custos\Tests\RacingMeterStore;

$root = dirname( __DIR__, 2 );
$scratch = sys_get_temp_dir() . '/custos-harness-' . getmypid();
/** Remove the harness's own scratch tree, symbolic links as links. */
function harness_clear( string $p ): void {
	if ( is_link( $p ) || is_file( $p ) ) {
		unlink( $p );
	} elseif ( is_dir( $p ) ) {
		foreach ( scandir( $p ) ?: [] as $e ) {
			if ( $e !== '.' && $e !== '..' ) {
				harness_clear( "$p/$e" );
			}
		}
		rmdir( $p );
	}
}
register_shutdown_function( static fn () => harness_clear( $scratch ) );

// ---- S: the store seam ------------------------------------------------------------------

$s = new FileStore( "$scratch/store" );
$t = 'Principia Machina/UWC/TST/Lock';
G::ok( $s instanceof PageStore, 'S1 FileStore keeps the PageStore contract' );
G::ok( $s->get( $t ) === null && !$s->exists( $t ), 'S2 an absent page reads as null and does not exist' );
$s->put( $t, 'one', 'first' );
G::ok( $s->get( $t ) === 'one' && $s->exists( $t ) && count( $s->revisions[$t] ) === 1
	&& $s->revisions[$t][0]['actor'] === 'Custos', 'S3 put writes the page as Custos\'s revision' );
$s->put( $t, 'one', 'again' );
G::ok( count( $s->revisions[$t] ) === 1, 'S4 put of the same text writes nothing (one write per page per landing)' );
G::ok( $s->casPut( $t, 'not the text', 'two', 'cas', 'Holder A' ) === false && $s->get( $t ) === 'one'
	&& count( $s->revisions[$t] ) === 1, 'S5 casPut on a base that does not match writes nothing and answers false' );
G::ok( $s->casPut( $t, null, 'two', 'cas', 'Holder A' ) === false && $s->get( $t ) === 'one',
	'S6 casPut expecting no page fails on a page that exists' );
G::ok( $s->casPut( $t, 'one', 'two', 'cas', 'Holder A' ) === true && $s->get( $t ) === 'two'
	&& end( $s->revisions[$t] )['actor'] === 'Holder A', 'S7 casPut on the matching base writes, as the named account\'s revision' );
G::ok( $s->casPut( $t, 'two', 'two', 'cas', 'Holder A' ) === true && count( $s->revisions[$t] ) === 2,
	'S8 casPut of the text already there answers true and writes nothing' );
$n = 'Principia Machina/UWC/TST/New';
G::ok( $s->casPut( $n, null, 'new', 'cas', 'Holder B' ) === true && $s->get( $n ) === 'new',
	'S9 casPut expecting no page creates it' );
$l = 'Principia Machina/Log';
$a = $s->appendAs( $l, 'line 1', 'append', 'Declarer' );
$b = $s->appendAs( $l, 'line 2', 'append', 'Declarer' );
G::ok( $a === 'line 1' && $b === "line 1\nline 2" && $s->get( $l ) === $b
	&& array_column( $s->revisions[$l], 'actor' ) === [ 'Declarer', 'Declarer' ],
	'S10 appendAs appends a line after a line feed, as the named account\'s revision, and answers the text' );
G::ok( $s->titles() === [ $l, $t, $n ], 'S11 titles with "/" and spaces are kept apart and listed', implode( ' | ', $s->titles() ) );
$s->tamper( $t, 'by hand' );
G::ok( $s->get( $t ) === 'by hand' && count( $s->revisions[$t] ) === 2, 'S12 a hand edit (tamper) logs no revision' );

// ---- C: the Calculator over the stand-in ---------------------------------------------------

$fakeSource = __DIR__ . '/fake_pcalc.sh';
$fakeDigest = trim( (string)file_get_contents( __DIR__ . '/fake_pcalc.sha256' ) );
G::ok( Calculator::digestOf( $fakeSource ) === $fakeDigest, 'C1 the stand-in digests to fake_pcalc.sha256',
	Calculator::digestOf( $fakeSource ) );
mkdir( "$scratch/bin", 0755, true );
chmod( $scratch, 0755 );
$fake = "$scratch/bin/pcalc";
copy( $fakeSource, $fake );
chmod( $fake, 0755 );
$want = [ 'version' => '0.1.0', 'digest' => $fakeDigest ];
$request = '{"value":{"b":1,"a":[2,3]}}';
$answer = '"{\"a\":[2,3],\"b\":1}"';

/**
 * The calls every binary must answer the same way: the stand-in (C) and the built pcalc (R).
 */
function calculator_calls( string $tag, string $binary, array $want, string $request, string $answer ): void {
	$runner = new ProcRunner();
	$c = new Calculator( $binary, $want, $runner, 'cli', new AnyResidence() );
	G::ok( $c->version() === $want['version'] && $c->starts === 1, "{$tag}2 pcalc version is read and equals CustosBuild's ({$want['version']})" );
	$r = $c->call( 'canonical', 'canonical_json', $request );
	G::ok( $r === [ 'exit' => 0, 'text' => $answer, 'value' => '{"a":[2,3],"b":1}' ],
		"{$tag}3 a call answers the canonical line and its value", json_encode( $r ) );
	$c->call( 'canonical', 'canonical_json', $request );
	G::ok( $c->starts === 3 && $runner->starts === 3, "{$tag}4 the version is read once per object: two calls, three starts",
		"starts {$c->starts}" );
	$r = $c->call( 'nofamily', 'nofunction', '{}' );
	G::ok( $r['exit'] === 2 && in_array( $r['refused'] ?? '', [ 'USAGE', 'UNKNOWN_FAMILY' ], true ) && is_string( $r['detail'] ?? null ),
		"{$tag}5 a refusal of the call (exit 2) is answered as a refusal", json_encode( $r ) );
	G::refuses( static fn () => $c->call( '--version', 'x', '{}' ), CalculatorFault::class, 'not a family or function name',
		"{$tag}6 a family that is not a word is refused before any start" );
}

calculator_calls( 'C', $fake, $want, $request, $answer );

$runner = new ProcRunner();
$c = new Calculator( $fake, $want, $runner, 'cli', new AnyResidence() );
$r = $c->call( 'canonical', 'canonical_json', '{"value":1}' );
G::ok( $r['exit'] === 1 && $r['refused'] === 'BAD_ARGUMENT' && $r['detail'] !== '',
	'C7 a refusal of the request (exit 1) is answered with its code and detail', json_encode( $r ) );
G::refuses( static fn () => $c->call( 'fault', 'exit', '{}' ), CalculatorFault::class, 'exit code 3',
	'C8 an exit code other than 0, 1 or 2 is a fault' );
G::refuses( static fn () => $c->call( 'fault', 'lines', '{}' ), CalculatorFault::class, 'did not write one line',
	'C9 an answer of two lines is a fault' );

$tampered = "$scratch/bin/pcalc-tampered";
copy( $fake, $tampered );
chmod( $tampered, 0755 );
file_put_contents( $tampered, "\n", FILE_APPEND );
$runner = new ProcRunner();
$c = new Calculator( $tampered, $want, $runner, 'cli', new AnyResidence() );
$e = G::refuses( static fn () => $c->call( 'canonical', 'canonical_json', $request ), DigestMismatch::class, 'DIGEST MISMATCH',
	'C10 a tampered binary is refused with DIGEST MISMATCH' );
G::ok( $runner->starts === 0 && $e instanceof DigestMismatch && $e->expected === $fakeDigest
	&& $e->found === Calculator::digestOf( $tampered ), 'C11 the tampered binary was never started; the refusal names both digests' );
G::ok( !( $e instanceof CalculatorFault ), 'C12 a digest mismatch is not a CalculatorFault (it halts; it is never caught as one)' );

$swap = "$scratch/bin/pcalc-swap";
copy( $fake, $swap );
chmod( $swap, 0755 );
$runner = new ProcRunner();
$c = new Calculator( $swap, $want, $runner, 'cli', new AnyResidence() );
$c->call( 'canonical', 'canonical_json', $request );
file_put_contents( $swap, "\n", FILE_APPEND );
G::refuses( static fn () => $c->call( 'canonical', 'canonical_json', $request ), DigestMismatch::class, 'DIGEST MISMATCH',
	'C13 the digest is checked before every call: a binary changed after the version was read is refused' );
G::ok( $runner->starts === 2, 'C14 the changed binary was not started', "starts {$runner->starts}" );

G::refuses( static fn () => ( new Calculator( "$scratch/bin/absent", $want, new ProcRunner(), 'cli', new AnyResidence() ) )->version(),
	DigestMismatch::class, '(unreadable)', 'C15 a binary that cannot be read is a digest mismatch' );
G::refuses( static fn () => ( new Calculator( '', $want, new ProcRunner(), 'cli', new AnyResidence() ) )->version(),
	CalculatorFault::class, 'CustosCalculator is empty', 'C16 no binary configured: no call (no default path)' );
G::refuses( static fn () => ( new Calculator( $fake, [ 'version' => '0.1.0', 'digest' => '' ], new ProcRunner(), 'cli', new AnyResidence() ) )->version(),
	CalculatorFault::class, 'names no digest', 'C17 no digest configured: no call' );
G::refuses( static fn () => ( new Calculator( $fake, [ 'version' => '0.1.0', 'digest' => strtoupper( $fakeDigest ) ], new ProcRunner(), 'cli', new AnyResidence() ) )->version(),
	CalculatorFault::class, 'names no digest', 'C18 a digest not in lowercase hexadecimal is not a digest' );
G::refuses( static fn () => ( new Calculator( $fake, [ 'version' => '0.2.0', 'digest' => $fakeDigest ], new ProcRunner(), 'cli', new AnyResidence() ) )->version(),
	CalculatorFault::class, 'not the expected "0.2.0"', 'C19 a version other than CustosBuild\'s is refused' );
$runner = new ProcRunner();
G::refuses( static fn () => ( new Calculator( $fake, $want, $runner, 'fpm-fcgi', new AnyResidence() ) )->call( 'canonical', 'canonical_json', $request ),
	CalculatorFault::class, 'never called inside a web request', 'C20 inside a web request no call is made' );
G::ok( $runner->starts === 0, 'C21 the web request\'s call started nothing' );

// ---- H: the residence check (D10), before the digest check ---------------------------------

$posix = function_exists( 'posix_geteuid' );
$isRoot = $posix && posix_geteuid() === 0;
$live = new ResidenceCheck();

/** A residence the harness builds under its fake root $top: $top/pma/pcalc, 0755 throughout. */
function residence_build( string $top, string $source ): string {
	harness_clear( $top );
	mkdir( "$top/pma", 0755, true );
	chmod( $top, 0755 );
	chmod( "$top/pma", 0755 );
	copy( $source, "$top/pma/pcalc" );
	chmod( "$top/pma/pcalc", 0755 );
	return "$top/pma/pcalc";
}

/** The residence probe's own time limit, in seconds: the probe answers in well under one. */
const PROBE_LIMIT = 60;

/**
 * Run argv with its standard output and error read until $limit seconds have passed (stream_select
 * with a deadline), then its end waited for to the same deadline (proc_get_status polled, so a process
 * that closed its output and runs on holds no wait): [output, exit code, why]. Past the deadline, or
 * when stream_select fails, the process is stopped (proc_terminate, SIGKILL), its pipes closed (a
 * grandchild that holds them holds no wait), proc_close then returning at once, and why says so; the
 * output is then null. A process that cannot be started gives [null, -1, the reason]. No wait in it is
 * unbounded, so a probe that hangs ends the case, never the harness. $select stands in for
 * stream_select (a case's own, to see its failure).
 */
function bounded_run( array $argv, ?array $env, int $limit, ?callable $select = null ): array {
	$select ??= static fn ( array &$r, int $s, int $us ) => @stream_select( $r, $w, $e, $s, $us );
	$proc = proc_open( $argv, [ 0 => [ 'file', '/dev/null', 'r' ], 1 => [ 'pipe', 'w' ], 2 => [ 'pipe', 'w' ] ], $pipes, null, $env );
	if ( !is_resource( $proc ) ) {
		return [ null, -1, 'the probe could not be started' ];
	}
	stream_set_blocking( $pipes[1], false );
	stream_set_blocking( $pipes[2], false );
	$out = '';
	$open = [ 1 => $pipes[1], 2 => $pipes[2] ];
	$deadline = microtime( true ) + $limit;
	$failed = false;
	while ( $open !== [] ) {
		$left = $deadline - microtime( true );
		if ( $left <= 0 ) {
			break;
		}
		$read = array_values( $open );
		$n = $select( $read, (int)floor( $left ), (int)( ( $left - floor( $left ) ) * 1e6 ) );
		if ( $n === false ) {
			$failed = true;
			break;
		}
		foreach ( $read as $r ) {
			$chunk = fread( $r, 65536 );
			if ( $chunk === false || ( $chunk === '' && feof( $r ) ) ) {
				unset( $open[array_search( $r, $open, true )] );
				continue;
			}
			if ( $r === $pipes[1] ) {
				$out .= $chunk;
			}
		}
	}
	$code = null;
	while ( !$failed && $open === [] ) {
		$st = proc_get_status( $proc );
		if ( !$st['running'] ) {
			$code = (int)$st['exitcode'];   // read once: proc_close cannot give it after this
			break;
		}
		if ( microtime( true ) >= $deadline ) {
			break;
		}
		usleep( 20000 );
	}
	if ( $code === null ) {
		proc_terminate( $proc, 9 );
		fclose( $pipes[1] );
		fclose( $pipes[2] );
		proc_close( $proc );
		return [ null, -1, $failed ? 'the probe\'s output could not be read and the probe was stopped'
			: "the probe overran its limit of $limit s and was stopped" ];
	}
	fclose( $pipes[1] );
	fclose( $pipes[2] );
	proc_close( $proc );
	return [ $out, $code, '' ];
}

/**
 * Run the live check, or the check under the fake root $top, as a user other than root
 * (setpriv to uid and gid 65534) within PROBE_LIMIT seconds: [the answer ("resident", or the
 * refusal), ''], or [null, why] when it could not be run or overran its limit.
 */
function residence_as_other( string $top, string $path ): array {
	$setpriv = is_executable( '/usr/bin/setpriv' ) ? '/usr/bin/setpriv' : '';
	if ( $setpriv === '' ) {
		return [ null, 'setpriv to uid 65534 could not run the probe here' ];
	}
	$argv = [ $setpriv, '--reuid=65534', '--regid=65534', '--clear-groups', PHP_BINARY,
		__DIR__ . '/residence_probe.php', $top, $path ];
	[ $out, $code, $why ] = bounded_run( $argv, null, PROBE_LIMIT );
	if ( $out === null ) {
		return [ null, $why ];
	}
	$out = trim( $out );
	return ( $code === 0 || $code === 1 ) && $out !== '' ? [ $out, '' ]
		: [ null, 'setpriv to uid 65534 could not run the probe here' ];
}

G::refuses( static fn () => $live->check( $fake ), UnsafeResidence::class, 'is outside /opt and /usr',
	'H1 a residence outside /opt and /usr is refused' );
G::refuses( static fn () => $live->check( '/opt/pma/../pma/pcalc' ), UnsafeResidence::class, 'is not in normal form',
	'H2 a path with a ".." segment is refused' );
G::refuses( static fn () => $live->check( 'opt/pma/pcalc' ), UnsafeResidence::class, 'is not an absolute path',
	'H3 a relative path is refused' );

$top = "$scratch/res/opt";
$check = new ResidenceCheck( [ $top ] );
$bin = residence_build( $top, $fake );
chmod( $bin, 0775 );
G::refuses( static fn () => $check->check( $bin ), UnsafeResidence::class, "$bin is writable by group or other",
	'H4 a binary writable by its group is refused' );
$bin = residence_build( $top, $fake );
chmod( "$top/pma", 0757 );
G::refuses( static fn () => $check->check( $bin ), UnsafeResidence::class, "$top/pma is writable by group or other",
	'H5 a folder above the binary writable by other is refused, naming the folder' );
chmod( "$top/pma", 0755 );
symlink( "$top/pma/pcalc", "$top/pma/link" );
G::refuses( static fn () => $check->check( "$top/pma/link" ), UnsafeResidence::class, "$top/pma/link is a symbolic link",
	'H6 a binary that is a symbolic link is refused' );
symlink( "$top/pma", "$top/lnk" );
G::refuses( static fn () => $check->check( "$top/lnk/pcalc" ), UnsafeResidence::class, "$top/lnk is a symbolic link",
	'H7 a symbolic link among the folders is refused' );
$bin = residence_build( $top, $fake );
if ( $isRoot ) {
	chown( $bin, 65534 );
}
G::refuses( static fn () => $check->check( $bin ), UnsafeResidence::class, "$bin is not owned by root",
	'H8 a binary not owned by root is refused' . ( $isRoot ? ' (owner 65534)' : ' (owner: this user)' ) );
$bin = residence_build( $top, $fake );
if ( $isRoot ) {
	G::refuses( static fn () => $check->check( $bin ), UnsafeResidence::class, "is writable by the running user",
		'H9 a binary the running user can write is refused (root, who writes every file)' );
	[ $seen, $why ] = residence_as_other( $top, $bin );
	if ( $seen === null ) {
		G::skip( 'H10 the safe residence (root, 0755 throughout) is accepted for a user other than root', $why );
	} else {
		G::ok( $seen === 'resident', 'H10 the safe residence (root, 0755 throughout) is accepted for a user other than root', $seen );
	}
} else {
	G::skip( 'H9 a binary the running user can write is refused',
		'this user cannot make a file that is root\'s and still its own to write; H8 refuses its own files first' );
	G::skip( 'H10 the safe residence (root, 0755 throughout) is accepted for a user other than root',
		'this user cannot create a root-owned file under the fake root' );
}
$usrBin = realpath( '/usr/bin/env' );
if ( !is_string( $usrBin ) || strncmp( $usrBin, '/usr/', 5 ) !== 0 ) {
	G::skip( 'H11 the live check accepts a root-owned binary under /usr', '/usr/bin/env does not resolve under /usr here' );
} elseif ( !$posix ) {
	G::skip( 'H11 the live check accepts a root-owned binary under /usr',
		'no posix extension here: the live check refuses every binary, as it must where the running user is unknown' );
} elseif ( $isRoot ) {
	[ $seen, $why ] = residence_as_other( 'live', $usrBin );
	if ( $seen === null ) {
		G::skip( "H11 the live check accepts a root-owned binary under /usr ($usrBin)", $why );
	} else {
		G::ok( $seen === 'resident', "H11 the live check accepts a root-owned binary under /usr ($usrBin)", $seen );
	}
} else {
	$why = '';
	try {
		$live->check( $usrBin );
	} catch ( UnsafeResidence $refused ) {
		$why = $refused->getMessage();
	}
	G::ok( $why === '', "H11 the live check accepts a root-owned binary under /usr ($usrBin)", $why );
}

$runner = new ProcRunner();
$c = new Calculator( $tampered, $want, $runner, 'cli' );
$e = G::refuses( static fn () => $c->call( 'canonical', 'canonical_json', $request ), UnsafeResidence::class, 'UNSAFE RESIDENCE',
	'H12 the Calculator\'s live check refuses a binary outside /opt and /usr, before its digest is checked (a tampered binary)' );
G::ok( $runner->starts === 0 && !( $e instanceof CalculatorFault ) && !( $e instanceof DigestMismatch ),
	'H13 that binary was never started; the refusal is neither a CalculatorFault nor a digest mismatch' );
$any = new AnyResidence();
$runner = new ProcRunner();
$c = new Calculator( $fake, $want, $runner, 'cli', $any );
$c->call( 'canonical', 'canonical_json', $request );
$c->call( 'canonical', 'canonical_json', $request );
G::ok( $any->checks === 1 && $runner->starts === 3, 'H14 the residence is checked once per object: two calls, one check, three starts',
	"checks {$any->checks}, starts {$runner->starts}" );

// The rule: no residence override. The sources the wiki runs read no environment and make
// no ResidenceCheck of their own; and the live check, run in a process whose environment names a
// root it does not name under every name tried, still refuses a safe residence under that root.
// Each pattern must compile: preg_match returns false on a broken pattern, which counts as a
// finding, never as a pass; and the second pattern must match the two spellings it is for.
$envPattern = '/\bgetenv\s*\(|\$_ENV\b|\$_SERVER\b|putenv\s*\(/';
$newPattern = '#new\s+\\\\?(?:Custos\\\\)?ResidenceCheck\b#';
$selfTest = [ 'new ResidenceCheck( [ $top ] )' => 1, 'new \\Custos\\ResidenceCheck( [] )' => 1,
	'new ResidenceChecker()' => 0, 'ResidenceCheck::class' => 0 ];
$selfMiss = [];
foreach ( $selfTest as $s => $want ) {
	if ( preg_match( $newPattern, $s ) !== $want ) {
		$selfMiss[] = $s;
	}
}
G::ok( $selfMiss === [] && preg_match( $envPattern, 'getenv( "X" )' ) === 1,
	'H15a the H15 patterns compile and match the spellings they are for (new ResidenceCheck, new \\Custos\\ResidenceCheck, getenv)',
	implode( '; ', $selfMiss ) );
$envReads = [];
foreach ( array_merge( glob( dirname( __DIR__ ) . '/includes/*.php' ) ?: [], glob( dirname( __DIR__ ) . '/maintenance/*.php' ) ?: [] ) as $f ) {
	$src = (string)file_get_contents( $f );
	$e = preg_match( $envPattern, $src );
	$n = basename( $f ) !== 'Calculator.php' ? preg_match( $newPattern, $src ) : 0;
	if ( $e !== 0 || $n !== 0 ) {
		$envReads[] = basename( $f ) . ( $e === false || $n === false ? ' (pattern error)' : '' );
	}
}
G::ok( $envReads === [], 'H15 no source of the wiki\'s side (includes/, maintenance/) reads the environment or makes a ResidenceCheck but the Calculator\'s live one',
	implode( ', ', $envReads ) );
$bin = residence_build( $top, $fake );
$names = [ 'CUSTOS_' . 'RESIDENCE_' . 'ROOT', 'CUSTOS_RESIDENCE', 'CUSTOS_ROOT', 'CUSTOS_ROOTS', 'RESIDENCE_ROOT', 'PMA_RESIDENCE', 'CUSTOS_CALCULATOR' ];
$env = array_fill_keys( $names, $top );
$argv = $isRoot && is_executable( '/usr/bin/setpriv' )
	? [ '/usr/bin/setpriv', '--reuid=65534', '--regid=65534', '--clear-groups', PHP_BINARY, __DIR__ . '/residence_probe.php', 'live', $bin ]
	: [ PHP_BINARY, __DIR__ . '/residence_probe.php', 'live', $bin ];
[ $seen, $code, $why ] = bounded_run( $argv, $env, PROBE_LIMIT );
$seen = trim( (string)$seen );
if ( $why !== '' ) {
	$seen = $why;
}
G::ok( $code === 1 && str_starts_with( $seen, 'UNSAFE RESIDENCE: ' ) && str_contains( $seen, "$bin is outside /opt and /usr" ),
	'H16 a binary under a root the check does not name is refused UNSAFE RESIDENCE whatever the environment holds (the root named under ' . count( $names ) . ' names)',
	"exit $code: $seen" );

$began = microtime( true );
[ $hung, $hungCode, $hungWhy ] = bounded_run( [ PHP_BINARY, '-r', 'fwrite( STDOUT, "x" ); sleep( 30 );' ], null, 1 );
$took = microtime( true ) - $began;
G::ok( $hung === null && $hungCode === -1 && str_contains( $hungWhy, 'overran its limit of 1 s' ) && $took < 10,
	'H17 a probe that overruns its limit is stopped within it, its case given the reason, never a wait without end',
	sprintf( '%.1f s: %s', $took, $hungWhy ) );
$began = microtime( true );
[ $closed, $closedCode, $closedWhy ] = bounded_run( [ PHP_BINARY, '-r', 'fclose( STDOUT ); fclose( STDERR ); sleep( 30 );' ], null, 1 );
$took = microtime( true ) - $began;
G::ok( $closed === null && $closedCode === -1 && str_contains( $closedWhy, 'overran its limit of 1 s' ) && $took < 10,
	'H17b a probe that closes its output and runs on is stopped at its limit too, never waited for',
	sprintf( '%.1f s: %s', $took, $closedWhy ) );
[ $fine, $fineCode, $fineWhy ] = bounded_run( [ PHP_BINARY, '-r', 'echo "answer\n"; exit( 1 );' ], null, 10 );
G::ok( $fine === "answer\n" && $fineCode === 1 && $fineWhy === '',
	'H17c a probe that ends within its limit gives its output and its own exit code', var_export( [ $fine, $fineCode ], true ) );
$began = microtime( true );
[ $unread, $unreadCode, $unreadWhy ] = bounded_run( [ PHP_BINARY, '-r', 'sleep( 30 );' ], null, 20,
	static fn ( array &$r, int $s, int $us ) => false );
$took = microtime( true ) - $began;
G::ok( $unread === null && $unreadCode === -1 && str_contains( $unreadWhy, 'could not be read and the probe was stopped' ) && $took < 10,
	'H17d a probe whose output cannot be read (stream_select fails) is stopped at once, never waited for',
	sprintf( '%.1f s: %s', $took, $unreadWhy ) );
$began = microtime( true );
$heldPid = sys_get_temp_dir() . '/pma-h17e-' . getmypid() . '.pid';
@unlink( $heldPid );
// The grandchild leaves the probe's session where it can (posix_setsid), else stays in it; either way it
// holds the probe's output past the probe's stop, and only the probe itself is stopped.
$grandCode = ( function_exists( 'posix_setsid' ) ? 'posix_setsid(); ' : '' )
	. 'file_put_contents( ' . var_export( $heldPid, true ) . ', getmypid() ); sleep( 30 );';
$heldArgv = [ '/bin/sh', '-c', escapeshellarg( PHP_BINARY ) . ' -r ' . escapeshellarg( $grandCode ) . ' & exec sleep 30' ];
[ $held, $heldCode, $heldWhy ] = bounded_run( $heldArgv, null, 1 );
$took = microtime( true ) - $began;
$grand = is_file( $heldPid ) ? (int)file_get_contents( $heldPid ) : 0;
if ( $grand > 0 && function_exists( 'posix_kill' ) ) {
	posix_kill( $grand, 9 );
}
@unlink( $heldPid );
G::ok( $held === null && $heldCode === -1 && str_contains( $heldWhy, 'overran its limit of 1 s' ) && $took < 10,
	'H17e a probe whose grandchild holds its output past the stop is closed at its limit, never waited for',
	sprintf( '%.1f s: %s', $took, $heldWhy ) );

// ---- P: the page classes and their titles ----------------------------------------------------

$pt = new PageTitles( 'Principia Machina/UWC', 'Principia Machina' );
/** The facts every page of a UWC needs (S3 of the review of the page classes): the UWC is live, stated. */
$live = [ 'retired' => false ];
$lean = (string)file_get_contents( "$root/Principia/Permissions.lean" );
$leanWords = preg_match( '/instance : WireWord PageClass where.*?toWire\n(.*?)\n\n/s', $lean, $m )
	&& preg_match_all( '/=> "([A-Z_ ]+)"/', $m[1], $mm ) ? $mm[1] : [];
G::ok( PageClass::WORDS === $leanWords && count( PageClass::WORDS ) === 40,
	'P1 the 40 page-class wire words, in the order of PageClass in Principia/Permissions.lean', count( $leanWords ) . ' read from the Lean file' );
$vec = json_decode( (string)file_get_contents( "$root/vectors/permissions.json" ), true );
$wire = array_values( array_filter( $vec ?: [], static fn ( $c ) => ( $c['function'] ?? '' ) === 'wire' && ( $c['enum'] ?? '' ) === 'PageClass' && isset( $c['members'] ) ) );
G::ok( count( $wire ) === 1 && $wire[0]['members'] === PageClass::WORDS, 'P2 the same words as the wire case of vectors/permissions.json' );
$publicNoRead = [];
foreach ( $vec ?: [] as $c ) {
	if ( ( $c['function'] ?? '' ) === 'permits' && ( $c['actor'] ?? '' ) === 'PUBLIC' && isset( $c['permitted'] )
		&& !in_array( 'READ', $c['permitted'], true ) ) {
		$publicNoRead[] = $c['class'];
	}
}
$publicNoRead = array_values( array_unique( $publicNoRead ) );
sort( $publicNoRead );
$restricted = PageClass::RESTRICTED;
sort( $restricted );
G::ok( $publicNoRead === $restricted, 'P3 the restricted classes are exactly those the Public does not read in the permits vectors ('
	. implode( ', ', $restricted ) . ')', implode( ', ', $publicNoRead ) );

/** Each form: the builder's title, the class it reads back as, and the parts it carries. */
$forms = [
	[ $pt->draft( 'TST' ), 'Principia Machina/UWC/TST/Draft', PageClass::DRAFT_UWC, [ 'prefix' => 'TST' ] ],
	[ $pt->researchAssembly( 'TST', 'Starting Set' ), 'Principia Machina/UWC/TST/Research Assembly/Starting Set',
		PageClass::RESEARCH_ASSEMBLY, [ 'part' => 'Starting Set' ] ],
	[ $pt->researchAssembly( 'TST', 'Correspondence Table' ), 'Principia Machina/UWC/TST/Research Assembly/Correspondence Table',
		PageClass::RESEARCH_ASSEMBLY, [] ],
	[ $pt->researchAssembly( 'TST', 'Criteria Set' ), 'Principia Machina/UWC/TST/Research Assembly/Criteria Set', PageClass::RESEARCH_ASSEMBLY, [] ],
	[ $pt->registerVolume( 'TST', 3 ), 'Principia Machina/UWC/TST/Register/Volume 3', PageClass::REGISTER_FROZEN, [ 'volume' => 3 ] ],
	[ $pt->bibliographyVolume( 'TST', 1 ), 'Principia Machina/UWC/TST/Bibliography/Volume 1', PageClass::BIBLIOGRAPHY_FROZEN, [ 'volume' => 1 ] ],
	[ $pt->accessList( 'TST' ), 'Principia Machina/UWC/TST/Access list', PageClass::ACCESS_LIST, [] ],
	[ $pt->lock( 'TST' ), 'Principia Machina/UWC/TST/Lock', PageClass::LOCK_PAGE, [] ],
	[ $pt->collaboration( 'TST' ), 'Principia Machina/UWC/TST/Collaboration', PageClass::COLLABORATION, [] ],
	[ $pt->staging( 'TST' ), 'Principia Machina/UWC/TST/Collaboration/Staging', PageClass::STAGING, [] ],
	[ $pt->staging( 'TST', 'Coworker A' ), 'Principia Machina/UWC/TST/Collaboration/Staging/Coworker A', PageClass::STAGING, [] ],
	[ $pt->controlPanel( 'TST' ), 'Principia Machina/UWC/TST/Control panel', PageClass::CONTROL_PANEL, [] ],
	[ $pt->controlPanel( 'TST', 'Schedule log' ), 'Principia Machina/UWC/TST/Control panel/Schedule log', PageClass::CONTROL_PANEL, [] ],
	[ $pt->index( 'TST' ), 'Principia Machina/UWC/TST/Index', PageClass::INDEX_AND_BADGE, [] ],
	[ $pt->reading( 'TST' ), 'Principia Machina/UWC/TST/Reading', PageClass::SPINE, [] ],
	[ $pt->communityView( 'TST' ), 'Principia Machina/UWC/TST/Community View', PageClass::COMMUNITY_LEDGER, [] ],
	[ $pt->fleetIndex(), 'Principia Machina/UWC/Index', PageClass::INDEX_AND_BADGE, [ 'prefix' => null ] ],
	[ $pt->declarationsHead(), 'Principia Machina/Declarations', PageClass::CHAIN_HEAD, [] ],
	[ $pt->buildChainHead(), 'Principia Machina/Build chain', PageClass::CHAIN_HEAD, [] ],
	[ $pt->declarationsVolume( 12 ), 'Principia Machina/Declarations/Volume 12', PageClass::DECLARATIONS_VOLUME, [ 'volume' => 12 ] ],
	[ $pt->buildChainVolume( 1 ), 'Principia Machina/Build chain/Volume 1', PageClass::BUILD_CHAIN_VOLUME, [ 'volume' => 1 ] ],
	[ $pt->communityLedgerVolume( 2 ), 'Principia Machina/Community Ledger/Volume 2', PageClass::COMMUNITY_LEDGER, [ 'volume' => 2 ] ],
	[ $pt->dossier( 'Agent One' ), 'Principia Machina/Dossier/Agent One', PageClass::DOSSIER, [ 'account' => 'Agent One' ] ],
	[ $pt->falconPage( 'F7' ), 'Principia Machina/Falcon/F7', PageClass::FALCON_PAGE, [ 'part' => 'F7' ] ],
	[ $pt->topPerformers(), 'Principia Machina/Top performers', PageClass::TOP_PERFORMER, [] ],
	[ $pt->topPerformers( '2026-10' ), 'Principia Machina/Top performers/2026-10', PageClass::TOP_PERFORMER, [ 'part' => '2026-10' ] ],
	[ $pt->configurationStrata(), 'Principia Machina/Configuration strata', PageClass::CONFIGURATION_STRATA, [] ],
	[ $pt->provision( 'GRAV-NEWTON', '1.0.0' ), 'Principia Machina/Provision/GRAV-NEWTON/1.0.0', PageClass::PROVISION,
		[ 'part' => 'GRAV-NEWTON', 'version' => '1.0.0' ] ],
	[ $pt->score( 'Agent One' ), 'Restricted:Score/Agent One', PageClass::SCORE_OR_USER_PAGE, [ 'account' => 'Agent One', 'restricted' => true ] ],
	[ $pt->falconRestricted( 'F7' ), 'Restricted:Falcon/F7', PageClass::FALCON_RESTRICTED, [ 'part' => 'F7', 'restricted' => true ] ],
	[ $pt->falconStratum(), 'Restricted:Falcon/Stratum', PageClass::FALCON_RESTRICTED, [ 'restricted' => true ] ],
];
$bad = [];
foreach ( $forms as [ $built, $want, $class, $parts ] ) {
	$r = $pt->classify( $built, $live );
	$ok = $built === $want && $r->class === $class && $r->governed && $r->restricted === ( $parts['restricted'] ?? false );
	foreach ( [ 'prefix', 'volume', 'account', 'part', 'version' ] as $k ) {
		if ( array_key_exists( $k, $parts ) && $r->$k !== $parts[$k] ) {
			$ok = false;
		}
	}
	if ( !$ok ) {
		$bad[] = "$built -> " . ( $r->class ?? 'none' );
	}
}
G::ok( $bad === [], 'P4 every title form builds the title v1 fixes, in PMA\'s words, and reads back as its class with its parts ('
	. count( $forms ) . ' forms)', implode( '; ', $bad ) );
$covered = array_unique( array_merge( array_column( $forms, 2 ), [ PageClass::REGISTER_OPEN, PageClass::BIBLIOGRAPHY_OPEN, PageClass::RETIRED_CONTAINER ] ) );
G::ok( count( $covered ) === 25, 'P5 the forms reach 25 of the 40 classes; the other 15 have no title form v1 fixes (listed in the README)',
	count( $covered ) . ': ' . implode( ', ', array_diff( PageClass::WORDS, $covered ) ) );
G::ok( $pt->classify( $pt->registerVolume( 'TST', 3 ), [ 'open' => true ] + $live )->class === PageClass::REGISTER_OPEN
	&& $pt->classify( $pt->bibliographyVolume( 'TST', 1 ), [ 'open' => true ] + $live )->class === PageClass::BIBLIOGRAPHY_OPEN
	&& $pt->classify( $pt->registerVolume( 'TST', 3 ), [ 'open' => 'yes' ] + $live )->class === PageClass::REGISTER_FROZEN,
	'P6 a volume is OPEN only when the caller states it OPEN (true); any other fact reads FROZEN' );
$ret = [];
foreach ( [ $pt->draft( 'TST' ), $pt->lock( 'TST' ), $pt->registerVolume( 'TST', 1 ), $pt->uwc( 'TST' ) . '/Anything' ] as $x ) {
	$ret[] = $pt->classify( $x, [ 'retired' => true ] )->class;
}
G::ok( $ret === [ PageClass::RETIRED_CONTAINER, PageClass::RETIRED_CONTAINER, PageClass::RETIRED_CONTAINER, null ]
	&& $pt->classify( $pt->declarationsHead(), [ 'retired' => true ] )->class === PageClass::CHAIN_HEAD,
	'P7 every page of a UWC stated RETIRED that fits a form is RETIRED CONTAINER; an unknown subpage stays without a class; a page outside the UWC root is not' );
$none = [
	'Principia Machina/UWC/TST/Unknown', 'Principia Machina/UWC/TST', 'Principia Machina/UWC', 'Principia Machina/UWC/TST/Register/Volume 0',
	'Principia Machina/UWC/TST/Register/Volume 03', 'Principia Machina/UWC/TST/Register', 'Principia Machina/UWC/TST/Research Assembly/TPK',
	'Principia Machina/UWC/9X/Draft', 'Principia Machina/UWC/T-1/Draft', 'Principia Machina/UWC/TST/Draft/Sub', 'Principia Machina/UWC/TST/Lock/Old',
	'Principia Machina/Declarations/Volume x', 'Principia Machina/Declarations/Other', 'Principia Machina/Dossier', 'Principia Machina/Dossier/A/B',
	'Principia Machina/Falcon/Stratum', 'Principia Machina/Top performers/2026-13', 'Principia Machina/Configuration strata/Old',
	'Principia Machina/Provision/grav/1.0.0', 'Principia Machina/Provision/GRAV/1.0', 'Principia Machina/Provision/GRAV/01.0.0',
	'Restricted:Score', 'Restricted:Score/A/B', 'Restricted:Canary/X', 'Restricted:Anything',
];
$wrong = [];
foreach ( $none as $x ) {
	$r = $pt->classify( $x );
	if ( !$r->refused() || $r->restricted !== ( strncmp( $x, 'Restricted:', 11 ) === 0 ) ) {
		$wrong[] = "$x -> " . ( $r->class ?? 'none' ) . ( $r->governed ? '' : ' (not governed)' );
	}
}
G::ok( $wrong === [], 'P8 a governed title in no form has no class and is refused, a restricted one still read as restricted ('
	. count( $none ) . ' titles)', implode( '; ', $wrong ) );
$free = [ 'Main Page', 'Principia Machina', 'Principia Machina/Progress/Status', 'Principia Machina/Hub', 'Principia Machina UWC/TST/Draft',
	'Talk:Principia Machina/UWC/TST/Draft' ];
$wrong = [];
foreach ( $free as $x ) {
	$r = $pt->classify( $x );
	if ( $r->governed || $r->class !== null || $r->restricted ) {
		$wrong[] = $x;
	}
}
G::ok( $wrong === [], 'P9 a title outside the two roots and the restricted namespace is not governed (the hand-edited and published pages)',
	implode( '; ', $wrong ) );
G::ok( $pt->classify( 'Principia_Machina/UWC/TST/Register/Volume_3', $live )->class === PageClass::REGISTER_FROZEN
	&& $pt->classify( ' Principia  Machina/UWC/TST/Lock ', $live )->class === PageClass::LOCK_PAGE
	&& $pt->classify( 'restricted:Score/Agent One' )->class === PageClass::SCORE_OR_USER_PAGE
	&& $pt->classify( 'RESTRICTED:Falcon/F7' )->restricted
	&& $pt->classify( 'principia Machina/UWC/TST/Lock', $live )->class === PageClass::LOCK_PAGE,
	'P10 a title is read in MediaWiki\'s text form: underscores and runs of spaces, the first letter, the namespace in any case' );
G::ok( $pt->draft( 'My_UWC' ) === 'Principia Machina/UWC/My UWC/Draft' && $pt->classify( $pt->draft( 'My_UWC' ) )->prefix === 'My_UWC'
	&& $pt->classify( 'Principia Machina/UWC/My_UWC/Draft' )->prefix === 'My_UWC',
	'P11 a prefix\'s underscore is a space in its title and reads back as the prefix' );
$refusals = [
	'P12 a prefix that is not an identifier' => static fn () => $pt->draft( '9X' ),
	'P13 a prefix with a hyphen' => static fn () => $pt->lock( 'T-1' ),
	'P14 a prefix with a run of underscores (its title would be another prefix\'s)' => static fn () => $pt->lock( 'A__B' ),
	'P15 a prefix beginning with an underscore' => static fn () => $pt->lock( '_A' ),
	'P16 the prefix Index (the fleet index\'s page)' => static fn () => $pt->lock( 'Index' ),
	'P17 a zone outside the Research Assembly\'s three' => static fn () => $pt->researchAssembly( 'TST', 'TPK' ),
	'P18 volume 0' => static fn () => $pt->registerVolume( 'TST', 0 ),
	'P19 an account with a slash' => static fn () => $pt->dossier( 'A/B' ),
	'P20 an account with an underscore' => static fn () => $pt->score( 'Agent_One' ),
	'P21 an account with a bidi override' => static fn () => $pt->dossier( "Agent\u{202E}One" ),
	'P22 an account that is not UTF-8' => static fn () => $pt->dossier( "Agent\xffOne" ),
	'P23 an account with a character MediaWiki refuses in a title' => static fn () => $pt->dossier( 'A[1]' ),
	'P24 a falcon named Stratum' => static fn () => $pt->falconPage( 'Stratum' ),
	'P25 a month 2026-13' => static fn () => $pt->topPerformers( '2026-13' ),
	'P26 a Provision identifier in lower case' => static fn () => $pt->provision( 'grav', '1.0.0' ),
	'P27 a Provision version with a leading zero' => static fn () => $pt->provision( 'GRAV', '1.01.0' ),
	'P28 a staging subpage with an empty segment' => static fn () => $pt->staging( 'TST', 'A//B' ),
	'P29 a title longer than 255 bytes' => static fn () => $pt->staging( 'TST', str_repeat( 'x', 250 ) ),
];
foreach ( $refusals as $what => $fn ) {
	G::refuses( $fn, PageFault::class, '', "$what is refused (PageFault)" );
}
$e = null;
try {
	$pt->dossier( "Agent\u{202E}One\xff" );
} catch ( PageFault $x ) {
	$e = $x->getMessage();
}
G::ok( $e !== null && strpos( $e, '<U+202E>' ) !== false && strpos( $e, '<0xFF>' ) !== false && strpos( $e, "\u{202E}" ) === false,
	'P30 a refusal shows a disallowed code point as <U+XXXX> and an invalid byte as <0xHH>, never the character (echo safety)', (string)$e );
G::refuses( static fn () => new PageTitles( '', 'Principia Machina' ), PageFault::class, 'CustosUwcRoot', 'P31 an empty page root is refused' );
$pt2 = new PageTitles( 'Wiki/Uwcs', 'Wiki/Decl' );
G::ok( $pt2->lock( 'TST' ) === 'Wiki/Uwcs/TST/Lock' && $pt2->classify( 'Wiki/Uwcs/TST/Lock', $live )->class === PageClass::LOCK_PAGE
	&& !$pt2->classify( 'Principia Machina/UWC/TST/Lock' )->governed && $pt2->declarationsHead() === 'Wiki/Decl/Declarations',
	'P32 the roots are the configuration\'s (CustosUwcRoot, CustosDeclRoot), never fixed in the code' );

// ---- B: the content model, named preformatted blocks ---------------------------------------

$rec = '{"CLASS":"RESULT","ID":"TST-4"}';
$blk = Blocks::render( 'record', $rec );
G::ok( $blk === "<pre class=\"pma-record\">\n$rec\n</pre>", 'B1 a block is <pre class="pma-<name>">, a line feed, the payload, a line feed, </pre>' );
$page = "Intro text.\n" . $blk . "\n" . Blocks::render( 'void', 'TST-5' ) . "\n" . Blocks::render( 'record', "{\"ID\":\"TST-6\"}\n{\"x\":\"\u{00E9}\"}" ) . "\nEnd.";
G::ok( Blocks::extract( $page, 'record' ) === [ $rec, "{\"ID\":\"TST-6\"}\n{\"x\":\"\u{00E9}\"}" ] && Blocks::extract( $page, 'void' ) === [ 'TST-5' ]
	&& Blocks::extract( $page, 'badge' ) === [], 'B2 extract answers the payloads of one name, in page order, multi-line and UTF-8 kept; other names passed over' );
G::ok( Blocks::extract( null, 'record' ) === [] && Blocks::extract( '', 'record' ) === [] && Blocks::extract( 'plain text', 'record' ) === [],
	'B3 no page, an empty page and a page without blocks read as no blocks' );
G::ok( Blocks::one( $page, 'void' ) === 'TST-5' && Blocks::one( $page, 'badge' ) === null, 'B4 one answers the one block of a name, or null' );
G::refuses( static fn () => Blocks::one( $page, 'record' ), PageFault::class, '2 blocks', 'B5 one refuses a page carrying two blocks of the name' );
G::ok( Blocks::all( $page ) === [ [ 'record', $rec ], [ 'void', 'TST-5' ], [ 'record', "{\"ID\":\"TST-6\"}\n{\"x\":\"\u{00E9}\"}" ] ],
	'B6 all answers every block, name and payload, in page order' );
G::ok( Blocks::extract( Blocks::render( 'record', '' ), 'record' ) === [ '' ], 'B7 an empty payload round-trips' );
$bad = [
	'B8 a block name with a capital' => static fn () => Blocks::render( 'Record', '{}' ),
	'B9 a block name with a hyphen' => static fn () => Blocks::render( 'chain-head', '{}' ),
	'B10 a payload carrying </pre>' => static fn () => Blocks::render( 'record', '{"a":"</pre>"}' ),
	'B11 a payload carrying </PRE > in another case' => static fn () => Blocks::render( 'record', '{"a":"</PRE >"}' ),
	'B12 a payload carrying <pre>' => static fn () => Blocks::render( 'record', '<pre>x' ),
	'B13 a payload that is not UTF-8' => static fn () => Blocks::render( 'record', "\xc3" ),
	'B14 a page whose block does not close' => static fn () => Blocks::all( "<pre class=\"pma-record\">\n{}\n" ),
	'B15 a page with a block opened inside a block' => static fn () => Blocks::all( "<pre class=\"pma-a\">\n<pre class=\"pma-b\">\nx\n</pre>\n</pre>" ),
	'B16 a page with a closing tag and no block' => static fn () => Blocks::all( "text </pre> more" ),
	'B17 a page with an unnamed pre block' => static fn () => Blocks::all( "<pre>\nx\n</pre>" ),
	'B18 a page with a version 1 block (tpm-)' => static fn () => Blocks::all( "<pre class=\"tpm-record\">\n{}\n</pre>" ),
	'B19 a page with a PRE tag in capitals' => static fn () => Blocks::all( "<PRE class=\"pma-record\">\n{}\n</PRE>" ),
	'B20 a block without its final line feed' => static fn () => Blocks::all( "<pre class=\"pma-record\">\n{}</pre>" ),
	'B21 a page that is not UTF-8' => static fn () => Blocks::all( "<pre class=\"pma-record\">\n\xff\n</pre>" ),
];
foreach ( $bad as $what => $fn ) {
	G::refuses( $fn, PageFault::class, '', "$what is refused (PageFault)" );
}
G::ok( Blocks::all( "<prefix> and </prefixed> are not pre tags\n" . $blk ) === [ [ 'record', $rec ] ],
	'B22 a tag that only begins with "pre" is text, not a block' );
$fs = new FileStore( "$scratch/pages" );
$title = $pt->registerVolume( 'TST', 1 );
$fs->put( $title, $page, 'write' );
G::ok( Blocks::extract( $fs->get( $title ), 'record' ) === Blocks::extract( $page, 'record' ),
	'B23 what a page holds after the store\'s put reads back block for block' );


// ---- Q: the review of the page classes (S1-S4 and the further refusals), each a refusal or a reading ------

/** classify $title with $facts and compare class, governed and restricted (and parts). */
function q_reads( PageTitles $pt, string $title, array $facts, ?string $class, bool $governed, bool $restricted, array $parts = [] ): bool {
	$r = $pt->classify( $title, $facts );
	$ok = $r->class === $class && $r->governed === $governed && $r->restricted === $restricted;
	foreach ( $parts as $k => $v ) {
		$ok = $ok && $r->$k === $v;
	}
	return $ok;
}
$nbsp = "\u{00A0}";
// S1: MediaWiki's title normalization before the governed test.
$s1 = [
	'Q1 "Restricted :Score/x" (a space before the colon) reads as the restricted score page'
		=> [ 'Restricted :Score/x', [], PageClass::SCORE_OR_USER_PAGE, true, true, [ 'account' => 'x' ] ],
	'Q2 "Restricted_:Score/x" (an underscore before the colon) reads as the restricted score page'
		=> [ 'Restricted_:Score/x', [], PageClass::SCORE_OR_USER_PAGE, true, true ],
	'Q3 ":Restricted:Score/x" (a leading colon) reads as the restricted score page'
		=> [ ':Restricted:Score/x', [], PageClass::SCORE_OR_USER_PAGE, true, true ],
	'Q4 "Restricted: Score/x" (a space after the colon) reads as the restricted score page'
		=> [ 'Restricted: Score/x', [], PageClass::SCORE_OR_USER_PAGE, true, true ],
	'Q5 a no-break space inside the UWC root folds to a space: the lock page'
		=> [ "Principia{$nbsp}Machina/UWC/TST/Lock", $live, PageClass::LOCK_PAGE, true, false ],
	'Q6 a no-break space at the end of an account folds away: the score page of "x"'
		=> [ "Restricted:Score/x{$nbsp}", [], PageClass::SCORE_OR_USER_PAGE, true, true, [ 'account' => 'x' ] ],
	'Q7 an ideographic space and a narrow no-break space fold too'
		=> [ "Principia\u{3000}Machina/UWC/TST/Access\u{202F}list", $live, PageClass::ACCESS_LIST, true, false ],
	'Q8 a decomposed "José" reads in NFC: the dossier of the composed name'
		=> [ "Principia Machina/Dossier/Jose\u{0301}", [], PageClass::DOSSIER, true, false, [ 'account' => "Jos\u{00E9}" ] ],
	'Q9 a direction mark MediaWiki strips is stripped: the lock page'
		=> [ "Principia Machina/UWC/TST/Lock\u{200E}", $live, PageClass::LOCK_PAGE, true, false ],
	'Q10 "::Restricted:Score/x" (two leading colons) cannot be read exactly: governed, restricted, refused'
		=> [ '::Restricted:Score/x', [], null, true, true ],
	'Q11 a title that is not UTF-8 cannot be read: governed, restricted, refused'
		=> [ "Principia Machina/UWC/TST/Lock\xff", $live, null, true, true ],
	'Q12 a governed title cut by "#" is refused'
		=> [ 'Principia Machina/UWC/TST/Lock#top', $live, null, true, false ],
	'Q13 a restricted title MediaWiki refuses (a "[") is refused, still restricted'
		=> [ 'Restricted:Score/a[1]', [], null, true, true ],
	'Q14 a governed title with a percent escape is refused'
		=> [ 'Principia Machina/Dossier/A%2FB', [], null, true, false ],
	'Q15 a governed title with a "." or ".." segment is refused'
		=> [ 'Principia Machina/UWC/TST/./Lock', $live, null, true, false ],
	'Q16 "Principia Machina/Dossier/.." is refused'
		=> [ 'Principia Machina/Dossier/..', [], null, true, false ],
];
foreach ( $s1 as $what => [ $title, $facts, $class, $gov, $res ] ) {
	$parts = $s1[$what][5] ?? [];
	$r = $pt->classify( $title, $facts );
	G::ok( q_reads( $pt, $title, $facts, $class, $gov, $res, $parts ), $what,
		'class ' . ( $r->class ?? 'none' ) . ', governed ' . var_export( $r->governed, true ) . ', restricted ' . var_export( $r->restricted, true ) );
}
G::ok( PageTitles::canon( "Principia Machina/UWC/TST/Lock{$nbsp}", false ) === null
	&& PageTitles::canon( "Principia Machina/Dossier/Jose\u{0301}", false ) === null
	&& PageTitles::canon( 'Principia Machina/UWC/TST/Lock', false ) === [ null, 'Principia Machina/UWC/TST/Lock', true, false ],
	'Q17 without a normalizer, a title with any non-ASCII byte cannot be read (fail closed); an ASCII title still reads' );
G::refuses( static fn () => $pt->dossier( "Jose\u{0301}" ), PageFault::class, '', 'Q18 the builder refuses an account not in NFC' );
G::refuses( static fn () => $pt->dossier( '.' ), PageFault::class, '', 'Q19 the builder refuses the account "."' );
G::refuses( static fn () => $pt->staging( 'TST', 'A/..' ), PageFault::class, '', 'Q20 the builder refuses a ".." subpage segment' );

// S2: the roots must be canonical; an invalid root throws.
$roots = [
	'Q21 a root whose first letter is lower case' => [ 'principia Machina/UWC', 'Principia Machina' ],
	'Q22 a root with a leading slash' => [ '/Principia Machina/UWC', 'Principia Machina' ],
	'Q23 a root with a trailing slash' => [ 'Principia Machina/UWC/', 'Principia Machina' ],
	'Q24 a root with a double slash' => [ 'Principia Machina//UWC', 'Principia Machina' ],
	'Q25 a root with an underscore' => [ 'Principia Machina/UWC', 'Principia_Machina' ],
	'Q26 a root with a run of spaces' => [ 'Principia  Machina/UWC', 'Principia Machina' ],
	'Q27 a root with a no-break space' => [ "Principia{$nbsp}Machina/UWC", 'Principia Machina' ],
	'Q28 a root in a namespace' => [ 'Restricted:UWC', 'Principia Machina' ],
	'Q29 a root not in NFC' => [ 'Principia Machina/UWC', "Jose\u{0301}" ],
	'Q30 a root with a "#"' => [ 'Principia Machina/UWC#x', 'Principia Machina' ],
	'Q31 the Declarer\'s root under the UWC root' => [ 'Principia Machina/UWC', 'Principia Machina/UWC/D' ],
	'Q32 the UWC root under a governed segment of the Declarer\'s root' => [ 'Principia Machina/Dossier/U', 'Principia Machina' ],
];
foreach ( $roots as $what => [ $u, $d ] ) {
	G::refuses( static fn () => new PageTitles( $u, $d ), PageFault::class, '', "$what is refused (PageFault)" );
}

// S3: the retired fact is required for a UWC page, and never classes a title in no form.
G::ok( q_reads( $pt, $pt->lock( 'TST' ), [], null, true, false ) && q_reads( $pt, $pt->draft( 'TST' ), [ 'retired' => 'yes' ], null, true, false )
	&& q_reads( $pt, $pt->registerVolume( 'TST', 1 ), [ 'retired' => 1, 'open' => true ], null, true, false ),
	'Q33 a UWC page whose retired fact is absent or not a boolean has no class' );
G::ok( q_reads( $pt, 'Principia Machina/UWC/TST/Garbage', [ 'retired' => true ], null, true, false )
	&& q_reads( $pt, 'Principia Machina/UWC/TST/Register/Volume 0', [ 'retired' => true ], null, true, false ),
	'Q34 RETIRED gives no class to a governed title in no form' );
G::ok( q_reads( $pt, $pt->fleetIndex(), [], PageClass::INDEX_AND_BADGE, true, false )
	&& q_reads( $pt, $pt->declarationsHead(), [], PageClass::CHAIN_HEAD, true, false ),
	'Q35 pages outside a UWC need no retired fact' );

// S4: a prefix the builders refuse never classifies.
$prefixes = [ 'Principia Machina/UWC/Index/Draft', 'Principia Machina/UWC/Index/Lock',
	'Principia Machina/UWC/_A/Lock', 'Principia Machina/UWC/A_/Lock', 'Principia Machina/UWC/9A/Lock', 'Principia Machina/UWC/A-B/Lock' ];
$wrong = [];
foreach ( $prefixes as $x ) {
	if ( !q_reads( $pt, $x, $live, null, true, false ) ) {
		$wrong[] = $x;
	}
}
G::ok( $wrong === [], 'Q36 a prefix the builders refuse (Index, an underscore at an end, not an identifier) is governed and has no class', implode( '; ', $wrong ) );
G::ok( q_reads( $pt, 'Principia Machina/UWC/A__B/Lock', $live, PageClass::LOCK_PAGE, true, false, [ 'prefix' => 'A_B' ] )
	&& $pt->lock( 'A_B' ) === 'Principia Machina/UWC/A B/Lock',
	'Q46 "A__B" in a title is the page MediaWiki stores as "A B", prefix A_B\'s lock, which the builder makes; the prefix A__B itself is refused (P14)' );

// Blocks: comments and unparsed tags make a page ambiguous; a failed match refuses.
$amb = [
	'Q37 a block inside <nowiki>' => "<nowiki>\n$blk\n</nowiki>",
	'Q38 a block inside a comment' => "<!--\n$blk\n-->",
	'Q39 a block inside <syntaxhighlight>' => "<syntaxhighlight lang=\"json\">\n$blk\n</syntaxhighlight>",
	'Q40 a block inside <math>' => "<math>\n$blk\n</math>",
	'Q41 a comment beside a block' => "$blk\n<!-- note -->",
	'Q42 an unclosed <NOWIKI/> in capitals beside a block' => "$blk\n<NOWIKI/>",
];
foreach ( $amb as $what => $text ) {
	G::refuses( static fn () => Blocks::all( $text ), PageFault::class, '', "$what makes the page ambiguous: refused (PageFault)" );
}
G::refuses( static fn () => Blocks::render( 'record', '{"a":"<!--"}' ), PageFault::class, '', 'Q43 a payload carrying a comment opening is refused' );
G::refuses( static fn () => Blocks::render( 'record', '{"a":"<nowiki>"}' ), PageFault::class, '', 'Q44 a payload carrying <nowiki> is refused' );
$jit = ini_get( 'pcre.jit' );
$limit = ini_get( 'pcre.backtrack_limit' );
ini_set( 'pcre.jit', '0' );
ini_set( 'pcre.backtrack_limit', '1' );
$e = null;
try {
	Blocks::all( str_repeat( 'a', 64 ) . "\n" . $blk );
} catch ( Throwable $x ) {
	$e = $x;
}
ini_set( 'pcre.backtrack_limit', (string)$limit );
ini_set( 'pcre.jit', (string)$jit );
G::ok( $e instanceof PageFault && strpos( $e->getMessage(), 'could not be searched' ) !== false,
	'Q45 a pattern match that fails (the backtrack limit) refuses the page, never reads as "no block"', $e === null ? 'nothing refused' : get_class( $e ) . ': ' . $e->getMessage() );

// Rework 2: character references decoded before the governed test; no title written with one is
// ever given a class (Custos never writes one); a reference not decoded exactly refuses.
$refs = [
	'Q47 "&#82;estricted:Score/x" (a decimal reference)' => [ '&#82;estricted:Score/x', [], true ],
	'Q48 "&#x52;estricted:Score/x" (a hexadecimal reference)' => [ '&#x52;estricted:Score/x', [], true ],
	'Q49 "Restricted&#58;Score/x" (the namespace colon as a reference)' => [ 'Restricted&#58;Score/x', [], true ],
	'Q50 "&#80;rincipia Machina/UWC/TST/Lock"' => [ '&#80;rincipia Machina/UWC/TST/Lock', $live, false ],
	'Q51 "Principia Machina&#47;UWC/TST/Lock" (a slash as a reference)' => [ 'Principia Machina&#47;UWC/TST/Lock', $live, false ],
	'Q52 "Principia Machina&sol;Dossier/x" (a named slash)' => [ 'Principia Machina&sol;Dossier/x', [], false ],
	'Q53 "Principia&nbsp;Machina/UWC/TST/Lock" (a named no-break space)' => [ 'Principia&nbsp;Machina/UWC/TST/Lock', $live, false ],
	'Q54 "Restricted:Score/&#x78;" (a reference inside the account)' => [ 'Restricted:Score/&#x78;', [], true ],
	'Q55 "&#0082;estricted:Score/x" (leading zeros)' => [ '&#0082;estricted:Score/x', [], true ],
	'Q56 "&#xD800;estricted:Score/x" (a surrogate: not decoded exactly)' => [ '&#xD800;estricted:Score/x', [], true ],
	'Q57 "&#0;Restricted:Score/x" (NUL: not decoded exactly)' => [ '&#0;Restricted:Score/x', [], true ],
	'Q58 "&#99999999999;Principia Machina/UWC/TST/Lock" (out of range)' => [ '&#99999999999;Principia Machina/UWC/TST/Lock', $live, true ],
	'Q59 "&bogusname;Principia Machina/UWC/TST/Lock" (an unknown name)' => [ '&bogusname;Principia Machina/UWC/TST/Lock', $live, true ],
];
foreach ( $refs as $what => [ $title, $facts, $res ] ) {
	$r = $pt->classify( $title, $facts );
	G::ok( $r->class === null && $r->governed && $r->restricted === $res, "$what is governed, has no class" . ( $res ? ', and reads restricted' : '' ),
		'class ' . ( $r->class ?? 'none' ) . ', governed ' . var_export( $r->governed, true ) . ', restricted ' . var_export( $r->restricted, true ) );
}
$c = PageTitles::canon( '&#82;estricted:Score/x' );
G::ok( $c === [ PageTitles::RESTRICTED_NAMESPACE, 'Score/x', true, true ] && PageTitles::canon( 'Principia&nbsp;Machina/UWC/TST/Lock' )
	=== [ null, 'Principia Machina/UWC/TST/Lock', true, true ] && PageTitles::canon( 'A &amp;amp; B' ) === [ null, 'A &amp; B', false, true ],
	'Q60 canon decodes each reference once, as MediaWiki does, and marks the title as written with one', json_encode( $c ) );
G::ok( q_reads( $pt, 'Main &amp; Side', [], null, false, false ) && q_reads( $pt, 'Principia Machina/Hub &#38; More', [], null, false, false ),
	'Q61 a title outside the governed territory stays ungoverned with or without a reference' );
$amb2 = [];
foreach ( [ 'gallery', 'hiero', 'timeline', 'html', 'ref', 'references', 'translate', 'poem', 'mapframe', 'maplink', 'imagemap', 'inputbox',
	'categorytree' ] as $tag ) {
	$page = "<$tag>\n$blk\n</$tag>";
	try {
		Blocks::all( $page );
		$amb2[] = $tag;
	} catch ( PageFault $x ) {
	}
	try {
		Blocks::render( 'record', "{\"a\":\"<$tag>\"}" );
		$amb2[] = "$tag (payload)";
	} catch ( PageFault $x ) {
	}
}
G::ok( $amb2 === [], 'Q62 a page or payload carrying gallery, hiero, timeline, html, ref, references, translate, poem, mapframe, maplink, imagemap, inputbox or categorytree is refused', implode( ', ', $amb2 ) );
G::ok( Blocks::all( "<refer> is text\n$blk" ) === [ [ 'record', $rec ] ], 'Q63 a tag that only begins with a refused name ("refer") is text' );
G::refuses( static fn () => Blocks::render( 'record', "{\"a\":\"x\0y\"}" ), PageFault::class, 'NUL', 'Q64 a payload carrying a NUL is refused' );
G::refuses( static fn () => Blocks::all( "<pre class=\"pma-record\">\nx\0y\n</pre>" ), PageFault::class, 'NUL', 'Q65 a page carrying a NUL is refused' );

// ---- T: the ticket store's contract, on FileTicketStore -------------------------------------

$ts = new FileTicketStore( "$scratch/tickets-t" );
G::ok( $ts->get( 1 ) === null, 'T1 an unknown ticket reads as null' );
G::ok( $ts->claimNext() === null, 'T2 an empty store has nothing to claim' );
$t1 = $ts->create( 'PETITION', 'Agent A', 'QED', '{"prefix":"QED"}' );
$t2 = $ts->create( 'PUSH', 'Agent B', 'QED', '{"prefix":"QED","records":"[]"}' );
$t3 = $ts->create( 'RELEASE', 'Agent A', 'GR', '{"prefix":"GR"}' );
G::ok( $t1 >= 1 && $t2 > $t1 && $t3 > $t2, "T3 create gives increasing ids ($t1, $t2, $t3)" );
$r1 = $ts->get( $t1 );
G::ok( is_array( $r1 ) && $r1['id'] === $t1 && $r1['op'] === 'PETITION' && $r1['account'] === 'Agent A' && $r1['prefix'] === 'QED',
	'T4 get reads back the op, the account and the prefix', json_encode( $r1 ) );
G::ok( is_array( $r1 ) && $r1['request'] === '{"prefix":"QED"}', 'T5 get reads back the request byte for byte' );
G::ok( is_array( $r1 ) && $r1['state'] === TicketStore::QUEUED && $r1['answer'] === null && $r1['done'] === null,
	'T6 a new ticket is QUEUED, with no answer and no done time' );
G::ok( is_array( $r1 ) && preg_match( '/\A[0-9]{14}\z/', $r1['created'] ) === 1, 'T7 the created time is 14 digits' );
$c1 = $ts->claimNext();
G::ok( is_array( $c1 ) && $c1['id'] === $t1 && $c1['state'] === TicketStore::IN_WORK, 'T8 claimNext takes the oldest QUEUED ticket, IN WORK' );
G::ok( ( $ts->get( $t1 )['state'] ?? '' ) === TicketStore::IN_WORK, 'T9 the claimed ticket stays IN WORK' );
$c2 = $ts->claimNext();
G::ok( is_array( $c2 ) && $c2['id'] === $t2, 'T10 the next claim takes the next ticket in id order' );
G::ok( $ts->answer( $t1, 'ANSWER ONE' ) === true, 'T11 answer of a ticket IN WORK is written' );
$d1 = $ts->get( $t1 );
G::ok( is_array( $d1 ) && $d1['state'] === TicketStore::DONE && $d1['answer'] === 'ANSWER ONE'
	&& preg_match( '/\A[0-9]{14}\z/', (string)$d1['done'] ) === 1, 'T12 the answered ticket is DONE with its answer and a done time' );
G::ok( $ts->answer( $t1, 'ANSWER TWO' ) === false && ( $ts->get( $t1 )['answer'] ?? '' ) === 'ANSWER ONE',
	'T13 a second answer is refused and the first stands' );
G::ok( $ts->answer( 999999, 'x' ) === false, 'T14 answer of an unknown ticket is refused' );
G::ok( $ts->answer( $t3, 'ANSWER THREE' ) === true && ( $ts->get( $t3 )['state'] ?? '' ) === TicketStore::DONE,
	'T15 answer of a QUEUED ticket makes it DONE' );
G::ok( $ts->claimNext() === null, 'T16 a second claim with none QUEUED is empty' );
G::ok( $ts->answer( $t2, '' ) === true && ( $ts->get( $t2 )['answer'] ?? null ) === '', 'T17 an empty answer is an answer' );
$t4 = $ts->create( 'PETITION', 'Agent A', 'QED', '{"prefix":"QED"}' );
$ts->create( 'RELEASE', 'Agent B', 'QED', '{"prefix":"QED"}' );
$ts->claim( $t4 );
G::ok( $ts->count( TicketStore::QUEUED ) === 1 && $ts->count( TicketStore::IN_WORK ) === 1 && $ts->count( TicketStore::DONE ) === 3,
	'T18 count gives the tickets in each state (QUEUED 1, IN WORK 1, DONE 3)' );
G::ok( $ts->count( 'queued' ) === 0 && $ts->count( '' ) === 0 && ( new FileTicketStore( "$scratch/tickets-t-empty" ) )->count( TicketStore::QUEUED ) === 0,
	'T19 count of a word that is no state, or of an empty store, is 0' );

// ---- O: the ops of action=pma (PETITION, POLL, PUSH, RELEASE), GA1 and the answer forms ---------

$enqueued = [];
$ots = new FileTicketStore( "$scratch/tickets-o" );
$ops = new Ops( $ots, static function ( int $id ) use ( &$enqueued ): void {
	$enqueued[] = $id;
}, 30, 64 );
/** The refusal's code, or "none". */
function o_code( callable $fn ): string {
	try {
		$fn();
	} catch ( Refusal $e ) {
		return $e->what;
	}
	return 'none';
}
$writers = [ 'PETITION' => [], 'PUSH' => [ 'records' => '[{"a":1}]' ], 'RELEASE' => [] ];
foreach ( $writers as $op => $base ) {
	$m = strtolower( $op );
	$before = count( $enqueued );
	G::ok( o_code( static fn () => $ops->$m( null, 'Agent A', $base ) ) === 'custos-prefix', "O $op: a missing prefix is refused (custos-prefix)" );
	G::ok( o_code( static fn () => $ops->$m( '', 'Agent A', $base ) ) === 'custos-prefix', "O $op: an empty prefix is refused (custos-prefix)" );
	G::ok( o_code( static fn () => $ops->$m( 'Q-E D', 'Agent A', $base ) ) === 'custos-prefix', "O $op: a prefix in no form is refused (custos-prefix)" );
	G::ok( o_code( static fn () => $ops->$m( 'Index', 'Agent A', $base ) ) === 'custos-prefix', "O $op: the prefix Index is refused (custos-prefix)" );
	G::ok( o_code( static fn () => $ops->$m( [ 'QED' ], 'Agent A', $base ) ) === 'custos-shape', "O $op: a prefix sent as an array is refused (custos-shape)" );
	G::ok( o_code( static fn () => $ops->$m( 'QED', 'Agent A', $base + [ 'account' => 'Agent B' ] ) ) === 'custos-account',
		"O $op: a second account parameter is refused (custos-account)" );
	G::ok( o_code( static fn () => $ops->$m( 'QED', 'Agent A', $base + [ 'account' => 'Agent A' ] ) ) === 'custos-account',
		"O $op: an account parameter naming the same account is refused too (custos-account)" );
	G::ok( o_code( static fn () => $ops->$m( 'QED', 'Agent A', array_merge( $base, [ 'records' => str_repeat( 'x', 65 ) ] ) ) )
		=== ( $op === 'PUSH' ? 'custos-too-large' : 'custos-unknown-param' ),
		"O $op: records past the byte bound is refused (" . ( $op === 'PUSH' ? 'custos-too-large' : 'custos-unknown-param, records not its parameter' ) . ')' );
	G::ok( o_code( static fn () => $ops->$m( 'QED', 'Agent A', $base + [ 'grant' => '1' ] ) ) === 'custos-unknown-param',
		"O $op: an unknown parameter is refused (custos-unknown-param)" );
	G::ok( o_code( static fn () => $ops->$m( 'QED', 'Agent A', $base + [ 'block' => [ 'b1' ] ] ) ) === 'custos-shape',
		"O $op: a parameter sent as an array is refused (custos-shape)" );
	G::ok( o_code( static fn () => $ops->$m( 'QED', 'Agent A', $base + [ 'block' => 'b 1' ] ) ) === 'custos-shape',
		"O $op: a block not in its form is refused (custos-shape)" );
	G::ok( o_code( static fn () => $ops->$m( 'QED', '', $base ) ) === 'custos-not-agent', "O $op: no account is refused (custos-not-agent)" );
	G::ok( count( $enqueued ) === $before, "O $op: no refusal wrote a ticket or enqueued a job" );
	$a = $ops->$m( 'QED', 'Agent A', $base + [ 'block' => 'b1' ] );
	G::ok( array_keys( $a ) === [ 'ticket', 'state', 'poll_after' ] && is_int( $a['ticket'] ) && $a['state'] === 'QUEUED' && $a['poll_after'] === 30,
		"O $op: the answer is {ticket, state QUEUED, poll_after}", json_encode( $a ) );
	G::ok( count( $enqueued ) === $before + 1 && end( $enqueued ) === $a['ticket'], "O $op: the job is enqueued once, with the ticket's id" );
	$row = $ots->get( $a['ticket'] );
	G::ok( is_array( $row ) && $row['op'] === $op && $row['account'] === 'Agent A' && $row['prefix'] === 'QED' && $row['state'] === 'QUEUED',
		"O $op: the ticket row carries the op's wire word, the account, the prefix, QUEUED" );
	$want = $op === 'PUSH' ? '{"block":"b1","prefix":"QED","records":"[{\"a\":1}]"}' : '{"block":"b1","prefix":"QED"}';
	G::ok( is_array( $row ) && $row['request'] === $want, "O $op: the request is stored as received", (string)( $row['request'] ?? '' ) );
}
G::ok( o_code( static fn () => $ops->push( 'QED', 'Agent A', [] ) ) === 'custos-missing-param', 'O PUSH without records is refused (custos-missing-param)' );
G::ok( o_code( static fn () => $ops->push( 'QED', 'Agent A', [ 'records' => "\xff" ] ) ) === 'custos-shape', 'O PUSH of records not UTF-8 is refused (custos-shape)' );
$at = $ops->push( 'QED', 'Agent A', [ 'records' => str_repeat( 'y', 64 ) ] );
G::ok( $at['state'] === 'QUEUED', 'O PUSH of records exactly at the byte bound is taken' );
$nb = $ops->push( 'QED', 'Agent A', [ 'records' => '{"z": "not parsed: {[" ' ] );
G::ok( ( $ots->get( $nb['ticket'] )['request'] ?? '' ) === '{"prefix":"QED","records":"{\"z\": \"not parsed: {[\" "}',
	'O PUSH of records that is not JSON is taken as received (records is never parsed)' );
G::ok( ( new Ops( $ots, static function ( int $id ): void {
} ) )->push( 'QED', 'Agent A', [ 'records' => str_repeat( 'w', 65 ) ] )['state'] === 'QUEUED',
	'O the default bound is 1,048,576 bytes (' . Ops::MAX_REQUEST_BYTES . ')' );

// POLL, on a store of its own so the claim below takes this ticket
$ots = new FileTicketStore( "$scratch/tickets-poll" );
$ops = new Ops( $ots, static function ( int $id ): void {
}, 30, 64 );
$q = $ops->petition( 'QED', 'Agent A', [] );
$pq = $ops->poll( [ 'ticket' => (string)$q['ticket'] ], 'Agent A' );
G::ok( $pq === [ 'ticket' => $q['ticket'], 'ticket_op' => 'PETITION', 'state' => 'QUEUED', 'poll_after' => 30 ], 'O POLL of a queued ticket: QUEUED and poll_after',
	json_encode( $pq ) );
$ots->claimNext();
$pw = $ops->poll( [ 'ticket' => (string)$q['ticket'] ], 'Agent A' );
G::ok( $pw['state'] === 'IN WORK' && !isset( $pw['answer'] ), 'O POLL of a ticket in work: IN WORK, no answer' );
$ots->answer( $q['ticket'], 'GRANTED lock QED' );
$pd = $ops->poll( [ 'ticket' => (string)$q['ticket'] ], 'Agent A' );
G::ok( $pd === [ 'ticket' => $q['ticket'], 'ticket_op' => 'PETITION', 'state' => 'DONE', 'answer' => 'GRANTED lock QED' ], 'O POLL of a done ticket: DONE and its answer',
	json_encode( $pd ) );
G::ok( o_code( static fn () => $ops->poll( [ 'ticket' => '987654' ], 'Agent A' ) ) === 'custos-no-ticket', 'O POLL of an unknown ticket is refused (custos-no-ticket)' );
G::ok( o_code( static fn () => $ops->poll( [ 'ticket' => (string)$q['ticket'] ], 'Agent B' ) ) === 'custos-ticket-not-yours',
	'O POLL of another account\'s ticket is refused (custos-ticket-not-yours)' );
G::ok( o_code( static fn () => $ops->poll( [ 'ticket' => (string)$q['ticket'] ], '' ) ) === 'custos-ticket-not-yours',
	'O POLL with no account is refused (custos-ticket-not-yours)' );
G::ok( o_code( static fn () => $ops->poll( [ 'ticket' => '01' ], 'Agent A' ) ) === 'custos-no-ticket', 'O POLL of a ticket not in its form is refused (custos-no-ticket)' );
G::ok( o_code( static fn () => $ops->poll( [], 'Agent A' ) ) === 'custos-missing-param', 'O POLL without a ticket is refused (custos-missing-param)' );
G::ok( o_code( static fn () => $ops->poll( [ 'ticket' => (string)$q['ticket'], 'account' => 'Agent A' ], 'Agent A' ) ) === 'custos-account',
	'O POLL with an account parameter is refused (custos-account)' );
G::ok( o_code( static fn () => $ops->poll( [ 'ticket' => (string)$q['ticket'], 'records' => 'x' ], 'Agent A' ) ) === 'custos-unknown-param',
	'O POLL with an unknown parameter is refused (custos-unknown-param)' );
G::ok( o_code( static fn () => $ops->run( 'POLL', 'QED', 'Agent A', [ 'ticket' => (string)$q['ticket'] ] ) ) === 'custos-unknown-param',
	'O POLL with a prefix is refused (custos-unknown-param)' );
G::ok( o_code( static fn () => $ops->run( 'RETURN', 'QED', 'Agent A', [] ) ) === 'custos-op', 'O an op outside the seven is refused (custos-op)' );
G::ok( $ops->run( 'RELEASE', 'QED', 'Agent A', [] )['state'] === 'QUEUED', 'O run dispatches by the wire word' );
G::ok( Refusal::scrub( 'Error: failed in /var/www/w/extensions/Custos/includes/Ops.php on line 42' ) === 'Error: failed in Ops.php',
	'O scrub strips every path and line number from a message', Refusal::scrub( 'Error: failed in /var/www/w/extensions/Custos/includes/Ops.php on line 42' ) );
// The sweep: POLL of the account's own QUEUED ticket at least the sweep age old pushes its job again.
$sPushed = [];
$sts = new FileTicketStore( "$scratch/tickets-sweep" );
$sNow = time();
$sOps = new Ops( $sts, static function ( int $id ) use ( &$sPushed ): void {
	$sPushed[] = $id;
}, 30, 64, 600, static function () use ( &$sNow ): int {
	return $sNow;
} );
$s1 = $sOps->petition( 'QED', 'Agent A', [] )['ticket'];
$sPushed = [];
$sNow += 598;
$sp = $sOps->poll( [ 'ticket' => (string)$s1 ], 'Agent A' );
G::ok( $sPushed === [] && $sp === [ 'ticket' => $s1, 'ticket_op' => 'PETITION', 'state' => 'QUEUED', 'poll_after' => 30 ],
	'O sweep: POLL of a QUEUED ticket younger than the sweep age pushes nothing', json_encode( [ $sPushed, $sp ] ) );
$sNow += 3;
$sp = $sOps->poll( [ 'ticket' => (string)$s1 ], 'Agent A' );
G::ok( $sPushed === [ $s1 ], 'O sweep: POLL of a QUEUED ticket at least the sweep age old pushes its job again, once, with its id', json_encode( $sPushed ) );
G::ok( $sp === [ 'ticket' => $s1, 'ticket_op' => 'PETITION', 'state' => 'QUEUED', 'poll_after' => 30 ], 'O sweep: POLL\'s answer keeps its form', json_encode( $sp ) );
$sPushed = [];
G::ok( o_code( static fn () => $sOps->poll( [ 'ticket' => (string)$s1 ], 'Agent B' ) ) === 'custos-ticket-not-yours' && $sPushed === [],
	'O sweep: another account\'s POLL of the ticket is refused and pushes nothing' );
G::ok( o_code( static fn () => $sOps->poll( [ 'ticket' => (string)$s1 ], '' ) ) === 'custos-ticket-not-yours' && $sPushed === [],
	'O sweep: a POLL with no account pushes nothing' );
$sts->claim( $s1 );
$sp = $sOps->poll( [ 'ticket' => (string)$s1 ], 'Agent A' );
G::ok( $sPushed === [] && $sp['state'] === 'IN WORK', 'O sweep: an IN WORK ticket is never re-pushed', json_encode( [ $sPushed, $sp ] ) );
$sts->answer( $s1, '{"grant":"x"}' );
$sp = $sOps->poll( [ 'ticket' => (string)$s1 ], 'Agent A' );
G::ok( $sPushed === [] && $sp['state'] === 'DONE', 'O sweep: a DONE ticket is never re-pushed', json_encode( [ $sPushed, $sp ] ) );
$s2 = $sOps->push( 'QED', 'Agent A', [ 'records' => '[]' ] )['ticket'];
$sPushed = [];
$sOps0 = new Ops( $sts, static function ( int $id ) use ( &$sPushed ): void {
	$sPushed[] = $id;
}, 30, 64, 0 );
$sOps0->poll( [ 'ticket' => (string)$s2 ], 'Agent A' );
$sOps0->poll( [ 'ticket' => (string)$s2 ], 'Agent A' );
G::ok( $sPushed === [ $s2, $s2 ] && ( $sts->get( $s2 )['state'] ?? '' ) === 'QUEUED',
	'O sweep: with the sweep age 0 every POLL of a QUEUED ticket pushes its job (the queue deduplicates; the claim lands it once), the ticket untouched',
	json_encode( $sPushed ) );
G::ok( Ops::SWEEP_AFTER === 600, 'O sweep: the default sweep age is 600 seconds' );
$s3 = $sOps0->petition( 'QED', 'Agent A', [] )['ticket'];
$sFaults = [];
$sOpsT = new Ops( $sts, static function ( int $id ): void {
	throw new \RuntimeException( 'the job queue is down at /var/www/w/includes/JobQueue.php' );
}, 30, 64, 0, null, static function ( int $id, \Throwable $e ) use ( &$sFaults ): void {
	$sFaults[] = [ $id, get_class( $e ) ];
} );
$sp = $sOpsT->poll( [ 'ticket' => (string)$s3 ], 'Agent A' );
G::ok( $sp === [ 'ticket' => $s3, 'ticket_op' => 'PETITION', 'state' => 'QUEUED', 'poll_after' => 30 ] && $sFaults === [ [ $s3, 'RuntimeException' ] ]
	&& ( $sts->get( $s3 )['state'] ?? '' ) === 'QUEUED',
	'O sweep: a push that throws is caught and given to the error channel; POLL still answers the ticket QUEUED', json_encode( [ $sp, $sFaults ] ) );
$sOps45 = new Ops( $sts, static function ( int $id ): void {
}, 45 );
$w202 = [ $sOps45->petition( 'QED', 'Agent A', [] )['poll_after'], $sOps45->push( 'QED', 'Agent A', [ 'records' => '[]' ] )['poll_after'],
	$sOps45->release( 'QED', 'Agent A', [] )['poll_after'] ];
$opsCode = '';
foreach ( token_get_all( (string)file_get_contents( dirname( __DIR__ ) . '/includes/Ops.php' ) ) as $tok ) {
	if ( !is_array( $tok ) || !in_array( $tok[0], [ T_COMMENT, T_DOC_COMMENT ], true ) ) {
		$opsCode .= is_array( $tok ) ? $tok[1] : $tok;
	}
}
G::ok( $w202 === [ 45, 45, 45 ] && stripos( $opsCode, 'calc' ) === false && stripos( $opsCode, 'jitter' ) === false
	&& stripos( $opsCode, 'random' ) === false,
	'O the 202\'s poll_after is the configured constant (45 here), never jittered: Ops\'s code names no Calculator, jitter or draw', json_encode( $w202 ) );
$jobCode = (string)file_get_contents( dirname( __DIR__ ) . '/includes/LandJob.php' );
G::ok( str_contains( $jobCode, '$this->removeDuplicates = true;' )
	&& preg_match( "/=== 'NOT QUEUED' \\) \\{(?:(?!return)[\\s\\S])*return true;/", $jobCode ) === 1
	&& preg_match( "/=== null \\) \\{\\s*(\\/\\/[^\\n]*\\s*)?wfDebugLog\\( Landing::LOG, \"land job: there is no ticket /", $jobCode ) === 1,
	'O LandJob: the job deduplicated (removeDuplicates), a duplicate whose ticket is not QUEUED ends without error, a job whose ticket does not exist logged one line' );

// Review of the ops' diff: the four findings, each a case.
$long = str_repeat( 'Q', 256 );
$lr = null;
try {
	$ops->petition( $long, 'Agent A', [] );
} catch ( Refusal $e ) {
	$lr = $e;
}
G::ok( $lr !== null && $lr->what === 'custos-prefix' && strpos( $lr->getMessage(), '256 bytes' ) !== false,
	'O a prefix past 255 bytes is refused in GA1 (custos-prefix), the column ct_prefix being VARBINARY(255)', $lr ? $lr->getMessage() : 'none' );
$win = 'failed in C:\\Program Files\\Wiki X\\extensions\\Custos\\includes\\Ops.php on line 7';
$sw = Refusal::scrub( $win, [ 'C:\\Program Files\\Wiki X' ] );
G::ok( $sw === 'failed in Ops.php', 'O scrub strips a known root with a space in it literally, then the path (C:\\Program Files\\...)', $sw );
$own = Refusal::scrub( 'at ' . dirname( __DIR__ ) . '/includes/Ops.php: 9' );
G::ok( $own === 'at Ops.php' && strpos( $own, dirname( __DIR__ ) ) === false, 'O scrub strips Custos\'s own folder as a known root', $own );
$api = '';
foreach ( token_get_all( (string)file_get_contents( dirname( __DIR__ ) . '/includes/ApiPma.php' ) ) as $tok ) {
	if ( !is_array( $tok ) || !in_array( $tok[0], [ T_COMMENT, T_DOC_COMMENT ], true ) ) {
		$api .= is_array( $tok ) ? $tok[1] : $tok;
	}
}
$internal = preg_match( "/dieWithError\\([^;]*'apierror-custos-internal'[^;]*;/s", $api, $im ) === 1 ? $im[0] : '';
G::ok( $internal !== '' && strpos( $internal, 'getMessage' ) === false && strpos( $api, "wfDebugLog( 'Custos'" ) !== false,
	'O ApiPma: custos-internal answers the op and the class name; the exception\'s message goes to the debug log only', $internal );
$rights = strpos( $api, "'custos-not-agent' );" );
$blocked = preg_match( "/if \\( \\\$write && \\\$user->getBlock\\(\\) \\) \\{\\s*\\\$this->dieWithError\\( \\[ 'apierror-custos-blocked', \\\$op \\], 'custos-blocked' \\);/", $api, $bm, PREG_OFFSET_CAPTURE ) === 1;
G::ok( $rights !== false && $blocked && $bm[0][1] > $rights && $bm[0][1] < (int)strpos( $api, 'foreach' ),
	'O ApiPma: a write op by a blocked account is refused (custos-blocked), after the rights check and before any parameter is read' );

// ---- F: what a ticket's refusal may say (Refusal::detail) --------------------------------
// POLL shows a ticket's answer to the ticket's account: every fault answers a fixed word and a detail
// from a closed set. Each fault here is constructed with a path, a file name, a host name and stderr
// text in it, and none of them may reach the answer's raw JSON.

$fLeaks = [ '/srv/wiki/extensions/Custos/includes/Store.php', 'db-host.example', 'stderr: segfault at 0x10' ];
$fMsg = 'SELECT * FROM custos_ticket at ' . $fLeaks[0] . ' on ' . $fLeaks[1] . ': ' . $fLeaks[2];
/** The answer's raw JSON as a ticket stores it: no "/", no ".php", no host name, no stderr text, no query. */
$fClean = static function ( array $answer ) use ( $fLeaks ): bool {
	$raw = json_encode( $answer, JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE );
	foreach ( [ '/', '.php', $fLeaks[1], 'stderr', 'segfault', 'SELECT', 'custos_ticket' ] as $bad ) {
		if ( str_contains( (string)$raw, $bad ) ) {
			return false;
		}
	}
	return true;
};
echo "F: Refusal::detail\n";
$a = Refusal::detail( new DigestMismatch( str_repeat( 'a', 64 ), str_repeat( 'b', 64 ) ) );
G::ok( $a === [ 'refused' => 'INTEGRITY HALT', 'detail' => 'digest mismatch' ], 'F1 INTEGRITY HALT says the words "digest mismatch" alone, no digest', json_encode( $a ) );
$a = Refusal::detail( new UnsafeResidence( $fLeaks[0] . ' ' . $fLeaks[1], 'is writable by group or other ' . $fMsg ) );
G::ok( $a === [ 'refused' => 'CALCULATOR FAULT', 'detail' => 'unsafe residence: mode' ] && $fClean( $a ),
	'F2 an UNSAFE RESIDENCE answers CALCULATOR FAULT and the check that failed by name, never the path', json_encode( $a ) );
// Every property ResidenceCheck words names a check of the closed set; only "cannot be checked" is UNCHECKED.
preg_match_all( "/new UnsafeResidence\\( \\\$\\w+, '([^']+)'/", (string)file_get_contents( "$root/custos/includes/ResidenceCheck.php" ), $fm );
$fChecks = [];
foreach ( $fm[1] as $prop ) {
	$fChecks[$prop] = ( new UnsafeResidence( '/opt/x', $prop ) )->check();
}
G::ok( count( $fChecks ) === 11 && count( array_filter( $fChecks, static fn ( $c ) => $c === UnsafeResidence::UNCHECKED ) ) === 1
	&& $fChecks['is not owned by root'] === UnsafeResidence::OWNER && $fChecks['is writable by group or other'] === UnsafeResidence::MODE
	&& $fChecks['is a symbolic link'] === UnsafeResidence::PATH_CLASS && array_diff( $fChecks, UnsafeResidence::CHECKS ) === [],
	'F3 each of the residence check\'s eleven properties names a check of the closed set (owner, mode, path class, unreadable; unchecked for the unknown user)',
	json_encode( $fChecks ) );
$a = Refusal::detail( new CalculatorFault( $fMsg, CalculatorFault::EXIT_CODE, 'governor', 'admit' ) );
$b = Refusal::detail( new CalculatorFault( $fMsg, 'free text ' . $fMsg, $fLeaks[0], 'not a word' ) );
$c = Refusal::detail( new CalculatorFault( $fMsg ) );
G::ok( $a === [ 'refused' => 'CALCULATOR FAULT', 'detail' => 'exit code: pcalc governor admit' ]
	&& $b === [ 'refused' => 'CALCULATOR FAULT', 'detail' => 'answer form' ] && $c === $b && $fClean( $a ) && $fClean( $b ),
	'F4 CALCULATOR FAULT says its fault from the closed set and the call\'s family and function; a fault or name outside the set is dropped, never echoed',
	json_encode( [ $a, $b ] ) );
$pf = null;
try {
	Blocks::one( "a\0b", 'lock' );
} catch ( PageFault $e ) {
	$pf = $e;
}
$pw = null;
try {
	( new PageWriter( new FileStore( "$scratch/f-pw" ), $pt ) )->read( 'X' );
} catch ( PageFault $e ) {
	$pw = $e;
}
$a = Refusal::detail( new PageFault( $fMsg ), PageClass::INDEX_AND_BADGE );
$b = Refusal::detail( new PageFault( $fMsg ), $fLeaks[0] );
G::ok( $a === [ 'refused' => 'PAGE FAULT', 'detail' => 'INDEX AND BADGE: page store' ] && $b === [ 'refused' => 'PAGE FAULT', 'detail' => 'page store' ]
	&& $pf !== null && Refusal::detail( $pf, PageClass::LOCK_PAGE )['detail'] === 'LOCK PAGE: block form'
	&& $pw !== null && Refusal::detail( $pw )['detail'] === 'landing order' && $fClean( $a ) && $fClean( $b ),
	'F5 PAGE FAULT says the page\'s class and the fault\'s name (by the file that raised it), never a title\'s bytes or a message; a class not a word is dropped',
	json_encode( [ $a, $b, $pf ? Refusal::detail( $pf ) : null ] ) );
$a = Refusal::detail( new RuntimeException( $fMsg ) );
$anonF = new class( $fMsg ) extends RuntimeException {
};
G::ok( $a === [ 'refused' => 'JOB FAULT', 'class' => 'RuntimeException' ] && Refusal::detail( $anonF ) === [ 'refused' => 'JOB FAULT', 'class' => 'RuntimeException@anonymous' ]
	&& $fClean( Refusal::detail( $anonF ) ),
	'F6 any other fault says JOB FAULT and its short class name; an anonymous class\'s name without the file it carries', json_encode( Refusal::detail( $anonF ) ) );
$fWords = [];
foreach ( Refusal::TABLE as [ $cls, $word ] ) {
	$fWords[] = ( class_exists( $cls ) || interface_exists( $cls ) ) ? $word : "missing $cls";
}
G::ok( $fWords === [ 'INTEGRITY HALT', 'CALCULATOR FAULT', 'CALCULATOR FAULT', 'PAGE FAULT', null, 'JOB FAULT' ]
	&& Refusal::detail( new Custos\LandRefused( 'LOCK HELD', 'the lock of RR is held', [ 'poll_after' => 3 ] ) ) === [ 'refused' => 'LOCK HELD', 'detail' => 'the lock of RR is held', 'poll_after' => 3 ],
	'F7 the table names each refusal\'s word, a LandRefused its own word and sentence with the members it adds', json_encode( $fWords ) );
$fApi = (string)file_get_contents( "$root/custos/includes/ApiPma.php" );
G::ok( str_contains( $fApi, "'apierror-custos-internal', \$op, Refusal::faultClass( \$e ) ]" ) && !str_contains( $fApi, 'strrchr' ),
	'F8 ApiPma\'s custos-internal names the short class as a ticket\'s JOB FAULT does: an anonymous class\'s file never reaches the answer' );

// ---- W: the page writer, one landing's saves batched, the badge last (charter 8.3) -------------

/** A FileStore whose casPut of one title first edits that page by hand: the base moves mid-save. */
function w_racing( FileStore $inner, string $raceOn ): PageStore {
	return new class( $inner, $raceOn ) implements PageStore {
		public function __construct( private FileStore $in, private string $race ) {
		}
		public function get( string $t ): ?string {
			return $this->in->get( $t );
		}
		public function exists( string $t ): bool {
			return $this->in->exists( $t );
		}
		public function put( string $t, string $x, string $s ): void {
			$this->in->put( $t, $x, $s );
		}
		public function casPut( string $t, ?string $e, string $x, string $s, string $a ): bool {
			if ( $t === $this->race ) {
				$this->in->tamper( $t, 'edited by hand during the landing' );
			}
			return $this->in->casPut( $t, $e, $x, $s, $a );
		}
		public function appendAs( string $t, string $l, string $s, string $a ): string {
			return $this->in->appendAs( $t, $l, $s, $a );
		}
	};
}
/**
 * A held lock's canonical writer for the tests that are not about it: the members' JSON as the
 * Calculator writes them (keys sorted by PageTexts, no space, slashes and UTF-8 unescaped).
 */
function w_canon(): callable {
	return static fn ( array $m ): string => json_encode( $m, JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_THROW_ON_ERROR );
}
/** The badge of a test landing. */
function w_badge( string $prefix, int $count, bool $retired = false ): string {
	return PageTexts::badge( $prefix, [ 'last_push' => '2026-10-24T05:00:00Z', 'last_release' => null, 'calculator_version' => '0.1.0',
		'calculator_digest' => str_repeat( 'a', 64 ), 'record_count' => $count, 'research_assembly' => str_repeat( 'b', 64 ) ], $retired, 1 );
}

$ws = new FileStore( "$scratch/writer" );
$w = new PageWriter( $ws, $pt );
$tReg = $pt->registerVolume( 'TST', 1 );
$tLock = $pt->lock( 'TST' );
$tIdx = $pt->index( 'TST' );
G::refuses( static fn () => $w->read( $tReg ), PageFault::class, 'no landing is open', 'W1 read before begin is refused' );
G::refuses( static fn () => $w->put( $tReg, 'x' ), PageFault::class, 'no landing is open', 'W2 put before begin is refused' );
G::refuses( static fn () => $w->commit(), PageFault::class, 'no landing is open', 'W3 commit before begin is refused' );
G::refuses( static fn () => $w->begin( 'TST', 'b 1' ), PageFault::class, 'work block', 'W4 begin refuses a block not in its form' );
G::refuses( static fn () => $w->begin( 'T-ST', 'b1' ), PageFault::class, 'record prefix', 'W5 begin refuses a prefix the titles refuse' );
$reg1 = PageTexts::register( 'TST', 1, '[{"ID":"TST-1"}]' );
$lock1 = PageTexts::lock( 'TST', null, null, null, null );
$w->begin( 'TST', 'b1' );
G::ok( $w->read( $tReg ) === null, 'W6 read answers null for a page that does not exist' );
$w->put( $tIdx, w_badge( 'TST', 1 ) );
$w->put( $tReg, 'first text, replaced' );
$w->put( $tLock, $lock1 );
$w->put( $tReg, $reg1 );
G::ok( $w->order() === [ $tReg, $tLock, $tIdx ], 'W7 the order: the pages as first put, the INDEX AND BADGE page last though put first', implode( ' | ', $w->order() ) );
$saved = $w->commit();
G::ok( $saved === [ $tReg, $tLock, $tIdx ], 'W8 commit answers the titles saved, the badge last' );
G::ok( count( $ws->revisions[$tReg] ) === 1 && count( $ws->revisions[$tLock] ) === 1 && count( $ws->revisions[$tIdx] ) === 1,
	'W9 each page saved once: a second put of a title replaced the first, never a second save' );
G::ok( $ws->get( $tReg ) === $reg1 && $ws->get( $tLock ) === $lock1 && $ws->get( $tIdx ) === w_badge( 'TST', 1 ), 'W10 each page holds the text last put' );
G::ok( array_unique( array_merge( array_column( $ws->revisions[$tReg], 'actor' ), array_column( $ws->revisions[$tIdx], 'actor' ) ) ) === [ 'Custos' ],
	'W11 every save is the system user Custos\'s revision' );
G::ok( $ws->revisions[$tReg][0]['summary'] === 'Custos: landing of block b1 on TST' && $ws->revisions[$tIdx][0]['summary'] === 'Custos: landing of block b1 on TST',
	'W12 each save\'s summary is the fixed form naming the landing block and the prefix', $ws->revisions[$tReg][0]['summary'] );
G::refuses( static fn () => $w->read( $tReg ), PageFault::class, 'no landing is open', 'W13 commit closes the landing' );
$w->begin( 'TST', 'b2' );
$w->put( $tReg, $reg1 . 'x' );
G::refuses( static fn () => $w->commit(), PageFault::class, 'INDEX AND BADGE', 'W14 a landing without its badge is refused' );
G::ok( $ws->get( $tReg ) === $reg1 && count( $ws->revisions[$tReg] ) === 1, 'W15 the landing without its badge saved nothing' );
$w->begin( 'TST', 'b3' );
G::ok( $w->read( $tReg ) === $reg1, 'W16 read answers the page\'s text' );
$ws->tamper( $tReg, 'edited by hand' );
G::ok( $w->read( $tReg ) === $reg1, 'W17 read answers the text as this landing first read it, the revision its saves are set against' );
$w->put( $tReg, PageTexts::register( 'TST', 1, '[{"ID":"TST-1"},{"ID":"TST-2"}]' ) );
$w->put( $tLock, PageTexts::lock( 'TST', 'Agent A', '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b3', w_canon() ) );
$w->put( $tIdx, w_badge( 'TST', 2 ) );
G::refuses( static fn () => $w->commit(), PageFault::class, 'BASE MOVED', 'W18 a page whose base moved since it was read refuses the landing (BASE MOVED)' );
G::ok( $ws->get( $tReg ) === 'edited by hand' && $ws->get( $tLock ) === $lock1 && $ws->get( $tIdx ) === w_badge( 'TST', 1 )
	&& count( $ws->revisions[$tLock] ) === 1 && count( $ws->revisions[$tIdx] ) === 1,
	'W19 the moved base saved nothing: no page of the landing, and the badge as it was' );
$ws->tamper( $tReg, $reg1 );
$w->begin( 'TST', 'b4' );
$w->put( $tReg, $reg1 . "\n" );
$w->put( $tIdx, w_badge( 'TST', 9 ) );
$ws->tamper( $tIdx, w_badge( 'TST', 5 ) );
G::refuses( static fn () => $w->commit(), PageFault::class, 'BASE MOVED', 'W20 a badge changed since begin read it refuses the landing (BASE MOVED)' );
G::ok( $ws->get( $tReg ) === $reg1 && count( $ws->revisions[$tReg] ) === 1, 'W21 the moved badge saved nothing' );
$ws->tamper( $tIdx, w_badge( 'TST', 1 ) );
$wr = new PageWriter( w_racing( $ws, $tLock ), $pt );
$wr->begin( 'TST', 'b5' );
$reg2 = PageTexts::register( 'TST', 1, '[{"ID":"TST-1"},{"ID":"TST-2"}]' );
$wr->put( $tReg, $reg2 );
$wr->put( $tLock, PageTexts::lock( 'TST', 'Agent A', '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b5', w_canon() ) );
$wr->put( $tIdx, w_badge( 'TST', 2 ) );
G::refuses( static fn () => $wr->commit(), PageFault::class, 'the badge not written', 'W22 a save that fails after the check (an edit during the landing) stops the landing' );
G::ok( $ws->get( $tReg ) === $reg2 && $ws->get( $tIdx ) === w_badge( 'TST', 1 ) && count( $ws->revisions[$tIdx] ) === 1,
	'W23 the failed save before the badge left no badge: the pages before it saved, the commit marker not written' );
$ws->tamper( $tLock, $lock1 );
$w->begin( 'TST', 'b6' );
$w->put( $tReg, $reg2 );
$w->put( $tLock, $lock1 );
$w->put( $tIdx, w_badge( 'TST', 2 ) );
$before = [ count( $ws->revisions[$tReg] ), count( $ws->revisions[$tLock] ), count( $ws->revisions[$tIdx] ) ];
G::ok( $w->commit() === [ $tReg, $tLock, $tIdx ] && [ count( $ws->revisions[$tReg] ), count( $ws->revisions[$tLock] ), count( $ws->revisions[$tIdx] ) ]
	=== [ $before[0], $before[1], $before[2] + 1 ], 'W24 a page put with the text it holds is not saved again; the changed badge is' );
$w->begin( 'TST', 'b7' );
$w->put( $pt->lock( 'TST' ), $lock1 );
$w->begin( 'TST', 'b8' );
G::ok( $w->order() === [], 'W25 a second begin drops the landing still open, unsaved' );

// The fence: put takes only the pages a landing writes under its own UWC prefix, or beyond it the
// classes begin names; any other title refuses the whole landing before anything is saved.
$wfStore = new FileStore( "$scratch/fence" );
$wf = new PageWriter( $wfStore, $pt );
$wfTitles = [ $pt->draft( 'TST' ), $pt->researchAssembly( 'TST', 'Criteria Set' ), $tReg, $tLock, $tIdx ];
$wf->begin( 'TST', 'f1' );
foreach ( $wfTitles as $t ) {
	$wf->put( $t, Blocks::render( 'draft', '{}' ) . "\n" );
}
$wf->put( $tIdx, w_badge( 'TST', 0 ) );
G::ok( $wf->commit() === [ $wfTitles[0], $wfTitles[1], $tReg, $tLock, $tIdx ],
	'W26 the landing\'s own DRAFT UWC, RESEARCH ASSEMBLY, register volume, LOCK PAGE and INDEX AND BADGE pages admitted and saved', implode( ' | ', $wfTitles ) );
/** Each refused put: the landing refused FENCE with the title and the class it read, closed, nothing saved. */
$wfRefused = static function ( string $title, string $read, string $what ) use ( $wf, $wfStore, $tReg, $tIdx ): void {
	$before = $wfStore->revisions;
	$wf->begin( 'TST', 'f2' );
	$wf->put( $tReg, PageTexts::register( 'TST', 1, '[]' ) . 'changed' );
	$wf->put( $tIdx, w_badge( 'TST', 5 ) );
	$msg = '';
	try {
		$wf->put( $title, 'x' );
	} catch ( PageFault $e ) {
		$msg = $e->getMessage();
	}
	$closed = false;
	try {
		$wf->commit();
	} catch ( PageFault $e ) {
		$closed = str_contains( $e->getMessage(), 'no landing is open' );
	}
	G::ok( str_starts_with( $msg, 'FENCE: ' ) && str_contains( $msg, 'the page ' . PageTitles::show( $title ) . ' (' ) && str_contains( $msg, "(read as $read)" )
		&& $closed && $wfStore->revisions === $before && !$wfStore->exists( $title ),
		"$what: refused FENCE naming the title and the class read ($read), the landing closed, nothing saved", $msg );
};
$wfRefused( $pt->registerVolume( 'OTH', 1 ), 'REGISTER OPEN of the UWC "OTH"', 'W27 put of another UWC\'s register volume' );
$wfRefused( $pt->lock( 'OTH' ), 'LOCK PAGE of the UWC "OTH"', 'W28 put of another UWC\'s LOCK PAGE' );
$wfRefused( $pt->index( 'TST_X' ), 'INDEX AND BADGE of the UWC "TST_X"', 'W29 put of the INDEX AND BADGE page of a UWC whose prefix extends the landing\'s' );
$wfRefused( $pt->uwc( 'TST' ) . '/Nonsense', 'a governed title of no class', 'W30 put of an unclassified governed title under the landing\'s own UWC' );
$wfRefused( 'Main Page', 'a page Custos does not govern', 'W31 put of an ordinary page' );
$wfRefused( $pt->accessList( 'TST' ), 'ACCESS LIST', 'W32 put of a page of the UWC of a class Custos does not write (ACCESS LIST)' );
$wfRefused( $pt->collaboration( 'TST' ), 'COLLABORATION', 'W33 put of the UWC\'s COLLABORATION page' );
$wfRefused( str_replace( 'Volume 1', 'Volume_1', $tReg ), 'REGISTER OPEN, not in canonical form', 'W34 put of the landing\'s register under a title not in canonical form' );
$wfRefused( $pt->fleetIndex(), 'INDEX AND BADGE', 'W35 put of the fleet\'s index by a landing that does not name it' );
$wfRefused( $pt->declarationsHead(), 'CHAIN HEAD', 'W36 put of the Declarer\'s root\'s chain head by a landing that does not name it' );
$wfRefused( $pt->dossier( 'Agent A' ), 'DOSSIER', 'W37 put of a dossier under the Declarer\'s root' );
$wfRefused( 'Restricted:Score/Agent A', 'SCORE OR USER PAGE', 'W38 put of a page in the restricted namespace' );
$wf->begin( 'TST', 'f3', [ PageClass::INDEX_AND_BADGE, PageClass::CHAIN_HEAD, PageClass::DECLARATIONS_VOLUME ] );
$wf->put( $pt->fleetIndex(), 'the fleet' );
$wf->put( $pt->declarationsHead(), 'the head' );
$wf->put( $pt->declarationsVolume( 1 ), 'volume 1' );
$wf->put( $tIdx, w_badge( 'TST', 1 ) );
G::ok( $wf->commit() === [ $pt->fleetIndex(), $pt->declarationsHead(), $pt->declarationsVolume( 1 ), $tIdx ]
	&& $wfStore->get( $pt->fleetIndex() ) === 'the fleet',
	'W39 a landing that names them at begin writes the fleet\'s index and the chain pages, the badge last' );
$wf->begin( 'TST', 'f4', [ PageClass::INDEX_AND_BADGE ] );
G::refuses( static fn () => $wf->put( $pt->buildChainHead(), 'x' ), PageFault::class, 'read as CHAIN HEAD', 'W40 a class beyond the UWC not named at begin stays fenced' );
G::refuses( static fn () => $wf->begin( 'TST', 'f5', [ PageClass::LOCK_PAGE ] ), PageFault::class, 'beyond its UWC', 'W41 begin refuses a class beyond the UWC outside BEYOND' );
$wfE = null;
$wf->begin( 'TST', 'f6' );
try {
	$wf->put( $pt->lock( 'OTH' ), 'x' );
} catch ( PageFault $e ) {
	$wfE = $e;
}
G::ok( $wfE !== null && Refusal::detail( $wfE, PageClass::LOCK_PAGE ) === [ 'refused' => 'PAGE FAULT', 'detail' => 'LOCK PAGE: landing order' ],
	'W42 the fence\'s refusal is a PAGE FAULT of the landing order: its ticket answer carries no title' );

// ---- X: the three page texts of the path, written and read back -------------------------------

$freeLock = PageTexts::lock( 'TST', null, null, null, null );
G::ok( PageTexts::readLock( $freeLock ) === '{"block":null,"expires_at":null,"granted_at":null,"holder":null}', 'X1 a free lock: every member null, keys sorted' );
$held = PageTexts::lock( 'TST', 'Agent A', '2026-10-24T05:00:00Z', '2026-10-24T09:00:00Z', 'b1', w_canon() );
$heldPayload = '{"block":"b1","expires_at":"2026-10-24T09:00:00Z","granted_at":"2026-10-24T05:00:00Z","holder":"Agent A"}';
G::ok( PageTexts::readLock( $held ) === $heldPayload, 'X2 a held lock: holder, granted-at, expires-at, the block identifier', (string)PageTexts::readLock( $held ) );
$xs = new FileStore( "$scratch/texts" );
$xs->put( $tLock, $held, 'x' );
G::ok( $xs->get( $tLock ) === $held && PageTexts::readLock( $xs->get( $tLock ) ) === $heldPayload, 'X3 the lock page written and read back byte for byte' );
$records = "[{\"CLASS\":\"MASTER\",\"ID\":\"TST-1\",\"TEXT\":\"r\u{00E9}gime\"},\n{\"ID\":\"TST-2\"}]";
$regText = PageTexts::register( 'TST', 1, $records );
$xs->put( $tReg, $regText, 'x' );
G::ok( PageTexts::readRegister( $xs->get( $tReg ) ) === $records, 'X4 the register volume\'s records read back byte for byte, lines and UTF-8 kept' );
G::ok( PageTexts::readRegister( PageTexts::register( 'TST', 1, '[]' ) ) === '[]', 'X5 an empty register volume carries []' );
$badgeText = w_badge( 'TST', 7 );
$xs->put( $tIdx, $badgeText, 'x' );
$badgePayload = '{"calculator_digest":"' . str_repeat( 'a', 64 ) . '","calculator_version":"0.1.0","last_push":"2026-10-24T05:00:00Z","last_release":null,"record_count":7,"research_assembly":"' . str_repeat( 'b', 64 ) . '"}';
G::ok( PageTexts::readBadge( $xs->get( $tIdx ) ) === $badgePayload, 'X6 the badge read back byte for byte: last push, last release, the Calculator\'s version and digest, the record count, the Research Assembly\'s digest',
	(string)PageTexts::readBadge( $xs->get( $tIdx ) ) );
G::ok( PageTexts::facts( $badgeText ) === [ 'retired' => false, 'open_volume' => 1 ], 'X7 the badge page states LIVE and the open volume, the facts classify takes' );
G::ok( PageTexts::facts( w_badge( 'TST', 7, true ) ) === [ 'retired' => true, 'open_volume' => 1 ], 'X8 a RETIRED UWC\'s badge page states it' );
G::ok( PageTexts::facts( null ) === [] && PageTexts::facts( 'no blocks' ) === [], 'X9 no badge page states no fact (each takes the reading that refuses)' );
G::ok( PageTexts::facts( Blocks::render( 'state', 'live' ) . "\n" . Blocks::render( 'open', '01' ) ) === [], 'X10 a state other than LIVE or RETIRED, a volume not in its form, state nothing' );
G::ok( PageTexts::facts( $badgeText . Blocks::render( 'state', 'RETIRED' ) ) === [] && PageTexts::facts( '<pre>' . $badgeText ) === [],
	'X11 a badge page with two state blocks, or blocks that do not read, states nothing' );
G::ok( PageTexts::readLock( null ) === null && PageTexts::readRegister( 'plain' ) === null && PageTexts::readBadge( $regText ) === null,
	'X12 a page without the block reads as null' );
$xbad = [
	'X13 a register payload carrying a pre tag' => static fn () => PageTexts::register( 'TST', 1, '[{"T":"<pre>"}]' ),
	'X14 a register payload carrying </pre>' => static fn () => PageTexts::register( 'TST', 1, '[{"T":"</pre>"}]' ),
	'X15 a register payload carrying a comment' => static fn () => PageTexts::register( 'TST', 1, '[{"T":"<!-- x"}]' ),
	'X16 a register payload carrying nowiki' => static fn () => PageTexts::register( 'TST', 1, '[{"T":"<nowiki>"}]' ),
	'X17 volume 0' => static fn () => PageTexts::register( 'TST', 0, '[]' ),
	'X18 a free lock carrying a block' => static fn () => PageTexts::lock( 'TST', null, null, null, 'b1' ),
	'X19 a held lock without its expiry' => static fn () => PageTexts::lock( 'TST', 'Agent A', '2026-10-24T05:00:00Z', null, 'b1' ),
	'X20 a holder with a hash (MediaWiki refuses it in a title)' => static fn () => PageTexts::lock( 'TST', 'Agent#A', '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1', w_canon() ),
	'X21 a holder with a slash (MediaWiki refuses it in an account name)' => static fn () => PageTexts::lock( 'TST', 'Agent/A', '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1', w_canon() ),
	'X22 a holder with an underscore (MediaWiki folds it to a space)' => static fn () => PageTexts::lock( 'TST', 'Agent_A', '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1', w_canon() ),
	'X23 a holder with a leading space' => static fn () => PageTexts::lock( 'TST', ' Agent', '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1', w_canon() ),
	'X24 a holder with a no-break space (MediaWiki folds it to a space)' => static fn () => PageTexts::lock( 'TST', "Agent\u{00A0}A", '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1', w_canon() ),
	'X25 a holder with a control character' => static fn () => PageTexts::lock( 'TST', "Agent\tA", '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1', w_canon() ),
	'X25a a holder not UTF-8' => static fn () => PageTexts::lock( 'TST', "Agent \xC3", '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1', w_canon() ),
	'X25b a holder past 255 bytes' => static fn () => PageTexts::lock( 'TST', str_repeat( "\u{00C9}", 128 ), '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1', w_canon() ),
	'X25c a held lock without its canonical writer' => static fn () => PageTexts::lock( 'TST', 'Agent A', '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1' ),
	'X25d a held lock whose writer answers two lines' => static fn () => PageTexts::lock( 'TST', 'Agent A', '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1',
		static fn ( array $m ): string => "{\n}" ),
	'X25e a held lock whose writer answers no string' => static fn () => PageTexts::lock( 'TST', 'Agent A', '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1',
		static fn ( array $m ): ?string => null ),
	'X26 a grant time not in its form' => static fn () => PageTexts::lock( 'TST', 'Agent A', '2026-10-24 05:00:00', '2026-10-24T06:00:00Z', 'b1' ),
	'X27 an expiry not after the grant' => static fn () => PageTexts::lock( 'TST', 'Agent A', '2026-10-24T06:00:00Z', '2026-10-24T06:00:00Z', 'b1' ),
	'X28 a lock\'s block not in its form' => static fn () => PageTexts::lock( 'TST', 'Agent A', '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b 1' ),
	'X29 a badge missing a member' => static fn () => PageTexts::badge( 'TST', [ 'last_push' => null, 'last_release' => null, 'calculator_version' => '0.1.0',
		'calculator_digest' => str_repeat( 'a', 64 ), 'record_count' => 0 ], false, 1 ),
	'X30 a badge with a member beyond the six' => static fn () => PageTexts::badge( 'TST', [ 'last_push' => null, 'last_release' => null, 'calculator_version' => '0.1.0',
		'calculator_digest' => str_repeat( 'a', 64 ), 'record_count' => 0, 'research_assembly' => str_repeat( 'b', 64 ), 'holder' => 'x' ], false, 1 ),
	'X31 a badge whose digest is not 64 lower-case hexadecimal digits' => static fn () => PageTexts::badge( 'TST', [ 'last_push' => null, 'last_release' => null,
		'calculator_version' => '0.1.0', 'calculator_digest' => str_repeat( 'A', 64 ), 'record_count' => 0, 'research_assembly' => str_repeat( 'b', 64 ) ], false, 1 ),
	'X32 a badge whose record count is a string' => static fn () => PageTexts::badge( 'TST', [ 'last_push' => null, 'last_release' => null,
		'calculator_version' => '0.1.0', 'calculator_digest' => str_repeat( 'a', 64 ), 'record_count' => '0', 'research_assembly' => str_repeat( 'b', 64 ) ], false, 1 ),
	'X33 a badge whose last push is not a time' => static fn () => PageTexts::badge( 'TST', [ 'last_push' => 'yesterday', 'last_release' => null,
		'calculator_version' => '0.1.0', 'calculator_digest' => str_repeat( 'a', 64 ), 'record_count' => 0, 'research_assembly' => str_repeat( 'b', 64 ) ], false, 1 ),
	'X34 a badge whose version carries a quote' => static fn () => PageTexts::badge( 'TST', [ 'last_push' => null, 'last_release' => null,
		'calculator_version' => '0.1"', 'calculator_digest' => str_repeat( 'a', 64 ), 'record_count' => 0, 'research_assembly' => str_repeat( 'b', 64 ) ], false, 1 ),
	'X35 an open volume 0' => static fn () => w_badge_open0(),
	'X36 a page text for a prefix in no form' => static fn () => PageTexts::lock( 'T-ST', null, null, null, null ),
];
function w_badge_open0(): string {
	return PageTexts::badge( 'TST', [ 'last_push' => null, 'last_release' => null, 'calculator_version' => '0.1.0',
		'calculator_digest' => str_repeat( 'a', 64 ), 'record_count' => 0, 'research_assembly' => str_repeat( 'b', 64 ) ], false, 0 );
}
foreach ( $xbad as $what => $fn ) {
	G::refuses( $fn, PageFault::class, '', "$what is refused (PageFault)" );
}
$pageTextsSrc = (string)file_get_contents( "$root/custos/includes/PageTexts.php" ) . (string)file_get_contents( "$root/custos/includes/PageWriter.php" )
	. (string)file_get_contents( "$root/custos/includes/PermissionHook.php" );
G::ok( preg_match( '/json_decode|JSON_OBJECT_AS_ARRAY/', $pageTextsSrc ) === 0, 'X37 the writer, the texts and the hook read no field of a payload (no json_decode)' );
G::ok( preg_match( '/json_encode|json_decode/', (string)file_get_contents( "$root/custos/includes/PageTexts.php" ) ) === 0
	&& preg_match( '/ACCOUNT_REFUSED/', (string)file_get_contents( "$root/custos/includes/PageTexts.php" ) ) === 0,
	'X37a the texts write no JSON of their own (no json_encode): a held lock\'s payload is the Calculator\'s, and the ASCII restriction on its holder is gone' );
/** The holders MediaWiki admits that the lock once refused: a space, an apostrophe, a double quote, a backslash, letters outside ASCII. */
$xNames = [ 'Agent A', "Agent O'Brien", 'Agent "Q"', 'Agent \\ B', "Agent \u{00C9}lodie", "\u{6E2C}\u{8A66} \u{0416}", "Agent O'\"\\ \u{00E9}" ];
$xOk = true;
$xLog = [];
foreach ( $xNames as $name ) {
	$text = PageTexts::lock( 'TST', $name, '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1', w_canon() );
	$xs->put( $tLock, $text, 'x' );
	$back = PageTexts::readLock( $xs->get( $tLock ) );
	$xOk = $xOk && $xs->get( $tLock ) === $text && is_string( $back ) && json_decode( $back, false, 8, JSON_THROW_ON_ERROR )->holder === $name;
	$xLog[] = (string)$back;
}
G::ok( $xOk && PageTexts::isAccount( end( $xNames ) ) && !PageTexts::isAccount( 'Agent_A' ),
	'X39 a holder with a space, an apostrophe, a double quote, a backslash and letters outside ASCII written and read back byte for byte (the stand-in writer)', implode( ' | ', $xLog ) );
$builtX = "$root/.lake/build/bin/pcalc";
if ( is_file( $builtX ) && is_executable( $builtX ) ) {
	$basicX = (string)file_get_contents( "$root/Principia/Basic.lean" );
	$verX = preg_match( '/^def version : String := "([^"]+)"$/m', $basicX, $m ) ? $m[1] : '';
	$cx = new Calculator( $builtX, [ 'version' => $verX, 'digest' => Calculator::digestOf( $builtX ) ], new ProcRunner(), 'cli', new AnyResidence() );
	$canon = true;
	foreach ( [ PageTexts::readLock( $freeLock ), $heldPayload, $badgePayload, PageTexts::readBadge( w_badge( 'TST', 0 ) ) ] as $p ) {
		$r = $cx->call( 'canonical', 'canonical_json', '{"value":' . $p . '}' );
		$canon = $canon && $r['exit'] === 0 && $r['value'] === $p;
	}
	G::ok( $canon, 'X38 the lock and badge objects PHP writes are the Calculator\'s canonical JSON of themselves (the built pcalc)' );
	// The lock as Landing writes it: its members through `canonical canonical_json`, and read back through it.
	$xCalc = static function ( array $m ) use ( $cx ): mixed {
		$r = $cx->call( 'canonical', 'canonical_json', '{"value":' . json_encode( $m, JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_THROW_ON_ERROR ) . '}' );
		return $r['exit'] === 0 ? $r['value'] : null;
	};
	$xOk = true;
	$xLog = [];
	foreach ( $xNames as $name ) {
		$text = PageTexts::lock( 'TST', $name, '2026-10-24T05:00:00Z', '2026-10-24T06:00:00Z', 'b1', $xCalc );
		$xs->put( $tLock, $text, 'x' );
		$payload = (string)PageTexts::readLock( $xs->get( $tLock ) );
		$r = $cx->call( 'canonical', 'canonical_json', '{"value":' . $payload . '}' );
		$xOk = $xOk && $xs->get( $tLock ) === $text && $r['exit'] === 0 && $r['value'] === $payload
			&& json_decode( $r['value'], false, 8, JSON_THROW_ON_ERROR )->holder === $name;
		$xLog[] = $payload;
	}
	G::ok( $xOk, 'X40 each such holder written through the Calculator\'s canonical_json and read back through it byte for byte, the name exact (the built pcalc)',
		implode( ' | ', $xLog ) );
} else {
	G::skip( 'X38 the lock and badge objects are canonical JSON', 'no built pcalc in this clone' );
	G::skip( 'X40 a holder of any spelling through the Calculator', 'no built pcalc in this clone' );
}

// ---- K: the permission hook over the permissions table, and the restricted namespace ---------------

$table = Permits::table();
$ks = new FileStore( "$scratch/hook" );
$kw = new PageWriter( $ks, $pt );
$kw->begin( 'TST', 'seed' );
$kw->put( $pt->registerVolume( 'TST', 1 ), PageTexts::register( 'TST', 1, '[]' ) );
$kw->put( $pt->index( 'TST' ), w_badge( 'TST', 0 ) );
$kw->commit();
$kw->begin( 'OLD', 'seed' );
$kw->put( $pt->index( 'OLD' ), w_badge( 'OLD', 0, true ) );
$kw->commit();
$kread = static fn ( string $t ): ?string => $ks->get( $t );
$roles = PermissionHook::DEFAULT_ROLES;
/** The accounts: name, system user, groups. */
$users = [
	'system' => [ 'Custos', true, [ '*', 'user' ] ],
	'impostor' => [ 'Custos', false, [ '*', 'user', 'autoconfirmed' ] ],
	'other system user' => [ 'Maintenance script', true, [ '*', 'user' ] ],
	'agent' => [ 'Agent A', false, [ '*', 'user', 'pma-agent' ] ],
	'plain' => [ 'Reader', false, [ '*', 'user', 'autoconfirmed' ] ],
	'anonymous' => [ '127.0.0.1', false, [ '*' ] ],
	'declarer' => [ 'Declarer', false, [ '*', 'user', 'pma-declarer' ] ],
	'operator' => [ 'Operator', false, [ '*', 'user', 'pma-operator' ] ],
	'contributor' => [ 'Contributor A', false, [ '*', 'user', 'autoconfirmed', 'pma-contributor' ] ],
	'contributor agent' => [ 'Agent C', false, [ '*', 'user', 'pma-agent', 'pma-contributor' ] ],
];
$k = static fn ( string $title, string $action, string $who, ?array $r = null, array $known = [] ): ?string
	=> PermissionHook::decide( $pt, $title, $action, $users[$who][0], $users[$who][1], $users[$who][2], $r ?? $roles, $kread, $table, $known );
$G = PermissionHook::GOVERNED;
$R = PermissionHook::RESTRICTED;
$writes = [ 'edit', 'create', 'move', 'delete', 'protect', 'upload' ];
$all = static function ( string $title, string $action ) use ( $k, $users ): array {
	$out = [];
	foreach ( array_keys( $users ) as $who ) {
		$out[$who] = $k( $title, $action, $who );
	}
	return $out;
};

// The table as PHP reads it: the file the built pcalc wrote, every case of permissions.json.
G::ok( hash_file( 'sha256', "$root/custos/permits.json" ) . "\n" === file_get_contents( "$root/custos/permits.sha256" ),
	'K custos/permits.json carries the digest custos/permits.sha256 records' );
$kCases = 0;
$kCells = 0;
$kBad = [];
$ctxWords = static function ( array $c ): array {
	$x = $c['context'] ?? [];
	return Permits::words( $x['policy'] ?? null, ( $x['listed'] ?? false ) === true, $x['named'] ?? null,
		( $x['queue_head'] ?? false ) === true, ( $x['reauthenticated'] ?? false ) === true );
};
$opWords = [ 'READ', 'WRITE', 'APPEND', 'PROTECT', 'WRITE THROUGH CUSTOS', 'APPEND THROUGH CUSTOS' ];
foreach ( $vec ?: [] as $c ) {
	$fn = $c['function'] ?? '';
	if ( $fn === 'permits' ) {
		$cells = isset( $c['permitted'] )
			? array_combine( $opWords, array_map( static fn ( $o ) => in_array( $o, $c['permitted'], true ), $opWords ) )
			: [ $c['op'] => $c['expected'] ];
		foreach ( $cells as $op => $want ) {
			$kCells++;
			if ( $table->cell( $c['actor'], $c['class'], $op, $ctxWords( $c ) ) !== $want ) {
				$kBad[] = "{$c['actor']} $op {$c['class']} " . json_encode( $c['context'] ?? [] );
			}
		}
	} elseif ( $fn === 'request' && is_array( $c['request'] ?? null ) ) {
		$kCells++;
		$r = $c['request'];
		if ( $table->cell( $r['actor'], $r['class'], $r['op'], $ctxWords( $r ) ) !== $c['expected'] ) {
			$kBad[] = 'request ' . json_encode( $c['args'] );
		}
	}
	$kCases++;
}
G::ok( $kCases > 0 && $kCases === count( $vec ?: [] ) && $kBad === [], "K the table read in PHP answers every cell of the $kCases cases of vectors/permissions.json as permits does ($kCells cells)",
	implode( '; ', array_slice( $kBad, 0, 8 ) ) );
G::ok( $table->cell( 'DECLARER', 'NO SUCH CLASS', 'READ', [] ) === null && $table->cell( 'DECLARER', 'SPINE', 'READ', [ 'NAMED' ] ) === null
	&& !$table->admits( [ 'NOBODY' ], PageClass::SPINE, 'READ', [ 'policy' => [ null ], 'listed' => [ false ], 'dossier' => [ null ], 'head' => [ false ], 'reauth' => [ false ] ] )
	&& !$table->admits( [ 'PUBLIC' ], PageClass::SPINE, 'READ', [ 'policy' => [], 'listed' => [ false ], 'dossier' => [ null ], 'head' => [ false ], 'reauth' => [ false ] ] ),
	'K a cell the table lacks refuses: an unknown class, a context not in the domain, an unknown asker, a fact with no value' );

// Every case of permissions.json through the hook's mapping: a title of the class, an account of the
// asker, the case's context as the known facts. Where the class has a title form and the context can
// be stated on it, the hook answers the cell; nowhere does it admit a cell the case refuses.
$askerOf = [ 'DECLARER' => [ 'declarer', [] ], 'OPERATOR' => [ 'operator', [] ], 'INITIATOR' => [ 'plain', [ 'initiator' => true ] ],
	'SPONSOR' => [ 'plain', [] ], 'PUBLIC' => [ 'anonymous', [] ], 'HOLDER' => [ 'agent', [ 'lock' => 'HOLDER' ] ],
	'COWORKER' => [ 'agent', [ 'lock' => 'COWORKER' ] ], 'AGENT' => [ 'agent', [ 'lock' => null ] ],
	'CONTRIBUTOR' => [ 'contributor', [] ] ];
$opAction = [ 'READ' => 'read', 'WRITE' => 'edit', 'PROTECT' => 'protect' ];
/** A title of each class Custos has a form for; a callable of the account named, for the classes whose title names one. */
$classTitle = [
	PageClass::RESEARCH_ASSEMBLY => $pt->researchAssembly( 'TST', 'Starting Set' ), PageClass::DRAFT_UWC => $pt->draft( 'TST' ),
	PageClass::ACCESS_LIST => $pt->accessList( 'TST' ), PageClass::SCORE_OR_USER_PAGE => [ $pt, 'score' ],
	PageClass::CONFIGURATION_STRATA => $pt->configurationStrata(), PageClass::COMMUNITY_LEDGER => $pt->communityLedgerVolume( 1 ),
	PageClass::DOSSIER => [ $pt, 'dossier' ], PageClass::DECLARATIONS_VOLUME => $pt->declarationsVolume( 1 ),
	PageClass::BUILD_CHAIN_VOLUME => $pt->buildChainVolume( 1 ), PageClass::CHAIN_HEAD => $pt->declarationsHead(),
	PageClass::TOP_PERFORMER => $pt->topPerformers(), PageClass::FALCON_PAGE => $pt->falconPage( 'F1' ),
	PageClass::FALCON_RESTRICTED => $pt->falconRestricted( 'F1' ), PageClass::PROVISION => $pt->provision( 'SPRING', '1.0.0' ),
	PageClass::INDEX_AND_BADGE => $pt->index( 'TST' ), PageClass::SPINE => $pt->reading( 'TST' ),
	PageClass::REGISTER_OPEN => $pt->registerVolume( 'TST', 1 ), PageClass::REGISTER_FROZEN => $pt->registerVolume( 'TST', 2 ),
	PageClass::BIBLIOGRAPHY_FROZEN => $pt->bibliographyVolume( 'TST', 1 ), PageClass::STAGING => $pt->staging( 'TST' ),
	PageClass::COLLABORATION => $pt->collaboration( 'TST' ), PageClass::LOCK_PAGE => $pt->lock( 'TST' ),
	PageClass::CONTROL_PANEL => $pt->controlPanel( 'TST' ), PageClass::RETIRED_CONTAINER => $pt->lock( 'OLD' ),
];
$kExact = 0;
$kStated = 0;
$kWider = [];
$kDiffer = [];
foreach ( $vec ?: [] as $c ) {
	if ( ( $c['function'] ?? '' ) !== 'permits' || !isset( $askerOf[$c['actor']] ) ) {
		continue;
	}
	[ $who, $known ] = $askerOf[$c['actor']];
	$x = $c['context'] ?? [];
	$form = $classTitle[$c['class']] ?? null;
	$named = isset( $x['named'] );
	$title = is_array( $form ) ? $form[0]->{$form[1]}( $named ? $users[$who][0] : 'Someone Else' ) : $form;
	$ref = $title === null ? null : $pt->classify( $title );
	// The context can be stated on the title: a policy or the access list only on a UWC's page; NAMED only on a title naming an account.
	$stated = $title !== null && ( !$named || is_array( $form ) )
		&& ( ( !isset( $x['policy'] ) && empty( $x['listed'] ) ) || $ref->prefix !== null );
	$known += [ 'policy' => $x['policy'] ?? null, 'listed' => ( $x['listed'] ?? false ) === true, 'head' => ( $x['queue_head'] ?? false ) === true,
		'reauth' => ( $x['reauthenticated'] ?? false ) === true ] + ( $named ? [ 'dossier' => $x['named'] ] : [] );
	$cells = isset( $c['permitted'] ) ? array_combine( array_keys( $opAction ), array_map( static fn ( $o ) => in_array( $o, $c['permitted'], true ), array_keys( $opAction ) ) )
		: ( isset( $opAction[$c['op']] ) ? [ $c['op'] => $c['expected'] ] : [] );
	foreach ( $cells as $op => $want ) {
		$admits = $title !== null && $k( $title, $opAction[$op], $who, null, $known ) === null;
		if ( $admits && !$want ) {
			$kWider[] = "{$c['actor']} $op {$c['class']} " . json_encode( $x );
		}
		if ( $stated ) {
			$kStated++;
			if ( $admits === $want ) {
				$kExact++;
			} else {
				$kDiffer[] = "{$c['actor']} $op {$c['class']} " . json_encode( $x );
			}
		}
	}
}
G::ok( $kWider === [], 'K the hook admits no read, write or protect a case of vectors/permissions.json refuses, its context the known facts',
	implode( '; ', array_slice( $kWider, 0, 8 ) ) );
G::ok( $kStated > 1000 && $kDiffer === [], "K where the class has a title form and the case's context can be stated on it, the hook answers the case's cell ($kExact of $kStated)",
	implode( '; ', array_slice( $kDiffer, 0, 8 ) ) );
echo "hook: $kExact cells of permissions.json answered through the hook's mapping\n";

// The Contributor (group pma-contributor) asks as the Public: its cells in the table are the Public's,
// and the hook's reading of them gives its group nothing more.
$permitsFile = json_decode( (string)file_get_contents( "$root/custos/permits.json" ), true );
$kcCells = 0;
$kcDiffer = [];
foreach ( $permitsFile['cells']['PUBLIC'] ?? [] as $cl => $byOp ) {
	foreach ( $byOp as $op => $words ) {
		foreach ( $permitsFile['contexts'] as $i => $ctx ) {
			$kcCells++;
			if ( $table->cell( 'CONTRIBUTOR', $cl, $op, $ctx ) !== $table->cell( 'PUBLIC', $cl, $op, $ctx ) ) {
				$kcDiffer[] = "$cl $op " . json_encode( $ctx );
			}
		}
	}
}
G::ok( $kcCells === 40 * 6 * 96 && $kcDiffer === [] && count( $permitsFile['cells']['CONTRIBUTOR'] ?? [] ) === 40,
	"K the table's Contributor cells are the Public's, every one ($kcCells cells: 40 classes, 6 operations, 96 contexts)",
	implode( '; ', array_slice( $kcDiffer, 0, 8 ) ) );
$kcActions = [ 'read', 'deletedhistory', 'edit', 'create', 'createpage', 'protect', 'move', 'delete', 'upload' ];
foreach ( $classTitle as $cl => $form ) {
	$title = is_array( $form ) ? $form[0]->{$form[1]}( 'Someone Else' ) : $form;
	$same = [];
	foreach ( $kcActions as $act ) {
		$pub = $k( $title, $act, 'plain' );
		if ( $k( $title, $act, 'contributor' ) !== $pub || $k( $title, $act, 'anonymous' ) !== $pub ) {
			$same[] = $act;
		}
	}
	$edit = $k( $title, 'edit', 'contributor' );
	$read = $k( $title, 'read', 'contributor' );
	G::ok( $same === [] && ( $k( $title, 'edit', 'plain' ) === null || $edit !== null ) && ( $k( $title, 'read', 'plain' ) !== null || $read === null ),
		"K the Contributor on $cl: an edit refused where the Public's is, a read admitted where the Public's is, every action the Public's answer",
		'differs: ' . implode( ', ', $same ) );
}
$ok = true;
$detail = '';
foreach ( $classTitle as $cl => $form ) {
	$title = is_array( $form ) ? $form[0]->{$form[1]}( 'Agent C' ) : $form;
	foreach ( [ 'read', 'edit', 'protect' ] as $act ) {
		foreach ( [ [], [ 'lock' => 'HOLDER', 'policy' => 'OPEN', 'listed' => true ], [ 'lock' => 'COWORKER' ], [ 'lock' => null ] ] as $known ) {
			if ( $k( $title, $act, 'contributor agent', null, $known ) !== PermissionHook::decide( $pt, $title, $act, 'Agent C', false,
				[ '*', 'user', 'pma-agent' ], $roles, $kread, $table, $known ) ) {
				$ok = false;
				$detail = "$cl $act " . json_encode( $known );
			}
		}
	}
}
G::ok( $ok, 'K an agent account in the Contributor\'s group asks as an agent in its lock state only: every answer the same account\'s without the group', $detail );
$noContributor = [ 'declarer' => 'pma-declarer', 'operator' => 'pma-operator', 'agent' => 'pma-agent' ];
$ok = true;
foreach ( $classTitle as $cl => $form ) {
	$title = is_array( $form ) ? $form[0]->{$form[1]}( 'Someone Else' ) : $form;
	foreach ( $kcActions as $act ) {
		$ok = $ok && $k( $title, $act, 'contributor', $noContributor ) === $k( $title, $act, 'contributor' );
	}
}
G::ok( $ok, 'K the Contributor role unset in $wgCustosRoles: the account asks as the Public, every answer unchanged' );

// The agent role unset in $wgCustosRoles (F6): an agent account would ask as the Public; refused.
$noAgent = [ 'declarer' => 'pma-declarer', 'operator' => 'pma-operator' ];
$pub = $pt->lock( 'TST' );
G::ok( $k( $pub, 'read', 'plain' ) === null && $k( $pub, 'read', 'agent', $noAgent ) === $G && $k( $pub, 'read', 'plain', $noAgent ) === $G
	&& $k( $pub, 'read', 'agent', $noAgent + [ 'agent' => '' ] ) === $G && $k( $pt->score( 'Agent A' ), 'read', 'agent', $noAgent ) === $R
	&& $k( $pub, 'edit', 'system', $noAgent ) === $G,
	'K the agent role missing or empty from $wgCustosRoles refuses every request on a governed title (an agent account never asks as the Public)' );

// REAUTHENTICATED only for a session that can set its user (F5): a bot password's or OAuth's, which
// MediaWiki answers SEC_OK by default, is not re-authenticated.
G::ok( PermissionHook::reauthenticated( true, true ) && !PermissionHook::reauthenticated( false, true )
	&& !PermissionHook::reauthenticated( true, false ) && !PermissionHook::reauthenticated( false, false ),
	'K REAUTHENTICATED needs a session that can set its user and SEC_OK: a bot password\'s or OAuth\'s session answered SEC_OK is not' );

// The facts read from no page yet are unknown: admitted only under every value.
$coll = $pt->collaboration( 'TST' );
G::ok( $k( $coll, 'edit', 'agent' ) === $G && $k( $coll, 'edit', 'agent', null, [ 'lock' => 'HOLDER' ] ) === $G
	&& $k( $coll, 'edit', 'agent', null, [ 'lock' => 'HOLDER', 'policy' => 'CLOSED', 'listed' => false ] ) === $G,
	'K an agent\'s edit of a UWC page is refused while its lock state, the policy or the access list is unknown, or under CLOSED off the list' );
G::ok( $k( $pt->score( 'Reader' ), 'read', 'plain' ) === $R && $k( $pt->score( 'Reader' ), 'read', 'plain', null, [ 'dossier' => 'NEITHER' ] ) === $R,
	'K a user\'s read of the score page its title names is refused while DOSSIER READ is unread, and under NEITHER' );
foreach ( [ 'SCORE OR USER PAGE' => $pt->score( 'Agent A' ), 'FALCON RESTRICTED' => $pt->falconRestricted( 'F1' ) ] as $what => $title ) {
	$read = $all( $title, 'read' );
	G::ok( $read['agent'] === $R && $read['plain'] === $R && $read['anonymous'] === $R && $read['system'] === $R && $read['impostor'] === $R,
		"K $what: read refused (custos-restricted-page) to the agent, the plain account, the anonymous one and the system user", json_encode( $read ) );
	G::ok( $read['declarer'] === ( $table->cell( 'DECLARER', $ref = $pt->classify( $title )->class, 'READ', [] ) ? null : $R )
		&& $read['operator'] === ( $table->cell( 'OPERATOR', $ref, 'READ', [] ) ? null : $R ),
		"K $what: the Declarer's and the Operator's reads are the table's cells", json_encode( $read ) );
	G::ok( $k( $title, 'read', 'declarer', [] ) === $R && $k( $title, 'read', 'operator', [ 'declarer' => 'pma-declarer' ] ) === $R
		&& $k( $title, 'read', 'declarer', [ 'declarer' => '' ] ) === $R,
		"K $what: a role missing from \$wgCustosRoles, or empty, admits no one" );
	$ok = true;
	foreach ( $writes as $act ) {
		$a = $all( $title, $act );
		$sys = in_array( $act, [ 'edit', 'create' ], true ) ? null : $G;
		$ok = $ok && $a['system'] === $sys && $a['agent'] === $G && $a['plain'] === $G && $a['impostor'] === $G && $a['other system user'] === $G;
	}
	G::ok( $ok, "K $what: every write-class action refused (custos-governed-page); the system user Custos admitted to edit and create only, refused move, delete, protect, upload" );
}
// The five restricted classes: no Public read, whatever the context.
$ok = true;
foreach ( PageClass::RESTRICTED as $cl ) {
	foreach ( [ [], [ 'OPEN' ], [ 'CLOSED', 'LISTED' ], [ 'QUEUE HEAD', 'REAUTHENTICATED' ] ] as $ctx ) {
		$ok = $ok && $table->cell( 'PUBLIC', $cl, 'READ', $ctx ) === false && $table->cell( 'AGENT', $cl, 'READ', $ctx ) === false;
	}
}
G::ok( $ok && count( PageClass::RESTRICTED ) === 5, 'K the five restricted classes: the table refuses the Public\'s and an agent\'s read in every context tried' );

// Writes and actions with no operation.
$ok = true;
$detail = '';
foreach ( [ $pt->registerVolume( 'TST', 1 ), $pt->lock( 'TST' ), $pt->index( 'TST' ), $pt->declarationsVolume( 1 ), $pt->lock( 'OLD' ) ] as $title ) {
	foreach ( [ 'move', 'delete', 'upload', 'import', 'mergehistory' ] as $act ) {
		foreach ( $all( $title, $act ) as $who => $ans ) {
			if ( $ans !== $G ) {
				$ok = false;
				$detail = "$title $act $who";
			}
		}
	}
}
G::ok( $ok, 'K a write-class action the table names no operation for (move, delete, upload, import, mergehistory) is refused to every account, the system user Custos included', $detail );
$ok = true;
foreach ( [ $pt->registerVolume( 'TST', 1 ), $pt->lock( 'TST' ), $pt->index( 'TST' ), $pt->declarationsVolume( 1 ) ] as $title ) {
	foreach ( [ 'edit', 'create', 'createpage', 'createtalk' ] as $act ) {
		$ok = $ok && $k( $title, $act, 'system' ) === null && $k( $title, $act, 'impostor' ) === $G && $k( $title, $act, 'other system user' ) === $G;
	}
	$ok = $ok && $k( $title, 'protect', 'system' ) === $G;
}
G::ok( $ok, 'K the system user Custos is admitted WRITE\'s actions (edit, create, createpage, createtalk) and refused protect; an impostor and another system user are refused' );
$ok = true;
foreach ( [ 'REGISTER OPEN' => $pt->registerVolume( 'TST', 1 ), 'LOCK PAGE' => $pt->lock( 'TST' ), 'DECLARATIONS VOLUME' => $pt->declarationsVolume( 1 ) ] as $cl => $title ) {
	foreach ( [ 'plain', 'anonymous', 'agent', 'declarer', 'operator' ] as $who ) {
		$want = $table->cell( 'PUBLIC', $cl, 'READ', [] ) || ( $who === 'declarer' && $table->cell( 'DECLARER', $cl, 'READ', [] ) );
		$ok = $ok && ( $k( $title, 'read', $who ) === null ) === $want && ( $k( $title, 'deletedhistory', $who ) === null ) === $want;
	}
}
G::ok( $ok, 'K a read (and a reviewed view right, deletedhistory among them) of a public class is the table\'s READ' );
$ok = true;
$detail = '';
foreach ( [ 'REGISTER OPEN' => $pt->registerVolume( 'TST', 1 ), 'LOCK PAGE' => $pt->lock( 'TST' ), 'DECLARATIONS VOLUME' => $pt->declarationsVolume( 1 ) ] as $cl => $title ) {
	foreach ( [ 'patrol', 'autopatrol', 'delete-redirect', 'move-subpages', 'pagelang', 'bigdelete', 'stashedit', 'changetags', 'linkpurge', 'custos-landing', 'history', 'some-extension-right' ] as $act ) {
		foreach ( [ 'plain', 'anonymous', 'agent', 'declarer', 'operator' ] as $who ) {
			if ( $k( $title, $act, $who ) !== $G ) {
				$ok = false;
				$detail = "$cl $act $who";
			}
		}
	}
}
G::ok( $ok && $table->cell( 'PUBLIC', PageClass::LOCK_PAGE, 'READ', [] ),
	'K a right not in the map (patrol, autopatrol, delete-redirect, move-subpages, pagelang, bigdelete, stashedit, changetags, linkpurge, an extension\'s) is refused (custos-governed-page) on a page the Public reads', $detail );
G::ok( $k( $pt->registerVolume( 'TST', 1 ), 'edit', 'plain' ) === $G && $k( $pt->registerVolume( 'TST', 1 ), 'edit', 'declarer' ) === $G,
	'K the register is edited by no account but the landing job (custos-governed-page)' );

$unclassified = [
	'a page in the restricted namespace in no form' => 'Restricted:Canary/F1',
	'a restricted page spelt with a space before the colon, in no form' => 'Restricted : Notes',
	'a page under the UWC root in no form' => 'Principia Machina/UWC/TST/Notes',
	'the UWC root itself' => 'Principia Machina/UWC',
	'a register volume not in its form' => 'Principia Machina/UWC/TST/Register/Volume 01',
	'a page of a UWC with no badge page' => $pt->lock( 'NEW' ),
	'a declarations volume not in its form' => 'Principia Machina/Declarations/Volume one',
	'a title MediaWiki cuts at #' => 'Principia Machina/UWC/TST/Lock#x',
	'a title written with a character reference' => 'Principia Machina/UWC/TST/&#76;ock',
];
foreach ( $unclassified as $what => $title ) {
	$ok = true;
	$detail = '';
	foreach ( array_merge( $writes, [ 'read', 'history' ] ) as $act ) {
		foreach ( $all( $title, $act ) as $who => $ans ) {
			if ( $ans === null ) {
				$ok = false;
				$detail = "$act by $who admitted";
			}
		}
	}
	G::ok( $ok, "K $what: refused for every action and every account, the system user, the Declarer and the Operator included", $detail );
}
G::ok( $k( 'Restricted:Canary/F1', 'read', 'declarer' ) === $R && $k( 'Restricted:Canary/F1', 'edit', 'declarer' ) === $R
	&& $k( 'Principia Machina/UWC/TST/Notes', 'read', 'plain' ) === $G,
	'K an unclassifiable title is refused custos-restricted-page in the restricted namespace, custos-governed-page elsewhere' );
G::ok( $k( 'principia_Machina/UWC/TST/Lock', 'edit', 'agent' ) === $G && $k( 'restricted:Score/Agent A', 'read', 'plain' ) === $R
	&& $k( ':Principia Machina/UWC/TST/Lock', 'edit', 'plain' ) === $G,
	'K a governed title spelt as MediaWiki also reads it (case of the first letter, underscores, a leading colon) is fenced the same' );
$ungoverned = [ 'Main Page', 'Principia Machina', 'Principia Machina/About', 'Talk:Principia Machina/UWC/TST/Lock', 'User:Agent A' ];
$ok = true;
foreach ( $ungoverned as $title ) {
	foreach ( array_merge( $writes, [ 'read' ] ) as $act ) {
		foreach ( $all( $title, $act ) as $ans ) {
			$ok = $ok && $ans === null;
		}
	}
}
G::ok( $ok, 'K every title Custos does not govern is untouched, for every action and account (' . implode( ', ', $ungoverned ) . ')' );

// The namespace: registered under the number the configuration defaults to; titles read through it.
$ext = json_decode( (string)file_get_contents( "$root/custos/extension.json" ), true );
$nsList = $ext['namespaces'] ?? [];
$num = $ext['config']['CustosRestrictedNamespace']['value'] ?? null;
G::ok( $num === PageTitles::RESTRICTED_NUMBER && $num % 2 === 0 && count( $nsList ) === 1
	&& $nsList[0]['id'] === $num && $nsList[0]['name'] === PageTitles::RESTRICTED_NAMESPACE,
	"K extension.json registers Restricted: under $num, the number \$wgCustosRestrictedNamespace defaults to, and no talk namespace" );
G::ok( PermissionHook::titleText( $num, 'Score/Agent A', 'Restricted:Score/Agent A', $num ) === 'Restricted:Score/Agent A'
	&& PermissionHook::titleText( $num + 1, 'Score/Agent A', ':Score/Agent A', $num ) === null
	&& PermissionHook::titleText( 0, 'Restricted:Score/Agent A', 'Restricted:Score/Agent A', $num ) === 'Restricted:Score/Agent A'
	&& PermissionHook::titleText( 0, 'Main Page', 'Main Page', $num ) === 'Main Page',
	'K the hook reads a title in the restricted namespace through the registered number, refuses the unregistered next number, and reads every other title as MediaWiki gives it' );
G::ok( PermissionHook::op( 'edit' ) === 'WRITE' && PermissionHook::op( 'protect' ) === 'PROTECT' && PermissionHook::op( 'read' ) === 'READ'
	&& PermissionHook::op( 'deletedhistory' ) === 'READ' && PermissionHook::op( 'deletedtext' ) === 'READ'
	&& PermissionHook::op( 'delete' ) === null && PermissionHook::op( 'move' ) === null && PermissionHook::op( 'patrol' ) === null
	&& PermissionHook::op( 'pagelang' ) === null && PermissionHook::op( 'history' ) === null && PermissionHook::op( 'some-extension-right' ) === null,
	'K the actions\' operations, an allow-list: edit WRITE, protect PROTECT, read and the reviewed view rights READ, every other action none' );

// The role groups' rows: pma-declarer and pma-operator exist on an installed wiki by a
// row each granting only the marker custos-role, which nothing checks. The hook is built from
// MainConfig and UserGroupManager alone and decides on the account's groups, never on a right, so
// the rows (rights of a group, not its members) change none of its decisions; the marker asked as
// an action has no operation and is refused on a governed title like any unmapped right.
$gp = $ext['GroupPermissions'] ?? [];
$marker = 'custos-role';
$rowsOk = ( $gp[$roles['declarer']] ?? null ) === [ $marker => true ] && ( $gp[$roles['operator']] ?? null ) === [ $marker => true ]
	&& in_array( $marker, $ext['AvailableRights'] ?? [], true );
$landing = [];
foreach ( $gp as $group => $rights ) {
	if ( ( $rights['custos-landing'] ?? false ) === true ) {
		$landing[] = $group;
	}
}
$readers = [];
foreach ( array_merge( glob( "$root/custos/includes/*.php" ), glob( "$root/custos/maintenance/*.php" ) ) as $f ) {
	if ( str_contains( (string)file_get_contents( $f ), $marker ) ) {
		$readers[] = basename( $f );
	}
}
$hookSrc = (string)file_get_contents( "$root/custos/includes/PermissionHook.php" );
$hookIn = ( $ext['HookHandlers']['permissions']['services'] ?? null ) === [ 'MainConfig', 'UserGroupManager' ]
	&& !str_contains( $hookSrc, 'isAllowed' ) && !str_contains( $hookSrc, 'GroupPermissions' ) && !str_contains( $hookSrc, 'PermissionManager' )
	&& ( new ReflectionMethod( PermissionHook::class, 'decide' ) )->getNumberOfParameters() === 10;
$markerOk = PermissionHook::op( $marker ) === null;
$detail = '';
foreach ( [ $pt->registerVolume( 'TST', 1 ), $pt->lock( 'TST' ), 'Restricted:Score/Agent A' ] as $title ) {
	foreach ( array_keys( $users ) as $who ) {
		if ( $k( $title, $marker, $who ) === null ) {
			$markerOk = false;
			$detail = "$title $marker $who admitted";
		}
	}
}
G::ok( $rowsOk && $landing === [ $roles['agent'] ] && $readers === [] && $hookIn && $markerOk,
	'K extension.json gives pma-declarer and pma-operator a row each granting only the marker custos-role, which no file of includes/ or maintenance/ names; '
	. 'custos-landing is pma-agent\'s alone; the hook takes no right (MainConfig and UserGroupManager), so the rows change none of its decisions; the marker as an action is refused on a governed title',
	json_encode( [ $rowsOk, $landing, $readers, $hookIn, $detail ] ) );

// ---- L: the landing job over FileStore, FileTicketStore, FileSeatStore and the built pcalc ---------

$lBuilt = "$root/.lake/build/bin/pcalc";
if ( !is_file( $lBuilt ) || !is_executable( $lBuilt ) ) {
	G::skip( 'L the landing job', 'no built pcalc in this clone (.lake/build/bin/pcalc); section L needs the Calculator itself' );
} else {
	echo "L: on .lake/build/bin/pcalc\n";
	$lBasic = (string)file_get_contents( "$root/Principia/Basic.lean" );
	$lVersion = preg_match( '/^def version : String := "([^"]+)"$/m', $lBasic, $m ) ? $m[1] : '';
	$lDigest = Calculator::digestOf( $lBuilt );
	$lCalc = new Calculator( $lBuilt, [ 'version' => $lVersion, 'digest' => $lDigest ], new ProcRunner(), 'cli', new AnyResidence() );
	$lDraft = (string)file_get_contents( "$root/docs/v1/tpx/TPX/examples/spring_draft.json" );
	$lPx = 'RR';

	/** A PageStore that logs the order of every save, over FileStore. */
	$lInner = new FileStore( "$scratch/land" );
	$lStore = new class( $lInner ) implements PageStore {
		public array $saves = [];
		public function __construct( public FileStore $inner ) {
		}
		public function get( string $title ): ?string {
			return $this->inner->get( $title );
		}
		public function exists( string $title ): bool {
			return $this->inner->exists( $title );
		}
		public function put( string $title, string $text, string $summary ): void {
			$this->saves[] = $title;
			$this->inner->put( $title, $text, $summary );
		}
		public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
			if ( $this->inner->get( $title ) !== $text ) {
				$this->saves[] = $title;
			}
			return $this->inner->casPut( $title, $expected, $text, $summary, $actor );
		}
		public function appendAs( string $title, string $line, string $summary, string $actor ): string {
			$this->saves[] = $title;
			return $this->inner->appendAs( $title, $line, $summary, $actor );
		}
	};

	// The seed, as Custos:SeedUwc writes it.
	$lCanon = $lCalc->call( 'canonical', 'canonical_json', '{"value":' . $lDraft . '}' )['value'];
	$lRaDigest = $lCalc->call( 'zone', 'digest_research_assembly_of', '{"tfk":' . $lDraft . '}' )['value'];
	$seed = new PageWriter( $lStore, $pt );
	$seed->begin( $lPx, 'seed' );
	$seed->put( $pt->draft( $lPx ), Blocks::render( 'draft', $lCanon ) . "\n" );
	foreach ( PageTitles::ZONES as $zone ) {
		$seed->put( $pt->researchAssembly( $lPx, $zone ), Blocks::render( 'assembly', $lCanon ) . "\n" );
	}
	$seed->put( $pt->registerVolume( $lPx, 1 ), PageTexts::register( $lPx, 1, '[]' ) );
	$seed->put( $pt->lock( $lPx ), PageTexts::lock( $lPx, null, null, null, null ) );
	$seed->put( $pt->index( $lPx ), PageTexts::badge( $lPx, [ 'last_push' => null, 'last_release' => null,
		'calculator_version' => $lVersion, 'calculator_digest' => $lDigest, 'record_count' => 0, 'research_assembly' => $lRaDigest ], false, 1 ) );
	$seed->commit();
	G::ok( is_string( $lRaDigest ) && preg_match( '/\A[0-9a-f]{64}\z/', $lRaDigest ) === 1, 'L1 the spring UWC seeded, its Research Assembly digested by the Calculator', (string)$lRaDigest );

	$lNow = 1793000000;
	$lTickets = new FileTicketStore( "$scratch/land-tickets" );
	$lSeats = new FileSeatStore( "$scratch/land-seats.json" );
	// The certificates: each agent of this section bound to a Sponsor of its own, 'Agent X' to 'Sponsor X',
	// so each Sponsor's bucket and slots are its one agent's; the cases LC below bind two agents to one Sponsor.
	$lCerts = new FileCertificateStore( "$scratch/land-certs.json" );
	$lCertify = static function ( string $agent, string $sponsor, string $state = CertificateStore::ACTIVE ) use ( $lCerts ): void {
		$lCerts->put( [ 'agent' => $agent, 'sponsor' => $sponsor, 'd_is' => str_repeat( 'd', 64 ), 'd_prompt' => str_repeat( 'e', 64 ),
			'family' => 'test family', 'model' => 'test model', 'state' => $state ] );
	};
	$lSponsorOf = static fn ( string $agent ): string => 'Sponsor ' . substr( $agent, strlen( 'Agent ' ) );
	foreach ( array_merge( range( 'A', 'Z' ), [ 'Zz' ], array_map( static fn ( int $n ): string => "N$n", range( 0, 5 ) ) ) as $k ) {
		$lCertify( "Agent $k", "Sponsor $k" );
	}
	$lNonces = new FileNonceStore( "$scratch/land-nonces.json" );
	$lConf = [ 'tps' => '0.4.0', 'd_is' => str_repeat( 'd', 64 ), 'digest' => $lDigest, 'poll_after' => 30 ];
	$lMeter = new MemMeterStore();
	$lLanding = new Landing( $lCalc, $lStore, $pt, $lTickets, $lSeats, $lCerts, $lConf, static function () use ( &$lNow ): int {
		return $lNow;
	}, static fn (): array => [ 0, 1 ], nonces: $lNonces, meter: $lMeter );
	$lOps = new Ops( $lTickets, static function ( int $id ): void {
	} );
	// A ticket as the op writes it, the parameters as given ($lRaw); $lTicket answers a PUSH's challenge as an agent
	// does, through the Calculator (Challenge::response) over the outstanding nonce, unless the PUSH names its own.
	$lRaw = static function ( string $op, string $account, array $params ) use ( $lOps, $lPx ): int {
		return $lOps->run( $op, $lPx, $account, $params )['ticket'];
	};
	$lTicket = static function ( string $op, string $account, array $params ) use ( $lRaw, $lNonces, $lCalc, $lPx ): int {
		$nonce = $lNonces->peek( $account, $lPx );
		if ( $op === 'PUSH' && !array_key_exists( 'challenge_response', $params ) && $nonce !== null ) {
			$params['challenge_response'] = Challenge::response( $lCalc, $nonce )[1];
		}
		return $lRaw( $op, $account, $params );
	};
	$lAnswer = static fn ( int $id ): array => (array)json_decode( (string)( $lTickets->get( $id )['answer'] ?? '' ), true );
	$tLk = $pt->lock( $lPx );
	$tRg = $pt->registerVolume( $lPx, 1 );
	$tIx = $pt->index( $lPx );
	$lLock = static fn (): array => (array)json_decode( (string)PageTexts::readLock( $lInner->get( $tLk ) ), true );
	$lBadge = static fn (): array => (array)json_decode( (string)PageTexts::readBadge( $lInner->get( $tIx ) ), true );
	$lRegister = static fn (): array => (array)json_decode( (string)PageTexts::readRegister( $lInner->get( $tRg ) ), true );
	$lSnap = static function () use ( $lInner ): array {
		$o = [];
		foreach ( $lInner->titles() as $t ) {
			$o[$t] = $lInner->get( $t );
		}
		return $o;
	};

	// PETITION
	$p1 = $lTicket( 'PETITION', 'Agent A', [ 'block' => 'b1' ] );
	$a = $lLanding->run( $p1 );
	G::ok( ( $a['grant'] ?? '' ) === '2026-10-26T07:33:20Z' && ( $a['expires'] ?? '' ) === '2026-10-26T08:33:20Z' && ( $a['block'] ?? '' ) === 'b1',
		'L2 a PETITION on a free lock is granted: the grant, the expiry one lease later, the block', json_encode( $a ) );
	G::ok( $lAnswer( $p1 ) === $a && ( $lTickets->get( $p1 )['state'] ?? '' ) === TicketStore::DONE, 'L3 the grant is the ticket\'s answer, the ticket DONE' );
	G::ok( ( $lLock()['holder'] ?? '' ) === 'Agent A' && ( $lLock()['block'] ?? '' ) === 'b1', 'L4 the lock page names the holder and the block' );
	G::ok( $lSeats->get( 'Agent A', 'agent' ) !== [ 0, 0 ] && $lSeats->get( 'Sponsor A', 'sponsor' ) !== [ 0, 0 ],
		'L5 the admission\'s charge is written to the seat table, the agent\'s and the sponsor\'s buckets', json_encode( [ $lSeats->get( 'Agent A', 'agent' ), $lSeats->get( 'Sponsor A', 'sponsor' ) ] ) );
	$charged = $lSeats->get( 'Agent A', 'agent' );
	G::ok( $charged[1] === $lNow, 'L6 the bucket\'s time is the admission\'s now', json_encode( $charged ) );
	G::ok( $lLanding->run( $p1 )['refused'] === 'NOT QUEUED' && $lAnswer( $p1 ) === $a, 'L7 a ticket already DONE is not run again; its answer stands' );

	$before = $lSnap();
	$p2 = $lTicket( 'PETITION', 'Agent B', [ 'block' => 'b2' ] );
	$a = $lLanding->run( $p2 );
	G::ok( ( $a['refused'] ?? '' ) === 'LOCK HELD' && ( $a['poll_after'] ?? 0 ) === 30, 'L8 a second account\'s PETITION is refused LOCK HELD, with when to poll', json_encode( $a ) );
	G::ok( $lSnap() === $before, 'L9 the refused PETITION writes no page' );

	// PUSH refusals
	$result = '{"ASSUMPTIONS":[],"CITES":[],"CLASS":"RESULT","DERIVATION":{"STEPS":2,"TEXT":"The force law and the definition of v."},'
		. '"EQUATION":"m * D(v, t) = -k_s * x","FALSIFIER":"A trajectory off the law.","FALSIFIER_CLASS":"F2","ID":"RR-1",'
		. '"REFS":["m","v","t","k_s","x"],"REGIME":"L","STATEMENT":"The equation of motion on the spring axis."}';
	$assumption = '{"ASSUMPTIONS":[],"CITES":[],"CLASS":"ASSUMPTION","ID":"RR-2","PROPOSITION":"The mass is constant.","REFS":["m"]}';
	$records = "[$result,$assumption]";
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent B', [ 'records' => $records, 'block' => 'b2' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'NOT HOLDER', 'L10 a PUSH by an account that does not hold the lock is refused NOT HOLDER', json_encode( $a ) );
	G::ok( $lSnap() === $before, 'L11 the refused PUSH writes no page' );

	$bad = str_replace( '"STATEMENT":"The equation of motion on the spring axis."', '"STATEMENT":""', $result );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$bad,$assumption]", 'block' => 'b1' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['index'] ?? -1 ) === 0
		&& ( $a['problems'][0]['answer'][0] ?? '' ) === 'REFUSED', 'L12 a PUSH with a record record_check refuses is refused RECORD CHECK, the record\'s problems answered', json_encode( $a ) );
	G::ok( count( $a['problems'] ?? [] ) === 1, 'L13 only the refused record carries problems' );
	$lTr = $lMeter->traffic( 'Agent A' );
	G::ok( $lTr !== null && str_contains( $lTr['record'], '"streak":1' ) && $lTr['stage'] === 'NORMAL',
		'L98 a PUSH admitted and then refused RECORD CHECK is stepped FAILED at the job\'s end: its streak counted (it was 0 after the PETITION)', json_encode( $lTr ) );
	G::ok( $lSnap() === $before && $lRegister() === [], 'L14 nothing is landed: all or nothing, the good record not landed either' );

	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => '[{"CLASS":"RESULT",', 'block' => 'b1' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'NOT READ' && in_array( $a['calculator']['refused'] ?? '', [ 'UNEXPECTED_END', 'UNEXPECTED_CHARACTER' ], true ), 'L15 records that are not JSON are refused by the Calculator\'s reader, NOT READ', json_encode( $a ) );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => '[],"x":1', 'block' => 'b1' ] );
	G::ok( ( $lLanding->run( $q )['refused'] ?? '' ) === 'NOT READ', 'L16 records that would add a member to the Calculator\'s request are refused, NOT READ' );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => '[]', 'block' => 'b1' ] );
	G::ok( ( $lLanding->run( $q )['refused'] ?? '' ) === 'RECORDS', 'L17 an empty batch is refused' );
	$corr = '{"ASSUMPTIONS":[],"CITES":[],"CLASS":"CORROBORATION","ID":"RR-20","TARGET":"RR-1"}';
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$corr]", 'block' => 'b1' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['answer'][1][0][0] ?? '' ) === 'LANDS', 'L18 a class this unit does not land (CORROBORATION) is refused, named', json_encode( $a ) );
	G::ok( $lSnap() === $before, 'L19 the refused PUSHes write no page' );

	// The digest gate: a tampered Research Assembly page.
	$ra0 = $pt->researchAssembly( $lPx, PageTitles::ZONES[0] );
	$raText = (string)$lInner->get( $ra0 );
	$lInner->tamper( $ra0, str_replace( '"S_MAX":10', '"S_MAX":11', $raText ) );
	G::ok( $lInner->get( $ra0 ) !== $raText, 'L20 a Research Assembly page edited by hand (the test\'s tamper)' );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => $records, 'block' => 'b1' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'DIGEST GATE', 'L21 a Research Assembly page that differs from the others refuses the PUSH, DIGEST GATE', json_encode( $a ) );
	foreach ( PageTitles::ZONES as $zone ) {
		$lInner->tamper( $pt->researchAssembly( $lPx, $zone ), str_replace( '"S_MAX":10', '"S_MAX":11', $raText ) );
	}
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => $records, 'block' => 'b1' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'DIGEST GATE' && str_contains( (string)( $a['detail'] ?? '' ), $lRaDigest ),
		'L22 a Research Assembly whose digest is not the badge\'s refuses the PUSH, DIGEST GATE, both digests named', json_encode( $a ) );
	G::ok( $lSnap() === $before, 'L23 the DIGEST GATE writes nothing' );
	foreach ( PageTitles::ZONES as $zone ) {
		$lInner->tamper( $pt->researchAssembly( $lPx, $zone ), $raText );
	}

	// The records' prefix is the UWC's: a first PUSH to the seeded, empty UWC under another prefix lands nothing.
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => str_replace( [ 'RR-1', 'RR-2' ], [ 'ZZ-1', 'ZZ-2' ], $records ), 'block' => 'b1' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['answer'][1][0][0] ?? '' ) === 'SEQUENCE'
		&& str_contains( (string)( $a['detail'] ?? '' ), 'RR-1' ) && $lSnap() === $before && $lRegister() === [],
		'L135 a first PUSH to a seeded UWC under a foreign prefix (ZZ-1 to the UWC RR) is refused SEQUENCE, the UWC\'s RR-1 named, nothing written', json_encode( $a ) );

	// The landing.
	$lStore->saves = [];
	$regRevs = count( $lInner->revisions[$tRg] ?? [] );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => $records, 'block' => 'b1' ] );
	$a = $lLanding->run( $q );
	G::ok( isset( $a['landed'] ) && array_column( $a['landed'], 'id' ) === [ 'RR-1', 'RR-2' ], 'L24 the PUSH of the spring UWC\'s first RESULT and ASSUMPTION lands both, in order', json_encode( $a ) );
	G::ok( ( $a['block'] ?? '' ) === 'b1' && ( $a['record_count'] ?? 0 ) === 2, 'L25 the answer names the block and the register\'s count' );
	G::ok( ( $a['landed'][0]['derivation_class'] ?? '' ) === 'INSPECTION' && array_key_exists( 'derivation_class', $a['landed'][1] ?? [] )
		&& $a['landed'][1]['derivation_class'] === null, 'L26 DERIVATION_CLASS INSPECTION for the prose derivation (credit_record), none for the ASSUMPTION' );
	$reg = $lRegister();
	G::ok( count( $reg ) === 2 && ( $reg[0]['ID'] ?? '' ) === 'RR-1' && ( $reg[1]['ID'] ?? '' ) === 'RR-2', 'L27 the register volume\'s block holds the two records', json_encode( $reg ) );
	G::ok( ( $reg[0]['DIGEST'] ?? '' ) === ( $a['landed'][0]['digest'] ?? 'x' ) && ( $reg[1]['DIGEST'] ?? '' ) === ( $a['landed'][1]['digest'] ?? 'x' ),
		'L28 each landed record carries its digest, the one answered' );
	G::ok( ( $reg[0]['LANDED_BY'] ?? '' ) === 'Custos' && ( $reg[0]['AUTHOR'] ?? '' ) === 'Agent A' && ( $reg[0]['BLOCK'] ?? '' ) === 'b1'
		&& ( $reg[0]['LANDED'] ?? '' ) === '2026-10-26T07:33:20Z', 'L29 the fields Custos owns: LANDED_BY Custos, AUTHOR the holder, BLOCK, LANDED' );
	G::ok( ( $reg[0]['GRADE'] ?? '' ) === 'PROVISIONAL' && ( $reg[0]['STATUS'] ?? '' ) === 'UNMARKED' && ( $reg[1]['GRADE'] ?? '' ) === 'PROVISIONAL',
		'L30 GRADE and STATUS the record table\'s initial values' );
	G::ok( ( $reg[0]['TPS'] ?? '' ) === '0.4.0' && ( $reg[0]['D_IS'] ?? '' ) === str_repeat( 'd', 64 ), 'L31 TPS and D_IS from configuration' );
	$ok = true;
	foreach ( $reg as $r ) {
		$c = $lCalc->call( 'record', 'record_check', json_encode( [ 'record' => $r, 'tfk' => json_decode( $lDraft ), 'setting' => 'OFF', 'stage' => 'LANDED' ] ) );
		$ok = $ok && ( $c['value'] ?? null ) === [ 'OK' ];
	}
	G::ok( $ok, 'L32 each landed record passes record_check at stage LANDED, its DIGEST checked by the Calculator' );
	$regText = PageTexts::readRegister( $lInner->get( $tRg ) );
	$canonReg = $lCalc->call( 'canonical', 'canonical_json', '{"value":' . $regText . '}' )['value'] ?? '';
	G::ok( $regText === $canonReg, 'L33 the register\'s text is the Calculator\'s canonical JSON' );
	G::ok( $lStore->saves === [ $tRg, $tIx ], 'L34 one save per page, the INDEX AND BADGE page last', implode( ' | ', $lStore->saves ) );
	G::ok( count( $lInner->revisions[$tRg] ?? [] ) === $regRevs + 1 && end( $lInner->revisions[$tRg] )['actor'] === 'Custos', 'L35 the register\'s one new revision is Custos\'s' );
	$b = $lBadge();
	G::ok( ( $b['record_count'] ?? -1 ) === 2 && ( $b['last_push'] ?? '' ) === '2026-10-26T07:33:20Z' && ( $b['research_assembly'] ?? '' ) === $lRaDigest
		&& ( $b['calculator_digest'] ?? '' ) === $lDigest && ( $b['calculator_version'] ?? '' ) === $lVersion, 'L36 the badge current: the count, the last push, the digests, the version', json_encode( $b ) );
	G::ok( $lAnswer( $q ) === $a, 'L37 the landing\'s answer is the ticket\'s, for POLL' );
	// The PMA row DERIVATION_CLASS, written by the job before the digest.
	G::ok( array_key_exists( 'DERIVATION_CLASS', $reg[0] ) && $reg[0]['DERIVATION_CLASS'] === ( $a['landed'][0]['derivation_class'] ?? 'x' )
		&& $reg[0]['DERIVATION_CLASS'] === 'INSPECTION', 'L76 the landed RESULT carries DERIVATION_CLASS, the class the reply answers (INSPECTION)', json_encode( $reg[0] ) );
	G::ok( !array_key_exists( 'DERIVATION_CLASS', $reg[1] ), 'L77 the landed ASSUMPTION carries no DERIVATION_CLASS', json_encode( $reg[1] ) );
	$lDig = static function ( array $r ) use ( $lCalc ): ?string {
		unset( $r['DIGEST'] );
		$d = $lCalc->call( 'record', 'record_digest', json_encode( [ 'record' => $r ] ) )['value'] ?? null;
		return is_array( $d ) && ( $d[0] ?? null ) === 'OK' && is_string( $d[1] ?? null ) ? $d[1] : null;
	};
	$noRow = $reg[0];
	unset( $noRow['DERIVATION_CLASS'] );
	G::ok( $lDig( $reg[0] ) !== null && $lDig( $reg[0] ) === ( $reg[0]['DIGEST'] ?? '' ) && $lDig( $noRow ) !== $reg[0]['DIGEST'],
		'L78 the landed RESULT\'s DIGEST is record_digest of the record with its DERIVATION_CLASS, which the digest covers', json_encode( [ $lDig( $reg[0] ), $lDig( $noRow ), $reg[0]['DIGEST'] ?? null ] ) );
	$polled = $lOps->poll( [ 'ticket' => (string)$q ], 'Agent A' );
	G::ok( ( $polled['state'] ?? '' ) === TicketStore::DONE && json_decode( (string)( $polled['answer'] ?? '' ), true ) === $a, 'L38 POLL answers the ticket DONE with the landing\'s answer' );

	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$assumption]", 'block' => 'b1' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && str_contains( (string)( $a['detail'] ?? '' ), 'index 0' ) && !str_contains( (string)( $a['detail'] ?? '' ), 'RR-2' ),
		'L39 an identifier landed already is refused, the record named by its index, its identifier not echoed', json_encode( $a ) );
	G::ok( $lSnap() === $before, 'L40 and nothing is written' );

	// The admission refused by the seat table (vectors/governor.json, "petition: agent one unit over").
	$lSeats->put( 'Agent C', 'agent', 64801, $lNow );
	$before = $lSnap();
	$q = $lTicket( 'PETITION', 'Agent C', [ 'block' => 'b3' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'ADMISSION' && ( $a['decision']['decision'] ?? '' ) === 'REFUSED' && ( $a['decision']['refusal'] ?? '' ) === 'RATE'
		&& ( $a['decision']['payer'] ?? '' ) === 'AGENT', 'L41 admit refuses when the seat table says so: RATE, the agent paying', json_encode( $a ) );
	G::ok( ( $a['poll_after'] ?? 0 ) === 1, 'L42 the refusal answers the governor\'s retry-after as poll_after' );
	G::ok( $lSeats->get( 'Agent C', 'agent' ) === [ 64801, $lNow ] && $lSeats->get( 'Sponsor C', 'sponsor' ) === [ 0, 0 ], 'L43 the charge untouched by a refusal' );
	G::ok( $lSnap() === $before, 'L44 the refused admission writes no page' );
	$lSlow = new Landing( $lCalc, $lStore, $pt, $lTickets, $lSeats, $lCerts, $lConf + [ 'agent_stop' => true ], static fn (): int => $lNow, static fn (): array => [ 0, 1 ], nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent D', [ 'block' => 'b4' ] );
	$a = $lSlow->run( $q );
	G::ok( ( $a['decision']['refusal'] ?? '' ) === 'SWITCH' && ( $a['decision']['reason'] ?? '' ) === 'AGENT STOP', 'L45 the AGENT STOP switch, from configuration, refuses at admission', json_encode( $a ) );

	// RELEASE
	$q = $lTicket( 'RELEASE', 'Agent B', [ 'block' => 'b2' ] );
	G::ok( ( $lLanding->run( $q )['refused'] ?? '' ) === 'NOT HOLDER', 'L46 a RELEASE by an account that does not hold the lock is refused' );
	$lNow += 60;
	$q = $lTicket( 'RELEASE', 'Agent A', [ 'block' => 'b1' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['released'] ?? '' ) === '2026-10-26T07:34:20Z' && ( $a['block'] ?? '' ) === 'b1', 'L47 the holder\'s RELEASE answers released, the block', json_encode( $a ) );
	G::ok( array_key_exists( 'holder', $lLock() ) && $lLock()['holder'] === null, 'L48 the lock is free' );
	G::ok( ( $lBadge()['last_release'] ?? '' ) === '2026-10-26T07:34:20Z' && ( $lBadge()['record_count'] ?? 0 ) === 2, 'L49 the badge\'s last release advanced, its count kept' );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => $records, 'block' => 'b1' ] );
	G::ok( ( $lLanding->run( $q )['refused'] ?? '' ) === 'NOT HOLDER', 'L50 a PUSH after the release is refused' );
	$q = $lTicket( 'PETITION', 'Agent B', [ 'block' => 'b2' ] );
	G::ok( isset( $lLanding->run( $q )['grant'] ), 'L51 the freed lock is granted to the next PETITION' );
	$lNow += 3601;
	$q = $lTicket( 'PETITION', 'Agent A', [ 'block' => 'b5' ] );
	G::ok( isset( $lLanding->run( $q )['grant'] ) && ( $lLock()['holder'] ?? '' ) === 'Agent A', 'L52 a lock past its lease is granted to another account' );

	// The integrity halt: a binary that is not the expected one.
	$tamperBin = "$scratch/land-bin/pcalc";
	mkdir( dirname( $tamperBin ), 0755, true );
	copy( $lBuilt, $tamperBin );
	chmod( $tamperBin, 0755 );
	file_put_contents( $tamperBin, "\n", FILE_APPEND );
	$tRunner = new ProcRunner();
	$tCalc = new Calculator( $tamperBin, [ 'version' => $lVersion, 'digest' => $lDigest ], $tRunner, 'cli', new AnyResidence() );
	$tLanding = new Landing( $tCalc, $lStore, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ], nonces: $lNonces );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => str_replace( [ 'RR-1', 'RR-2' ], [ 'RR-3', 'RR-4' ], $records ), 'block' => 'b5' ] );
	$e = G::refuses( static fn () => $tLanding->run( $q ), DigestMismatch::class, 'DIGEST MISMATCH', 'L53 a tampered binary halts the landing: DIGEST MISMATCH thrown to the job' );
	G::ok( ( $lAnswer( $q )['refused'] ?? '' ) === 'INTEGRITY HALT' && ( $lTickets->get( $q )['state'] ?? '' ) === TicketStore::DONE,
		'L54 the ticket answered INTEGRITY HALT', json_encode( $lAnswer( $q ) ) );
	G::ok( $lSnap() === $before && $tRunner->starts === 0, 'L55 the pages unchanged and the binary never started' );

	// The job's context.
	G::ok( JobContext::refusal( JobContext::MIN_ADDRESS_SPACE, "Limit Soft Limit\nMax address space 1073741824 1073741824 bytes\n" ) !== null,
		'L56 an address space below the measured need refuses JOB CONTEXT' );
	G::ok( JobContext::refusal( JobContext::MIN_ADDRESS_SPACE, "Max address space unlimited unlimited bytes\n" ) === null
		&& JobContext::refusal( JobContext::MIN_ADDRESS_SPACE, 'Max address space ' . ( 2025138 * 1024 ) . " x bytes\n" ) === null,
		'L57 an unlimited address space, or one at the need, passes' );
	G::ok( JobContext::refusal( 0, '' ) === null, 'L58 a minimum of 0 checks nothing' );

	// A PUSH lands under the block the lock was granted for (the lock: Agent A's, block b5, L52).
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => str_replace( [ 'RR-1', 'RR-2' ], [ 'RR-3', 'RR-4' ], $records ), 'block' => 'b1' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'NOT HOLDER' && str_contains( (string)( $a['detail'] ?? '' ), 'b5' ),
		'L59 the holder\'s PUSH naming a block other than the one the lock was granted for is refused NOT HOLDER', json_encode( $a ) );
	G::ok( $lSnap() === $before && count( $lRegister() ) === 2, 'L60 and nothing is written' );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => str_replace( [ 'RR-1', 'RR-2' ], [ 'RR-3', 'RR-4' ], $records ) ] );
	$a = $lLanding->run( $q );
	$reg = $lRegister();
	G::ok( ( $a['block'] ?? '' ) === 'b5' && count( $reg ) === 4 && ( $reg[2]['BLOCK'] ?? '' ) === 'b5' && ( $reg[3]['BLOCK'] ?? '' ) === 'b5',
		'L61 a PUSH naming no block lands under the lock\'s grant, the records\' BLOCK b5', json_encode( $a ) );

	// record_check's setting: the UWC's BIBLIOGRAPHY SETTING from its DRAFT UWC page, OFF when the page states none.
	$lit = str_replace( [ '"ID":"RR-1"', '"REFS":' ], [ '"ID":"RR-5"', '"LITERATURE":["RR-BIB1"],"REFS":' ], $result );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$lit]" ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['answer'][1][0][0] ?? '' ) === 'REC-30',
		'L62 the spring DRAFT page states no setting, so OFF, the fleet default: a RESULT carrying LITERATURE is refused REC-30', json_encode( $a ) );
	G::ok( $lSnap() === $before, 'L63 and nothing is written' );
	$tDr = $pt->draft( $lPx );
	$drText = (string)$lInner->get( $tDr );
	$lInner->tamper( $tDr, $drText . Blocks::render( Landing::SETTING, 'OPEN' ) . "\n" );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$lit]" ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'UWC' && str_contains( (string)( $a['detail'] ?? '' ), 'bibliography setting' ) && $lSnap() === $before,
		'L64 a DRAFT page stating a word other than OFF, ON or CLOSED (the access policy\'s OPEN) refuses the PUSH, nothing written', json_encode( $a ) );
	$lInner->tamper( $tDr, $drText . Blocks::render( Landing::SETTING, 'ON' ) . "\n" );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$lit]" ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['answer'][1][0][0] ?? '' ) === 'REC-61' && $lSnap() === $before,
		'L65 under ON, stated on the DRAFT page, the same RESULT passes record_check and is refused by citation_check, REC-61: no bibliography entry is landed yet', json_encode( $a ) );
	$c = $lCalc->call( 'record', 'record_check', json_encode( [ 'record' => json_decode( $lit ), 'tfk' => json_decode( $lDraft ), 'setting' => 'ON', 'stage' => 'PUSH' ] ) );
	$c0 = $lCalc->call( 'record', 'record_check', json_encode( [ 'record' => json_decode( $lit ), 'tfk' => json_decode( $lDraft ), 'setting' => 'OFF', 'stage' => 'PUSH' ] ) );
	G::ok( ( $c['value'] ?? null ) === [ 'OK' ] && ( $c0['value'][1][0][0] ?? '' ) === 'REC-30', 'L66 the setting decides record_check: the record passes under ON and is refused REC-30 under OFF', json_encode( [ $c, $c0 ] ) );
	$lInner->tamper( $tDr, $drText );

	// A bare KERNEL derivation is refused at the PUSH: record_check answers REC-44, and nothing is written.
	$kernel = str_replace( [ '"ID":"RR-1"', '{"STEPS":2,"TEXT":"The force law and the definition of v."}' ], [ '"ID":"RR-5"', '{"PROOF":"opaque export text"}' ], $result );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$kernel]" ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['answer'][1][0][0] ?? '' ) === 'REC-44',
		'L79 a bare KERNEL is refused RECORD CHECK REC-44', json_encode( $a ) );
	G::ok( $lSnap() === $before, 'L80 and nothing is written' );

	// PROSE with the KERNEL proof attached: credit_record answers INSPECTION on the PROSE text, and it lands
	// with DERIVATION_CLASS INSPECTION, inside its digest.
	$attached = str_replace( [ '"ID":"RR-1"', '{"STEPS":2,"TEXT":"The force law and the definition of v."}' ],
		[ '"ID":"RR-5"', '{"STEPS":2,"TEXT":"The force law and the definition of v.","ATTACHMENT":{"PROOF":"opaque export text"}}' ], $result );
	$cr = $lCalc->call( 'derivation', 'credit_record', '{"record":' . $attached . ',"register":[],"starting_set":{}}' );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$attached]" ] );
	$a = $lLanding->run( $q );
	$reg = $lRegister();
	$last = end( $reg );
	G::ok( $cr['exit'] === 0 && ( $cr['value']['CLASS'] ?? '' ) === 'INSPECTION' && array_column( $a['landed'] ?? [], 'id' ) === [ 'RR-5' ]
		&& ( $a['landed'][0]['derivation_class'] ?? '' ) === 'INSPECTION' && ( $last['DERIVATION_CLASS'] ?? '' ) === 'INSPECTION'
		&& ( $last['DERIVATION']['ATTACHMENT']['PROOF'] ?? '' ) === 'opaque export text',
		'L136 PROSE with a KERNEL attachment lands with DERIVATION_CLASS INSPECTION, the attachment kept', json_encode( [ $cr['value'] ?? $cr['refused'] ?? null, $a ] ) );
	G::ok( $lDig( $last ) === ( $last['DIGEST'] ?? 'x' ), 'L137 and its DIGEST is record_digest of the record with the field' );

	// A RESULT whose credit the Calculator grants: the class is the Calculator's answer, not a constant.
	// The shape of vectors/structured_credit.json's "accepted-backward" (a law applied right to left),
	// its law the Research Assembly's TPK's KIN, D(x, t) = v: credit_record answers MECHANICAL.
	$mech = str_replace( [ '"ID":"RR-1"', '{"STEPS":2,"TEXT":"The force law and the definition of v."}', '"EQUATION":"m * D(v, t) = -k_s * x"',
		'"REFS":["m","v","t","k_s","x"]', '"STATEMENT":"The equation of motion on the spring axis."' ],
		[ '"ID":"RR-6"', '{"STEPS":[{"EQUATION":"v = D(x, t)","FORWARD":false,"LAW":"KIN","SITE":"rhs"}]}', '"EQUATION":"v = D(x, t)"',
		'"REFS":["v","x","t"]', '"STATEMENT":"The velocity is the rate of x."' ], $result );
	$cr = $lCalc->call( 'derivation', 'credit_record', '{"record":' . $mech . ',"register":[],"starting_set":' . json_encode( json_decode( $lDraft, true )['TPK'] ) . '}' );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$mech]" ] );
	$a = $lLanding->run( $q );
	$reg = $lRegister();
	$last = end( $reg );
	$noRow = $last;
	unset( $noRow['DERIVATION_CLASS'] );
	G::ok( $cr['exit'] === 0 && ( $cr['value']['CLASS'] ?? '' ) === 'MECHANICAL' && array_column( $a['landed'] ?? [], 'id' ) === [ 'RR-6' ]
		&& ( $a['landed'][0]['derivation_class'] ?? '' ) === 'MECHANICAL' && ( $last['DERIVATION_CLASS'] ?? '' ) === 'MECHANICAL'
		&& $lDig( $last ) === ( $last['DIGEST'] ?? 'x' ) && $lDig( $noRow ) !== $last['DIGEST'],
		'L81 a RESULT whose structured derivation credit_record answers MECHANICAL lands with DERIVATION_CLASS MECHANICAL, the reply\'s class, inside its DIGEST',
		json_encode( [ $cr['value'] ?? $cr['refused'] ?? null, $a ] ) );

	// The four constructions version 1 refused (its landing gates a1 3.1, 3.6, 3.8 and b1 L8).
	// The register: RR-1 to RR-6; the lock: Agent A's, block b5.
	$ass7 = str_replace( '"ID":"RR-2"', '"ID":"RR-7"', $assumption );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => '[' . str_replace( '"ID":"RR-2"', '"ID":"RR-8"', $assumption ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['answer'][1][0][0] ?? '' ) === 'SEQUENCE'
		&& str_contains( (string)( $a['detail'] ?? '' ), 'RR-7' ) && str_contains( (string)( $a['detail'] ?? '' ), 'index 0' )
		&& !str_contains( (string)( $a['detail'] ?? '' ), 'RR-8' ) && $lSnap() === $before,
		'L121 a record whose identifier is not the next free one (RR-8 where it is RR-7) is refused SEQUENCE, its index and the Calculator\'s next named, its own identifier not echoed, nothing written', json_encode( $a ) );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => '[' . str_replace( '"ID":"RR-2"', '"ID":"RR-8"', $assumption ) . ",$ass7]" ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['answer'][1][0][0] ?? '' ) === 'SEQUENCE' && $lSnap() === $before,
		'L138 a batch out of sequence (RR-8 before RR-7) is refused SEQUENCE, nothing written', json_encode( $a ) );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => '[' . str_replace( '"ID":"RR-2"', '"ID":"QQ-7"', $assumption ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['answer'][1][0][0] ?? '' ) === 'SEQUENCE' && $lSnap() === $before,
		'L139 the next number under another prefix than the register\'s (QQ-7 where it is RR-7) is refused SEQUENCE, nothing written', json_encode( $a ) );
	$ixText = (string)$lInner->get( $tIx );
	$lInner->tamper( $tIx, str_replace( Blocks::render( PageTexts::OPEN, '1' ), Blocks::render( PageTexts::OPEN, '2' ), $ixText ) );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$ass7]" ] );
	$a = $lLanding->run( $q );
	G::ok( $ixText !== $lInner->get( $tIx ) && ( $a['refused'] ?? '' ) === 'REGISTER' && $lSnap() === $before,
		'L140 a UWC whose open register volume is above 1 is refused REGISTER until the volume roll is built (the sequence counts volume 1 alone), nothing written', json_encode( $a ) );
	$lInner->tamper( $tIx, $ixText );
	$before = $lSnap();
	$cite = str_replace( [ '"CITES":[]', '"ID":"RR-1"' ], [ '"CITES":["RR-99"]', '"ID":"RR-7"' ], $result );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$cite]" ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['answer'][1][0][0] ?? '' ) === 'REC-58'
		&& ( $a['problems'][0]['answer'][1][0][1] ?? '' ) === 'CITES' && $lSnap() === $before,
		'L141 a record citing an identifier not in the register is refused by citation_check, REC-58, nothing written', json_encode( $a ) );
	$citeA = str_replace( [ '"ASSUMPTIONS":[]', '"ID":"RR-1"' ], [ '"ASSUMPTIONS":["RR-1"]', '"ID":"RR-7"' ], $result );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$citeA]" ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['answer'][1][0][0] ?? '' ) === 'REC-58'
		&& ( $a['problems'][0]['answer'][1][0][1] ?? '' ) === 'ASSUMPTIONS' && $lSnap() === $before,
		'L142 a record whose ASSUMPTIONS names a RESULT, not an ASSUMPTION of the register, is refused REC-58, nothing written', json_encode( $a ) );
	$sup = str_replace( '"ID":"RR-2"', '"ID":"RR-7","SUPERSEDES":"RR-2"', $assumption );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$sup]" ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'][0]['answer'][1][0][0] ?? '' ) === 'WITHDRAWAL'
		&& ( $a['problems'][0]['answer'][1][0][1] ?? '' ) === 'SUPERSEDES' && $lSnap() === $before,
		'L122 a record carrying SUPERSEDES (its own author\'s standing ASSUMPTION) is refused WITHDRAWAL: the withdrawal is not built, nothing written', json_encode( $a ) );
	$citeOk = str_replace( [ '"ASSUMPTIONS":[]', '"CITES":[]', '"ID":"RR-1"' ], [ '"ASSUMPTIONS":["RR-7"]', '"CITES":["RR-1"]', '"ID":"RR-8"' ], $result );
	$q = $lTicket( 'PUSH', 'Agent A', [ 'records' => "[$ass7,$citeOk]" ] );
	$a = $lLanding->run( $q );
	G::ok( array_column( $a['landed'] ?? [], 'id' ) === [ 'RR-7', 'RR-8' ] && count( $lRegister() ) === 8,
		'L123 the next free identifiers in sequence, a RESULT citing a landed RESULT and an ASSUMPTION landed before it in the batch: both land', json_encode( $a ) );
	// The access policy: the DRAFT UWC page's block pma-policy, the ACCESS LIST page's pma-access.
	$tAl = $pt->accessList( $lPx );
	$lInner->tamper( $tDr, $drText . Blocks::render( Landing::POLICY, 'CLOSED' ) . "\n" );
	$before = $lSnap();
	$q = $lTicket( 'PETITION', 'Agent J', [ 'block' => 'b10' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'ACCESS' && $lSnap() === $before,
		'L124 a CLOSED UWC whose access list cannot be read (no page) refuses the PETITION, ACCESS, nothing written (fail closed)', json_encode( $a ) );
	$lInner->tamper( $tAl, Blocks::render( Landing::ACCESS, '{"Agent J":1}' ) . "\n" );
	$before = $lSnap();
	$q = $lTicket( 'PETITION', 'Agent J', [ 'block' => 'b10' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'ACCESS' && $lSnap() === $before, 'L125 an access list that is not a list of account names refuses, ACCESS', json_encode( $a ) );
	$lInner->tamper( $tAl, Blocks::render( Landing::ACCESS, '["Agent J"]' ) . "\n" );
	$lNow += 3601;
	$before = $lSnap();
	$q = $lTicket( 'PETITION', 'Agent B', [ 'block' => 'b2' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'ACCESS' && !str_contains( (string)( $a['detail'] ?? '' ), '/' ) && $lSnap() === $before,
		'L126 under CLOSED an account off the access list is not granted the lock: ACCESS, nothing written', json_encode( $a ) );
	$q = $lTicket( 'PETITION', 'Agent J', [ 'block' => 'b10' ] );
	$a = $lLanding->run( $q );
	G::ok( isset( $a['grant'] ) && ( $lLock()['holder'] ?? '' ) === 'Agent J', 'L127 an account on the list petitions and is granted', json_encode( $a ) );
	$lInner->tamper( $tAl, Blocks::render( Landing::ACCESS, '["Agent B"]' ) . "\n" );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( '"ID":"RR-2"', '"ID":"RR-9"', $assumption ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'ACCESS' && $lSnap() === $before, 'L128 a holder taken off the list lands nothing: the PUSH refused ACCESS', json_encode( $a ) );
	$lInner->tamper( $tDr, $drText . Blocks::render( Landing::POLICY, 'SHUT' ) . "\n" );
	$q = $lTicket( 'PETITION', 'Agent B', [ 'block' => 'b2' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'UWC' && str_contains( (string)( $a['detail'] ?? '' ), 'access policy' ), 'L129 a policy word other than OPEN or CLOSED refuses, UWC', json_encode( $a ) );
	$lInner->tamper( $tDr, $drText . Blocks::render( Landing::POLICY, 'OPEN' ) . "\n" );
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( '"ID":"RR-2"', '"ID":"RR-9"', $assumption ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( array_column( $a['landed'] ?? [], 'id' ) === [ 'RR-9' ], 'L143 under OPEN the holder off the list lands', json_encode( $a ) );
	$lInner->tamper( $tDr, $drText );

	// The strike screen (`landing strike_screen`): SR3's mechanical tests at landing. The strike is not
	// written yet, so what the strike rule would strike is refused STRIKE OWED, nothing written.
	$mRec = static function ( string $id, string $value, string $uc ): array {
		return [ 'ID' => $id, 'CLASS' => 'RESULT', 'CITES' => [], 'ASSUMPTIONS' => [], 'STATEMENT' => "Measured E_x: $value m.", 'REGIME' => 'M',
			'DERIVATION' => [ 'STEPS' => 1, 'TEXT' => 'Read from the bench gauge.' ],
			'FALSIFIER' => 'A repeat reading outside the stated uncertainty.', 'FALSIFIER_CLASS' => 'F3',
			'QUANTITY' => 'E_x', 'VALUE' => $value, 'UNIT' => 'm', 'U_C' => $uc,
			'BUDGET' => [ [ 'NAME' => 'gauge', 'U' => $uc, 'UNIT' => 'm', 'EVALUATION' => 'B', 'BASIS' => 'manufacturer\'s specification' ] ],
			'CORRELATED' => false, 'AT' => [ [ 'DOF' => 't', 'VALUE' => '0', 'UNIT' => 's' ] ] ];
	};
	$strikeOwed = static function ( array $a ): bool {
		foreach ( $a['problems'] ?? [] as $p ) {
			if ( ( $p['answer'][1][0][0] ?? '' ) !== 'STRIKE OWED' ) {
				return false;
			}
		}
		return ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['problems'] ?? [] ) !== [];
	};
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => json_encode( [ $mRec( 'RR-10', '0', '0.001' ), $mRec( 'RR-11', '1', '0.001' ) ] ) ] );
	$a = $lLanding->run( $q );
	G::ok( $strikeOwed( $a ) && count( $a['problems'] ) === 1 && ( $a['problems'][0]['index'] ?? -1 ) === 0
		&& str_contains( (string)( $a['problems'][0]['answer'][1][0][2] ?? '' ), 'RR-10 and RR-11 (CONTRADICTS)' ),
		'L105 two M records 1000 u apart: the push is refused STRIKE OWED, nothing written (the pair named; L106 the pages)', json_encode( $a ) );
	G::ok( $lSnap() === $before && count( $lRegister() ) === 9, 'L106 nothing written: the register and every page as before' );
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => json_encode( [ $mRec( 'RR-10', '0', '0.001' ), $mRec( 'RR-11', '0.002', '0.001' ) ] ) ] );
	$a = $lLanding->run( $q );
	G::ok( array_column( $a['landed'] ?? [], 'id' ) === [ 'RR-10', 'RR-11' ], 'L107 two M records within k u of each other: the test clears them, both land', json_encode( $a ) );
	// A register holding a pair the strike rule would strike (set in place by fixture, as the strike
	// would have met it): a record citing a member of the pair is refused, nothing written.
	$regText0 = (string)$lInner->get( $tRg );
	$ixText0 = (string)$lInner->get( $tIx );
	$reg = $lRegister();
	foreach ( $reg as &$r ) {
		if ( ( $r['ID'] ?? '' ) === 'RR-11' ) {
			$r['VALUE'] = '1';
		}
	}
	unset( $r );
	$lInner->tamper( $tRg, PageTexts::register( $lPx, 1, (string)$lCalc->call( 'canonical', 'canonical_json', json_encode( [ 'value' => $reg ] ) )['value'] ) );
	$cite11 = [ 'ID' => 'RR-12', 'CLASS' => 'RESULT', 'CITES' => [ 'RR-11' ], 'ASSUMPTIONS' => [], 'STATEMENT' => 'A consequence of RR-11.',
		'REGIME' => 'L', 'DERIVATION' => [ 'STEPS' => 1, 'TEXT' => 'Restate.' ], 'FALSIFIER' => 'As cited.', 'FALSIFIER_CLASS' => 'F3' ];
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => json_encode( [ $cite11 ] ) ] );
	$a = $lLanding->run( $q );
	G::ok( $strikeOwed( $a ) && ( $a['problems'][0]['index'] ?? -1 ) === 0 && str_contains( (string)( $a['problems'][0]['answer'][1][0][2] ?? '' ), 'reached by RR-12' ),
		'L108 a citation of a record the strike rule refutes is refused STRIKE OWED, the citing record named', json_encode( $a ) );
	G::ok( $lSnap() === $before, 'L109 nothing written' );
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => json_encode( [ array_merge( $cite11, [ 'CITES' => [ 'RR-1' ], 'STATEMENT' => 'A consequence of RR-1.' ] ) ] ) ] );
	$a = $lLanding->run( $q );
	G::ok( array_column( $a['landed'] ?? [], 'id' ) === [ 'RR-12' ], 'L110 a batch that reaches no member of the pair lands beside it', json_encode( $a ) );

	// Fail closed: a `strike_screen` answer other than ["OK", []] that names no pair (owed, a refusal
	// as a value, an answer outside its form, a pcalc that fails) refuses the push, nothing written.
	// The Calculator's runner answers the screen as each case sets; every other call is pcalc's own.
	$sFake = null;
	$sRunner = new class( $sFake ) implements ShellRunner {
		private ProcRunner $proc;
		private ?array $fake;
		public function __construct( ?array &$fake ) {
			$this->fake = &$fake;
			$this->proc = new ProcRunner();
		}
		public function run( array $argv, string $stdin ): array {
			if ( $this->fake !== null && array_slice( $argv, 1 ) === [ 'landing', 'strike_screen' ] ) {
				return $this->fake;
			}
			return $this->proc->run( $argv, $stdin );
		}
	};
	$sCalc = new Calculator( $lBuilt, [ 'version' => $lVersion, 'digest' => $lDigest ], $sRunner, 'cli', new AnyResidence() );
	$sLanding = new Landing( $sCalc, $lStore, $pt, $lTickets, $lSeats, $lCerts, $lConf, static function () use ( &$lNow ): int {
		return $lNow;
	}, static fn (): array => [ 0, 1 ], nonces: $lNonces );
	// A batch the screen clears (it reaches no member of the pair the fixture holds): only the fake refuses it.
	$sBatch = json_encode( [ array_merge( $cite11, [ 'ID' => 'RR-13', 'CITES' => [ 'RR-1' ], 'STATEMENT' => 'A consequence of RR-1.' ] ) ] );
	$before = $lSnap();
	$sFake = [ 1, '{"detail":"the batch reaches more than 8 quantities; the strike screen compares at most 8","refused":"OWED"}' . "\n", '' ];
	$a = $sLanding->run( $lTicket( 'PUSH', 'Agent J', [ 'records' => $sBatch ] ) );
	G::ok( ( $a['refused'] ?? '' ) === 'CALCULATOR REFUSED' && str_contains( (string)( $a['detail'] ?? '' ), 'the strike screen: OWED' ) && $lSnap() === $before,
		'L111 a strike screen answered OWED refuses the push CALCULATOR REFUSED, nothing written', json_encode( $a ) );
	$sFake = [ 0, '["REFUSED",[["REC-50","-","records is not a register"]]]' . "\n", '' ];
	$a = $sLanding->run( $lTicket( 'PUSH', 'Agent J', [ 'records' => $sBatch ] ) );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && str_contains( (string)( $a['detail'] ?? '' ), 'the strike screen refuses the register' ) && $lSnap() === $before,
		'L112 a strike screen answered REFUSED as a value refuses the push RECORD CHECK, nothing written', json_encode( $a ) );
	$sFake = [ 0, '["OK","none"]' . "\n", '' ];
	$a = $sLanding->run( $lTicket( 'PUSH', 'Agent J', [ 'records' => $sBatch ] ) );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && $lSnap() === $before,
		'L113 a strike screen answer outside its form refuses the push RECORD CHECK, nothing written', json_encode( $a ) );
	$sFake = [ 139, '', 'Segmentation fault' ];
	$sQ = $lTicket( 'PUSH', 'Agent J', [ 'records' => $sBatch ] );
	G::refuses( static fn () => $sLanding->run( $sQ ), CalculatorFault::class, 'landing strike_screen',
		'L114 a pcalc that fails on the strike screen is a fault: the job is rethrown' );
	$a = $lAnswer( $sQ );
	G::ok( ( $a['refused'] ?? '' ) === 'CALCULATOR FAULT' && $lSnap() === $before,
		'L115 its ticket answered CALCULATOR FAULT, nothing written', json_encode( $a ) );
	$sFake = null;
	$a = $sLanding->run( $lTicket( 'PUSH', 'Agent J', [ 'records' => $sBatch ] ) );
	G::ok( array_column( $a['landed'] ?? [], 'id' ) === [ 'RR-13' ], 'L116 the same batch, the screen answered by pcalc, lands', json_encode( $a ) );
	$lInner->tamper( $tRg, $regText0 );
	$lInner->tamper( $tIx, $ixText0 );

	// Any other fault answers the ticket JOB FAULT with the class name only, gives the class and message to
	// the error channel, and is rethrown: a store that fails on every call.
	$down = new class implements PageStore {
		public function get( string $title ): ?string {
			throw new RuntimeException( 'the store is down (the test\'s fault)' );
		}
		public function exists( string $title ): bool {
			throw new RuntimeException( 'the store is down (the test\'s fault)' );
		}
		public function put( string $title, string $text, string $summary ): void {
			throw new RuntimeException( 'the store is down (the test\'s fault)' );
		}
		public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
			throw new RuntimeException( 'the store is down (the test\'s fault)' );
		}
		public function appendAs( string $title, string $line, string $summary, string $actor ): string {
			throw new RuntimeException( 'the store is down (the test\'s fault)' );
		}
	};
	$fSunk = [];
	$fLanding = new Landing( $lCalc, $down, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ],
		static function ( int $id, Throwable $e ) use ( &$fSunk ): void {
			$fSunk[] = [ $id, get_class( $e ), $e->getMessage() ];
		}, nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent F', [ 'block' => 'b6' ] );
	G::refuses( static fn () => $fLanding->run( $q ), RuntimeException::class, 'the store is down', 'L67 a fault of no kind the job names is rethrown to the job' );
	G::ok( $fSunk === [ [ $q, 'RuntimeException', 'the store is down (the test\'s fault)' ] ],
		'L67 and the error channel was given the ticket, the exception\'s class and its message', json_encode( $fSunk ) );
	$fa = $lAnswer( $q );
	$faRaw = (string)( $lTickets->get( $q )['answer'] ?? '' );
	G::ok( $fa === [ 'refused' => 'JOB FAULT', 'class' => 'RuntimeException' ] && !str_contains( $faRaw, 'store' ) && !str_contains( $faRaw, 'fault' )
		&& ( $lTickets->get( $q )['state'] ?? '' ) === TicketStore::DONE && !in_array( $q, array_column( $lTickets->inWork(), 'id' ), true ),
		'L68 the ticket answered JOB FAULT with the exception\'s class name and nothing of its message, DONE, no longer in flight', $faRaw );

	// The charge an admission answers is applied whole, or the job faults: a stand-in that answers `governor admit`
	// itself and hands every other call to the built pcalc.
	$lWrap = static function ( string $name, string $admit ) use ( $scratch, $lBuilt, $lVersion ): Calculator {
		$bin = "$scratch/land-wrap/$name";
		if ( !is_dir( dirname( $bin ) ) ) {
			mkdir( dirname( $bin ), 0755, true );
		}
		file_put_contents( $bin, "#!/bin/sh\nif [ \"\$1\" = governor ] && [ \"\$2\" = admit ]; then\n\tcat > /dev/null\n\tprintf '%s\\n' '$admit'\n\texit 0\nfi\n"
			. "exec '$lBuilt' \"\$@\"\n" );
		chmod( $bin, 0755 );
		return new Calculator( $bin, [ 'version' => $lVersion, 'digest' => Calculator::digestOf( $bin ) ], new ProcRunner(), 'cli', new AnyResidence() );
	};
	$before = $lSnap();
	$wLanding = new Landing( $lWrap( 'half', '{"charge":{"agent":[1,2]},"decision":"ADMITTED"}' ), $lStore, $pt, $lTickets, $lSeats, $lCerts, $lConf,
		static fn (): int => $lNow, static fn (): array => [ 0, 1 ], nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent G', [ 'block' => 'b7' ] );
	G::refuses( static fn () => $wLanding->run( $q ), CalculatorFault::class, 'a charge not of the form',
		'L69 an ADMITTED answer whose charge lacks the sponsor\'s bucket faults the job (CalculatorFault), never skipped' );
	G::ok( ( $lAnswer( $q )['refused'] ?? '' ) === 'CALCULATOR FAULT' && $lSeats->get( 'Agent G', 'agent' ) === [ 0, 0 ] && $lSnap() === $before,
		'L70 the ticket answered CALCULATOR FAULT, the seat table untouched, no page written', json_encode( $lAnswer( $q ) ) );
	$wLanding = new Landing( $lWrap( 'none', '{"charge":null,"decision":"ADMITTED"}' ), $lStore, $pt, $lTickets, $lSeats, $lCerts, $lConf,
		static fn (): int => $lNow, static fn (): array => [ 0, 1 ], nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent G', [ 'block' => 'b7' ] );
	G::refuses( static fn () => $wLanding->run( $q ), CalculatorFault::class, 'a charge not of the form',
		'L71 a null charge with the governor on, in a lane it charges (PETITION, 3), faults the job' );
	$oLanding = new Landing( $lCalc, $lStore, $pt, $lTickets, $lSeats, $lCerts, $lConf + [ 'governor_off' => true ], static fn (): int => $lNow,
		static fn (): array => [ 0, 1 ], nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent H', [ 'block' => 'b8' ] );
	$a = $oLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'LOCK HELD' && $lSeats->get( 'Agent H', 'agent' ) === [ 0, 0 ] && $lSeats->get( 'Sponsor H', 'sponsor' ) === [ 0, 0 ],
		'L72 with the governor off admit answers no charge (null) and the op runs: LOCK HELD, the seat table untouched', json_encode( $a ) );

	// The error channel by default is wfDebugLog's `Custos`; a channel that fails stops nothing; the short class name.
	if ( !function_exists( 'wfDebugLog' ) ) {
		function wfDebugLog( string $group, string $text, $dest = 'all', array $context = [] ): void {
			$GLOBALS['harness_debug_log'][] = [ $group, $text ];
		}
	}
	$GLOBALS['harness_debug_log'] = [];
	$dLanding = new Landing( $lCalc, $down, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ], nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent I', [ 'block' => 'b9' ] );
	G::refuses( static fn () => $dLanding->run( $q ), RuntimeException::class, 'the store is down', 'L73 a fault with no sink given is rethrown' );
	G::ok( $GLOBALS['harness_debug_log'] === [ [ Landing::LOG, "land ticket $q: RuntimeException: the store is down (the test's fault)" ] ]
		&& Landing::LOG === 'Custos' && ( $lAnswer( $q )['class'] ?? '' ) === 'RuntimeException' && !isset( $lAnswer( $q )['detail'] ),
		'L73 and with no sink given the class and message go to the debug log `Custos`, the ticket\'s answer carrying the class only',
		json_encode( $GLOBALS['harness_debug_log'] ) );
	$bLanding = new Landing( $lCalc, $down, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ],
		static function ( int $id, Throwable $e ): void {
			throw new LogicException( 'the error channel is down too' );
		}, nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent I', [ 'block' => 'b9' ] );
	G::refuses( static fn () => $bLanding->run( $q ), RuntimeException::class, 'the store is down', 'L74 an error channel that fails does not replace the fault rethrown' );
	G::ok( ( $lAnswer( $q )['refused'] ?? '' ) === 'JOB FAULT' && ( $lTickets->get( $q )['state'] ?? '' ) === TicketStore::DONE,
		'L74 and the ticket is still answered JOB FAULT and DONE', json_encode( $lAnswer( $q ) ) );
	$anon = new class( 'a path /srv/x and a host (the test\'s fault)' ) extends RuntimeException {
	};
	G::ok( Landing::faultClass( $anon ) === 'RuntimeException@anonymous' && Landing::faultClass( new DigestMismatch( 'a', 'b' ) ) === 'DigestMismatch'
		&& Landing::faultClass( new RuntimeException( 'x' ) ) === 'RuntimeException',
		'L75 the short class name: no namespace, and an anonymous class\'s name without the file it carries', Landing::faultClass( $anon ) );

	// A record lands as pushed or not at all: a value PHP cannot hold as the Calculator read it is refused NOT READ
	// before any check, nothing landed. The holder is Agent J (L91), under its lease.
	$lHold = static fn ( array $a ): bool => ( $a['refused'] ?? '' ) === 'NOT READ' && str_ends_with( (string)( $a['detail'] ?? '' ), Landing::HOLD );
	$lRegBefore = $lRegister();
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( [ '"ID":"RR-1"', '"STEPS":2' ], [ '"ID":"RR-12"', '"STEPS":9223372036854775808' ], $result ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( $lHold( $a ) && ( $a['detail'] ?? '' ) === 'the records: ' . Landing::HOLD && $lSnap() === $before && $lRegister() === $lRegBefore,
		'L130 a record carrying the integer 2^63 (past PHP_INT_MAX) is refused NOT READ, a number the landing cannot hold exactly; nothing landed', json_encode( $a ) );
	G::ok( $lAnswer( $q ) === $a && ( $lTickets->get( $q )['state'] ?? '' ) === TicketStore::DONE, 'L131 the refusal is the ticket\'s answer, the ticket DONE' );
	foreach ( [ '12345678901234567890' => [ 'L132a', 'a 20-digit integer' ], '-9223372036854775809' => [ 'L132b', 'the integer -2^63 - 1 (below PHP_INT_MIN)' ] ] as $n => [ $case, $label ] ) {
		$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( [ '"ID":"RR-1"', '"STEPS":2' ], [ '"ID":"RR-12"', "\"STEPS\":$n" ], $result ) . ']' ] );
		$a = $lLanding->run( $q );
		G::ok( $lHold( $a ) && $lSnap() === $before, "$case a record carrying $label is refused NOT READ; nothing landed", json_encode( $a ) );
	}
	// A decimal of 20 significant digits: the Calculator's canonical text carries twelve (the twelve-digit form),
	// which binary64 holds and PHP writes back byte for byte, so the read passes and the record checks decide.
	$c20 = $lCalc->call( 'canonical', 'canonical_json', '{"value":1.2345678901234567890}' )['value'] ?? '';
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( [ '"ID":"RR-1"', '"STEPS":2' ], [ '"ID":"RR-12"', '"STEPS":1.2345678901234567890' ], $result ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( $c20 === '1.23456789012' && ( $a['refused'] ?? '' ) === 'RECORD CHECK' && $lSnap() === $before,
		'L133 a decimal of 20 significant digits is read as the Calculator\'s twelve-digit form (not NOT READ); the record checks refuse it, nothing landed', json_encode( [ $c20, $a ] ) );
	// The register and the lock pass through the same check.
	$regPage = (string)$lInner->get( $tRg );
	$lInner->tamper( $tRg, str_replace( '"STEPS":2', '"STEPS":9223372036854775808', $regPage ) );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( '"ID":"RR-2"', '"ID":"RR-12"', $assumption ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( $lInner->get( $tRg ) !== $regPage && $lHold( $a ) && ( $a['detail'] ?? '' ) === 'the register: ' . Landing::HOLD && $lSnap() === $before,
		'L134 a register text carrying the integer 2^63 refuses the PUSH NOT READ; nothing landed, the register as it was', json_encode( $a ) );
	$lInner->tamper( $tRg, $regPage );
	$lockPage = (string)$lInner->get( $tLk );
	$lInner->tamper( $tLk, str_replace( '"holder":', '"expected":9223372036854775808,"holder":', $lockPage ) );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( '"ID":"RR-2"', '"ID":"RR-12"', $assumption ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( $lInner->get( $tLk ) !== $lockPage && $lHold( $a ) && ( $a['detail'] ?? '' ) === 'the lock: ' . Landing::HOLD && $lSnap() === $before,
		'L105 a lock text carrying the integer 2^63 refuses NOT READ; nothing written', json_encode( $a ) );
	$lInner->tamper( $tLk, $lockPage );
	// The spring RESULT and ASSUMPTION (L24) landed as pushed: each landed DIGEST is the Calculator's record_digest of
	// the pushed text with the members Custos owns, built by concatenation, never through PHP's values.
	$owned = [ 'AUTHOR', 'BLOCK', 'DERIVATION_CLASS', 'D_IS', 'GRADE', 'LANDED', 'LANDED_BY', 'STATUS', 'TPS' ];
	$reg = $lRegister();
	$same = true;
	foreach ( [ 0 => $result, 1 => $assumption ] as $i => $pushed ) {
		$mine = array_intersect_key( $reg[$i], array_flip( $owned ) );
		$text = substr( $pushed, 0, -1 ) . ',' . substr( json_encode( $mine, JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE ), 1 );
		$d = $lCalc->call( 'record', 'record_digest', '{"record":' . $text . '}' )['value'] ?? null;
		$same = $same && is_array( $d ) && ( $d[0] ?? null ) === 'OK' && ( $d[1] ?? null ) === ( $reg[$i]['DIGEST'] ?? 'x' );
	}
	G::ok( $same && ( $reg[0]['ID'] ?? '' ) === 'RR-1' && ( $reg[1]['ID'] ?? '' ) === 'RR-2',
		'L106 the spring RESULT and ASSUMPTION landed with the digests the Calculator computes on the pushed text and the members Custos owns', json_encode( [ $reg[0]['DIGEST'] ?? null, $reg[1]['DIGEST'] ?? null ] ) );
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( '"ID":"RR-2"', '"ID":"RR-12"', $assumption ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( array_column( $a['landed'] ?? [], 'id' ) === [ 'RR-12' ], 'L107 with the register and the lock restored the holder\'s next record lands', json_encode( $a ) );
	// An integer past binary64's range: PHP decodes it to INF, which its encoder will not write; NOT READ, never JOB FAULT.
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( [ '"ID":"RR-1"', '"STEPS":2' ], [ '"ID":"RR-13"', '"STEPS":' . str_repeat( '9', 400 ) ], $result ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['detail'] ?? '' ) === 'the records: ' . Landing::HOLD && $lHold( $a ) && $lSnap() === $before,
		'L108 a record carrying a 400-digit integer (INF to PHP) is refused NOT READ, not JOB FAULT; nothing landed', json_encode( $a ) );
	// The request, the badge and the access list read through the same check.
	$q = $lTickets->create( 'PETITION', 'Agent J', $lPx, '{"block":"b10","n":9223372036854775808}' );
	$a = $lLanding->run( $q );
	G::ok( ( $a['detail'] ?? '' ) === 'the ticket\'s request: ' . Landing::HOLD && $lHold( $a ) && $lSnap() === $before,
		'L109 a ticket\'s request carrying the integer 2^63 is refused NOT READ; nothing written', json_encode( $a ) );
	$ixPage = (string)$lInner->get( $tIx );
	$lInner->tamper( $tIx, preg_replace( '/"record_count":\d+/', '"record_count":9223372036854775808', $ixPage, 1 ) );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( '"ID":"RR-2"', '"ID":"RR-13"', $assumption ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( $lInner->get( $tIx ) !== $ixPage && ( $a['detail'] ?? '' ) === 'the badge: ' . Landing::HOLD && $lHold( $a ) && $lSnap() === $before,
		'L110 a badge carrying the integer 2^63 refuses the PUSH NOT READ; nothing landed', json_encode( $a ) );
	$lInner->tamper( $tIx, $ixPage );
	$lInner->tamper( $tDr, $drText . Blocks::render( Landing::POLICY, 'CLOSED' ) . "\n" );
	$lInner->tamper( $tAl, Blocks::render( Landing::ACCESS, '["Agent J",9223372036854775808]' ) . "\n" );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( '"ID":"RR-2"', '"ID":"RR-13"', $assumption ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['detail'] ?? '' ) === 'the access list: ' . Landing::HOLD && $lHold( $a ) && $lSnap() === $before,
		'L111 under CLOSED an access list carrying the integer 2^63 refuses the PUSH NOT READ; nothing landed', json_encode( $a ) );
	$lInner->tamper( $tAl, Blocks::render( Landing::ACCESS, '["Agent J"]' ) . "\n" );
	$lInner->tamper( $tDr, $drText );
	// Where PHP spells a value otherwise than the canonical text (an exponent; U+2028, which PHP escapes), PHP's text
	// is read by the Calculator once more and the value is held where that canonical text is the first. A record
	// field takes no JSON number but STEPS (an integer) and no text holding U+2028, so such a record is read and
	// the record checks refuse it; the request and the lock carry them as members the job does not read.
	$c = static fn ( string $t ): string => (string)( $lCalc->call( 'canonical', 'canonical_json', '{"value":' . $t . '}' )['value'] ?? '' );
	$ls = "a\u{2028}b\u{2029}c";
	$php = json_encode( json_decode( $c( '[1e-05,1e+20,"' . $ls . '"]' ) ), JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_PRESERVE_ZERO_FRACTION );
	G::ok( $c( '[1e-05,1e+20,"' . $ls . '"]' ) === '[1e-05,1e+20,"' . $ls . '"]' && $php === '[1.0e-5,1.0e+20,"a\\u2028b\\u2029c"]'
		&& $c( $php ) === '[1e-05,1e+20,"' . $ls . '"]',
		'L112 PHP spells 1e-05, 1e+20 and U+2028/U+2029 otherwise than the canonical text, and the canonical text of PHP\'s text is the first', $php );
	G::ok( $c( '9223372036854775808' ) === '9223372036854775808' && $c( json_encode( json_decode( '9223372036854775808' ) ) ) === '9.22337203685e+18'
		&& $c( json_encode( json_decode( '12345678901234567890' ), JSON_PRESERVE_ZERO_FRACTION ) ) === '1.23456789012e+19'
		&& $c( json_encode( json_decode( '100000000000000000000' ), JSON_PRESERVE_ZERO_FRACTION ) ) === '1e+20',
		'L113 an integer PHP does not hold is written by PHP as a float, which the Calculator reads as a number, never the integer: the canonical texts differ' );
	$before = $lSnap();
	foreach ( [ 'L114a' => '1e-05', 'L114b' => '1e+20' ] as $case => $n ) {
		$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( [ '"ID":"RR-1"', '"STEPS":2' ], [ '"ID":"RR-13"', "\"STEPS\":$n" ], $result ) . ']' ] );
		$a = $lLanding->run( $q );
		G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && $lSnap() === $before,
			"$case a record carrying $n is read (not NOT READ); the record checks refuse it (STEPS an integer), nothing landed", json_encode( $a ) );
	}
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( [ '"ID":"RR-2"', 'The mass is constant.' ], [ '"ID":"RR-13"', "The mass\u{2028}is constant." ], $assumption ) . ']' ] );
	$a = $lLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && str_contains( json_encode( $a ), 'REC-10' ) && $lSnap() === $before,
		'L115 a record whose PROPOSITION holds U+2028 is read (not NOT READ); the record checks refuse it (REC-10), nothing landed', json_encode( $a ) );
	$lockPage = (string)$lInner->get( $tLk );
	$lInner->tamper( $tLk, str_replace( '"holder":', '"expected":1e-05,"held":1e+20,"holder":', $lockPage ) );
	$records = '[' . str_replace( '"ID":"RR-2"', '"ID":"RR-13"', $assumption ) . ']';
	$jNonce = $lNonces->peek( 'Agent J', $lPx );
	$q = $lTickets->create( 'PUSH', 'Agent J', $lPx, json_encode( [ 'note' => $ls, 'records' => $records ]
		+ ( $jNonce === null ? [] : [ 'challenge_response' => Challenge::response( $lCalc, $jNonce )[1] ] ), JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE ) );
	$a = $lLanding->run( $q );
	G::ok( array_column( $a['landed'] ?? [], 'id' ) === [ 'RR-13' ] && str_contains( (string)$lInner->get( $tRg ), '"ID":"RR-13"' ),
		'L116 a request carrying a string with U+2028 and U+2029, and a lock carrying 1e-05 and 1e+20, are held: the record lands', json_encode( $a ) );
	$lInner->tamper( $tLk, $lockPage );
	$regPage = (string)$lInner->get( $tRg );
	$lInner->tamper( $tRg, str_replace( '"PROPOSITION":"The mass is constant."', '"PROPOSITION":"The mass' . "\u{2028}" . 'is constant."', $regPage ) );
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( '"ID":"RR-2"', '"ID":"RR-14"', $assumption ) . ']' ] );
	$a = $lLanding->run( $q );
	$page = (string)$lInner->get( $tRg );
	G::ok( array_column( $a['landed'] ?? [], 'id' ) === [ 'RR-14' ] && str_contains( $page, '"ID":"RR-14"' )
		&& str_contains( $page, '"PROPOSITION":"The mass' . "\u{2028}" . 'is constant."' ) && !str_contains( $page, '\\u2028' ),
		'L117 a register whose landed record holds U+2028 is held: the next record lands, the string byte-equal in the register written', json_encode( $a ) );
	$before = $lSnap();
	$lRegBefore = $lRegister();
	foreach ( [ '9223372036854775808' => [ 'L118a', '2^63' ], '-9223372036854775809' => [ 'L118b', '-2^63 - 1' ], '100000000000000000000' => [ 'L118c', '10^20 (binary64 holds it; PHP an int does not)' ] ] as $n => [ $case, $label ] ) {
		$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( [ '"ID":"RR-1"', '"STEPS":2' ], [ '"ID":"RR-15"', "\"STEPS\":$n" ], $result ) . ']' ] );
		$a = $lLanding->run( $q );
		G::ok( ( $a['detail'] ?? '' ) === 'the records: ' . Landing::HOLD && $lHold( $a ) && $lSnap() === $before && $lRegister() === $lRegBefore,
			"$case a record carrying the integer $label is still refused NOT READ, detail HOLD, after the second reading; nothing landed", json_encode( $a ) );
	}
	// Under serialize_precision 17 (php.ini may say so) PHP writes 0.1 as 0.10000000000000001, whose canonical text is
	// 0.1 again: the job sets -1 while it runs, so the checks are sent the canonical value, and restores the setting.
	$sent = [];
	$spy = new class( $sent ) implements \Custos\ShellRunner {
		public function __construct( private array &$sent ) {
		}

		public function run( array $argv, string $stdin ): array {
			$this->sent[] = $stdin;
			return ( new ProcRunner() )->run( $argv, $stdin );
		}
	};
	$sLanding = new Landing( new Calculator( $lBuilt, [ 'version' => $lVersion, 'digest' => $lDigest ], $spy, 'cli', new AnyResidence() ),
		$lStore, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ], nonces: $lNonces );
	$was = ini_get( 'serialize_precision' );
	ini_set( 'serialize_precision', '17' );
	$before = $lSnap();
	$q = $lTicket( 'PUSH', 'Agent J', [ 'records' => '[' . str_replace( [ '"ID":"RR-1"', '"STEPS":2' ], [ '"ID":"RR-15"', '"STEPS":0.1' ], $result ) . ']' ] );
	$a = $sLanding->run( $q );
	$after = ini_get( 'serialize_precision' );
	ini_set( 'serialize_precision', (string)$was );
	$checks = array_values( array_filter( $sent, static fn ( string $t ): bool => str_contains( $t, '"stage":"PUSH"' ) ) );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && $lSnap() === $before && count( $checks ) === 1
		&& str_contains( $checks[0], '"STEPS":0.1,' ) && !str_contains( implode( '', $sent ), '0.10000000000000001' ) && $after === '17',
		'L119 under serialize_precision 17 a record carrying 0.1 is checked on the canonical value 0.1, never 0.10000000000000001; the setting restored', json_encode( [ $a, $after ] ) );
	// The ticket's answer is written under the job's setting too. A wait is a count (the base cast, plus the governor's
	// jitter), so the float is the governor's: a decision carrying 0.1, the test's wrapper, which the answer carries whole.
	$pLanding = new Landing( $lWrap( 'tenth', '{"decision":"REFUSED","reason":"AGENT STOP","refusal":"SWITCH","retry_after":5,"weight":0.1}' ), $lStore, $pt,
		$lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ] );
	ini_set( 'serialize_precision', '17' );
	$q = $lTicket( 'PETITION', 'Agent H', [ 'block' => 'b8' ] );
	$a = $pLanding->run( $q );
	$after = ini_get( 'serialize_precision' );
	ini_set( 'serialize_precision', (string)$was );
	$text = (string)( $lTickets->get( $q )['answer'] ?? '' );
	G::ok( ( $a['refused'] ?? '' ) === 'ADMISSION' && str_contains( $text, '"weight":0.1' ) && !str_contains( $text, '0.10000000000000001' ) && $after === '17',
		'L120 under serialize_precision 17 the ticket\'s answer is written under -1 (the decision\'s 0.1, never 0.10000000000000001); the setting restored', $text );
	// What a ticket's refusal may say, through the job: each fault built with a path, a file name, a
	// host name and stderr text; the ticket's raw answer carries none of them and the error channel all.
	$xSunk = [];
	$xSink = static function ( int $id, Throwable $e ) use ( &$xSunk ): void {
		$xSunk[] = [ $id, get_class( $e ), $e->getMessage() ];
	};
	$xRaw = static fn ( int $id ): string => (string)( $lTickets->get( $id )['answer'] ?? '' );
	$xSunkHas = static function ( int $id, string $needle ) use ( &$xSunk ): bool {
		foreach ( $xSunk as [ $sid, , $msg ] ) {
			if ( $sid === $id && str_contains( $msg, $needle ) ) {
				return true;
			}
		}
		return false;
	};
	// CALCULATOR FAULT: pcalc ends with exit code 7 and writes a path, a file name, a host name and stderr text.
	$xBin = "$scratch/land-wrap/stderr";
	file_put_contents( $xBin, "#!/bin/sh\nif [ \"\$1\" = canonical ]; then\n\tcat > /dev/null\n\techo '" . $fMsg . "' >&2\n\texit 7\nfi\n"
		. "exec '$lBuilt' \"\$@\"\n" );
	chmod( $xBin, 0755 );
	$xLanding = new Landing( new Calculator( $xBin, [ 'version' => $lVersion, 'digest' => Calculator::digestOf( $xBin ) ], new ProcRunner(), 'cli', new AnyResidence() ),
		$lStore, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ], $xSink, nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent X', [ 'block' => 'b20' ] );
	G::refuses( static fn () => $xLanding->run( $q ), CalculatorFault::class, 'exit code 7', 'LF1 pcalc ending with exit code 7 faults the job, rethrown with its stderr in the message' );
	G::ok( $lAnswer( $q ) === [ 'refused' => 'CALCULATOR FAULT', 'detail' => 'exit code: pcalc canonical canonical_json' ] && $fClean( $lAnswer( $q ) )
		&& !str_contains( $xRaw( $q ), $scratch ) && $xSunkHas( $q, $fLeaks[2] ) && $xSunkHas( $q, $fLeaks[0] ),
		'LF2 CALCULATOR FAULT answers the fault\'s name and the call, no path, no host name, no stderr; the error channel has pcalc\'s stderr line',
		$xRaw( $q ) );
	// UNSAFE RESIDENCE: a residence check refusing a path that names a host and a file.
	$xRes = new class( $fLeaks[0] . '.' . $fLeaks[1] ) implements \Custos\Residence {
		public function __construct( private string $p ) {
		}
		public function check( string $path ): void {
			throw new UnsafeResidence( $this->p, 'is not owned by root' );
		}
	};
	$xLanding = new Landing( new Calculator( $lBuilt, [ 'version' => $lVersion, 'digest' => $lDigest ], new ProcRunner(), 'cli', $xRes ),
		$lStore, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ], $xSink, nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent X', [ 'block' => 'b21' ] );
	G::refuses( static fn () => $xLanding->run( $q ), UnsafeResidence::class, 'UNSAFE RESIDENCE', 'LF3 an unsafe residence faults the job, rethrown with its path' );
	G::ok( $lAnswer( $q ) === [ 'refused' => 'CALCULATOR FAULT', 'detail' => 'unsafe residence: owner' ] && $fClean( $lAnswer( $q ) ) && $xSunkHas( $q, $fLeaks[0] ),
		'LF4 the ticket answered the check that failed by name (owner), never the path; the error channel has the path', $xRaw( $q ) );
	// INTEGRITY HALT: the tampered binary, under the scratch folder.
	$xLanding = new Landing( $tCalc, $lStore, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ], $xSink, nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent X', [ 'block' => 'b22' ] );
	G::refuses( static fn () => $xLanding->run( $q ), DigestMismatch::class, 'DIGEST MISMATCH', 'LF5 the tampered binary halts the job' );
	G::ok( $lAnswer( $q ) === [ 'refused' => 'INTEGRITY HALT', 'detail' => 'digest mismatch' ] && $fClean( $lAnswer( $q ) )
		&& !str_contains( $xRaw( $q ), $lDigest ) && $xSunkHas( $q, 'DIGEST MISMATCH: ' ),
		'LF6 INTEGRITY HALT answers "digest mismatch" alone, no digest and no path; the error channel has the message', $xRaw( $q ) );
	// PAGE FAULT: a page store faulting with every leak in its message.
	$xPf = new class( $fMsg ) implements PageStore {
		public function __construct( private string $m ) {
		}
		public function get( string $title ): ?string {
			throw new PageFault( $this->m . ' ' . $title );
		}
		public function exists( string $title ): bool {
			throw new PageFault( $this->m );
		}
		public function put( string $title, string $text, string $summary ): void {
			throw new PageFault( $this->m );
		}
		public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
			throw new PageFault( $this->m );
		}
		public function appendAs( string $title, string $line, string $summary, string $actor ): string {
			throw new PageFault( $this->m );
		}
	};
	$xLanding = new Landing( $lCalc, $xPf, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ], $xSink, nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent X', [ 'block' => 'b23' ] );
	$a = $xLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'PAGE FAULT' && ( $a['detail'] ?? '' ) === 'INDEX AND BADGE: page store' && is_int( $a['poll_after'] ?? null )
		&& $fClean( $a ) && !str_contains( $xRaw( $q ), 'Principia Machina' ) && $xSunkHas( $q, $fLeaks[1] ),
		'LF7 PAGE FAULT answers the page\'s class and the fault\'s name, no title and no message; the error channel has the message', $xRaw( $q ) );
	// The access policy's read names its own page: a store faulting on the DRAFT UWC page alone.
	$xDraftPf = new class( $lInner, $pt->draft( $lPx ), $fMsg ) implements PageStore {
		public function __construct( private FileStore $inner, private string $bad, private string $m ) {
		}
		public function get( string $title ): ?string {
			if ( $title === $this->bad ) {
				throw new PageFault( $this->m . ' ' . $title );
			}
			return $this->inner->get( $title );
		}
		public function exists( string $title ): bool {
			return $this->inner->exists( $title );
		}
		public function put( string $title, string $text, string $summary ): void {
			throw new PageFault( $this->m );
		}
		public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
			throw new PageFault( $this->m );
		}
		public function appendAs( string $title, string $line, string $summary, string $actor ): string {
			throw new PageFault( $this->m );
		}
	};
	$xLanding = new Landing( $lCalc, $xDraftPf, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ], $xSink );
	$q = $lTicket( 'PETITION', 'Agent X', [ 'block' => 'b23' ] );
	$a = $xLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'PAGE FAULT' && ( $a['detail'] ?? '' ) === 'DRAFT UWC: page store' && $fClean( $a ),
		'LF7a a fault reading the DRAFT UWC page for the access policy answers that page\'s class, never the badge\'s read before it', $xRaw( $q ) );
	// Under CLOSED the access list's read names its own page: the same store faulting on the ACCESS LIST page alone.
	$xAlPf = new ( $xDraftPf::class )( $lInner, $pt->accessList( $lPx ), $fMsg );
	$lInner->tamper( $tDr, $drText . Blocks::render( Landing::POLICY, 'CLOSED' ) . "\n" );
	$xLanding = new Landing( $lCalc, $xAlPf, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ], $xSink );
	$q = $lTicket( 'PETITION', 'Agent X', [ 'block' => 'b23' ] );
	$a = $xLanding->run( $q );
	$lInner->tamper( $tDr, $drText );
	G::ok( ( $a['refused'] ?? '' ) === 'PAGE FAULT' && ( $a['detail'] ?? '' ) === 'ACCESS LIST: page store' && $fClean( $a ),
		'LF7b a fault reading the ACCESS LIST page of a CLOSED UWC answers that page\'s class, never the DRAFT UWC page\'s read before it', $xRaw( $q ) );
	// JOB FAULT: a store whose fault carries a query, a path and the server's name.
	$xDown = new class( $fMsg ) implements PageStore {
		public function __construct( private string $m ) {
		}
		public function get( string $title ): ?string {
			throw new RuntimeException( $this->m );
		}
		public function exists( string $title ): bool {
			throw new RuntimeException( $this->m );
		}
		public function put( string $title, string $text, string $summary ): void {
			throw new RuntimeException( $this->m );
		}
		public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
			throw new RuntimeException( $this->m );
		}
		public function appendAs( string $title, string $line, string $summary, string $actor ): string {
			throw new RuntimeException( $this->m );
		}
	};
	$xLanding = new Landing( $lCalc, $xDown, $pt, $lTickets, $lSeats, $lCerts, $lConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ], $xSink, nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent X', [ 'block' => 'b24' ] );
	G::refuses( static fn () => $xLanding->run( $q ), RuntimeException::class, 'SELECT', 'LF8 a database fault is rethrown with its query' );
	G::ok( $lAnswer( $q ) === [ 'refused' => 'JOB FAULT', 'class' => 'RuntimeException' ] && $fClean( $lAnswer( $q ) ) && $xSunkHas( $q, 'SELECT * FROM custos_ticket' ),
		'LF9 JOB FAULT answers the class alone; the error channel has the query, the path and the host', $xRaw( $q ) );

	// The job's waits: the base plus the governor's jitter for the draw, `governor jitter {"base", "draw"}`.
	$jConf = array_replace( $lConf, [ 'poll_after' => 40 ] );
	$jDraw = static fn (): array => [ 3, 4 ];
	$jWant = $lCalc->call( 'governor', 'jitter', '{"base":40,"draw":[3,4]}' );
	G::ok( $jWant['exit'] === 0 && $jWant['value'] === 3, 'L82 the Calculator\'s jitter of a wait of 40 s for the draw [3, 4]: 3 s (10 per cent of 40, three quarters)',
		json_encode( $jWant ) );
	$jExpect = 40 + (int)$jWant['value'];
	$jLanding = new Landing( $lCalc, $lStore, $pt, $lTickets, $lSeats, $lCerts, $jConf, static fn (): int => $lNow, $jDraw, nonces: $lNonces );
	$before = $lSnap();
	$q = $lTicket( 'PETITION', 'Agent K', [ 'block' => 'b10' ] );
	$a = $jLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'LOCK HELD' && ( $a['poll_after'] ?? 0 ) === $jExpect && $lSnap() === $before,
		"L83 LOCK HELD answers poll_after the base plus the Calculator's jitter ($jExpect), nothing written", json_encode( $a ) );
	$pfStore = new class implements PageStore {
		/** Asked inside each call when set (L100: is the seat lock held now?); its answers kept in $seen. */
		public ?Closure $probe = null;
		public array $seen = [];
		private function fault(): never {
			if ( $this->probe !== null ) {
				$this->seen[] = ( $this->probe )();
			}
			throw new PageFault( 'the page store faulted (the test\'s fault)' );
		}
		public function get( string $title ): ?string {
			$this->fault();
		}
		public function exists( string $title ): bool {
			$this->fault();
		}
		public function put( string $title, string $text, string $summary ): void {
			$this->fault();
		}
		public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
			$this->fault();
		}
		public function appendAs( string $title, string $line, string $summary, string $actor ): string {
			$this->fault();
		}
	};
	$pfLanding = new Landing( $lCalc, $pfStore, $pt, $lTickets, $lSeats, $lCerts, $jConf, static fn (): int => $lNow, $jDraw, nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent K', [ 'block' => 'b11' ] );
	$a = $pfLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'PAGE FAULT' && ( $a['poll_after'] ?? 0 ) === $jExpect && $lAnswer( $q ) === $a
		&& array_keys( $a ) === [ 'refused', 'detail', 'poll_after' ],
		"L84 PAGE FAULT answers poll_after the base plus the Calculator's jitter ($jExpect), its form kept", json_encode( $a ) );
	// An ADMISSION refusal's wait is the decision's retry_after exactly; the built Calculator's answer for
	// the same request is kept by a wrapper that copies `governor admit`'s line aside.
	$teeFile = "$scratch/land-wrap/tee-admit.json";
	$teeBin = "$scratch/land-wrap/tee";
	@mkdir( dirname( $teeBin ), 0755, true );
	file_put_contents( $teeBin, "#!/bin/sh\nif [ \"\$1\" = governor ] && [ \"\$2\" = admit ]; then\n\t'$lBuilt' \"\$@\" | tee '$teeFile'\n\texit 0\nfi\n"
		. "exec '$lBuilt' \"\$@\"\n" );
	chmod( $teeBin, 0755 );
	$teeCalc = new Calculator( $teeBin, [ 'version' => $lVersion, 'digest' => Calculator::digestOf( $teeBin ) ], new ProcRunner(), 'cli', new AnyResidence() );
	$before = $lSnap();
	$teeLanding = new Landing( $teeCalc, $lStore, $pt, $lTickets, $lSeats, $lCerts, array_replace( $jConf, [ 'agent_stop' => true ] ),
		static fn (): int => $lNow, $jDraw );
	$q = $lTicket( 'PETITION', 'Agent L', [ 'block' => 'b12' ] );
	$a = $teeLanding->run( $q );
	$teeWant = json_decode( (string)@file_get_contents( $teeFile ), true );
	G::ok( ( $a['refused'] ?? '' ) === 'ADMISSION' && is_int( $teeWant['retry_after'] ?? null ) && $a['poll_after'] === $teeWant['retry_after']
		&& $a['decision'] === $teeWant && $lSnap() === $before,
		'L117 an ADMISSION refusal answers poll_after the built Calculator\'s retry_after for the same request, exactly, nothing written', json_encode( [ $a, $teeWant ] ) );
	$before = $lSnap();
	$nrLanding = new Landing( $lWrap( 'noretry', '{"decision":"REFUSED","reason":"AGENT STOP","refusal":"SWITCH"}' ), $lStore, $pt, $lTickets, $lSeats,
		$lCerts, $jConf, static fn (): int => $lNow, $jDraw, nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent L', [ 'block' => 'b12' ] );
	$nrFault = null;
	try {
		$nrLanding->run( $q );
	} catch ( CalculatorFault $e ) {
		$nrFault = $e;
	}
	$a = $lAnswer( $q );
	G::ok( $nrFault !== null && $nrFault->fault === CalculatorFault::ANSWER_FORM && ( $a['refused'] ?? '' ) === 'CALCULATOR FAULT'
		&& !isset( $a['poll_after'] ) && $lSnap() === $before,
		'L118 a refusing decision without retry_after faults the job (answer form), never a configured wait: nothing written', json_encode( $a ) );
	foreach ( [ 'L119' => [ 'negative', '{"decision":"REFUSED","reason":"AGENT STOP","refusal":"SWITCH","retry_after":-1}' ],
		'L120' => [ 'nonarray', 'null' ] ] as $nrLabel => [ $nrName, $nrAdmit ] ) {
		$before = $lSnap();
		$nrLanding = new Landing( $lWrap( "rt-$nrName", $nrAdmit ), $lStore, $pt, $lTickets, $lSeats, $lCerts, $jConf, static fn (): int => $lNow, $jDraw );
		$q = $lTicket( 'PETITION', 'Agent L', [ 'block' => 'b12' ] );
		$nrFault = null;
		try {
			$nrLanding->run( $q );
		} catch ( CalculatorFault $e ) {
			$nrFault = $e;
		}
		$a = $lAnswer( $q );
		G::ok( $nrFault !== null && $nrFault->fault === CalculatorFault::ANSWER_FORM && ( $a['refused'] ?? '' ) === 'CALCULATOR FAULT'
			&& !isset( $a['poll_after'] ) && $lSnap() === $before,
			"$nrLabel an ADMISSION refusal whose decision is $nrName (no retry_after of 0 or more) faults the job (answer form), nothing written", json_encode( $a ) );
	}
	$lSeats->put( 'Agent M', 'agent', 64801, $lNow );
	$q = $lTicket( 'PETITION', 'Agent M', [ 'block' => 'b13' ] );
	$a = $jLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'ADMISSION' && is_int( $a['decision']['retry_after'] ?? null ) && $a['poll_after'] === $a['decision']['retry_after'],
		'L86 an ADMISSION refusal carrying the governor\'s retry_after answers it as it stands', json_encode( $a ) );
	$dfLanding = new Landing( $lCalc, $lStore, $pt, $lTickets, $lSeats, $lCerts, $jConf, static fn (): int => $lNow, nonces: $lNonces );
	$seen = [];
	for ( $k = 0; $k < 6; $k++ ) {
		$q = $lTicket( 'PETITION', "Agent N$k", [ 'block' => 'b14' ] );
		$a = $dfLanding->run( $q );
		$seen[] = $a['poll_after'] ?? -1;
	}
	G::ok( min( $seen ) >= 40 && max( $seen ) <= 44, 'L87 with the default draw (random_int) every LOCK HELD wait lies between the base and the base plus 10 per cent',
		json_encode( $seen ) );
	$z = new Landing( $lCalc, $lStore, $pt, $lTickets, $lSeats, $lCerts, $jConf, static fn (): int => $lNow, static fn (): array => [ 0, 1 ], nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent O', [ 'block' => 'b15' ] );
	G::ok( ( $z->run( $q )['poll_after'] ?? 0 ) === 40, 'L88 a draw of 0 adds no jitter: the base itself' );
	$bad = new Landing( $lCalc, $lStore, $pt, $lTickets, $lSeats, $lCerts, array_replace( $jConf, [ 'governor_off' => true ] ), static fn (): int => $lNow,
		static fn (): array => [ 5, 3 ], nonces: $lNonces );
	$q = $lTicket( 'PETITION', 'Agent P', [ 'block' => 'b16' ] );
	$a = $bad->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'LOCK HELD' && ( $a['poll_after'] ?? 0 ) === 44, 'L89 a draw past 1 is held at 1 by the Calculator: the base plus 10 per cent', json_encode( $a ) );

	// Each ticket landed once: a ticket's job pushed twice (POLL's sweep beside the enqueue), both run.
	$dPushed = [];
	$dOps = new Ops( $lTickets, static function ( int $id ) use ( &$dPushed ): void {
		$dPushed[] = $id;
	}, 30, Ops::MAX_REQUEST_BYTES, 0 );
	$lNow += 3601;
	$dq = $dOps->run( 'PETITION', $lPx, 'Agent Q', [ 'block' => 'b17' ] )['ticket'];
	$dOps->poll( [ 'ticket' => (string)$dq ], 'Agent Q' );
	G::ok( $dPushed === [ $dq, $dq ], 'L90 the ticket\'s job pushed twice: the enqueue and POLL\'s sweep', json_encode( $dPushed ) );
	$first = $lLanding->run( $dPushed[0] );
	$seatsQ = [ $lSeats->get( 'Agent Q', 'agent' ), $lSeats->get( 'Sponsor Q', 'sponsor' ) ];
	$after1 = $lSnap();
	$second = $lLanding->run( $dPushed[1] );
	G::ok( isset( $first['grant'] ) && ( $second['refused'] ?? '' ) === 'NOT QUEUED' && $lSnap() === $after1
		&& [ $lSeats->get( 'Agent Q', 'agent' ), $lSeats->get( 'Sponsor Q', 'sponsor' ) ] === $seatsQ,
		'L91 the first job lands the ticket; the second finds it not QUEUED and writes nothing (no page, no charge)', json_encode( [ $first, $second ] ) );
	G::ok( $lAnswer( $dq ) === $first && ( $lTickets->get( $dq )['state'] ?? '' ) === TicketStore::DONE,
		'L92 the ticket\'s answer is the first job\'s, DONE', json_encode( $lAnswer( $dq ) ) );
	$pd = $dOps->poll( [ 'ticket' => (string)$dq ], 'Agent Q' );
	G::ok( count( $dPushed ) === 2 && json_decode( (string)( $pd['answer'] ?? '' ), true ) === $first, 'L93 POLL of the answered ticket pushes nothing and answers the first landing' );

	// The seat charge atomic across jobs: the admission's read, decision and charge under the account's seat lock.
	$sParams = (string)file_get_contents( "$root/Principia/Parameters.lean" );
	G::ok( preg_match( '/^\s*slotRetryAfter : WallSeconds := ⟨(\d+)⟩$/mu', $sParams, $m ) === 1 && (int)$m[1] === Landing::SLOT_RETRY_AFTER,
		'L94 Landing::SLOT_RETRY_AFTER is Principia/Parameters.lean\'s slotRetryAfter (' . Landing::SLOT_RETRY_AFTER . ' s)', $m[1] ?? '' );
	$sFile = "$scratch/race-seats.json";
	$sA = new FileSeatStore( $sFile );
	$sB = new FileSeatStore( $sFile );
	G::ok( $sA->lock( 'Agent R', 0 ) && !$sB->lock( 'Agent R', 0 ) && $sB->lock( 'Agent S', 0 ) && !$sB->holds( 'Agent R' ),
		'L95 FileSeatStore\'s lock: one account\'s lock held by one holder, a second refused; another account\'s lock taken beside it (no contention)' );
	$sB->unlock( 'Agent S' );
	$sDraw = static fn (): array => [ 3, 4 ];
	$sJitter = $lCalc->call( 'governor', 'jitter', '{"base":' . Landing::SLOT_RETRY_AFTER . ',"draw":[3,4]}' );
	$sTickets = new FileTicketStore( "$scratch/race-tickets-a" );
	$sOps = new Ops( $sTickets, static function ( int $id ): void {
	} );
	$sLanding = new Landing( $lCalc, $pfStore, $pt, $sTickets, $sB, $lCerts, $lConf + [ 'seat_lock_seconds' => 0 ], static fn (): int => $lNow, $sDraw, nonces: $lNonces );
	$q = $sOps->run( 'PETITION', $lPx, 'Agent R', [ 'block' => 'r1' ] )['ticket'];
	$a = $sLanding->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'ADMISSION' && !isset( $a['decision'] ) && $sJitter['exit'] === 0
		&& ( $a['poll_after'] ?? 0 ) === Landing::SLOT_RETRY_AFTER + (int)$sJitter['value'] && str_contains( (string)( $a['detail'] ?? '' ), 'seat lock' ),
		'L96 a seat lock not obtained answers ADMISSION, poll_after SLOT RETRY-AFTER plus the Calculator\'s jitter, no decision asked', json_encode( $a ) );
	G::ok( $sB->get( 'Agent R', 'agent' ) === [ 0, 0 ] && $sB->get( 'Sponsor R', 'sponsor' ) === [ 0, 0 ] && $sA->holds( 'Agent R' ) && !$sB->holds( 'Agent R' ),
		'L97 and nothing is charged; the other holder\'s lock stands' );
	$sA->unlock( 'Agent R' );
	$sFree = static function ( string $account ) use ( $sFile ): bool {
		$probe = new FileSeatStore( $sFile );
		$free = $probe->lock( $account, 0 );
		$probe->unlock( $account );
		return $free;
	};
	$sB->put( 'Agent T', 'agent', 64801, $lNow );
	$sRefuse = new Landing( $lCalc, $pfStore, $pt, $sTickets, $sB, $lCerts, $lConf, static fn (): int => $lNow, $sDraw, nonces: $lNonces );
	$q = $sOps->run( 'PETITION', $lPx, 'Agent T', [ 'block' => 'r2' ] )['ticket'];
	$a = $sRefuse->run( $q );
	G::ok( ( $a['decision']['refusal'] ?? '' ) === 'RATE' && $sB->get( 'Agent T', 'agent' ) === [ 64801, $lNow ] && !$sB->holds( 'Agent T' ) && $sFree( 'Agent T' ),
		'L98 the seat lock released after a refusal (RATE), nothing charged', json_encode( $a ) );
	$sFault = new Landing( $lWrap( 'race-half', '{"charge":{"agent":[1,2]},"decision":"ADMITTED"}' ), $pfStore, $pt, $sTickets, $sB, $lCerts, $lConf,
		static fn (): int => $lNow, $sDraw, nonces: $lNonces );
	$q = $sOps->run( 'PETITION', $lPx, 'Agent U', [ 'block' => 'r3' ] )['ticket'];
	G::refuses( static fn () => $sFault->run( $q ), CalculatorFault::class, 'a charge not of the form', 'L99 a Calculator fault inside the critical section is rethrown' );
	G::ok( !$sB->holds( 'Agent U' ) && $sFree( 'Agent U' ) && $sB->get( 'Agent U', 'agent' ) === [ 0, 0 ], 'L99 and the seat lock is released after it, nothing charged' );
	$sAdmit = new Landing( $lCalc, $pfStore, $pt, $sTickets, $sB, $lCerts, $lConf, static fn (): int => $lNow, $sDraw, nonces: $lNonces );
	$q = $sOps->run( 'PETITION', $lPx, 'Agent V', [ 'block' => 'r4' ] )['ticket'];
	$pfStore->seen = [];
	$pfStore->probe = static fn (): bool => $sB->holds( 'Agent V' ) || !$sFree( 'Agent V' );
	$a = $sAdmit->run( $q );
	$pfStore->probe = null;
	G::ok( ( $a['refused'] ?? '' ) === 'PAGE FAULT' && $sB->get( 'Agent V', 'agent' ) !== [ 0, 0 ] && !$sB->holds( 'Agent V' ) && $sFree( 'Agent V' )
		&& $pfStore->seen !== [] && !in_array( true, $pfStore->seen, true ),
		'L100 the seat lock released before the op: admitted and charged, the op\'s page fault met with the lock free (asked inside the page store\'s own call)',
		json_encode( [ $a, $pfStore->seen ] ) );
	// The charge's two rows one write (DbSeatStore: one atomic section): the sponsor's row faulting leaves the agent's unchanged too.
	$sB->put( 'Agent X', 'agent', 100, $lNow - 10 );
	$sB->put( 'Sponsor X', 'sponsor', 50, $lNow - 10 );
	$sB->beforeRow = static function ( string $account, string $kind ): void {
		if ( $kind === 'sponsor' ) {
			throw new RuntimeException( 'the second row\'s write faulted (the test\'s fault)' );
		}
	};
	$q = $sOps->run( 'PETITION', $lPx, 'Agent X', [ 'block' => 'r5' ] )['ticket'];
	G::refuses( static fn () => $sAdmit->run( $q ), RuntimeException::class, 'the second row', 'L104 a fault on the charge\'s second row is rethrown' );
	$sB->beforeRow = null;
	G::ok( $sB->get( 'Agent X', 'agent' ) === [ 100, $lNow - 10 ] && $sB->get( 'Sponsor X', 'sponsor' ) === [ 50, $lNow - 10 ] && !$sB->holds( 'Agent X' ) && $sFree( 'Agent X' ),
		'L104 and neither row changed (the agent\'s charge not committed without the sponsor\'s); the seat lock released' );
	// What the seat lock's refusals may say: a charge or an unlock faulting with a query, a path and a host name in its message.
	$xSunk = [];
	$sLeak = new Landing( $lCalc, $pfStore, $pt, $sTickets, $sB, $lCerts, $lConf, static fn (): int => $lNow, $sDraw, $xSink );
	$sB->beforeRow = static function ( string $account, string $kind ) use ( $fMsg ): void {
		if ( $kind === 'sponsor' ) {
			throw new RuntimeException( $fMsg );
		}
	};
	$q = $sOps->run( 'PETITION', $lPx, 'Agent Y', [ 'block' => 'r6' ] )['ticket'];
	G::refuses( static fn () => $sLeak->run( $q ), RuntimeException::class, 'SELECT', 'LF10 a charge faulting with a query, a path and a host name is rethrown with them' );
	$sB->beforeRow = null;
	$a = json_decode( (string)( $sTickets->get( $q )['answer'] ?? '' ), true );
	G::ok( $a === [ 'refused' => 'JOB FAULT', 'class' => 'RuntimeException' ] && $fClean( $a ) && $xSunkHas( $q, 'SELECT * FROM custos_ticket' )
		&& !$sB->holds( 'Agent Y' ) && $sFree( 'Agent Y' ),
		'LF10 and the ticket answers JOB FAULT and the class alone; the error channel has the query; the seat lock released',
		(string)( $sTickets->get( $q )['answer'] ?? '' ) );
	// A seat store whose unlock faults: with the charge's own fault in flight, and after a charge that held.
	$sUnlockMsg = 'unlock ' . $fMsg;
	$sBad = new class( $sB, $sUnlockMsg ) implements \Custos\SeatStore {
		public bool $failCharge = false;
		public function __construct( private FileSeatStore $s, private string $m ) {
		}
		public function get( string $account, string $kind ): array {
			return $this->s->get( $account, $kind );
		}
		public function put( string $account, string $kind, int $level, int $since ): void {
			$this->s->put( $account, $kind, $level, $since );
		}
		public function charge( string $account, array $agent, string $sponsorAccount, array $sponsor ): void {
			if ( $this->failCharge ) {
				throw new RuntimeException( 'charge ' . $this->m );
			}
			$this->s->charge( $account, $agent, $sponsorAccount, $sponsor );
		}
		public function lock( string $account, int $seconds ): bool {
			return $this->s->lock( $account, $seconds );
		}
		public function unlock( string $account ): void {
			$this->s->unlock( $account );
			throw new RuntimeException( $this->m );
		}
	};
	$xSunk = [];
	$sBad->failCharge = true;
	$sLeak = new Landing( $lCalc, $pfStore, $pt, $sTickets, $sBad, $lCerts, $lConf, static fn (): int => $lNow, $sDraw, $xSink );
	$q = $sOps->run( 'PETITION', $lPx, 'Agent Z', [ 'block' => 'r7' ] )['ticket'];
	G::refuses( static fn () => $sLeak->run( $q ), RuntimeException::class, 'charge unlock SELECT', 'LF11 an unlock faulting while the charge\'s fault is in flight: the charge\'s fault is the one rethrown' );
	$a = json_decode( (string)( $sTickets->get( $q )['answer'] ?? '' ), true );
	G::ok( $a === [ 'refused' => 'JOB FAULT', 'class' => 'RuntimeException' ] && $fClean( $a ) && $xSunkHas( $q, 'charge unlock SELECT' )
		&& $xSunkHas( $q, $sUnlockMsg ) && $sFree( 'Agent Z' ),
		'LF11 and the ticket answers JOB FAULT and the class alone; the error channel has both messages', (string)( $sTickets->get( $q )['answer'] ?? '' ) );
	$xSunk = [];
	$sBad->failCharge = false;
	$q = $sOps->run( 'PETITION', $lPx, 'Agent Zz', [ 'block' => 'r8' ] )['ticket'];
	G::refuses( static fn () => $sLeak->run( $q ), RuntimeException::class, 'unlock SELECT', 'LF12 an unlock faulting after the charge held is rethrown with its message' );
	$a = json_decode( (string)( $sTickets->get( $q )['answer'] ?? '' ), true );
	G::ok( $a === [ 'refused' => 'JOB FAULT', 'class' => 'RuntimeException' ] && $fClean( $a ) && $xSunkHas( $q, $sUnlockMsg ) && $sFree( 'Agent Zz' ),
		'LF12 and the ticket answers JOB FAULT and the class alone, no query, path or host; the error channel has the message',
		(string)( $sTickets->get( $q )['answer'] ?? '' ) );

	// Two jobs racing for one account's last seat, the second a process of its own (seat_race.php): the second reaches the
	// seat lock while the first sits between its read and its write. Each job has its own ticket store, so the slot count
	// (one in flight per agent) stays out and the bucket alone decides: 64800 of 72000 (twenty seats) leaves one PETITION's two.
	$sRace = static function ( string $tag, bool $locks ) use ( $scratch, $lCalc, $lBuilt, $lVersion, $lDigest, $lNow, $lPx, $pt, $pfStore, $lConf, $sDraw, $lCerts, $lNonces ): array {
		$file = "$scratch/race-$tag.json";
		$first = new FileSeatStore( $file, $locks );
		$first->put( 'Agent W', 'agent', 64800, $lNow );
		$tA = new FileTicketStore( "$scratch/race-$tag-a" );
		$tB = new FileTicketStore( "$scratch/race-$tag-b" );
		$qA = ( new Ops( $tA, static function ( int $id ): void {
		} ) )->run( 'PETITION', $lPx, 'Agent W', [ 'block' => 'w1' ] )['ticket'];
		$qB = ( new Ops( $tB, static function ( int $id ): void {
		} ) )->run( 'PETITION', $lPx, 'Agent W', [ 'block' => 'w2' ] )['ticket'];
		$marker = "$scratch/race-$tag.marker";
		$spec = "$scratch/race-$tag.spec.json";
		file_put_contents( $spec, json_encode( [ 'seats' => $file, 'locks' => $locks, 'tickets' => "$scratch/race-$tag-b", 'ticket' => $qB,
			'binary' => $lBuilt, 'version' => $lVersion, 'digest' => $lDigest, 'now' => $lNow, 'lock_seconds' => 10, 'marker' => $marker,
			'certs' => "$scratch/land-certs.json" ] ) );
		$child = null;
		$pipes = [];
		$out = '';
		$first->afterGet = static function ( string $account, string $kind ) use ( &$child, &$pipes, &$out, $spec, $marker, $locks ): void {
			if ( $kind !== 'agent' || $child !== null ) {
				return;
			}
			$child = proc_open( [ PHP_BINARY, __DIR__ . '/seat_race.php', $spec ], [ 1 => [ 'pipe', 'w' ], 2 => [ 'pipe', 'w' ] ], $pipes );
			$until = microtime( true ) + 30;
			while ( !is_file( $marker ) && microtime( true ) < $until ) {
				usleep( 10000 );
			}
			if ( $locks ) {
				// The second is at the lock: held there while the first decides and writes.
				usleep( 300000 );
			} else {
				// Without the lock the second reads, decides and writes now, between the first's read and its write.
				$out = (string)stream_get_contents( $pipes[1] );
				proc_close( $child );
			}
		};
		$aA = ( new Landing( $lCalc, $pfStore, $pt, $tA, $first, $lCerts, $lConf, static fn (): int => $lNow, $sDraw, nonces: $lNonces ) )->run( $qA );
		if ( $locks && is_resource( $child ) ) {
			$out = (string)stream_get_contents( $pipes[1] );
			proc_close( $child );
		}
		return [ $aA, (array)json_decode( trim( $out ), true ), ( new FileSeatStore( $file ) )->get( 'Agent W', 'agent' ) ];
	};
	[ $rA, $rB, $rBucket ] = $sRace( 'lock', true );
	G::ok( ( $rA['refused'] ?? '' ) === 'PAGE FAULT' && ( $rB['refused'] ?? '' ) === 'ADMISSION' && ( $rB['decision']['refusal'] ?? '' ) === 'RATE'
		&& ( $rB['decision']['payer'] ?? '' ) === 'AGENT',
		'L101 two jobs racing for one account\'s last seat under the lock: the first admitted (its op then met a page fault), the second refused RATE',
		json_encode( [ $rA, $rB ] ) );
	G::ok( $rBucket === [ 72000, $lNow ], 'L102 the bucket charged once: 64800 and one PETITION\'s two seats (7200), at the admission\'s now', json_encode( $rBucket ) );
	[ $nA, $nB, $nBucket ] = $sRace( 'nolock', false );
	G::ok( ( $nA['refused'] ?? '' ) === 'PAGE FAULT' && ( $nB['refused'] ?? '' ) === 'PAGE FAULT' && $nBucket === [ 72000, $lNow ],
		'L103 the same race over a store without the lock admits both on one charge (the lost update the lock prevents): the race is real',
		json_encode( [ $nA, $nB, $nBucket ] ) );

	// Two agents of one Sponsor racing for its last seat: each job has its own ticket store (the slot count stays out),
	// the Sponsor's bucket alone decides, one PETITION's two seats left in it; the second job is a process of its own.
	$vRace = static function ( string $tag, bool $locks ) use ( $scratch, $lBuilt, $lVersion, $lDigest, $lNow, $lPx, $pt, $pfStore, $lConf, $sDraw, $lCerts, $lCalc, $lCertify ): array {
		$lCertify( 'Agent P1', 'Sponsor V' );
		$lCertify( 'Agent P2', 'Sponsor V' );
		$file = "$scratch/race-$tag.json";
		$first = new FileSeatStore( $file, $locks );
		$first->put( 'Sponsor V', 'sponsor', 108000 - 7200, $lNow );
		$tA = new FileTicketStore( "$scratch/race-$tag-a" );
		$tB = new FileTicketStore( "$scratch/race-$tag-b" );
		$qA = ( new Ops( $tA, static function ( int $id ): void {
		} ) )->run( 'PETITION', $lPx, 'Agent P1', [ 'block' => 'v1' ] )['ticket'];
		$qB = ( new Ops( $tB, static function ( int $id ): void {
		} ) )->run( 'PETITION', $lPx, 'Agent P2', [ 'block' => 'v2' ] )['ticket'];
		$marker = "$scratch/race-$tag.marker";
		$spec = "$scratch/race-$tag.spec.json";
		file_put_contents( $spec, json_encode( [ 'seats' => $file, 'locks' => $locks, 'tickets' => "$scratch/race-$tag-b", 'ticket' => $qB,
			'binary' => $lBuilt, 'version' => $lVersion, 'digest' => $lDigest, 'now' => $lNow, 'lock_seconds' => 10, 'marker' => $marker,
			'certs' => "$scratch/land-certs.json" ] ) );
		$child = null;
		$pipes = [];
		$out = '';
		$first->afterGet = static function ( string $account, string $kind ) use ( &$child, &$pipes, &$out, $spec, $marker, $locks ): void {
			if ( $kind !== 'sponsor' || $child !== null ) {
				return;
			}
			$child = proc_open( [ PHP_BINARY, __DIR__ . '/seat_race.php', $spec ], [ 1 => [ 'pipe', 'w' ], 2 => [ 'pipe', 'w' ] ], $pipes );
			$until = microtime( true ) + 30;
			while ( !is_file( $marker ) && microtime( true ) < $until ) {
				usleep( 10000 );
			}
			if ( $locks ) {
				// The second holds its own agent's lock and waits at the Sponsor's, which the first holds.
				usleep( 300000 );
			} else {
				$out = (string)stream_get_contents( $pipes[1] );
				proc_close( $child );
			}
		};
		$aA = ( new Landing( $lCalc, $pfStore, $pt, $tA, $first, $lCerts, $lConf, static fn (): int => $lNow, $sDraw ) )->run( $qA );
		if ( $locks && is_resource( $child ) ) {
			$out = (string)stream_get_contents( $pipes[1] );
			proc_close( $child );
		}
		return [ $aA, (array)json_decode( trim( $out ), true ), ( new FileSeatStore( $file ) )->get( 'Sponsor V', 'sponsor' ) ];
	};
	[ $vA, $vB, $vBucket ] = $vRace( 'sponsor', true );
	$vAdmitted = static fn ( array $r ): bool => ( $r['refused'] ?? '' ) === 'PAGE FAULT';
	G::ok( $vAdmitted( $vA ) && ( $vB['refused'] ?? '' ) === 'ADMISSION' && ( $vB['decision']['refusal'] ?? '' ) === 'RATE' && ( $vB['decision']['payer'] ?? '' ) === 'SPONSOR',
		'L105 two agents of one Sponsor racing for its last seat under the locks: exactly one admitted, the other refused RATE, the payer SPONSOR', json_encode( [ $vA, $vB ] ) );
	G::ok( $vBucket === [ 108000, $lNow ], 'L106 the Sponsor\'s bucket charged once', json_encode( $vBucket ) );
	[ $nvA, $nvB ] = $vRace( 'sponsor-nolock', false );
	G::ok( $vAdmitted( $nvA ) && $vAdmitted( $nvB ), 'L107 the same race over a store without the locks admits both (the lost update the Sponsor\'s lock prevents): the race is real', json_encode( [ $nvA, $nvB ] ) );

	// The certificate: admission reads the agent's Sponsor from custos_certificate. A Calculator that logs every
	// call it is asked, so "the governor not asked" is read from the log; seats and tickets of their own.
	$cLog = "$scratch/cert-calls.log";
	$cBin = "$scratch/land-wrap/cert-log";
	file_put_contents( $cBin, "#!/bin/sh\nprintf '%s %s\\n' \"\$1\" \"\$2\" >> '$cLog'\nexec '$lBuilt' \"\$@\"\n" );
	chmod( $cBin, 0755 );
	$cCalc = new Calculator( $cBin, [ 'version' => $lVersion, 'digest' => Calculator::digestOf( $cBin ) ], new ProcRunner(), 'cli', new AnyResidence() );
	$cSeats = new FileSeatStore( "$scratch/cert-seats.json" );
	$cLocked = [];
	$cSeats->beforeLock = static function ( string $account ) use ( &$cLocked ): void {
		$cLocked[] = $account;
	};
	$cFree = static function ( string $account ) use ( $scratch ): bool {
		$probe = new FileSeatStore( "$scratch/cert-seats.json" );
		$free = $probe->lock( $account, 0 );
		$probe->unlock( $account );
		return $free;
	};
	$cTickets = new FileTicketStore( "$scratch/cert-tickets" );
	$cOps = new Ops( $cTickets, static function ( int $id ): void {
	} );
	$cLanding = new Landing( $cCalc, $pfStore, $pt, $cTickets, $cSeats, $lCerts, $lConf, static fn (): int => $lNow, $sDraw );
	$cGoverned = static fn (): bool => is_file( $cLog ) && str_contains( (string)file_get_contents( $cLog ), 'governor ' );
	$cRefused = static function ( string $agent, string $block ) use ( $cOps, $cLanding, $cLog, $cGoverned, $cSeats, &$cLocked, $pfStore, $lPx, $lSponsorOf ): array {
		@unlink( $cLog );
		$cLocked = [];
		$pfStore->seen = [];
		$pfStore->probe = static fn (): bool => true;
		$a = $cLanding->run( $cOps->run( 'PETITION', $lPx, $agent, [ 'block' => $block ] )['ticket'] );
		$pfStore->probe = null;
		$ok = $a === [ 'refused' => 'ADMISSION', 'detail' => Landing::NO_CERTIFICATE ] && !$cGoverned() && is_file( $cLog ) && $cLocked === []
			&& $cSeats->get( $agent, 'agent' ) === [ 0, 0 ] && $cSeats->get( $lSponsorOf( $agent ), 'sponsor' ) === [ 0, 0 ] && $pfStore->seen === [];
		return [ $ok, json_encode( [ $a, $cLocked, is_file( $cLog ) ? file_get_contents( $cLog ) : '' ] ) ];
	};
	[ $ok, $why ] = $cRefused( 'Agent Nocert', 'c1' );
	G::ok( $ok, 'LC1 an agent with no certificate is refused ADMISSION "' . Landing::NO_CERTIFICATE . '" before the governor is asked; no seat lock, nothing charged, no page read', $why );
	$lCertify( 'Agent Susp', 'Sponsor Susp', 'SUSPENDED' );
	$lCertify( 'Agent Revk', 'Sponsor Revk', 'REVOKED' );
	[ $ok, $why ] = $cRefused( 'Agent Susp', 'c2' );
	[ $ok2, $why2 ] = $cRefused( 'Agent Revk', 'c3' );
	G::ok( $ok && $ok2, 'LC2 an agent whose certificate is SUSPENDED or REVOKED is refused the same way, nothing charged', "$why $why2" );
	// Re-certified ACTIVE, the same agent is admitted: the refusal was the certificate's alone.
	$lCertify( 'Agent Susp', 'Sponsor Susp' );
	$a = $cLanding->run( $cOps->run( 'PETITION', $lPx, 'Agent Susp', [ 'block' => 'c4' ] )['ticket'] );
	G::ok( ( $a['refused'] ?? '' ) === 'PAGE FAULT' && $cSeats->get( 'Agent Susp', 'agent' ) === [ 7200, $lNow ]
		&& $cSeats->get( 'Sponsor Susp', 'sponsor' ) === [ 7200, $lNow ] && $cSeats->get( 'Agent Susp', 'sponsor' ) === [ 0, 0 ],
		'LC3 an ACTIVE certificate admits: the agent\'s bucket charged on its own account, the sponsor\'s on the Sponsor\'s account, none on the agent\'s',
		json_encode( [ $a, $cSeats->get( 'Agent Susp', 'agent' ), $cSeats->get( 'Sponsor Susp', 'sponsor' ) ] ) );
	G::ok( $cLocked === [ 'Agent Susp', 'Sponsor Susp' ] && $cFree( 'Agent Susp' ) && $cFree( 'Sponsor Susp' ) && !$cSeats->holds( 'Sponsor Susp' ),
		'LC4 the agent\'s and the Sponsor\'s seat locks taken in the order of their names, both released', json_encode( $cLocked ) );
	// Two agents of one Sponsor share its bucket: one PETITION's two seats left in the Sponsor's burst.
	$lCertify( 'Agent P1', 'Sponsor P' );
	$lCertify( 'Agent P2', 'Sponsor P' );
	$cSeats->put( 'Sponsor P', 'sponsor', 108000 - 7200, $lNow );
	$a1 = $cLanding->run( $cOps->run( 'PETITION', $lPx, 'Agent P1', [ 'block' => 'c5' ] )['ticket'] );
	$a2 = $cLanding->run( $cOps->run( 'PETITION', $lPx, 'Agent P2', [ 'block' => 'c6' ] )['ticket'] );
	G::ok( ( $a1['refused'] ?? '' ) === 'PAGE FAULT' && ( $a2['refused'] ?? '' ) === 'ADMISSION' && ( $a2['decision']['refusal'] ?? '' ) === 'RATE'
		&& ( $a2['decision']['payer'] ?? '' ) === 'SPONSOR',
		'LC5 two agents of one Sponsor share its seat cap: the first admitted on its last seats, the second, whose own bucket is empty, refused RATE, the payer SPONSOR',
		json_encode( [ $a1, $a2 ] ) );
	G::ok( $cSeats->get( 'Sponsor P', 'sponsor' ) === [ 108000, $lNow ] && $cSeats->get( 'Agent P1', 'agent' ) === [ 7200, $lNow ]
		&& $cSeats->get( 'Agent P2', 'agent' ) === [ 0, 0 ],
		'LC6 the Sponsor\'s bucket charged once, by the first agent; the second agent\'s bucket untouched',
		json_encode( [ $cSeats->get( 'Sponsor P', 'sponsor' ), $cSeats->get( 'Agent P1', 'agent' ), $cSeats->get( 'Agent P2', 'agent' ) ] ) );
	// The Sponsor's slots count the tickets in flight of every agent bound to it: two IN WORK, one each of two agents.
	$lCertify( 'Agent Q1', 'Sponsor Q' );
	$lCertify( 'Agent Q2', 'Sponsor Q' );
	$lCertify( 'Agent Q3', 'Sponsor Q' );
	$cTickets->claim( $cOps->run( 'PETITION', $lPx, 'Agent Q1', [ 'block' => 'c7' ] )['ticket'] );
	$cTickets->claim( $cOps->run( 'PETITION', $lPx, 'Agent Q2', [ 'block' => 'c8' ] )['ticket'] );
	$a = $cLanding->run( $cOps->run( 'PETITION', $lPx, 'Agent Q3', [ 'block' => 'c9' ] )['ticket'] );
	G::ok( ( $a['refused'] ?? '' ) === 'ADMISSION' && ( $a['decision']['refusal'] ?? '' ) === 'SLOTS'
		&& $cSeats->get( 'Agent Q3', 'agent' ) === [ 0, 0 ] && $cSeats->get( 'Sponsor Q', 'sponsor' ) === [ 0, 0 ],
		'LC7 the Sponsor\'s slots count every bound agent\'s tickets in flight: a third agent with none of its own refused SLOTS, nothing charged',
		json_encode( $a ) );
	$a = $cLanding->run( $cOps->run( 'PETITION', $lPx, 'Agent R1', [ 'block' => 'c10' ] )['ticket'] );
	$lCertify( 'Agent R1', 'Sponsor R1' );
	$a2 = $cLanding->run( $cOps->run( 'PETITION', $lPx, 'Agent R1', [ 'block' => 'c11' ] )['ticket'] );
	G::ok( ( $a['refused'] ?? '' ) === 'ADMISSION' && ( $a2['refused'] ?? '' ) === 'PAGE FAULT',
		'LC8 an agent of another Sponsor is not counted in Sponsor Q\'s slots: refused with no certificate, admitted once certified', json_encode( [ $a, $a2 ] ) );

	// The agent's seat lock obtained, the Sponsor's held by another job: the agent's lock is released, nothing charged.
	$lCertify( 'Agent LS', 'Sponsor LS' );
	$lsHolder = new FileSeatStore( "$scratch/cert-seats.json" );
	$lsHeld = $lsHolder->lock( 'Sponsor LS', 0 );
	$lsLanding = new Landing( $cCalc, $pfStore, $pt, $cTickets, $cSeats, $lCerts, $lConf + [ 'seat_lock_seconds' => 0 ], static fn (): int => $lNow, $sDraw );
	$cLocked = [];
	$a = $lsLanding->run( $cOps->run( 'PETITION', $lPx, 'Agent LS', [ 'block' => 'c12' ] )['ticket'] );
	G::ok( $lsHeld && ( $a['refused'] ?? '' ) === 'ADMISSION' && str_contains( (string)( $a['detail'] ?? '' ), "the account's sponsor's seat lock" )
		&& $cLocked === [ 'Agent LS', 'Sponsor LS' ] && !$cSeats->holds( 'Agent LS' ) && $cFree( 'Agent LS' ) && $lsHolder->holds( 'Sponsor LS' )
		&& $cSeats->get( 'Agent LS', 'agent' ) === [ 0, 0 ] && $cSeats->get( 'Sponsor LS', 'sponsor' ) === [ 0, 0 ],
		'LC9 the agent\'s seat lock obtained and the Sponsor\'s held by another job: the agent\'s lock released, the answer names "the account\'s sponsor\'s seat lock", nothing charged; the other holder\'s lock stands',
		json_encode( [ $a, $cLocked ] ) );
	$lsHolder->unlock( 'Sponsor LS' );

	// A certificate store whose get() throws: admission fails closed (no lock held, nothing charged, the job faults).
	$lfCerts = new class implements CertificateStore {
		public function get( string $agent ): ?array {
			throw new RuntimeException( 'the certificate store faulted (the test\'s fault)' );
		}
		public function agentsOf( string $sponsor ): array {
			throw new RuntimeException( 'the certificate store faulted (the test\'s fault)' );
		}
		public function put( array $row ): void {
			throw new RuntimeException( 'the certificate store faulted (the test\'s fault)' );
		}
	};
	$xSunk = [];
	$cLocked = [];
	$lfLanding = new Landing( $cCalc, $pfStore, $pt, $cTickets, $cSeats, $lfCerts, $lConf, static fn (): int => $lNow, $sDraw, $xSink );
	@unlink( $cLog );
	$q = $cOps->run( 'PETITION', $lPx, 'Agent LF', [ 'block' => 'c13' ] )['ticket'];
	G::refuses( static fn () => $lfLanding->run( $q ), RuntimeException::class, 'the certificate store faulted', 'LC10 a certificate store whose get() throws faults the job, the fault rethrown' );
	$lfAnswer = (array)json_decode( (string)( $cTickets->get( $q )['answer'] ?? '' ), true );
	G::ok( $lfAnswer === [ 'refused' => 'JOB FAULT', 'class' => 'RuntimeException' ] && $cLocked === [] && !$cGoverned()
		&& $cSeats->get( 'Agent LF', 'agent' ) === [ 0, 0 ] && $cSeats->get( 'Sponsor LF', 'sponsor' ) === [ 0, 0 ] && $cFree( 'Agent LF' ) && $cFree( 'Sponsor LF' ),
		'LC10 and admission fails closed: the ticket answers JOB FAULT, no seat lock taken, the governor not asked, nothing charged',
		json_encode( [ $lfAnswer, $cLocked ] ) );

	// ---- N: the execution challenge (TPS 5.3.19), both of Custos's sides, on the built pcalc -------------------
	echo "N: the execution challenge\n";
	$nCorpus = json_decode( (string)file_get_contents( "$root/vectors/challenge_corpus.json" ), true );
	$nShow = static function ( mixed $v ): string {
		if ( is_bool( $v ) ) {
			return $v ? 'true' : 'false';
		}
		return '[' . implode( ',', array_map( 'strval', (array)$v ) ) . ']';
	};
	$nCases = is_array( $nCorpus['cases'] ?? null ) ? $nCorpus['cases'] : [];
	G::ok( count( $nCases ) === 21, 'N0 the corpus vectors/challenge_corpus.json holds 21 cases', (string)count( $nCases ) );
	foreach ( $nCases as $i => $c ) {
		$in = $c['input'] ?? [];
		switch ( $c['fn'] ?? '' ) {
			case 'challenge_preimage':
				$got = Challenge::preimage( $lCalc, $in['nonce'] ?? null );
				break;
			case 'challenge_response':
				$got = Challenge::response( $lCalc, $in['nonce'] ?? null );
				break;
			default:
				$got = Challenge::verify( $lCalc, $in['nonce'] ?? null, $in['response'] ?? null );
		}
		G::ok( $nShow( $got ) === ( $c['expect'] ?? '' ), 'N' . ( $i + 1 ) . ' corpus ' . ( $c['id'] ?? '?' ) . ' through pcalc digest from PHP',
			$nShow( $got ) );
	}

	// A UWC of its own, seeded as L1 seeds RR.
	$nPx = 'RN';
	$seed = new PageWriter( $lStore, $pt );
	$seed->begin( $nPx, 'seed' );
	$seed->put( $pt->draft( $nPx ), Blocks::render( 'draft', $lCanon ) . "\n" );
	foreach ( PageTitles::ZONES as $zone ) {
		$seed->put( $pt->researchAssembly( $nPx, $zone ), Blocks::render( 'assembly', $lCanon ) . "\n" );
	}
	$seed->put( $pt->registerVolume( $nPx, 1 ), PageTexts::register( $nPx, 1, '[]' ) );
	$seed->put( $pt->lock( $nPx ), PageTexts::lock( $nPx, null, null, null, null ) );
	$seed->put( $pt->index( $nPx ), PageTexts::badge( $nPx, [ 'last_push' => null, 'last_release' => null,
		'calculator_version' => $lVersion, 'calculator_digest' => $lDigest, 'record_count' => 0, 'research_assembly' => $lRaDigest ], false, 1 ) );
	$seed->commit();
	$nNow = $lNow + 86400;
	$nTickets = new FileTicketStore( "$scratch/n-tickets" );
	$nSeats = new FileSeatStore( "$scratch/n-seats.json" );
	$nStore = new FileNonceStore( "$scratch/n-nonces.json" );
	$nLanding = new Landing( $lCalc, $lStore, $pt, $nTickets, $nSeats, $lCerts, $lConf, static function () use ( &$nNow ): int {
		return $nNow += 60;
	}, static fn (): array => [ 0, 1 ], nonces: $nStore );
	$nOps = new Ops( $nTickets, static function ( int $id ): void {
	} );
	$nRun = static function ( string $op, string $account, array $params ) use ( $nOps, $nLanding, $nPx ): array {
		return $nLanding->run( $nOps->run( $op, $nPx, $account, $params )['ticket'] );
	};
	$nRight = static fn ( string $nonce ): string => Challenge::response( $lCalc, $nonce )[1];
	$nReg = $pt->registerVolume( $nPx, 1 );
	$nRegister = static fn (): array => (array)json_decode( (string)PageTexts::readRegister( $lInner->get( $nReg ) ), true );
	$nRec = static fn ( string $id ): string => str_replace( 'RR-2', $id, $assumption );

	$a = $nRun( 'PETITION', 'Agent N', [ 'block' => 'n1' ] );
	$n1 = (string)( $a['challenge'] ?? '' );
	G::ok( isset( $a['grant'] ) && Challenge::nonceOk( $n1 ), 'N22 a granted PETITION answers a nonce of 32 lowercase hexadecimal characters, `challenge`', json_encode( $a ) );
	G::ok( $nStore->peek( 'Agent N', $nPx ) === $n1, 'N23 the nonce is the account\'s outstanding one on the UWC, in the nonce table' );
	G::ok( !isset( $a['execution'] ), 'N24 a PETITION attests nothing: no `execution` member' );

	$before = $lSnap();
	$a = $nRun( 'PUSH', 'Agent N', [ 'records' => '[' . $nRec( 'RN-1' ) . ']', 'challenge_response' => str_repeat( '0', 64 ) ] );
	$n2 = (string)( $a['challenge'] ?? '' );
	G::ok( ( $a['refused'] ?? '' ) === 'CHALLENGE' && ( $a['execution'] ?? '' ) === 'REASONED' && str_contains( (string)( $a['detail'] ?? '' ), 'wrong' ),
		'N25 a wrong response is attested REASONED and the PUSH refused CHALLENGE', json_encode( $a ) );
	G::ok( $lSnap() === $before && $nRegister() === [], 'N26 a REASONED PUSH lands nothing: every presented value refused, no page written' );
	G::ok( Challenge::nonceOk( $n2 ) && $n2 !== $n1 && $nStore->peek( 'Agent N', $nPx ) === $n2,
		'N27 the nonce is consumed and a fresh one issued, carried by the refusal' );

	$a = $nRun( 'PUSH', 'Agent N', [ 'records' => '[' . $nRec( 'RN-1' ) . ']', 'challenge_response' => $nRight( $n1 ) ] );
	$n3 = (string)( $a['challenge'] ?? '' );
	G::ok( ( $a['refused'] ?? '' ) === 'CHALLENGE' && ( $a['execution'] ?? '' ) === 'REASONED' && $nRegister() === [],
		'N28 a nonce used twice: the right response to a consumed nonce is REASONED, nothing landed', json_encode( $a ) );

	$a = $nRun( 'PUSH', 'Agent N', [ 'records' => '[' . $nRec( 'RN-1' ) . ']', 'challenge_response' => $nRight( $n3 ) ] );
	$n4 = (string)( $a['challenge'] ?? '' );
	G::ok( ( $a['execution'] ?? '' ) === 'EXECUTED' && array_column( $a['landed'] ?? [], 'id' ) === [ 'RN-1' ],
		'N29 the right response, computed by the Calculator, is attested EXECUTED and the PUSH lands', json_encode( $a ) );
	G::ok( count( $nRegister() ) === 1 && Challenge::nonceOk( $n4 ) && $n4 !== $n3 && $nStore->peek( 'Agent N', $nPx ) === $n4,
		'N30 the landing\'s answer carries the next nonce, the outstanding one' );

	$before = $lSnap();
	$a = $nRun( 'PUSH', 'Agent N', [ 'records' => '[' . $nRec( 'RN-2' ) . ']' ] );
	$n5 = (string)( $a['challenge'] ?? '' );
	G::ok( ( $a['refused'] ?? '' ) === 'CHALLENGE' && ( $a['execution'] ?? '' ) === 'REASONED' && str_contains( (string)( $a['detail'] ?? '' ), 'missing' )
		&& $lSnap() === $before, 'N31 an absent response is REASONED, nothing landed', json_encode( $a ) );
	$a = $nRun( 'PUSH', 'Agent N', [ 'records' => '[' . $nRec( 'RN-2' ) . ']', 'challenge_response' => strtoupper( $nRight( $n5 ) ) ] );
	$n6 = (string)( $a['challenge'] ?? '' );
	G::ok( ( $a['refused'] ?? '' ) === 'CHALLENGE' && str_contains( (string)( $a['detail'] ?? '' ), 'not 64 lowercase' ) && $lSnap() === $before,
		'N32 a response not in its form (uppercase) is REASONED, nothing landed', json_encode( $a ) );

	$nStore->tamper( 'Agent N', $nPx, '0123456789ABCDEF0123456789ABCDEF' );
	$a = $nRun( 'PUSH', 'Agent N', [ 'records' => '[' . $nRec( 'RN-2' ) . ']', 'challenge_response' => $nRight( $n6 ) ] );
	$n7 = (string)( $a['challenge'] ?? '' );
	G::ok( ( $a['refused'] ?? '' ) === 'CHALLENGE' && str_starts_with( (string)( $a['detail'] ?? '' ), Challenge::BAD_NONCE )
		&& !str_contains( json_encode( $a ), '0123456789ABCDEF' ) && $lSnap() === $before,
		'N33 an outstanding nonce not in its form is refused in the answer\'s words, never quoted, nothing landed', json_encode( $a ) );

	$nStore->take( 'Agent N', $nPx );
	$a = $nRun( 'PUSH', 'Agent N', [ 'records' => '[' . $nRec( 'RN-2' ) . ']', 'challenge_response' => $nRight( $n7 ) ] );
	$n8 = (string)( $a['challenge'] ?? '' );
	G::ok( ( $a['refused'] ?? '' ) === 'CHALLENGE' && str_contains( (string)( $a['detail'] ?? '' ), 'no challenge is outstanding' ) && $lSnap() === $before,
		'N34 no nonce outstanding: REASONED, nothing landed', json_encode( $a ) );

	$bad = str_replace( '"PROPOSITION":"The mass is constant."', '"PROPOSITION":""', $nRec( 'RN-2' ) );
	$a = $nRun( 'PUSH', 'Agent N', [ 'records' => "[$bad]", 'challenge_response' => $nRight( $n8 ) ] );
	$n9 = (string)( $a['challenge'] ?? '' );
	G::ok( ( $a['refused'] ?? '' ) === 'RECORD CHECK' && ( $a['execution'] ?? '' ) === 'EXECUTED' && Challenge::nonceOk( $n9 ) && $n9 !== $n8,
		'N35 a PUSH refused after its challenge passed carries EXECUTED and the next nonce', json_encode( $a ) );

	$a = $nRun( 'PUSH', 'Agent O', [ 'records' => '[' . $nRec( 'RN-2' ) . ']', 'challenge_response' => $nRight( $n9 ) ] );
	G::ok( ( $a['refused'] ?? '' ) === 'NOT HOLDER' && !isset( $a['challenge'] ) && !isset( $a['execution'] ) && $nStore->peek( 'Agent N', $nPx ) === $n9,
		'N36 a PUSH refused before the challenge (not the holder) consumes no nonce and answers none', json_encode( $a ) );

	$a = $nRun( 'PUSH', 'Agent N', [ 'records' => '[' . $nRec( 'RN-2' ) . ']', 'challenge_response' => $nRight( $n9 ) ] );
	G::ok( ( $a['execution'] ?? '' ) === 'EXECUTED' && count( $nRegister() ) === 2, 'N37 the next nonce answered, the next PUSH lands', json_encode( $a ) );

	G::ok( o_code( static fn () => $nOps->run( 'PUSH', $nPx, 'Agent N', [ 'records' => '[1]', 'challenge_response' => [ 'x' ] ] ) ) === 'custos-shape',
		'N38 GA1: a challenge_response that is not one string is refused custos-shape' );

	// A Landing without a nonce store checks the challenge all the same: a nonce another object issued is not outstanding there.
	$nMem = new Landing( $lCalc, $lStore, $pt, $nTickets, $nSeats, $lCerts, $lConf, static function () use ( &$nNow ): int {
		return $nNow += 60;
	}, static fn (): array => [ 0, 1 ] );
	$q = $nOps->run( 'PUSH', $nPx, 'Agent N', [ 'records' => '[' . $nRec( 'RN-3' ) . ']', 'challenge_response' => $nRight( (string)$nStore->peek( 'Agent N', $nPx ) ) ] )['ticket'];
	$a = $nMem->run( $q );
	G::ok( ( $a['refused'] ?? '' ) === 'CHALLENGE' && ( $a['execution'] ?? '' ) === 'REASONED' && count( $nRegister() ) === 2,
		'N39 a Landing without a nonce store refuses a PUSH whose nonce it never issued, REASONED (no unchecked path)', json_encode( $a ) );

	$nTwo = new FileNonceStore( "$scratch/n-nonces.json" );
	$nStore->put( 'Agent Z', $nPx, str_repeat( 'c', 32 ), 1 );
	G::ok( $nTwo->take( 'Agent Z', $nPx ) === str_repeat( 'c', 32 ) && $nStore->take( 'Agent Z', $nPx ) === null,
		'N40 the nonce store over one table: of two takes of one nonce, by two objects, one gets it' );

	$nLand = (string)file_get_contents( "$root/custos/includes/Landing.php" );
	$nChal = (string)file_get_contents( "$root/custos/includes/Challenge.php" );
	G::ok( substr_count( $nLand, 'bin2hex( random_bytes( 16 ) )' ) === 1 && preg_match( '/\b(mt_rand|rand|uniqid|lcg_value)\s*\(/', $nLand ) !== 1
		&& preg_match( '/\b(hash|sha1|md5|hash_hmac|crc32)\s*\(/', $nChal . $nLand ) !== 1 && str_contains( $nChal, "'digest', \$fn" ),
		'N41 the nonce drawn by random_bytes(16) alone; no digest computed in Challenge.php or Landing.php but by pcalc digest' );
}

// ---- G: the governor's meter, the budget roll-up, the PRE-GATE, STATUS, INQUIRE, HEARTBEAT --------

require_once "$root/custos/pregate.php";

// The traffic record's two writers on the store alone, no Calculator: a step that leaves the
// record unchanged writes nothing, a changed step writes record, stage and time under its compare and set.
$gU = new MemMeterStore();
$gU->putTraffic( 'Agent Same', 'r1', 'NORMAL', 10 );
$gUstaged = $gU->stageTraffic( 'Agent Same', 'r1', 'THROTTLED', 20 );
$gUkept = $gU->casTraffic( 'Agent Same', 'r1', 'r1', 'NORMAL', 30 );
$gU->putTraffic( 'Agent Gone', 'r1', 'NORMAL', 10 );
$gU->casTraffic( 'Agent Gone', 'r1', 'r2', 'PENALIZED', 40 );
$gUmiss = $gU->casTraffic( 'Agent Gone', 'r1', 'r1', 'NORMAL', 50 );
G::ok( $gUstaged && $gUkept && $gU->traffic( 'Agent Same' ) === [ 'record' => 'r1', 'stage' => 'THROTTLED', 'time' => 20 ]
	&& !$gUmiss && $gU->traffic( 'Agent Gone' ) === [ 'record' => 'r2', 'stage' => 'PENALIZED', 'time' => 40 ],
	'G74 a step that leaves the record unchanged writes nothing: the stage and time stay as the roll-up last wrote them; on a record changed since its read it is a miss, nothing written',
	json_encode( [ $gUstaged, $gUkept, $gUmiss, $gU->traffic( 'Agent Same' ), $gU->traffic( 'Agent Gone' ) ] ) );
$gV = new MemMeterStore();
$gV->putTraffic( 'Agent Moves', 'r1', 'NORMAL', 10 );
$gV->stageTraffic( 'Agent Moves', 'r1', 'THROTTLED', 20 );
$gVcas = $gV->casTraffic( 'Agent Moves', 'r1', 'r2', 'PENALIZED', 60 );
$gVafter = $gV->traffic( 'Agent Moves' );
$gVlate = $gV->casTraffic( 'Agent Moves', 'r1', 'r3', 'NORMAL', 70 );
G::ok( $gVcas && $gVafter === [ 'record' => 'r2', 'stage' => 'PENALIZED', 'time' => 60 ] && !$gVlate && $gV->traffic( 'Agent Moves' ) === $gVafter,
	'G75 a step that changes the record writes record, stage and time together under its compare and set; a step on the record it replaced writes none of them',
	json_encode( [ $gVcas, $gVafter, $gVlate, $gV->traffic( 'Agent Moves' ) ] ) );

if ( !isset( $lCalc ) ) {
	G::skip( 'G the governor\'s meter', 'no built pcalc in this clone; section G needs the Calculator itself' );
} else {
	// The lane table: custos/lanes.json, every kind's lane as the built pcalc answers it.
	$gLanes = Meter::lanes();
	$gMiss = [];
	foreach ( $gLanes as $k => $n ) {
		$a = $lCalc->call( 'governor', 'lane', json_encode( [ 'kind' => (string)$k ] ) );
		if ( ( $a['value']['number'] ?? null ) !== $n ) {
			$gMiss[] = $k;
		}
	}
	G::ok( count( $gLanes ) === 24 && $gMiss === [], 'G1 custos/lanes.json: the 24 governed kinds, each lane the built pcalc\'s', implode( ', ', $gMiss ) );
	G::ok( $gLanes['STATUS'] === 3 && $gLanes['INQUIRE'] === 2 && $gLanes['HEARTBEAT'] === 2 && $gLanes['ANONYMOUS READ'] === 6, 'G2 the ops\' lanes: STATUS 3, INQUIRE 2, HEARTBEAT 2, an anonymous read 6' );

	// GA0 and GA9: the meter's rows.
	G::ok( Meter::kind( true, true, 'pma', 'PETITION' ) === 'PETITION' && Meter::kind( true, true, 'pma', 'POLL' ) === 'POLL OTHER'
		&& Meter::kind( true, true, 'pma', 'STATUS' ) === 'STATUS', 'G3 an op of action=pma is metered as its kind (POLL as POLL OTHER)' );
	G::ok( Meter::kind( true, true, 'query', null ) === 'AGENT CORE READ' && Meter::kind( true, false, null, null ) === 'SIGNED IN USER'
		&& Meter::kind( false, false, 'query', null ) === 'ANONYMOUS READ' && Meter::kind( false, false, 'pma', 'NOPE' ) === 'ANONYMOUS READ',
		'G4 an agent\'s other call AGENT CORE READ, a signed-in account SIGNED IN USER, an anonymous request ANONYMOUS READ' );
	$gStart = [ 'time' => 1793000000, 'wall_ms' => 5000, 'cpu' => 200 ];
	$gEnd = [ 'wall_ms' => 5750, 'cpu' => 450, 'memory' => 4194304, 'bytes' => 812, 'landed' => 0 ];
	$gRow = Meter::row( $gLanes, 'PETITION', 'Agent G', '', $gStart, $gEnd, 10, 7 );
	G::ok( $gRow !== null && $gRow['cpu'] === 250 && $gRow['wall'] === 750 && $gRow['memory'] === 4194304 && $gRow['bytes'] === 812,
		'G5 a row: CPU and wall in thousandths of a second, peak memory, response bytes', json_encode( $gRow ) );
	G::ok( $gRow['lane'] === 3 && $gRow['weight'] === 1 && $gRow['network'] === '' && $gRow['time'] === 1793000000,
		'G6 an account\'s row: its lane, weight 1 (never sampled), no network, the start\'s time' );
	G::ok( Meter::row( $gLanes, 'ANONYMOUS READ', '', '192.0.2.0/24', $gStart, $gEnd, 10, 3 ) === null, 'G7 an anonymous read the sample passes over writes no row' );
	$gAnon = Meter::row( $gLanes, 'ANONYMOUS READ', '', '192.0.2.0/24', $gStart, $gEnd, 10, 0 );
	G::ok( $gAnon !== null && $gAnon['weight'] === 10 && $gAnon['lane'] === 6 && $gAnon['network'] === '192.0.2.0/24', 'G8 an anonymous read kept stands for the sample, weight 10, with its network' );
	G::ok( Meter::network( '192.0.2.77' ) === '192.0.2.0/24' && Meter::network( '2001:db8:1:2::5' ) === '2001:db8:1::/48' && Meter::network( 'x' ) === '',
		'G9 an anonymous network: an IPv4 /24, an IPv6 /48, nothing of a non-address' );
	$gNeg = Meter::row( $gLanes, 'PUSH', 'Agent G', '', $gStart, [ 'wall_ms' => 1, 'cpu' => 1, 'memory' => -1, 'bytes' => -5, 'landed' => 3 ], 1, 0 );
	G::ok( $gNeg['cpu'] === 0 && $gNeg['wall'] === 0 && $gNeg['memory'] === 0 && $gNeg['bytes'] === 0 && $gNeg['landed'] === 3, 'G10 no count of a row is negative' );
	G::ok( Meter::cpuNow() >= 0 && is_int( Meter::cpuNow() ), 'G11 the CPU time read from getrusage, a count' );

	// The roll-up: three horizons, the level the Calculator's.
	$gMeter = new MemMeterStore();
	$gNow = 1793100000;
	$gMeter->record( [ 'time' => $gNow - 60, 'account' => 'Agent G', 'network' => '', 'op' => 'PUSH', 'lane' => 2, 'cpu' => 1000, 'wall' => 1, 'memory' => 1, 'bytes' => 1, 'landed' => 0, 'weight' => 1 ] );
	$gMeter->record( [ 'time' => $gNow - 7200, 'account' => '', 'network' => '192.0.2.0/24', 'op' => 'ANONYMOUS READ', 'lane' => 6, 'cpu' => 30, 'wall' => 1, 'memory' => 1, 'bytes' => 1, 'landed' => 0, 'weight' => 10 ] );
	$gMeter->record( [ 'time' => $gNow - 2 * 86400, 'account' => 'Agent G', 'network' => '', 'op' => 'PETITION', 'lane' => 3, 'cpu' => 5000, 'wall' => 1, 'memory' => 1, 'bytes' => 1, 'landed' => 0, 'weight' => 1 ] );
	$gMeter->record( [ 'time' => $gNow - 40 * 86400, 'account' => 'Agent G', 'network' => '', 'op' => 'PETITION', 'lane' => 3, 'cpu' => 99999, 'wall' => 1, 'memory' => 1, 'bytes' => 1, 'landed' => 0, 'weight' => 1 ] );
	$gDeny = "$scratch/pregate.list";
	$gBudget = new Budget( $lCalc, $gMeter, $gDeny, draw: static fn (): array => [ 0, 1 ] );
	$gR = $gBudget->run( $gNow );
	G::ok( $gR['use'] === [ 'hour' => 1000, 'day' => 1300, 'thirty_days' => 6300 ], 'G12 the use over the hour, the day and thirty days, each row weighted by its sample', json_encode( $gR['use'] ) );
	G::ok( $gR['requests'] === [ 'hour' => 1, 'day' => 11, 'thirty_days' => 12 ], 'G13 the requests over the three horizons; a row past thirty days counted in none', json_encode( $gR['requests'] ) );
	$gP = $lCalc->call( 'governor', 'pressure_level', json_encode( [ 'use' => $gR['use'], 'prev' => 'CLEAR', 'external_until' => 0, 'now' => $gNow ] ) )['value'];
	G::ok( $gR['level'] === $gP['level'] && $gR['kept'] === $gP['kept'], 'G14 the level and the kept level are pcalc governor pressure_level\'s over the sums', json_encode( $gP ) );
	$gB = $gMeter->budget();
	G::ok( $gB['use'] === $gR['use'] && $gB['rolled'] === $gNow && $gB['level'] === $gR['level'], 'G15 the roll-up written to the budget with its time and level' );
	G::ok( is_file( $gDeny ) && file_get_contents( $gDeny ) === Budget::DENY_HEAD . " $gNow\n", 'G16 with no CONTAINED account the list is its head line alone' );
	$gHot = new MemMeterStore();
	$gHot->record( [ 'time' => $gNow - 10, 'account' => 'X', 'network' => '', 'op' => 'PUSH', 'lane' => 2, 'cpu' => 4000000, 'wall' => 1, 'memory' => 1, 'bytes' => 1, 'landed' => 0, 'weight' => 1 ] );
	$gHr = ( new Budget( $lCalc, $gHot, '', draw: static fn (): array => [ 0, 1 ] ) )->run( $gNow );
	$gHp = $lCalc->call( 'governor', 'pressure_level', json_encode( [ 'use' => $gHr['use'], 'prev' => 'CLEAR', 'external_until' => 0, 'now' => $gNow ] ) )['value'];
	G::ok( $gHr['level'] === $gHp['level'] && $gHr['level'] !== 'CLEAR', 'G17 a use past the hour\'s budget raises the level, as pcalc answers it (' . $gHr['level'] . ')' );
	$gHr2 = ( new Budget( $lCalc, $gHot, '', draw: static fn (): array => [ 0, 1 ] ) )->run( $gNow + 4000 );
	$gHp2 = $lCalc->call( 'governor', 'pressure_level', json_encode( [ 'use' => $gHr2['use'], 'prev' => $gHr['kept'], 'external_until' => 0, 'now' => $gNow + 4000 ] ) )['value'];
	G::ok( $gHr2['level'] === $gHp2['level'] && $gHr2['kept'] === $gHp2['kept'], 'G18 the next roll-up asks with the kept level as prev (the hysteresis the Calculator\'s)' );

	// The traffic records and the PRE-GATE's list: ten BACKOFF VIOLATIONs in 24 hours CONTAIN (the Calculator's step).
	$gRec = json_decode( Landing::FRESH_TRAFFIC, true );
	for ( $i = 0; $i < 10; $i++ ) {
		$gRec = $lCalc->call( 'governor', 'traffic_step', json_encode( [ 'traffic' => $gRec, 'now' => $gNow + $i, 'event' => 'BACKOFF VIOLATION' ] ) )['value']['traffic'];
	}
	$gMeter->putTraffic( 'Agent C', json_encode( $gRec ), 'NORMAL', $gNow );
	$gMeter->putTraffic( 'Agent N', Landing::FRESH_TRAFFIC, 'NORMAL', $gNow );
	$gR = $gBudget->run( $gNow + 20 );
	$gSt = $gBudget->stage( json_encode( $gRec ), $gNow + 20, 'PETITION' );
	G::ok( $gR['stages'] === [ 'Agent C' => $gSt['stage'], 'Agent N' => 'NORMAL' ] && $gMeter->traffic( 'Agent C' )['stage'] === $gSt['stage'],
		'G19 each account\'s stage read at the roll-up by pcalc governor traffic_stage and written beside its record', json_encode( $gR['stages'] ) );
	$gStatic = $gSt['stage'] === 'CONTAINED';
	G::ok( $gStatic && ( $gR['stages']['Agent C'] ?? '' ) === 'CONTAINED', 'G20 an account the Calculator contains (by its traffic events) is CONTAINED at the roll-up', json_encode( $gSt ) );
	$gBase = $gSt['served_retry_after'] ?? null;
	$gJ = $lCalc->call( 'governor', 'jitter', json_encode( [ 'base' => $gBase, 'draw' => [ 0, 1 ] ] ) )['value'];
	$gBudgetSrc = (string)file_get_contents( "$root/custos/includes/Budget.php" );
	G::ok( is_int( $gBase ) && $gR['denied'] === [ 'Agent C' => $gBase + $gJ ] && preg_match( '/pollAfter|POLL_AFTER|\[\'(flood|breaker)\'\]/', $gBudgetSrc ) !== 1,
		'G21 the list names the CONTAINED account alone, its wait the Calculator\'s served_retry_after plus pcalc\'s jitter, no wait chosen in PHP', json_encode( [ $gR['denied'], $gSt ] ) );
	$gList = (string)file_get_contents( $gDeny );
	G::ok( str_starts_with( $gList, Budget::DENY_HEAD . ' ' ) && str_contains( $gList, "account\tAgent C\t" . ( $gBase + $gJ ) . "\n" ) && !str_contains( $gList, 'Agent N' ),
		'G22 the list written: its head line and one line per CONTAINED account' );
	G::ok( glob( "$scratch/pregate.list.tmp.*" ) === [], 'G23 the list written through a temporary file renamed over it: none left behind' );
	clearstatcache();
	G::ok( ( fileperms( $gDeny ) & 0777 ) === 0640, 'G54 the list\'s mode 0640, set on the temporary file before the rename', sprintf( '%o', fileperms( $gDeny ) & 0777 ) );
	$gOld = "$gDeny.tmp.aaaaaaaaaaaa";
	$gYoung = "$gDeny.tmp.bbbbbbbbbbbb";
	file_put_contents( $gOld, 'a crashed run' );
	touch( $gOld, time() - 3600 );
	file_put_contents( $gYoung, 'a concurrent run' );
	Budget::writeDeny( $gDeny, [], $gNow );
	G::ok( !is_file( $gOld ) && is_file( $gYoung ), 'G55 a crashed run\'s temporary file is removed at the next write; a young one, a concurrent run\'s, is left' );
	@unlink( $gYoung );
	Budget::writeDeny( $gDeny, [ "Bad\nName" => 5, 'Agent D' => 7 ], 9 );
	G::ok( file_get_contents( $gDeny ) === Budget::DENY_HEAD . " 9\naccount\tAgent D\t7\n", 'G24 an account name with a control character is never written into the list' );
	G::refuses( static fn () => Budget::writeDeny( "$scratch/no-such-folder/list", [], 1 ), RuntimeException::class, 'could not be written', 'G25 a list that cannot be written is refused, never left in part' );

	// The PRE-GATE.
	$gUa = 'PRB/0.2.0 (TPM; Agent D)';
	$gText = (string)file_get_contents( $gDeny );
	G::ok( custos_pregate( $gText, $gUa, 'pma', 'PETITION', 10 ) === 6, 'G26 the PRE-GATE answers a listed account 429 with its Retry-After' );
	G::ok( custos_pregate( $gText, $gUa, 'pma', 'PUSH', 9 ) === 7 && custos_pregate( $gText, $gUa, 'pma', 'PUSH', 14 ) === 2 && custos_pregate( $gText, $gUa, 'pma', 'PUSH', 15 ) === 1,
		'G69 the Retry-After is the wait left: the head\'s time plus the listed seconds, less now (9 + 7 - 14 = 2)' );
	G::ok( custos_pregate( $gText, $gUa, 'pma', 'RELEASE', 10 ) === null && custos_pregate( $gText, $gUa, 'pma', 'INQUIRE', 10 ) === null, 'G27 RELEASE and INQUIRE pass the PRE-GATE' );
	G::ok( custos_pregate( $gText, 'PRB/0.2.0 (TPM; Agent E)', 'pma', 'PUSH', 10 ) === null && custos_pregate( $gText, 'curl/8', 'query', null, 10 ) === null, 'G28 an account not listed, or no account named, goes on' );
	G::ok( custos_pregate( '', $gUa, 'pma', 'PUSH', 10 ) === null && custos_pregate( "account\tAgent D\t7\n", $gUa, 'pma', 'PUSH', 10 ) === null, 'G29 a list missing, or without its head line, does nothing' );
	G::ok( custos_pregate( Budget::DENY_HEAD . " 1\naccount\tAgent D\tx\n", $gUa, 'pma', 'PUSH', 2 ) === null, 'G30 a line whose wait is not a count is passed over' );
	G::ok( custos_pregate( $gText, $gUa, 'pma', 'PUSH', 15 ) === 1 && custos_pregate( $gText, $gUa, 'pma', 'PUSH', 16 ) === null && custos_pregate( $gText, $gUa, 'pma', 'PUSH', 9 + 86400 ) === null,
		'G56 a line holds until its head\'s time plus its seconds (9 + 7) and passes from then on: a stale list never denies for ever' );
	G::ok( custos_pregate( $gText, 'PRB/0.2.0 (TPM; Agent D)', 'query', null, 10 ) === 6,
		'G57 a User-Agent naming a listed account denies its sender whoever sends it: a spoofed name only ever denies' );
	G::ok( custos_pregate( $gText, 'PRB/0.2.0 (TPM; Agent D) (TPM; Agent E)', 'pma', 'PUSH', 10 ) === null && custos_pregate( $gText, 'PRB/0.2.0 (TPM; Agent E; Agent D', 'pma', 'PUSH', 10 ) === null,
		'G58 the account is the last member of the User-Agent\'s last parentheses alone: a listed name elsewhere in it is not read' );
	G::ok( custos_pregate_list( "$scratch/no-such-list" ) === '' && custos_pregate_list( '' ) === '' && custos_pregate_list( $gDeny ) === $gText
		&& custos_pregate( custos_pregate_list( "$scratch/no-such-list" ), $gUa, 'pma', 'PUSH', 10 ) === null,
		'G59 the PRE-GATE\'s read: a list not named or missing is empty text, and every request goes on; a list present is read whole' );
	$gPg = (string)file_get_contents( "$root/custos/pregate.php" );
	G::ok( substr_count( $gPg, 'file_get_contents(' ) === 1 && preg_match( '/\b(fopen|require|include|mysqli|PDO|curl_|json_decode)\b/', $gPg ) !== 1, 'G31 the PRE-GATE reads its list and nothing else' );

	// The roll-up and the landing job stepping one account's record at once (the lost update): a
	// Landing step is written between the roll-up's read of the record and its write of the stage.
	$gRace = new RacingMeterStore( new MemMeterStore() );
	$gRace->putTraffic( 'Agent L', Landing::FRESH_TRAFFIC, 'NORMAL', $gNow );
	$gStepped = json_encode( $lCalc->call( 'governor', 'traffic_step', '{"traffic":' . Landing::FRESH_TRAFFIC . ',"now":' . ( $gNow + 30 )
		. ',"end":{"kind":"PETITION","ending":"RATE","retry_after":5}}' )['value']['traffic'] ?? null );
	$gRace->between = static function ( MeterStore $m ) use ( $gStepped, $gNow ): void {
		$m->putTraffic( 'Agent L', $gStepped, 'NORMAL', $gNow + 30 );
	};
	$gRace->times = 1;
	$gRace->active = true;
	$gRr = ( new Budget( $lCalc, $gRace, '', draw: static fn (): array => [ 0, 1 ] ) )->run( $gNow + 40 );
	$gRace->active = false;
	$gRl = $gRace->traffic( 'Agent L' );
	G::ok( str_contains( $gStepped, '"streak":1' ) && $gRace->fired === 1 && ( $gRl['record'] ?? '' ) === $gStepped && $gRr['unsettled'] === []
		&& ( $gRl['stage'] ?? '' ) === $gBudget->stage( $gStepped, $gNow + 40, 'PETITION' )['stage'] && ( $gRl['time'] ?? 0 ) === $gNow + 40,
		'G60 a Landing step written between the roll-up\'s read and its write is kept: the stage is written beside the landed record, read again, never over it', json_encode( [ $gRl, $gRr['unsettled'] ] ) );
	// Literal where the old roll-up lacks the constant, so the race cases run against it too.
	$gTries = defined( Budget::class . '::STAGE_TRIES' ) ? constant( Budget::class . '::STAGE_TRIES' ) : 3;
	$gLanded = [];
	for ( $i = 0; $i < $gTries; $i++ ) {
		$gLanded[] = json_encode( $lCalc->call( 'governor', 'traffic_step', '{"traffic":' . ( $gLanded[$i - 1] ?? $gStepped ) . ',"now":' . ( $gNow + 50 + $i )
			. ',"end":{"kind":"PETITION","ending":"RATE","retry_after":5}}' )['value']['traffic'] ?? null );
	}
	$gRace->times = $gTries;
	$gRace->fired = 0;
	$gRace->between = static function ( MeterStore $m ) use ( $gRace, $gLanded, $gNow ): void {
		$m->putTraffic( 'Agent L', $gLanded[$gRace->fired], 'NORMAL', $gNow + 50 + $gRace->fired );
	};
	$gMiss = new MemMeterStore();
	$gMiss->putTraffic( 'Agent M', Landing::FRESH_TRAFFIC, 'NORMAL', $gNow );
	G::ok( $gMiss->stageTraffic( 'Agent M', '{"other":1}', 'CONTAINED', $gNow + 1 ) === false && $gMiss->traffic( 'Agent M' ) === [ 'record' => Landing::FRESH_TRAFFIC, 'stage' => 'NORMAL', 'time' => $gNow ]
		&& $gMiss->stageTraffic( 'Agent Z', '{}', 'NORMAL', 1 ) === false && $gMiss->traffic( 'Agent Z' ) === null
		&& $gMiss->stageTraffic( 'Agent M', Landing::FRESH_TRAFFIC, 'THROTTLED', $gNow + 2 ) === true && $gMiss->traffic( 'Agent M' )['stage'] === 'THROTTLED',
		'G61 the stage\'s write is a compare and set: a record changed since its read, or gone, is never written; the record itself never' );
	$gRace->active = true;
	$gOver = ( new Budget( $lCalc, $gRace, '', draw: static fn (): array => [ 0, 1 ] ) )->run( $gNow + 60 );
	$gRace->active = false;
	G::ok( count( array_unique( $gLanded ) ) === $gTries && $gRace->fired === $gTries && $gOver['unsettled'] === [ 'Agent L' ]
		&& $gRace->traffic( 'Agent L' )['record'] === $gLanded[$gTries - 1] && $gRace->traffic( 'Agent L' )['time'] === $gNow + 50 + $gTries - 1,
		'G62 a record overtaken at every read: the last Landing step stands, the stage left to the next roll-up', json_encode( [ $gOver['unsettled'], $gRace->traffic( 'Agent L' ) ] ) );
	$gPr = new MemMeterStore();
	foreach ( [ 10, 2592000, 2592001, 3000000 ] as $gAge ) {
		$gPr->record( [ 'time' => $gNow - $gAge, 'account' => 'X', 'network' => '', 'op' => 'PUSH', 'lane' => 2, 'cpu' => 1, 'wall' => 1, 'memory' => 1, 'bytes' => 1, 'landed' => 0, 'weight' => 1 ] );
	}
	$gPrR = ( new Budget( $lCalc, $gPr, '', draw: static fn (): array => [ 0, 1 ] ) )->run( $gNow );
	G::ok( $gPrR['pruned'] === 2 && array_column( $gPr->rows( 0 ), 'time' ) === [ $gNow - 10, $gNow - 2592000 ],
		'G63 custos_meter pruned at each roll-up: the rows before the thirty days\' window removed, the window kept', json_encode( [ $gPrR['pruned'], array_column( $gPr->rows( 0 ), 'time' ) ] ) );

	// The metered state in the landing job: the budget and the traffic record handed to admit.
	$gSeats = new FileSeatStore( "$scratch/g-seats.json" );
	$gTickets = new FileTicketStore( "$scratch/g-tickets" );
	$gNonces = new FileNonceStore( "$scratch/g-nonces.json" );
	$gM = new MemMeterStore();
	$gT = $lNow + 30 * 86400;
	// The certificates of this section: every account certified, its own Sponsor, so each admission takes one
	// seat lock and reads one bucket's account, as the meter's cases were written; section L binds Sponsors.
	$gCerts = new class implements CertificateStore {
		public function get( string $agent ): ?array {
			return [ 'agent' => $agent, 'sponsor' => $agent, 'd_is' => str_repeat( 'd', 64 ), 'd_prompt' => str_repeat( 'e', 64 ),
				'family' => 'test family', 'model' => 'test model', 'state' => CertificateStore::ACTIVE ];
		}

		public function agentsOf( string $sponsor ): array {
			return [ $sponsor ];
		}

		public function put( array $row ): void {
			throw new LogicException( 'the section\'s certificates are fixed' );
		}
	};
	$gLand = new Landing( $lCalc, $lStore, $pt, $gTickets, $gSeats, $gCerts, $lConf, static function () use ( &$gT ): int {
		return $gT;
	}, static fn (): array => [ 0, 1 ], nonces: $gNonces, meter: $gM );
	$gOps = new Ops( $gTickets, static function ( int $id ): void {
	}, 30, Ops::MAX_REQUEST_BYTES, Ops::SWEEP_AFTER, static fn (): int => $gT, null, $gM, [ 'version' => $lVersion, 'digest' => $lDigest ] );
	$gAns = static fn ( int $id ): array => (array)json_decode( (string)( $gTickets->get( $id )['answer'] ?? '' ), true );
	$gRefused = static function ( string $account, string $op = 'PETITION' ) use ( $gOps, $gLand, $gAns, $lPx ): array {
		$id = $gOps->run( $op, $lPx, $account, [ 'block' => 'g1' ] )['ticket'];
		$gLand->run( $id );
		return [ $id, $gAns( $id ) ];
	};
	// GA2-GA6: each refusal's HTTP status and Retry-After, from admit's decision, its retry_after exactly.
	$gCases = [
		'G32 GA2 AGENT STOP (a switch): 403' => [ [ 'agent_stop' => true ], 'Agent S1', 403, 'SWITCH' ],
		'G33 GA2 a SUSPENDED account (a switch): 403' => [ [ 'suspended' => [ 'Agent S2' ] ], 'Agent S2', 403, 'SWITCH' ],
	];
	foreach ( $gCases as $what => [ $conf, $acct, $status, $word ] ) {
		$l = new Landing( $lCalc, $lStore, $pt, $gTickets, $gSeats, $gCerts, $conf + $lConf, static fn (): int => $gT, static fn (): array => [ 0, 1 ], nonces: $gNonces, meter: $gM );
		$id = $gOps->run( 'PETITION', $lPx, $acct, [ 'block' => 'g1' ] )['ticket'];
		$l->run( $id );
		$a = $gAns( $id );
		$p = $gOps->poll( [ 'ticket' => (string)$id ], $acct );
		G::ok( ( $a['refused'] ?? '' ) === 'ADMISSION' && ( $a['decision']['refusal'] ?? '' ) === $word && ( $a['status'] ?? 0 ) === $status
			&& is_int( $a['decision']['retry_after'] ?? null ) && ( $a['poll_after'] ?? null ) === $a['decision']['retry_after']
			&& ( $p['http_status'] ?? 0 ) === $status && ( $p['retry_after'] ?? null ) === $a['poll_after'],
			$what . ': POLL answers it as the HTTP status with the decision\'s retry_after, exactly, as Retry-After', json_encode( [ $a, $p ] ) );
	}
	// GA5 RATE: the agent's bucket primed past its burst.
	$gSeats->put( 'Agent R', 'agent', 200000, $gT );
	[ $id, $a ] = $gRefused( 'Agent R' );
	$p = $gOps->poll( [ 'ticket' => (string)$id ], 'Agent R' );
	G::ok( ( $a['decision']['refusal'] ?? '' ) === 'RATE' && ( $a['status'] ?? 0 ) === 429 && $p['http_status'] === 429, 'G34 GA5 RATE (the seat table primed): 429', json_encode( $a ) );
	G::ok( $p['retry_after'] === $a['decision']['retry_after'] && $a['poll_after'] === $a['decision']['retry_after'] && $p['retry_after'] > 0,
		'G35 the Retry-After POLL answers is the decision\'s retry_after, the Calculator\'s, jitter included', json_encode( $p ) );
	G::ok( $gSeats->get( 'Agent R', 'agent' ) === [ 200000, $gT ], 'G36 a refusal charges nothing' );
	$gTr = $gM->traffic( 'Agent R' );
	G::ok( $gTr !== null && $gTr['stage'] === 'NORMAL' && str_contains( $gTr['record'], '"streak":1' ), 'G37 the refusal is stepped into the account\'s traffic record (pcalc traffic_step, the end RATE)', json_encode( $gTr ) );
	// GA4 PRESSURE: the budget's use past the fleet's.
	$gM->putBudget( [ 'hour' => 4000000, 'day' => 4000000, 'thirty_days' => 4000000 ], [ 'hour' => 1, 'day' => 1, 'thirty_days' => 1 ], $gT, 'OVERLOADED', 'OVERLOADED' );
	[ $id, $a ] = $gRefused( 'Agent P' );
	$p = $gOps->poll( [ 'ticket' => (string)$id ], 'Agent P' );
	G::ok( ( $a['decision']['refusal'] ?? '' ) === 'PRESSURE' && ( $a['status'] ?? 0 ) === 503 && $p['http_status'] === 503, 'G38 GA4 PRESSURE (the budget\'s use past the fleet\'s): 503, the level the Calculator\'s from the use', json_encode( $a ) );
	G::ok( $gM->traffic( 'Agent P' )['stage'] === 'NORMAL' && !str_contains( $gM->traffic( 'Agent P' )['record'], '"streak":1' ), 'G39 a fleet cause is never the account\'s: its streak not counted' );
	$gM->putBudget( [ 'hour' => 0, 'day' => 0, 'thirty_days' => 0 ], [ 'hour' => 0, 'day' => 0, 'thirty_days' => 0 ], $gT, 'CLEAR', 'CLEAR' );
	// GA3 TRAFFIC: a CONTAINED account's record.
	$gM->putTraffic( 'Agent T', json_encode( $gRec ), 'CONTAINED', $gT );
	[ $id, $a ] = $gRefused( 'Agent T' );
	$p = $gOps->poll( [ 'ticket' => (string)$id ], 'Agent T' );
	G::ok( ( $a['refused'] ?? '' ) === 'ADMISSION' && ( $a['status'] ?? 0 ) === 403 && ( $a['decision']['refusal'] ?? '' ) === 'SWITCH'
		&& ( $a['decision']['reason'] ?? '' ) === 'CONTAINED' && $p['http_status'] === 403,
		'G40 GA3 a CONTAINED account\'s PETITION refused SWITCH (reason CONTAINED): 403, answered by POLL', json_encode( $a ) );
	// GA6 SLOTS: the account's request in flight.
	$gTickets->create( 'PETITION', 'Agent Q', $lPx, '{"prefix":"' . $lPx . '"}' );
	$gIn = $gTickets->claim( (int)$gTickets->create( 'PETITION', 'Agent Q', $lPx, '{"prefix":"' . $lPx . '"}' ) );
	[ $id, $a ] = $gRefused( 'Agent Q' );
	G::ok( ( $a['decision']['refusal'] ?? '' ) === 'SLOTS' && ( $a['status'] ?? 0 ) === $a['decision']['status'] && in_array( $a['status'], [ 429, 503 ], true ),
		'G41 GA6 SLOTS (one request in flight per agent): the decision\'s status (' . ( $a['status'] ?? '' ) . ')', json_encode( $a ) );
	$gTickets->answer( (int)$gIn['id'], '{"refused":"TEST"}' );
	G::ok( Ops::refusalStatus( '{"refused":"LOCK HELD","poll_after":31}' ) === null && Ops::refusalStatus( '{"status":200,"poll_after":3}' ) === null
		&& Ops::refusalStatus( 'not json' ) === null && Ops::refusalStatus( '{"status":429,"poll_after":12}' ) === [ 429, 12 ], 'G42 POLL answers an HTTP status only of a governor\'s refusal (403, 429, 503) with its wait' );
	G::ok( Ops::refusalStatus( '{"status":403}' ) === [ 403, null ] && Ops::refusalStatus( '{"status":429,"poll_after":"12"}' ) === [ 429, null ],
		'G64 a refusal whose answer carries no wait: its HTTP status alone, no Retry-After' );
	$gApi = (string)file_get_contents( "$root/custos/includes/ApiPma.php" );
	G::ok( preg_match( "/if \\( isset\\( \\\$out\\['retry_after'\\] \\) \\) \\{\\s*\\\$request->response\\(\\)->header\\( 'Retry-After: '/", $gApi ) === 1,
		'G65 ApiPma sends Retry-After only when POLL answers a retry_after' );
	$gLane0 = $lCalc->call( 'governor', 'admit', json_encode( [ 'state' => [ 'now' => $gT, 'agent_stop' => false, 'suspended' => false, 'governor_off' => false,
		'agent_seats' => [ 999999999, $gT ], 'sponsor_seats' => [ 999999999, $gT ], 'agent_in_flight' => 0, 'sponsor_in_flight' => 0, 'finishing_in_flight' => 0,
		'starting_in_flight' => 0, 'pressure' => 'OVERLOADED' ], 'request' => [ 'kind' => 'ESSENTIAL JOB', 'seats' => 0, 'draw' => [ 0, 1 ] ] ] ) )['value'];
	G::ok( ( $gLane0['decision'] ?? '' ) === 'ADMITTED', 'G43 lane 0 is never refused on budget: the essential job admitted at OVERLOADED with the buckets full' );

	// The ops: STATUS, INQUIRE, HEARTBEAT.
	$gS = $gOps->run( 'STATUS', null, 'Agent T', [] );
	G::ok( $gS['build'] === [ 'version' => $lVersion, 'digest' => $lDigest ] && $gS['governor']['level'] === 'CLEAR' && $gS['stage'] === 'CONTAINED',
		'G44 STATUS: the Calculator\'s version and digest, the governor\'s level, the account\'s stage', json_encode( $gS ) );
	G::ok( $gOps->run( 'STATUS', null, '', [] )['stage'] === null, 'G45 STATUS of no account: the site\'s part alone' );
	G::ok( $gOps->run( 'INQUIRE', null, 'Agent T', [] ) === [ 'account' => 'Agent T', 'stage' => 'CONTAINED' ]
		&& $gOps->run( 'INQUIRE', null, 'Agent New', [] )['stage'] === 'NORMAL', 'G46 INQUIRE: the account\'s stage, NORMAL with no record' );
	G::ok( o_code( static fn () => $gOps->run( 'INQUIRE', null, '', [] ) ) === 'custos-not-agent' && o_code( static fn () => $gOps->run( 'STATUS', 'RR', 'A', [] ) ) === 'custos-unknown-param'
		&& o_code( static fn () => $gOps->run( 'STATUS', null, 'A', [ 'x' => 'y' ] ) ) === 'custos-unknown-param', 'G47 INQUIRE needs an account; STATUS takes no prefix and no parameter' );
	$gH = $gOps->run( 'HEARTBEAT', $lPx, 'Agent H', [ 'block' => 'g1' ] );
	G::ok( $gH['state'] === TicketStore::QUEUED && ( $gTickets->get( $gH['ticket'] )['op'] ?? '' ) === 'HEARTBEAT', 'G48 HEARTBEAT writes a ticket, as the write ops do' );
	$gLand->run( $gH['ticket'] );
	G::ok( ( $gAns( $gH['ticket'] )['refused'] ?? '' ) === 'NOT HOLDER', 'G49 a HEARTBEAT by an account that holds no lock: NOT HOLDER', json_encode( $gAns( $gH['ticket'] ) ) );
	$gT += 7200;
	$gPid = $gOps->run( 'PETITION', $lPx, 'Agent H', [ 'block' => 'g1' ] )['ticket'];
	$gLand->run( $gPid );
	$gG = $gAns( $gPid );
	$gT += 600;
	$gHid = $gOps->run( 'HEARTBEAT', $lPx, 'Agent H', [] )['ticket'];
	$gLand->run( $gHid );
	$gHa = $gAns( $gHid );
	$gLk = $lLock();
	G::ok( isset( $gG['grant'] ) && ( $gHa['expires'] ?? '' ) === gmdate( 'Y-m-d\TH:i:s\Z', $gT + 3600 ) && ( $gLk['expires_at'] ?? '' ) === $gHa['expires']
		&& ( $gLk['granted_at'] ?? '' ) === $gG['grant'] && ( $gLk['block'] ?? '' ) === 'g1', 'G50 the holder\'s HEARTBEAT extends the lease from now, the grant and the block kept', json_encode( [ $gG, $gHa, $gLk ] ) );
	G::ok( $gM->traffic( 'Agent H' )['stage'] === 'NORMAL' && str_contains( $gM->traffic( 'Agent H' )['record'], '"streak":0' ), 'G51 an admitted request is stepped SUCCEEDED into its traffic record' );
	$gT += 4000;
	$gRid = $gOps->run( 'RELEASE', $lPx, 'Agent H', [] )['ticket'];
	$gLand->run( $gRid );
	G::ok( ( $gAns( $gRid )['block'] ?? '' ) === 'g1' && is_string( $gAns( $gRid )['released'] ?? null ) && array_key_exists( 'holder', $lLock() ) && $lLock()['holder'] === null,
		'G52 the holder\'s RELEASE past the heartbeat\'s lease, no other account having taken the lock: released, the lock page cleared', json_encode( [ $gAns( $gRid ), $lLock() ] ) );
	$gLandSrc = (string)file_get_contents( "$root/custos/includes/Landing.php" ) . (string)file_get_contents( "$root/custos/includes/Budget.php" );
	G::ok( preg_match( '/\b(random_int|mt_rand)\s*\([^)]*\)\s*%|\bCONTAINED\b.*[<>]=?\s*\d/', $gLandSrc ) !== 1 && substr_count( $gLandSrc, "'governor', 'admit'" ) >= 1,
		'G53 no level, stage or jitter computed in PHP: admit, pressure_level, traffic_step, traffic_stage and jitter are the Calculator\'s' );

	// The end of each request, stepped at the job's end: an admitted op that fails counts toward
	// ERROR STREAK; CACHED ONLY steps nothing.
	G::ok( Landing::endingOf( [ 'decision' => 'ADMITTED' ], 'SUCCEEDED' ) === 'SUCCEEDED' && Landing::endingOf( [ 'decision' => 'ADMITTED' ], 'FAILED' ) === 'FAILED'
		&& Landing::endingOf( [ 'decision' => 'REFUSED', 'refusal' => 'RATE' ], 'FAILED' ) === 'RATE' && Landing::endingOf( [ 'decision' => 'REFUSED', 'refusal' => 'NONE SUCH' ], 'FAILED' ) === 'FAILED'
		&& Landing::endingOf( null, 'FAILED' ) === 'FAILED', 'G66 the ending: an admitted op by its outcome, a refusal by its word (FAILED when not an ending)' );
	$gCached = $lCalc->call( 'governor', 'admit', json_encode( [ 'state' => [ 'now' => $gT, 'agent_stop' => false, 'suspended' => false, 'governor_off' => false,
		'agent_seats' => [ 0, $gT ], 'sponsor_seats' => [ 0, $gT ], 'agent_in_flight' => 0, 'sponsor_in_flight' => 0, 'finishing_in_flight' => 0,
		'starting_in_flight' => 0, 'pressure' => 'OVERLOADED' ], 'request' => [ 'kind' => 'ANONYMOUS READ', 'seats' => 0, 'draw' => [ 0, 1 ] ] ] ) )['value'];
	G::ok( ( $gCached['decision'] ?? '' ) === 'CACHED ONLY' && Landing::endingOf( $gCached, 'SUCCEEDED' ) === null && Landing::endingOf( $gCached, 'FAILED' ) === null,
		'G67 a CACHED ONLY decision (pcalc admit, lane 6 at OVERLOADED) ends no governed request of an AGENT account: no traffic step', json_encode( $gCached ) );
	// A non-holder's HEARTBEAT, admitted and refused NOT HOLDER, again and again: the stages
	// Principia.Governor.Traffic gives, through pcalc: THROTTLED at ERROR STREAK, PENALIZED at a
	// second THROTTLED in the hour, and at the third PENALIZED in 24 hours CONTAINED; the clock moved
	// past PENALTY HOUR each time the account is PENALIZED, so that it is entered again from below.
	$gSeen = [];
	$gLast = null;
	for ( $i = 0; $i < 600; $i++ ) {
		$id = $gOps->run( 'HEARTBEAT', $lPx, 'Agent F', [] )['ticket'];
		$gLand->run( $id );
		$gStage = $gM->traffic( 'Agent F' )['stage'] ?? '';
		if ( $gStage !== $gLast ) {
			$gSeen[] = $gStage;
			$gLast = $gStage;
		}
		if ( $gStage === 'CONTAINED' ) {
			break;
		}
		$gT += $gStage === 'PENALIZED' ? 3700 : 1;
	}
	$id = $gOps->run( 'HEARTBEAT', $lPx, 'Agent F', [] )['ticket'];
	$gLand->run( $id );
	G::ok( $gSeen === [ 'NORMAL', 'THROTTLED', 'PENALIZED', 'NORMAL', 'THROTTLED', 'PENALIZED', 'NORMAL', 'THROTTLED', 'CONTAINED' ]
		&& ( $gAns( $id )['decision']['reason'] ?? '' ) === 'CONTAINED',
		'G68 failures after admission build the error streak: THROTTLED, then PENALIZED, then CONTAINED, and the next request refused CONTAINED', json_encode( [ $gSeen, $i ] ) );

	// The step's write: a compare and set on the record read, no seat lock taken (none to time out),
	// a miss read and stepped again. $gStep is one step as the Calculator gives it, from the record
	// text $rec (null: none yet), ERROR STREAK added when TE2 is raised, in Landing's text.
	$gStep = static function ( ?string $rec, string $op, string $ending, int $now ) use ( $lCalc ): string {
		$r = $lCalc->call( 'governor', 'traffic_step', '{"traffic":' . ( $rec ?? Landing::FRESH_TRAFFIC ) . ',"now":' . $now . ',"end":'
			. json_encode( [ 'kind' => $op, 'ending' => $ending, 'retry_after' => null ] ) . '}' )['value'];
		if ( ( $r['raises'] ?? false ) === true ) {
			$r = $lCalc->call( 'governor', 'traffic_step', json_encode( [ 'traffic' => $r['traffic'], 'now' => $now, 'event' => 'ERROR STREAK' ] ) )['value'];
		}
		return json_encode( $r['traffic'], JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_PRESERVE_ZERO_FRACTION );
	};
	// A seat store whose lock is obtained once (the admission's) and times out at every later try.
	$gLockOnce = static fn (): SeatStore => new class( $gSeats ) implements SeatStore {
		public int $locks = 0;

		public function __construct( private SeatStore $in ) {
		}

		public function get( string $account, string $kind ): array {
			return $this->in->get( $account, $kind );
		}

		public function put( string $account, string $kind, int $level, int $since ): void {
			$this->in->put( $account, $kind, $level, $since );
		}

		public function charge( string $account, array $agent, string $sponsorAccount, array $sponsor ): void {
			$this->in->charge( $account, $agent, $sponsorAccount, $sponsor );
		}

		public function lock( string $account, int $seconds ): bool {
			return ++$this->locks === 1 && $this->in->lock( $account, $seconds );
		}

		public function unlock( string $account ): void {
			$this->in->unlock( $account );
		}
	};
	$gFaults = [];
	$gSink = static function ( int $id, Throwable $e ) use ( &$gFaults ): void {
		$gFaults[] = get_class( $e ) . ': ' . $e->getMessage();
	};
	$gT += 86400;
	$gK = $gLockOnce();
	$gKLand = new Landing( $lCalc, $lStore, $pt, $gTickets, $gK, $gCerts, $lConf, static fn (): int => $gT, static fn (): array => [ 0, 1 ], $gSink, nonces: $gNonces, meter: $gM );
	$gKid = $gOps->run( 'PETITION', $lPx, 'Agent Lapse', [ 'block' => 'g1' ] )['ticket'];
	$gKa = $gKLand->run( $gKid );
	G::ok( isset( $gKa['grant'] ) && !isset( $gKa['refused'] ) && $gK->locks === 1 && $gFaults === []
		&& ( $gM->traffic( 'Agent Lapse' )['record'] ?? '' ) === $gStep( null, 'PETITION', 'SUCCEEDED', $gT ),
		'G70 a success whose seat lock times out after admission still records its traffic step, once: the step takes no seat lock',
		json_encode( [ $gKa, $gK->locks, $gFaults, $gM->traffic( 'Agent Lapse' ) ] ) );
	$gRid = $gOps->run( 'RELEASE', $lPx, 'Agent Lapse', [] )['ticket'];
	$gLand->run( $gRid );

	// GA1: a request refused by its shape (a 400) is stepped SHAPE, nothing charged.
	$gQ = [];
	$gQrec = null;
	foreach ( [ [ 'PETITION', '1', 'REQUEST' ], [ 'PUSH', '{"block":"g1","records":"[]"}', 'RECORDS' ], [ 'PETITION', '{', 'NOT READ' ] ] as [ $op, $req, $word ] ) {
		$gT += 5;
		$id = $gTickets->create( $op, 'Agent Shape', $lPx, $req );
		$gLand->run( $id );
		$gQrec = $gStep( $gQrec, $op, 'SHAPE', $gT );
		$gQ[] = [ $gAns( $id )['refused'] ?? '', ( $gM->traffic( 'Agent Shape' )['record'] ?? '' ) === $gQrec, $word ];
	}
	G::ok( array_column( $gQ, 0 ) === array_column( $gQ, 2 ) && array_column( $gQ, 1 ) === [ true, true, true ]
		&& str_contains( $gQrec, '"streak":3' ) && $gSeats->get( 'Agent Shape', SeatStore::AGENT ) === [ 0, 0 ],
		'G71 400 refusals (REQUEST, RECORDS, NOT READ of the request) are stepped SHAPE: each counted toward the error streak once, nothing charged',
		json_encode( [ $gQ, $gM->traffic( 'Agent Shape' ), $gQrec ] ) );

	// Across a timeout and the next job: a non-holder's HEARTBEAT (admitted, refused NOT HOLDER, FAILED)
	// whose seat lock times out after admission, then the next job, overtaken between its read and its
	// write by another job's step: every step written once, none twice.
	$gDm = new RacingMeterStore( new MemMeterStore() );
	$gD = $gLockOnce();
	$gDA = new Landing( $lCalc, $lStore, $pt, $gTickets, $gD, $gCerts, $lConf, static fn (): int => $gT, static fn (): array => [ 0, 1 ], $gSink, nonces: $gNonces, meter: $gDm );
	$gDB = new Landing( $lCalc, $lStore, $pt, $gTickets, $gSeats, $gCerts, $lConf, static fn (): int => $gT, static fn (): array => [ 0, 1 ], $gSink, nonces: $gNonces, meter: $gDm );
	$gT += 60;
	$gDt1 = $gT;
	$id = $gOps->run( 'HEARTBEAT', $lPx, 'Agent Twice', [] )['ticket'];
	$gDA->run( $id );
	$gD1 = $gDm->traffic( 'Agent Twice' )['record'] ?? '';
	$gT += 1;
	$gDt2 = $gT;
	$gDx = $gStep( $gD1, 'HEARTBEAT', 'FAILED', $gDt2 );
	$gDm->active = true;
	$gDm->times = 1;
	$gDm->between = static function ( MeterStore $m ) use ( $gD1, $gDx ): void {
		$m->casTraffic( 'Agent Twice', $gD1, $gDx, 'NORMAL', 0 );
	};
	$id = $gOps->run( 'HEARTBEAT', $lPx, 'Agent Twice', [] )['ticket'];
	$gDB->run( $id );
	$gDm->active = false;
	$gD2 = $gDm->traffic( 'Agent Twice' )['record'] ?? '';
	G::ok( ( $gAns( $id )['refused'] ?? '' ) === 'NOT HOLDER' && $gD->locks === 1 && $gD1 === $gStep( null, 'HEARTBEAT', 'FAILED', $gDt1 ) && str_contains( $gD1, '"streak":1' )
		&& $gDm->fired === 1 && $gD2 === $gStep( $gDx, 'HEARTBEAT', 'FAILED', $gDt2 ) && $gD2 !== $gStep( $gD1, 'HEARTBEAT', 'FAILED', $gDt2 ) && $gFaults === [],
		'G72 a step is never counted twice across a timeout and the next job: the timed-out job\'s step written once, the next job\'s step, overtaken by another\'s, read again and written once on it',
		json_encode( [ $gD1, $gDx, $gD2, $gDm->fired, $gFaults ] ) );
	$gOnce = new MemMeterStore();
	$gOnce->putTraffic( 'Agent Cas', Landing::FRESH_TRAFFIC, 'NORMAL', 0 );
	G::ok( $gOnce->casTraffic( 'Agent Cas', Landing::FRESH_TRAFFIC, 'x', 'NORMAL', 1 ) && !$gOnce->casTraffic( 'Agent Cas', Landing::FRESH_TRAFFIC, 'y', 'NORMAL', 2 )
		&& !$gOnce->casTraffic( 'Agent Cas', null, 'z', 'NORMAL', 3 ) && $gOnce->casTraffic( 'Agent Cas2', null, 'w', 'NORMAL', 4 )
		&& !$gOnce->casTraffic( 'Agent Cas2', null, 'v', 'NORMAL', 5 ) && $gOnce->traffic( 'Agent Cas' )['record'] === 'x' && $gOnce->traffic( 'Agent Cas2' )['record'] === 'w',
		'G73 the record\'s compare and set: written only on the text read, a first record only where none is; a second write on one read never lands' );
}

// ---- I: the identity values at PETITION and PUSH, shape-checked and recorded, nothing enforced -----
// prompt_digest (PETITION, PUSH), stated_model (PETITION), relayed_model (PETITION, PUSH): each optional;
// a presented value rides on the ticket's request as received; no comparison or enforcement here.

$ienq = [];
$its = new FileTicketStore( "$scratch/tickets-i" );
$iops = new Ops( $its, static function ( int $id ) use ( &$ienq ): void {
	$ienq[] = $id;
}, 30 );
$iDigest = str_repeat( 'ab12', 16 );
$iAll = [ 'prompt_digest' => $iDigest, 'stated_model' => 'model-x 1.0', 'relayed_model' => 'vendor/model-y:2' ];
$iPush = [ 'records' => '[{"a":1}]' ];

$a = $iops->petition( 'QED', 'Agent A', $iAll );
G::ok( ( $its->get( $a['ticket'] )['request'] ?? '' )
	=== '{"prefix":"QED","prompt_digest":"' . $iDigest . '","relayed_model":"vendor\/model-y:2","stated_model":"model-x 1.0"}'
	|| ( $its->get( $a['ticket'] )['request'] ?? '' )
	=== '{"prefix":"QED","prompt_digest":"' . $iDigest . '","relayed_model":"vendor/model-y:2","stated_model":"model-x 1.0"}',
	'I1 PETITION takes all three identity values and records them unchanged on the ticket', (string)( $its->get( $a['ticket'] )['request'] ?? '' ) );
$b = $iops->push( 'QED', 'Agent A', $iPush + [ 'prompt_digest' => $iDigest, 'relayed_model' => 'vendor/model-y:2' ] );
$req = json_decode( (string)( $its->get( $b['ticket'] )['request'] ?? '' ), true );
G::ok( is_array( $req ) && $req['prompt_digest'] === $iDigest && $req['relayed_model'] === 'vendor/model-y:2'
	&& $req['records'] === '[{"a":1}]' && !isset( $req['stated_model'] ),
	'I2 PUSH takes prompt_digest and relayed_model and records them unchanged on the ticket' );
G::ok( array_keys( $a ) === [ 'ticket', 'state', 'poll_after' ] && array_keys( $b ) === [ 'ticket', 'state', 'poll_after' ]
	&& $a['state'] === 'QUEUED' && $b['state'] === 'QUEUED',
	'I3 the answer keeps its form with the identity values presented (QUEUED, nothing enforced)' );

$before = count( $ienq );
$bad = [
	'I4 prompt_digest with an upper-case letter' => [ 'prompt_digest' => strtoupper( $iDigest ) ],
	'I5 prompt_digest of 63 characters' => [ 'prompt_digest' => substr( $iDigest, 1 ) ],
	'I6 prompt_digest with a non-hexadecimal character' => [ 'prompt_digest' => substr( $iDigest, 1 ) . 'g' ],
	'I7 prompt_digest of 65 characters' => [ 'prompt_digest' => $iDigest . '0' ],
	'I8 prompt_digest empty' => [ 'prompt_digest' => '' ],
	'I9 relayed_model over its byte bound' => [ 'relayed_model' => str_repeat( 'm', Ops::MAX_MODEL_BYTES + 1 ) ],
	'I10 stated_model over its byte bound' => [ 'stated_model' => str_repeat( 'm', Ops::MAX_MODEL_BYTES + 1 ) ],
	'I11 a model with a control character' => [ 'relayed_model' => "a\nb" ],
	'I12 a model not UTF-8' => [ 'relayed_model' => "\xff" ],
	'I13 a model sent as an array' => [ 'relayed_model' => [ 'a' ] ],
];
foreach ( $bad as $what => $p ) {
	G::ok( o_code( static fn () => $iops->petition( 'QED', 'Agent A', $p ) ) === 'custos-shape', "$what is refused at PETITION (custos-shape)" );
}
G::ok( o_code( static fn () => $iops->push( 'QED', 'Agent A', $iPush + $bad['I5 prompt_digest of 63 characters'] ) ) === 'custos-shape',
	'I14 prompt_digest of 63 characters is refused at PUSH (custos-shape)' );
G::ok( o_code( static fn () => $iops->push( 'QED', 'Agent A', $iPush + $bad['I4 prompt_digest with an upper-case letter'] ) ) === 'custos-shape',
	'I15 prompt_digest with an upper-case letter is refused at PUSH (custos-shape)' );
G::ok( o_code( static fn () => $iops->push( 'QED', 'Agent A', $iPush + $bad['I9 relayed_model over its byte bound'] ) ) === 'custos-shape',
	'I16 relayed_model over its byte bound is refused at PUSH (custos-shape)' );
G::ok( o_code( static fn () => $iops->push( 'QED', 'Agent A', $iPush + [ 'stated_model' => 'm' ] ) ) === 'custos-unknown-param',
	'I17 stated_model on PUSH is refused (custos-unknown-param)' );
foreach ( [ 'prompt_digest' => $iDigest, 'stated_model' => 'm', 'relayed_model' => 'm' ] as $k => $v ) {
	G::ok( o_code( static fn () => $iops->release( 'QED', 'Agent A', [ $k => $v ] ) ) === 'custos-unknown-param',
		"I18 $k on RELEASE is refused (custos-unknown-param)" );
}
G::ok( o_code( static fn () => $iops->poll( [ 'ticket' => '1', 'relayed_model' => 'm' ], 'Agent A' ) ) === 'custos-unknown-param',
	'I19 an identity value on POLL is refused (custos-unknown-param)' );
G::ok( count( $ienq ) === $before, 'I20 no refusal wrote a ticket or enqueued a job' );

$edge = $iops->petition( 'QED', 'Agent A', [ 'relayed_model' => str_repeat( 'm', Ops::MAX_MODEL_BYTES ) ] );
G::ok( $edge['state'] === 'QUEUED', 'I21 a model name exactly at its byte bound is taken' );
$only = $iops->petition( 'QED', 'Agent A', [ 'stated_model' => 'only-this' ] );
G::ok( ( $its->get( $only['ticket'] )['request'] ?? '' ) === '{"prefix":"QED","stated_model":"only-this"}',
	'I22 each value is optional: one alone is recorded alone' );
$n1 = $iops->petition( 'QED', 'Agent A', [ 'block' => 'b1' ] );
$n2 = $iops->push( 'QED', 'Agent A', [ 'records' => '[]' ] );
G::ok( ( $its->get( $n1['ticket'] )['request'] ?? '' ) === '{"block":"b1","prefix":"QED"}'
	&& ( $its->get( $n2['ticket'] )['request'] ?? '' ) === '{"prefix":"QED","records":"[]"}',
	'I23 a PETITION and a PUSH with none of the values record the request as before' );
$api = (string)file_get_contents( __DIR__ . '/../includes/ApiPma.php' );
G::ok( strpos( $api, "'prompt_digest' =>" ) !== false && strpos( $api, "'stated_model' =>" ) !== false && strpos( $api, "'relayed_model' =>" ) !== false,
	'I24 ApiPma declares the three parameters' );

// ---- JB: the batch jobs' frame over FileJobRunStore and a scripted governor --------------------

$jbRunner = new class implements \Custos\ShellRunner {
	public array $admits = [];
	public int $starts = 0;
	public ?array $answer = null;

	public function run( array $argv, string $stdin ): array {
		$this->starts++;
		if ( array_slice( $argv, 1 ) === [ 'version' ] ) {
			return [ 0, "0.1.0\n", '' ];
		}
		$req = json_decode( $stdin, true );
		$this->admits[] = $req;
		if ( $this->answer !== null ) {
			return [ 0, json_encode( $this->answer ) . "\n", '' ];
		}
		$p = $req['state']['pressure'] ?? 'CLEAR';
		$a = in_array( $p, [ 'CLEAR', 'BUSY' ], true )
			? [ 'decision' => 'ADMITTED', 'charge' => null ]
			: [ 'decision' => 'REFUSED', 'status' => 503, 'refusal' => 'PRESSURE', 'level' => $p, 'retry_after' => 120 ];
		return [ 0, json_encode( $a ) . "\n", '' ];
	}
};
$jbCalc = new Calculator( $fake, [ 'version' => '0.1.0', 'digest' => $fakeDigest ], $jbRunner, 'cli', new AnyResidence() );
$jbRuns = new FileJobRunStore( "$scratch/jobruns" );
$jbNow = 1793000000;
$jbClock = static function () use ( &$jbNow ): int {
	return $jbNow;
};
$jbDraw = static fn (): array => [ 7, 1000000 ];
$jbSunk = [];
$jbSink = static function ( string $job, Throwable $e ) use ( &$jbSunk ): void {
	$jbSunk[] = [ $job, get_class( $e ), $e->getMessage() ];
};
$jbFrame = static fn ( array $conf = [], array $bodies = [], ?Calculator $c = null ) => new BatchJob( $c ?? $jbCalc, $jbRuns,
	$conf + [ 'min_address_space' => 0 ], $bodies, $jbClock, $jbDraw, $jbSink );

// JB1: the run store's contract.
$id1 = $jbRuns->start( 'recheck', '20261031050000' );
$id2 = $jbRuns->start( 'cluster', '20261031050100' );
$open = $jbRuns->get( $id1 );
$fin = $jbRuns->finish( $id1, 'DONE', 'words', '{"n":1}', '20261031050200' );
$again = $jbRuns->finish( $id1, 'FAULT', 'other', '{}', '20261031050300' );
$id3 = $jbRuns->start( 'recheck', '20261031050400' );
G::ok( $id2 > $id1 && $id3 > $id2 && $open['done'] === null && $open['outcome'] === null && $fin && !$again
	&& $jbRuns->get( $id1 )['outcome'] === 'DONE' && $jbRuns->get( $id1 )['counts'] === '{"n":1}' && $jbRuns->get( 99999 ) === null
	&& $jbRuns->last( 'recheck' )['id'] === $id3 && $jbRuns->last( 'cluster' )['id'] === $id2 && $jbRuns->last( 'reaudit' ) === null
	&& !$jbRuns->finish( 99999, 'DONE', '', '{}', '20261031050500' ),
	'JB1 the run store: ids rising, a run open until finished, finished once, get and last (the latest by id), none for an unknown run' );

// JB2: an admitted run with no body: NOTHING DUE, NOT BUILT; the record written at the start and the end; the kind per job.
$kinds = [];
$ok = true;
foreach ( [ 'reaudit' => 'DEFERRABLE JOB', 'cluster' => 'DEFERRABLE JOB', 'recheck' => 'BIBLIOGRAPHY RECHECK JOB' ] as $job => $kind ) {
	$jbRunner->admits = [];
	$r = $jbFrame()->run( $job );
	$row = $jbRuns->get( $r['id'] );
	$req = $jbRunner->admits[0]['request'] ?? [];
	$st = $jbRunner->admits[0]['state'] ?? [];
	$ok = $ok && $r['outcome'] === 'NOTHING DUE' && $r['detail'] === 'NOT BUILT' && $row['job'] === $job && $row['outcome'] === 'NOTHING DUE'
		&& $row['detail'] === 'NOT BUILT' && $row['counts'] === '{}' && $row['started'] === gmdate( 'YmdHis', $jbNow ) && $row['done'] === gmdate( 'YmdHis', $jbNow )
		&& ( $req['kind'] ?? '' ) === $kind && ( $st['pressure'] ?? '' ) === 'CLEAR' && ( $st['now'] ?? 0 ) === $jbNow && count( $jbRunner->admits ) === 1;
	$kinds[] = "$job=$kind";
}
G::ok( $ok, 'JB2 each of the three jobs answers NOT BUILT (NOTHING DUE) after one `governor admit` of its kind at the level CLEAR; the record is written at the start and the end', implode( ', ', $kinds ) );

// JB3: lane 5 refused at STRAINED and OVERLOADED, admitted at BUSY; a refusal ends DEFERRED with the retry-after, the body not run.
$ran = 0;
$body = static function ( Calculator $c ) use ( &$ran ): array {
	$ran++;
	return [ 'outcome' => 'DONE' ];
};
$res = [];
foreach ( [ 'STRAINED', 'OVERLOADED', 'BUSY' ] as $level ) {
	$res[$level] = $jbFrame( [ 'pressure' => $level ], [ 'cluster' => $body ] )->run( 'cluster' );
}
G::ok( $res['STRAINED']['outcome'] === 'DEFERRED' && $res['STRAINED']['retry_after'] === 120 && $res['OVERLOADED']['outcome'] === 'DEFERRED'
	&& $res['BUSY']['outcome'] === 'DONE' && $ran === 1
	&& $jbRuns->get( $res['STRAINED']['id'] )['outcome'] === 'DEFERRED' && str_contains( $jbRuns->get( $res['STRAINED']['id'] )['detail'], '120' ),
	'JB3 lane 5 refused at STRAINED and OVERLOADED (DEFERRED with the governor\'s retry-after, the body not run, the run record the only write), admitted at BUSY',
	json_encode( $res ) );

// JB4: a refusal without a retry-after answers the configured wait.
$jbRunner->answer = [ 'decision' => 'REFUSED', 'status' => 503, 'refusal' => 'SWITCH', 'reason' => 'AGENT STOP' ];
$r = $jbFrame( [ 'defer_wait' => 77 ] )->run( 'recheck' );
$jbRunner->answer = null;
G::ok( $r['outcome'] === 'DEFERRED' && $r['retry_after'] === 77, 'JB4 a refusal with no retry-after answers CustosBatch\'s defer_wait', json_encode( $r ) );

// JB5: the job's context checked before anything: the Calculator never started.
$before = $jbRunner->starts;
$r = ( new BatchJob( $jbCalc, $jbRuns, [ 'min_address_space' => JobContext::MIN_ADDRESS_SPACE,
	'limits' => "Limit Soft Limit\nMax address space 1073741824 1073741824 bytes\n" ], [], $jbClock, $jbDraw, $jbSink ) )->run( 'reaudit' );
G::ok( $r['outcome'] === 'JOB CONTEXT' && $jbRunner->starts === $before && $jbRuns->get( $r['id'] )['outcome'] === 'JOB CONTEXT'
	&& str_starts_with( $jbRuns->get( $r['id'] )['detail'], 'JOB CONTEXT' ),
	'JB5 an address space below the minimum ends the run JOB CONTEXT with the Calculator never started', json_encode( $r ) );

// JB6: a tampered binary: INTEGRITY HALT, the binary never started, the record finished.
$tRunner = new ProcRunner();
$tCalc = new Calculator( $fake, [ 'version' => '0.1.0', 'digest' => str_repeat( 'a', 64 ) ], $tRunner, 'cli', new AnyResidence() );
$jbSunk = [];
$r = $jbFrame( [], [], $tCalc )->run( 'cluster' );
G::ok( $r['outcome'] === 'INTEGRITY HALT' && $r['detail'] === 'digest mismatch' && $tRunner->starts === 0
	&& $jbRuns->get( $r['id'] )['outcome'] === 'INTEGRITY HALT' && count( $jbSunk ) === 1 && $jbSunk[0][1] === DigestMismatch::class,
	'JB6 a digest mismatch ends the run INTEGRITY HALT, "digest mismatch" alone, the binary never started, the error channel given the digests', json_encode( $r ) );

// JB7: a fault ends FAULT with the words the closed set allows; the message goes to the error channel alone.
$jbSunk = [];
$r1 = $jbFrame( [], [ 'recheck' => static function ( Calculator $c ): array {
	throw new RuntimeException( 'cannot open /srv/wiki/secret.php on host wiki.example.org: stderr text' );
} ] )->run( 'recheck' );
$r2 = $jbFrame( [], [ 'recheck' => static function ( Calculator $c ): array {
	throw new CalculatorFault( 'pcalc broke at /opt/x', CalculatorFault::EXIT_CODE, 'recheck', 'batch' );
} ] )->run( 'recheck' );
$words = json_encode( [ $r1, $r2, $jbRuns->get( $r1['id'] ), $jbRuns->get( $r2['id'] ) ] );
G::ok( $r1['outcome'] === 'FAULT' && $r2['outcome'] === 'FAULT' && $r2['detail'] === 'exit code: pcalc recheck batch'
	&& !str_contains( $words, '/srv' ) && !str_contains( $words, 'wiki.example.org' ) && !str_contains( $words, 'stderr text' ) && !str_contains( $words, '/opt' )
	&& count( $jbSunk ) === 2 && str_contains( $jbSunk[0][2], 'wiki.example.org' ),
	'JB7 a body\'s fault ends the run FAULT; the record carries no path, host name or stderr text (Refusal::detail), the error channel the message', $words );

// JB8: a body's own outcome and counts recorded; an outcome outside the set a FAULT; an unknown job refused; no fetch and no timer in the frame.
$r = $jbFrame( [], [ 'reaudit' => static fn ( Calculator $c ): array => [ 'outcome' => 'DONE', 'detail' => 'two pages', 'counts' => [ 'pages' => 2 ] ] ] )->run( 'reaudit' );
$bad = $jbFrame( [], [ 'reaudit' => static fn ( Calculator $c ): array => [ 'outcome' => 'MADE UP' ] ] )->run( 'reaudit' );
$src = '';
foreach ( [ '/includes/BatchJob.php', '/maintenance/Job.php' ] as $f ) {
	foreach ( token_get_all( (string)file_get_contents( dirname( __DIR__ ) . $f ) ) as $tok ) {
		if ( !is_array( $tok ) || !in_array( $tok[0], [ T_COMMENT, T_DOC_COMMENT ], true ) ) {
			$src .= is_array( $tok ) ? $tok[1] : $tok;
		}
	}
}
$ext = json_decode( (string)file_get_contents( dirname( __DIR__ ) . '/extension.json' ), true );
G::refuses( static fn () => $jbFrame()->run( 'nothing' ), InvalidArgumentException::class, 'not a batch job', 'JB8 an unknown job name is refused before any record' );
G::ok( $r['outcome'] === 'DONE' && $jbRuns->get( $r['id'] )['counts'] === '{"pages":2}' && $jbRuns->get( $r['id'] )['detail'] === 'two pages'
	&& $bad['outcome'] === 'FAULT' && !preg_match( '/curl|fsockopen|file_get_contents\(\s*[\'"]http|HttpRequestFactory|Timer|Schedule/i', $src )
	&& array_intersect_key( $ext['JobClasses'], array_flip( [ 'custosReaudit', 'custosCluster', 'custosRecheck' ] ) ) === [
		'custosReaudit' => 'Custos\\ReauditJob', 'custosCluster' => 'Custos\\ClusterJob', 'custosRecheck' => 'Custos\\RecheckJob' ]
	&& ( $ext['config']['CustosBatch']['value'] ?? null ) === BatchJob::DEFAULTS,
	'JB8 a body\'s outcome, detail and counts recorded; an outcome outside the closed set a FAULT; the frame fetches nothing and sets no timer; the three job classes and CustosBatch registered',
	json_encode( [ $r, $bad ] ) );

// ---- Z: the structure test with register (TPS 5.3.47): the op STRUCTURE_TEST, its job, the line --------

// The op's shape (GA1), no Calculator: Ops alone.
$zQueued = [];
$zOpsT = new FileTicketStore( "$scratch/structure-op-tickets" );
$zOps = new Ops( $zOpsT, static function ( int $id ) use ( &$zQueued ): void {
	$zQueued[] = $id;
} );
G::ok( o_code( fn () => $zOps->run( 'STRUCTURE_TEST', null, 'Agent A', [] ) ) === 'custos-prefix', 'Z1 a STRUCTURE_TEST naming no prefix is refused custos-prefix' );
G::ok( o_code( fn () => $zOps->run( 'STRUCTURE_TEST', 'Re-hearsal', 'Agent A', [] ) ) === 'custos-prefix', 'Z2 a STRUCTURE_TEST of a prefix in no form is refused custos-prefix' );
G::ok( o_code( fn () => $zOps->run( 'STRUCTURE_TEST', [ 'SP' ], 'Agent A', [] ) ) === 'custos-shape', 'Z3 a STRUCTURE_TEST whose prefix is not one string is refused custos-shape' );
G::ok( o_code( fn () => $zOps->run( 'STRUCTURE_TEST', 'SP', 'Agent A', [ 'block' => 'b1' ] ) ) === 'custos-unknown-param'
	&& o_code( fn () => $zOps->run( 'STRUCTURE_TEST', 'SP', 'Agent A', [ 'records' => '[]' ] ) ) === 'custos-unknown-param',
	'Z4 a STRUCTURE_TEST takes the prefix alone: a block or records refused custos-unknown-param' );
G::ok( o_code( fn () => $zOps->run( 'STRUCTURE_TEST', 'SP', 'Agent A', [ 'account' => 'Agent B' ] ) ) === 'custos-account', 'Z5 a STRUCTURE_TEST naming an account is refused custos-account' );
G::ok( o_code( fn () => $zOps->run( 'STRUCTURE_TEST', 'SP', '', [] ) ) === 'custos-not-agent', 'Z6 a STRUCTURE_TEST with no account is refused custos-not-agent' );
G::ok( $zOpsT->count( 'QUEUED' ) + $zOpsT->count( 'IN WORK' ) + $zOpsT->count( 'DONE' ) === 0 && $zQueued === [], 'Z7 the refused STRUCTURE_TESTs write no ticket and push no job', json_encode( $zQueued ) );
$zOk = $zOps->run( 'STRUCTURE_TEST', 'SP', 'Agent A', [] );
$zRow = $zOpsT->get( (int)( $zOk['ticket'] ?? 0 ) );
G::ok( array_keys( $zOk ) === [ 'ticket', 'state', 'poll_after' ] && $zOk['state'] === 'QUEUED' && $zQueued === [ $zOk['ticket'] ]
	&& ( $zRow['op'] ?? '' ) === 'STRUCTURE_TEST' && ( $zRow['request'] ?? '' ) === '{"prefix":"SP"}',
	'Z8 a STRUCTURE_TEST writes one ticket (op STRUCTURE_TEST, the prefix its request) and pushes its job: QUEUED and when to poll, as PETITION', json_encode( [ $zOk, $zRow ] ) );

// The line's form (PageTexts) and its composition from an answer (Landing::structureLine), no Calculator.
G::ok( PageTexts::isStructureLine( PageTexts::STRUCTURE_NONE ) && PageTexts::isStructureLine( 'STRUCTURE TEST 2026-11-02 structurally regular with register WITH -' )
	&& PageTexts::isStructureLine( 'STRUCTURE TEST 2026-11-02 FINDINGS ["UNDER","v"] WITH SP-2, SP-10' )
	&& !PageTexts::isStructureLine( 'STRUCTURE TEST 2026-11-02 regular WITH -' ) && !PageTexts::isStructureLine( "STRUCTURE TEST 2026-11-02 structurally regular with register WITH -\nx" )
	&& !PageTexts::isStructureLine( 'STRUCTURE TEST 2026-13-02 structurally regular with register WITH -' ),
	'Z9 a STRUCTURE TEST LINE is "STRUCTURE TEST none" or the date, the result and WITH the identifiers on one line; anything else is not one' );
G::refuses( fn () => PageTexts::badge( 'SP', [ 'last_push' => null, 'last_release' => null, 'calculator_version' => '0.1.0',
	'calculator_digest' => str_repeat( 'a', 64 ), 'record_count' => 0, 'research_assembly' => str_repeat( 'b', 64 ) ], false, 1, 'STRUCTURE TEST maybe' ),
	PageFault::class, 'not a STRUCTURE TEST LINE', 'Z10 the INDEX AND BADGE page refuses a line not in its form' );
G::ok( PageTexts::structureSays( 'STRUCTURE TEST 2026-11-02 structurally regular with register WITH -' )
	=== PageTexts::structureSays( 'STRUCTURE TEST 2027-01-01 structurally regular with register WITH -' )
	&& PageTexts::structureSays( PageTexts::STRUCTURE_NONE ) === 'none',
	'Z11 two lines that differ only in their date say the same (the line is rewritten only when that changes)' );
$zAnswer = [ 'OK', [], [ [ 'OVER-EOM', 'v', [ 'EOM_X', 'SP-2' ], 'a line' ] ], [ 'USED', [ 'SP-2', 'SP-10' ] ], [ 'SETTLED', [] ], [ 'OPEN', [] ] ];
G::ok( Landing::structureLine( $zAnswer, '2026-11-02' ) === 'STRUCTURE TEST 2026-11-02 FINDINGS ["OVER-EOM","v",["EOM_X","SP-2"],"a line"] WITH SP-2, SP-10'
	&& Landing::structureLine( [ 'OK', [], [], [ 'USED', [] ], [ 'SETTLED', [] ], [ 'OPEN', [] ] ], '2026-11-02' ) === 'STRUCTURE TEST 2026-11-02 structurally regular with register WITH -',
	'Z12 the line read from the answer alone: FINDINGS and each finding as the Calculator wrote it, in its order; USED in its order (never sorted here); "-" when none' );
$zFault = null;
try {
	Landing::structureLine( [ 'OK', [], [], [ 'USED', [ 'SP-1, SP-2' ] ], [ 'SETTLED', [] ], [ 'OPEN', [] ] ], '2026-11-02' );
} catch ( CalculatorFault $e ) {
	$zFault = $e;
}
$zRefused = null;
try {
	Landing::structureLine( [ 'REFUSED', 'RECORD:SP-1: STATUS UNMARKED is not a status word' ], '2026-11-02' );
} catch ( \Custos\LandRefused $e ) {
	$zRefused = $e;
}
G::ok( $zFault !== null && $zFault->fault === CalculatorFault::ANSWER_FORM && $zRefused !== null && $zRefused->word === 'STRUCTURE TEST',
	'Z13 an answer not of eom_register_test\'s form is a CALCULATOR FAULT (an identifier the line could not keep apart among them); ["REFUSED", reason] is refused STRUCTURE TEST' );

$zBuilt = "$root/.lake/build/bin/pcalc";
if ( !isset( $lCalc ) || !is_file( $zBuilt ) ) {
	G::skip( 'Z the structure test over the built pcalc', 'no built pcalc in this clone (.lake/build/bin/pcalc)' );
} else {
	$zPx = 'SP';
	$zInner = new FileStore( "$scratch/structure" );
	$zSaves = [];
	$zStore = new class( $zInner, $zSaves ) implements PageStore {
		public function __construct( public FileStore $inner, public array &$saves ) {
		}
		public function get( string $title ): ?string {
			return $this->inner->get( $title );
		}
		public function exists( string $title ): bool {
			return $this->inner->exists( $title );
		}
		public function put( string $title, string $text, string $summary ): void {
			$this->saves[] = $title;
			$this->inner->put( $title, $text, $summary );
		}
		public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
			$this->saves[] = $title;
			return $this->inner->casPut( $title, $expected, $text, $summary, $actor );
		}
		public function appendAs( string $title, string $line, string $summary, string $actor ): string {
			$this->saves[] = $title;
			return $this->inner->appendAs( $title, $line, $summary, $actor );
		}
	};
	// The seed, as Custos:SeedUwc writes it, "STRUCTURE TEST none" on the INDEX AND BADGE page.
	$seed = new PageWriter( $zStore, $pt );
	$seed->begin( $zPx, 'seed' );
	$seed->put( $pt->draft( $zPx ), Blocks::render( 'draft', $lCanon ) . "\n" );
	foreach ( PageTitles::ZONES as $zone ) {
		$seed->put( $pt->researchAssembly( $zPx, $zone ), Blocks::render( 'assembly', $lCanon ) . "\n" );
	}
	$seed->put( $pt->registerVolume( $zPx, 1 ), PageTexts::register( $zPx, 1, '[]' ) );
	$seed->put( $pt->lock( $zPx ), PageTexts::lock( $zPx, null, null, null, null ) );
	$seed->put( $pt->index( $zPx ), PageTexts::badge( $zPx, [ 'last_push' => null, 'last_release' => null,
		'calculator_version' => $lVersion, 'calculator_digest' => $lDigest, 'record_count' => 0, 'research_assembly' => $lRaDigest ], false, 1, PageTexts::STRUCTURE_NONE ) );
	$seed->commit();
	$zIx = $pt->index( $zPx );
	$zRg = $pt->registerVolume( $zPx, 1 );
	$zLine = static fn (): ?string => PageTexts::readStructure( $zInner->get( $zIx ) );
	$seedSrc = (string)file_get_contents( "$root/custos/maintenance/SeedUwc.php" );
	G::ok( $zLine() === 'STRUCTURE TEST none' && str_contains( $seedSrc, '], false, 1, PageTexts::STRUCTURE_NONE );' ),
		'Z14 after the seed the INDEX AND BADGE page reads "STRUCTURE TEST none" (Custos:SeedUwc writes it so)', (string)$zLine() );

	$zNow = 1793000000;
	$zTickets = new FileTicketStore( "$scratch/structure-tickets" );
	$zSeats = new FileSeatStore( "$scratch/structure-seats.json" );
	$zNonces = new FileNonceStore( "$scratch/structure-nonces.json" );
	$zMeter = new MemMeterStore();
	$zPushed = [];
	$zFaults = [];
	$zThrow = false;
	$zLanding = new Landing( $lCalc, $zStore, $pt, $zTickets, $zSeats, $lCerts, $lConf, static function () use ( &$zNow ): int {
		return $zNow;
	}, static fn (): array => [ 0, 1 ], static function ( int $id, Throwable $e ) use ( &$zFaults ): void {
		$zFaults[] = get_class( $e ) . ': ' . $e->getMessage();
	}, $zNonces, $zMeter, static function ( string $prefix ) use ( &$zPushed, &$zThrow ): void {
		if ( $zThrow ) {
			throw new RuntimeException( 'the job queue at /var/run/jobs on db.internal is down' );
		}
		$zPushed[] = $prefix;
	} );
	$zO = new Ops( $zTickets, static function ( int $id ): void {
	} );
	$zRun = static function ( string $op, string $account, array $params = [] ) use ( $zO, $zLanding, $zNonces, $lCalc, $zPx ): array {
		$nonce = $zNonces->peek( $account, $zPx );
		if ( $op === 'PUSH' && $nonce !== null ) {
			$params['challenge_response'] = Challenge::response( $lCalc, $nonce )[1];
		}
		return $zLanding->run( $zO->run( $op, $zPx, $account, $params )['ticket'] );
	};
	$zSnap = static function () use ( $zInner ): array {
		$o = [];
		foreach ( $zInner->titles() as $t ) {
			$o[$t] = $zInner->get( $t );
		}
		return $o;
	};
	$zDirect = static function ( string $register ) use ( $lCalc, $lCanon ): string {
		return Landing::structureLine( $lCalc->call( 'eom', 'eom_register_test', '{"tfk":' . $lCanon . ',"records":' . $register . '}' )['value'], '2026-10-26' );
	};

	$before = $zSnap();
	$a = $zRun( 'STRUCTURE_TEST', 'Agent A' );
	G::ok( ( $a['refused'] ?? '' ) === 'NOT HOLDER' && $zSnap() === $before, 'Z15 a STRUCTURE_TEST on a free lock is refused by the job, NOT HOLDER, nothing written', json_encode( $a ) );
	$zRun( 'PETITION', 'Agent A', [ 'block' => 'b1' ] );
	$before = $zSnap();
	$zSaves = [];
	$a = $zRun( 'STRUCTURE_TEST', 'Agent B' );
	G::ok( ( $a['refused'] ?? '' ) === 'NOT HOLDER' && $zSnap() === $before && $zSaves === [],
		'Z16 a STRUCTURE_TEST from an account that does not hold the lock is refused by the job, NOT HOLDER, nothing written', json_encode( $a ) );
	$seatsBefore = $zSeats->get( 'Agent A', 'agent' );
	$zSaves = [];
	$a = $zRun( 'STRUCTURE_TEST', 'Agent A' );
	$want = 'STRUCTURE TEST 2026-10-26 structurally regular with register WITH -';
	G::ok( ( $a['structure_test'] ?? '' ) === $want && ( $a['written'] ?? null ) === true && $zLine() === $want,
		'Z17 the holder\'s STRUCTURE_TEST is answered with the line, written on the INDEX AND BADGE page', json_encode( $a ) );
	G::ok( $zSaves === [ $zIx ], 'Z18 the line is one save, the INDEX AND BADGE page alone, through PageWriter', json_encode( $zSaves ) );
	G::ok( $want === $zDirect( '[]' ), 'Z19 the line equals the one read from the Calculator\'s own answer (pcalc eom eom_register_test) over the same Research Assembly and records' );
	G::ok( $zSeats->get( 'Agent A', 'agent' ) !== $seatsBefore, 'Z20 the STRUCTURE_TEST was admitted through governor admit (lane 3): its seats charged to the holder', json_encode( [ $seatsBefore, $zSeats->get( 'Agent A', 'agent' ) ] ) );
	$zBadge = PageTexts::readBadge( $zInner->get( $zIx ) );

	$zNow += 86400;
	// A day later the lease has lapsed: the holder petitions again.
	$zRun( 'PETITION', 'Agent A', [ 'block' => 'b1' ] );
	$zSaves = [];
	$before = $zSnap();
	$a = $zRun( 'STRUCTURE_TEST', 'Agent A' );
	G::ok( ( $a['structure_test'] ?? '' ) === $want && ( $a['written'] ?? null ) === false && $zSaves === [] && $zSnap() === $before,
		'Z21 the line unchanged beside its date (a day later) leaves the INDEX AND BADGE page unsaved; the line as it stands answered', json_encode( [ $a, $zSaves ] ) );

	// Standing records with a declared form: the register as version 1's test reads it, SP-10 and SP-2 out of order.
	$zReg = '[{"EQUATION":"m * D(v, t) = -k_s * x","ID":"SP-10","ROLE":"EOM(v)","STATUS":"PROVISIONAL"},'
		. '{"EQUATION":"D(x, t) = v","ID":"SP-2","ROLE":"EOM(x)","STATUS":"ESTABLISHED"},{"ID":"SP-3","STATUS":"HELD"}]';
	$zInner->tamper( $zRg, PageTexts::register( $zPx, 1, $zReg ) );
	$zSaves = [];
	$a = $zRun( 'STRUCTURE_TEST', 'Agent A' );
	$zWant = $zDirect( $zReg );
	$zLineNow = (string)$zLine();
	G::ok( ( $a['written'] ?? null ) === true && PageTexts::structureSays( $zLineNow ) === PageTexts::structureSays( $zWant ) && str_starts_with( $zLineNow, 'STRUCTURE TEST 2026-10-27 FINDINGS ' ),
		'Z22 standing records with a form: the line FINDINGS, its result and identifiers those of the Calculator\'s answer for the same Research Assembly and records', $zLineNow . ' | ' . $zWant );
	G::ok( str_ends_with( $zLineNow, ' WITH SP-2, SP-10' ) && $zSaves === [ $zIx ], 'Z23 the identifiers in the order of the answer\'s USED (prefix, then number: SP-2 before SP-10), the held SP-3 not used', $zLineNow );

	// The register as this Custos lands it today (STATUS UNMARKED): the Calculator refuses the test; nothing written.
	$zInner->tamper( $zRg, PageTexts::register( $zPx, 1, '[{"ID":"SP-1","STATUS":"UNMARKED","ROLE":"EOM(v)","EQUATION":"m * D(v, t) = -k_s * x"}]' ) );
	$before = $zSnap();
	$a = $zRun( 'STRUCTURE_TEST', 'Agent A' );
	G::ok( ( $a['refused'] ?? '' ) === 'STRUCTURE TEST' && ( $a['calculator'][0] ?? '' ) === 'REFUSED' && $zSnap() === $before,
		'Z24 an answer ["REFUSED", reason] is refused STRUCTURE TEST, the line left as it stands (a record status word the test does not read: a later corner)', json_encode( $a ) );

	// The job: no ticket, no account; lane 5 under pressure refused, writing nothing.
	$zInner->tamper( $zRg, PageTexts::register( $zPx, 1, '[]' ) );
	$zMeter->putBudget( [ 'hour' => 4000000, 'day' => 4000000, 'thirty_days' => 4000000 ], [ 'hour' => 1, 'day' => 1, 'thirty_days' => 1 ], $zNow, 'STRAINED', 'STRAINED' );
	$before = $zSnap();
	$zSaves = [];
	$a = $zLanding->structureJob( $zPx );
	G::ok( ( $a['refused'] ?? '' ) === 'ADMISSION' && ( $a['decision']['decision'] ?? '' ) === 'REFUSED' && ( $a['decision']['refusal'] ?? '' ) === 'PRESSURE'
		&& $zSnap() === $before && $zSaves === [],
		'Z25 the structure-test job is admitted as STRUCTURE TEST JOB (lane 5): refused by pressure (STRAINED), nothing written', json_encode( $a ) );
	$zMeter->putBudget( [ 'hour' => 0, 'day' => 0, 'thirty_days' => 0 ], [ 'hour' => 0, 'day' => 0, 'thirty_days' => 0 ], $zNow, 'CLEAR', 'CLEAR' );
	$a = $zLanding->structureJob( $zPx );
	$zJobLine = 'STRUCTURE TEST 2026-10-27 structurally regular with register WITH -';
	G::ok( ( $a['written'] ?? null ) === true && $zLine() === $zJobLine && $zSaves === [ $zIx ],
		'Z26 the job at CLEAR runs the test and writes the changed line, one save of the INDEX AND BADGE page', json_encode( [ $a, $zSaves ] ) );
	$zSaves = [];
	$a = $zLanding->structureJob( $zPx );
	G::ok( ( $a['written'] ?? null ) === false && $zSaves === [], 'Z27 the job with the line unchanged writes nothing', json_encode( $a ) );
	$zSeatsAll = (string)@file_get_contents( "$scratch/structure-seats.json" );
	G::ok( !str_contains( $zSeatsAll, '""' ), 'Z28 the job charges no seats: no account\'s row is written by it', $zSeatsAll );

	// A landing pushes one job for its UWC, and carries the line through.
	$zSp = str_replace( [ 'RR-1', 'RR-2' ], [ 'SP-1', 'SP-2' ], "[$result,$assumption]" );
	$zPushed = [];
	$a = $zRun( 'PUSH', 'Agent A', [ 'records' => $zSp ] );
	G::ok( array_column( $a['landed'] ?? [], 'id' ) === [ 'SP-1', 'SP-2' ] && $zPushed === [ $zPx ],
		'Z29 a PUSH that lands pushes the structure-test job once, for its UWC (deduplicated per UWC by the queue: StructureTestJob, removeDuplicates)', json_encode( [ $a, $zPushed ] ) );
	G::ok( $zLine() === $zJobLine, 'Z30 the PUSH rewrote the badge and carried the line through unchanged', (string)$zLine() );
	$zPushed = [];
	$a = $zRun( 'PUSH', 'Agent A', [ 'records' => '[]' ] );
	G::ok( isset( $a['refused'] ) && $zPushed === [], 'Z31 a PUSH refused pushes no job', json_encode( [ $a, $zPushed ] ) );
	$zThrow = true;
	$zFaults = [];
	$zNext = str_replace( [ 'RR-1', 'RR-2' ], [ 'SP-3', 'SP-4' ], "[$result,$assumption]" );
	$a = $zRun( 'PUSH', 'Agent A', [ 'records' => $zNext ] );
	$zThrow = false;
	G::ok( array_column( $a['landed'] ?? [], 'id' ) === [ 'SP-3', 'SP-4' ] && count( $zFaults ) === 1 && str_contains( $zFaults[0], 'job queue' )
		&& !str_contains( json_encode( $a ), 'db.internal' ),
		'Z32 a job push that throws goes to the error channel; the landing stands, its answer carrying nothing of the message', json_encode( [ $a, $zFaults ] ) );
	// The landed register (STATUS UNMARKED): the job's test refused by the Calculator, nothing written.
	$before = $zSnap();
	$a = $zLanding->structureJob( $zPx );
	G::ok( ( $a['refused'] ?? '' ) === 'STRUCTURE TEST' && $zSnap() === $before,
		'Z33 the job over the register as landed today is refused STRUCTURE TEST by the Calculator\'s answer; nothing written', json_encode( $a ) );
	$a = $zRun( 'RELEASE', 'Agent A', [ 'block' => 'b1' ] );
	G::ok( isset( $a['released'] ) && $zLine() === $zJobLine, 'Z34 a RELEASE rewrote the badge and carried the line through unchanged', json_encode( $a ) );
	$zNow += 3600;
	$before = $zSnap();
	$a = $zRun( 'STRUCTURE_TEST', 'Agent A' );
	G::ok( ( $a['refused'] ?? '' ) === 'NOT HOLDER' && $zSnap() === $before, 'Z35 after the RELEASE the former holder\'s STRUCTURE_TEST is refused NOT HOLDER, nothing written', json_encode( $a ) );
	$apiSrc = (string)file_get_contents( "$root/custos/includes/ApiPma.php" ) . (string)file_get_contents( "$root/custos/includes/Ops.php" );
	G::ok( !str_contains( $apiSrc, 'eom_register_test' ) && !str_contains( $apiSrc, 'Calculator::' ) && !str_contains( $apiSrc, 'new Calculator' ),
		'Z36 the op calls no Calculator in the web request: ApiPma and Ops name neither the Calculator nor the test' );
}

// ---- U: the routes around the permission hook (RestrictedRoutes) ------------------------------

// Its own accounts, table and titles: the names of section K are reused by later sections.
$upt = new PageTitles( 'Principia Machina/UWC', 'Principia Machina' );
$uTable = Permits::table();
$uStore = new FileStore( "$scratch/routes" );
$uRead = static fn ( string $t ): ?string => $uStore->get( $t );
$uUsers = [
	'agent' => [ 'Agent A', false, [ '*', 'user', 'pma-agent' ] ],
	'plain' => [ 'Reader', false, [ '*', 'user', 'autoconfirmed' ] ],
	'anonymous' => [ '127.0.0.1', false, [ '*' ] ],
	'impostor' => [ 'Custos', false, [ '*', 'user', 'autoconfirmed' ] ],
	'declarer' => [ 'Declarer', false, [ '*', 'user', 'pma-declarer' ] ],
	'operator' => [ 'Operator', false, [ '*', 'user', 'pma-operator' ] ],
];
$uk = static fn ( string $title, string $action, string $who ): ?string => PermissionHook::decide( $upt, $title, $action,
	$uUsers[$who][0], $uUsers[$who][1], $uUsers[$who][2], PermissionHook::DEFAULT_ROLES, $uRead, $uTable );
$uR = PermissionHook::RESTRICTED;

$un = RestrictedRoutes::numbers( 7240 );
$names = [ 'Restricted' ];
G::ok( $un === [ 7240, 7241 ], 'U1 the restricted numbers are the namespace\'s, 7240, and the next, 7241' );
$ur = static fn ( int $ns, string $t ): bool => RestrictedRoutes::restrictedTitle( $upt, $ns, $t, 7240 );
G::ok( $ur( 7240, 'Restricted:Falcon/Stratum' ) && $ur( 7240, 'Restricted:Score/Agent A' ) && $ur( 7241, 'Anything' )
	&& $ur( 0, 'Restricted:Falcon/F1' ) && $ur( 0, "Restricted:Score/\xff" ) && $ur( 7240, 'Restricted:No form here' ),
	'U2 a title is restricted in the namespace, in the next number, read by classify as a restricted class, or unreadable (fail closed)' );
G::ok( !$ur( 0, 'Main Page' ) && !$ur( 0, 'Principia Machina/UWC/TST/Register/Volume 1' ) && !$ur( 0, 'Principia Machina/Spine' )
	&& !$ur( 4, 'Project:Restricted' ) && !$ur( 0, 'Restrictedx:Falcon/F1' ),
	'U3 an ordinary page, a public governed page and a title only resembling the namespace are not restricted' );
// Transclusion and the parser's reads of another page: the fetch refused for a restricted title, the inner one asked otherwise.
$asked = [];
$inner = static function ( $link, $parser = null ) use ( &$asked ) {
	$asked[] = [ $link, $parser ];
	return 'revision of ' . $link;
};
$isR = static fn ( $l ): bool => RestrictedRoutes::namesRestricted( (string)$l, $names );
$fetch = RestrictedRoutes::fetcher( $inner, $isR );
G::ok( $fetch( 'Restricted:Falcon/Stratum', 'p' ) === false && $fetch( ':Restricted:Score/A' ) === false && $asked === []
	&& $fetch( 'Template:Box', 'p' ) === 'revision of Template:Box' && $asked === [ [ 'Template:Box', 'p' ] ],
	'U4 transclusion: the parser\'s fetch answers no revision for a restricted page without asking further, and asks the wiki\'s own for any other' );
$set = RestrictedRoutes::settings( [ 'wgNonincludableNamespaces' => [ 10 ], 'wgNamespacesToBeSearchedDefault' => [ 0 => true, 7240 => true ] ], 7240 );
$set0 = RestrictedRoutes::settings( [], 7240 );
G::ok( $set['wgNonincludableNamespaces'] === [ 10, 7240, 7241 ] && $set['wgNamespacesToBeSearchedDefault'] === [ 0 => true, 7240 => false, 7241 => false ]
	&& $set0['wgNonincludableNamespaces'] === [ 7240, 7241 ]
	&& RestrictedRoutes::settings( $set, 7240 ) === $set,
	'U5 the settings: both numbers non-includable and not searched by default, the Operator\'s own values kept, applied twice the same' );
G::ok( RestrictedRoutes::searchable( [ 0 => '', 4 => 'Project', 7240 => 'Restricted', 7241 => '' ], $un ) === [ 0 => '', 4 => 'Project' ],
	'U6 search: the namespace and the next number are not searchable, every other namespace kept' );
G::ok( RestrictedRoutes::namesRestricted( 'Restricted:Score/A', $names ) && RestrictedRoutes::namesRestricted( ': restricted _ :x', $names )
	&& RestrictedRoutes::namesRestricted( 'RESTRICTED:Falcon/1', $names ) && RestrictedRoutes::namesRestricted( ' Restricted:', $names )
	&& !RestrictedRoutes::namesRestricted( 'Main:Restricted:x', $names ) && !RestrictedRoutes::namesRestricted( 'Score/A', $names )
	&& !RestrictedRoutes::namesRestricted( 'Restrictedx:y', $names ) && !RestrictedRoutes::namesRestricted( 'Restricted', $names ),
	'U7 a text names the namespace by its prefix in any case, with a leading colon, spaces and underscores, and only so' );
G::ok( RestrictedRoutes::requestNamesRestricted( [ 'action' => 'query', 'apnamespace' => '7240' ], $un )
	&& RestrictedRoutes::requestNamesRestricted( [ 'rcnamespace' => '0|7241' ], $un )
	&& RestrictedRoutes::requestNamesRestricted( [ 'gapnamespace' => " +07240 " ], $un )
	&& RestrictedRoutes::requestNamesRestricted( [ 'srnamespace' => "\x1f0\x1f7240" ], $un )
	&& RestrictedRoutes::requestNamesRestricted( [ 'namespace' => [ '7240' ] ], $un )
	&& RestrictedRoutes::requestNamesRestricted( [ 'PSNamespace' => '7240' ], $un )
	&& !RestrictedRoutes::requestNamesRestricted( [ 'rcnamespace' => '*' ], $un )
	&& !RestrictedRoutes::requestNamesRestricted( [ 'apnamespace' => '0|1|72400' ], $un )
	&& !RestrictedRoutes::requestNamesRestricted( [ 'titles' => '7240', 'pageids' => '7240' ], $un ),
	'U8 the API: a request naming 7240 or 7241 in any parameter ending in "namespace" is refused, in every form the API reads; "*" and other parameters are not' );
$q = [
	'pages' => [
		'12' => [ 'pageid' => 12, 'ns' => 7240, 'title' => 'Restricted:Falcon/Stratum', 'revisions' => [ [ 'user' => 'Custos', 'comment' => 'secret' ] ] ],
		'13' => [ 'pageid' => 13, 'ns' => 0, 'title' => 'Main Page', 'revisions' => [ [ 'user' => 'Reader', 'comment' => 'hello' ] ] ],
		'-1' => [ 'ns' => 7240, 'title' => 'Restricted:Score/Nobody', 'missing' => true ],
	],
	'allpages' => [ [ 'pageid' => 12, 'ns' => '7240', 'title' => 'Restricted:Falcon/Stratum' ], [ 'pageid' => 13, 'ns' => 0, 'title' => 'Main Page' ], '_element' => 'p' ],
	'recentchanges' => [ [ 'type' => 'new', 'ns' => 7240, 'title' => 'Restricted:Falcon/Stratum', 'comment' => 'secret' ], [ 'type' => 'edit', 'ns' => 0, 'title' => 'Main Page' ] ],
	'logevents' => [ [ 'ns' => 0, 'title' => 'Old', 'type' => 'move', 'params' => [ 'target_ns' => 7240, 'target_title' => 'Restricted:Falcon/Moved' ] ],
		[ 'ns' => 0, 'title' => 'Plain', 'type' => 'create' ] ],
	'search' => [ [ 'ns' => 7241, 'title' => 'X', 'snippet' => 'secret' ], [ 'ns' => 0, 'title' => 'Y', 'snippet' => 'open' ] ],
	'redirects' => [ [ 'from' => 'Shortcut', 'to' => 'Restricted:Falcon/Stratum' ], [ 'from' => 'A', 'to' => 'B' ] ],
	'searchinfo' => [ 'totalhits' => 2 ],
];
$clean = RestrictedRoutes::scrub( $q, $un, $names );
G::ok( array_keys( $clean['pages'] ) === [ 13 ] && $clean['allpages'] === [ [ 'pageid' => 13, 'ns' => 0, 'title' => 'Main Page' ], '_element' => 'p' ]
	&& $clean['recentchanges'] === [ [ 'type' => 'edit', 'ns' => 0, 'title' => 'Main Page' ] ]
	&& $clean['logevents'] === [ [ 'ns' => 0, 'title' => 'Plain', 'type' => 'create' ] ]
	&& $clean['search'] === [ [ 'ns' => 0, 'title' => 'Y', 'snippet' => 'open' ] ]
	&& $clean['redirects'] === [ [ 'from' => 'A', 'to' => 'B' ] ] && $clean['searchinfo'] === [ 'totalhits' => 2 ]
	&& strpos( json_encode( $clean ), 'secret' ) === false && strpos( json_encode( $clean ), 'Restricted' ) === false
	&& RestrictedRoutes::scrub( $clean, $un, $names ) === $clean,
	'U9 the API\'s query result: prop=revisions\' page, allpages, recentchanges, a move into the namespace, search and a redirect to it removed; every other item and the metadata kept',
	json_encode( $clean ) );
G::ok( RestrictedRoutes::exclusions( [ 'recentchanges', 'page' ], $un ) === [ 'rc_namespace NOT IN (7240,7241)', 'page_namespace NOT IN (7240,7241)' ]
	&& RestrictedRoutes::exclusions( [ 'rc' => 'recentchanges', 'actor' => 'actor', 'comment_rc_comment' => 'comment' ], $un ) === [ 'rc.rc_namespace NOT IN (7240,7241)' ]
	&& RestrictedRoutes::exclusions( [ 'revision', 'page', 'archive', 'logging', 'watchlist' ], $un )
		=== [ 'page_namespace NOT IN (7240,7241)', 'ar_namespace NOT IN (7240,7241)', 'log_namespace NOT IN (7240,7241)', 'wl_namespace NOT IN (7240,7241)' ]
	&& RestrictedRoutes::exclusions( [ 'revision', 'user' ], $un ) === [ '1 = 0' ]
	&& RestrictedRoutes::exclusions( [ 'page' ], [] ) === [ '1 = 0' ],
	'U10 the change lists, new pages, contributions, the prefix index and export: the namespace left out of each table with a namespace column; a query with none, or no numbers read, matches no row (fail closed)' );
$lu = new ArrayObject();
$other = new stdClass();
G::ok( RestrictedRoutes::keepUpdates( [ $other, $lu, $other ], true, ArrayObject::class ) === [ $other, $other ]
	&& RestrictedRoutes::keepUpdates( [ $other, $lu ], false, ArrayObject::class ) === [ $other, $lu ]
	&& RestrictedRoutes::LINKS_UPDATE === 'MediaWiki\\Deferred\\LinksUpdate\\LinksUpdate',
	'U11 the link tables: a restricted page\'s LinksUpdate dropped, its other updates kept; an ordinary page\'s kept whole' );
G::ok( RestrictedRoutes::integer( '07240' ) === 7240 && RestrictedRoutes::integer( ' +7241 ' ) === 7241 && RestrictedRoutes::integer( 7240 ) === 7240
	&& RestrictedRoutes::integer( '-7240' ) === null && RestrictedRoutes::integer( '7240a' ) === null && RestrictedRoutes::integer( '1e3' ) === null,
	'U12 a number read as the API reads an integer, and nothing else' );
// The routes core closes by its own read check (view, action=raw, action=render, action=history, diff=, Special:Export,
// the API's export, prop=revisions' content, action=parse, action=compare): each asks the permission hook "read".
$coreRead = [];
foreach ( [ 'agent', 'plain', 'anonymous', 'impostor', 'declarer', 'operator' ] as $who ) {
	$coreRead[$who] = [ $uk( 'Restricted:Falcon/Stratum', 'read', $who ), $uk( 'Restricted:Falcon/F1', 'read', $who ), $uk( 'Restricted:Score/Reader', 'read', $who ) ];
}
G::ok( $coreRead['agent'] === [ $uR, $uR, $uR ] && $coreRead['plain'] === [ $uR, $uR, $uR ] && $coreRead['anonymous'] === [ $uR, $uR, $uR ]
	&& $coreRead['impostor'] === [ $uR, $uR, $uR ] && $coreRead['declarer'] === [ null, null, null ] && $coreRead['operator'] === [ null, null, null ]
	&& $uk( 'Main Page', 'read', 'agent' ) === null,
	'U13 the routes core closes by its read check: the hook refuses "read" of a restricted page to an agent, a user, an anonymous reader and an impostor of the system user, admits the Declarer\'s and the Operator\'s groups, and leaves an ordinary page alone',
	json_encode( $coreRead ) );
[ $uRevs, $uPages, $uOver ] = RestrictedRoutes::ids( [ 'revids' => '12|0012|-3|x', 'oldid' => 7, 'fromrev' => "\x1f8\x1f9", 'torev' => ' 10 ',
	'pageids' => '5|6', 'pageid' => '5', 'fromid' => '40', 'toid' => '41', 'curid' => '42', 'rvstartid' => '99', 'titles' => '13' ] );
G::ok( $uRevs === [ 12, 7, 8, 9, 10 ] && $uPages === [ 5, 6, 40, 41, 42 ] && $uOver === false
	&& RestrictedRoutes::ids( [ 'revids' => implode( '|', range( 1, 501 ) ) ] )[2] === true && RestrictedRoutes::ids( [] ) === [ [], [], false ],
	'U15 the API\'s ids: the revisions (revids, oldid, fromrev, torev) and the pages (pageids, pageid, fromid, toid, curid) a request names, each looked up before any module answers; past 500 refused' );
G::ok( PermissionHook::refusal( $uR, 'Restricted:Falcon/Stratum' ) === [ $uR ]
	&& PermissionHook::refusal( PermissionHook::GOVERNED, 'Principia Machina/Spine' ) === [ PermissionHook::GOVERNED, 'Principia Machina/Spine' ],
	'U16 the hook\'s refusal of a restricted page names no title (oldid=, diff=, curid= would hand it out by its id); a governed page\'s names its public title' );
// The routes of the review rework: the random pages, the lists of every namespace, the protected pages, search by its
// prefix or "all:" (Special:Search, the API, the REST API), the moves into the namespace in the change lists.
$all = [ 'all', 'tout' ];
$sr = static fn ( string $name, ?string $sub, array $req = [], ?array $n = null ): bool
	=> RestrictedRoutes::specialRefused( $name, $sub, $req, $n ?? $un, $names, $all );
G::ok( $sr( 'Randompage', 'Restricted' ) && $sr( 'Randompage', 'restricted' ) && $sr( 'Randomredirect', 'Main,Restricted' )
	&& $sr( 'Randomrootpage', ' Restricted ,Project' ) && $sr( 'Randompage', null, [], [] )
	&& !$sr( 'Randompage', null ) && !$sr( 'Randompage', 'Project' ) && !$sr( 'Randompage', 'Main,Project' ) && !$sr( 'Randompage', 'Restrictedx' )
	&& !$sr( 'RandomInCategory', 'Restricted' ),
	'U17 Special:Random, RandomRedirect and RandomRootPage refused for a subpage naming the namespace, alone or in a comma list, in any case; any other subpage, and no subpage, admitted; no numbers read refuses' );
G::ok( $sr( 'Listredirects', null ) && $sr( 'BrokenRedirects', null ) && $sr( 'DoubleRedirects', null, [ 'namespace' => '0' ] ) && $sr( 'Unwatchedpages', null )
	&& $sr( 'Protectedpages', null ) && $sr( 'Protectedpages', null, [ 'namespace' => '' ] ) && $sr( 'Protectedtitles', null, [ 'namespace' => '7240' ] )
	&& $sr( 'Protectedtitles', null, [ 'namespace' => ' 07241' ] ) && !$sr( 'Protectedpages', null, [ 'namespace' => '0' ] )
	&& !$sr( 'Protectedtitles', null, [ 'namespace' => '4' ] ) && !$sr( 'Recentchanges', null ) && !$sr( 'Version', null, [], [] ),
	'U18 the lists of every namespace without a hook (ListRedirects, BrokenRedirects, DoubleRedirects, UnwatchedPages) refused whole; ProtectedPages and ProtectedTitles refused unless a public namespace is chosen; other special pages untouched' );
G::ok( $sr( 'Allpages', null, [ 'namespace' => '7240' ] ) && $sr( 'Allpages', null, [ 'from' => 'Restricted:F' ] ) && $sr( 'Prefixindex', 'Restricted:F' )
	&& $sr( 'Prefixindex', null, [ 'prefix' => 'restricted:x' ] ) && !$sr( 'Allpages', null ) && !$sr( 'Allpages', null, [ 'namespace' => '4', 'from' => 'A' ] ),
	'U19 Special:AllPages and Special:PrefixIndex: refused for the namespace by number or by the prefix of the subpage, from, to or prefix, as before' );
$sn = static fn ( string $q ): bool => RestrictedRoutes::searchNamesRestricted( $q, $names, $all );
G::ok( $sn( 'Restricted:Falcon' ) && $sn( 'all:word' ) && $sn( 'ALL: word' ) && $sn( ' all:word' ) && $sn( 'tout:mot' ) && $sn( ':restricted_:x' )
	&& !$sn( 'word' ) && !$sn( 'allwords:x' ) && !$sn( 'Main:all:x' ) && !$sn( 'Project:Restricted:x' )
	&& $sr( 'Search', null, [ 'search' => 'all:zq' ] ) && $sr( 'Search', 'Restricted:Falcon' ) && $sr( 'Search', null, [ 'search' => 'x', 'prefix' => 'Restricted:F' ] )
	&& !$sr( 'Search', null, [ 'search' => 'Falcon' ] ),
	'U20 search: a text naming the namespace by its prefix, or every namespace by "all:" or the wiki\'s own word, in any case, reaches a restricted page (the database search reads either unfiltered) and is refused, Special:Search by its search, prefix or subpage; any other text admitted' );
G::ok( RestrictedRoutes::restKind( '/v1/search/page' ) === 'search' && RestrictedRoutes::restKind( '/v1/search/title' ) === 'search'
	&& RestrictedRoutes::restKind( '/v1/search' ) === 'search' && RestrictedRoutes::restKind( '/x', true ) === 'search'
	&& RestrictedRoutes::restKind( '/site/v1/sitemap/0/page/0' ) === 'sitemap' && RestrictedRoutes::restKind( '/y', false, true ) === 'sitemap'
	&& RestrictedRoutes::restKind( '/v1/page/Main_Page' ) === null && RestrictedRoutes::restKind( '/v1/searchx' ) === null
	&& RestrictedRoutes::restRefused( 'search', 'all:zq', $un, $names, $all ) && RestrictedRoutes::restRefused( 'search', 'Restricted:Fal', $un, $names, $all )
	&& RestrictedRoutes::restRefused( 'search', [ 'x' ], $un, $names, $all ) && RestrictedRoutes::restRefused( 'search', 'Falcon', [], $names, $all )
	&& RestrictedRoutes::restRefused( 'sitemap', '', $un, $names, $all )
	&& !RestrictedRoutes::restRefused( 'search', 'Falcon', $un, $names, $all ) && !RestrictedRoutes::restRefused( null, 'all:x', $un, $names, $all ),
	'U23 the REST API: /v1/search/page and /v1/search/title refused for a text naming the namespace or every namespace ("all:"), the sitemap routes whole; another search and every other route untouched; no numbers read refuses' );
$like = static fn ( string $p ): string => " LIKE '%" . $p . "%'";
$mx = RestrictedRoutes::moveExclusion( [ 'Restricted', 'restricted' ], $like );
G::ok( $mx === "(rc_log_type IS NULL OR rc_log_type <> 'move' OR NOT (rc_params LIKE '%Restricted:%' OR rc_params LIKE '%restricted:%'))"
	&& RestrictedRoutes::moveExclusion( [ 'Restricted area' ], $like, 'rc.' )
		=== "(rc.rc_log_type IS NULL OR rc.rc_log_type <> 'move' OR NOT (rc.rc_params LIKE '%Restricted area:%' OR rc.rc_params LIKE '%Restricted_area:%'))"
	&& RestrictedRoutes::moveExclusion( [], $like ) === "(rc_log_type IS NULL OR rc_log_type <> 'move')",
	'U21 the change lists: a move whose target the parameters name in the namespace left out (its row carries the source\'s namespace), every other row kept; no names read leaves out every move (fail closed)', $mx );
$rcMove = [ 'recentchanges' => [ [ 'type' => 'log', 'ns' => 0, 'title' => 'Old', 'logtype' => 'move', 'logparams' => [ 'target_ns' => 7240, 'target_title' => 'Restricted:Falcon/Moved' ] ],
	[ 'type' => 'log', 'ns' => 0, 'title' => 'Old2', 'logtype' => 'move', 'logparams' => [ 'target_ns' => 0, 'target_title' => 'New2' ] ] ] ];
G::ok( RestrictedRoutes::scrub( $rcMove, $un, $names ) === [ 'recentchanges' => [ $rcMove['recentchanges'][1] ] ],
	'U22 the API\'s list=recentchanges: a move into the namespace removed whole by its logparams, its source title with it; a move elsewhere kept' );
G::ok( RestrictedRoutes::refusedStatus( true, false ) === 403 && RestrictedRoutes::refusedStatus( true, true ) === null
	&& RestrictedRoutes::refusedStatus( false, false ) === null && RestrictedRoutes::refusedStatus( false, true ) === null,
	'U24 index.php\'s answer: a restricted page the asker may not read answers 403 (MediaWiki renders the hook\'s refusal as a page answered 200); a readable restricted page and every other page keep MediaWiki\'s own status' );
// U25: the handler itself, onBeforeInitialize, on stubs: the status it sets on the output, through its three questions.
if ( !interface_exists( 'MediaWiki\Config\Config' ) ) {
	eval( 'namespace MediaWiki\Config; interface Config { public function get( $name ); public function has( $name ); }' );
}
$u25Config = new class implements MediaWiki\Config\Config {
	public function get( $name ) { return 7240; }
	public function has( $name ) { return true; }
};
$u25Out = new class { public $status = null; public function setStatusCode( $c ) { $this->status = $c; } };
$u25Req = static fn ( array $v ) => new class( $v ) {
	public function __construct( private array $v ) {}
	public function getVal( $k, $d = null ) { return $this->v[$k] ?? $d; }
};
$u25Throw = static function () { throw new RuntimeException( 'fault' ); };
$u25Restricted = static fn ( $t ) => str_starts_with( (string)$t, 'Restricted:' );
$u25Redirects = static fn ( $t ) => [ 'Shortcut' => 'Restricted:Falcon/Stratum', 'Public shortcut' => 'Main Page' ][(string)$t] ?? null;
$u25Run = static function ( string $title, array $req, ?Closure $restricted, ?Closure $redirect, ?Closure $read ) use ( $u25Config, $u25Out, $u25Req ): ?int {
	$h = new RestrictedRoutes( $u25Config, $restricted, $redirect, $read );
	$out = clone $u25Out;
	$h->onBeforeInitialize( $title, null, $out, 'asker', $u25Req( $req ), null );
	return $out->status;
};
$u25No = static fn ( $u, $t ) => false;
$u25Yes = static fn ( $u, $t ) => true;
$u25 = [
	'restricted, unreadable' => $u25Run( 'Restricted:Falcon/Stratum', [], $u25Restricted, $u25Redirects, $u25No ),
	'restricted, readable' => $u25Run( 'Restricted:Falcon/Stratum', [], $u25Restricted, $u25Redirects, $u25Yes ),
	'public' => $u25Run( 'Main Page', [], $u25Restricted, $u25Redirects, $u25No ),
	'redirect to it, viewed' => $u25Run( 'Shortcut', [], $u25Restricted, $u25Redirects, $u25No ),
	'redirect to it, readable' => $u25Run( 'Shortcut', [], $u25Restricted, $u25Redirects, $u25Yes ),
	'redirect to it, redirect=no' => $u25Run( 'Shortcut', [ 'redirect' => 'no' ], $u25Restricted, $u25Redirects, $u25No ),
	'redirect to it, history' => $u25Run( 'Shortcut', [ 'action' => 'history' ], $u25Restricted, $u25Redirects, $u25No ),
	'redirect to it, render' => $u25Run( 'Shortcut', [ 'action' => 'render' ], $u25Restricted, $u25Redirects, $u25No ),
	'redirect to it, oldid' => $u25Run( 'Shortcut', [ 'oldid' => '7' ], $u25Restricted, $u25Redirects, $u25No ),
	'redirect to a public page' => $u25Run( 'Public shortcut', [], $u25Restricted, $u25Redirects, $u25No ),
	'userCan throws' => $u25Run( 'Restricted:Falcon/Stratum', [], $u25Restricted, $u25Redirects, $u25Throw ),
	'isRestricted throws' => $u25Run( 'Main Page', [], $u25Throw, $u25Redirects, $u25Yes ),
	'the redirect lookup throws' => $u25Run( 'Main Page', [], $u25Restricted, $u25Throw, $u25Yes ),
];
G::ok( $u25 === [ 'restricted, unreadable' => 403, 'restricted, readable' => null, 'public' => null, 'redirect to it, viewed' => 403,
		'redirect to it, readable' => null, 'redirect to it, redirect=no' => null, 'redirect to it, history' => null, 'redirect to it, render' => 403, 'redirect to it, oldid' => null,
		'redirect to a public page' => null, 'userCan throws' => 403, 'isRestricted throws' => 403, 'the redirect lookup throws' => 403 ]
	&& RestrictedRoutes::followsRedirect( 'view', null ) && !RestrictedRoutes::followsRedirect( 'view', 'no' ) && !RestrictedRoutes::followsRedirect( 'raw', null ) && RestrictedRoutes::followsRedirect( 'render', null ) && !RestrictedRoutes::followsRedirect( 'view', null, true ),
	'U25 onBeforeInitialize on stubs: 403 set on the output for a restricted page the asker may not read and for the view or render of a redirect to one; nothing set for a readable one, a public page, a redirect not followed (redirect=no, another action, an old revision) or to a public page; a fault in the read check, the restricted test or the redirect lookup sets 403 (fail closed)',
	json_encode( $u25 ) );

// Every handler wired: each method on<Hook> of RestrictedRoutes is named by extension.json under the handler "restricted", and back.
$ej = json_decode( (string)file_get_contents( "$root/custos/extension.json" ), true );
$wired = array_keys( array_filter( $ej['Hooks'] ?? [], static fn ( $h ) => in_array( 'restricted', (array)$h, true ) ) );
$methods = array_values( array_filter( get_class_methods( RestrictedRoutes::class ),
	static fn ( string $m ) => str_starts_with( $m, 'on' ) && $m !== 'onRegistration' ) );
$wantMethods = array_map( static fn ( string $h ) => 'on' . strtr( $h, ':', '_' ), $wired );
sort( $methods );
sort( $wantMethods );
G::ok( $methods === $wantMethods && count( $methods ) === 19 && ( $ej['HookHandlers']['restricted']['class'] ?? '' ) === 'Custos\\RestrictedRoutes'
	&& ( $ej['callback'] ?? '' ) === 'Custos\\RestrictedRoutes::onRegistration',
	'U14 every route\'s handler wired: the 19 hooks of RestrictedRoutes named in extension.json under "restricted", each with its method, and the settings\' callback',
	json_encode( [ $methods, $wantMethods ] ) );

// ---- R: the built pcalc, when it exists -----------------------------------------------------

$built = "$root/.lake/build/bin/pcalc";
if ( is_file( $built ) && is_executable( $built ) ) {
	$basic = (string)file_get_contents( "$root/Principia/Basic.lean" );
	$version = preg_match( '/^def version : String := "([^"]+)"$/m', $basic, $m ) ? $m[1] : '';
	G::ok( $version !== '', "R1 Principia/Basic.lean defines the version ($version)" );
	calculator_calls( 'R', $built, [ 'version' => $version, 'digest' => Calculator::digestOf( $built ) ], $request, $answer );
	$c = new Calculator( $built, [ 'version' => $version, 'digest' => Calculator::digestOf( $built ) ], new ProcRunner(), 'cli', new AnyResidence() );
	$r = $c->call( 'canonical', 'canonical_json', '{"value":1' );
	G::ok( $r['exit'] === 1 && $r['refused'] === 'UNEXPECTED_END', 'R7 pcalc\'s refusal of a request is read', json_encode( $r ) );
	echo "calculator: the built pcalc, version $version, digest ", Calculator::digestOf( $built ), "\n";
	// Version 1's landing gates a1, a2, b1, b1-fault, b1-range, b1-inc4 and b1-repro replayed as scenarios, in their own process.
	$sOut = [];
	$sExit = 1;
	exec( escapeshellarg( PHP_BINARY ) . ' ' . escapeshellarg( __DIR__ . '/scenarios.php' ) . ' 2>&1', $sOut, $sExit );
	$sLine = (string)( end( $sOut ) ?: '' );
	G::ok( $sExit === 0 && str_starts_with( $sLine, 'scenarios: ALL PASS ' ), "R8 version 1's landing gates a1, a2, b1, b1-fault, b1-range, b1-inc4 and b1-repro replayed as scenarios: $sLine",
		implode( "\n", array_slice( $sOut, -12 ) ) );
	echo "$sLine\n";
} else {
	echo "calculator: no built pcalc in this clone (.lake/build/bin/pcalc); R not run\n";
}

exit( G::report( 'harness' ) );
