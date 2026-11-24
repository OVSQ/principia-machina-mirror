<?php
/**
 * kernel_checker.php: KernelChecker's own test, over the stand-in checker fake_checker.sh (its
 * digest in fake_checker.sha256) copied into a scratch folder, through ProcRunner.
 *
 *   php custos/tests/kernel_checker.php
 *
 * Accepted on exit 0 with the expected output alone; refused, with only its word, on a wrong
 * statement, on exit 1, on a timeout, on a digest mismatch, an unsafe residence, a prelude
 * mismatch or a configuration that permits another axiom (the last four with the binary never
 * started); refused on an exit that is not the integer 0, a line after the "Checked" line, an
 * expected statement with a line feed inside it, and a configuration with a key outside T5's own
 * or a repeated key. Prints one line per case and "kernel checker: ALL PASS <n>/<n>". Command line only;
 * it touches no wiki and needs no pcalc.
 */

declare( strict_types=1 );

require_once __DIR__ . '/bootstrap.php';

use Custos\Calculator;
use Custos\KernelChecker;
use Custos\ResidenceCheck;
use Custos\Tests\AnyResidence;
use Custos\Tests\ProcRunner;

$scratch = sys_get_temp_dir() . '/custos-kernel-checker-' . getmypid();
@mkdir( $scratch, 0700, true );

$source = __DIR__ . '/fake_checker.sh';
$digest = trim( (string)file_get_contents( __DIR__ . '/fake_checker.sha256' ) );
G::ok( Calculator::digestOf( $source ) === $digest, 'K1 the stand-in digests to fake_checker.sha256',
	Calculator::digestOf( $source ) );
$bin = "$scratch/fake_checker.sh";
copy( $source, $bin );
chmod( $bin, 0755 );

$config = [ 'use_stdin' => true, 'permitted_axioms' => [ 'propext', 'Classical.choice', 'Quot.sound' ],
	'unpermitted_axiom_hard_error' => true, 'num_threads' => 1 ];
file_put_contents( "$scratch/config.json", json_encode( $config ) . "\n" );
$prelude = "{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n{\"prelude\":1}\n";
file_put_contents( "$scratch/prelude.ndjson", $prelude );
$statement = 'theorem Fake.t : 1 + 1 = 2';

$conf = [ 'binary' => $bin, 'digest' => $digest, 'config' => "$scratch/config.json", 'prelude' => "$scratch/prelude.ndjson",
	'prelude_digest' => hash( 'sha256', $prelude ), 'seconds' => 1 ];

/** A checker over $conf (with $over applied) and its runner. */
$make = static function ( array $over = [], $residence = null ) use ( $conf ): array {
	$runner = new ProcRunner();
	return [ new KernelChecker( array_merge( $conf, $over ), $runner, $residence ?? new AnyResidence(), 'cli' ), $runner ];
};
$refusedAs = static fn ( array $a, string $w ): bool => $a === [ 'verdict' => KernelChecker::REFUSED, 'word' => $w ];

// Accepted: exit 0, the statement, the "Checked" line.
[ $kc, $r ] = $make();
$a = $kc->check( $prelude . "CASE accept\n", $statement );
G::ok( $a === [ 'verdict' => KernelChecker::ACCEPTED ] && $r->starts === 1, 'K2 exit 0 with the statement and the Checked line is accepted',
	json_encode( [ $a, $r->starts ] ) );
$a = $kc->check( $prelude . "CASE accept\n", $statement . "\n" );
G::ok( $a === [ 'verdict' => KernelChecker::ACCEPTED ], 'K3 the expected statement\'s trailing line feed is not part of it', json_encode( $a ) );

// Refused on a wrong line: the checker accepts a different statement.
$a = $kc->check( $prelude . "CASE wrong\n", $statement );
G::ok( $refusedAs( $a, KernelChecker::OUTPUT ), 'K4 exit 0 with another statement is refused "output"', json_encode( $a ) );
$a = $kc->check( $prelude . "CASE accept\n", 'theorem Fake.t : 1 + 1' );
G::ok( $refusedAs( $a, KernelChecker::OUTPUT ), 'K5 an expected statement that is only a prefix of the printed one is refused "output"', json_encode( $a ) );

// Refused on exit 1 (the unpermitted axiom, T5 case C) and on any other non-zero exit.
$a = $kc->check( $prelude . "CASE axiom\n", $statement );
G::ok( $refusedAs( $a, KernelChecker::EXIT ), 'K6 exit 1 is refused "exit"', json_encode( $a ) );
$a = $kc->check( $prelude . "CASE unknown\n", $statement );
G::ok( $refusedAs( $a, KernelChecker::EXIT ), 'K7 exit 2 is refused "exit"', json_encode( $a ) );

// Refused on a timeout, whatever the checker answered after it.
[ $kc, $r ] = $make();
$began = microtime( true );
$a = $kc->check( $prelude . "CASE sleep\n", $statement );
G::ok( $refusedAs( $a, KernelChecker::TIMEOUT ) && $r->starts === 1, 'K8 a run past its limit is refused "timeout", though it ended with exit 0 and the expected output',
	sprintf( '%s in %.1f s', json_encode( $a ), microtime( true ) - $began ) );
$tick = 0.0;
$kc = new KernelChecker( $conf, new ProcRunner(), new AnyResidence(), 'cli', static function () use ( &$tick ): float {
	return $tick += 1.0;
} );
$a = $kc->check( $prelude . "CASE accept\n", $statement );
G::ok( $refusedAs( $a, KernelChecker::TIMEOUT ), 'K9 a run whose measured time equals the limit is refused "timeout"', json_encode( $a ) );

// Refused on a digest mismatch, never started.
[ $kc, $r ] = $make( [ 'digest' => str_repeat( '0', 64 ) ] );
$a = $kc->check( $prelude . "CASE accept\n", $statement );
G::ok( $refusedAs( $a, KernelChecker::DIGEST_MISMATCH ) && $r->starts === 0 && $kc->starts === 0,
	'K10 a binary that does not digest to the configured digest is refused "digest mismatch" and never started', json_encode( [ $a, $r->starts ] ) );
[ $kc, $r ] = $make();
$a = $kc->check( $prelude . "CASE accept\n", $statement );
$changed = "$scratch/changed.sh";
copy( $bin, $changed );
file_put_contents( $changed, "\n", FILE_APPEND );
chmod( $changed, 0755 );
$b = ( new KernelChecker( array_merge( $conf, [ 'binary' => $changed ] ), $r, new AnyResidence(), 'cli' ) )->check( $prelude . "CASE accept\n", $statement );
G::ok( $a['verdict'] === KernelChecker::ACCEPTED && $refusedAs( $b, KernelChecker::DIGEST_MISMATCH ) && $r->starts === 1,
	'K11 the stand-in changed by one byte is refused "digest mismatch" and never started', json_encode( [ $a, $b, $r->starts ] ) );

// Refused on an unsafe residence, never started: the live check over the scratch folder as its
// root (owned by the running user, so refused for root and for any other user alike).
[ $kc, $r ] = $make( [], new ResidenceCheck( [ $scratch ] ) );
$a = $kc->check( $prelude . "CASE accept\n", $statement );
G::ok( $refusedAs( $a, KernelChecker::UNSAFE_RESIDENCE ) && $r->starts === 0,
	'K12 a binary in a residence the running user can write is refused "unsafe residence" and never started', json_encode( [ $a, $r->starts ] ) );
$any = new class implements \Custos\Residence {
	public array $seen = [];
	public function check( string $path ): void {
		$this->seen[] = basename( $path );
		if ( basename( $path ) === 'config.json' ) {
			throw new \Custos\UnsafeResidence( $path, 'is writable by group or other' );
		}
	}
};
[ $kc, $r ] = $make( [], $any );
$a = $kc->check( $prelude . "CASE accept\n", $statement );
G::ok( $refusedAs( $a, KernelChecker::UNSAFE_RESIDENCE ) && $r->starts === 0 && $any->seen === [ 'fake_checker.sh', 'config.json' ],
	'K13 the configuration file\'s residence is checked as the binary\'s: unsafe, refused and never started', json_encode( [ $a, $any->seen ] ) );

// Refused on a prelude digest mismatch, never started: the prelude file is not the configured
// one, or the export does not open with it.
[ $kc, $r ] = $make( [ 'prelude_digest' => hash( 'sha256', 'another prelude' ) ] );
$a = $kc->check( $prelude . "CASE accept\n", $statement );
G::ok( $refusedAs( $a, KernelChecker::PRELUDE_MISMATCH ) && $r->starts === 0,
	'K14 a prelude whose digest is not the configured one is refused "prelude mismatch" and never started', json_encode( [ $a, $r->starts ] ) );
[ $kc, $r ] = $make();
$a = $kc->check( "{\"prelude\":2}\nCASE accept\n", $statement );
G::ok( $refusedAs( $a, KernelChecker::PRELUDE_MISMATCH ) && $r->starts === 0,
	'K15 an export that does not open with the fixed prelude is refused "prelude mismatch" and never started', json_encode( [ $a, $r->starts ] ) );

// Refused on a configuration that permits another axiom, or none of the hard-error rule.
$bad = [
	'a fourth axiom' => array_merge( $config, [ 'permitted_axioms' => [ 'propext', 'Classical.choice', 'Quot.sound', 'pmaT5Unpermitted' ] ] ),
	'two of the three' => array_merge( $config, [ 'permitted_axioms' => [ 'propext', 'Quot.sound' ] ] ),
	'a repeated axiom' => array_merge( $config, [ 'permitted_axioms' => [ 'propext', 'Classical.choice', 'Quot.sound', 'propext' ] ] ),
	'no hard error' => array_merge( $config, [ 'unpermitted_axiom_hard_error' => false ] ),
	'no stdin' => array_merge( $config, [ 'use_stdin' => false ] ),
];
$seen = [];
foreach ( $bad as $what => $c ) {
	file_put_contents( "$scratch/bad.json", json_encode( $c ) . "\n" );
	[ $kc, $r ] = $make( [ 'config' => "$scratch/bad.json" ] );
	$a = $kc->check( $prelude . "CASE accept\n", $statement );
	if ( !$refusedAs( $a, KernelChecker::CONFIGURATION ) || $r->starts !== 0 ) {
		$seen[] = $what;
	}
}
G::ok( $seen === [], 'K16 a configuration with a fourth axiom, two of the three, a repeated one, no hard error or no stdin is refused "configuration" and never started',
	implode( ', ', $seen ) );

// Refused in a web request and when not configured, never started.
$r = new ProcRunner();
$a = ( new KernelChecker( $conf, $r, new AnyResidence(), 'apache2handler' ) )->check( $prelude . "CASE accept\n", $statement );
$b = ( new KernelChecker( array_merge( $conf, [ 'binary' => '' ] ), $r, new AnyResidence(), 'cli' ) )->check( $prelude . "CASE accept\n", $statement );
$c = ( new KernelChecker( $conf, $r, new AnyResidence(), 'cli' ) )->check( $prelude . "CASE accept\n", '' );
G::ok( $refusedAs( $a, KernelChecker::WEB_REQUEST ) && $refusedAs( $b, KernelChecker::NOT_CONFIGURED ) && $refusedAs( $c, KernelChecker::NOT_CONFIGURED )
	&& $r->starts === 0, 'K17 a web request is refused "web request"; an empty binary or an empty expected statement "not configured"; none started',
	json_encode( [ $a, $b, $c ] ) );

// The runner's answer read strictly: an exit that is not the integer 0 is refused "exit", though
// the output is the expected one; a line after the "Checked" line is refused "output". A stub
// runner stands in, since the stand-in checker answers through a real process (an integer).
$stub = static function ( $exit, string $out ): object {
	return new class( $exit, $out ) implements \Custos\ShellRunner {
		public int $starts = 0;
		/** @param mixed $exit */
		public function __construct( private $exit, private string $out ) {
		}
		public function run( array $argv, string $stdin ): array {
			$this->starts++;
			return [ $this->exit, $this->out, '' ];
		}
	};
};
$good = "$statement\nChecked 3 declarations with no errors\n";
$seen = [];
foreach ( [ 'null' => null, 'false' => false, 'empty' => '', 'the text 0' => '0', 'the float 0.0' => 0.0, 'true' => true ] as $what => $exit ) {
	$r = $stub( $exit, $good );
	$a = ( new KernelChecker( $conf, $r, new AnyResidence(), 'cli' ) )->check( $prelude . "CASE accept\n", $statement );
	if ( !$refusedAs( $a, KernelChecker::EXIT ) || $r->starts !== 1 ) {
		$seen[] = $what;
	}
}
$r = $stub( 0, $good );
$a = ( new KernelChecker( $conf, $r, new AnyResidence(), 'cli' ) )->check( $prelude . "CASE accept\n", $statement );
G::ok( $seen === [] && $a === [ 'verdict' => KernelChecker::ACCEPTED ],
	'K19 an exit of null, false, "", "0", 0.0 or true is refused "exit" with the expected output; the integer 0 is accepted',
	json_encode( [ $seen, $a ] ) );
$r = $stub( 0, $good . "theorem Fake.u : 2 = 2\n" );
$a = ( new KernelChecker( $conf, $r, new AnyResidence(), 'cli' ) )->check( $prelude . "CASE accept\n", $statement );
G::ok( $refusedAs( $a, KernelChecker::OUTPUT ), 'K20 a line after the "Checked" line is refused "output"', json_encode( $a ) );

// An expected statement with a line feed inside it is refused "not configured", never started: it
// could take the "Checked" line into itself and match an output of more lines.
$two = "$statement\nChecked 3 declarations with no errors";
$r = $stub( 0, "$two\nChecked 3 declarations with no errors\n" );
$a = ( new KernelChecker( $conf, $r, new AnyResidence(), 'cli' ) )->check( $prelude . "CASE accept\n", $two );
$r2 = $stub( 0, $good );
$b = ( new KernelChecker( $conf, $r2, new AnyResidence(), 'cli' ) )->check( $prelude . "CASE accept\n", "theorem Fake.t :\n1 + 1 = 2" );
G::ok( $refusedAs( $a, KernelChecker::NOT_CONFIGURED ) && $refusedAs( $b, KernelChecker::NOT_CONFIGURED ) && $r->starts === 0 && $r2->starts === 0,
	'K21 an expected statement with a line feed inside it is refused "not configured" and never started', json_encode( [ $a, $b ] ) );

// The configuration's keys are allow-listed (T5's own, ops/t5/t5_cases.py) and none is repeated, at
// any depth: a repeated key the decoder would resolve to its last value is refused.
$text = json_encode( $config );
$badText = [
	'an unknown key' => json_encode( array_merge( $config, [ 'permit_any_axiom' => true ] ) ),
	'a repeated key, the last one true' => '{"use_stdin":false,' . substr( $text, 1 ),
	'a repeated key, written with an escape' => '{"use\\u005fstdin":false,' . substr( $text, 1 ),
	'a repeated key in a nested object' => substr( $text, 0, -1 ) . ',"pp_options":{"proofs":false,"proofs":true}}',
	'not an object' => '[' . $text . ']',
];
$seen = [];
foreach ( $badText as $what => $t ) {
	file_put_contents( "$scratch/bad.json", $t . "\n" );
	[ $kc, $r ] = $make( [ 'config' => "$scratch/bad.json" ] );
	$a = $kc->check( $prelude . "CASE accept\n", $statement );
	if ( !$refusedAs( $a, KernelChecker::CONFIGURATION ) || $r->starts !== 0 ) {
		$seen[] = $what;
	}
}
$full = [ 'use_stdin' => true, 'permitted_axioms' => [ 'propext', 'Classical.choice', 'Quot.sound' ], 'unpermitted_axiom_hard_error' => true,
	'nat_extension' => true, 'string_extension' => true, 'num_threads' => 1, 'print_axioms' => false, 'print_success_message' => true,
	'pp_declars' => [ 'Fake.t' ], 'pp_to_stdout' => true, 'pp_options' => [ 'proofs' => false, 'width' => 100 ] ];
file_put_contents( "$scratch/full.json", json_encode( $full, JSON_PRETTY_PRINT ) . "\n" );
[ $kc, $r ] = $make( [ 'config' => "$scratch/full.json" ] );
$a = $kc->check( $prelude . "CASE accept\n", $statement );
G::ok( $seen === [] && $a === [ 'verdict' => KernelChecker::ACCEPTED ],
	'K22 a configuration with an unknown key, a repeated key (plain, escaped or nested) or not an object is refused "configuration" and never started; T5\'s own keys are accepted',
	json_encode( [ $seen, $a ] ) );

// A refusal says its word alone: no path, no digest, no output; and every word is in WORDS.
$src = (string)file_get_contents( dirname( __DIR__ ) . '/includes/KernelChecker.php' );
preg_match_all( '/self::refused\(\s*self::([A-Z_]+)\s*\)/', $src, $m );
$used = array_values( array_unique( array_map( static fn ( string $n ): string => constant( KernelChecker::class . '::' . $n ), $m[1] ) ) );
sort( $used );
$words = KernelChecker::WORDS;
sort( $words );
G::ok( $used === $words && preg_match_all( '/self::refused\(/', $src ) === count( $m[1] ),
	'K18 every refusal in KernelChecker names a constant word of WORDS and nothing else, and every word is used', json_encode( [ $used, $words ] ) );

foreach ( glob( "$scratch/*" ) ?: [] as $f ) {
	@unlink( $f );
}
@rmdir( $scratch );
exit( G::report( 'kernel checker' ) );
