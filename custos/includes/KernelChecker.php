<?php
/**
 * KernelChecker: Custos's one way into an independent Lean kernel checker, for a RESULT whose
 * DERIVATION is a KERNEL proof (charter 8.7, test T5; ops/t5/README.md). One object is one
 * checker binary; where two checkers are both required, the call is made once on each.
 *
 * `check($proofText, $expectedStatement)` answers ["verdict" => "accepted"] or
 * ["verdict" => "refused", "word" => one of WORDS]. The word is all a refusal says: no path,
 * no digest, no checker output. Acceptance is exit 0 with the expected output alone: the
 * checker prints the checked theorem's statement (without its proof), then the line
 * "Checked <n> declarations with no errors", and nothing else. Every other outcome is a
 * refusal; nothing here throws for a refusal, so a caller cannot mistake an exception path for
 * acceptance.
 *
 * Before the first start, once per object, the residence of the binary and of the checker's
 * configuration file is checked (Residence: the same check as the Calculator's binary, D10),
 * and the configuration is read: one JSON object, its keys in CONFIG_KEYS and none repeated; it
 * must take the export on stdin, permit exactly the three
 * axioms of T5 (PERMITTED) and make any other axiom a hard error. Before every start the
 * binary's SHA-256 digest is compared with the configured one, the prelude file's digest with
 * the configured prelude digest, and the export must open with the prelude's bytes, so what the
 * checker checks is the fixed prelude and the proof's own items after it. A failure of any of
 * these refuses with the binary not started.
 *
 * The run is boxed: the live runner is BoxedRunner (MediaWiki's shell framework, network off,
 * the wiki's $wgMaxShell* limits stopping the process); the export goes on stdin, the
 * configuration's path is the one argument. A run whose wall time reaches the configured
 * seconds is refused "timeout" whatever it answered. Never inside a web request, as the
 * Calculator.
 *
 * The configuration comes to the constructor; the wiki's keys and the landing's use of the
 * answer are not here. The runner's exit is read strictly: only the integer 0 is a success. The Residence is required: the wiki's side makes no residence check of
 * its own outside the Calculator, so the caller passes the live one.
 */

namespace Custos;

final class KernelChecker {
	/** The axioms a checked proof may use, T5's three (ops/t5/README.md, "the configuration"). */
	public const PERMITTED = [ 'Classical.choice', 'Quot.sound', 'propext' ];
	/** The default limit of one run, in seconds. */
	public const SECONDS = 10;

	public const ACCEPTED = 'accepted';
	public const REFUSED = 'refused';

	/** The refusal words, a closed set. */
	public const WEB_REQUEST = 'web request';
	public const NOT_CONFIGURED = 'not configured';
	public const UNSAFE_RESIDENCE = 'unsafe residence';
	public const CONFIGURATION = 'configuration';
	public const DIGEST_MISMATCH = 'digest mismatch';
	public const PRELUDE_MISMATCH = 'prelude mismatch';
	public const TIMEOUT = 'timeout';
	public const EXIT = 'exit';
	public const OUTPUT = 'output';
	public const WORDS = [ self::WEB_REQUEST, self::NOT_CONFIGURED, self::UNSAFE_RESIDENCE, self::CONFIGURATION,
		self::DIGEST_MISMATCH, self::PRELUDE_MISMATCH, self::TIMEOUT, self::EXIT, self::OUTPUT ];

	/** The PHP SAPIs that are not a web request. */
	private const COMMAND_LINE = [ 'cli', 'phpdbg' ];
	private const HEX64 = '/^[0-9a-f]{64}$/';
	/**
	 * The configuration's keys: the three it must hold and the rest T5's own configuration
	 * carries (ops/t5/t5_cases.py); any other key is refused.
	 */
	public const CONFIG_KEYS = [ 'use_stdin', 'permitted_axioms', 'unpermitted_axiom_hard_error', 'nat_extension',
		'string_extension', 'num_threads', 'print_axioms', 'print_success_message', 'pp_declars', 'pp_to_stdout', 'pp_options' ];
	/** The checker's last line on acceptance. */
	private const CHECKED = '/^Checked [0-9]+ declarations with no errors$/';

	private string $binary;
	private string $digest;
	private string $configFile;
	private string $prelude;
	private string $preludeDigest;
	private float $seconds;
	private ShellRunner $runner;
	private Residence $residence;
	private string $sapi;
	/** @var callable(): float */
	private $clock;
	private bool $ready = false;
	/** Starts of the binary by this object (the tests count them). */
	public int $starts = 0;

	/**
	 * @param array $config "binary" (absolute path), "digest" (its SHA-256, 64 lowercase
	 *   hexadecimal digits), "config" (the checker's configuration file, absolute path),
	 *   "prelude" (the fixed prelude's export file), "prelude_digest" (its SHA-256),
	 *   "seconds" (the limit of one run; SECONDS when absent)
	 * @param Residence $residence the residence check; the live one is the Calculator's
	 * @param callable|null $clock seconds as a float; microtime(true) when null
	 */
	public function __construct( array $config, ShellRunner $runner, Residence $residence, string $sapi = PHP_SAPI,
		?callable $clock = null
	) {
		$this->binary = self::text( $config['binary'] ?? null );
		$this->digest = self::text( $config['digest'] ?? null );
		$this->configFile = self::text( $config['config'] ?? null );
		$this->prelude = self::text( $config['prelude'] ?? null );
		$this->preludeDigest = self::text( $config['prelude_digest'] ?? null );
		$s = $config['seconds'] ?? self::SECONDS;
		$this->seconds = is_int( $s ) || is_float( $s ) ? (float)$s : 0.0;
		$this->runner = $runner;
		$this->residence = $residence;
		$this->sapi = $sapi;
		$this->clock = $clock ?? static fn (): float => microtime( true );
	}

	/**
	 * Check $proofText, an export in the checker's format opening with the fixed prelude,
	 * against $expectedStatement, the statement the checker must print for the proved theorem.
	 *
	 * @return array{verdict: string, word?: string}
	 */
	public function check( string $proofText, string $expectedStatement ): array {
		if ( !in_array( $this->sapi, self::COMMAND_LINE, true ) ) {
			return self::refused( self::WEB_REQUEST );
		}
		if ( $this->binary === '' || $this->configFile === '' || $this->prelude === ''
			|| !preg_match( self::HEX64, $this->digest ) || !preg_match( self::HEX64, $this->preludeDigest )
			|| !( $this->seconds > 0 ) || trim( $expectedStatement ) === ''
			|| str_contains( rtrim( $expectedStatement, "\n" ), "\n" )
		) {
			return self::refused( self::NOT_CONFIGURED );
		}
		if ( !$this->ready ) {
			try {
				$this->residence->check( $this->binary );
				$this->residence->check( $this->configFile );
			} catch ( UnsafeResidence $e ) {
				return self::refused( self::UNSAFE_RESIDENCE );
			}
			if ( !self::configured( $this->configFile ) ) {
				return self::refused( self::CONFIGURATION );
			}
			$this->ready = true;
		}
		if ( Calculator::digestOf( $this->binary ) !== $this->digest ) {
			return self::refused( self::DIGEST_MISMATCH );
		}
		$prelude = is_file( $this->prelude ) && is_readable( $this->prelude ) ? file_get_contents( $this->prelude ) : false;
		if ( !is_string( $prelude ) || $prelude === '' || self::digestOfBytes( $prelude ) !== $this->preludeDigest
			|| !str_starts_with( $proofText, $prelude )
		) {
			return self::refused( self::PRELUDE_MISMATCH );
		}

		$this->starts++;
		$began = ( $this->clock )();
		[ $exit, $out ] = $this->runner->run( [ $this->binary, $this->configFile ], $proofText );
		$took = ( $this->clock )() - $began;
		if ( $took >= $this->seconds ) {
			return self::refused( self::TIMEOUT );
		}
		if ( $exit !== 0 ) {
			return self::refused( self::EXIT );
		}
		if ( !self::expected( (string)$out, $expectedStatement ) ) {
			return self::refused( self::OUTPUT );
		}
		return [ 'verdict' => self::ACCEPTED ];
	}

	/**
	 * The output is the statement, then the "Checked" line, each ending in a line feed, and
	 * nothing else; the statement compared byte for byte, its trailing line feeds aside. A
	 * statement with a line feed inside it never reaches here (check() refuses it).
	 */
	private static function expected( string $out, string $statement ): bool {
		$statement = rtrim( $statement, "\n" );
		if ( !str_starts_with( $out, $statement . "\n" ) || substr( $out, -1 ) !== "\n" ) {
			return false;
		}
		$rest = substr( $out, strlen( $statement ) + 1, -1 );
		return strpos( $rest, "\n" ) === false && preg_match( self::CHECKED, $rest ) === 1;
	}

	/**
	 * The checker's configuration: one JSON object, its keys in CONFIG_KEYS and none repeated at
	 * any depth; the export on stdin, exactly PERMITTED, any other axiom a hard error.
	 */
	private static function configured( string $file ): bool {
		$text = is_file( $file ) && is_readable( $file ) ? file_get_contents( $file ) : false;
		if ( !is_string( $text ) || !self::keysOnce( $text ) ) {
			return false;
		}
		$c = json_decode( $text, true, 64 );
		if ( !is_array( $c ) || array_is_list( $c ) || array_diff( array_keys( $c ), self::CONFIG_KEYS ) !== []
			|| !is_array( $c['permitted_axioms'] ?? null )
		) {
			return false;
		}
		$axioms = $c['permitted_axioms'];
		if ( !array_is_list( $axioms ) || count( $axioms ) !== count( array_unique( $axioms, SORT_REGULAR ) ) ) {
			return false;
		}
		foreach ( $axioms as $a ) {
			if ( !is_string( $a ) ) {
				return false;
			}
		}
		sort( $axioms, SORT_STRING );
		return $axioms === self::PERMITTED && ( $c['use_stdin'] ?? null ) === true
			&& ( $c['unpermitted_axiom_hard_error'] ?? null ) === true;
	}

	/**
	 * True when no object in the JSON text repeats a key, the keys compared as decoded (an escape
	 * is the character it writes), so the decoder's last-one-wins never hides a value. A text that
	 * is not JSON is left to json_decode, which refuses it.
	 */
	private static function keysOnce( string $text ): bool {
		$stack = [];
		$n = strlen( $text );
		for ( $i = 0; $i < $n; $i++ ) {
			$ch = $text[$i];
			if ( $ch === '{' ) {
				$stack[] = [];
			} elseif ( $ch === '[' ) {
				$stack[] = null;
			} elseif ( $ch === '}' || $ch === ']' ) {
				array_pop( $stack );
			} elseif ( $ch === '"' ) {
				$j = $i + 1;
				while ( $j < $n && $text[$j] !== '"' ) {
					$j += $text[$j] === '\\' ? 2 : 1;
				}
				$raw = substr( $text, $i, $j - $i + 1 );
				$i = $j;
				$k = $j + 1;
				while ( $k < $n && strpos( " \t\r\n", $text[$k] ) !== false ) {
					$k++;
				}
				$top = array_key_last( $stack );
				if ( $k < $n && $text[$k] === ':' && $top !== null && is_array( $stack[$top] ) ) {
					$key = json_decode( $raw );
					if ( !is_string( $key ) || isset( $stack[$top][$key] ) ) {
						return false;
					}
					$stack[$top][$key] = true;
				}
			}
		}
		return true;
	}

	/**
	 * The SHA-256 digest of $bytes, the very bytes read (never the file again, which could have
	 * changed since): written to a private temporary file and digested there by the Calculator's
	 * own digestOf. '' when no temporary file can be made, which matches no configured digest.
	 */
	private static function digestOfBytes( string $bytes ): string {
		$f = tmpfile();
		if ( $f === false ) {
			return '';
		}
		$path = stream_get_meta_data( $f )['uri'] ?? '';
		$d = fwrite( $f, $bytes ) === strlen( $bytes ) && fflush( $f ) && is_string( $path ) ? Calculator::digestOf( $path ) : '';
		fclose( $f );
		return $d;
	}

	private static function refused( string $word ): array {
		return [ 'verdict' => self::REFUSED, 'word' => $word ];
	}

	/** @param mixed $v */
	private static function text( $v ): string {
		return is_string( $v ) ? $v : '';
	}
}
