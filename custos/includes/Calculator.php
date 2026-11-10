<?php
/**
 * Calculator: Custos's one way into the Calculator's binary, pcalc.
 *
 * `call($family, $function, $json)` starts `pcalc <family> <function>` with $json on stdin
 * (Main.lean, Principia/Calculator.lean: one JSON value in, one line of canonical JSON out,
 * exit 0; a refusal `{"detail","refused"}` with exit 1 for the request, 2 for the call).
 * Before the first start of the binary its residence is checked (ResidenceCheck, D10): the
 * binary and every folder above it up to /opt or /usr owned by root and writable by no other
 * user, else UnsafeResidence and the binary is never started. Then, before every start of the
 * binary, `pcalc version` included, its SHA-256 digest is checked against CustosBuild's: a
 * binary that differs is refused (DigestMismatch) and never started.
 * The residence and `pcalc version` are read once per Calculator object, so once per request
 * cycle: the wiki makes one object per request or per job (fromConfig), and the version must
 * equal CustosBuild's.
 *
 * Never inside a web request: the object refuses every
 * call unless PHP runs on the command line, which is where the job runner and maintenance
 * scripts run. The live route is BoxedRunner, MediaWiki's shell framework.
 */

namespace Custos;

use JsonException;
use MediaWiki\Config\Config;

final class Calculator {
	/** A family or function name: what pcalc's families table holds. */
	private const WORD = '/^[a-z][a-z0-9_]*$/';
	/** The PHP SAPIs that are not a web request. */
	private const COMMAND_LINE = [ 'cli', 'phpdbg' ];

	private string $binary;
	private string $digest;
	private string $expectedVersion;
	private ShellRunner $runner;
	private string $sapi;
	private Residence $residence;
	private bool $resides = false;
	private ?string $version = null;
	/** Starts of the binary by this object, `pcalc version` included (the harness counts them). */
	public int $starts = 0;

	/**
	 * @param string $binary the binary's absolute path (CustosCalculator)
	 * @param array $expected CustosBuild: ["version" => ..., "digest" => 64 hexadecimal digits]
	 * @param Residence|null $residence the residence check; null is the live ResidenceCheck
	 */
	public function __construct( string $binary, array $expected, ShellRunner $runner, string $sapi = PHP_SAPI,
		?Residence $residence = null
	) {
		$this->binary = $binary;
		$this->digest = is_string( $expected['digest'] ?? null ) ? $expected['digest'] : '';
		$this->expectedVersion = is_string( $expected['version'] ?? null ) ? $expected['version'] : '';
		$this->runner = $runner;
		$this->sapi = $sapi;
		$this->residence = $residence ?? new ResidenceCheck();
	}

	/**
	 * One object per request cycle, from the wiki's configuration, over the shell framework,
	 * with the live residence check unless a test supplies one.
	 */
	public static function fromConfig( Config $config, ?ShellRunner $runner = null, ?Residence $residence = null ): self {
		$expected = $config->get( 'CustosBuild' );
		return new self( (string)$config->get( 'CustosCalculator' ), is_array( $expected ) ? $expected : [],
			$runner ?? new BoxedRunner(), PHP_SAPI, $residence );
	}

	/**
	 * The answer to `pcalc <family> <function>` with $json on stdin:
	 * ["exit" => 0, "text" => the canonical JSON line, "value" => it decoded], or a refusal
	 * ["exit" => 1 or 2, "text" => the line, "refused" => the code, "detail" => the sentence].
	 *
	 * @throws UnsafeResidence a user other than root could change the binary; it was not started
	 * @throws DigestMismatch the binary is not the expected one; it was not started
	 * @throws CalculatorFault no call could be made, or the answer is outside the protocol
	 */
	public function call( string $family, string $function, string $json ): array {
		foreach ( [ $family, $function ] as $word ) {
			if ( !preg_match( self::WORD, $word ) ) {
				throw new CalculatorFault( "not a family or function name: \"$word\"", CalculatorFault::NOT_A_WORD );
			}
		}
		$this->version();
		[ $exit, $out, $err ] = $this->start( [ $family, $function ], $json );
		if ( !in_array( $exit, [ 0, 1, 2 ], true ) ) {
			// pcalc's stderr enters the message, which goes to the error channel only (Refusal::detail).
			throw new CalculatorFault( "pcalc $family $function ended with exit code $exit: " . self::firstLine( $err ),
				CalculatorFault::EXIT_CODE, $family, $function );
		}
		$text = self::oneLine( $out, "pcalc $family $function", $family, $function );
		$value = self::decode( $text, "pcalc $family $function", $family, $function );
		if ( $exit === 0 ) {
			return [ 'exit' => 0, 'text' => $text, 'value' => $value ];
		}
		if ( !is_array( $value ) || !is_string( $value['refused'] ?? null ) || !is_string( $value['detail'] ?? null ) ) {
			throw new CalculatorFault( "pcalc $family $function ended with exit code $exit without a refusal",
				CalculatorFault::NO_REFUSAL, $family, $function );
		}
		return [ 'exit' => $exit, 'text' => $text, 'refused' => $value['refused'], 'detail' => $value['detail'] ];
	}

	/**
	 * What `pcalc version` prints, read at this object's first use and kept; it must equal
	 * CustosBuild's version.
	 */
	public function version(): string {
		if ( $this->version === null ) {
			[ $exit, $out, $err ] = $this->start( [ 'version' ], '' );
			if ( $exit !== 0 ) {
				throw new CalculatorFault( "pcalc version ended with exit code $exit: " . self::firstLine( $err ),
					CalculatorFault::EXIT_CODE, 'version' );
			}
			$version = self::oneLine( $out, 'pcalc version', 'version' );
			if ( $version !== $this->expectedVersion ) {
				throw new CalculatorFault( "pcalc version prints \"$version\", not the expected \"{$this->expectedVersion}\"",
					CalculatorFault::VERSION, 'version' );
			}
			$this->version = $version;
		}
		return $this->version;
	}

	/** The residence check (once per object), the digest check, then one start of the binary. */
	private function start( array $args, string $stdin ): array {
		if ( !in_array( $this->sapi, self::COMMAND_LINE, true ) ) {
			throw new CalculatorFault( 'the Calculator is never called inside a web request; '
				. 'the call belongs to a job or a maintenance script', CalculatorFault::WEB_REQUEST );
		}
		if ( $this->binary === '' ) {
			throw new CalculatorFault( 'no Calculator is configured: CustosCalculator is empty', CalculatorFault::NOT_CONFIGURED );
		}
		if ( !preg_match( '/^[0-9a-f]{64}$/', $this->digest ) ) {
			throw new CalculatorFault( 'CustosBuild names no digest (64 lowercase hexadecimal digits), so no call is made',
				CalculatorFault::NO_DIGEST );
		}
		if ( !$this->resides ) {
			$this->residence->check( $this->binary );
			$this->resides = true;
		}
		$found = self::digestOf( $this->binary );
		if ( $found !== $this->digest ) {
			throw new DigestMismatch( $this->digest, $found );
		}
		$this->starts++;
		[ $exit, $out, $err ] = $this->runner->run( array_merge( [ $this->binary ], $args ), $stdin );
		return [ (int)$exit, (string)$out, (string)$err ];
	}

	/** The SHA-256 digest of a file, lowercase hexadecimal; "" when it cannot be read. */
	public static function digestOf( string $path ): string {
		if ( !is_file( $path ) || !is_readable( $path ) ) {
			return '';
		}
		$d = hash_file( 'sha256', $path );
		return is_string( $d ) ? $d : '';
	}

	/** The single line pcalc wrote, without its line feed. */
	private static function oneLine( string $out, string $what, string $family, string $function = '' ): string {
		if ( $out === '' || substr( $out, -1 ) !== "\n" || strpos( substr( $out, 0, -1 ), "\n" ) !== false ) {
			throw new CalculatorFault( "$what did not write one line", CalculatorFault::NOT_ONE_LINE, $family, $function );
		}
		return substr( $out, 0, -1 );
	}

	/** @return mixed */
	private static function decode( string $text, string $what, string $family, string $function ) {
		try {
			return json_decode( $text, true, 512, JSON_BIGINT_AS_STRING | JSON_THROW_ON_ERROR );
		} catch ( JsonException $e ) {
			throw new CalculatorFault( "$what wrote a line that is not JSON", CalculatorFault::NOT_JSON, $family, $function );
		}
	}

	private static function firstLine( string $s ): string {
		$line = trim( strtok( $s, "\n" ) ?: '' );
		return $line === '' ? '(nothing on stderr)' : substr( $line, 0, 300 );
	}
}
