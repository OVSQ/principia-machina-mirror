<?php
/**
 * The tests' bootstrap: Custos's classes by the same rule extension.json gives MediaWiki
 * (AutoloadNamespaces: Custos\ to includes/, one class per file named after it), the tests'
 * own classes (Custos\Tests\ to tests/), and the harness's G class. Command line only.
 */

declare( strict_types=1 );

if ( PHP_SAPI !== 'cli' && PHP_SAPI !== 'phpdbg' ) {
	http_response_code( 404 );
	exit( 1 );
}

spl_autoload_register( static function ( string $class ): void {
	foreach ( [ 'Custos\\Tests\\' => __DIR__ . '/', 'Custos\\' => dirname( __DIR__ ) . '/includes/' ] as $prefix => $dir ) {
		if ( strncmp( $class, $prefix, strlen( $prefix ) ) === 0 ) {
			$file = $dir . str_replace( '\\', '/', substr( $class, strlen( $prefix ) ) ) . '.php';
			if ( is_file( $file ) ) {
				require_once $file;
			}
			return;
		}
	}
} );

/** The harness: assertions counted, a refusal expected, a skip with its reason, one result line. */
final class G {
	public static int $pass = 0;
	public static int $fail = 0;
	public static int $skip = 0;
	/** @var string[] */
	public static array $log = [];

	public static function ok( bool $c, string $what, string $detail = '' ): void {
		if ( $c ) {
			self::$pass++;
			self::$log[] = "PASS  $what";
		} else {
			self::$fail++;
			self::$log[] = "FAIL  $what" . ( $detail !== '' ? "\n      $detail" : '' );
		}
	}

	/**
	 * Run $fn; a pass when it throws a $class whose message contains $needle. Returns the
	 * exception caught, or null.
	 */
	public static function refuses( callable $fn, string $class, string $needle, string $what ): ?Throwable {
		try {
			$fn();
		} catch ( Throwable $e ) {
			$good = $e instanceof $class && strpos( $e->getMessage(), $needle ) !== false;
			self::ok( $good, $what, get_class( $e ) . ': ' . $e->getMessage() );
			return $e;
		}
		self::ok( false, $what, "expected $class containing \"$needle\"; nothing was refused" );
		return null;
	}

	/** A case that cannot run here: logged with its reason, counted apart, never as a pass. */
	public static function skip( string $what, string $reason ): void {
		self::$skip++;
		self::$log[] = "SKIP  $what\n      $reason";
	}

	/**
	 * Print the log, "<name>: <k> skipped" when a case was skipped, and "<name>: ALL PASS <n>/<n>"
	 * or "<name>: FAIL <p>/<n>" (skips counted in neither); the exit code.
	 */
	public static function report( string $name ): int {
		foreach ( self::$log as $line ) {
			echo $line, "\n";
		}
		if ( self::$skip > 0 ) {
			echo "$name: ", self::$skip, " skipped\n";
		}
		$n = self::$pass + self::$fail;
		echo "$name: ", self::$fail === 0 ? 'ALL PASS' : 'FAIL', ' ', self::$pass, '/', $n, "\n";
		return self::$fail === 0 ? 0 : 1;
	}
}
