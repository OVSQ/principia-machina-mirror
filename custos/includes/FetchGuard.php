<?php
/**
 * FetchGuard: each guard of the fetch layer (docs/design/pma_custos_jobs.md, "The fetch layer").
 * The checks are pure statics; pacing, the one-request-at-a-time rule and the run's caps are the
 * instance's, with its clock and its sleep given (a test gives a fake clock; nothing here reads
 * the environment).
 *
 * Address: ADDRESS for an address in a private, loopback, link-local, shared, documentation,
 * multicast or reserved range, IPv4 or IPv6, an IPv4 address carried inside an IPv6 one (mapped,
 * NAT64, 6to4) judged as that IPv4 address; the IPv4-compatible range ::/96, the local NAT64 range
 * 64:ff9b:1::/48, the old site-local fec0::/10 and the old 6to4 relay 192.88.99.0/24 refused whole;
 * an address that does not parse is refused.
 */

namespace Custos;

final class FetchGuard {
	public const MAX_BYTES = 20 * 1024 * 1024;
	public const MAX_HOPS = 3;
	public const MAX_MEMBER_BYTES = 50 * 1024 * 1024;
	public const MAX_ENTRIES = 256;
	/** Member names ending so are nested archives. */
	private const NESTED = '/\.(?:zip|gz|tgz|bz2|xz|7z|rar|tar|zst)$/i';
	private const BLOCKED = [
		'0.0.0.0/8', '10.0.0.0/8', '100.64.0.0/10', '127.0.0.0/8', '169.254.0.0/16', '172.16.0.0/12',
		'192.0.0.0/24', '192.0.2.0/24', '192.168.0.0/16', '198.18.0.0/15', '198.51.100.0/24',
		'192.88.99.0/24', '203.0.113.0/24', '224.0.0.0/4', '240.0.0.0/4',
		'::/96', '64:ff9b:1::/48', '::1/128', '100::/64', '2001::/32', '2001:db8::/32', 'fc00::/7', 'fe80::/10', 'fec0::/10', 'ff00::/8',
	];

	/** @var array<string,float> */
	private array $last = [];
	/** @var array<string,bool> */
	private array $busy = [];
	private ?float $started = null;
	private int $requests = 0;
	/** @var callable */
	private $clock;
	/** @var callable */
	private $sleep;

	/**
	 * @param callable $clock fn(): float, seconds
	 * @param callable $sleep fn(float $seconds): void
	 * @param int|null $runSeconds the whole run's lookup time (BIBLIO LOOKUP TIME), null: none
	 * @param int|null $runRequests the run's lookup count (BIBLIO LOOKUP CAP), null: none
	 */
	public function __construct( callable $clock, callable $sleep, ?int $runSeconds = null, ?int $runRequests = null ) {
		$this->clock = $clock;
		$this->sleep = $sleep;
		$this->runSeconds = $runSeconds;
		$this->runRequests = $runRequests;
	}

	private ?int $runSeconds;
	private ?int $runRequests;

	/** The host of an allowed address: HTTPS, no user information, port 443 or none, a declared host. */
	public static function checkUrl( string $url, array $hosts, string $source = '' ): string {
		if ( preg_match( '/[\x00-\x20\x7f\\\\]/', $url ) === 1 ) {
			throw new FetchFault( FetchFault::SCHEME, $source );
		}
		$p = parse_url( $url );
		if ( !is_array( $p ) || strtolower( (string)( $p['scheme'] ?? '' ) ) !== 'https'
			|| isset( $p['user'] ) || isset( $p['pass'] ) || ( isset( $p['port'] ) && $p['port'] !== 443 )
			|| !isset( $p['host'] ) || $p['host'] === '' ) {
			throw new FetchFault( FetchFault::SCHEME, $source );
		}
		$host = strtolower( $p['host'] );
		foreach ( $hosts as $h ) {
			if ( is_string( $h ) && strtolower( $h ) === $host ) {
				return $host;
			}
		}
		throw new FetchFault( FetchFault::HOST, $source );
	}

	/** True when $ip is a public address (see the class note). */
	public static function addressAllowed( string $ip ): bool {
		$bin = @inet_pton( $ip );
		if ( $bin === false ) {
			return false;
		}
		if ( strlen( $bin ) === 16 ) {
			$inner = null;
			if ( strncmp( $bin, str_repeat( "\0", 10 ) . "\xff\xff", 12 ) === 0 ) {
				$inner = substr( $bin, 12 );
			} elseif ( strncmp( $bin, "\x00\x64\xff\x9b" . str_repeat( "\0", 8 ), 12 ) === 0 ) {
				$inner = substr( $bin, 12 );
			} elseif ( strncmp( $bin, "\x20\x02", 2 ) === 0 ) {
				$inner = substr( $bin, 2, 4 );
			}
			if ( $inner !== null && !self::addressAllowed( (string)inet_ntop( $inner ) ) ) {
				return false;
			}
		}
		foreach ( self::BLOCKED as $range ) {
			[ $net, $bits ] = explode( '/', $range );
			$nb = (string)inet_pton( $net );
			if ( strlen( $nb ) === strlen( $bin ) && self::inRange( $bin, $nb, (int)$bits ) ) {
				return false;
			}
		}
		return true;
	}

	private static function inRange( string $bin, string $net, int $bits ): bool {
		$whole = intdiv( $bits, 8 );
		if ( substr( $bin, 0, $whole ) !== substr( $net, 0, $whole ) ) {
			return false;
		}
		$rest = $bits % 8;
		if ( $rest === 0 ) {
			return true;
		}
		$mask = ( 0xff << ( 8 - $rest ) ) & 0xff;
		return ( ord( $bin[$whole] ) & $mask ) === ( ord( $net[$whole] ) & $mask );
	}

	/** Every resolved address must be allowed; the first is the one the connection is pinned to. */
	public static function pick( array $ips, string $source = '' ): string {
		$ips = array_values( array_filter( $ips, 'is_string' ) );
		if ( $ips === [] ) {
			throw new FetchFault( FetchFault::TRANSPORT, $source );
		}
		foreach ( $ips as $ip ) {
			if ( !self::addressAllowed( $ip ) ) {
				throw new FetchFault( FetchFault::ADDRESS, $source );
			}
		}
		return $ips[0];
	}

	/** The connected address must be the pinned one. */
	public static function checkConnected( string $pinned, string $connected, string $source = '' ): void {
		$a = @inet_pton( $pinned );
		$b = @inet_pton( $connected );
		if ( $a === false || $b === false || $a !== $b || !self::addressAllowed( $connected ) ) {
			throw new FetchFault( FetchFault::ADDRESS, $source );
		}
	}

	/**
	 * The next URL of a redirect from $base: $location made absolute, then checkUrl's guards
	 * (declared host, HTTPS), at hop number $hop (1 for the first); a hop past MAX_HOPS is REDIRECT.
	 */
	public static function redirect( string $base, string $location, int $hop, array $hosts, string $source = '' ): string {
		if ( $hop > self::MAX_HOPS || $location === '' || preg_match( '/[\x00-\x20\x7f\\\\]/', $location ) === 1 ) {
			throw new FetchFault( FetchFault::REDIRECT, $source );
		}
		$b = parse_url( $base );
		if ( !is_array( $b ) || !isset( $b['scheme'], $b['host'] ) ) {
			throw new FetchFault( FetchFault::REDIRECT, $source );
		}
		if ( strncmp( $location, '//', 2 ) === 0 ) {
			$next = $b['scheme'] . ':' . $location;
		} elseif ( preg_match( '#^[A-Za-z][A-Za-z0-9+.-]*:#', $location ) === 1 ) {
			$next = $location;
		} elseif ( $location[0] === '/' ) {
			$next = $b['scheme'] . '://' . $b['host'] . ( isset( $b['port'] ) ? ':' . $b['port'] : '' ) . $location;
		} else {
			$dir = substr( (string)( $b['path'] ?? '/' ), 0, (int)strrpos( (string)( $b['path'] ?? '/' ), '/' ) + 1 );
			$next = $b['scheme'] . '://' . $b['host'] . ( isset( $b['port'] ) ? ':' . $b['port'] : '' ) . $dir . $location;
		}
		try {
			self::checkUrl( $next, $hosts, $source );
		} catch ( FetchFault $e ) {
			throw new FetchFault( FetchFault::REDIRECT, $source );
		}
		return $next;
	}

	/** SIZE when $bytes passes $limit (at most MAX_BYTES). */
	public static function checkSize( int $bytes, int $limit = self::MAX_BYTES, string $source = '' ): void {
		if ( $bytes > min( $limit, self::MAX_BYTES ) ) {
			throw new FetchFault( FetchFault::SIZE, $source );
		}
	}

	/**
	 * An archive's entries, [ { name, size } ... ] (size decompressed), against the declared members:
	 * at most MAX_ENTRIES entries, each at most MAX_MEMBER_BYTES, no nested archive, and only the
	 * declared members read; an entry outside the declared members is skipped, one that is
	 * declared and broke a limit refuses the archive. Returns the declared members found.
	 *
	 * The sizes are the archive's own declared ones and are trusted here: the extractor that reads a
	 * member must stop at MAX_MEMBER_BYTES of output whatever the entry declared (a member that
	 * inflates past its declared size is a fault there, ARCHIVE), so this check is the first limit,
	 * never the only one.
	 *
	 * @return string[]
	 */
	public static function archive( array $entries, array $members, string $source = '' ): array {
		if ( count( $entries ) > self::MAX_ENTRIES ) {
			throw new FetchFault( FetchFault::ARCHIVE, $source );
		}
		$found = [];
		foreach ( $entries as $e ) {
			$name = is_array( $e ) ? ( $e['name'] ?? null ) : null;
			$size = is_array( $e ) ? ( $e['size'] ?? null ) : null;
			if ( !is_string( $name ) || !is_int( $size ) || $size < 0 || preg_match( self::NESTED, $name ) === 1 ) {
				throw new FetchFault( FetchFault::ARCHIVE, $source );
			}
			if ( in_array( $name, $members, true ) ) {
				if ( $size > self::MAX_MEMBER_BYTES ) {
					throw new FetchFault( FetchFault::ARCHIVE, $source );
				}
				$found[] = $name;
			}
		}
		return $found;
	}

	/** SCHEMA when the declared check, if there is one, refuses the body (the payload is refused whole). */
	public static function checkSchema( string $body, ?callable $schema, string $source = '' ): void {
		if ( $schema !== null && $schema( $body ) !== true ) {
			throw new FetchFault( FetchFault::SCHEMA, $source );
		}
	}

	/** The download's SHA-256, 64 lowercase hexadecimal digits, for the run record's counts. */
	public static function digest( string $body ): string {
		return (string)openssl_digest( $body, 'sha256' );
	}

	/**
	 * Every message, with each contact value cut out, so that no output of a job carries one.
	 *
	 * @param string[] $contacts
	 */
	public static function scrub( string $text, array $contacts ): string {
		foreach ( $contacts as $c ) {
			if ( is_string( $c ) && $c !== '' ) {
				$text = str_replace( [ $c, rawurlencode( $c ), urlencode( $c ) ], '[contact]', $text );
			}
		}
		return $text;
	}

	/**
	 * Before a request to $source: CAP past the run's time or count, BUSY while a request to the
	 * source is in flight, then the wait that keeps $pacing seconds from the source's last call.
	 * Pair with done().
	 */
	public function admit( string $source, int $pacing = 0 ): void {
		$now = ( $this->clock )();
		$this->started ??= $now;
		if ( ( $this->runSeconds !== null && $now - $this->started >= $this->runSeconds )
			|| ( $this->runRequests !== null && $this->requests >= $this->runRequests ) ) {
			throw new FetchFault( FetchFault::CAP, $source );
		}
		if ( $this->busy[$source] ?? false ) {
			throw new FetchFault( FetchFault::BUSY, $source );
		}
		$this->busy[$source] = true;
		$this->requests++;
		if ( isset( $this->last[$source] ) && $pacing > 0 ) {
			$wait = $this->last[$source] + $pacing - $now;
			if ( $wait > 0 ) {
				( $this->sleep )( $wait );
			}
		}
	}

	/** After the request to $source, however it ended. */
	public function done( string $source ): void {
		$this->busy[$source] = false;
		$this->last[$source] = ( $this->clock )();
	}
}
