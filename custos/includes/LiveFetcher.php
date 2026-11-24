<?php
/**
 * LiveFetcher: the Fetcher that reaches a server. HTTPS only, the guards of FetchGuard applied
 * before each request (scheme, declared host, resolved addresses, pacing, caps) and after it
 * (the connected address against the pinned one, the redirect, the size, the schema).
 *
 * The request leaves through a transport, a callable, so that a test serves canned answers and no
 * request leaves the machine; the default is curl, which pins the connection to the address the
 * guards chose (CURLOPT_RESOLVE), verifies the certificate and the host name, follows no redirect
 * itself, and stops reading at the size limit. (MediaWiki's HTTP request factory, the design's
 * first choice, cannot pin the connection to a resolved address; that is why the transport is
 * curl's, and the guards are Custos's own in front of it.)
 *
 * The contact values ($contact, the CustosRegistryContact entries, one per source name) are sent in
 * the request where the declaration says (the agent string, or one query parameter) and are never
 * written anywhere: no fault message carries one (a fault's text is FetchFault's fixed sentence),
 * the transport's own error text is dropped, no frame of a fault's trace holds one as an argument,
 * and the object shows none to var_dump or print_r.
 */

namespace Custos;

use Closure;
use InvalidArgumentException;
use Throwable;

final class LiveFetcher implements Fetcher {
	public const AGENT = 'PrincipiaMachina-Custos';
	/** @var Closure(string):string the contact values behind a closure, which no dump of the object shows */
	private Closure $contact;
	/** @var string[] the source names that have a value */
	private array $named = [];
	/** @var callable */
	private $resolver;
	/** @var callable */
	private $transport;
	/** @var callable */
	private $clock;

	/**
	 * @param array<string,string> $contact source name => contact value
	 * @param callable|null $resolver fn(string $host): string[] the addresses (default: DNS)
	 * @param callable|null $clock fn(): float, seconds (default: microtime)
	 * @param callable|null $transport fn(string $url, string $host, string $ip, array $headers, float $timeout, int $maxBytes):
	 *   array{status:int, location:?string, body:string, ip:string} (default: curl); it throws FetchFault
	 *   (TIME, SIZE, CERTIFICATE, TRANSPORT) or anything else, which becomes TRANSPORT
	 */
	public function __construct(
		array $contact,
		private FetchGuard $guard,
		?callable $resolver = null,
		?callable $transport = null,
		?callable $clock = null,
	) {
		$this->clock = $clock ?? static fn (): float => microtime( true );
		$values = [];
		foreach ( $contact as $source => $value ) {
			if ( !is_string( $source ) || !is_string( $value ) || preg_match( '/[\x00-\x20\x7f]/', $value ) === 1 ) {
				throw new InvalidArgumentException( 'a contact value is a string with no space or control character' );
			}
			$values[$source] = $value;
		}
		$this->named = array_keys( $values );
		$this->contact = static fn ( string $source ): string => $values[$source] ?? '';
		$this->resolver = $resolver ?? self::dns( ... );
		$this->transport = $transport ?? self::curl( ... );
	}

	/** The object shows no contact value. */
	public function __debugInfo(): array {
		return [ 'contact' => array_fill_keys( $this->named, '[set]' ) ];
	}

	public function __serialize(): array {
		return [];
	}

	public function fetch( string $source, string $url, array $declared ): string {
		$hosts = is_array( $declared['hosts'] ?? null ) ? $declared['hosts'] : [];
		$timeout = $declared['timeout'] ?? 0;
		if ( !is_int( $timeout ) || $timeout < 1 ) {
			throw new FetchFault( FetchFault::TIME, $source );
		}
		$pacing = is_int( $declared['pacing'] ?? 0 ) ? (int)( $declared['pacing'] ?? 0 ) : 0;
		$limit = is_int( $declared['max_bytes'] ?? null ) ? min( $declared['max_bytes'], FetchGuard::MAX_BYTES ) : FetchGuard::MAX_BYTES;
		$schema = is_callable( $declared['schema'] ?? null ) ? $declared['schema'] : null;
		FetchGuard::checkUrl( $url, $hosts, $source );
		$this->guard->admit( $source, $pacing );
		$started = (float)( $this->clock )();
		try {
			for ( $hop = 0; ; $hop++ ) {
				$remaining = $timeout - ( (float)( $this->clock )() - $started );
				if ( $remaining <= 0 ) {
					throw new FetchFault( FetchFault::TIME, $source );
				}
				$host = FetchGuard::checkUrl( $url, $hosts, $source );
				$ip = FetchGuard::pick( $this->resolve( $host, $source ), $source );
				$remaining = $timeout - ( (float)( $this->clock )() - $started );
				if ( $remaining <= 0 ) {
					throw new FetchFault( FetchFault::TIME, $source );
				}
				$place = $declared['contact'] ?? null;
				$r = $this->send( fn (): array => $this->request( $source, $url, $place ), $host, $ip, $remaining, $limit, $source );
				if ( (float)( $this->clock )() - $started > $timeout ) {
					throw new FetchFault( FetchFault::TIME, $source );
				}
				FetchGuard::checkConnected( $ip, (string)$r['ip'], $source );
				$status = (int)$r['status'];
				if ( $status >= 300 && $status < 400 ) {
					$url = FetchGuard::redirect( $url, (string)( $r['location'] ?? '' ), $hop + 1, $hosts, $source );
					continue;
				}
				if ( $status !== 200 ) {
					throw new FetchFault( FetchFault::STATUS, $source );
				}
				$body = (string)$r['body'];
				FetchGuard::checkSize( strlen( $body ), $limit, $source );
				FetchGuard::checkSchema( $body, $schema, $source );
				return $body;
			}
		} finally {
			$this->guard->done( $source );
		}
	}

	/** @return string[] */
	private function resolve( string $host, string $source ): array {
		try {
			$ips = ( $this->resolver )( $host );
		} catch ( Throwable ) {
			throw new FetchFault( FetchFault::TRANSPORT, $source );
		}
		return is_array( $ips ) ? $ips : [];
	}

	/**
	 * One request through the transport. The URL and headers, which may carry the contact value, come
	 * from $request, a closure, so that no frame of a fault's trace holds them as an argument (a
	 * trace shows a closure as an object); the transport's own fault is dropped and a new one with
	 * the fixed sentence raised, so its frames are not carried either.
	 *
	 * @param Closure():array{0:string,1:string[]} $request
	 */
	private function send( Closure $request, string $host, string $ip, float $timeout, int $limit, string $source ): array {
		try {
			[ $url, $headers ] = $request();
			$r = ( $this->transport )( $url, $host, $ip, $headers, $timeout, $limit );
		} catch ( FetchFault $e ) {
			throw new FetchFault( $e->word, $source );
		} catch ( Throwable ) {
			throw new FetchFault( FetchFault::TRANSPORT, $source );
		}
		if ( !is_array( $r ) || !isset( $r['status'], $r['ip'], $r['body'] ) ) {
			throw new FetchFault( FetchFault::TRANSPORT, $source );
		}
		return $r;
	}

	/**
	 * The request's URL and headers with the source's contact value put where the declaration says;
	 * none is sent for a source with no value or no declared place.
	 *
	 * @return array{0:string,1:string[]}
	 */
	private function request( string $source, string $url, mixed $place ): array {
		$agent = self::AGENT;
		$value = ( $this->contact )( $source );
		if ( $value !== '' && is_array( $place ) ) {
			if ( ( $place['in'] ?? '' ) === 'agent' ) {
				$agent .= ' (mailto:' . $value . ')';
			} elseif ( ( $place['in'] ?? '' ) === 'query' && is_string( $place['param'] ?? null ) && preg_match( '/^[A-Za-z0-9_.-]+$/', $place['param'] ) === 1 ) {
				$url .= ( str_contains( $url, '?' ) ? '&' : '?' ) . $place['param'] . '=' . rawurlencode( $value );
			}
		}
		return [ $url, [ 'User-Agent: ' . $agent, 'Accept: */*' ] ];
	}

	/**
	 * The addresses of $host, A and AAAA. dns_get_record takes no time limit of its own: the system
	 * resolver's (resolv.conf "timeout" and "attempts") bounds it, the fetch counts the lookup
	 * against the declared time and sends no request once that is spent, and the job's own run
	 * time (BIBLIO LOOKUP TIME) bounds the whole run.
	 *
	 * @return string[]
	 */
	private static function dns( string $host ): array {
		$ips = [];
		foreach ( dns_get_record( $host, DNS_A | DNS_AAAA ) ?: [] as $rec ) {
			$ips[] = $rec['ip'] ?? $rec['ipv6'] ?? null;
		}
		return array_values( array_filter( $ips, 'is_string' ) );
	}

	/**
	 * The curl options of one request, a pure function a test reads without a handle or a network.
	 * curl is given the URL rebuilt from the parts FetchGuard::checkUrl approved (scheme, host, path,
	 * query; no port, user information or fragment), never the raw text, so curl and parse_url
	 * cannot read it differently; the connection is pinned to the checked address twice
	 * (CURLOPT_RESOLVE and CURLOPT_CONNECT_TO); the proxy is off (CURLOPT_PROXY '' and
	 * CURLOPT_NOPROXY '*'), so a proxy named in the environment cannot carry the request past the
	 * pin. https is the only protocol: CURLOPT_PROTOCOLS_STR where PHP and curl have it (PHP 8.3,
	 * curl 7.85), else the bit mask CURLPROTO_HTTPS.
	 *
	 * @return array<int,mixed>
	 */
	public static function curlOptions( string $url, string $host, string $ip, array $headers, float $timeout ): array {
		$checked = FetchGuard::checkUrl( $url, [ $host ] );
		$p = parse_url( $url );
		$path = (string)( $p['path'] ?? '' );
		$target = 'https://' . $checked . ( $path === '' ? '/' : $path ) . ( isset( $p['query'] ) ? '?' . $p['query'] : '' );
		$ms = max( 1, (int)( $timeout * 1000 ) );
		$to = str_contains( $ip, ':' ) ? "[$ip]" : $ip;
		$protocols = defined( 'CURLOPT_PROTOCOLS_STR' )
			? [ CURLOPT_PROTOCOLS_STR => 'https', CURLOPT_REDIR_PROTOCOLS_STR => 'https' ]
			: [ CURLOPT_PROTOCOLS => CURLPROTO_HTTPS, CURLOPT_REDIR_PROTOCOLS => CURLPROTO_HTTPS ];
		return [
			CURLOPT_URL => $target,
			CURLOPT_PROXY => '',
			CURLOPT_NOPROXY => '*',
			CURLOPT_FOLLOWLOCATION => false,
			CURLOPT_SSL_VERIFYPEER => true,
			CURLOPT_SSL_VERIFYHOST => 2,
			CURLOPT_RESOLVE => [ "$checked:443:$ip" ],
			CURLOPT_CONNECT_TO => [ "$checked:443:$to:443" ],
			CURLOPT_HTTPHEADER => $headers,
			CURLOPT_TIMEOUT_MS => $ms,
			CURLOPT_CONNECTTIMEOUT_MS => $ms,
		] + $protocols;
	}

	/** The default transport. Never called by a test. */
	private static function curl( string $url, string $host, string $ip, array $headers, float $timeout, int $maxBytes ): array {
		if ( !function_exists( 'curl_init' ) ) {
			throw new FetchFault( FetchFault::TRANSPORT );
		}
		$ch = curl_init();
		$body = '';
		$location = null;
		$over = false;
		curl_setopt_array( $ch, self::curlOptions( $url, $host, $ip, $headers, $timeout ) + [
			CURLOPT_HEADERFUNCTION => static function ( $c, string $line ) use ( &$location ): int {
				if ( stripos( $line, 'location:' ) === 0 ) {
					$location = trim( substr( $line, 9 ) );
				}
				return strlen( $line );
			},
			CURLOPT_WRITEFUNCTION => static function ( $c, string $chunk ) use ( &$body, &$over, $maxBytes ): int {
				if ( strlen( $body ) + strlen( $chunk ) > $maxBytes ) {
					$over = true;
					return 0;
				}
				$body .= $chunk;
				return strlen( $chunk );
			},
		] );
		$ok = curl_exec( $ch );
		$errno = curl_errno( $ch );
		$status = (int)curl_getinfo( $ch, CURLINFO_RESPONSE_CODE );
		$connected = (string)curl_getinfo( $ch, CURLINFO_PRIMARY_IP );
		curl_close( $ch );
		if ( $over ) {
			throw new FetchFault( FetchFault::SIZE );
		}
		if ( $ok === false ) {
			throw new FetchFault( match ( true ) {
				$errno === 28 => FetchFault::TIME,
				in_array( $errno, [ 35, 51, 58, 59, 60, 77, 82, 83, 90, 91 ], true ) => FetchFault::CERTIFICATE,
				default => FetchFault::TRANSPORT,
			} );
		}
		return [ 'status' => $status, 'location' => $location, 'body' => $body, 'ip' => $connected ];
	}
}
