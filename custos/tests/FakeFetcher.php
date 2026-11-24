<?php
/**
 * FakeFetcher: the Fetcher the harness gives a job. It serves canned text by address and makes no
 * request. The declared guards that need no network still apply to it (the address's form and host,
 * the size, the schema, and the pacing and caps when a FetchGuard is given), so a job's test meets the
 * refusals the live class gives. An address with no canned text is a TRANSPORT fault; a canned
 * FetchFault is thrown as it is (a test's way to serve a failing source).
 */

namespace Custos\Tests;

use Custos\Fetcher;
use Custos\FetchFault;
use Custos\FetchGuard;

final class FakeFetcher implements Fetcher {
	/** @var array<int,array{0:string,1:string}> every call, [ source, url ] */
	public array $calls = [];

	/** @param array<string,string|FetchFault> $canned address => body */
	public function __construct( private array $canned, private ?FetchGuard $guard = null ) {
	}

	public function fetch( string $source, string $url, array $declared ): string {
		$this->calls[] = [ $source, $url ];
		$hosts = is_array( $declared['hosts'] ?? null ) ? $declared['hosts'] : [];
		FetchGuard::checkUrl( $url, $hosts, $source );
		$this->guard?->admit( $source, is_int( $declared['pacing'] ?? null ) ? $declared['pacing'] : 0 );
		try {
			$r = $this->canned[$url] ?? null;
			if ( $r instanceof FetchFault ) {
				throw new FetchFault( $r->word, $source );
			}
			if ( !is_string( $r ) ) {
				throw new FetchFault( FetchFault::TRANSPORT, $source );
			}
			$limit = is_int( $declared['max_bytes'] ?? null ) ? $declared['max_bytes'] : FetchGuard::MAX_BYTES;
			FetchGuard::checkSize( strlen( $r ), $limit, $source );
			FetchGuard::checkSchema( $r, is_callable( $declared['schema'] ?? null ) ? $declared['schema'] : null, $source );
			return $r;
		} finally {
			$this->guard?->done( $source );
		}
	}
}
