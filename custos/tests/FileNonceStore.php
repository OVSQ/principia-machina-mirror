<?php
/**
 * FileNonceStore: the NonceStore on disk, for the harness: one JSON file of every outstanding nonce,
 * each put and take under an flock of <file>.lock, so of two takes of one nonce, by two objects or
 * two processes, one gets it. peek() reads the outstanding nonce without taking it (the harness's
 * own, to answer a challenge as an agent would).
 */

namespace Custos\Tests;

use Custos\NonceStore;

final class FileNonceStore implements NonceStore {
	public function __construct( private string $file ) {
	}

	public function put( string $account, string $prefix, string $nonce, int $issued ): void {
		$this->locked( static function ( array $all ) use ( $account, $prefix, $nonce, $issued ): array {
			$all[$prefix . "\n" . $account] = [ $nonce, $issued ];
			return [ $all, null ];
		} );
	}

	public function take( string $account, string $prefix ): ?string {
		return $this->locked( static function ( array $all ) use ( $account, $prefix ): array {
			$k = $prefix . "\n" . $account;
			$v = $all[$k][0] ?? null;
			unset( $all[$k] );
			return [ $all, $v ];
		} );
	}

	public function peek( string $account, string $prefix ): ?string {
		$all = is_file( $this->file ) ? json_decode( (string)file_get_contents( $this->file ), true ) : [];
		return is_array( $all ) ? ( $all[$prefix . "\n" . $account][0] ?? null ) : null;
	}

	/** Write the outstanding nonce as given, in any form (the harness's tamper). */
	public function tamper( string $account, string $prefix, string $nonce ): void {
		$this->put( $account, $prefix, $nonce, 0 );
	}

	private function locked( callable $fn ): mixed {
		$g = fopen( $this->file . '.lock', 'c' );
		flock( $g, LOCK_EX );
		$all = is_file( $this->file ) ? json_decode( (string)file_get_contents( $this->file ), true ) : [];
		[ $all, $out ] = $fn( is_array( $all ) ? $all : [] );
		file_put_contents( $this->file . '.tmp', json_encode( $all, JSON_THROW_ON_ERROR ) );
		rename( $this->file . '.tmp', $this->file );
		flock( $g, LOCK_UN );
		fclose( $g );
		return $out;
	}
}
