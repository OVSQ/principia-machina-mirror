<?php
/**
 * FileCertificateStore: the CertificateStore on disk, for the harness: one JSON file of every
 * row, keyed by the agent account. The contract is DbCertificateStore's: put() replaces the
 * agent's row whole (under an flock of <file>.lock, so two writers never lose each other's row).
 */

namespace Custos\Tests;

use Custos\CertificateStore;

final class FileCertificateStore implements CertificateStore {
	public function __construct( private string $file ) {
	}

	public function get( string $agent ): ?array {
		$r = $this->all()[$agent] ?? null;
		return is_array( $r ) ? $r : null;
	}

	public function agentsOf( string $sponsor ): array {
		$agents = [];
		foreach ( $this->all() as $agent => $r ) {
			if ( ( $r['sponsor'] ?? null ) === $sponsor ) {
				$agents[] = (string)$agent;
			}
		}
		sort( $agents, SORT_STRING );
		return $agents;
	}

	public function put( array $row ): void {
		$g = fopen( $this->file . '.lock', 'c' );
		flock( $g, LOCK_EX );
		try {
			$all = $this->all();
			$r = [];
			foreach ( self::FIELDS as $f ) {
				$r[$f] = (string)$row[$f];
			}
			$all[$r['agent']] = $r;
			file_put_contents( $this->file . '.tmp', json_encode( $all, JSON_THROW_ON_ERROR ) );
			rename( $this->file . '.tmp', $this->file );
		} finally {
			flock( $g, LOCK_UN );
			fclose( $g );
		}
	}

	private function all(): array {
		return is_file( $this->file ) ? (array)json_decode( (string)file_get_contents( $this->file ), true ) : [];
	}
}
