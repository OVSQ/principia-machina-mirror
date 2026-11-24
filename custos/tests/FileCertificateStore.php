<?php
/**
 * FileCertificateStore: the CertificateStore on disk, for the harness: one JSON file of every
 * row, keyed by the agent account. The contract is DbCertificateStore's: put() replaces the
 * agent's row whole (under an flock of <file>.lock, so two writers never lose each other's row).
 * The refused-PROMPT marks are a second file, <file>.marks (custos_prompt_mark's rows, keyed by the
 * agent: state, marked, cleared), so the certificates' file is unchanged by a mark; put() writes
 * the certificate and then clears the agent's standing mark, under the same lock, so a certificate
 * write that fails leaves the mark standing (DbCertificateStore's atomic section); a write that fails
 * throws, and no row of either file is deleted.
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
			self::write( $this->file, $all );
			$marks = $this->marks();
			if ( ( $marks[$r['agent']]['state'] ?? null ) === self::MARK_STANDING ) {
				$marks[$r['agent']]['state'] = self::MARK_CLEARED;
				$marks[$r['agent']]['cleared'] = time();
				self::write( $this->file . '.marks', $marks );
			}
		} finally {
			flock( $g, LOCK_UN );
			fclose( $g );
		}
	}

	public function promptMarked( string $agent ): bool {
		return ( $this->marks()[$agent]['state'] ?? null ) === self::MARK_STANDING;
	}

	public function markPrompt( string $agent, int $at ): void {
		$g = fopen( $this->file . '.lock', 'c' );
		flock( $g, LOCK_EX );
		try {
			$marks = $this->marks();
			if ( ( $marks[$agent]['state'] ?? null ) !== self::MARK_STANDING ) {
				$marks[$agent] = [ 'state' => self::MARK_STANDING, 'marked' => $at, 'cleared' => 0 ];
				self::write( $this->file . '.marks', $marks );
			}
		} finally {
			flock( $g, LOCK_UN );
			fclose( $g );
		}
	}

	/** The marks' rows, keyed by the agent (the test reads them). */
	public function marks(): array {
		$f = $this->file . '.marks';
		return is_file( $f ) ? (array)json_decode( (string)file_get_contents( $f ), true ) : [];
	}

	private static function write( string $file, array $rows ): void {
		if ( @file_put_contents( $file . '.tmp', json_encode( $rows, JSON_THROW_ON_ERROR ) ) === false
			|| !@rename( $file . '.tmp', $file ) ) {
			throw new \RuntimeException( 'the store\'s file ' . basename( $file ) . ' was not written' );
		}
	}

	private function all(): array {
		return is_file( $this->file ) ? (array)json_decode( (string)file_get_contents( $this->file ), true ) : [];
	}
}
