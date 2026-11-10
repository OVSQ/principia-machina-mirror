<?php
/**
 * FileJobRunStore: the JobRunStore on disk, for the harness. One JSON file per run under a root
 * folder, a counter file for the ids. No MediaWiki class is used; the contract is DbJobRunStore's.
 */

namespace Custos\Tests;

use Custos\JobRunStore;

final class FileJobRunStore implements JobRunStore {
	private string $root;

	public function __construct( string $root ) {
		$this->root = rtrim( $root, '/' );
		if ( !is_dir( $this->root ) ) {
			mkdir( $this->root, 0777, true );
		}
	}

	public function start( string $job, string $started ): int {
		$counter = $this->root . '/next';
		$id = is_file( $counter ) ? (int)file_get_contents( $counter ) : 1;
		file_put_contents( $counter, (string)( $id + 1 ) );
		$this->write( [ 'id' => $id, 'job' => $job, 'started' => $started, 'done' => null, 'outcome' => null,
			'detail' => '', 'counts' => '{}' ] );
		return $id;
	}

	public function finish( int $id, string $outcome, string $detail, string $counts, string $done ): bool {
		$row = $this->get( $id );
		if ( $row === null || $row['done'] !== null ) {
			return false;
		}
		$row['done'] = $done;
		$row['outcome'] = $outcome;
		$row['detail'] = $detail;
		$row['counts'] = $counts;
		$this->write( $row );
		return true;
	}

	public function get( int $id ): ?array {
		$p = $this->path( $id );
		return is_file( $p ) ? json_decode( (string)file_get_contents( $p ), true ) : null;
	}

	public function last( string $job ): ?array {
		$best = null;
		foreach ( glob( $this->root . '/r*.json' ) ?: [] as $f ) {
			$row = json_decode( (string)file_get_contents( $f ), true );
			if ( is_array( $row ) && $row['job'] === $job && ( $best === null || $row['id'] > $best['id'] ) ) {
				$best = $row;
			}
		}
		return $best;
	}

	private function write( array $row ): void {
		file_put_contents( $this->path( $row['id'] ), json_encode( $row, JSON_THROW_ON_ERROR ) );
	}

	private function path( int $id ): string {
		return $this->root . '/r' . $id . '.json';
	}
}
