<?php
/**
 * FileTicketStore: the TicketStore on disk, for the harness. One JSON file per ticket under a
 * root folder, a counter file for the ids. No MediaWiki class is used; the contract is
 * DbTicketStore's. The harness alone reads these files; Custos's PHP never parses a request.
 */

namespace Custos\Tests;

use Custos\TicketStore;

final class FileTicketStore implements TicketStore {
	private string $root;

	public function __construct( string $root ) {
		$this->root = rtrim( $root, '/' );
		if ( !is_dir( $this->root ) ) {
			mkdir( $this->root, 0777, true );
		}
	}

	public function create( string $op, string $account, string $prefix, string $request ): int {
		$counter = $this->root . '/next';
		$id = is_file( $counter ) ? (int)file_get_contents( $counter ) : 1;
		file_put_contents( $counter, (string)( $id + 1 ) );
		$this->write( [ 'id' => $id, 'op' => $op, 'account' => $account, 'prefix' => $prefix, 'request' => $request,
			'state' => self::QUEUED, 'answer' => null, 'created' => gmdate( 'YmdHis' ), 'done' => null ] );
		return $id;
	}

	public function get( int $id ): ?array {
		$p = $this->path( $id );
		return is_file( $p ) ? json_decode( (string)file_get_contents( $p ), true ) : null;
	}

	public function answer( int $id, string $answer ): bool {
		$row = $this->get( $id );
		if ( $row === null || $row['state'] === self::DONE ) {
			return false;
		}
		$row['state'] = self::DONE;
		$row['answer'] = $answer;
		$row['done'] = gmdate( 'YmdHis' );
		$this->write( $row );
		return true;
	}

	public function claimNext(): ?array {
		$ids = [];
		foreach ( glob( $this->root . '/t*.json' ) ?: [] as $f ) {
			$ids[] = (int)substr( basename( $f, '.json' ), 1 );
		}
		sort( $ids );
		foreach ( $ids as $id ) {
			$row = $this->get( $id );
			if ( $row !== null && $row['state'] === self::QUEUED ) {
				$row['state'] = self::IN_WORK;
				$this->write( $row );
				return $row;
			}
		}
		return null;
	}

	public function claim( int $id ): ?array {
		$row = $this->get( $id );
		if ( $row === null || $row['state'] !== self::QUEUED ) {
			return null;
		}
		$row['state'] = self::IN_WORK;
		$this->write( $row );
		return $row;
	}

	public function inWork(): array {
		$out = [];
		foreach ( glob( $this->root . '/t*.json' ) ?: [] as $f ) {
			$row = $this->get( (int)substr( basename( $f, '.json' ), 1 ) );
			if ( $row !== null && $row['state'] === self::IN_WORK ) {
				$out[$row['id']] = [ 'id' => $row['id'], 'op' => $row['op'], 'account' => $row['account'] ];
			}
		}
		ksort( $out );
		return array_values( $out );
	}

	public function count( string $state ): int {
		$n = 0;
		foreach ( glob( $this->root . '/t*.json' ) ?: [] as $f ) {
			$row = $this->get( (int)substr( basename( $f, '.json' ), 1 ) );
			if ( $row !== null && $row['state'] === $state ) {
				$n++;
			}
		}
		return $n;
	}

	private function path( int $id ): string {
		return $this->root . "/t$id.json";
	}

	private function write( array $row ): void {
		file_put_contents( $this->path( $row['id'] ), json_encode( $row, JSON_UNESCAPED_SLASHES | JSON_THROW_ON_ERROR ) );
	}
}
