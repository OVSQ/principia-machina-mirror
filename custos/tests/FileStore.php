<?php
/**
 * FileStore: the PageStore on disk, for the harness. One file per page title under a root
 * folder, and a revision log per page so a test can count saves (one write per page per
 * landing) and see whose revision each is. No MediaWiki class is used; the contract is
 * MwStore's.
 */

namespace Custos\Tests;

use Custos\PageStore;

final class FileStore implements PageStore {
	private string $root;
	/** @var array<string, list<array{actor:string, summary:string}>> */
	public array $revisions = [];

	public function __construct( string $root ) {
		$this->root = rtrim( $root, '/' );
		if ( !is_dir( $this->root ) ) {
			mkdir( $this->root, 0777, true );
		}
	}

	public function get( string $title ): ?string {
		$p = $this->path( $title );
		return is_file( $p ) ? (string)file_get_contents( $p ) : null;
	}

	public function exists( string $title ): bool {
		return is_file( $this->path( $title ) );
	}

	public function put( string $title, string $text, string $summary ): void {
		if ( $this->get( $title ) === $text ) {
			return;
		}
		$this->save( $title, $text, $summary, 'Custos' );
	}

	public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
		$current = $this->get( $title );
		if ( $current !== $expected ) {
			return false;
		}
		if ( $current === $text ) {
			return true;
		}
		$this->save( $title, $text, $summary, $actor );
		return true;
	}

	public function appendAs( string $title, string $line, string $summary, string $actor ): string {
		$current = $this->get( $title ) ?? '';
		$new = $current === '' ? $line : $current . "\n" . $line;
		$this->save( $title, $new, $summary, $actor );
		return $new;
	}

	/** Every title stored, sorted. */
	public function titles(): array {
		$out = [];
		foreach ( glob( $this->root . '/*.txt' ) ?: [] as $f ) {
			$out[] = rawurldecode( basename( $f, '.txt' ) );
		}
		sort( $out, SORT_STRING );
		return $out;
	}

	/** Overwrite a page as a hand edit would, with no revision logged (tamper tests). */
	public function tamper( string $title, string $text ): void {
		file_put_contents( $this->path( $title ), $text );
	}

	private function path( string $title ): string {
		return $this->root . '/' . rawurlencode( $title ) . '.txt';
	}

	private function save( string $title, string $text, string $summary, string $actor ): void {
		file_put_contents( $this->path( $title ), $text );
		$this->revisions[$title][] = [ 'actor' => $actor, 'summary' => $summary ];
	}
}
