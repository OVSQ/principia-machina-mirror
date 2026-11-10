<?php
/**
 * PageStore: the seam between Custos's logic and the wiki's pages. MwStore is the live
 * store over MediaWiki's services; tests/FileStore.php keeps the same contract on disk so
 * the harness runs without MediaWiki. Written anew for Custos, after the
 * shape of version 1's seam.
 */

namespace Custos;

interface PageStore {
	/** The main slot's text of $title, or null when the page does not exist. */
	public function get( string $title ): ?string;

	public function exists( string $title ): bool;

	/**
	 * Create or replace $title with $text as the system user Custos's revision. Nothing is
	 * written when the page already holds $text (one write per page per landing).
	 */
	public function put( string $title, string $text, string $summary ): void;

	/**
	 * Compare-and-set: write $text only while the page's current text equals $expected
	 * (null: the page must not exist). True when written or already equal to $text; false
	 * when the base did not match, an edit conflict, and nothing is written. The revision
	 * is $actor's own.
	 */
	public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool;

	/** Append $line, after a line feed when the page is not empty, as $actor's own revision; the new full text. */
	public function appendAs( string $title, string $line, string $summary, string $actor ): string;
}
