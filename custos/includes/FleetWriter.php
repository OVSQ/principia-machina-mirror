<?php
/**
 * FleetWriter: the writer of the pages that have no UWC badge, the top performer pages
 * (design pma_custos_jobs, "Writes, in order", item 5). The proven PageWriter needs a UWC's
 * INDEX AND BADGE page as its commit marker; these pages have none, so the page `D/Top
 * performers` is the marker here:
 *
 *   publish()    the snapshot `D/Top performers/<YYYY-MM>` first, the page `D/Top performers` last
 *   stateOnly()  the page alone (a state change writes no snapshot)
 *
 * Both are compare-and-set on every page: publish() against the text it reads first, stateOnly() against the page the caller passes (the one its text was built from). Before the first save every
 * base is read again; one that moved refuses the whole write, BASE MOVED, nothing saved. A save
 * that fails after the first (an edit between the check and the save) refuses the rest and the page
 * is not written, so a reader sees the prior page beside at most a new snapshot, never the new page
 * beside no snapshot. A month's snapshot is never rewritten with other text: SNAPSHOT EXISTS,
 * nothing saved (a retry after a refusal that left the snapshot writes the same text and passes).
 * The titles are PageTitles::topPerformers' alone; no other title is reachable. PHP reads no field
 * of a text: PageTexts writes them from the Calculator's answer.
 */

namespace Custos;

final class FleetWriter {
	/** The summary of every save. */
	public const SUMMARY = 'Custos: top performers of %s';

	public function __construct(
		private PageStore $store,
		private PageTitles $titles,
		private string $actor = MwStore::SYSTEM_USER
	) {
	}

	/**
	 * Write the month's snapshot, then the page. Answers the titles saved, in order.
	 *
	 * @throws PageFault "BASE MOVED" or "SNAPSHOT EXISTS"; nothing is saved at the first
	 */
	public function publish( string $month, string $snapshotText, string $pageText ): array {
		$snapshot = $this->titles->topPerformers( $month );
		return $this->commit( $month, [ $snapshot => $snapshotText, $this->titles->topPerformers() => $pageText ], $snapshot );
	}

	/**
	 * Write the page alone (a state change: no snapshot). $expectedPage is the page the caller read
	 * and built $pageText from (page()); it is the compare base, so an edit or a publication after
	 * that read refuses the write. The page's month block must be $month.
	 *
	 * @throws PageFault "BASE MOVED" or "MONTH MISMATCH"; nothing is saved
	 */
	public function stateOnly( string $month, string $pageText, string $expectedPage ): array {
		$page = $this->titles->topPerformers();
		$this->titles->topPerformers( $month );
		if ( Blocks::one( $expectedPage, PageTexts::MONTH ) !== $month ) {
			throw new PageFault( "MONTH MISMATCH: the page \"$page\" is not the month $month's; nothing saved" );
		}
		return $this->commit( $month, [ $page => $pageText ], null, [ $page => $expectedPage ] );
	}

	/** The page's text as stored now (null: none), for the caller's prior state. */
	public function page(): ?string {
		return $this->store->get( $this->titles->topPerformers() );
	}

	/**
	 * @param array<string,string> $texts in save order, the page last
	 * @param array<string,string> $given bases the caller read earlier; a title not given is read here
	 */
	private function commit( string $month, array $texts, ?string $snapshot, array $given = [] ): array {
		$base = [];
		foreach ( $texts as $title => $text ) {
			$base[$title] = array_key_exists( $title, $given ) ? $given[$title] : $this->store->get( $title );
		}
		if ( $snapshot !== null && $base[$snapshot] !== null && $base[$snapshot] !== $texts[$snapshot] ) {
			throw new PageFault( "SNAPSHOT EXISTS: the snapshot \"$snapshot\" is not rewritten with other text; nothing saved" );
		}
		foreach ( $texts as $title => $text ) {
			if ( $this->store->get( $title ) !== $base[$title] ) {
				throw new PageFault( "BASE MOVED: the page \"$title\" changed since it was read; nothing saved" );
			}
		}
		$summary = sprintf( self::SUMMARY, $month );
		$saved = [];
		foreach ( $texts as $title => $text ) {
			if ( !$this->store->casPut( $title, $base[$title], $text, $summary, $this->actor ) ) {
				throw new PageFault( "BASE MOVED: the page \"$title\" changed while it was saved; " . count( $saved ) . ' saved, the page not written' );
			}
			$saved[] = $title;
		}
		return $saved;
	}
}
