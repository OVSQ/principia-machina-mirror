<?php
/**
 * PageWriter: one landing's page writes, batched (charter 8.3). begin() opens the landing and
 * reads the UWC's INDEX AND BADGE page; put() collects a page's new text, reading the page's
 * current text the first time the landing names it (read() does the same and answers it);
 * commit() saves each collected page once, through PageStore::casPut, against the text read in
 * this landing, the INDEX AND BADGE page last and only after every other save succeeded: the
 * badge is the landing's commit marker (v1's Recorder, the badge LAST).
 *
 * Before the first save every base is read again; one that moved refuses the whole landing with
 * BASE MOVED and nothing is saved. A save that fails after that (an edit between the check and
 * the save) refuses the rest of the landing, BASE MOVED, and the badge is not written, so the
 * UWC reads as the landing not made. PHP reads no field of a payload: the texts are carried
 * through as given (PageTexts writes them).
 *
 * The fence: put() takes only a title in MediaWiki's canonical form that classifies
 * (PageTitles::classify) as a page Custos writes under the landing's own UWC prefix (FENCED: the
 * DRAFT UWC page, a RESEARCH ASSEMBLY page, a register volume, the LOCK PAGE, the INDEX AND
 * BADGE page), or, where begin() names its class, a page beyond the UWC (BEYOND: the fleet's
 * index, the Declarer's root's chain heads and volumes). Any other title (another UWC's, a
 * governed title of no class, a class Custos does not write, an ordinary page) refuses the whole
 * landing before anything is saved, as BASE MOVED does: the landing is closed unsaved and the
 * refusal names the title and the class it read.
 */

namespace Custos;

final class PageWriter {
	/** The summary of every save of a landing: the block and the prefix. */
	public const SUMMARY = 'Custos: landing of block %s on %s';
	/** A work block's name, Ops's form. */
	private const BLOCK = '/\A[A-Za-z0-9][A-Za-z0-9_.:-]{0,63}\z/';
	/** The classes a landing writes under its own UWC prefix. */
	public const FENCED = [ PageClass::DRAFT_UWC, PageClass::RESEARCH_ASSEMBLY, PageClass::REGISTER_OPEN,
		PageClass::LOCK_PAGE, PageClass::INDEX_AND_BADGE ];
	/** The classes beyond the UWC an op may name at begin(): the fleet's index and the chain pages. */
	public const BEYOND = [ PageClass::INDEX_AND_BADGE, PageClass::CHAIN_HEAD, PageClass::DECLARATIONS_VOLUME,
		PageClass::BUILD_CHAIN_VOLUME ];
	/**
	 * The facts the fence classifies with: the writer does not judge a UWC's state (the landing
	 * reads it from the badge first), and a volume it writes is the open one.
	 */
	private const FACTS = [ 'retired' => false, 'open' => true ];

	private ?string $prefix = null;
	private ?string $block = null;
	private ?string $badge = null;
	/** @var string[] the classes beyond the UWC this landing may write (BEYOND) */
	private array $beyond = [];
	/** @var array<string, ?string> each title's text as read in this landing (null: no page) */
	private array $base = [];
	/** @var array<string, string> each collected title's new text, in the order first put */
	private array $pending = [];

	public function __construct(
		private PageStore $store,
		private PageTitles $titles,
		private string $actor = MwStore::SYSTEM_USER
	) {
	}

	/**
	 * Open the landing of $block on the UWC $prefix; any landing still open is dropped unsaved.
	 * $beyond: the classes beyond the UWC this landing writes, each one of BEYOND (none: the
	 * landing writes its UWC's pages alone).
	 *
	 * @throws PageFault a prefix the titles refuse, a block not in its form, a class not of BEYOND
	 */
	public function begin( string $prefix, string $block, array $beyond = [] ): void {
		if ( preg_match( self::BLOCK, $block ) !== 1 ) {
			throw new PageFault( 'not a work block\'s name: ' . PageTitles::show( $block ) );
		}
		foreach ( $beyond as $class ) {
			if ( !is_string( $class ) || !in_array( $class, self::BEYOND, true ) ) {
				throw new PageFault( 'not a class a landing writes beyond its UWC: ' . ( is_string( $class ) ? PageTitles::show( $class ) : gettype( $class ) ) );
			}
		}
		$badge = $this->titles->index( $prefix );
		$this->prefix = $prefix;
		$this->block = $block;
		$this->badge = $badge;
		$this->beyond = array_values( $beyond );
		$this->base = [];
		$this->pending = [];
		$this->read( $badge );
	}

	/**
	 * The text of $title as this landing read it (null: no page), read now the first time. The text
	 * read stands for the revision: casPut saves only while the page still holds it.
	 */
	public function read( string $title ): ?string {
		$this->open();
		if ( !array_key_exists( $title, $this->base ) ) {
			$this->base[$title] = $this->store->get( $title );
		}
		return $this->base[$title];
	}

	/**
	 * Collect $text for $title; a second put of the title in this landing replaces the first (one
	 * save per page). A title outside the fence refuses the landing whole, nothing saved.
	 *
	 * @throws PageFault "FENCE" (the landing closed unsaved)
	 */
	public function put( string $title, string $text ): void {
		$this->open();
		$this->fence( $title );
		$this->read( $title );
		$this->pending[$title] = $text;
	}

	/** The titles collected, in the order they will be saved (the badge last). */
	public function order(): array {
		$this->open();
		$out = array_values( array_filter( array_keys( $this->pending ), fn ( $t ) => $t !== $this->badge ) );
		if ( isset( $this->pending[$this->badge] ) ) {
			$out[] = $this->badge;
		}
		return $out;
	}

	/**
	 * Save the landing: each collected page once, the badge last. Answers the titles saved, in
	 * order. The landing is closed whatever the outcome.
	 *
	 * @throws PageFault "BASE MOVED" (a page changed since this landing read it), or a landing
	 *   without its badge
	 */
	public function commit(): array {
		$this->open();
		try {
			if ( !isset( $this->pending[$this->badge] ) ) {
				throw new PageFault( 'a landing writes its INDEX AND BADGE page, the commit marker; nothing saved' );
			}
			$order = $this->order();
			foreach ( $order as $t ) {
				if ( $this->store->get( $t ) !== $this->base[$t] ) {
					throw new PageFault( "BASE MOVED: the page \"$t\" changed since this landing read it; nothing saved" );
				}
			}
			$summary = sprintf( self::SUMMARY, $this->block, $this->prefix );
			$saved = [];
			foreach ( $order as $t ) {
				if ( !$this->store->casPut( $t, $this->base[$t], $this->pending[$t], $summary, $this->actor ) ) {
					throw new PageFault( "BASE MOVED: the page \"$t\" changed while this landing saved; "
						. count( $saved ) . ' saved, the badge not written' );
				}
				$saved[] = $t;
			}
			return $saved;
		} finally {
			$this->close();
		}
	}

	/** Whether $title lies inside this landing's fence; else the landing is closed and refused. */
	private function fence( string $title ): void {
		$ref = $this->titles->classify( $title, self::FACTS );
		$c = PageTitles::canon( $title );
		$canonical = $c !== null && $c[0] === null && $c[1] === $title;
		$inside = $canonical && $ref->class !== null && (
			( $ref->prefix !== null && $ref->prefix === $this->prefix && in_array( $ref->class, self::FENCED, true ) )
			|| ( $ref->prefix === null && in_array( $ref->class, $this->beyond, true ) ) );
		if ( $inside ) {
			return;
		}
		$read = $ref->class ?? ( $ref->governed ? 'a governed title of no class' : 'a page Custos does not govern' );
		if ( $ref->class !== null && !$canonical && $c !== null && $c[0] === null ) {
			$read .= ', not in canonical form';
		} elseif ( $ref->class !== null && $ref->prefix !== null && $ref->prefix !== $this->prefix ) {
			$read .= ' of the UWC ' . PageTitles::show( $ref->prefix );
		}
		$prefix = (string)$this->prefix;
		$this->close();
		throw new PageFault( 'FENCE: the landing on ' . $prefix . ' does not write the page ' . PageTitles::show( $title )
			. ' (read as ' . $read . '); nothing saved' );
	}

	private function close(): void {
		$this->prefix = $this->block = $this->badge = null;
		$this->beyond = [];
		$this->base = [];
		$this->pending = [];
	}

	private function open(): void {
		if ( $this->prefix === null ) {
			throw new PageFault( 'no landing is open (begin first)' );
		}
	}
}
