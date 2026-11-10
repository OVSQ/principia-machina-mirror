<?php
/**
 * PageTexts: the three page texts of the live path, in the block form (Blocks).
 *
 *   LOCK PAGE        one block pma-lock: {"block","expires_at","granted_at","holder"}, all null
 *                    when the lock is free
 *   REGISTER OPEN    one block pma-register: the records as the Calculator wrote them (its
 *                    canonical JSON), carried through whole; an append rewrites the block whole
 *   INDEX AND BADGE  the block pma-badge: {"calculator_digest","calculator_version","last_push",
 *                    "last_release","record_count","research_assembly"}; then pma-state, one word,
 *                    LIVE or RETIRED; then pma-open, the number of the open register volume; then,
 *                    where the UWC has one, pma-structure, the STRUCTURE TEST LINE (TPS 5.3.47):
 *                    "STRUCTURE TEST none" from the seed, else "STRUCTURE TEST <date> <result> WITH
 *                    <identifiers>" as Landing composes it from the Calculator's answer; a landing
 *                    that rewrites the badge carries the line through whole
 *
 * Each written by Blocks::render and read by Blocks::one. PHP reads no field of a payload: a
 * reader answers the payload whole (the Calculator's `canonical` family is the one parser). A
 * held lock's payload is written by the Calculator: lock() checks the members' forms and hands
 * them to the caller's canonical writer, which answers `pcalc canonical canonical_json` of them
 * (Landing asks it in the job, as it asks the register's text), so an account name of any
 * spelling MediaWiki admits is carried exactly. A free lock is the fixed text FREE_LOCK. The
 * badge is built here from values whose forms are checked so that its JSON needs no escape:
 * keys sorted, no space, every string printable ASCII without a quote or a backslash, so the
 * text is the one canonical JSON gives. The two words of
 * the INDEX AND BADGE page (the state, the open volume) are the facts a title cannot carry
 * (PageTitles::classify), read by comparing a whole payload with a fixed word, never parsed.
 */

namespace Custos;

final class PageTexts {
	public const LOCK = 'lock';
	public const REGISTER = 'register';
	public const BADGE = 'badge';
	public const STATE = 'state';
	public const OPEN = 'open';
	public const LIVE = 'LIVE';
	public const RETIRED = 'RETIRED';
	public const STRUCTURE = 'structure';
	/** The STRUCTURE TEST LINE until the first run (TPS 5.3.47), written by the seed. */
	public const STRUCTURE_NONE = 'STRUCTURE TEST none';
	/**
	 * A STRUCTURE TEST LINE after a run: the date, the result ("structurally regular with register",
	 * or FINDINGS and the findings), WITH and the identifiers ("-" when none); one line.
	 */
	private const STRUCTURE_LINE = '/\ASTRUCTURE TEST [0-9]{4}-(?:0[1-9]|1[0-2])-(?:0[1-9]|[12][0-9]|3[01]) (?:structurally regular with register|FINDINGS [^\x00-\x1f\x7f]+) WITH [^\x00-\x1f\x7f]+\z/u';

	private const STAMP = '/\A[0-9]{4}-(?:0[1-9]|1[0-2])-(?:0[1-9]|[12][0-9]|3[01])T(?:[01][0-9]|2[0-3]):[0-5][0-9]:[0-5][0-9]Z\z/';
	private const BLOCK = '/\A[A-Za-z0-9][A-Za-z0-9_.:-]{0,63}\z/';
	private const DIGEST = '/\A[0-9a-f]{64}\z/';
	private const VERSION = '/\A[0-9A-Za-z][0-9A-Za-z.+-]{0,63}\z/';
	/** A free lock's payload: every member null, keys sorted (the Calculator's canonical JSON of it). */
	public const FREE_LOCK = '{"block":null,"expires_at":null,"granted_at":null,"holder":null}';
	/** An account name's longest form: MediaWiki's limit on a title's bytes. */
	private const ACCOUNT_BYTES = 255;
	/**
	 * What no account name MediaWiki admits carries: a control character, a character its titles
	 * refuse (# < > [ ] | { }), a slash, the underscore and the other space characters its titles
	 * fold to a space, a direction mark, the replacement character; nor a space at an end or two
	 * together. Every other UTF-8 name is carried (quotes, backslashes, letters outside ASCII).
	 */
	private const ACCOUNT = '/\A(?! )(?!.* \z)(?!.*  )[^\p{Cc}#<>\[\]|{}\/_\x{A0}\x{1680}\x{180E}\x{2000}-\x{200A}\x{2028}\x{2029}\x{202F}\x{205F}\x{3000}\x{200E}\x{200F}\x{202A}-\x{202E}\x{FFFD}]+\z/su';

	/**
	 * The lock page's text; holder null: the lock is free, and every other value must be null too.
	 * A held lock's payload is $canonical's answer for its members (an array, keys sorted):
	 * the Calculator's canonical JSON of them, one line.
	 *
	 * @param ?callable(array): mixed $canonical required for a held lock
	 */
	public static function lock( string $prefix, ?string $holder, ?string $grantedAt, ?string $expiresAt, ?string $block,
		?callable $canonical = null ): string {
		$all = [ $holder, $grantedAt, $expiresAt, $block ];
		if ( $holder === null ) {
			if ( $all !== [ null, null, null, null ] ) {
				throw new PageFault( 'a free lock carries no grant, expiry or block' );
			}
			$payload = self::FREE_LOCK;
		} else {
			self::account( $holder );
			self::form( (string)$grantedAt, self::STAMP, 'a grant time (YYYY-MM-DDThh:mm:ssZ)' );
			self::form( (string)$expiresAt, self::STAMP, 'an expiry time (YYYY-MM-DDThh:mm:ssZ)' );
			self::form( (string)$block, self::BLOCK, 'a work block\'s name' );
			if ( strcmp( (string)$expiresAt, (string)$grantedAt ) <= 0 ) {
				throw new PageFault( 'a lock expires after it is granted' );
			}
			if ( $canonical === null ) {
				throw new PageFault( 'a held lock\'s payload is the Calculator\'s canonical JSON of its members; no writer given' );
			}
			$payload = $canonical( [ 'block' => $block, 'expires_at' => $expiresAt, 'granted_at' => $grantedAt, 'holder' => $holder ] );
			if ( !is_string( $payload ) || $payload === '' || preg_match( '/[\r\n]/', $payload ) === 1 ) {
				throw new PageFault( 'the lock\'s canonical text is not one line' );
			}
		}
		return self::head( $prefix, 'The lock of the UWC' ) . Blocks::render( self::LOCK, $payload ) . "\n";
	}

	/** Whether $name is an account name the lock carries (ACCOUNT, at most ACCOUNT_BYTES bytes, UTF-8). */
	public static function isAccount( string $name ): bool {
		return $name !== '' && strlen( $name ) <= self::ACCOUNT_BYTES && preg_match( '//u', $name ) === 1
			&& preg_match( self::ACCOUNT, $name ) === 1;
	}

	private static function account( string $name ): void {
		if ( !self::isAccount( $name ) ) {
			throw new PageFault( 'not an account name the lock carries: ' . PageTitles::show( $name ) );
		}
	}

	/** A register volume's text: $records the Calculator's canonical JSON of the volume's records, carried through. */
	public static function register( string $prefix, int $volume, string $records ): string {
		if ( $volume < 1 ) {
			throw new PageFault( "not a volume number: $volume" );
		}
		return self::head( $prefix, "Volume $volume of the register of the UWC" ) . Blocks::render( self::REGISTER, $records ) . "\n";
	}

	/**
	 * The INDEX AND BADGE page's text. $badge: last_push, last_release (a time or null),
	 * calculator_version, calculator_digest (CustosBuild's), record_count (the Calculator's count
	 * of the register's records), research_assembly (the Research Assembly's digest). $structure:
	 * the STRUCTURE TEST LINE (STRUCTURE_NONE or a line in its form), null where the UWC has none.
	 */
	public static function badge( string $prefix, array $badge, bool $retired, int $openVolume, ?string $structure = null ): string {
		$keys = [ 'calculator_digest', 'calculator_version', 'last_push', 'last_release', 'record_count', 'research_assembly' ];
		$given = array_keys( $badge );
		sort( $given );
		if ( $given !== $keys ) {
			throw new PageFault( 'the badge carries exactly ' . implode( ', ', $keys ) );
		}
		foreach ( [ 'last_push', 'last_release' ] as $k ) {
			if ( $badge[$k] !== null ) {
				self::form( $badge[$k], self::STAMP, "the badge's $k (a time or null)" );
			}
		}
		self::form( $badge['calculator_version'], self::VERSION, 'the Calculator\'s version' );
		self::form( $badge['calculator_digest'], self::DIGEST, 'the Calculator\'s digest' );
		self::form( $badge['research_assembly'], self::DIGEST, 'the Research Assembly\'s digest' );
		if ( !is_int( $badge['record_count'] ) || $badge['record_count'] < 0 ) {
			throw new PageFault( 'the badge\'s record_count is a count' );
		}
		if ( $openVolume < 1 ) {
			throw new PageFault( "not a volume number: $openVolume" );
		}
		if ( $structure !== null && !self::isStructureLine( $structure ) ) {
			throw new PageFault( 'not a STRUCTURE TEST LINE: ' . PageTitles::show( $structure ) );
		}
		return self::head( $prefix, 'The index and badge of the UWC' )
			. Blocks::render( self::BADGE, self::object( $badge ) ) . "\n"
			. Blocks::render( self::STATE, $retired ? self::RETIRED : self::LIVE ) . "\n"
			. Blocks::render( self::OPEN, (string)$openVolume ) . "\n"
			. ( $structure === null ? '' : Blocks::render( self::STRUCTURE, $structure ) . "\n" );
	}

	/** Whether $line is STRUCTURE_NONE or a STRUCTURE TEST LINE in its form. */
	public static function isStructureLine( string $line ): bool {
		return $line === self::STRUCTURE_NONE || preg_match( self::STRUCTURE_LINE, $line ) === 1;
	}

	/**
	 * What a STRUCTURE TEST LINE says beside its date: the result and the identifiers ("none" for
	 * STRUCTURE_NONE). Two lines that differ only in their date say the same: the line is rewritten
	 * only when this changes (TPS 5.3.47).
	 */
	public static function structureSays( string $line ): string {
		return $line === self::STRUCTURE_NONE ? 'none' : substr( $line, strlen( 'STRUCTURE TEST 0000-00-00 ' ) );
	}

	/** The STRUCTURE TEST LINE, whole; null when the page has none. @throws PageFault */
	public static function readStructure( ?string $text ): ?string {
		return Blocks::one( $text, self::STRUCTURE );
	}

	/** The lock's payload, whole; null when the page has none. @throws PageFault */
	public static function readLock( ?string $text ): ?string {
		return Blocks::one( $text, self::LOCK );
	}

	/** The register volume's records, whole; null when the page has none. @throws PageFault */
	public static function readRegister( ?string $text ): ?string {
		return Blocks::one( $text, self::REGISTER );
	}

	/** The badge's payload, whole; null when the page has none. @throws PageFault */
	public static function readBadge( ?string $text ): ?string {
		return Blocks::one( $text, self::BADGE );
	}

	/**
	 * The facts PageTitles::classify takes for a page of the UWC whose INDEX AND BADGE page is
	 * $text: "retired" only when the page states LIVE or RETIRED; "open" => the open volume's
	 * number only when it is digits. A page absent, or carrying anything else, states nothing,
	 * and each absent fact takes classify's reading that refuses.
	 */
	public static function facts( ?string $text ): array {
		try {
			$state = Blocks::one( $text, self::STATE );
			$open = Blocks::one( $text, self::OPEN );
		} catch ( PageFault $e ) {
			return [];
		}
		$facts = [];
		if ( $state === self::LIVE || $state === self::RETIRED ) {
			$facts['retired'] = $state === self::RETIRED;
		}
		if ( $open !== null && preg_match( '/\A[1-9][0-9]{0,8}\z/', $open ) === 1 ) {
			$facts['open_volume'] = (int)$open;
		}
		return $facts;
	}

	private static function head( string $prefix, string $what ): string {
		if ( !PageTitles::isPrefix( $prefix ) ) {
			throw new PageFault( 'not a record prefix: ' . PageTitles::show( $prefix ) );
		}
		return "$what $prefix, written by Custos; it is changed only by a landing.\n\n";
	}

	private static function form( mixed $v, string $pattern, string $what ): void {
		if ( !is_string( $v ) || preg_match( $pattern, $v ) !== 1 ) {
			throw new PageFault( "not $what: " . ( is_string( $v ) ? PageTitles::show( $v ) : gettype( $v ) ) );
		}
	}

	/**
	 * The JSON of an object of checked values (strings in forms needing no escape, counts, null):
	 * keys sorted, no space; the text canonical JSON gives.
	 */
	private static function object( array $o ): string {
		ksort( $o, SORT_STRING );
		$members = [];
		foreach ( $o as $k => $v ) {
			$members[] = '"' . $k . '":' . ( $v === null ? 'null' : ( is_int( $v ) ? (string)$v : '"' . $v . '"' ) );
		}
		return '{' . implode( ',', $members ) . '}';
	}
}
