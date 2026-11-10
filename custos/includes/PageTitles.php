<?php
/**
 * PageTitles: the title of every page Custos writes, built from the two page roots, and
 * the reverse: classify(), which says what page class a title names. Pure: no MediaWiki class is
 * used, so the harness tests it without the host; the permission hook and the page writer read
 * titles through it.
 *
 * The forms are version 1's (TPS 5.3, 5.6.10, 5.9.13, 5.11, 5.13.2, 5.19.1, 5.20, 5.21, 5.22,
 * and the title helpers of its Recorder) in PMA's words (docs/terminology_map.md). Under the UWC
 * root, per UWC <p> (its record prefix):
 *   <p>/Draft                              DRAFT UWC
 *   <p>/Research Assembly/<zone>           RESEARCH ASSEMBLY (Starting Set, Correspondence Table, Criteria Set)
 *   <p>/Register/Volume <v>                REGISTER OPEN or REGISTER FROZEN
 *   <p>/Bibliography/Volume <v>            BIBLIOGRAPHY OPEN or BIBLIOGRAPHY FROZEN
 *   <p>/Access list                        ACCESS LIST
 *   <p>/Lock                               LOCK PAGE
 *   <p>/Collaboration                      COLLABORATION
 *   <p>/Collaboration/Staging[/...]        STAGING
 *   <p>/Control panel[/...]                CONTROL PANEL (the schedule and work-block logs beneath)
 *   <p>/Index                              INDEX AND BADGE
 *   <p>/Reading                            SPINE
 *   <p>/Community View                     COMMUNITY LEDGER
 * and the fleet's index, <UWC root>/Index, INDEX AND BADGE. Under the Declarer's root:
 *   Declarations, Build chain              CHAIN HEAD
 *   Declarations/Volume <v>                DECLARATIONS VOLUME
 *   Build chain/Volume <v>                 BUILD CHAIN VOLUME
 *   Community Ledger/Volume <v>            COMMUNITY LEDGER
 *   Dossier/<account>                      DOSSIER
 *   Falcon/<id>                            FALCON PAGE
 *   Top performers[/<YYYY-MM>]             TOP PERFORMER
 *   Configuration strata                   CONFIGURATION STRATA
 *   Provision/<id>/<version>               PROVISION
 * In the restricted namespace:
 *   Restricted:Score/<account>             SCORE OR USER PAGE
 *   Restricted:Falcon/<id>, Falcon/Stratum FALCON RESTRICTED
 *
 * A title is GOVERNED when it lies under the UWC root, in the restricted namespace, or under one
 * of the Declarer's root's segments above. A governed title in none of the forms has no class,
 * and every check refuses it. Facts a title cannot carry are passed to classify(), and each one
 * absent takes the reading that refuses: a volume is FROZEN unless stated OPEN; a UWC stated
 * RETIRED puts every page of it in RETIRED CONTAINER.
 *
 * classify() first reads a title as MediaWiki does (canon(): NFC, its space characters folded,
 * direction marks dropped, a leading colon, the namespace in any case with spaces around its
 * colon, the first letter upper case), and only then tests whether it is governed. A title it
 * cannot read exactly is governed and refused; so is a governed title MediaWiki would refuse.
 * Every fact a UWC page needs must be stated: "retired" must be true or false, else no class.
 * A record prefix may carry underscores, so the builders refuse a prefix with a run of two (it
 * would name the same page as the prefix with one) and classify() reads a prefix's spaces back
 * as underscores.
 */

namespace Custos;

use MediaWiki\Config\Config;

final class PageTitles {
	/**
	 * The restricted namespace's title, with no talk namespace, registered by extension.json under the number
	 * $wgCustosRestrictedNamespace defaults to (RESTRICTED_NUMBER); the permission hook reads a
	 * title in it through that number (PermissionHook::titleText).
	 */
	public const RESTRICTED_NAMESPACE = 'Restricted';
	/** Its default number: even, outside the namespaces MediaWiki and its extensions register. */
	public const RESTRICTED_NUMBER = 7240;
	/** The Research Assembly's three zones, in PMA's words (v1: TPK, TrM, TMS). */
	public const ZONES = [ 'Starting Set', 'Correspondence Table', 'Criteria Set' ];
	/** The fleet index's name under the UWC root; never a UWC's prefix. */
	public const FLEET_INDEX = 'Index';
	/** The falcon stratum page's name in the restricted namespace; never a falcon's identifier. */
	public const STRATUM = 'Stratum';
	/** MediaWiki's limit on a title's bytes. */
	public const MAX_BYTES = 255;

	/** The segments of the Declarer's root Custos governs. */
	private const DECL_SEGMENTS = [ 'Declarations', 'Build chain', 'Community Ledger', 'Dossier', 'Falcon',
		'Top performers', 'Configuration strata', 'Provision' ];

	private string $uwcRoot;
	private string $declRoot;

	/**
	 * Each root must already be in MediaWiki's canonical form (canon() leaves it unchanged), in
	 * the main namespace (no colon), its first letter upper case, no slash at either end and no
	 * empty segment, every segment one title segment. The Declarer's root must not lie under
	 * the UWC root, nor the UWC root under one of the Declarer's root's governed segments, so
	 * that no title reads under both. Else PageFault: an invalid root never classifies.
	 */
	public function __construct( string $uwcRoot, string $declRoot ) {
		foreach ( [ 'CustosUwcRoot' => $uwcRoot, 'CustosDeclRoot' => $declRoot ] as $key => $root ) {
			$c = self::canon( $root );
			$segs = explode( '/', $root );
			if ( $root === '' || $c === null || $c[0] !== null || $c[1] !== $root || !$c[2]
				|| strpos( $root, ':' ) !== false || !self::allSegments( $segs ) ) {
				throw new PageFault( "the page root $key is not a title in canonical form: " . self::show( $root ) );
			}
		}
		if ( $declRoot === $uwcRoot || strncmp( $declRoot . '/', $uwcRoot . '/', strlen( $uwcRoot ) + 1 ) === 0 ) {
			throw new PageFault( 'the Declarer\'s root lies at or under the UWC root' );
		}
		foreach ( self::DECL_SEGMENTS as $seg ) {
			$g = $declRoot . '/' . $seg;
			if ( $uwcRoot === $g || strncmp( $uwcRoot, $g . '/', strlen( $g ) + 1 ) === 0 ) {
				throw new PageFault( "the UWC root lies under the Declarer's governed segment $seg" );
			}
		}
		$this->uwcRoot = $uwcRoot;
		$this->declRoot = $declRoot;
	}

	public static function fromConfig( Config $config ): self {
		return new self( (string)$config->get( 'CustosUwcRoot' ), (string)$config->get( 'CustosDeclRoot' ) );
	}

	// ---- the builders: one per title form -----------------------------------------------------

	public function uwc( string $prefix ): string {
		return $this->check( $this->uwcRoot . '/' . self::prefixSegment( $prefix ) );
	}

	public function draft( string $prefix ): string {
		return $this->check( $this->uwc( $prefix ) . '/Draft' );
	}

	public function researchAssembly( string $prefix, string $zone ): string {
		if ( !in_array( $zone, self::ZONES, true ) ) {
			throw new PageFault( 'not a zone of the Research Assembly: ' . self::show( $zone ) );
		}
		return $this->check( $this->uwc( $prefix ) . '/Research Assembly/' . $zone );
	}

	public function registerVolume( string $prefix, int $volume ): string {
		return $this->check( $this->uwc( $prefix ) . '/Register/Volume ' . self::volume( $volume ) );
	}

	public function bibliographyVolume( string $prefix, int $volume ): string {
		return $this->check( $this->uwc( $prefix ) . '/Bibliography/Volume ' . self::volume( $volume ) );
	}

	public function accessList( string $prefix ): string {
		return $this->check( $this->uwc( $prefix ) . '/Access list' );
	}

	public function lock( string $prefix ): string {
		return $this->check( $this->uwc( $prefix ) . '/Lock' );
	}

	public function collaboration( string $prefix ): string {
		return $this->check( $this->uwc( $prefix ) . '/Collaboration' );
	}

	/** The staging subpage, or a page beneath it ($sub one or more segments). */
	public function staging( string $prefix, string $sub = '' ): string {
		return $this->check( $this->uwc( $prefix ) . '/Collaboration/Staging' . self::sub( $sub ) );
	}

	/** The control panel, or a page beneath it: its schedule log, its work-block log. */
	public function controlPanel( string $prefix, string $sub = '' ): string {
		return $this->check( $this->uwc( $prefix ) . '/Control panel' . self::sub( $sub ) );
	}

	/** A UWC's Index page, the badge's page (v1: Manifest). */
	public function index( string $prefix ): string {
		return $this->check( $this->uwc( $prefix ) . '/Index' );
	}

	/** A UWC's Reading page (v1: Library). */
	public function reading( string $prefix ): string {
		return $this->check( $this->uwc( $prefix ) . '/Reading' );
	}

	public function communityView( string $prefix ): string {
		return $this->check( $this->uwc( $prefix ) . '/Community View' );
	}

	/** The fleet's index of UWCs. */
	public function fleetIndex(): string {
		return $this->check( $this->uwcRoot . '/' . self::FLEET_INDEX );
	}

	public function declarationsHead(): string {
		return $this->check( $this->declRoot . '/Declarations' );
	}

	public function declarationsVolume( int $volume ): string {
		return $this->check( $this->declRoot . '/Declarations/Volume ' . self::volume( $volume ) );
	}

	public function buildChainHead(): string {
		return $this->check( $this->declRoot . '/Build chain' );
	}

	public function buildChainVolume( int $volume ): string {
		return $this->check( $this->declRoot . '/Build chain/Volume ' . self::volume( $volume ) );
	}

	public function communityLedgerVolume( int $volume ): string {
		return $this->check( $this->declRoot . '/Community Ledger/Volume ' . self::volume( $volume ) );
	}

	public function dossier( string $account ): string {
		return $this->check( $this->declRoot . '/Dossier/' . self::segment( $account, 'an account' ) );
	}

	public function falconPage( string $id ): string {
		return $this->check( $this->declRoot . '/Falcon/' . self::falconId( $id ) );
	}

	/** The top performer page, or its snapshot of a month (YYYY-MM). */
	public function topPerformers( ?string $month = null ): string {
		if ( $month === null ) {
			return $this->check( $this->declRoot . '/Top performers' );
		}
		if ( !self::isMonth( $month ) ) {
			throw new PageFault( 'not a month (YYYY-MM): ' . self::show( $month ) );
		}
		return $this->check( $this->declRoot . '/Top performers/' . $month );
	}

	public function configurationStrata(): string {
		return $this->check( $this->declRoot . '/Configuration strata' );
	}

	public function provision( string $id, string $version ): string {
		if ( !self::isProvisionId( $id ) ) {
			throw new PageFault( 'not a Provision identifier: ' . self::show( $id ) );
		}
		if ( !self::isVersion( $version ) ) {
			throw new PageFault( 'not a Provision version: ' . self::show( $version ) );
		}
		return $this->check( $this->declRoot . '/Provision/' . $id . '/' . $version );
	}

	public function score( string $account ): string {
		return $this->check( self::RESTRICTED_NAMESPACE . ':Score/' . self::segment( $account, 'an account' ) );
	}

	public function falconRestricted( string $id ): string {
		return $this->check( self::RESTRICTED_NAMESPACE . ':Falcon/' . self::falconId( $id ) );
	}

	public function falconStratum(): string {
		return $this->check( self::RESTRICTED_NAMESPACE . ':Falcon/' . self::STRATUM );
	}

	// ---- the reverse --------------------------------------------------------------------------

	/**
	 * What $title names. $facts: "open" => true for a register or bibliography volume the
	 * Calculator found OPEN (else FROZEN); "retired" => true or false, required for every page
	 * of a UWC (absent or not a boolean: no class). RETIRED gives RETIRED CONTAINER only to a
	 * page that fits a form.
	 */
	public function classify( string $title, array $facts = [] ): PageRef {
		$c = self::canon( $title );
		if ( $c === null ) {
			// Not readable exactly (not UTF-8, not normalizable here, a second leading colon, a
			// character reference not decoded exactly): it may name any governed page, the
			// restricted ones included, so it is governed, restricted and refused (fail closed).
			return new PageRef( null, true, true );
		}
		[ $ns, $t, $valid ] = $c;
		$hadReference = $c[3];
		$open = ( $facts['open'] ?? false ) === true;
		$retired = $facts['retired'] ?? null;

		if ( $ns === self::RESTRICTED_NAMESPACE ) {
			$r = $this->restricted( $t );
		} else {
			$r = null;
			$u = $this->uwcRoot . '/';
			$d = $this->declRoot . '/';
			if ( strncmp( $t, $u, strlen( $u ) ) === 0 ) {
				$r = $this->underUwc( substr( $t, strlen( $u ) ), $open, $retired );
			} elseif ( $t === $this->uwcRoot ) {
				$r = new PageRef( null, true, false );
			} elseif ( strncmp( $t, $d, strlen( $d ) ) === 0 ) {
				$r = $this->underDecl( substr( $t, strlen( $d ) ) );
			}
			if ( $r === null ) {
				return new PageRef( null, false, false );
			}
		}
		if ( ( !$valid || $hadReference ) && $r->governed ) {
			// A title MediaWiki refuses, or reads only up to a "#", or one written with a character
			// reference (Custos never writes one): never a page of a class.
			return new PageRef( null, true, $r->restricted );
		}
		return $r;
	}

	private function restricted( string $rest ): PageRef {
		$s = explode( '/', $rest );
		if ( count( $s ) === 2 && $s[0] === 'Score' && self::isSegment( $s[1] ) ) {
			return new PageRef( PageClass::SCORE_OR_USER_PAGE, true, true, null, null, $s[1] );
		}
		if ( count( $s ) === 2 && $s[0] === 'Falcon' && self::isSegment( $s[1] ) ) {
			return new PageRef( PageClass::FALCON_RESTRICTED, true, true, null, null, null, $s[1] );
		}
		return new PageRef( null, true, true );
	}

	/** $retired: the caller's fact, which must be a boolean for every page of a UWC. */
	private function underUwc( string $rest, bool $open, mixed $retired ): PageRef {
		$s = explode( '/', $rest );
		if ( $s === [ self::FLEET_INDEX ] ) {
			return new PageRef( PageClass::INDEX_AND_BADGE, true, false );
		}
		$prefix = str_replace( ' ', '_', $s[0] );
		if ( !self::isBuildablePrefix( $prefix ) ) {
			return new PageRef( null, true, false );
		}
		if ( !is_bool( $retired ) ) {
			return new PageRef( null, true, false, $prefix );
		}
		$class = null;
		$volume = null;
		$part = null;
		$tail = array_slice( $s, 1 );
		$n = count( $tail );
		$head = $tail[0] ?? null;
		if ( $n === 1 ) {
			$class = [
				'Draft' => PageClass::DRAFT_UWC,
				'Access list' => PageClass::ACCESS_LIST,
				'Lock' => PageClass::LOCK_PAGE,
				'Collaboration' => PageClass::COLLABORATION,
				'Control panel' => PageClass::CONTROL_PANEL,
				'Index' => PageClass::INDEX_AND_BADGE,
				'Reading' => PageClass::SPINE,
				'Community View' => PageClass::COMMUNITY_LEDGER,
			][$head] ?? null;
		} elseif ( $n === 2 && $head === 'Research Assembly' && in_array( $tail[1], self::ZONES, true ) ) {
			$class = PageClass::RESEARCH_ASSEMBLY;
			$part = $tail[1];
		} elseif ( $n === 2 && ( $head === 'Register' || $head === 'Bibliography' ) ) {
			$volume = self::readVolume( $tail[1] );
			if ( $volume !== null ) {
				$class = $head === 'Register'
					? ( $open ? PageClass::REGISTER_OPEN : PageClass::REGISTER_FROZEN )
					: ( $open ? PageClass::BIBLIOGRAPHY_OPEN : PageClass::BIBLIOGRAPHY_FROZEN );
			}
		} elseif ( $n >= 2 && $head === 'Collaboration' && $tail[1] === 'Staging' && self::allSegments( $tail ) ) {
			$class = PageClass::STAGING;
		} elseif ( $n >= 2 && $head === 'Control panel' && self::allSegments( $tail ) ) {
			$class = PageClass::CONTROL_PANEL;
		}
		if ( $retired && $class !== null ) {
			$class = PageClass::RETIRED_CONTAINER;
		}
		return new PageRef( $class, true, false, $prefix, $volume, null, $part );
	}

	private function underDecl( string $rest ): PageRef {
		$s = explode( '/', $rest );
		if ( !in_array( $s[0], self::DECL_SEGMENTS, true ) ) {
			return new PageRef( null, false, false );
		}
		$n = count( $s );
		$volume = $n === 2 ? self::readVolume( $s[1] ) : null;
		switch ( $s[0] ) {
			case 'Declarations':
			case 'Build chain':
				if ( $n === 1 ) {
					return new PageRef( PageClass::CHAIN_HEAD, true, false );
				}
				if ( $volume !== null ) {
					return new PageRef( $s[0] === 'Declarations' ? PageClass::DECLARATIONS_VOLUME : PageClass::BUILD_CHAIN_VOLUME,
						true, false, null, $volume );
				}
				break;
			case 'Community Ledger':
				if ( $volume !== null ) {
					return new PageRef( PageClass::COMMUNITY_LEDGER, true, false, null, $volume );
				}
				break;
			case 'Dossier':
				if ( $n === 2 && self::isSegment( $s[1] ) ) {
					return new PageRef( PageClass::DOSSIER, true, false, null, null, $s[1] );
				}
				break;
			case 'Falcon':
				if ( $n === 2 && self::isSegment( $s[1] ) && $s[1] !== self::STRATUM ) {
					return new PageRef( PageClass::FALCON_PAGE, true, false, null, null, null, $s[1] );
				}
				break;
			case 'Top performers':
				if ( $n === 1 ) {
					return new PageRef( PageClass::TOP_PERFORMER, true, false );
				}
				if ( $n === 2 && self::isMonth( $s[1] ) ) {
					return new PageRef( PageClass::TOP_PERFORMER, true, false, null, null, null, $s[1] );
				}
				break;
			case 'Configuration strata':
				if ( $n === 1 ) {
					return new PageRef( PageClass::CONFIGURATION_STRATA, true, false );
				}
				break;
			case 'Provision':
				if ( $n === 3 && self::isProvisionId( $s[1] ) && self::isVersion( $s[2] ) ) {
					return new PageRef( PageClass::PROVISION, true, false, null, null, null, $s[1], $s[2] );
				}
				break;
		}
		return new PageRef( null, true, false );
	}

	// ---- the grammar --------------------------------------------------------------------------

	/** The characters MediaWiki folds to one space in a title (MediaWikiTitleCodec), underscore included. */
	private const SPACES = '[ _\x{A0}\x{1680}\x{180E}\x{2000}-\x{200A}\x{2028}\x{2029}\x{202F}\x{205F}\x{3000}]';
	/** The direction marks MediaWiki strips from a title. */
	private const MARKS = '[\x{200E}\x{200F}\x{202A}-\x{202E}]';

	/** The whitespace fold alone: a run of MediaWiki's space characters is one space; the ends trimmed. */
	public static function norm( string $title ): string {
		if ( preg_match( '//u', $title ) !== 1 ) {
			return $title;
		}
		return trim( (string)preg_replace( '/' . self::SPACES . '+/u', ' ', $title ), ' ' );
	}

	/**
	 * A title as MediaWiki reads it: [namespace (RESTRICTED_NAMESPACE or null for the main
	 * one), text, valid, written with a character reference], or null when it cannot be read
	 * exactly. In order: valid UTF-8; character references decoded once (decodeReferences); NFC
	 * (Normalizer; without it any non-ASCII byte makes the title unreadable); the direction
	 * marks removed; MediaWiki's space characters folded; one leading colon dropped (a second
	 * makes it unreadable); the namespace "Restricted" in any case, spaces allowed around its
	 * colon; the first letter upper case. Valid is false when MediaWiki would refuse the title
	 * or read only part of it: a character it refuses (# < > [ ] | { }, a control), a percent
	 * escape, an HTML entity, a relative path segment, three tildes, an empty text, more than
	 * MAX_BYTES bytes; "#" cuts the text there.
	 */
	public static function canon( string $title, ?bool $normalizer = null ): ?array {
		if ( preg_match( '//u', $title ) !== 1 ) {
			return null;
		}
		$decoded = self::decodeReferences( $title );
		if ( $decoded === null ) {
			return null;
		}
		$hadReference = $decoded !== $title;
		$title = $decoded;
		$normalizer ??= class_exists( 'Normalizer' );
		if ( $normalizer ) {
			$n = \Normalizer::normalize( $title, \Normalizer::FORM_C );
			if ( !is_string( $n ) ) {
				return null;
			}
			$title = $n;
		} elseif ( preg_match( '/[\x80-\xff]/', $title ) === 1 ) {
			return null;
		}
		$t = self::norm( (string)preg_replace( '/' . self::MARKS . '/u', '', $title ) );
		if ( $t !== '' && $t[0] === ':' ) {
			$t = ltrim( substr( $t, 1 ), ' ' );
			if ( $t !== '' && $t[0] === ':' ) {
				return null;
			}
		}
		$ns = null;
		if ( preg_match( '/\A([^:]+?) ?: ?(.*)\z/su', $t, $m ) === 1 ) {
			if ( strcasecmp( str_replace( ' ', '_', $m[1] ), self::RESTRICTED_NAMESPACE ) === 0 ) {
				$ns = self::RESTRICTED_NAMESPACE;
				$t = $m[2];
			}
		}
		$valid = true;
		$cut = strpos( $t, '#' );
		if ( $cut !== false ) {
			$valid = false;
			$t = rtrim( substr( $t, 0, $cut ), ' ' );
		}
		if ( $t !== '' ) {
			$first = mb_substr( $t, 0, 1, 'UTF-8' );
			$t = mb_strtoupper( $first, 'UTF-8' ) . substr( $t, strlen( $first ) );
		}
		if ( $t === '' || strlen( $t ) > self::MAX_BYTES
			|| preg_match( '/[<>\[\]|{}\x00-\x1f\x7f]|\p{Cc}|%[0-9A-Fa-f]{2}|&[A-Za-z0-9\x80-\xff#]+;|~~~/u', $t ) === 1
			|| preg_match( '#(?:\A|/)\.{1,2}(?:/|\z)#', $t ) === 1 ) {
			$valid = false;
		}
		return [ $ns, $t, $valid, $hadReference ];
	}

	/**
	 * MediaWiki's first step on a title (Sanitizer::decodeCharReferencesAndNormalize): every
	 * character reference decoded once, decimal &#NNN;, hexadecimal &#xHH; and named &name;.
	 * Null when a reference cannot be decoded exactly here: a numeric one outside the code
	 * points MediaWiki keeps (it would give U+FFFD), a named one PHP's HTML5 table does not
	 * hold (MediaWiki's aliases among them), or a pattern match that fails. A name PHP decodes
	 * and MediaWiki would not leaves MediaWiki an invalid title, and classify() gives no title
	 * written with a reference a class, so the wider table only refuses.
	 */
	private static function decodeReferences( string $s ): ?string {
		$bad = false;
		$out = preg_replace_callback( '/&(?:#([0-9]+)|#[xX]([0-9A-Fa-f]+)|([A-Za-z\x80-\xff][A-Za-z0-9\x80-\xff]*));/',
			static function ( array $m ) use ( &$bad ): string {
				if ( ( $m[3] ?? '' ) !== '' ) {
					$d = html_entity_decode( $m[0], ENT_QUOTES | ENT_HTML5, 'UTF-8' );
					if ( $d === $m[0] ) {
						$bad = true;
					}
					return $d;
				}
				$digits = ( $m[2] ?? '' ) !== '' ? $m[2] : $m[1];
				$hex = ( $m[2] ?? '' ) !== '';
				$digits = ltrim( $digits, '0' );
				if ( strlen( $digits ) > 8 ) {
					$bad = true;
					return '';
				}
				$cp = $digits === '' ? 0 : ( $hex ? hexdec( $digits ) : (int)$digits );
				if ( !( $cp === 0x09 || $cp === 0x0a || $cp === 0x0d || ( $cp >= 0x20 && $cp <= 0xd7ff )
					|| ( $cp >= 0xe000 && $cp <= 0xfffd ) || ( $cp >= 0x10000 && $cp <= 0x10ffff ) ) ) {
					$bad = true;
					return '';
				}
				return mb_chr( (int)$cp, 'UTF-8' );
			}, $s );
		return ( $out === null || $bad ) ? null : $out;
	}

	/** A record prefix: [A-Za-z_][A-Za-z0-9_]* (v1's identifier, Principia's Zone.isIdent). */
	public static function isPrefix( string $p ): bool {
		return preg_match( '/\A[A-Za-z_][A-Za-z0-9_]*\z/', $p ) === 1;
	}

	/** v1's module identifier, Principia's isProvisionId: at most 32, [A-Z][A-Z0-9]*(-[A-Z0-9]+)*. */
	public static function isProvisionId( string $s ): bool {
		return strlen( $s ) <= 32 && preg_match( '/\A[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*\z/', $s ) === 1;
	}

	/** Principia's isVersion: three parts, each 0 or 1-9 then at most three digits. */
	public static function isVersion( string $s ): bool {
		return preg_match( '/\A(?:0|[1-9][0-9]{0,3})\.(?:0|[1-9][0-9]{0,3})\.(?:0|[1-9][0-9]{0,3})\z/', $s ) === 1;
	}

	public static function isMonth( string $s ): bool {
		return preg_match( '/\A[0-9]{4}-(?:0[1-9]|1[0-2])\z/', $s ) === 1;
	}

	/**
	 * One title segment: valid UTF-8, not empty, no "/", no character MediaWiki refuses in a
	 * title (# < > [ ] | { }), no control or format character, no underscore (a space is its
	 * text form), no leading or trailing space, no run of spaces.
	 */
	public static function isSegment( string $s ): bool {
		return $s !== '' && $s !== '.' && $s !== '..' && preg_match( '//u', $s ) === 1
			&& preg_match( '/[\/#<>\[\]|{}_\x00-\x1f\x7f]|\p{C}|\x{2028}|\x{2029}|%[0-9A-Fa-f]{2}|&[A-Za-z0-9\x80-\xff#]+;|~~~/u', $s ) === 0
			&& $s === self::norm( $s )
			&& ( class_exists( 'Normalizer' ) ? \Normalizer::isNormalized( $s, \Normalizer::FORM_C )
				: preg_match( '/[\x80-\xff]/', $s ) === 0 );
	}

	/** A prefix the builders accept: an identifier, no run of underscores, none at an end, not Index. */
	public static function isBuildablePrefix( string $p ): bool {
		try {
			self::prefixSegment( $p );
			return true;
		} catch ( PageFault $e ) {
			return false;
		}
	}

	private static function allSegments( array $parts ): bool {
		foreach ( $parts as $p ) {
			if ( !self::isSegment( $p ) ) {
				return false;
			}
		}
		return true;
	}

	/** A volume number's text: 1, 2, ... without a leading zero. */
	private static function readVolume( string $s ): ?int {
		return preg_match( '/\AVolume ([1-9][0-9]{0,8})\z/', $s, $m ) === 1 ? (int)$m[1] : null;
	}

	private static function volume( int $v ): string {
		if ( $v < 1 || $v > 999999999 ) {
			throw new PageFault( "not a volume number: $v" );
		}
		return (string)$v;
	}

	private static function prefixSegment( string $prefix ): string {
		if ( !self::isPrefix( $prefix ) ) {
			throw new PageFault( 'not a record prefix ([A-Za-z_][A-Za-z0-9_]*): ' . self::show( $prefix ) );
		}
		if ( strpos( $prefix, '__' ) !== false ) {
			throw new PageFault( "the prefix $prefix carries a run of underscores; its title would name the same page as another prefix's" );
		}
		if ( $prefix[0] === '_' || substr( $prefix, -1 ) === '_' ) {
			throw new PageFault( "the prefix $prefix begins or ends with an underscore; its title segment would begin or end with a space" );
		}
		if ( $prefix === self::FLEET_INDEX ) {
			throw new PageFault( 'the prefix Index names the fleet index\'s page' );
		}
		return str_replace( '_', ' ', $prefix );
	}

	private static function segment( string $s, string $what ): string {
		if ( !self::isSegment( $s ) ) {
			throw new PageFault( "not $what that is one title segment: " . self::show( $s ) );
		}
		return $s;
	}

	private static function falconId( string $id ): string {
		self::segment( $id, 'a falcon identifier' );
		if ( $id === self::STRATUM ) {
			throw new PageFault( 'the falcon identifier Stratum names the stratum page' );
		}
		return $id;
	}

	private static function sub( string $sub ): string {
		if ( $sub === '' ) {
			return '';
		}
		foreach ( explode( '/', $sub ) as $p ) {
			self::segment( $p, 'a subpage name' );
		}
		return '/' . $sub;
	}

	private function check( string $title ): string {
		if ( strlen( $title ) > self::MAX_BYTES ) {
			throw new PageFault( 'the title is longer than ' . self::MAX_BYTES . ' bytes: ' . self::show( substr( $title, 0, 64 ) ) . '...' );
		}
		return $title;
	}

	/** Input shown in a message: every disallowed code point as <U+XXXX>, every invalid byte as <0xHH> (v1's echo safety). */
	public static function show( string $s ): string {
		$out = '';
		$i = 0;
		$len = strlen( $s );
		while ( $i < $len ) {
			if ( preg_match( '/\G(?:[\x00-\x7f]|[\xc2-\xdf][\x80-\xbf]|\xe0[\xa0-\xbf][\x80-\xbf]|[\xe1-\xec\xee\xef][\x80-\xbf]{2}'
				. '|\xed[\x80-\x9f][\x80-\xbf]|\xf0[\x90-\xbf][\x80-\xbf]{2}|[\xf1-\xf3][\x80-\xbf]{3}|\xf4[\x80-\x8f][\x80-\xbf]{2})/',
				$s, $m, 0, $i ) !== 1 ) {
				$out .= sprintf( '<0x%02X>', ord( $s[$i] ) );
				$i++;
				continue;
			}
			$c = $m[0];
			$i += strlen( $c );
			if ( ( $c !== "\t" && preg_match( '/\A(?:\p{C}|\x{2028}|\x{2029})\z/u', $c ) === 1 ) ) {
				$out .= sprintf( '<U+%04X>', mb_ord( $c, 'UTF-8' ) );
			} else {
				$out .= $c;
			}
		}
		return '"' . $out . '"';
	}
}
