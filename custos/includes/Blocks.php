<?php
/**
 * Blocks: Custos's content model. A page Custos writes holds its machine text in
 * preformatted blocks of a named class, as version 1 did:
 *
 *   <pre class="pma-<name>">
 *   <payload>
 *   </pre>
 *
 * the payload the Calculator's canonical JSON (or a chain's lines), on lines of its own. PHP
 * reads no JSON here: the Calculator's `canonical` family is the one parser, and MediaWiki
 * validates nothing on save. This class only writes a block and finds the blocks of a name, and
 * refuses what would make that ambiguous: a name outside [a-z]+, a payload that could close the
 * block or is not UTF-8, a page whose blocks do not close or nest.
 */

namespace Custos;

final class Blocks {
	/** The class every block's name is prefixed with. */
	public const PREFIX = 'pma-';
	/** A pre tag opening, as MediaWiki's parser reads one: any case, then a space, ">" or "/". */
	private const OPEN = '#<pre(?=[\s>/])#i';
	/** A pre tag closing, in any case. */
	private const CLOSE = '#</pre\s*>#i';
	/**
	 * What changes how MediaWiki's parser reads a pre tag, or hides one: a comment, and the tags
	 * whose content is not parsed as wikitext (nowiki, syntaxhighlight, source, math, chem, ce,
	 * score, graph, templatedata, includeonly, noinclude, onlyinclude, gallery, hiero, timeline,
	 * html, ref, references, translate, poem, mapframe, maplink, imagemap, inputbox, categorytree),
	 * opening or closing, any
	 * case. A page or payload carrying one is ambiguous and refused (fail closed).
	 */
	private const AMBIGUOUS = '#<!--|<\s*/?\s*(?:nowiki|syntaxhighlight|source|math|chem|ce|score|graph|templatedata|includeonly|noinclude|onlyinclude|gallery|hiero|timeline|html|ref|references|translate|poem|mapframe|maplink|imagemap|inputbox|categorytree)(?=[\s>/])#i';

	/** The block's text: the opening tag, a line feed, the payload, a line feed, the closing tag. */
	public static function render( string $name, string $payload ): string {
		self::name( $name );
		self::payload( $payload );
		return '<pre class="' . self::PREFIX . $name . "\">\n" . $payload . "\n</pre>";
	}

	/**
	 * The payloads of every block named $name on $text, in page order; [] for a page without
	 * one (null: no page). Blocks of other names, and text between blocks, are passed over.
	 *
	 * @throws PageFault the page's blocks do not close, nest, or a block is not in the form above
	 */
	public static function extract( ?string $text, string $name ): array {
		self::name( $name );
		$out = [];
		foreach ( self::all( $text ) as [ $n, $payload ] ) {
			if ( $n === $name ) {
				$out[] = $payload;
			}
		}
		return $out;
	}

	/** The one block named $name; null when there is none. @throws PageFault when there are two or more */
	public static function one( ?string $text, string $name ): ?string {
		$all = self::extract( $text, $name );
		if ( count( $all ) > 1 ) {
			throw new PageFault( 'the page carries ' . count( $all ) . ' blocks ' . self::PREFIX . "$name where one is read" );
		}
		return $all[0] ?? null;
	}

	/**
	 * Every block on the page, [name, payload] in page order. Every pre tag on the page, opening or
	 * closing, in any case, must belong to a block of the form above.
	 *
	 * @throws PageFault
	 */
	public static function all( ?string $text ): array {
		if ( $text === null || $text === '' ) {
			return [];
		}
		if ( !mb_check_encoding( $text, 'UTF-8' ) ) {
			throw new PageFault( 'the page\'s text is not UTF-8' );
		}
		if ( strpos( $text, "\0" ) !== false ) {
			throw new PageFault( 'the page\'s text carries a NUL' );
		}
		$amb = self::find( $text, self::AMBIGUOUS, 0 );
		if ( $amb !== null ) {
			throw new PageFault( 'the page carries a comment or an unparsed tag at byte ' . $amb . ', which could hide or change a block' );
		}
		$out = [];
		$pos = 0;
		$len = strlen( $text );
		while ( true ) {
			$open = self::find( $text, self::OPEN, $pos );
			$close = self::find( $text, self::CLOSE, $pos );
			if ( $open === null && $close === null ) {
				break;
			}
			if ( $open === null || ( $close !== null && $close < $open ) ) {
				throw new PageFault( 'a block closes that was not opened, at byte ' . $close );
			}
			if ( preg_match( '/\G<pre class="pma-([a-z]+)">\n/', $text, $m, 0, $open ) !== 1 ) {
				throw new PageFault( 'a preformatted block at byte ' . $open . ' is not a named block: <pre class="pma-<name>"> and a line feed' );
			}
			$start = $open + strlen( $m[0] );
			$end = self::find( $text, self::CLOSE, $start );
			if ( $end === null ) {
				throw new PageFault( 'the block ' . self::PREFIX . $m[1] . ' at byte ' . $open . ' does not close' );
			}
			$inner = self::find( $text, self::OPEN, $start );
			if ( $inner !== null && $inner < $end ) {
				throw new PageFault( 'a block opens inside the block ' . self::PREFIX . $m[1] . ' at byte ' . $open );
			}
			if ( $end === $start || $text[$end - 1] !== "\n" || substr( $text, $end, 6 ) !== '</pre>' ) {
				throw new PageFault( 'the block ' . self::PREFIX . $m[1] . ' at byte ' . $open . ' does not end with a line feed and </pre>' );
			}
			$out[] = [ $m[1], substr( $text, $start, $end - 1 - $start ) ];
			$pos = $end + 6;
			if ( $pos > $len ) {
				break;
			}
		}
		return $out;
	}

	private static function name( string $name ): void {
		if ( preg_match( '/\A[a-z]+\z/', $name ) !== 1 ) {
			throw new PageFault( 'a block name is lower-case letters a to z: ' . PageTitles::show( $name ) );
		}
	}

	private static function payload( string $payload ): void {
		if ( !mb_check_encoding( $payload, 'UTF-8' ) ) {
			throw new PageFault( 'a block\'s payload is not UTF-8' );
		}
		if ( strpos( $payload, "\0" ) !== false ) {
			throw new PageFault( 'a block\'s payload carries a NUL' );
		}
		if ( self::find( $payload, self::OPEN, 0 ) !== null || self::find( $payload, self::CLOSE, 0 ) !== null
			|| self::find( $payload, self::AMBIGUOUS, 0 ) !== null ) {
			throw new PageFault( 'a block\'s payload carries a <pre> or </pre> tag, a comment or an unparsed tag, which would open, close or hide a block' );
		}
	}

	/** The byte offset of the first match of $pattern in $text from $from; null when absent. @throws PageFault when the match itself fails */
	private static function find( string $text, string $pattern, int $from ): ?int {
		$r = preg_match( $pattern, $text, $m, PREG_OFFSET_CAPTURE, $from );
		if ( $r === false ) {
			throw new PageFault( 'the page could not be searched (' . preg_last_error_msg() . '); it is refused' );
		}
		return $r === 1 ? $m[0][1] : null;
	}
}
