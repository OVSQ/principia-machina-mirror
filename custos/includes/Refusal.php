<?php
/**
 * Refusal: an op of action=pma refused before anything is written. $what is the API error's
 * code, which opens "custos-"; the message says what was refused and carries no path;
 * scrub makes any message so before it reaches an answer.
 *
 * detail: every refusal the landing job writes to a ticket, which POLL shows the ticket's account.
 * A fault answers a fixed word and a detail drawn from a closed set (TABLE), never a path, a query,
 * a host name, a title's bytes or pcalc's stderr; the exception's class and message go to the
 * error channel (Landing's) and, where the job rethrows, to the job's setLastError.
 */

namespace Custos;

use RuntimeException;
use Throwable;

final class Refusal extends RuntimeException {
	/**
	 * The refusals a ticket is answered with, the first entry the exception matches: its word, and
	 * what its answer may say. The tests (harness.php, section F) read it.
	 */
	public const TABLE = [
		[ DigestMismatch::class, 'INTEGRITY HALT', 'detail: the words "digest mismatch" alone' ],
		[ UnsafeResidence::class, 'CALCULATOR FAULT', 'detail: "unsafe residence: " and the check that failed, one of UnsafeResidence::CHECKS' ],
		[ CalculatorFault::class, 'CALCULATOR FAULT', 'detail: the fault, one of CalculatorFault::FAULTS, then ": pcalc" and the call\'s family and function, each a word' ],
		[ PageFault::class, 'PAGE FAULT', 'detail: the page\'s class, one of PageClass::WORDS, then ": " (where known) and the fault, one of PageFault::FAULTS' ],
		[ LandRefused::class, null, 'its own word; detail: its sentence, written by Landing from the ticket\'s values and the Calculator\'s answer; the members it adds' ],
		[ Throwable::class, 'JOB FAULT', 'class: the exception\'s short class name, and no detail' ],
	];
	public const DIGEST_MISMATCH = 'digest mismatch';
	/** A family or function name, Calculator's form. */
	private const WORD = '/^[a-z][a-z0-9_]*$/';

	public string $what;

	public function __construct( string $what, string $message ) {
		parent::__construct( $message );
		$this->what = $what;
	}

	/**
	 * The members of a ticket's answer for the fault $e: "refused" (TABLE's word) and what TABLE lets
	 * it say. $page is the class of the page being read or written when a PageFault arose (null:
	 * not known), one of PageClass::WORDS or dropped.
	 */
	public static function detail( Throwable $e, ?string $page = null ): array {
		if ( $e instanceof DigestMismatch ) {
			return [ 'refused' => 'INTEGRITY HALT', 'detail' => self::DIGEST_MISMATCH ];
		}
		if ( $e instanceof UnsafeResidence ) {
			return [ 'refused' => 'CALCULATOR FAULT', 'detail' => 'unsafe residence: ' . $e->check() ];
		}
		if ( $e instanceof CalculatorFault ) {
			$fault = in_array( $e->fault, CalculatorFault::FAULTS, true ) ? $e->fault : CalculatorFault::ANSWER_FORM;
			$call = '';
			foreach ( [ $e->family, $e->function ] as $w ) {
				if ( preg_match( self::WORD, $w ) === 1 ) {
					$call .= ' ' . $w;
				}
			}
			return [ 'refused' => 'CALCULATOR FAULT', 'detail' => $call === '' ? $fault : "$fault: pcalc$call" ];
		}
		if ( $e instanceof PageFault ) {
			$fault = $e->fault();
			$known = $page !== null && PageClass::isWord( $page );
			return [ 'refused' => 'PAGE FAULT', 'detail' => $known ? "$page: $fault" : $fault ];
		}
		if ( $e instanceof LandRefused ) {
			return [ 'refused' => $e->word, 'detail' => mb_substr( $e->getMessage(), 0, 500 ) ] + $e->extra;
		}
		return [ 'refused' => 'JOB FAULT', 'class' => self::faultClass( $e ) ];
	}

	/** The exception's class name without its namespace, and without the file an anonymous class's name carries. */
	public static function faultClass( Throwable $e ): string {
		$name = explode( "\0", get_class( $e ), 2 )[0];
		$at = strrpos( $name, '\\' );
		return $at === false ? $name : substr( $name, $at + 1 );
	}

	/**
	 * A message with every file path cut to its last segment and every line number dropped.
	 * The known roots go first, literally, so a root with a space in it ("C:\Program Files\X")
	 * leaves nothing behind: MediaWiki's ($IP, MW_INSTALL_PATH), Custos's own folder, and any
	 * root the caller knows (the Calculator's residence, where the caller has it).
	 *
	 * @param string[] $roots
	 */
	public static function scrub( string $s, array $roots = [] ): string {
		$known = $roots;
		$known[] = dirname( __DIR__ );
		if ( defined( 'MW_INSTALL_PATH' ) ) {
			$known[] = (string)constant( 'MW_INSTALL_PATH' );
		}
		if ( isset( $GLOBALS['IP'] ) && is_string( $GLOBALS['IP'] ) ) {
			$known[] = $GLOBALS['IP'];
		}
		$cut = [];
		foreach ( $known as $r ) {
			$r = rtrim( (string)$r, '\\/' );
			if ( strlen( $r ) > 1 ) {
				$cut[] = $r;
				$cut[] = strtr( $r, '\\/', '/\\' );
			}
		}
		usort( $cut, static fn ( string $a, string $b ): int => strlen( $b ) <=> strlen( $a ) );
		$s = str_replace( $cut, '', $s );
		$s = preg_replace( '#(?:[A-Za-z]:)?(?:[\\\\/][^\\\\/\s:"\'()]+)+[\\\\/]([^\\\\/\s:"\'()]+)#', '$1', $s ) ?? '';
		$s = preg_replace( '/(?: on line|:) ?\d+\b/', '', $s ) ?? '';
		return mb_substr( $s, 0, 300 );
	}
}
