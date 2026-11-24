<?php
/**
 * Assignments: the assignment block of a UWC's collaboration page, `pma-assignments`.
 *
 * The Holder writes the block: a JSON list of rows {"block", "assignee", "grant", "kind", "ends",
 * "range"} (docs/design/pma_custos_ops.md 4.4). `block()` builds its text, for the Holder's tools
 * and the tests. Custos reads it only through the Calculator, `hold assignments` with the block's
 * text, the Holder's account and the server clock: the rows, each LIVE or EXPIRED, or the block
 * refused with the Calculator's word (MALFORMED, TIME, HOLDER, DUPLICATE and the index of the
 * first bad row), or the call refused as a request. No PHP parses a row, a form or a time: this
 * class finds the block on the page (Blocks), hands its text over and compares the Calculator's
 * answer for the account and the block's name.
 *
 * `find()` answers a row, or one of the words the RETURN job will answer: NO ASSIGNMENT (no row
 * for the block), NOT ASSIGNEE (the row names another account), EXPIRED (the server clock is past
 * the row's end); a refused block answers the Calculator's word. The block's text lives here, not
 * in PageTexts, so this unit shares no file with the jobs' page texts.
 */

namespace Custos;

use JsonException;

final class Assignments {
	/** The block's name on the page: the class `pma-assignments`. */
	public const BLOCK = 'assignments';
	public const NO_ASSIGNMENT = 'NO ASSIGNMENT';
	public const NOT_ASSIGNEE = 'NOT ASSIGNEE';
	public const EXPIRED = 'EXPIRED';
	/** The members of a row, in the order the Holder writes them. */
	private const MEMBERS = [ 'block', 'assignee', 'grant', 'kind', 'ends', 'range' ];

	/**
	 * The block's text for $rows (each an array of the six members): the `<pre class="pma-assignments">`
	 * block of Blocks, its payload one line of JSON. Which forms a row must take is the Calculator's
	 * to say when the block is read; this writes what it is given, and refuses only what is no row.
	 *
	 * @throws PageFault a row lacks a member or carries another, or the text cannot be written
	 */
	public static function block( array $rows ): string {
		if ( !array_is_list( $rows ) ) {
			throw new PageFault( 'the assignments are a list of rows' );
		}
		foreach ( $rows as $i => $row ) {
			if ( !is_array( $row ) || !self::sameMembers( $row ) ) {
				throw new PageFault( "assignment row $i is not an object with the members " . implode( ', ', self::MEMBERS ) );
			}
		}
		try {
			$payload = json_encode( $rows, JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_THROW_ON_ERROR );
		} catch ( JsonException $e ) {
			throw new PageFault( 'the assignments cannot be written as JSON' );
		}
		return Blocks::render( self::BLOCK, $payload );
	}

	/**
	 * What the collaboration page's assignment block says at server time $now, for the Holder $holder:
	 *   ["rows" => [["account", "block", "ends", "kind", "state"], ...]]   state LIVE or EXPIRED, the page's order
	 *   ["refused" => the word, "index" => the first bad row or null]      the block refused
	 *   ["refused" => the code, "detail" => the sentence, "index" => null]  the call refused as a request
	 * A page without the block has no rows. $pageText null is no page.
	 *
	 * @throws PageFault the page's blocks are not in the form of Blocks, or there are two assignment blocks
	 * @throws CalculatorFault the call could not be made or its answer is outside the protocol
	 * @throws UnsafeResidence
	 * @throws DigestMismatch
	 */
	public static function read( Calculator $calc, ?string $pageText, string $holder, string $now ): array {
		$text = Blocks::one( $pageText, self::BLOCK );
		if ( $text === null ) {
			return [ 'rows' => [] ];
		}
		$request = json_encode( [ 'text' => $text, 'holder' => $holder, 'now' => $now ],
			JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_INVALID_UTF8_SUBSTITUTE );
		$a = $calc->call( 'hold', 'assignments', (string)$request );
		if ( $a['exit'] !== 0 ) {
			return [ 'refused' => $a['refused'], 'detail' => $a['detail'], 'index' => null ];
		}
		$v = $a['value'];
		if ( is_array( $v ) && ( $v[0] ?? null ) === 'OK' && is_array( $v[1] ?? null ) && count( $v ) === 2 ) {
			return [ 'rows' => $v[1] ];
		}
		if ( is_array( $v ) && ( $v[0] ?? null ) === 'REFUSED' && is_string( $v[1] ?? null ) && count( $v ) === 3
			&& ( $v[2] === null || is_int( $v[2] ) ) ) {
			return [ 'refused' => $v[1], 'index' => $v[2] ];
		}
		throw new CalculatorFault( 'pcalc hold assignments answered outside its form', CalculatorFault::ANSWER_FORM, 'hold', 'assignments' );
	}

	/**
	 * The row for $account and $block in the answer of read(), or the word that refuses it:
	 *   ["row" => ["account", "block", "ends", "kind", "state"]]
	 *   ["refused" => NO ASSIGNMENT | NOT ASSIGNEE | EXPIRED]
	 * or, when $read is a refusal, that refusal unchanged. The comparison is of two strings the
	 * Calculator wrote and the caller holds; nothing is parsed.
	 */
	public static function find( array $read, string $account, string $block ): array {
		if ( isset( $read['refused'] ) ) {
			return $read;
		}
		foreach ( $read['rows'] ?? [] as $row ) {
			if ( ( $row['block'] ?? null ) !== $block ) {
				continue;
			}
			if ( ( $row['account'] ?? null ) !== $account ) {
				return [ 'refused' => self::NOT_ASSIGNEE ];
			}
			return ( $row['state'] ?? null ) === 'LIVE' ? [ 'row' => $row ] : [ 'refused' => self::EXPIRED ];
		}
		return [ 'refused' => self::NO_ASSIGNMENT ];
	}

	private static function sameMembers( array $row ): bool {
		$k = array_keys( $row );
		sort( $k );
		$m = self::MEMBERS;
		sort( $m );
		return $k === $m;
	}
}
