<?php
/**
 * PageFault: a page title or a page's blocks that Custos will not build or read: a title part
 * that is not one title segment, a block name or payload outside the content model, a page
 * whose blocks do not close or nest. Nothing is written or used from it.
 *
 * Its message (which may carry a title's bytes or a payload's) goes to the error channel only; the
 * ticket's answer says the page's class and fault(), one of FAULTS (Refusal::detail).
 */

namespace Custos;

use RuntimeException;

final class PageFault extends RuntimeException {
	/** The faults a ticket's answer may name, by the file that raised the fault. */
	public const BLOCK_FORM = 'block form';
	public const PAGE_TEXT = 'page text';
	public const TITLE_FORM = 'title form';
	public const BASE_MOVED = 'base moved';
	public const LANDING_ORDER = 'landing order';
	public const PAGE_STORE = 'page store';
	public const FAULTS = [ self::BLOCK_FORM, self::PAGE_TEXT, self::TITLE_FORM, self::BASE_MOVED, self::LANDING_ORDER, self::PAGE_STORE ];
	private const BY_FILE = [ 'Blocks' => self::BLOCK_FORM, 'PageTexts' => self::PAGE_TEXT, 'PageTitles' => self::TITLE_FORM,
		'PageWriter' => self::LANDING_ORDER ];

	/**
	 * The fault's name, one of FAULTS: what the file that raised it checks (a page store or any
	 * other file: PAGE_STORE), BASE MOVED the page writer's by the word its message opens with.
	 */
	public function fault(): string {
		$name = self::BY_FILE[basename( $this->getFile(), '.php' )] ?? self::PAGE_STORE;
		if ( $name === self::LANDING_ORDER && str_starts_with( $this->getMessage(), 'BASE MOVED' ) ) {
			return self::BASE_MOVED;
		}
		return $name;
	}
}
