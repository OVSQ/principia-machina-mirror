<?php
/**
 * PageRef: what a page title names, as PageTitles::classify reads it. Its page class is one of
 * PageClass::WORDS, or null when the title names none. "governed" is true for every title in the
 * territory Custos keeps (the restricted namespace, every page under the UWC root, the reserved
 * pages under the Declarer's root): a governed title with no class is one Custos refuses, never
 * one it allows. The other fields are the title's parts, null where the form has none.
 */

namespace Custos;

final class PageRef {
	public function __construct(
		public readonly ?string $class,
		public readonly bool $governed,
		public readonly bool $restricted,
		/** The UWC's record prefix, for a page under the UWC root. */
		public readonly ?string $prefix = null,
		/** The volume number of a register, bibliography, chain or ledger volume. */
		public readonly ?int $volume = null,
		/** The account a dossier or score page names. */
		public readonly ?string $account = null,
		/** A falcon's or a Provision's identifier; a snapshot's month; a zone's name. */
		public readonly ?string $part = null,
		/** A Provision's version. */
		public readonly ?string $version = null
	) {
	}

	/** Governed and in no class: Custos refuses every operation on it. */
	public function refused(): bool {
		return $this->governed && $this->class === null;
	}
}
