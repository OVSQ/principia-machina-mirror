<?php
/**
 * PageClass: the 40 page classes of the permissions table, by their wire words, in the order of
 * `PageClass` in Principia/Permissions.lean (the rows of version 1's TPS 5.13.2 that name a page,
 * in PMA's words). The Calculator's `permissions permits` takes these words; Custos only names
 * them. A page Custos governs but cannot place in one of them has no class, and is refused.
 */

namespace Custos;

final class PageClass {
	public const RESEARCH_ASSEMBLY = 'RESEARCH ASSEMBLY';
	public const DRAFT_UWC = 'DRAFT UWC';
	public const SPECIFICATION = 'SPECIFICATION';
	public const IMPLEMENTATION = 'IMPLEMENTATION';
	public const CALCULATOR_SOURCE = 'CALCULATOR SOURCE';
	public const ACCESS_LIST = 'ACCESS LIST';
	public const CANARY_FAILURE_DETAIL = 'CANARY FAILURE DETAIL';
	public const SCORE_OR_USER_PAGE = 'SCORE OR USER PAGE';
	public const OVERRIDE_DETAIL = 'OVERRIDE DETAIL';
	public const PROMPT_MANIFEST = 'PROMPT MANIFEST';
	public const CONFIGURATION_STRATA = 'CONFIGURATION STRATA';
	public const COMMUNITY_LEDGER = 'COMMUNITY LEDGER';
	public const DOSSIER = 'DOSSIER';
	public const OVERRIDE_DECLARATION = 'OVERRIDE DECLARATION';
	public const SCORECARD = 'SCORECARD';
	public const DECLARATIONS_VOLUME = 'DECLARATIONS VOLUME';
	public const BUILD_CHAIN_VOLUME = 'BUILD CHAIN VOLUME';
	public const CHAIN_HEAD = 'CHAIN HEAD';
	public const DECLARATION_OUTSIDE_D_IS = 'DECLARATION OUTSIDE D_IS';
	public const TOP_PERFORMER = 'TOP PERFORMER';
	public const FALCON_PAGE = 'FALCON PAGE';
	public const FALCON_LOG = 'FALCON LOG';
	public const FALCON_RESTRICTED = 'FALCON RESTRICTED';
	public const PROVISION = 'PROVISION';
	public const PROPOSAL = 'PROPOSAL';
	public const CANDIDATE_CERTIFICATE = 'CANDIDATE CERTIFICATE';
	public const INDEX_AND_BADGE = 'INDEX AND BADGE';
	public const SPINE = 'SPINE';
	public const HUB_FRAME = 'HUB FRAME';
	public const AGENT_HELP = 'AGENT HELP';
	public const REGISTER_OPEN = 'REGISTER OPEN';
	public const REGISTER_FROZEN = 'REGISTER FROZEN';
	public const BIBLIOGRAPHY_OPEN = 'BIBLIOGRAPHY OPEN';
	public const BIBLIOGRAPHY_FROZEN = 'BIBLIOGRAPHY FROZEN';
	public const STAGING = 'STAGING';
	public const COLLABORATION = 'COLLABORATION';
	public const LOCK_PAGE = 'LOCK PAGE';
	public const CONTROL_PANEL = 'CONTROL PANEL';
	public const SYNTHETIC_CONTAINER = 'SYNTHETIC CONTAINER';
	public const RETIRED_CONTAINER = 'RETIRED CONTAINER';

	/** Every wire word, in the Lean enumeration's order. */
	public const WORDS = [
		self::RESEARCH_ASSEMBLY, self::DRAFT_UWC, self::SPECIFICATION, self::IMPLEMENTATION,
		self::CALCULATOR_SOURCE, self::ACCESS_LIST, self::CANARY_FAILURE_DETAIL, self::SCORE_OR_USER_PAGE,
		self::OVERRIDE_DETAIL, self::PROMPT_MANIFEST, self::CONFIGURATION_STRATA, self::COMMUNITY_LEDGER,
		self::DOSSIER, self::OVERRIDE_DECLARATION, self::SCORECARD, self::DECLARATIONS_VOLUME,
		self::BUILD_CHAIN_VOLUME, self::CHAIN_HEAD, self::DECLARATION_OUTSIDE_D_IS, self::TOP_PERFORMER,
		self::FALCON_PAGE, self::FALCON_LOG, self::FALCON_RESTRICTED, self::PROVISION, self::PROPOSAL,
		self::CANDIDATE_CERTIFICATE, self::INDEX_AND_BADGE, self::SPINE, self::HUB_FRAME, self::AGENT_HELP,
		self::REGISTER_OPEN, self::REGISTER_FROZEN, self::BIBLIOGRAPHY_OPEN, self::BIBLIOGRAPHY_FROZEN,
		self::STAGING, self::COLLABORATION, self::LOCK_PAGE, self::CONTROL_PANEL, self::SYNTHETIC_CONTAINER,
		self::RETIRED_CONTAINER,
	];

	/**
	 * The classes whose pages lie in the restricted namespace: exactly the rows the Public does
	 * not read (`restricted_iff` in Principia/Permissions.lean).
	 */
	public const RESTRICTED = [
		self::CANARY_FAILURE_DETAIL, self::SCORE_OR_USER_PAGE, self::OVERRIDE_DETAIL, self::PROMPT_MANIFEST,
		self::FALCON_RESTRICTED,
	];

	public static function isWord( string $word ): bool {
		return in_array( $word, self::WORDS, true );
	}

	public static function isRestricted( string $word ): bool {
		return in_array( $word, self::RESTRICTED, true );
	}
}
