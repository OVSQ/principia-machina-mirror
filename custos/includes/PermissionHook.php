<?php
/**
 * PermissionHook: the fence around the pages Custos governs, on MediaWiki's hook
 * getUserPermissionsErrors (MediaWiki 1.46: $title, $user, $action, &$result; false refuses).
 * It reads the permissions table (Permits, custos/permits.json, generated from `permits`
 * in Principia/Permissions.lean by the built Calculator) and admits nothing the table refuses.
 *
 * The title is read by PageTitles::classify; a title in the restricted namespace is read
 * through its registered number, $wgCustosRestrictedNamespace; it has no talk namespace, and
 * a title MediaWiki gives the next number (unregistered, nameless) is refused for every action.
 * Every title Custos does not govern is untouched. On a governed title:
 *   - one that does not classify is refused for every action and every account;
 *   - an action whose operation is WRITE (edit, create, createpage, createtalk) by the system
 *     user "Custos" is admitted: it is the landing job carrying a WRITE or APPEND THROUGH CUSTOS
 *     (the ticket's account is the job's check, not the hook's); every other action of the
 *     system user (delete, move, protect, upload, import among them) is asked as any account's;
 *   - every other request is mapped to one cell: the asker, the class, the operation, the
 *     context, and admitted only when the table permits it (Permits::admits). The asker: the
 *     Declarer's, the Operator's and the Contributor's groups of $wgCustosRoles, the Public for
 *     every account, and an account in the agent's group as an agent account in its lock state
 *     only (no user's role, the Contributor's included). The Contributor's cells are the
 *     Public's (Principia/Permissions.lean: the Contributor has no column), so its group adds
 *     nothing the Public is not permitted; the hook reads them from the table all the same,
 *     and the harness checks every one of them against the Public's. The operation
 *     (an allow-list, Op): edit, create, createpage, createtalk WRITE; protect PROTECT; read and
 *     the reviewed view rights (READ_ACTIONS) READ; every other action, a right an extension
 *     adds included, none (refused). The context: the title's named account (a score
 *     or dossier page naming the account asking), and REAUTHENTICATED from the session
 *     (MediaWiki's reauthentication: AuthManager::securitySensitiveOperationStatus, and only for a
 *     session that can set its user: a bot password's or OAuth's session, which MediaWiki answers
 *     SEC_OK by default without re-authenticating, is never REAUTHENTICATED).
 *   - A fact Custos reads from no page yet (the UWC's ACCESS POLICY and access list, the lock's
 *     state and queue head of the account, its DOSSIER READ setting, the Initiator of the UWC)
 *     is unknown: the request is admitted only when the table permits it under every value the
 *     fact may take, and an unknown role is not held. A fact outside a UWC has its one value
 *     (no policy, not listed).
 * Refusals: custos-governed-page for a write-class action and for any action on a page of a
 * public class, naming the title; custos-restricted-page for any other action on a restricted page
 * or a title in the restricted namespace, naming no title (refusal()). The facts a title cannot
 * carry (the UWC LIVE or RETIRED, the open register volume) are read from the UWC's INDEX AND
 * BADGE page (PageTexts::facts); an absent fact takes the reading that refuses, as classify does. A table or a configuration that
 * cannot be read refuses (fail closed).
 */

namespace Custos;

use MediaWiki\Auth\AuthManager;
use MediaWiki\Config\Config;
use MediaWiki\MediaWikiServices;
use MediaWiki\User\UserGroupManager;
use Throwable;

final class PermissionHook {
	public const GOVERNED = 'custos-governed-page';
	public const RESTRICTED = 'custos-restricted-page';
	/**
	 * The rights that only show a page: MediaWiki's read, and the reviewed rights that show its
	 * deleted history or text (MediaWiki 1.46.2). A right not listed here, WRITE's or PROTECT's
	 * is refused on a governed title: a right MediaWiki or an extension adds is a change until reviewed.
	 */
	public const READ_ACTIONS = [ 'read', 'deletedhistory', 'deletedtext' ];
	/** $wgCustosRoles's defaults: the group of each role's accounts. */
	public const DEFAULT_ROLES = [ 'declarer' => 'pma-declarer', 'operator' => 'pma-operator', 'agent' => 'pma-agent',
		'contributor' => 'pma-contributor' ];

	public function __construct(
		private Config $config,
		private UserGroupManager $groups
	) {
	}

	/** getUserPermissionsErrors */
	public function onGetUserPermissionsErrors( $title, $user, $action, &$result ) {
		$text = $title->getPrefixedText();
		try {
			$read = self::titleText( $title->getNamespace(), $title->getText(), $text,
				(int)$this->config->get( 'CustosRestrictedNamespace' ) );
			if ( $read === null ) {
				$result = self::refusal( self::RESTRICTED, $text );
				return false;
			}
			$text = $read;
			$titles = PageTitles::fromConfig( $this->config );
			$roles = $this->config->get( 'CustosRoles' );
			$store = new MwStore();
			$auth = MediaWikiServices::getInstance()->getAuthManager();
			$reauth = self::reauthenticated( $auth->getRequest()->getSession()->canSetUser(),
				$auth->securitySensitiveOperationStatus( 'custos-permits' ) === AuthManager::SEC_OK );
			$key = self::decide( $titles, $text, (string)$action, $user->getName(), $user->isSystemUser(),
				$this->groups->getUserEffectiveGroups( $user ), is_array( $roles ) ? $roles : [],
				static fn ( string $t ): ?string => $store->get( $t ), Permits::table(), [ 'reauth' => $reauth ] );
		} catch ( Throwable $e ) {
			// A configuration, a table or a store that cannot be read: nothing is admitted (fail closed).
			$key = self::GOVERNED;
		}
		if ( $key === null ) {
			return true;
		}
		$result = self::refusal( $key, $text );
		return false;
	}

	/**
	 * The refusal's message and its parameters: a restricted page's refusal names no title, since
	 * a reader who asked by a revision or a page id (oldid=, diff=, curid=, the API's revids) would
	 * learn the title from it; a governed page's names its title, which is public.
	 */
	public static function refusal( string $key, string $title ): array {
		return $key === self::RESTRICTED ? [ $key ] : [ $key, $title ];
	}

	/**
	 * The title as classify reads it: in the restricted namespace (its registered number $ns)
	 * "Restricted:<text>", else MediaWiki's own; null for the next number, the talk namespace
	 * MediaWiki would pair with it, registered by no one: refused for every action.
	 */
	public static function titleText( int $namespace, string $text, string $prefixed, int $ns ): ?string {
		if ( $namespace === $ns ) {
			return PageTitles::RESTRICTED_NAMESPACE . ':' . $text;
		}
		if ( $namespace === $ns + 1 ) {
			return null;
		}
		return $prefixed;
	}

	/**
	 * REAUTHENTICATED: the session can set its user (it is one a person logs in to, not a bot
	 * password's or OAuth's) and MediaWiki answers the operation SEC_OK ($secOk).
	 */
	public static function reauthenticated( bool $canSetUser, bool $secOk ): bool {
		return $canSetUser && $secOk;
	}

	/**
	 * The fence's answer: null (admitted) or the refusal's message key.
	 *
	 * @param bool $system the account is MediaWiki's system user (User::isSystemUser)
	 * @param string[] $groups the account's effective groups
	 * @param array $roles role => group; a role missing or not a string admits no one, and the agent
	 *   role missing or empty refuses every request on a governed title
	 * @param callable(string): ?string $read a page's text by title, read without a permission check
	 * @param array $known the facts known: "reauth" (bool; absent false); and, where a caller
	 *   knows them (the harness), "initiator" (bool), "lock" (null, HOLDER, COWORKER), "policy"
	 *   (null, OPEN, CLOSED), "listed" (bool), "dossier" (a DOSSIER READ word), "head" (bool).
	 *   Each fact absent is unknown and takes every value it may.
	 */
	public static function decide( PageTitles $titles, string $title, string $action, string $user, bool $system,
		array $groups, array $roles, callable $read, Permits $table, array $known = []
	): ?string {
		$ref = $titles->classify( $title );
		if ( !$ref->governed ) {
			return null;
		}
		if ( $ref->prefix !== null ) {
			$facts = PageTexts::facts( $read( $titles->index( $ref->prefix ) ) );
			$ref = $titles->classify( $title, $facts );
			if ( $ref->class === PageClass::REGISTER_FROZEN && $ref->volume !== null
				&& $ref->volume === ( $facts['open_volume'] ?? null ) ) {
				$ref = $titles->classify( $title, $facts + [ 'open' => true ] );
			}
		}
		$restricted = $ref->restricted || ( $ref->class !== null && PageClass::isRestricted( $ref->class ) );
		if ( $ref->refused() ) {
			return $restricted ? self::RESTRICTED : self::GOVERNED;
		}
		$op = self::op( $action );
		$refusal = ( $op !== 'READ' || !$restricted ) ? self::GOVERNED : self::RESTRICTED;
		$agentGroup = $roles['agent'] ?? null;
		if ( !is_string( $agentGroup ) || $agentGroup === '' ) {
			// No agent group configured: an agent account could not be told from a user and would
			// ask as the Public; a configuration error refuses (fail closed).
			return $refusal;
		}
		if ( $op === 'WRITE' && $system && $user === MwStore::SYSTEM_USER ) {
			return null;
		}
		if ( $op === null ) {
			return $refusal;
		}
		$askers = [ 'PUBLIC' ];
		foreach ( [ 'declarer' => 'DECLARER', 'operator' => 'OPERATOR', 'contributor' => 'CONTRIBUTOR' ] as $role => $word ) {
			if ( self::inRole( $groups, $roles, $role ) ) {
				$askers[] = $word;
			}
		}
		if ( ( $known['initiator'] ?? false ) === true ) {
			$askers[] = 'INITIATOR';
		}
		$agent = self::inRole( $groups, $roles, 'agent' );
		if ( $agent ) {
			// An agent account asks as an agent in its lock state, never in a user's role: the
			// Public's cells it holds are inside its own (a user's named read is not an agent's).
			$askers = [];
		}
		$uwc = $ref->prefix !== null;
		$named = $ref->account !== null && $ref->account === $user;
		$one = static fn ( string $k, array $all ) => array_key_exists( $k, $known ) ? [ $known[$k] ] : $all;
		$facts = [
			'lock' => $agent ? $one( 'lock', Permits::LOCK_STATES ) : [],
			'policy' => $uwc ? $one( 'policy', Permits::POLICIES ) : [ null ],
			'listed' => $uwc ? $one( 'listed', [ false, true ] ) : [ false ],
			'dossier' => $named ? $one( 'dossier', Permits::DOSSIER_READS ) : [ null ],
			'head' => $one( 'head', [ false, true ] ),
			'reauth' => [ ( $known['reauth'] ?? false ) === true ],
		];
		return $table->admits( $askers, $ref->class, $op, $facts ) ? null : $refusal;
	}

	/**
	 * The table's operation for a MediaWiki action (an allow-list); null: an action the table
	 * names no operation for, refused on a governed title.
	 */
	public static function op( string $action ): ?string {
		if ( in_array( $action, [ 'edit', 'create', 'createpage', 'createtalk' ], true ) ) {
			return 'WRITE';
		}
		if ( $action === 'protect' ) {
			return 'PROTECT';
		}
		return in_array( $action, self::READ_ACTIONS, true ) ? 'READ' : null;
	}

	private static function inRole( array $groups, array $roles, string $role ): bool {
		$g = $roles[$role] ?? null;
		return is_string( $g ) && $g !== '' && in_array( $g, $groups, true );
	}
}
