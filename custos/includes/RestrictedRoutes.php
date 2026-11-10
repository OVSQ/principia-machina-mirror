<?php
/**
 * RestrictedRoutes: every route by which MediaWiki 1.46.2 hands out a page's text or title,
 * closed for the restricted pages, each by the hook or the setting MediaWiki provides for it.
 * The permission hook (PermissionHook) refuses a per-page read of a restricted page to all but
 * the Declarer's and the Operator's groups; these handlers close the routes that read a page
 * around that check.
 *
 * A restricted page: a title in the restricted namespace (its registered number,
 * $wgCustosRestrictedNamespace, and the next number, which the permission hook refuses for every
 * action), or a title PageTitles::classify reads as restricted (every page of a restricted class
 * lies in the namespace; a title classify cannot read exactly is restricted too, fail closed).
 * The per-page routes (transclusion, the parser's reads of another page, the link tables) test the
 * whole predicate; the list routes test the two namespace numbers, since every page of a
 * restricted class lies in the namespace.
 *
 * The routes and their handlers (custos/README.md, "Restricted routes", lists each with the
 * routes core already closes by its own read check through the permission hook):
 *   transclusion: $wgNonincludableNamespaces carries both numbers (onRegistration) and
 *     BeforeParserFetchTemplateRevisionRecord skips a restricted template, redirects included;
 *     the parser's reads of another page's revision ({{REVISIONID:}}, {{REVISIONUSER:}},
 *     {{REVISIONTIMESTAMP:}}, {{PAGESIZE:}} and the like) through ParserOptionsRegister, whose
 *     currentRevisionRecordCallback answers no revision for a restricted page. Refused to every
 *     reader, the Declarer and the Operator included: the parser cache is shared.
 *   search: the namespace not searchable (SearchableNamespaces, and false in
 *     $wgNamespacesToBeSearchedDefault); a hit on a restricted page never shown (ShowSearchHit), a
 *     suggestion never offered (ApiOpenSearchSuggest); the API's list=search and list=prefixsearch
 *     by the scrub below. A search text naming the namespace by its prefix, or every namespace by
 *     "all:" (the database search reads either without the searchable namespaces' filter), is
 *     refused: Special:Search (SpecialPageBeforeExecute), the API's srsearch, pssearch and search
 *     (ApiCheckCanExecute), and the REST API's /v1/search/page and /v1/search/title
 *     (RestCheckCanExecute; its handler runs neither ShowSearchHit nor ApiOpenSearchSuggest and
 *     names a redirect's own title beside its target); the REST API's sitemap routes refused whole
 *     (RestCheckCanExecute).
 *   export: Special:Export and the API's export read-check each page (core); every export
 *     outside the command line also leaves the namespace out of its query (ModifyExportQuery),
 *     so exportall never carries it. The Operator's dumpBackup on the host keeps it.
 *   the API's query results: a request naming a restricted namespace in any parameter ending
 *     in "namespace", or a restricted page by a revision or page id (revids, oldid, fromrev, torev,
 *     pageids, pageid, fromid, toid, curid), is refused (ApiCheckCanExecute,
 *     apierror-custos-restricted-route); every
 *     result of action=query is scrubbed of each item naming a restricted title (APIAfterExecute):
 *     prop=revisions and its metadata, list=allpages, list=allrevisions, list=recentchanges,
 *     list=usercontribs, list=logevents, list=search, list=prefixsearch, and every other list
 *     and generator.
 *   the change lists: Special:RecentChanges, RecentChangesLinked, Watchlist and their feeds
 *     (ChangesListSpecialPageQuery, which also leaves out every move into the namespace: its row
 *     carries the source's namespace and the target only in its parameters), Special:NewPages
 *     (SpecialNewpagesConditions),
 *     Special:Contributions and its feed (ContribsPager::getQueryInfo), Special:Log
 *     (LogEventsListLineEnding: the line emptied), each leaving the namespace out.
 *   the title lists: Special:AllPages and Special:PrefixIndex refused for a restricted namespace
 *     (SpecialPageBeforeExecute) and the namespace left out of PrefixIndex's query
 *     (SpecialPrefixIndexQuery); Special:Random, RandomRedirect and RandomRootPage refused for a
 *     subpage naming it (SpecialPageBeforeExecute) and the namespace left out of their query
 *     (RandomPageQuery); Special:ListRedirects, BrokenRedirects, DoubleRedirects and
 *     UnwatchedPages refused whole (they list every namespace and offer no hook);
 *     Special:ProtectedPages and ProtectedTitles refused unless a public namespace is chosen.
 *   the link tables: a restricted page's links, categories, templates and properties never
 *     recorded (RevisionDataUpdates drops its LinksUpdate), so WhatLinksHere, the category
 *     pages, Special:PagesWithProp and the API's backlinks, categorymembers, alllinks and
 *     pageswithprop never name it. The redirect table is written outside LinksUpdate (WikiPage),
 *     so Special:WhatLinksHere leaves the namespace out of each of its queries
 *     (SpecialWhatLinksHereQuery), its redirects included.
 * Every list route refuses every reader, the Declarer and the Operator included: a list may be
 * transcluded ({{Special:RecentChanges}}) into the shared parser cache, and a feed is cached
 * whole. The Declarer and the Operator read a restricted page by its own title (view, raw,
 * render, history, diffs, action=parse), each through the permission hook.
 * The permission hook's own refusal of a restricted page names no title (PermissionHook::refusal):
 * index.php's oldid=, diff= and curid= would otherwise hand the title out by its id.
 * A handler that cannot read its configuration refuses (fail closed).
 */

namespace Custos;

use MediaWiki\Config\Config;
use MediaWiki\MediaWikiServices;
use Throwable;

final class RestrictedRoutes {
	/** The message of a refused title list (Special:AllPages, Special:PrefixIndex). */
	public const REFUSED = 'custos-restricted-route';
	/** The API's refusal of a request naming a restricted namespace. */
	public const API_REFUSED = 'apierror-custos-restricted-route';
	/** The title lists refused for a restricted namespace, by their canonical names. */
	public const TITLE_LISTS = [ 'Allpages', 'Prefixindex' ];
	/**
	 * The random pages (SpecialRandomPage and its subclasses), refused when the subpage names the
	 * namespace: their subpage is a namespace name or a comma list of them, and any namespace serves.
	 */
	public const RANDOM_LISTS = [ 'Randompage', 'Randomredirect', 'Randomrootpage' ];
	/**
	 * The query pages that list every namespace and offer no hook to leave one out (MediaWiki 1.46.2):
	 * refused whole, to every reader. ListRedirects reads the page table's redirect flag,
	 * BrokenRedirects and DoubleRedirects the redirect table, Unwatchedpages every namespace but 8.
	 */
	public const REFUSED_LISTS = [ 'Listredirects', 'BrokenRedirects', 'DoubleRedirects', 'Unwatchedpages' ];
	/** The pagers that list every namespace unless one is chosen: refused unless a public one is. */
	public const NAMESPACE_LISTS = [ 'Protectedpages', 'Protectedtitles' ];
	/** Special:Search: refused when its text names the namespace by its prefix, or every namespace by "all:". */
	public const SEARCH_PAGES = [ 'Search' ];
	/** The API's parameters that carry a search text (list=search, list=prefixsearch, action=opensearch). */
	public const SEARCH_PARAMS = [ 'srsearch', 'gsrsearch', 'pssearch', 'gpssearch', 'search' ];
	/** Core's message of the keyword that searches every namespace (not Custos's own). */
	public const SEARCH_ALL = 'searchall';
	/** The REST API's refusal of a search naming a restricted namespace or every namespace. */
	public const REST_REFUSED = 'A search naming the restricted namespace, or every namespace, is refused.';
	/** The namespace column of each table a list's query may read. */
	public const NAMESPACE_COLUMNS = [
		'page' => 'page_namespace',
		'recentchanges' => 'rc_namespace',
		'archive' => 'ar_namespace',
		'logging' => 'log_namespace',
		'watchlist' => 'wl_namespace',
	];
	/** The keys of an API result item that carry a title. */
	public const TITLE_KEYS = [ 'title', 'to', 'from', 'target_title', 'fromtitle', 'totitle' ];
	/** LinksUpdate, which writes a page's link tables. */
	public const LINKS_UPDATE = 'MediaWiki\\Deferred\\LinksUpdate\\LinksUpdate';

	/** @var callable|null the currentRevisionRecordCallback this one wraps */
	private static $innerFetch = null;

	/**
	 * @param ?\Closure $restrictedProbe fn( $title ): bool, else isRestricted (the harness's seam)
	 * @param ?\Closure $redirectProbe fn( $title ): ?LinkTarget, a page's redirect target, else MediaWiki's RedirectLookup
	 * @param ?\Closure $readProbe fn( $user, $title ): bool, else PermissionManager::userCan( 'read', RIGOR_SECURE )
	 */
	public function __construct(
		private Config $config,
		private ?\Closure $restrictedProbe = null,
		private ?\Closure $redirectProbe = null,
		private ?\Closure $readProbe = null
	) {
	}

	// ---- the pure part, which the harness tests ---------------------------------------------

	/** The two numbers: the restricted namespace's and the next, refused for every action. */
	public static function numbers( int $ns ): array {
		return [ $ns, $ns + 1 ];
	}

	/** A title is restricted: in either number, or read as restricted by classify. */
	public static function restrictedTitle( PageTitles $titles, int $namespace, string $prefixed, int $ns ): bool {
		if ( in_array( $namespace, self::numbers( $ns ), true ) ) {
			return true;
		}
		$ref = $titles->classify( $prefixed );
		return $ref->restricted || ( $ref->class !== null && PageClass::isRestricted( $ref->class ) );
	}

	/**
	 * A text names a restricted title: its namespace prefix (before the first colon, after a
	 * leading one, spaces and underscores folded, in any case) is one of $names.
	 */
	public static function namesRestricted( string $text, array $names ): bool {
		$t = ltrim( str_replace( '_', ' ', $text ), " \t" );
		if ( str_starts_with( $t, ':' ) ) {
			$t = substr( $t, 1 );
		}
		$colon = strpos( $t, ':' );
		if ( $colon === false ) {
			return false;
		}
		$prefix = trim( (string)preg_replace( '/\s+/u', ' ', substr( $t, 0, $colon ) ) );
		foreach ( $names as $name ) {
			if ( $name !== '' && strcasecmp( $prefix, str_replace( '_', ' ', $name ) ) === 0 ) {
				return true;
			}
		}
		return false;
	}

	/**
	 * A subpage names the namespace as the random pages read it: the whole subpage, or one part of a
	 * comma list, is one of $names (spaces and underscores folded, any case, spaces around ignored).
	 */
	public static function subpageNamesNamespace( ?string $par, array $names ): bool {
		if ( $par === null ) {
			return false;
		}
		foreach ( array_merge( [ $par ], explode( ',', $par ) ) as $part ) {
			$p = trim( str_replace( '_', ' ', $part ) );
			foreach ( $names as $name ) {
				if ( $name !== '' && strcasecmp( $p, trim( str_replace( '_', ' ', $name ) ) ) === 0 ) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * A search text reaches a restricted page: it names the namespace by its prefix (namesRestricted),
	 * or every namespace by a keyword of $allWords ("all", and the wiki's own word) and a colon, in any
	 * case, after spaces. MediaWiki's database search reads such a prefix without the searchable
	 * namespaces' filter (SearchDatabase::extractNamespacePrefix), and "all:" searches every namespace.
	 */
	public static function searchNamesRestricted( string $q, array $names, array $allWords ): bool {
		if ( self::namesRestricted( $q, $names ) ) {
			return true;
		}
		$t = strtolower( ltrim( str_replace( '_', ' ', $q ), " \t" ) );
		foreach ( $allWords as $w ) {
			if ( is_string( $w ) && $w !== '' && str_starts_with( $t, strtolower( trim( $w ) ) . ':' ) ) {
				return true;
			}
		}
		return false;
	}

	/**
	 * A special page refused for the restricted pages, given its canonical name, its subpage and the
	 * request's values: the title lists for a restricted namespace (by number, or by the prefix of the
	 * subpage, from, to or prefix), the random pages for a subpage naming it, the lists of every
	 * namespace without a hook (REFUSED_LISTS) always, the protected pages and titles unless a public
	 * namespace is chosen, Special:Search for a text reaching it. No numbers read: each of them refused.
	 */
	public static function specialRefused( string $name, ?string $subPage, array $request, array $numbers, array $names, array $allWords ): bool {
		$val = static fn ( string $k ) => is_string( $request[$k] ?? null ) ? $request[$k] : null;
		$governed = array_merge( self::TITLE_LISTS, self::RANDOM_LISTS, self::REFUSED_LISTS, self::NAMESPACE_LISTS, self::SEARCH_PAGES );
		if ( !in_array( $name, $governed, true ) ) {
			return false;
		}
		if ( $numbers === [] || in_array( $name, self::REFUSED_LISTS, true ) ) {
			return true;
		}
		if ( in_array( $name, self::TITLE_LISTS, true ) ) {
			if ( in_array( self::integer( $val( 'namespace' ) ?? '0' ), $numbers, true ) ) {
				return true;
			}
			foreach ( [ $subPage, $val( 'from' ), $val( 'to' ), $val( 'prefix' ) ] as $t ) {
				if ( is_string( $t ) && self::namesRestricted( $t, $names ) ) {
					return true;
				}
			}
			return false;
		}
		if ( in_array( $name, self::RANDOM_LISTS, true ) ) {
			return self::subpageNamesNamespace( $subPage, $names );
		}
		if ( in_array( $name, self::NAMESPACE_LISTS, true ) ) {
			$ns = self::integer( $val( 'namespace' ) );
			return $ns === null || in_array( $ns, $numbers, true );
		}
		foreach ( [ $subPage, $val( 'search' ), $val( 'prefix' ) ] as $t ) {
			if ( is_string( $t ) && self::searchNamesRestricted( $t, $names, $allWords ) ) {
				return true;
			}
		}
		return false;
	}

	/**
	 * The condition that leaves out of the change lists every move whose target is restricted: a row of
	 * the log type "move" (its rc_namespace is the source's) whose parameters carry a name of the
	 * namespace and a colon. $like gives the SQL of "LIKE '%<text>%'" for a text (Database::buildLike);
	 * $q the table's alias and a dot. No names read: every move row left out (fail closed).
	 */
	public static function moveExclusion( array $names, callable $like, string $q = '' ): string {
		$patterns = [];
		foreach ( $names as $name ) {
			if ( !is_string( $name ) || $name === '' ) {
				continue;
			}
			foreach ( [ $name, str_replace( ' ', '_', $name ), str_replace( '_', ' ', $name ) ] as $n ) {
				$patterns[$n . ':'] = true;
			}
		}
		$base = "{$q}rc_log_type IS NULL OR {$q}rc_log_type <> 'move'";
		if ( $patterns === [] ) {
			return "($base)";
		}
		$likes = array_map( static fn ( string $p ) => "{$q}rc_params" . $like( $p ), array_keys( $patterns ) );
		return "($base OR NOT (" . implode( ' OR ', $likes ) . '))';
	}

	/** A REST route's kind by its handler or its path: "search", "sitemap", or null (untouched). */
	public static function restKind( string $path, bool $searchHandler = false, bool $sitemapHandler = false ): ?string {
		if ( $sitemapHandler || preg_match( '#/sitemap(/|$)#', $path ) === 1 ) {
			return 'sitemap';
		}
		if ( $searchHandler || preg_match( '#/search(/|$)#', $path ) === 1 ) {
			return 'search';
		}
		return null;
	}

	/** A REST route of $kind refused: a sitemap always, a search whose text $q reaches a restricted page; no numbers read refuses. */
	public static function restRefused( ?string $kind, mixed $q, array $numbers, array $names, array $allWords ): bool {
		if ( $kind === null ) {
			return false;
		}
		if ( $numbers === [] || $kind === 'sitemap' || !is_string( $q ) ) {
			return true;
		}
		return self::searchNamesRestricted( $q, $names, $allWords );
	}

	/** An integer written as the API reads one (signs, zeros and spaces around), else null. */
	public static function integer( mixed $v ): ?int {
		if ( is_int( $v ) ) {
			return $v;
		}
		if ( is_string( $v ) && preg_match( '/^\s*\+?0*(\d{1,9})\s*$/', $v, $m ) ) {
			return (int)$m[1];
		}
		return null;
	}

	/**
	 * A request's parameters name a restricted namespace: a parameter whose name ends in
	 * "namespace" (any module prefix) carries one of $numbers among its values ("|", or the
	 * API's U+001F form). "*" (every namespace) is not refused: its results are scrubbed.
	 */
	public static function requestNamesRestricted( array $params, array $numbers ): bool {
		foreach ( $params as $name => $value ) {
			if ( !is_string( $name ) || !str_ends_with( strtolower( $name ), 'namespace' ) ) {
				continue;
			}
			$values = is_array( $value ) ? $value : [ $value ];
			foreach ( $values as $v ) {
				if ( !is_string( $v ) && !is_int( $v ) ) {
					continue;
				}
				$v = (string)$v;
				$parts = str_starts_with( $v, "\x1f" ) ? explode( "\x1f", substr( $v, 1 ) ) : explode( '|', $v );
				foreach ( $parts as $p ) {
					if ( in_array( self::integer( $p ), $numbers, true ) ) {
						return true;
					}
				}
			}
		}
		return false;
	}

	/** The API's parameters that name a revision by its id, and a page by its id. */
	public const REVISION_ID_PARAMS = [ 'revids', 'oldid', 'fromrev', 'torev' ];
	public const PAGE_ID_PARAMS = [ 'pageids', 'pageid', 'fromid', 'toid', 'curid' ];

	/**
	 * The revision ids and the page ids a request names (REVISION_ID_PARAMS, PAGE_ID_PARAMS),
	 * each read as the API reads an integer, at most $cap of each (the rest refused by the caller).
	 *
	 * @return array{0: int[], 1: int[], 2: bool} the revision ids, the page ids, more than $cap named
	 */
	public static function ids( array $params, int $cap = 500 ): array {
		$out = [ [], [] ];
		$over = false;
		foreach ( [ self::REVISION_ID_PARAMS, self::PAGE_ID_PARAMS ] as $i => $names ) {
			foreach ( $names as $name ) {
				$v = $params[$name] ?? null;
				if ( !is_string( $v ) && !is_int( $v ) ) {
					continue;
				}
				$v = (string)$v;
				foreach ( str_starts_with( $v, "\x1f" ) ? explode( "\x1f", substr( $v, 1 ) ) : explode( '|', $v ) as $p ) {
					$n = self::integer( $p );
					if ( $n !== null && $n > 0 && !in_array( $n, $out[$i], true ) ) {
						$out[$i][] = $n;
					}
				}
			}
			if ( count( $out[$i] ) > $cap ) {
				$over = true;
				$out[$i] = array_slice( $out[$i], 0, $cap );
			}
		}
		return [ $out[0], $out[1], $over ];
	}

	/** An API result item names a restricted title: its "ns" (or "<x>_ns") or a title key. */
	public static function itemRestricted( array $item, array $numbers, array $names ): bool {
		foreach ( $item as $k => $v ) {
			if ( !is_string( $k ) ) {
				continue;
			}
			if ( ( $k === 'ns' || str_ends_with( $k, '_ns' ) ) && in_array( self::integer( $v ), $numbers, true ) ) {
				return true;
			}
			if ( in_array( $k, self::TITLE_KEYS, true ) && is_string( $v ) && self::namesRestricted( $v, $names ) ) {
				return true;
			}
			if ( ( $k === 'params' || $k === 'logparams' ) && is_array( $v ) && self::itemRestricted( $v, $numbers, $names ) ) {
				// a log entry whose parameters name a restricted title (a move into the namespace)
				return true;
			}
		}
		return false;
	}

	/**
	 * The API result with every item naming a restricted title removed, at any depth; a list
	 * (its keys other than the result's metadata, those starting "_", were 0 to n-1) renumbered.
	 */
	public static function scrub( array $data, array $numbers, array $names ): array {
		$keys = array_values( array_filter( array_keys( $data ), static fn ( $k ) => !is_string( $k ) || !str_starts_with( $k, '_' ) ) );
		$list = $keys === array_keys( $keys );
		$removed = false;
		foreach ( $data as $k => $v ) {
			if ( !is_array( $v ) ) {
				continue;
			}
			if ( self::itemRestricted( $v, $numbers, $names ) ) {
				unset( $data[$k] );
				$removed = true;
			} else {
				$data[$k] = self::scrub( $v, $numbers, $names );
			}
		}
		if ( !$list || !$removed ) {
			return $data;
		}
		$out = [];
		foreach ( $data as $k => $v ) {
			if ( is_int( $k ) ) {
				$out[] = $v;
			}
		}
		foreach ( $data as $k => $v ) {
			if ( !is_int( $k ) ) {
				$out[$k] = $v;
			}
		}
		return $out;
	}

	/**
	 * The conditions that leave the restricted namespace out of a query over $tables (alias =>
	 * table, or a list of tables): one per table with a namespace column. A query with none of
	 * them gets a condition no row meets (fail closed).
	 */
	public static function exclusions( array $tables, array $numbers ): array {
		if ( $numbers === [] ) {
			return [ '1 = 0' ];
		}
		$in = implode( ',', array_map( 'intval', $numbers ) );
		$out = [];
		foreach ( $tables as $alias => $table ) {
			if ( !is_string( $table ) || !isset( self::NAMESPACE_COLUMNS[$table] ) ) {
				continue;
			}
			$q = is_string( $alias ) ? $alias . '.' : '';
			$out[] = $q . self::NAMESPACE_COLUMNS[$table] . " NOT IN ($in)";
		}
		return $out === [] ? [ '1 = 0' ] : $out;
	}

	/** The searchable namespaces without either number. */
	public static function searchable( array $arr, array $numbers ): array {
		foreach ( $numbers as $n ) {
			unset( $arr[$n] );
		}
		return $arr;
	}

	/** A restricted page's secondary updates without its LinksUpdate (by class, $class). */
	public static function keepUpdates( array $updates, bool $restricted, string $class = self::LINKS_UPDATE ): array {
		if ( !$restricted ) {
			return $updates;
		}
		return array_values( array_filter( $updates, static fn ( $u ) => !( $u instanceof $class ) ) );
	}

	/**
	 * The settings the routes need, given the globals: both numbers in NonincludableNamespaces,
	 * both false in NamespacesToBeSearchedDefault; what the Operator set kept.
	 */
	public static function settings( array $globals, int $ns ): array {
		$non = is_array( $globals['wgNonincludableNamespaces'] ?? null ) ? $globals['wgNonincludableNamespaces'] : [];
		$search = is_array( $globals['wgNamespacesToBeSearchedDefault'] ?? null ) ? $globals['wgNamespacesToBeSearchedDefault'] : [];
		foreach ( self::numbers( $ns ) as $n ) {
			if ( !in_array( $n, $non, true ) ) {
				$non[] = $n;
			}
			$search[$n] = false;
		}
		return [ 'wgNonincludableNamespaces' => $non, 'wgNamespacesToBeSearchedDefault' => $search ];
	}

	/** A revision fetch that answers false for a restricted title and asks $inner otherwise. */
	public static function fetcher( callable $inner, callable $restricted ): callable {
		return static fn ( $link, $parser = null ) => $restricted( $link ) ? false : $inner( $link, $parser );
	}

	// ---- MediaWiki's side --------------------------------------------------------------------

	/** extension.json's callback: the settings, before any service reads them. */
	public static function onRegistration(): void {
		$ns = self::integer( $GLOBALS['wgCustosRestrictedNamespace'] ?? null ) ?? PageTitles::RESTRICTED_NUMBER;
		foreach ( self::settings( $GLOBALS, $ns ) as $k => $v ) {
			$GLOBALS[$k] = $v;
		}
	}

	private function ns(): int {
		$ns = self::integer( $this->config->get( 'CustosRestrictedNamespace' ) );
		if ( $ns === null ) {
			throw new \UnexpectedValueException( 'CustosRestrictedNamespace' );
		}
		return $ns;
	}

	/** The names a title's prefix may give the namespace: its name and every alias of it. */
	private function names(): array {
		$ns = $this->ns();
		$names = [ PageTitles::RESTRICTED_NAMESPACE ];
		$lang = MediaWikiServices::getInstance()->getContentLanguage();
		$name = $lang->getNsText( $ns );
		if ( is_string( $name ) && $name !== '' ) {
			$names[] = $name;
		}
		foreach ( $lang->getNamespaceIds() as $alias => $id ) {
			if ( in_array( (int)$id, self::numbers( $ns ), true ) ) {
				$names[] = (string)$alias;
			}
		}
		return array_values( array_unique( $names ) );
	}

	/** A LinkTarget or PageReference is restricted; a fault reads it restricted (fail closed). */
	public function isRestricted( $link ): bool {
		try {
			$text = MediaWikiServices::getInstance()->getTitleFormatter()->getPrefixedText( $link );
			return self::restrictedTitle( PageTitles::fromConfig( $this->config ), (int)$link->getNamespace(), $text, $this->ns() );
		} catch ( Throwable ) {
			return true;
		}
	}

	/** The two numbers, or none when the configuration cannot be read: every caller then refuses. */
	private function numbersOrNone(): array {
		try {
			return self::numbers( $this->ns() );
		} catch ( Throwable ) {
			return [];
		}
	}

	/**
	 * The HTTP status of index.php's answer for a title: 403 for a restricted page the asker may not
	 * read, else null (MediaWiki's own). MediaWiki 1.46.2 renders the permission hook's refusal of a
	 * read (ActionEntryPoint, PermissionsError) as an error page answered 200, which a cache, a
	 * crawler or an agent's client takes for the page; the refusal is answered 403 instead, the same
	 * for every restricted title, so the status tells no existing page from an absent one.
	 */
	public static function refusedStatus( bool $restricted, bool $readable ): ?int {
		return $restricted && !$readable ? 403 : null;
	}

	/**
	 * index.php follows a page's redirect (ActionEntryPoint::initializeArticle): the view and
	 * action=render, not of an old revision or a diff, unless redirect=no.
	 */
	public static function followsRedirect( string $action, ?string $redirect, bool $oldOrDiff = false ): bool {
		return in_array( $action, [ 'view', 'render' ], true ) && $redirect !== 'no' && !$oldOrDiff;
	}

	/**
	 * BeforeInitialize (index.php, before its own read check): answers 403 for a restricted page the
	 * asker may not read, and for the view of a page whose redirect index.php would follow to one
	 * (followsRedirect, refusedStatus); the read is asked of MediaWiki as its check asks it, through the permission
	 * hook. A fault in any of the three questions answers 403 (fail closed); the refusal itself stays
	 * core's.
	 */
	public function onBeforeInitialize( $title, $unused, $output, $user, $request, $mediaWiki ): void {
		if ( $title === null ) {
			return;
		}
		$status = $this->viewStatus( $title, $user, (string)$request->getVal( 'action', 'view' ), $request->getVal( 'redirect' ),
			$request->getVal( 'oldid' ) !== null || $request->getVal( 'diff' ) !== null );
		if ( $status !== null ) {
			$output->setStatusCode( $status );
		}
	}

	/** onBeforeInitialize's status for a title, an asker, the action and the redirect parameter. */
	public function viewStatus( $title, $user, string $action, ?string $redirect, bool $oldOrDiff = false ): ?int {
		$asked = $title;
		try {
			$restricted = $this->restrictedProbe !== null ? (bool)( $this->restrictedProbe )( $title ) : $this->isRestricted( $title );
			if ( !$restricted && self::followsRedirect( $action, $redirect, $oldOrDiff ) ) {
				$target = $this->redirectProbe !== null ? ( $this->redirectProbe )( $title ) : self::redirectTarget( $title );
				if ( $target !== null ) {
					$restricted = $this->restrictedProbe !== null ? (bool)( $this->restrictedProbe )( $target ) : $this->isRestricted( $target );
					$asked = $target;
				}
			}
		} catch ( Throwable ) {
			return self::refusedStatus( true, false );
		}
		if ( !$restricted ) {
			return null;
		}
		try {
			$readable = $this->readProbe !== null ? (bool)( $this->readProbe )( $user, $asked ) : self::canRead( $user, $asked );
		} catch ( Throwable ) {
			$readable = false;
		}
		return self::refusedStatus( true, $readable );
	}

	/** A page's redirect target, or null: a title that cannot exist or does not, or no redirect. */
	private static function redirectTarget( $title ) {
		if ( !$title->canExist() || !$title->exists() ) {
			return null;
		}
		return MediaWikiServices::getInstance()->getRedirectLookup()->getRedirectTarget( $title );
	}

	/** MediaWiki's read check, as index.php asks it. */
	private static function canRead( $user, $link ): bool {
		$title = \MediaWiki\Title\Title::newFromLinkTarget( $link );
		return MediaWikiServices::getInstance()->getPermissionManager()
			->userCan( 'read', $user, $title, \MediaWiki\Permissions\PermissionManager::RIGOR_SECURE );
	}

	/** BeforeParserFetchTemplateRevisionRecord: a restricted template is never fetched. */
	public function onBeforeParserFetchTemplateRevisionRecord( $contextTitle, $title, &$skip, &$revRecord ) {
		if ( $this->isRestricted( $title ) ) {
			$skip = true;
			$revRecord = null;
			return false;
		}
		return true;
	}

	/** ParserOptionsRegister: the parser's read of another page's revision refused for a restricted one. */
	public function onParserOptionsRegister( &$defaults, &$inCacheKey, &$lazyLoad ) {
		$current = $defaults['currentRevisionRecordCallback'] ?? null;
		if ( $current !== [ self::class, 'fetchRevision' ] ) {
			self::$innerFetch = $current ?? [ \MediaWiki\Parser\Parser::class, 'statelessFetchRevisionRecord' ];
		}
		$defaults['currentRevisionRecordCallback'] = [ self::class, 'fetchRevision' ];
	}

	/** The parser's currentRevisionRecordCallback: no revision for a restricted page. */
	public static function fetchRevision( $link, $parser = null ) {
		$self = new self( MediaWikiServices::getInstance()->getMainConfig() );
		$inner = self::$innerFetch ?? [ \MediaWiki\Parser\Parser::class, 'statelessFetchRevisionRecord' ];
		return self::fetcher( $inner, [ $self, 'isRestricted' ] )( $link, $parser );
	}

	/** SearchableNamespaces: the namespace is not searchable. */
	public function onSearchableNamespaces( &$arr ) {
		$n = $this->numbersOrNone();
		if ( $n === [] ) {
			$arr = [];
			return;
		}
		$arr = self::searchable( $arr, $n );
	}

	/** ShowSearchHit: a hit on a restricted page shows nothing (a prefix such as "all:" reaches it). */
	public function onShowSearchHit( $searchPage, $result, $terms, &$link, &$redirect, &$section, &$extract,
		&$score, &$size, &$date, &$related, &$html
	) {
		$title = $result->getTitle();
		if ( $title === null || $this->isRestricted( $title ) ) {
			$html = '';
			return false;
		}
		return true;
	}

	/** ApiOpenSearchSuggest: no suggestion names a restricted page. */
	public function onApiOpenSearchSuggest( &$results ) {
		foreach ( $results as $k => $r ) {
			foreach ( [ 'title', 'redirect from' ] as $key ) {
				if ( isset( $r[$key] ) && is_object( $r[$key] ) && $this->isRestricted( $r[$key] ) ) {
					unset( $results[$k] );
					continue 2;
				}
			}
		}
	}

	/**
	 * ApiCheckCanExecute: a request naming a restricted namespace, or a revision or a page of a
	 * restricted page by its id, is refused before any module answers (a module's own refusal,
	 * such as prop=revisions' "cannot view", would name the title).
	 */
	public function onApiCheckCanExecute( $module, $user, &$message ) {
		$params = $module->getMain()->getRequest()->getValues();
		$n = $this->numbersOrNone();
		if ( $n === [] || self::requestNamesRestricted( $params, $n ) || $this->idsRestricted( $params )
			|| $this->searchTextRestricted( $params ) ) {
			$message = self::API_REFUSED;
			return false;
		}
		return true;
	}

	/** A search text of the request (SEARCH_PARAMS) reaches a restricted page. */
	private function searchTextRestricted( array $params ): bool {
		foreach ( self::SEARCH_PARAMS as $k ) {
			if ( is_string( $params[$k] ?? null ) && self::searchNamesRestricted( $params[$k], $this->safeNames(), $this->allWords() ) ) {
				return true;
			}
		}
		return false;
	}

	/** The keywords MediaWiki's search reads as every namespace: "all" and the wiki's own (searchall). */
	private function allWords(): array {
		$words = [ 'all' ];
		try {
			$words[] = wfMessage( self::SEARCH_ALL )->inContentLanguage()->text();
		} catch ( Throwable ) {
		}
		return $words;
	}

	/**
	 * RestCheckCanExecute: the REST API's search (/v1/search/page, /v1/search/title) refused when its
	 * text names the namespace by its prefix or every namespace by "all:". Its handler never calls
	 * ApiOpenSearchSuggest or ShowSearchHit, and it answers a redirect's target with the redirect's own
	 * title (matched_title), read-checking the target only. The sitemap routes (/site/v1/sitemap/...,
	 * off unless $wgSitemapApiConfig enables them) refused whole: they list every namespace the robot
	 * policies index, and any by include_namespace, with no read check.
	 */
	public function onRestCheckCanExecute( $module, $handler, $path, $request, &$error ) {
		$kind = self::restKind( (string)$path,
			$handler instanceof \MediaWiki\Rest\Handler\SearchHandler, $handler instanceof \MediaWiki\Rest\Handler\SitemapHandlerBase );
		if ( $kind === null ) {
			return true;
		}
		$q = $request->getQueryParams()['q'] ?? '';
		if ( self::restRefused( $kind, $q, $this->numbersOrNone(), $this->safeNames(), $this->allWords() ) ) {
			$error = new \MediaWiki\Rest\HttpException( self::REST_REFUSED, 403 );
			return false;
		}
		return true;
	}

	/** The request names a restricted page by a revision id or a page id; a fault reads it so. */
	private function idsRestricted( array $params ): bool {
		[ $revs, $pages, $over ] = self::ids( $params );
		if ( $revs === [] && $pages === [] ) {
			return false;
		}
		try {
			$services = MediaWikiServices::getInstance();
			$lookup = $services->getRevisionLookup();
			$store = $services->getPageStore();
			$titles = $services->getTitleFactory();
			foreach ( $revs as $id ) {
				$rev = $lookup->getRevisionById( $id );
				if ( $rev !== null && $this->isRestricted( $titles->newFromPageIdentity( $rev->getPage() ) ) ) {
					return true;
				}
			}
			foreach ( $pages as $id ) {
				$page = $store->getPageById( $id );
				if ( $page !== null && $this->isRestricted( $titles->newFromPageIdentity( $page ) ) ) {
					return true;
				}
			}
			return $over;
		} catch ( Throwable ) {
			return true;
		}
	}

	/** APIAfterExecute: action=query's result carries no restricted title. */
	public function onAPIAfterExecute( $module ) {
		if ( !$module instanceof \MediaWiki\Api\ApiQuery ) {
			return;
		}
		$result = $module->getResult();
		$query = $result->getResultData( [ 'query' ] );
		if ( !is_array( $query ) ) {
			return;
		}
		$n = $this->numbersOrNone();
		$clean = $n === [] ? [] : self::scrub( $query, $n, $this->safeNames() );
		if ( $clean !== $query ) {
			$result->removeValue( [], 'query', \MediaWiki\Api\ApiResult::NO_SIZE_CHECK );
			$result->addValue( [], 'query', $clean, \MediaWiki\Api\ApiResult::NO_VALIDATE );
		}
	}

	private function safeNames(): array {
		try {
			return $this->names();
		} catch ( Throwable ) {
			return [ PageTitles::RESTRICTED_NAMESPACE ];
		}
	}

	/**
	 * ChangesListSpecialPageQuery: RecentChanges, RecentChangesLinked, Watchlist and their feeds; the
	 * namespace left out, and every move into it (its row carries the source's namespace).
	 */
	public function onChangesListSpecialPageQuery( $name, &$tables, &$fields, &$conds, &$query_options, &$join_conds, $opts ) {
		$conds = array_merge( (array)$conds, self::exclusions( (array)$tables, $this->numbersOrNone() ) );
		foreach ( (array)$tables as $alias => $table ) {
			if ( $table !== 'recentchanges' ) {
				continue;
			}
			try {
				$dbr = MediaWikiServices::getInstance()->getConnectionProvider()->getReplicaDatabase();
				$like = static fn ( string $p ) => $dbr->buildLike( $dbr->anyString(), $p, $dbr->anyString() );
				$conds[] = self::moveExclusion( $this->names(), $like, is_string( $alias ) ? $alias . '.' : '' );
			} catch ( Throwable ) {
				$conds[] = '1 = 0';
			}
		}
	}

	/** RandomPageQuery: the random pages' query leaves the namespace out (any namespace list they read). */
	public function onRandomPageQuery( &$tables, &$conds, &$joinConds ) {
		$conds = array_merge( (array)$conds, self::exclusions( (array)$tables, $this->numbersOrNone() ) );
	}

	/**
	 * SpecialWhatLinksHereQuery: Special:WhatLinksHere never lists a restricted page, a redirect
	 * included (the redirect table is written outside LinksUpdate), nor a stale link row of a page
	 * moved into the namespace.
	 */
	public function onSpecialWhatLinksHereQuery( $table, $data, $queryBuilder ) {
		foreach ( self::exclusions( [ 'page' ], $this->numbersOrNone() ) as $c ) {
			$queryBuilder->andWhere( $c );
		}
	}

	/** SpecialNewpagesConditions: Special:NewPages. */
	public function onSpecialNewpagesConditions( $special, $opts, &$conds, &$tables, &$fields, &$join_conds ) {
		$conds = array_merge( (array)$conds, self::exclusions( (array)$tables, $this->numbersOrNone() ) );
	}

	/** ContribsPager::getQueryInfo: Special:Contributions and the API's feedcontributions. */
	public function onContribsPager__getQueryInfo( $pager, &$queryInfo ) {
		$queryInfo['conds'] = array_merge( (array)( $queryInfo['conds'] ?? [] ),
			self::exclusions( (array)( $queryInfo['tables'] ?? [] ), $this->numbersOrNone() ) );
	}

	/** SpecialPrefixIndexQuery: the namespace left out of Special:PrefixIndex's query. */
	public function onSpecialPrefixIndexQuery( array $fieldData, $queryBuilder ) {
		foreach ( self::exclusions( [ 'page' ], $this->numbersOrNone() ) as $c ) {
			$queryBuilder->andWhere( $c );
		}
	}

	/**
	 * SpecialPageBeforeExecute: the special pages specialRefused names, refused for the restricted
	 * pages (AllPages, PrefixIndex, the random pages, the lists of every namespace, the protected
	 * pages and titles, Search).
	 */
	public function onSpecialPageBeforeExecute( $special, $subPage ) {
		$request = $special->getRequest();
		$values = [];
		foreach ( [ 'namespace', 'from', 'to', 'prefix', 'search' ] as $k ) {
			$v = $request->getVal( $k );
			if ( is_string( $v ) ) {
				$values[$k] = $v;
			}
		}
		$refused = self::specialRefused( (string)$special->getName(), is_string( $subPage ) ? $subPage : null, $values,
			$this->numbersOrNone(), $this->safeNames(), $this->allWords() );
		if ( $refused ) {
			$special->getOutput()->addWikiMsg( self::REFUSED );
			return false;
		}
		return true;
	}

	/** LogEventsListLineEnding: a log line about a restricted page shows nothing. */
	public function onLogEventsListLineEnding( $page, &$ret, $entry, &$classes, &$attribs ) {
		$target = $entry->getTarget();
		$params = $entry->getParameters();
		$moved = is_array( $params ) ? ( $params['4::target'] ?? $params[0] ?? null ) : null;
		if ( $this->isRestricted( $target ) || ( is_string( $moved ) && self::namesRestricted( $moved, $this->safeNames() ) ) ) {
			$ret = '';
			$attribs = [];
		}
	}

	/** ModifyExportQuery: an export outside the command line leaves the namespace out. */
	public function onModifyExportQuery( $db, &$tables, $cond, &$opts, &$join_conds, &$conds ) {
		if ( PHP_SAPI === 'cli' || PHP_SAPI === 'phpdbg' ) {
			return;
		}
		$conds = array_merge( (array)$conds, self::exclusions( (array)$tables, $this->numbersOrNone() ) );
	}

	/** RevisionDataUpdates: a restricted page's link tables are never written. */
	public function onRevisionDataUpdates( $title, $renderedRevision, &$updates ) {
		$updates = self::keepUpdates( $updates, $this->isRestricted( $title ) );
	}
}
