<?php
/**
 * wiring.php: the extension's wiring, version 1's W1-W12 restated for Custos, and W13.
 *
 *   php custos/tests/wiring.php                        W1-W17, without MediaWiki
 *   php maintenance/run.php <path>/custos/tests/wiring.php
 *                                                      W1-W17, then M1-M15 on that wiki
 *
 * The harness loads Custos's classes by its own autoloader; the wiki loads them through
 * extension.json. W1-W17 check that what the harness loads the wiki can load too, and that
 * the files keep the rules this unit set. M1-M15 check it on a wiki that ran
 * wfLoadExtension('Custos'): the extension, its classes, its configuration, the API module
 * and the job class registered, $wgJobRunRate 0, the store seam live as the system user
 * Custos, and the Calculator called through the shell framework with its digest checked.
 *
 *   W1  extension.json parses: name Custos, manifest_version 2, a version
 *   W2  every class and interface in includes/ is in namespace Custos, one per file named after it
 *   W3  AutoloadNamespaces maps Custos\ to includes/ and nothing else; AutoloadClasses names only
 *       the maintenance scripts Certify, Job, Land, SeedUwc and Ticket (maintenance/<name>.php)
 *   W4  every class extension.json names (APIModules, JobClasses, HookHandlers) is declared in includes/
 *   W5  every message the PHP and extension.json name is in en.json and qqq.json, which carry the same keys
 *   W6  every configuration key the PHP reads is declared in extension.json's config
 *   W7  the configuration's defaults: no Calculator path, no digest, no version; version 1's page roots
 *   W8  requires MediaWiki >= 1.46
 *   W9  README.md's front matter carries extension.json's version and the sentinel line
 *   W10 every PHP file under custos/ passes php -l
 *   W11 no PHP file under includes/ uses the word "hash" (the function hash_file aside) or "TPX"
 *   W12 the API module's code names no Calculator; the Calculator refuses a call outside the command line
 *   W13 the wiki's Calculator makes the live residence check: fromConfig passes no residence of its own,
 *       ResidenceCheck's roots are /opt and /usr, and no configuration key reaches it (D10)
 *   W14 the tables custos_ticket, custos_seat, custos_certificate, custos_job_run, custos_nonce, custos_meter, custos_budget and custos_traffic, each registered by the schema hook by its own name with its own
 *       SQL: sql/<table>.json with its columns, its generated SQL sql/<type>/<table>.sql; the hook only adds tables
 *   W15 the group pma-agent and its right custos-landing, the rights custos-landing and custos-role; CustosPollAfter 30, CustosMaxRequestBytes 1,048,576,
 *       CustosSweepAfter 600, CustosSeatLockSeconds 10 (Landing's default)
 *   W16 the op STRUCTURE_TEST and its job wired: a write op of Ops (so ApiPma posts it with a CSRF
 *       token, by the right custos-landing) taking the prefix alone; the job type custosStructureTest
 *       is Custos\StructureTestJob, pushed by LandJob after a PUSH lands, deduplicated
 *   W17 the restricted routes' hooks (RestrictedRoutes) under the handler "restricted", each spelled as MediaWiki 1.46.2
 *       runs it (hook names are case-sensitive), and the settings' callback onRegistration
 *   M1  the wiki loaded Custos at extension.json's version
 *   M2  every class of W2 autoloads on the wiki
 *   M3  the configuration reads back as LocalSettings set it (a path, a digest, a version)
 *   M4  action=pma is Custos\ApiPma
 *   M5  the job types custosLand and custosStructureTest are Custos\LandJob and Custos\StructureTestJob, made by
 *       the wiki's job factory, deduplicated
 *   M6  $wgJobRunRate is 0: no job runs inside a web request
 *   M7  MwStore live: put, get, exists, casPut, appendAs, the revisions Custos's
 *   M8  the Calculator through BoxedRunner: "calculator: version <v>, digest match", or
 *       "UNSAFE RESIDENCE" or "DIGEST MISMATCH" and exit 1; always the live check (rehearsal.sh
 *       places the binary under /opt, root's, and runs this as a user other than root)
 *   M9  DbTicketStore live on the table custos_ticket: create, get, answer once
 *   M10 the right custos-landing is the group pma-agent's alone
 *   M11 the hook getUserPermissionsErrors is registered (the permission hook, PermissionHook)
 *   M12 DbNonceStore live on the table custos_nonce: put, a second put replacing it, take once, then none
 *   M13 DbNonceStore, two takes of one row by two objects: one gets the nonce; the loser's delete,
 *       issued after the winner's (both having read the row), removes no row, so it gets none
 *   M14 the job types custosReaudit, custosCluster and custosRecheck are the batch classes, made by the job factory, deduplicated;
 *       CustosBatch reads as its defaults; DbJobRunStore live: start, finish once, get, last
 *   M15 the restricted routes live: their hooks registered, the namespace and the next number non-includable,
 *       not searched by default and not searchable, the parser's revision fetch RestrictedRoutes::fetchRevision
 *
 * Prints the log and "wiring: ALL PASS <n>/<n>"; exit 0 only then.
 */

declare( strict_types=1 );

require_once __DIR__ . '/bootstrap.php';

/** W1-W17: the files alone. */
function custos_wiring_files(): void {
	$dir = dirname( __DIR__ );
	$ext = json_decode( (string)file_get_contents( "$dir/extension.json" ), true );
	G::ok( is_array( $ext ) && ( $ext['name'] ?? '' ) === 'Custos' && ( $ext['manifest_version'] ?? 0 ) === 2
		&& is_string( $ext['version'] ?? null ) && $ext['version'] !== '', 'W1 extension.json parses: name Custos, manifest_version 2, a version' );
	$ext = is_array( $ext ) ? $ext : [];

	$declared = [];
	$bad = [];
	foreach ( glob( "$dir/includes/*.php" ) ?: [] as $f ) {
		$src = (string)file_get_contents( $f );
		$ns = preg_match( '/^namespace\s+([^;]+);/m', $src, $m ) ? $m[1] : '';
		preg_match_all( '/^\s*(?:final\s+|abstract\s+)?(?:class|interface|trait|enum)\s+([A-Za-z_][A-Za-z0-9_]*)/m', $src, $mm );
		if ( $ns !== 'Custos' || $mm[1] !== [ basename( $f, '.php' ) ] ) {
			$bad[] = basename( $f ) . " (namespace $ns; " . implode( ',', $mm[1] ) . ')';
		}
		foreach ( $mm[1] as $c ) {
			$declared["Custos\\$c"] = basename( $f );
		}
	}
	G::ok( $declared !== [] && $bad === [], 'W2 every class and interface in includes/ is in namespace Custos, one per file named after it ('
		. count( $declared ) . ')', implode( '; ', $bad ) );
	$scripts = [ 'Certify', 'Job', 'Land', 'SeedUwc', 'Ticket' ];
	$scriptsOk = true;
	foreach ( $scripts as $sc ) {
		$src = (string)@file_get_contents( "$dir/maintenance/$sc.php" );
		$scriptsOk = $scriptsOk && preg_match( '/^namespace Custos\\\\Maintenance;$/m', $src ) === 1
			&& preg_match( "/^final class $sc extends Maintenance /m", $src ) === 1
			&& substr( rtrim( $src ), -strlen( "return $sc::class;" ) ) === "return $sc::class;";
	}
	G::ok( ( $ext['AutoloadNamespaces'] ?? null ) === [ 'Custos\\' => 'includes/' ]
		&& ( $ext['AutoloadClasses'] ?? null ) === [ 'Custos\\Maintenance\\Certify' => 'maintenance/Certify.php', 'Custos\\Maintenance\\Job' => 'maintenance/Job.php', 'Custos\\Maintenance\\Land' => 'maintenance/Land.php', 'Custos\\Maintenance\\SeedUwc' => 'maintenance/SeedUwc.php',
			'Custos\\Maintenance\\Ticket' => 'maintenance/Ticket.php' ]
		&& $scriptsOk,
		'W3 AutoloadNamespaces maps Custos\\ to includes/ and nothing else; AutoloadClasses names the maintenance scripts Certify, Job, Land, SeedUwc and Ticket, which their files declare and return' );
	$named = array_merge( array_values( $ext['APIModules'] ?? [] ), array_values( $ext['JobClasses'] ?? [] ),
		array_map( static fn ( $h ) => $h['class'] ?? '', array_values( $ext['HookHandlers'] ?? [] ) ) );
	$absent = array_values( array_filter( $named, static fn ( $c ) => !isset( $declared[$c] ) ) );
	G::ok( count( $named ) === 11 && $absent === [], 'W4 every class extension.json names (APIModules, JobClasses, HookHandlers) is declared in includes/ ('
		. count( $named ) . ')', implode( ', ', $absent ) );

	$en = json_decode( (string)file_get_contents( "$dir/i18n/en.json" ), true ) ?: [];
	$qqq = json_decode( (string)file_get_contents( "$dir/i18n/qqq.json" ), true ) ?: [];
	$keys = [ (string)( $ext['descriptionmsg'] ?? '' ) => 'extension.json' ];
	foreach ( array_keys( $ext['APIModules'] ?? [] ) as $api ) {
		$keys["apihelp-$api-summary"] = 'APIModules';
	}
	foreach ( glob( "$dir/includes/*.php" ) ?: [] as $f ) {
		preg_match_all( "/(?:->msg|wfMessage|Msg)\\(\\s*'([a-z][a-z0-9-]*)'/", (string)file_get_contents( $f ), $m );
		foreach ( $m[1] as $k ) {
			$keys[$k] = basename( $f );
		}
	}
	$missing = [];
	foreach ( $keys as $k => $where ) {
		if ( !isset( $en[$k] ) || !isset( $qqq[$k] ) ) {
			$missing[] = "$k ($where)";
		}
	}
	$enKeys = array_diff( array_keys( $en ), [ '@metadata' ] );
	$qqqKeys = array_diff( array_keys( $qqq ), [ '@metadata' ] );
	sort( $enKeys );
	sort( $qqqKeys );
	G::ok( $missing === [] && $enKeys === $qqqKeys, 'W5 every message named is in en.json and qqq.json, which carry the same keys ('
		. count( $keys ) . ')', implode( ', ', $missing ) . ' ' . implode( ',', array_diff( $enKeys, $qqqKeys ) ) );

	$config = $ext['config'] ?? [];
	$read = [];
	foreach ( glob( "$dir/includes/*.php" ) ?: [] as $f ) {
		preg_match_all( "/->get\\(\\s*'(Custos[A-Za-z]+)'\\s*\\)/", (string)file_get_contents( $f ), $m );
		foreach ( $m[1] as $k ) {
			$read[$k] = basename( $f );
		}
	}
	$undeclared = array_keys( array_diff_key( $read, $config ) );
	G::ok( $read !== [] && $undeclared === [], 'W6 every configuration key the PHP reads is declared in extension.json (' . count( $read ) . ')',
		implode( ', ', $undeclared ) );
	G::ok( ( $config['CustosCalculator']['value'] ?? null ) === ''
		&& ( $config['CustosBuild']['value'] ?? null ) === [ 'version' => '', 'digest' => '' ]
		&& ( $config['CustosUwcRoot']['value'] ?? null ) === 'Principia Machina/UWC'
		&& ( $config['CustosDeclRoot']['value'] ?? null ) === 'Principia Machina',
		'W7 the defaults: no Calculator path, no digest, no version; the roots "Principia Machina/UWC" and "Principia Machina"' );
	G::ok( ( $ext['requires']['MediaWiki'] ?? '' ) === '>= 1.46.0', 'W8 requires MediaWiki >= 1.46' );

	$readme = (string)file_get_contents( "$dir/README.md" );
	G::ok( preg_match( '/\A---\n(?:.*\n)*?version: ' . preg_quote( (string)( $ext['version'] ?? '-' ), '/' ) . '\n(?:.*\n)*?---\n/', $readme ) === 1
		&& substr( rtrim( $readme ), -strlen( 'END OF ARTIFACT --- README' ) ) === 'END OF ARTIFACT --- README',
		'W9 README.md carries extension.json\'s version in its front matter and ends with its sentinel' );

	$lint = [];
	$files = array_merge( glob( "$dir/includes/*.php" ) ?: [], glob( "$dir/maintenance/*.php" ) ?: [], glob( "$dir/tests/*.php" ) ?: [] );
	foreach ( $files as $f ) {
		exec( escapeshellarg( PHP_BINARY ) . ' -l ' . escapeshellarg( $f ) . ' 2>&1', $out, $code );
		if ( $code !== 0 ) {
			$lint[] = basename( $f );
		}
	}
	G::ok( $lint === [], 'W10 every PHP file under custos/ passes php -l (' . count( $files ) . ')', implode( ', ', $lint ) );

	$words = [];
	foreach ( glob( "$dir/includes/*.php" ) ?: [] as $f ) {
		$src = str_replace( 'hash_file(', '', (string)file_get_contents( $f ) );
		if ( preg_match( '/hash|\bTPX\b/i', $src, $m ) ) {
			$words[] = basename( $f ) . " ({$m[0]})";
		}
	}
	G::ok( $words === [], 'W11 no PHP file under includes/ says "hash" (hash_file aside) or "TPX"', implode( ', ', $words ) );

	$web = '';
	foreach ( token_get_all( (string)file_get_contents( "$dir/includes/ApiPma.php" ) ) as $tok ) {
		if ( !is_array( $tok ) || !in_array( $tok[0], [ T_COMMENT, T_DOC_COMMENT ], true ) ) {
			$web .= is_array( $tok ) ? $tok[1] : $tok;
		}
	}
	$calc = (string)file_get_contents( "$dir/includes/Calculator.php" );
	G::ok( !preg_match( '/Calculator|BoxedRunner|ShellRunner/', $web )
		&& strpos( $calc, "private const COMMAND_LINE = [ 'cli', 'phpdbg' ];" ) !== false,
		'W12 the API module\'s code names no Calculator; the Calculator refuses a call outside the command line' );

	$res = (string)file_get_contents( "$dir/includes/ResidenceCheck.php" );
	$reads = [];
	foreach ( array_merge( glob( "$dir/includes/*.php" ) ?: [], glob( "$dir/maintenance/*.php" ) ?: [] ) as $f ) {
		$src = (string)file_get_contents( $f );
		if ( preg_match( '/->get\(\s*\'Custos[A-Za-z]*Residen/', $src ) || preg_match( '/\bgetenv\s*\(|\$_ENV\b|\$_SERVER\b/', $src ) ) {
			$reads[] = basename( $f );
		}
	}
	G::ok( strpos( $calc, '$runner ?? new BoxedRunner(), PHP_SAPI, $residence );' ) !== false
		&& strpos( $calc, '$this->residence = $residence ?? new ResidenceCheck();' ) !== false
		&& strpos( $res, "public const ROOTS = [ '/opt', '/usr' ];" ) !== false
		&& strpos( $res, 'array $roots = self::ROOTS )' ) !== false && strpos( $res, '$owners' ) === false && $reads === [],
		'W13 the wiki\'s Calculator makes the live residence check: roots /opt and /usr, every property, no configuration key, no environment read',
		implode( ', ', $reads ) );

	// Each table registered by its own name with its own SQL, generated from its own abstract schema.
	$tables = [
		'custos_ticket' => [ 'DbTicketStore', [ 'ct_id', 'ct_op', 'ct_account', 'ct_prefix', 'ct_request', 'ct_state', 'ct_answer', 'ct_created', 'ct_done' ] ],
		'custos_seat' => [ 'DbSeatStore', [ 'cs_account', 'cs_kind', 'cs_level', 'cs_since' ] ],
		'custos_certificate' => [ 'DbCertificateStore', [ 'cc_agent', 'cc_sponsor', 'cc_d_is', 'cc_d_prompt', 'cc_family', 'cc_model', 'cc_state' ] ],
		'custos_job_run' => [ 'DbJobRunStore', [ 'cj_id', 'cj_job', 'cj_started', 'cj_done', 'cj_outcome', 'cj_detail', 'cj_counts' ] ],
		'custos_nonce' => [ 'DbNonceStore', [ 'cn_account', 'cn_prefix', 'cn_nonce', 'cn_issued' ] ],
		'custos_meter' => [ 'DbMeterStore', [ 'cm_id', 'cm_time', 'cm_account', 'cm_network', 'cm_op', 'cm_lane', 'cm_cpu', 'cm_wall', 'cm_memory',
			'cm_bytes', 'cm_landed', 'cm_weight' ], 'METER' ],
		'custos_budget' => [ 'DbMeterStore', [ 'cb_horizon', 'cb_use', 'cb_requests', 'cb_rolled', 'cb_level', 'cb_kept' ], 'BUDGET' ],
		'custos_traffic' => [ 'DbMeterStore', [ 'ctr_account', 'ctr_record', 'ctr_stage', 'ctr_time' ], 'TRAFFIC' ],
	];
	$bad = [];
	foreach ( $tables as $table => $spec ) {
		[ $store, $want ] = $spec;
		$const = $spec[2] ?? 'TABLE';
		$schema = json_decode( (string)@file_get_contents( "$dir/sql/$table.json" ), true );
		if ( !is_array( $schema ) || count( $schema ) !== 1 || ( $schema[0]['name'] ?? '' ) !== $table
			|| array_column( $schema[0]['columns'] ?? [], 'name' ) !== $want ) {
			$bad[] = "sql/$table.json";
		}
		foreach ( [ 'sqlite', 'mysql' ] as $type ) {
			$sql = (string)@file_get_contents( "$dir/sql/$type/$table.sql" );
			if ( !str_starts_with( $sql, "-- This file is automatically generated using maintenance/generateSchemaSql.php.\n-- Source: sql/$table.json\n" )
				|| substr_count( $sql, 'CREATE TABLE ' ) !== 1 || !str_contains( $sql, "CREATE TABLE /*_*/$table (" ) ) {
				$bad[] = "sql/$type/$table.sql";
			}
		}
		if ( strpos( (string)@file_get_contents( "$dir/includes/$store.php" ), "public const $const = '$table';" ) === false ) {
			$bad[] = "$store::$const";
		}
	}
	// The one source each: no schema file of two tables, no hand-made patch.
	$left = array_merge( glob( "$dir/sql/tables.json" ) ?: [], glob( "$dir/sql/*/tables-generated.sql" ) ?: [], glob( "$dir/sql/*/patch-*.sql" ) ?: [] );
	$hook = (string)@file_get_contents( "$dir/includes/SchemaHooks.php" );
	preg_match_all( '/\$updater->([A-Za-z]+)\(/', $hook, $calls );
	$hookOk = str_contains( $hook, 'public const TABLES = [ DbTicketStore::TABLE, DbSeatStore::TABLE, DbCertificateStore::TABLE, DbJobRunStore::TABLE, DbNonceStore::TABLE, DbMeterStore::METER, DbMeterStore::BUDGET, DbMeterStore::TRAFFIC ];' )
		&& str_contains( $hook, '$updater->addExtensionTable( $table, "$sql/$table.sql" );' ) && $calls[1] === [ 'getDB', 'addExtensionTable' ];
	G::ok( $bad === [] && $left === [] && $hookOk && ( $ext['Hooks']['LoadExtensionSchemaUpdates'] ?? '' ) === 'schema',
		'W14 the tables custos_ticket (nine columns), custos_seat (four), custos_certificate (seven), custos_job_run (seven), custos_nonce (four), custos_meter (twelve), custos_budget (six) and custos_traffic (four), each registered by the schema hook by its own name with its own SQL '
		. '(sql/<type>/<table>.sql for sqlite and mysql, generated from sql/<table>.json, its one source); the hook only adds tables',
		implode( ', ', array_merge( $bad, $left ) ) . ( $hookOk ? '' : ' (the hook)' ) );
	G::ok( ( $ext['GroupPermissions']['pma-agent']['custos-landing'] ?? false ) === true && ( $ext['AvailableRights'] ?? [] ) === [ 'custos-landing', 'custos-role' ]
		&& ( $config['CustosPollAfter']['value'] ?? null ) === 30 && ( $config['CustosMaxRequestBytes']['value'] ?? null ) === 1048576
		&& ( $config['CustosSweepAfter']['value'] ?? null ) === 600
		&& ( $config['CustosSeatLockSeconds']['value'] ?? null ) === 10 && \Custos\Landing::SEAT_LOCK_SECONDS === 10,
		'W15 the group pma-agent holds the right custos-landing (the rights: custos-landing and the marker custos-role); poll_after 30 s; records at most 1,048,576 bytes; the sweep after 600 s; the seat lock waited for 10 s' );
	$landJob = (string)@file_get_contents( "$dir/includes/LandJob.php" );
	$stJob = (string)@file_get_contents( "$dir/includes/StructureTestJob.php" );
	G::ok( in_array( 'STRUCTURE_TEST', \Custos\Ops::WRITE_OPS, true ) && in_array( 'STRUCTURE_TEST', \Custos\Ops::OPS, true )
		&& \Custos\Ops::PARAMS['STRUCTURE_TEST'] === [] && !isset( \Custos\Ops::REQUIRED['STRUCTURE_TEST'] )
		&& ( $ext['JobClasses']['custosStructureTest'] ?? null ) === 'Custos\\StructureTestJob' && str_contains( $stJob, "public const TYPE = 'custosStructureTest';" )
		&& str_contains( $stJob, '$this->removeDuplicates = true;' ) && str_contains( $landJob, "new StructureTestJob( [ 'prefix' => \$prefix ] )" ),
		'W16 the op STRUCTURE_TEST is a write op of Ops taking the prefix alone (ApiPma: a POST, a CSRF token, the right custos-landing); the job custosStructureTest is StructureTestJob, deduplicated, pushed by LandJob after a PUSH lands' );
	// The hook names are case-sensitive: each spelled as MediaWiki 1.46.2's HookRunner, ApiHookRunner and the REST API's HookRunner run it.
	$routes = [ 'BeforeParserFetchTemplateRevisionRecord', 'ParserOptionsRegister', 'SearchableNamespaces', 'ShowSearchHit',
		'ApiOpenSearchSuggest', 'ApiCheckCanExecute', 'APIAfterExecute', 'ChangesListSpecialPageQuery', 'SpecialNewpagesConditions',
		'ContribsPager::getQueryInfo', 'SpecialPrefixIndexQuery', 'SpecialPageBeforeExecute', 'LogEventsListLineEnding',
		'ModifyExportQuery', 'RevisionDataUpdates', 'RestCheckCanExecute', 'RandomPageQuery', 'SpecialWhatLinksHereQuery', 'BeforeInitialize' ];
	$wired = array_keys( array_filter( $ext['Hooks'] ?? [], static fn ( $h ) => in_array( 'restricted', (array)$h, true ) ) );
	sort( $routes );
	sort( $wired );
	G::ok( $wired === $routes && ( $ext['HookHandlers']['restricted']['class'] ?? '' ) === 'Custos\\RestrictedRoutes'
		&& ( $ext['HookHandlers']['restricted']['services'] ?? [] ) === [ 'MainConfig' ]
		&& ( $ext['callback'] ?? '' ) === 'Custos\\RestrictedRoutes::onRegistration',
		'W17 the restricted routes wired: the 19 hooks of RestrictedRoutes under the handler "restricted", each spelled as MediaWiki 1.46.2 runs it, and the settings\' callback',
		json_encode( array_values( array_diff( $wired, $routes ) + array_diff( $routes, $wired ) ) ) );
}

/** M1-M15: on the wiki that loaded Custos. */
function custos_wiring_wiki(): bool {
	$services = \MediaWiki\MediaWikiServices::getInstance();
	$config = $services->getMainConfig();
	$dir = dirname( __DIR__ );
	$ext = json_decode( (string)file_get_contents( "$dir/extension.json" ), true );
	$registry = \MediaWiki\Registration\ExtensionRegistry::getInstance();
	G::ok( $registry->isLoaded( 'Custos' ) && ( $registry->getAllThings()['Custos']['version'] ?? '' ) === $ext['version'],
		"M1 the wiki loaded Custos {$ext['version']}" );

	$classes = [];
	foreach ( glob( "$dir/includes/*.php" ) ?: [] as $f ) {
		$classes[] = 'Custos\\' . basename( $f, '.php' );
	}
	$unloaded = array_values( array_filter( $classes, static fn ( $c ) => !class_exists( $c ) && !interface_exists( $c ) ) );
	G::ok( $unloaded === [], 'M2 every class of includes/ autoloads on the wiki (' . count( $classes ) . ')', implode( ', ', $unloaded ) );

	$binary = (string)$config->get( 'CustosCalculator' );
	$expected = $config->get( 'CustosBuild' );
	G::ok( $binary !== '' && is_array( $expected ) && preg_match( '/^[0-9a-f]{64}$/', (string)( $expected['digest'] ?? '' ) ) === 1
		&& ( $expected['version'] ?? '' ) !== '' && $config->get( 'CustosUwcRoot' ) === 'Principia Machina/UWC',
		'M3 the configuration reads back: a Calculator path, a digest, a version, the roots' );
	G::ok( ( $config->get( 'APIModules' )['pma'] ?? null ) === 'Custos\\ApiPma', 'M4 action=pma is Custos\\ApiPma' );
	$job = $services->getJobFactory()->newJob( 'custosLand', [] );
	G::ok( ( $config->get( 'JobClasses' )['custosLand'] ?? null ) === 'Custos\\LandJob' && $job instanceof \Custos\LandJob && $job->ignoreDuplicates()
		&& is_int( $config->get( 'CustosSweepAfter' ) ),
		'M5 the job type custosLand is Custos\\LandJob, made by the job factory, deduplicated (removeDuplicates); CustosSweepAfter configured' );
	$stJob = $services->getJobFactory()->newJob( 'custosStructureTest', [ 'prefix' => 'WIRING' ] );
	G::ok( ( $config->get( 'JobClasses' )['custosStructureTest'] ?? null ) === 'Custos\\StructureTestJob' && $stJob instanceof \Custos\StructureTestJob
		&& $stJob->ignoreDuplicates(), 'M5 the job type custosStructureTest is Custos\\StructureTestJob, made by the job factory, deduplicated (one per UWC)' );
	G::ok( $config->get( 'JobRunRate' ) === 0 || $config->get( 'JobRunRate' ) === 0.0, 'M6 $wgJobRunRate is 0' );
	$batch = [ 'custosReaudit' => \Custos\ReauditJob::class, 'custosCluster' => \Custos\ClusterJob::class, 'custosRecheck' => \Custos\RecheckJob::class ];
	$bad = [];
	foreach ( $batch as $type => $class ) {
		$j = $services->getJobFactory()->newJob( $type, [] );
		if ( ( $config->get( 'JobClasses' )[$type] ?? null ) !== $class || !( $j instanceof $class ) || !$j->ignoreDuplicates() || $j->allowRetries() ) {
			$bad[] = $type;
		}
	}
	$runs = new \Custos\DbJobRunStore( $services->getConnectionProvider() );
	$rid = $runs->start( 'recheck', gmdate( 'YmdHis' ) );
	$open = $runs->get( $rid );
	$ended = $runs->finish( $rid, 'DONE', 'wiring M14', '{}', gmdate( 'YmdHis' ) ) && !$runs->finish( $rid, 'FAULT', 'again', '{}', gmdate( 'YmdHis' ) );
	$closed = $runs->get( $rid );
	G::ok( $bad === [] && $config->get( 'CustosBatch' ) === \Custos\BatchJob::DEFAULTS
		&& is_array( $open ) && $open['done'] === null && $open['outcome'] === null
		&& $ended && is_array( $closed ) && $closed['outcome'] === 'DONE' && $closed['detail'] === 'wiring M14' && $closed['counts'] === '{}'
		&& preg_match( '/\A[0-9]{14}\z/', (string)$closed['done'] ) === 1 && ( $runs->last( 'recheck' )['id'] ?? 0 ) === $rid && $runs->get( $rid + 1000000 ) === null,
		'M14 the three batch job types are the batch classes, deduplicated and not retried; CustosBatch reads as its defaults; DbJobRunStore live on custos_job_run: start, finish once, get, last',
		implode( ', ', $bad ) . json_encode( [ $open, $closed ] ) );

	$store = new \Custos\MwStore( $services );
	$t = $config->get( 'CustosUwcRoot' ) . '/WIRING/Store ' . gmdate( 'YmdHis' ) . '-' . getmypid();
	$fresh = $store->get( $t ) === null && !$store->exists( $t );
	$store->put( $t, 'one', 'Custos wiring M7' );
	$rev = $services->getRevisionLookup()->getRevisionByTitle( $services->getTitleFactory()->newFromText( $t ) );
	$firstId = $rev ? $rev->getId() : 0;
	$store->put( $t, 'one', 'Custos wiring M7, again' );
	$same = $services->getRevisionLookup()->getRevisionByTitle( $services->getTitleFactory()->newFromText( $t ) );
	$cas = $store->casPut( $t, 'not the text', 'two', 'Custos wiring M7', 'Custos' ) === false
		&& $store->casPut( $t, 'one', 'two', 'Custos wiring M7', 'Custos' ) === true;
	$appended = $store->appendAs( $t, 'three', 'Custos wiring M7', 'Custos' );
	G::ok( $fresh && $rev !== null && $rev->getUser() !== null && $rev->getUser()->getName() === \Custos\MwStore::SYSTEM_USER
		&& $same !== null && $same->getId() === $firstId && $cas && $appended === "two\nthree" && $store->get( $t ) === "two\nthree"
		&& $store->exists( $t ), 'M7 MwStore live: put as the system user Custos, no second save of the same text, casPut, appendAs' );

	$tickets = new \Custos\DbTicketStore( $services->getConnectionProvider() );
	$id = $tickets->create( 'PETITION', 'Custos wiring', 'WIRING', '{"prefix":"WIRING"}' );
	$row = $tickets->get( $id );
	$answered = $tickets->answer( $id, 'wiring M9' ) && !$tickets->answer( $id, 'again' );
	$done = $tickets->get( $id );
	G::ok( $id > 0 && is_array( $row ) && $row['state'] === 'QUEUED' && $row['request'] === '{"prefix":"WIRING"}' && $row['account'] === 'Custos wiring'
		&& $answered && is_array( $done ) && $done['state'] === 'DONE' && $done['answer'] === 'wiring M9' && preg_match( '/\A[0-9]{14}\z/', (string)$done['done'] ) === 1
		&& $tickets->get( $id + 1000000 ) === null,
		'M9 DbTicketStore live on the table custos_ticket: create, get, answer once (the wiring\'s ticket is answered, never left to a job)',
		json_encode( [ $row, $done ] ) );
	$perm = $services->getGroupPermissionsLookup();
	G::ok( $perm->groupHasPermission( 'pma-agent', 'custos-landing' ) && in_array( 'custos-landing', $services->getPermissionManager()->getAllPermissions(), true )
		&& !$perm->groupHasPermission( 'user', 'custos-landing' ) && !$perm->groupHasPermission( '*', 'custos-landing' ),
		'M10 the right custos-landing is the group pma-agent\'s alone' );
	G::ok( $services->getHookContainer()->isRegistered( 'getUserPermissionsErrors' )
		&& ( $services->getMainConfig()->get( 'CustosRoles' ) ?? null ) === \Custos\PermissionHook::DEFAULT_ROLES,
		'M11 the hook getUserPermissionsErrors is registered; CustosRoles reads as its defaults' );
	$nonces = new \Custos\DbNonceStore();
	$nonces->put( 'Custos wiring', 'WIRING', str_repeat( 'a', 32 ), 1 );
	$nonces->put( 'Custos wiring', 'WIRING', str_repeat( 'b', 32 ), 2 );
	$taken = $nonces->take( 'Custos wiring', 'WIRING' );
	G::ok( $taken === str_repeat( 'b', 32 ) && $nonces->take( 'Custos wiring', 'WIRING' ) === null,
		'M12 DbNonceStore live on the table custos_nonce: a put replaces the outstanding nonce, a take removes it, a second take finds none',
		(string)$taken );
	$nA = new \Custos\DbNonceStore();
	$nB = new \Custos\DbNonceStore();
	$nonce = str_repeat( 'd', 32 );
	$nA->put( 'Custos wiring', 'WIRING', $nonce, 3 );
	$dbw = $services->getDBLoadBalancer()->getConnection( \Wikimedia\Rdbms\ILoadBalancer::DB_PRIMARY, [], false,
		\Wikimedia\Rdbms\ILoadBalancer::CONN_TRX_AUTOCOMMIT );
	$where = [ 'cn_account' => 'Custos wiring', 'cn_prefix' => 'WIRING', 'cn_nonce' => $nonce ];
	$seenByB = $dbw->newSelectQueryBuilder()->select( 'cn_nonce' )->from( \Custos\DbNonceStore::TABLE )
		->where( $where )->caller( __FUNCTION__ )->fetchField();
	$wonA = $nA->take( 'Custos wiring', 'WIRING' );
	$dbw->newDeleteQueryBuilder()->deleteFrom( \Custos\DbNonceStore::TABLE )->where( $where )->caller( __FUNCTION__ )->execute();
	$lostB = $dbw->affectedRows();
	$wonB = $nB->take( 'Custos wiring', 'WIRING' );
	G::ok( $seenByB === $nonce && $wonA === $nonce && $lostB === 0 && $wonB === null,
		'M13 DbNonceStore, two takes of one row by two objects: one gets the nonce; the other, its read made before the winner\'s delete, deletes no row and gets none',
		json_encode( [ $seenByB, $wonA, $lostB, $wonB ] ) );
	$rn = (int)$config->get( 'CustosRestrictedNamespace' );
	$hooks = $services->getHookContainer();
	$defaults = \MediaWiki\Parser\ParserOptions::newFromAnon()->getCurrentRevisionRecordCallback();
	$searchable = $services->getSearchEngineConfig()->searchableNamespaces();
	G::ok( $hooks->isRegistered( 'BeforeParserFetchTemplateRevisionRecord' ) && $hooks->isRegistered( 'APIAfterExecute' )
		&& $hooks->isRegistered( 'RevisionDataUpdates' ) && $hooks->isRegistered( 'ContribsPager::getQueryInfo' )
		&& $services->getNamespaceInfo()->isNonincludable( $rn ) && $services->getNamespaceInfo()->isNonincludable( $rn + 1 )
		&& ( $config->get( 'NamespacesToBeSearchedDefault' )[$rn] ?? null ) === false
		&& !isset( $searchable[$rn] ) && !isset( $searchable[$rn + 1] ) && isset( $searchable[NS_MAIN] )
		&& $defaults === [ \Custos\RestrictedRoutes::class, 'fetchRevision' ],
		"M15 the restricted routes live: the hooks registered, the namespace $rn and the next non-includable and not searched, not searchable, the parser's revision fetch Custos's" );

	try {
		$c = \Custos\Calculator::fromConfig( $config );
		$version = $c->version();
		$r = $c->call( 'canonical', 'canonical_json', '{"value":{"b":1,"a":[2,3]}}' );
		G::ok( $r['exit'] === 0 && $r['value'] === '{"a":[2,3],"b":1}' && $c->starts === 2,
			"M8 the Calculator through the shell framework: version $version, one call answered, digest checked before each start",
			json_encode( $r ) );
		echo "calculator: version $version, digest match\n";
	} catch ( \Custos\UnsafeResidence $e ) {
		G::ok( false, 'M8 the Calculator through the shell framework', $e->getMessage() );
		echo $e->getMessage(), "\n";
		return false;
	} catch ( \Custos\DigestMismatch $e ) {
		G::ok( false, 'M8 the Calculator through the shell framework', $e->getMessage() );
		echo $e->getMessage(), "\n";
		return false;
	} catch ( \Throwable $e ) {
		G::ok( false, 'M8 the Calculator through the shell framework', get_class( $e ) . ': ' . $e->getMessage() );
	}
	return true;
}

if ( defined( 'RUN_MAINTENANCE_IF_MAIN' ) ) {
	if ( !class_exists( 'CustosWiring', false ) ) {
		/** The maintenance script maintenance/run.php runs. */
		final class CustosWiring extends \MediaWiki\Maintenance\Maintenance {
			public function __construct() {
				parent::__construct();
				$this->addDescription( 'Custos\'s wiring checks, W1-W17 and M1-M15, on this wiki' );
			}

			public function execute() {
				custos_wiring_files();
				custos_wiring_wiki();
				exit( G::report( 'wiring' ) );
			}
		}
	}
	return CustosWiring::class;
}

custos_wiring_files();
echo "(without MediaWiki: M1-M15 run under maintenance/run.php)\n";
exit( G::report( 'wiring' ) );
