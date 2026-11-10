<?php
/**
 * schema_tools.php: the autoloader of the libraries MediaWiki's generateSchemaSql needs and its
 * vendor tree leaves out (they are composer's require-dev: doctrine/dbal, doctrine/sql-formatter,
 * seld/jsonlint, with dbal's doctrine/deprecations and doctrine/event-manager). rehearsal.sh
 * clones each at the commit rehearsal.json pins into <scratch>/schema-tools and runs
 * `php -d auto_prepend_file=<this file> maintenance/run.php generateSchemaSql ...` with
 * CUSTOS_SCHEMA_TOOLS naming that folder. Command line only.
 */

if ( PHP_SAPI !== 'cli' ) {
	exit( 1 );
}

spl_autoload_register( static function ( string $class ): void {
	$top = getenv( 'CUSTOS_SCHEMA_TOOLS' );
	if ( !is_string( $top ) || $top === '' ) {
		return;
	}
	$map = [
		'Doctrine\\DBAL\\' => 'dbal/src/',
		'Doctrine\\SqlFormatter\\' => 'sql-formatter/src/',
		'Doctrine\\Deprecations\\' => 'deprecations/src/',
		'Doctrine\\Common\\' => 'event-manager/src/',
		'Seld\\JsonLint\\' => 'jsonlint/src/Seld/JsonLint/',
	];
	foreach ( $map as $prefix => $dir ) {
		if ( strncmp( $class, $prefix, strlen( $prefix ) ) === 0 ) {
			$file = "$top/$dir" . str_replace( '\\', '/', substr( $class, strlen( $prefix ) ) ) . '.php';
			if ( is_file( $file ) ) {
				require_once $file;
			}
			return;
		}
	}
} );
