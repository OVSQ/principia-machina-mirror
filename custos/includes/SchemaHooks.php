<?php
/**
 * SchemaHooks: the hook LoadExtensionSchemaUpdates, which adds each of Custos's tables when
 * update.php runs on a wiki that lacks it: custos_ticket from sql/<type>/custos_ticket.sql,
 * custos_seat from sql/<type>/custos_seat.sql, custos_certificate from
 * sql/<type>/custos_certificate.sql, custos_job_run from sql/<type>/custos_job_run.sql and custos_nonce
 * (the execution challenge's nonces) from sql/<type>/custos_nonce.sql, each table registered by its own
 * name with its own SQL. A wiki installed before the seat table (custos_ticket alone) gains custos_seat,
 * custos_certificate, custos_job_run and custos_nonce on its next update, and one installed before the
 * certificate table gains custos_certificate; a table present is passed over. Each file is written by
 * MediaWiki's maintenance/run.php generateSchemaSql from that table's own abstract schema,
 * sql/custos_ticket.json, sql/custos_seat.json, sql/custos_certificate.json, sql/custos_job_run.json and
 * sql/custos_nonce.json, the schema's one source each; the rehearsal checks that they are current.
 * An update only adds a table: it never drops, renames or rewrites one.
 */

namespace Custos;

use MediaWiki\Installer\Hook\LoadExtensionSchemaUpdatesHook;

final class SchemaHooks implements LoadExtensionSchemaUpdatesHook {
	/** The tables, each by its own name; its SQL is sql/<type>/<name>.sql, its source sql/<name>.json. */
	public const TABLES = [ DbTicketStore::TABLE, DbSeatStore::TABLE, DbCertificateStore::TABLE, DbJobRunStore::TABLE, DbNonceStore::TABLE, DbMeterStore::METER, DbMeterStore::BUDGET, DbMeterStore::TRAFFIC ];

	/** @inheritDoc */
	public function onLoadExtensionSchemaUpdates( $updater ) {
		$type = $updater->getDB()->getType();
		$sql = dirname( __DIR__ ) . "/sql/$type";
		foreach ( self::TABLES as $table ) {
			$updater->addExtensionTable( $table, "$sql/$table.sql" );
		}
	}
}
