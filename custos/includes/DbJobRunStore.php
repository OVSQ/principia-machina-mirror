<?php
/**
 * DbJobRunStore: the JobRunStore over MediaWiki's database (the table custos_job_run, made by
 * the hook LoadExtensionSchemaUpdates from sql/<type>/custos_job_run.sql). Thin glue.
 * MediaWiki 1.46.
 */

namespace Custos;

use MediaWiki\MediaWikiServices;
use Wikimedia\Rdbms\IConnectionProvider;

final class DbJobRunStore implements JobRunStore {
	public const TABLE = 'custos_job_run';

	private IConnectionProvider $db;

	public function __construct( ?IConnectionProvider $db = null ) {
		$this->db = $db ?? MediaWikiServices::getInstance()->getConnectionProvider();
	}

	public function start( string $job, string $started ): int {
		$dbw = $this->db->getPrimaryDatabase();
		$dbw->newInsertQueryBuilder()
			->insertInto( self::TABLE )
			->row( [
				'cj_job' => $job,
				'cj_started' => $dbw->timestamp( $started ),
				'cj_done' => null,
				'cj_outcome' => '',
				'cj_detail' => '',
				'cj_counts' => '{}',
			] )
			->caller( __METHOD__ )
			->execute();
		return $dbw->insertId();
	}

	public function finish( int $id, string $outcome, string $detail, string $counts, string $done ): bool {
		$dbw = $this->db->getPrimaryDatabase();
		$dbw->newUpdateQueryBuilder()
			->update( self::TABLE )
			->set( [ 'cj_done' => $dbw->timestamp( $done ), 'cj_outcome' => $outcome, 'cj_detail' => $detail, 'cj_counts' => $counts ] )
			->where( [ 'cj_id' => $id, 'cj_done' => null ] )
			->caller( __METHOD__ )
			->execute();
		return $dbw->affectedRows() === 1;
	}

	public function get( int $id ): ?array {
		return $this->row( [ 'cj_id' => $id ], false );
	}

	public function last( string $job ): ?array {
		return $this->row( [ 'cj_job' => $job ], true );
	}

	private function row( array $where, bool $newest ): ?array {
		$q = $this->db->getPrimaryDatabase()->newSelectQueryBuilder()
			->select( [ 'cj_id', 'cj_job', 'cj_started', 'cj_done', 'cj_outcome', 'cj_detail', 'cj_counts' ] )
			->from( self::TABLE )
			->where( $where )
			->caller( __METHOD__ );
		if ( $newest ) {
			$q->orderBy( 'cj_id', 'DESC' )->limit( 1 );
		}
		$r = $q->fetchRow();
		if ( !$r ) {
			return null;
		}
		return [
			'id' => (int)$r->cj_id,
			'job' => (string)$r->cj_job,
			'started' => (string)wfTimestamp( TS_MW, $r->cj_started ),
			'done' => $r->cj_done === null ? null : (string)wfTimestamp( TS_MW, $r->cj_done ),
			'outcome' => $r->cj_done === null ? null : (string)$r->cj_outcome,
			'detail' => (string)$r->cj_detail,
			'counts' => (string)$r->cj_counts,
		];
	}
}
