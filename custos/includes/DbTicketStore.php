<?php
/**
 * DbTicketStore: the TicketStore over MediaWiki's database (the table custos_ticket, made by
 * the hook LoadExtensionSchemaUpdates from sql/<type>/custos_ticket.sql). Thin glue: the
 * request is stored as received and never read here. MediaWiki 1.46.
 */

namespace Custos;

use MediaWiki\MediaWikiServices;
use Wikimedia\Rdbms\IConnectionProvider;
use Wikimedia\Rdbms\IDatabase;
use Wikimedia\Rdbms\IReadableDatabase;

final class DbTicketStore implements TicketStore {
	public const TABLE = 'custos_ticket';

	private IConnectionProvider $db;

	public function __construct( ?IConnectionProvider $db = null ) {
		$this->db = $db ?? MediaWikiServices::getInstance()->getConnectionProvider();
	}

	public function create( string $op, string $account, string $prefix, string $request ): int {
		$dbw = $this->db->getPrimaryDatabase();
		$dbw->newInsertQueryBuilder()
			->insertInto( self::TABLE )
			->row( [
				'ct_op' => $op,
				'ct_account' => $account,
				'ct_prefix' => $prefix,
				'ct_request' => $request,
				'ct_state' => self::QUEUED,
				'ct_answer' => null,
				'ct_created' => $dbw->timestamp(),
				'ct_done' => null,
			] )
			->caller( __METHOD__ )
			->execute();
		return $dbw->insertId();
	}

	public function get( int $id ): ?array {
		// The primary: a POLL right after its PETITION reads the row just written.
		return $this->row( $this->db->getPrimaryDatabase(), [ 'ct_id' => $id ], false );
	}

	public function answer( int $id, string $answer ): bool {
		$dbw = $this->db->getPrimaryDatabase();
		$dbw->newUpdateQueryBuilder()
			->update( self::TABLE )
			->set( [ 'ct_state' => self::DONE, 'ct_answer' => $answer, 'ct_done' => $dbw->timestamp() ] )
			->where( [ 'ct_id' => $id, 'ct_state' => [ self::QUEUED, self::IN_WORK ] ] )
			->caller( __METHOD__ )
			->execute();
		return $dbw->affectedRows() === 1;
	}

	/** The oldest QUEUED row, then a conditional update; a racing claim of the same row moves on to the next. */
	public function claimNext(): ?array {
		$dbw = $this->db->getPrimaryDatabase();
		while ( true ) {
			$row = $this->row( $dbw, [ 'ct_state' => self::QUEUED ], true );
			if ( $row === null ) {
				return null;
			}
			$dbw->newUpdateQueryBuilder()
				->update( self::TABLE )
				->set( [ 'ct_state' => self::IN_WORK ] )
				->where( [ 'ct_id' => $row['id'], 'ct_state' => self::QUEUED ] )
				->caller( __METHOD__ )
				->execute();
			if ( $dbw->affectedRows() === 1 ) {
				$row['state'] = self::IN_WORK;
				return $row;
			}
		}
	}

	public function claim( int $id ): ?array {
		$dbw = $this->db->getPrimaryDatabase();
		$dbw->newUpdateQueryBuilder()
			->update( self::TABLE )
			->set( [ 'ct_state' => self::IN_WORK ] )
			->where( [ 'ct_id' => $id, 'ct_state' => self::QUEUED ] )
			->caller( __METHOD__ )
			->execute();
		if ( $dbw->affectedRows() !== 1 ) {
			return null;
		}
		return $this->row( $dbw, [ 'ct_id' => $id ], false );
	}

	public function inWork(): array {
		$res = $this->db->getPrimaryDatabase()->newSelectQueryBuilder()
			->select( [ 'ct_id', 'ct_op', 'ct_account' ] )
			->from( self::TABLE )
			->where( [ 'ct_state' => self::IN_WORK ] )
			->orderBy( 'ct_id' )
			->caller( __METHOD__ )
			->fetchResultSet();
		$out = [];
		foreach ( $res as $r ) {
			$out[] = [ 'id' => (int)$r->ct_id, 'op' => (string)$r->ct_op, 'account' => (string)$r->ct_account ];
		}
		return $out;
	}

	public function count( string $state ): int {
		return (int)$this->db->getPrimaryDatabase()->newSelectQueryBuilder()
			->select( 'COUNT(*)' )
			->from( self::TABLE )
			->where( [ 'ct_state' => $state ] )
			->caller( __METHOD__ )
			->fetchField();
	}

	private function row( IReadableDatabase $db, array $where, bool $oldest ): ?array {
		$q = $db->newSelectQueryBuilder()
			->select( [ 'ct_id', 'ct_op', 'ct_account', 'ct_prefix', 'ct_request', 'ct_state', 'ct_answer', 'ct_created', 'ct_done' ] )
			->from( self::TABLE )
			->where( $where )
			->caller( __METHOD__ );
		if ( $oldest ) {
			$q->orderBy( 'ct_id' )->limit( 1 );
		}
		$r = $q->fetchRow();
		if ( !$r ) {
			return null;
		}
		return [
			'id' => (int)$r->ct_id,
			'op' => (string)$r->ct_op,
			'account' => (string)$r->ct_account,
			'prefix' => (string)$r->ct_prefix,
			'request' => (string)$r->ct_request,
			'state' => (string)$r->ct_state,
			'answer' => $r->ct_answer === null ? null : (string)$r->ct_answer,
			'created' => (string)wfTimestamp( TS_MW, $r->ct_created ),
			'done' => $r->ct_done === null ? null : (string)wfTimestamp( TS_MW, $r->ct_done ),
		];
	}
}
