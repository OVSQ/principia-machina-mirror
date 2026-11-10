<?php
/** DbMeterStore: the meter's live store (MeterStore) over custos_meter, custos_budget and custos_traffic. */

namespace Custos;

use MediaWiki\MediaWikiServices;
use Wikimedia\Rdbms\IDatabase;
use Wikimedia\Rdbms\ILoadBalancer;

final class DbMeterStore implements MeterStore {
	public const METER = 'custos_meter';
	public const BUDGET = 'custos_budget';
	public const TRAFFIC = 'custos_traffic';
	private const COUNTS = [ 'time', 'lane', 'cpu', 'wall', 'memory', 'bytes', 'landed', 'weight' ];

	private ILoadBalancer $lb;

	public function __construct( ?ILoadBalancer $lb = null ) {
		$this->lb = $lb ?? MediaWikiServices::getInstance()->getDBLoadBalancer();
	}

	public function record( array $row ): void {
		$r = [ 'cm_account' => (string)$row['account'], 'cm_network' => (string)$row['network'], 'cm_op' => (string)$row['op'] ];
		foreach ( self::COUNTS as $k ) {
			$r["cm_$k"] = max( 0, (int)( $row[$k] ?? 0 ) );
		}
		$this->db()->newInsertQueryBuilder()->insertInto( self::METER )->row( $r )->caller( __METHOD__ )->execute();
	}

	public function rows( int $since ): array {
		$res = $this->db()->newSelectQueryBuilder()->select( '*' )->from( self::METER )
			->where( $this->db()->expr( 'cm_time', '>=', $since ) )->caller( __METHOD__ )->fetchResultSet();
		$out = [];
		foreach ( $res as $r ) {
			$row = [ 'account' => (string)$r->cm_account, 'network' => (string)$r->cm_network, 'op' => (string)$r->cm_op ];
			foreach ( self::COUNTS as $k ) {
				$row[$k] = (int)$r->{"cm_$k"};
			}
			$out[] = $row;
		}
		return $out;
	}

	public function prune( int $before ): int {
		$db = $this->db();
		$db->newDeleteQueryBuilder()->deleteFrom( self::METER )->where( $db->expr( 'cm_time', '<', $before ) )->caller( __METHOD__ )->execute();
		return $db->affectedRows();
	}

	public function budget(): array {
		$b = MemMeterStore::empty();
		$res = $this->db()->newSelectQueryBuilder()->select( '*' )->from( self::BUDGET )->caller( __METHOD__ )->fetchResultSet();
		foreach ( $res as $r ) {
			$h = (string)$r->cb_horizon;
			if ( isset( MeterStore::HORIZONS[$h] ) ) {
				$b['use'][$h] = (int)$r->cb_use;
				$b['requests'][$h] = (int)$r->cb_requests;
				$b['rolled'] = (int)$r->cb_rolled;
				$b['level'] = (string)$r->cb_level;
				$b['kept'] = (string)$r->cb_kept;
			}
		}
		return $b;
	}

	public function putBudget( array $use, array $requests, int $rolled, string $level, string $kept ): void {
		foreach ( array_keys( MeterStore::HORIZONS ) as $h ) {
			$this->db()->newReplaceQueryBuilder()->replaceInto( self::BUDGET )->uniqueIndexFields( [ 'cb_horizon' ] )
				->row( [ 'cb_horizon' => $h, 'cb_use' => (int)( $use[$h] ?? 0 ), 'cb_requests' => (int)( $requests[$h] ?? 0 ),
					'cb_rolled' => $rolled, 'cb_level' => $level, 'cb_kept' => $kept ] )
				->caller( __METHOD__ )->execute();
		}
	}

	public function traffic( string $account ): ?array {
		$r = $this->db()->newSelectQueryBuilder()->select( [ 'ctr_record', 'ctr_stage', 'ctr_time' ] )->from( self::TRAFFIC )
			->where( [ 'ctr_account' => $account ] )->caller( __METHOD__ )->fetchRow();
		return $r ? [ 'record' => (string)$r->ctr_record, 'stage' => (string)$r->ctr_stage, 'time' => (int)$r->ctr_time ] : null;
	}

	public function putTraffic( string $account, string $record, string $stage, int $time ): void {
		$this->db()->newReplaceQueryBuilder()->replaceInto( self::TRAFFIC )->uniqueIndexFields( [ 'ctr_account' ] )
			->row( [ 'ctr_account' => $account, 'ctr_record' => $record, 'ctr_stage' => $stage, 'ctr_time' => $time ] )
			->caller( __METHOD__ )->execute();
	}

	public function casTraffic( string $account, ?string $was, string $record, string $stage, int $time ): bool {
		$db = $this->db();
		if ( $was === null ) {
			// The first record: made only where none is (the primary key), else a miss.
			$db->newInsertQueryBuilder()->insertInto( self::TRAFFIC )->ignore()
				->row( [ 'ctr_account' => $account, 'ctr_record' => $record, 'ctr_stage' => $stage, 'ctr_time' => $time ] )
				->caller( __METHOD__ )->execute();
			return $db->affectedRows() === 1;
		}
		if ( $record === $was ) {
			// An unchanged step writes nothing: no UPDATE, so ctr_stage and ctr_time stay the
			// last writer's; it only compares, a read of the record as it stands.
			return ( $this->traffic( $account )['record'] ?? null ) === $was;
		}
		// The record differs from $was, so a matched row always changes and counts as affected: no
		// row affected is a miss.
		$db->newUpdateQueryBuilder()->update( self::TRAFFIC )
			->set( [ 'ctr_record' => $record, 'ctr_stage' => $stage, 'ctr_time' => $time ] )
			->where( [ 'ctr_account' => $account, 'ctr_record' => $was ] )->caller( __METHOD__ )->execute();
		return $db->affectedRows() === 1;
	}

	public function stageTraffic( string $account, string $record, string $stage, int $time ): bool {
		$db = $this->db();
		$db->newUpdateQueryBuilder()->update( self::TRAFFIC )->set( [ 'ctr_stage' => $stage, 'ctr_time' => $time ] )
			->where( [ 'ctr_account' => $account, 'ctr_record' => $record ] )->caller( __METHOD__ )->execute();
		if ( $db->affectedRows() > 0 ) {
			return true;
		}
		// No row changed: the record moved on (a miss), or the row already held this stage and time
		// (a match whose values were equal, which a database may count as no row affected).
		$now = $this->traffic( $account );
		return $now !== null && $now['record'] === $record && $now['stage'] === $stage && $now['time'] === $time;
	}

	public function accounts(): array {
		return array_map( 'strval', $this->db()->newSelectQueryBuilder()->select( 'ctr_account' )->from( self::TRAFFIC )
			->caller( __METHOD__ )->fetchFieldValues() );
	}

	private function db(): IDatabase {
		return $this->lb->getConnection( ILoadBalancer::DB_PRIMARY, [], false, ILoadBalancer::CONN_TRX_AUTOCOMMIT );
	}
}
