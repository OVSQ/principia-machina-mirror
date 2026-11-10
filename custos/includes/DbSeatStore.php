<?php
/**
 * DbSeatStore: the SeatStore over MediaWiki's database (the table custos_seat, made from
 * sql/<type>/custos_seat.sql). MediaWiki 1.46.
 *
 * The seat lock is the database's named lock (IDatabase::lock: GET_LOCK on MySQL and MariaDB, the
 * lock manager's file lock on SQLite), named SeatStore::LOCK_PREFIX . $account. The lock and every
 * read and write of the table go through the primary's autocommit connection
 * (ILoadBalancer::CONN_TRX_AUTOCOMMIT), outside the job's transaction round: the read after the
 * lock sees the last holder's committed write (no REPEATABLE READ snapshot taken before the lock),
 * and the charge is committed before the lock is released. charge() writes the two rows inside one
 * atomic section (startAtomic, cancelAtomic on a fault, endAtomic) on that same connection: both
 * rows commit or neither does. On SQLite MediaWiki hands the round's
 * connection instead (database-level locking: its transactions are serializable, LoadBalancer's
 * sanitizeConnectionFlags), and the named lock still orders the admissions.
 */

namespace Custos;

use MediaWiki\MediaWikiServices;
use Throwable;
use Wikimedia\Rdbms\IDatabase;
use Wikimedia\Rdbms\ILoadBalancer;

final class DbSeatStore implements SeatStore {
	public const TABLE = 'custos_seat';

	private ILoadBalancer $lb;

	public function __construct( ?ILoadBalancer $lb = null ) {
		$this->lb = $lb ?? MediaWikiServices::getInstance()->getDBLoadBalancer();
	}

	public function get( string $account, string $kind ): array {
		$r = $this->db()->newSelectQueryBuilder()
			->select( [ 'cs_level', 'cs_since' ] )
			->from( self::TABLE )
			->where( [ 'cs_account' => $account, 'cs_kind' => $kind ] )
			->caller( __METHOD__ )
			->fetchRow();
		return $r ? [ (int)$r->cs_level, (int)$r->cs_since ] : [ 0, 0 ];
	}

	public function put( string $account, string $kind, int $level, int $since ): void {
		$this->replace( $this->db(), $account, $kind, $level, $since, __METHOD__ );
	}

	public function charge( string $account, array $agent, string $sponsorAccount, array $sponsor ): void {
		$db = $this->db();
		$db->startAtomic( __METHOD__, IDatabase::ATOMIC_CANCELABLE );
		try {
			$this->replace( $db, $account, self::AGENT, (int)$agent[0], (int)$agent[1], __METHOD__ );
			$this->replace( $db, $sponsorAccount, self::SPONSOR, (int)$sponsor[0], (int)$sponsor[1], __METHOD__ );
		} catch ( Throwable $e ) {
			$db->cancelAtomic( __METHOD__ );
			throw $e;
		}
		$db->endAtomic( __METHOD__ );
	}

	private function replace( IDatabase $db, string $account, string $kind, int $level, int $since, string $caller ): void {
		$db->newReplaceQueryBuilder()
			->replaceInto( self::TABLE )
			->uniqueIndexFields( [ 'cs_account', 'cs_kind' ] )
			->row( [ 'cs_account' => $account, 'cs_kind' => $kind, 'cs_level' => $level, 'cs_since' => $since ] )
			->caller( $caller )
			->execute();
	}

	public function lock( string $account, int $seconds ): bool {
		return (bool)$this->db()->lock( self::LOCK_PREFIX . $account, __METHOD__, max( 0, $seconds ) );
	}

	public function unlock( string $account ): void {
		$this->db()->unlock( self::LOCK_PREFIX . $account, __METHOD__ );
	}

	/** The primary's autocommit connection, one per request: the lock and the rows share it. */
	private function db(): IDatabase {
		return $this->lb->getConnection( ILoadBalancer::DB_PRIMARY, [], false, ILoadBalancer::CONN_TRX_AUTOCOMMIT );
	}
}
