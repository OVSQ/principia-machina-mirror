<?php
/**
 * DbNonceStore: the NonceStore over MediaWiki's database (the table custos_nonce, made from
 * sql/<type>/custos_nonce.sql). MediaWiki 1.46. One row per account and prefix: put replaces it;
 * take reads it and deletes that row with that nonce, and returns the nonce only when its delete
 * removed one row, so of two jobs taking one nonce exactly one gets it. The primary's autocommit
 * connection, as DbSeatStore's: the delete is committed before the job goes on.
 */

namespace Custos;

use MediaWiki\MediaWikiServices;
use Wikimedia\Rdbms\IDatabase;
use Wikimedia\Rdbms\ILoadBalancer;

final class DbNonceStore implements NonceStore {
	public const TABLE = 'custos_nonce';

	private ILoadBalancer $lb;

	public function __construct( ?ILoadBalancer $lb = null ) {
		$this->lb = $lb ?? MediaWikiServices::getInstance()->getDBLoadBalancer();
	}

	public function put( string $account, string $prefix, string $nonce, int $issued ): void {
		$this->db()->newReplaceQueryBuilder()
			->replaceInto( self::TABLE )
			->uniqueIndexFields( [ 'cn_account', 'cn_prefix' ] )
			->row( [ 'cn_account' => $account, 'cn_prefix' => $prefix, 'cn_nonce' => $nonce, 'cn_issued' => $issued ] )
			->caller( __METHOD__ )
			->execute();
	}

	public function take( string $account, string $prefix ): ?string {
		$db = $this->db();
		$nonce = $db->newSelectQueryBuilder()
			->select( 'cn_nonce' )
			->from( self::TABLE )
			->where( [ 'cn_account' => $account, 'cn_prefix' => $prefix ] )
			->caller( __METHOD__ )
			->fetchField();
		if ( !is_string( $nonce ) ) {
			return null;
		}
		$db->newDeleteQueryBuilder()
			->deleteFrom( self::TABLE )
			->where( [ 'cn_account' => $account, 'cn_prefix' => $prefix, 'cn_nonce' => $nonce ] )
			->caller( __METHOD__ )
			->execute();
		return $db->affectedRows() === 1 ? $nonce : null;
	}

	private function db(): IDatabase {
		return $this->lb->getConnection( ILoadBalancer::DB_PRIMARY, [], false, ILoadBalancer::CONN_TRX_AUTOCOMMIT );
	}
}
