<?php
/**
 * DbCertificateStore: the CertificateStore over MediaWiki's database (the table
 * custos_certificate, made from sql/<type>/custos_certificate.sql). MediaWiki 1.46.
 *
 * Every read and the write go through the primary's autocommit connection
 * (ILoadBalancer::CONN_TRX_AUTOCOMMIT), as DbSeatStore's do: admission reads the row the
 * Operator's last Custos:Certify committed, not a replica's or a snapshot's copy.
 */

namespace Custos;

use MediaWiki\MediaWikiServices;
use Wikimedia\Rdbms\IDatabase;
use Wikimedia\Rdbms\ILoadBalancer;

final class DbCertificateStore implements CertificateStore {
	public const TABLE = 'custos_certificate';
	/** Each member of a row and its column. */
	private const COLUMNS = [
		'agent' => 'cc_agent', 'sponsor' => 'cc_sponsor', 'd_is' => 'cc_d_is', 'd_prompt' => 'cc_d_prompt',
		'family' => 'cc_family', 'model' => 'cc_model', 'state' => 'cc_state',
	];

	private ILoadBalancer $lb;

	public function __construct( ?ILoadBalancer $lb = null ) {
		$this->lb = $lb ?? MediaWikiServices::getInstance()->getDBLoadBalancer();
	}

	public function get( string $agent ): ?array {
		$r = $this->db()->newSelectQueryBuilder()
			->select( array_values( self::COLUMNS ) )
			->from( self::TABLE )
			->where( [ 'cc_agent' => $agent ] )
			->caller( __METHOD__ )
			->fetchRow();
		if ( !$r ) {
			return null;
		}
		$row = [];
		foreach ( self::COLUMNS as $member => $column ) {
			$row[$member] = (string)$r->$column;
		}
		return $row;
	}

	public function agentsOf( string $sponsor ): array {
		$agents = array_map( 'strval', $this->db()->newSelectQueryBuilder()
			->select( 'cc_agent' )
			->from( self::TABLE )
			->where( [ 'cc_sponsor' => $sponsor ] )
			->caller( __METHOD__ )
			->fetchFieldValues() );
		sort( $agents, SORT_STRING );
		return $agents;
	}

	public function put( array $row ): void {
		$values = [];
		foreach ( self::COLUMNS as $member => $column ) {
			$values[$column] = (string)$row[$member];
		}
		$this->db()->newReplaceQueryBuilder()
			->replaceInto( self::TABLE )
			->uniqueIndexFields( [ 'cc_agent' ] )
			->row( $values )
			->caller( __METHOD__ )
			->execute();
	}

	/** The primary's autocommit connection. */
	private function db(): IDatabase {
		return $this->lb->getConnection( ILoadBalancer::DB_PRIMARY, [], false, ILoadBalancer::CONN_TRX_AUTOCOMMIT );
	}
}
