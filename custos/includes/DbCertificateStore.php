<?php
/**
 * DbCertificateStore: the CertificateStore over MediaWiki's database (the table
 * custos_certificate, made from sql/<type>/custos_certificate.sql, and the refused-PROMPT marks, the
 * table custos_prompt_mark, made from sql/<type>/custos_prompt_mark.sql). MediaWiki 1.46.
 *
 * A mark's row is never deleted: put() turns a STANDING mark CLEARED (with the time) and replaces
 * the certificate's row in one atomic section, so a row write that fails rolls the clear back and the
 * mark stands; markPrompt() writes STANDING over a CLEARED row or none (the row keeps the latest
 * episode's times, not a history).
 *
 * Every read and the write go through the primary's autocommit connection
 * (ILoadBalancer::CONN_TRX_AUTOCOMMIT), as DbSeatStore's do: admission reads the row the
 * Operator's last Custos:Certify committed, not a replica's or a snapshot's copy.
 */

namespace Custos;

use MediaWiki\MediaWikiServices;
use Throwable;
use Wikimedia\Rdbms\IDatabase;
use Wikimedia\Rdbms\ILoadBalancer;

final class DbCertificateStore implements CertificateStore {
	public const TABLE = 'custos_certificate';
	public const MARK = 'custos_prompt_mark';
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
		// The re-certification clears the mark and writes the row in one atomic section: a row write that
		// fails cancels the section, so the clear is rolled back and the mark stands on the old row.
		// A refusal racing this write marks the new row (refusing more).
		$db = $this->db();
		$db->startAtomic( __METHOD__, IDatabase::ATOMIC_CANCELABLE );
		try {
			$db->newUpdateQueryBuilder()
				->update( self::MARK )
				->set( [ 'cpm_state' => self::MARK_CLEARED, 'cpm_cleared' => time() ] )
				->where( [ 'cpm_agent' => (string)$row['agent'], 'cpm_state' => self::MARK_STANDING ] )
				->caller( __METHOD__ )
				->execute();
			$db->newReplaceQueryBuilder()
				->replaceInto( self::TABLE )
				->uniqueIndexFields( [ 'cc_agent' ] )
				->row( $values )
				->caller( __METHOD__ )
				->execute();
		} catch ( Throwable $e ) {
			$db->cancelAtomic( __METHOD__ );
			throw $e;
		}
		$db->endAtomic( __METHOD__ );
	}

	public function promptMarked( string $agent ): bool {
		return $this->db()->newSelectQueryBuilder()
			->select( 'cpm_agent' )
			->from( self::MARK )
			->where( [ 'cpm_agent' => $agent, 'cpm_state' => self::MARK_STANDING ] )
			->caller( __METHOD__ )
			->fetchField() !== false;
	}

	public function markPrompt( string $agent, int $at ): void {
		if ( $this->promptMarked( $agent ) ) {
			return;
		}
		$this->db()->newReplaceQueryBuilder()
			->replaceInto( self::MARK )
			->uniqueIndexFields( [ 'cpm_agent' ] )
			->row( [ 'cpm_agent' => $agent, 'cpm_state' => self::MARK_STANDING, 'cpm_marked' => $at, 'cpm_cleared' => 0 ] )
			->caller( __METHOD__ )
			->execute();
	}

	/** The primary's autocommit connection. */
	private function db(): IDatabase {
		return $this->lb->getConnection( ILoadBalancer::DB_PRIMARY, [], false, ILoadBalancer::CONN_TRX_AUTOCOMMIT );
	}
}
