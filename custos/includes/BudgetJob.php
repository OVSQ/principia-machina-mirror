<?php
/**
 * BudgetJob: the job custosBudget (charter 8.5, a batch job run by the job runner): one budget roll-up
 * (Budget::run) at the server's time. Pushed deduplicated at the end of every governed request the
 * meter records (Meter), so one waits at a time.
 */

namespace Custos;

use MediaWiki\JobQueue\GenericParameterJob;
use MediaWiki\JobQueue\Job;
use MediaWiki\MediaWikiServices;
use Throwable;

final class BudgetJob extends Job implements GenericParameterJob {
	public const TYPE = 'custosBudget';

	public function __construct( array $params ) {
		parent::__construct( self::TYPE, $params );
		$this->removeDuplicates = true;
	}

	public function run() {
		$config = MediaWikiServices::getInstance()->getMainConfig();
		try {
			$r = ( new Budget( Calculator::fromConfig( $config ), new DbMeterStore(), (string)$config->get( 'CustosPreGateFile' ) ) )->run( time() );
			if ( $r['unsettled'] !== [] ) {
				wfDebugLog( Landing::LOG, 'budget: stage left to the next roll-up for ' . count( $r['unsettled'] ) . ' account(s), each overtaken by a landing step' );
			}
		} catch ( Throwable $e ) {
			wfDebugLog( Landing::LOG, 'budget: ' . get_class( $e ) . ': ' . $e->getMessage() );
			$this->setLastError( Refusal::faultClass( $e ) );
			return false;
		}
		return true;
	}

	public function allowRetries() {
		return false;
	}
}
