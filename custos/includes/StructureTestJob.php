<?php
/**
 * StructureTestJob: the job class `custosStructureTest` (charter 8.5, a batch job run by the job
 * runner; TPS 5.3.47 (i)): the structure test with register of one UWC (["prefix" => its prefix]),
 * Landing::structureJob: admitted through `governor admit` as STRUCTURE TEST JOB (lane 5), one
 * Calculator call over the Research Assembly and the open register volume, and the UWC's STRUCTURE
 * TEST LINE written on its INDEX AND BADGE page through PageWriter only when it changes.
 *
 * Pushed by the landing job after every PUSH that lands (LandJob), deduplicated (removeDuplicates
 * over its one parameter, the prefix), so one waits per UWC. A refusal (the admission under
 * pressure, the UWC, the Calculator's refusal of the test, a PAGE FAULT) writes nothing and ends the
 * job without error, its word to the error channel; the next landing pushes it again. A fault fails
 * the job with setLastError (its short class), the class and message in the error channel. Not
 * retried. The job's context is checked first (JobContext), as the landing job's.
 */

namespace Custos;

use MediaWiki\Config\Config;
use MediaWiki\JobQueue\GenericParameterJob;
use MediaWiki\JobQueue\Job;
use MediaWiki\MediaWikiServices;
use Throwable;

final class StructureTestJob extends Job implements GenericParameterJob {
	public const TYPE = 'custosStructureTest';

	public function __construct( array $params ) {
		parent::__construct( self::TYPE, $params );
		$this->removeDuplicates = true;
	}

	public function run() {
		$config = MediaWikiServices::getInstance()->getMainConfig();
		$prefix = $this->params['prefix'] ?? null;
		if ( !is_string( $prefix ) || !PageTitles::isBuildablePrefix( $prefix ) ) {
			$this->setLastError( 'STRUCTURE TEST: the job names no record prefix' );
			return false;
		}
		try {
			$answer = self::runFor( $config, $prefix );
		} catch ( Throwable $e ) {
			$this->setLastError( Refusal::faultClass( $e ) );
			return false;
		}
		if ( isset( $answer['refused'] ) ) {
			wfDebugLog( Landing::LOG, 'structure test of ' . $prefix . ': ' . $answer['refused'] . ': ' . ( $answer['detail'] ?? '' ) );
			if ( $answer['refused'] === 'JOB CONTEXT' ) {
				$this->setLastError( (string)$answer['detail'] );
				return false;
			}
		}
		return true;
	}

	/** The structure test of the UWC $prefix as the job runs it, under the job's context: its answer. */
	public static function runFor( Config $config, string $prefix ): array {
		$ctx = (array)$config->get( 'CustosJobContext' );
		$refusal = JobContext::refusal( (int)( $ctx['min_address_space'] ?? JobContext::MIN_ADDRESS_SPACE ) );
		if ( $refusal !== null ) {
			return [ 'refused' => 'JOB CONTEXT', 'detail' => $refusal ];
		}
		$landing = new Landing( Calculator::fromConfig( $config ), new MwStore(), PageTitles::fromConfig( $config ),
			new DbTicketStore(), new DbSeatStore(), new DbCertificateStore(), Landing::confFrom( $config ), nonces: new DbNonceStore(), meter: new DbMeterStore() );
		return $landing->structureJob( $prefix );
	}

	public function allowRetries() {
		return false;
	}
}
