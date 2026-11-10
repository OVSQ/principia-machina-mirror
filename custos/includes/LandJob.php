<?php
/**
 * LandJob: the job class `custosLand`, the ticket's work out of the web request.
 * run() checks the job's context (JobContext: CustosJobContext's address space) and then
 * runs Landing over the ticket the job carries (["ticket" => id]); every answer, a refusal
 * included, is written to the ticket. A fault of the Calculator (a DIGEST MISMATCH, an UNSAFE
 * RESIDENCE, a call outside its protocol) answers the ticket and fails the job with
 * setLastError; a DIGEST MISMATCH halts every landing, the Calculator refusing each call while
 * the binary differs. Not retried. The wiki runs jobs only from its job runner ($wgJobRunRate = 0).
 *
 * Deduplicated (removeDuplicates): the API's enqueue and POLL's sweep (Ops) push the same job for a
 * ticket, and one job per ticket waits in the queue. A job whose ticket is no longer QUEUED (claimed
 * or answered by an earlier job) is a duplicate: Landing's conditional claim writes nothing and the
 * job ends without error, so each ticket is landed once.
 *
 * A PUSH that lands pushes the job custosStructureTest for its UWC (StructureTestJob), deduplicated.
 */

namespace Custos;

use MediaWiki\Config\Config;
use MediaWiki\JobQueue\GenericParameterJob;
use MediaWiki\JobQueue\Job;
use MediaWiki\MediaWikiServices;
use Throwable;

final class LandJob extends Job implements GenericParameterJob {
	public const TYPE = 'custosLand';

	public function __construct( array $params ) {
		parent::__construct( self::TYPE, $params );
		$this->removeDuplicates = true;
	}

	public function run() {
		$config = MediaWikiServices::getInstance()->getMainConfig();
		$id = (int)( $this->params['ticket'] ?? 0 );
		try {
			$answer = self::runTicket( $config, $id );
		} catch ( Throwable $e ) {
			$this->setLastError( $e->getMessage() );
			return false;
		}
		if ( ( $answer['refused'] ?? null ) === 'NOT QUEUED' ) {
			// A duplicate job: the ticket was claimed or answered by an earlier one; nothing was written.
			if ( ( new DbTicketStore() )->get( $id ) === null ) {
				// No such ticket: one line to the error channel; the job still ends without error.
				wfDebugLog( Landing::LOG, "land job: there is no ticket $id; nothing was run" );
			}
			return true;
		}
		if ( ( $answer['refused'] ?? null ) === 'JOB CONTEXT' ) {
			$this->setLastError( (string)$answer['detail'] );
			return false;
		}
		return true;
	}

	/**
	 * One ticket run as the job runs it, under the job's context: the job and the maintenance
	 * script Custos:land share it. The ticket's answer.
	 */
	public static function runTicket( Config $config, int $id ): array {
		$tickets = new DbTicketStore();
		$ctx = (array)$config->get( 'CustosJobContext' );
		$refusal = JobContext::refusal( (int)( $ctx['min_address_space'] ?? JobContext::MIN_ADDRESS_SPACE ) );
		if ( $refusal !== null ) {
			$answer = [ 'refused' => 'JOB CONTEXT', 'detail' => $refusal ];
			if ( $tickets->claim( $id ) !== null ) {
				$tickets->answer( $id, json_encode( $answer, JSON_UNESCAPED_SLASHES | JSON_THROW_ON_ERROR ) );
			}
			return $answer;
		}
		$landing = new Landing( Calculator::fromConfig( $config ), new MwStore(), PageTitles::fromConfig( $config ),
			$tickets, new DbSeatStore(), new DbCertificateStore(), Landing::confFrom( $config ), nonces: new DbNonceStore(), meter: new DbMeterStore(),
			afterPush: static function ( string $prefix ): void {
				// The structure test after every PUSH that lands: one job per UWC waits (removeDuplicates).
				MediaWikiServices::getInstance()->getJobQueueGroup()->push( new StructureTestJob( [ 'prefix' => $prefix ] ) );
			} );
		return $landing->run( $id );
	}

	public function allowRetries() {
		return false;
	}
}
