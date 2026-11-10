<?php
/**
 * BatchJobBase: the job class every batch job shares (custosReaudit, custosCluster, custosRecheck):
 * it runs the job named by its subclass through the frame (BatchJob), under the job's context, and
 * records the run. Deduplicated (removeDuplicates): one job of a type waits in the queue. Not
 * retried. A run ending FAULT, INTEGRITY HALT or JOB CONTEXT fails the job with setLastError.
 * The wiki runs jobs only from its job runner ($wgJobRunRate = 0).
 */

namespace Custos;

use MediaWiki\Config\Config;
use MediaWiki\JobQueue\GenericParameterJob;
use MediaWiki\JobQueue\Job;
use MediaWiki\MediaWikiServices;
use Throwable;

abstract class BatchJobBase extends Job implements GenericParameterJob {
	/** The job type and the frame's job name. */
	abstract protected static function jobName(): string;

	public function __construct( array $params ) {
		parent::__construct( 'custos' . ucfirst( static::jobName() ), $params );
		$this->removeDuplicates = true;
	}

	public function run() {
		try {
			$answer = self::runNamed( MediaWikiServices::getInstance()->getMainConfig(), static::jobName() );
		} catch ( Throwable $e ) {
			$this->setLastError( Refusal::faultClass( $e ) );
			return false;
		}
		if ( in_array( $answer['outcome'], [ 'FAULT', 'INTEGRITY HALT', 'JOB CONTEXT' ], true ) ) {
			$this->setLastError( $answer['outcome'] . ': ' . $answer['detail'] );
			return false;
		}
		return true;
	}

	/** One run of the job $name as the job runner runs it: the job and the maintenance script share it. */
	public static function runNamed( Config $config, string $name ): array {
		$frame = new BatchJob( Calculator::fromConfig( $config ), new DbJobRunStore(), BatchJob::confFrom( $config ) );
		return $frame->run( $name );
	}

	public function allowRetries() {
		return false;
	}
}
