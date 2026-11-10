<?php
/**
 * Job: a batch job enqueued by name, or its last run read, through the job queue and the run table
 * (the Operator's act on the command line, and a timer's). Exactly one of:
 *
 *   php maintenance/run.php Custos:Job --job <reaudit|cluster|recheck>
 *   php maintenance/run.php Custos:Job --last <reaudit|cluster|recheck>
 *
 * --job pushes the job (deduplicated) and prints "enqueued <name>"; the job runner runs it.
 * --last prints the last run of the job as "<outcome>" and, on a second line, its detail; exit 1
 * when the job has no run or its last run has not ended. Nothing here runs the Calculator.
 */

namespace Custos\Maintenance;

use Custos\BatchJob;
use Custos\ClusterJob;
use Custos\DbJobRunStore;
use Custos\ReauditJob;
use Custos\RecheckJob;
use MediaWiki\Maintenance\Maintenance;

final class Job extends Maintenance {
	private const CLASSES = [
		BatchJob::REAUDIT => ReauditJob::class,
		BatchJob::CLUSTER => ClusterJob::class,
		BatchJob::RECHECK => RecheckJob::class,
	];

	public function __construct() {
		parent::__construct();
		$this->addDescription( 'Custos: enqueue a batch job by name, or print its last run' );
		$this->addOption( 'job', 'Enqueue this batch job (reaudit, cluster or recheck)', false, true );
		$this->addOption( 'last', 'Print the last run of this batch job', false, true );
		$this->requireExtension( 'Custos' );
	}

	public function execute() {
		$modes = array_values( array_filter( [ 'job', 'last' ], fn ( $o ) => $this->hasOption( $o ) ) );
		if ( count( $modes ) !== 1 ) {
			$this->fatalError( 'job: give exactly one of --job and --last' );
		}
		$name = (string)$this->getOption( $modes[0] );
		if ( !isset( self::CLASSES[$name] ) ) {
			$this->fatalError( "job: not a batch job: $name" );
		}
		if ( $modes[0] === 'job' ) {
			$class = self::CLASSES[$name];
			$this->getServiceContainer()->getJobQueueGroup()->push( new $class( [] ) );
			$this->output( "enqueued $name\n" );
			return;
		}
		$row = ( new DbJobRunStore( $this->getServiceContainer()->getConnectionProvider() ) )->last( $name );
		if ( $row === null || $row['outcome'] === null ) {
			$this->fatalError( "job: $name has no ended run" );
		}
		$this->output( $row['outcome'] . "\n" . $row['detail'] . "\n" );
	}
}

return Job::class;
