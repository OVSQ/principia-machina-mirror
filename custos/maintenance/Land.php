<?php
/**
 * Land: one ticket run by hand as the job custosLand runs it (the Operator's act on the command
 * line: a maintenance script is a command-line context), its answer printed:
 *
 *   php maintenance/run.php Custos:land --ticket <id>
 *
 * Prints "land: <the answer's JSON>"; exit 1 when the run failed (a DIGEST MISMATCH, an UNSAFE
 * RESIDENCE, a Calculator fault), its message printed first. The residence is the live check,
 * as for the job and Custos:SeedUwc.
 */

namespace Custos\Maintenance;

use Custos\LandJob;
use MediaWiki\Maintenance\Maintenance;
use Throwable;

final class Land extends Maintenance {
	public function __construct() {
		parent::__construct();
		$this->addDescription( 'Custos: run one ticket as the landing job runs it, and print its answer' );
		$this->addOption( 'ticket', 'The ticket\'s number', true, true );
		$this->requireExtension( 'Custos' );
	}

	public function execute() {
		$id = (string)$this->getOption( 'ticket' );
		if ( preg_match( '/\A[1-9][0-9]{0,17}\z/', $id ) !== 1 ) {
			$this->fatalError( "land: not a ticket: $id" );
		}
		try {
			$answer = LandJob::runTicket( $this->getServiceContainer()->getMainConfig(), (int)$id );
		} catch ( Throwable $e ) {
			$this->output( $e->getMessage() . "\n" );
			$this->fatalError( "land: the ticket $id was not landed" );
		}
		$this->output( 'land: ' . json_encode( $answer, JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE ) . "\n" );
	}
}

return Land::class;
