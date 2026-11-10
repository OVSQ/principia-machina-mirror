<?php
/**
 * Ticket: the ticket store written and read by hand, through TicketStore (DbTicketStore over the
 * wiki's own database, wherever its LocalSettings.php puts it), the Operator's act on the command
 * line (a maintenance script is a command-line context). Exactly one of:
 *
 *   php maintenance/run.php Custos:Ticket --new <op> --account <name> --prefix <px> --request <json>
 *   php maintenance/run.php Custos:Ticket --answer <id>
 *   php maintenance/run.php Custos:Ticket --count <state>
 *
 * --new writes one ticket QUEUED and prints its id: the op PETITION, PUSH or RELEASE, a prefix
 * PageTitles builds, the account a user name, the request UTF-8 text stored as given and never
 * parsed here (the landing job reads it through the Calculator). No job is enqueued: the ticket is
 * run by `Custos:Land --ticket <id>`.
 * --answer prints the ticket's answer (ct_answer) as written; exit 1 when there is no such ticket
 * or it is not yet DONE.
 * --count prints the number of tickets in the state QUEUED, IN WORK or DONE.
 *
 * The rehearsal (custos/tests/rehearsal.sh) reads and writes its tickets through this script, so
 * it never opens the wiki's database by a path of its own.
 */

namespace Custos\Maintenance;

use Custos\DbTicketStore;
use Custos\PageTitles;
use Custos\TicketStore;
use MediaWiki\Maintenance\Maintenance;

final class Ticket extends Maintenance {
	private const OPS = [ 'PETITION', 'PUSH', 'RELEASE' ];
	private const STATES = [ TicketStore::QUEUED, TicketStore::IN_WORK, TicketStore::DONE ];

	public function __construct() {
		parent::__construct();
		$this->addDescription( 'Custos: write a ticket QUEUED, print a ticket\'s answer, or count the tickets in a state, through the ticket store' );
		$this->addOption( 'new', 'Write one ticket QUEUED of this op (PETITION, PUSH or RELEASE) and print its number', false, true );
		$this->addOption( 'account', 'With --new: the account\'s user name', false, true );
		$this->addOption( 'prefix', 'With --new: the UWC\'s record prefix', false, true );
		$this->addOption( 'request', 'With --new: the request\'s parameters as JSON text, stored as given', false, true );
		$this->addOption( 'answer', 'Print the answer of the ticket of this number', false, true );
		$this->addOption( 'count', 'Print the number of tickets in this state (QUEUED, IN WORK or DONE)', false, true );
		$this->requireExtension( 'Custos' );
	}

	public function execute() {
		$modes = array_values( array_filter( [ 'new', 'answer', 'count' ], fn ( $o ) => $this->hasOption( $o ) ) );
		if ( count( $modes ) !== 1 ) {
			$this->fatalError( 'ticket: give exactly one of --new, --answer and --count' );
		}
		$store = new DbTicketStore( $this->getServiceContainer()->getConnectionProvider() );
		switch ( $modes[0] ) {
			case 'new':
				$this->create( $store );
				break;
			case 'answer':
				$this->answer( $store );
				break;
			default:
				$this->count( $store );
		}
	}

	private function create( TicketStore $store ): void {
		$op = (string)$this->getOption( 'new' );
		$account = (string)$this->getOption( 'account', '' );
		$prefix = (string)$this->getOption( 'prefix', '' );
		$request = $this->getOption( 'request' );
		if ( !in_array( $op, self::OPS, true ) ) {
			$this->fatalError( "ticket: not an op that writes a ticket: $op" );
		}
		if ( $account === '' || !mb_check_encoding( $account, 'UTF-8' ) ) {
			$this->fatalError( 'ticket: --new needs --account, a user name' );
		}
		if ( !PageTitles::isBuildablePrefix( $prefix ) ) {
			$this->fatalError( 'ticket: --new needs --prefix, a record prefix' );
		}
		if ( !is_string( $request ) || $request === '' || !mb_check_encoding( $request, 'UTF-8' ) ) {
			$this->fatalError( 'ticket: --new needs --request, UTF-8 text' );
		}
		$this->output( $store->create( $op, $account, $prefix, $request ) . "\n" );
	}

	private function answer( TicketStore $store ): void {
		$id = (string)$this->getOption( 'answer' );
		if ( preg_match( '/\A[1-9][0-9]{0,17}\z/', $id ) !== 1 ) {
			$this->fatalError( "ticket: not a ticket: $id" );
		}
		$row = $store->get( (int)$id );
		if ( $row === null ) {
			$this->fatalError( "ticket: no ticket $id" );
		}
		if ( $row['state'] !== TicketStore::DONE || $row['answer'] === null ) {
			$this->fatalError( "ticket: the ticket $id is {$row['state']}, not answered" );
		}
		$this->output( $row['answer'] . "\n" );
	}

	private function count( TicketStore $store ): void {
		$state = (string)$this->getOption( 'count' );
		if ( !in_array( $state, self::STATES, true ) ) {
			$this->fatalError( "ticket: not a ticket state: $state" );
		}
		$this->output( $store->count( $state ) . "\n" );
	}
}

return Ticket::class;
