<?php
/**
 * seat_race.php: the second job of the harness's seat races (harness.php, section L), run as its
 * own process so that two admissions of one account truly race over one FileSeatStore file.
 *
 *   php custos/tests/seat_race.php <the race's JSON file>
 *
 * The JSON names: seats (the FileSeatStore file), locks (false: the store without the lock),
 * tickets (this job's FileTicketStore folder) and ticket (its number), binary, version and digest
 * (the built pcalc), now, lock_seconds, certs (the FileCertificateStore file the first job reads), and marker (a file written just before the job asks for
 * the seat lock, so the first job knows the second is at the lock). The page store faults on every
 * call (PAGE FAULT), so the race is the admission's alone. The ticket's agent is whichever the ticket names: the same process
 * runs the race of one account (Agent W) and that of two agents of one Sponsor (Agent P1, Agent P2; harness L105-L107). Prints the ticket's answer as JSON.
 * Command line only.
 */

declare( strict_types=1 );

require_once __DIR__ . '/bootstrap.php';

use Custos\Calculator;
use Custos\Landing;
use Custos\PageFault;
use Custos\PageStore;
use Custos\PageTitles;
use Custos\Tests\AnyResidence;
use Custos\Tests\FileCertificateStore;
use Custos\Tests\FileSeatStore;
use Custos\Tests\FileTicketStore;
use Custos\Tests\ProcRunner;

$race = json_decode( (string)file_get_contents( (string)( $argv[1] ?? '' ) ), true, 8, JSON_THROW_ON_ERROR );
$seats = new FileSeatStore( (string)$race['seats'], (bool)$race['locks'] );
$marker = (string)$race['marker'];
$seats->beforeLock = static function ( string $account ) use ( $marker ): void {
	file_put_contents( $marker, $account );
};
$faulting = new class implements PageStore {
	public function get( string $title ): ?string {
		throw new PageFault( 'the page store faulted (the race\'s fault)' );
	}
	public function exists( string $title ): bool {
		throw new PageFault( 'the page store faulted (the race\'s fault)' );
	}
	public function put( string $title, string $text, string $summary ): void {
		throw new PageFault( 'the page store faulted (the race\'s fault)' );
	}
	public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
		throw new PageFault( 'the page store faulted (the race\'s fault)' );
	}
	public function appendAs( string $title, string $line, string $summary, string $actor ): string {
		throw new PageFault( 'the page store faulted (the race\'s fault)' );
	}
};
$calc = new Calculator( (string)$race['binary'], [ 'version' => (string)$race['version'], 'digest' => (string)$race['digest'] ], new ProcRunner(), 'cli',
	new AnyResidence() );
$now = (int)$race['now'];
$landing = new Landing( $calc, $faulting, new PageTitles( 'Principia Machina/UWC', 'Principia Machina' ), new FileTicketStore( (string)$race['tickets'] ),
	$seats, new FileCertificateStore( (string)$race['certs'] ), [ 'poll_after' => 30, 'seat_lock_seconds' => (int)$race['lock_seconds'] ], static fn (): int => $now, static fn (): array => [ 0, 1 ] );
echo json_encode( $landing->run( (int)$race['ticket'] ), JSON_UNESCAPED_SLASHES | JSON_THROW_ON_ERROR ), "\n";
