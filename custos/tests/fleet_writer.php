<?php
/**
 * fleet_writer.php: the cases FW1 to FW6 of the fleet-level writer (FleetWriter) and the top
 * performer page texts (PageTexts::topPerformers), on the test stores. Its own runner until the
 * harness takes the cases in (the K chain's harness unit).
 *
 *   php custos/tests/fleet_writer.php
 *
 * Command line only.
 */

declare( strict_types=1 );

require_once __DIR__ . '/bootstrap.php';

use Custos\Blocks;
use Custos\FleetWriter;
use Custos\PageFault;
use Custos\PageStore;
use Custos\PageTexts;
use Custos\PageTitles;
use Custos\Tests\FileStore;

/** A store that logs each casPut in order and can run a hook just before a given save. */
final class FwStore implements PageStore {
	/** @var string[] */
	public array $saves = [];
	/** @var array<string, callable> title => run before that title's casPut */
	public array $before = [];
	public function __construct( private FileStore $inner ) {
	}
	public function get( string $title ): ?string {
		return $this->inner->get( $title );
	}
	public function exists( string $title ): bool {
		return $this->inner->exists( $title );
	}
	public function put( string $title, string $text, string $summary ): void {
		$this->inner->put( $title, $text, $summary );
	}
	public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
		if ( isset( $this->before[$title] ) ) {
			( $this->before[$title] )();
		}
		$had = count( $this->inner->revisions[$title] ?? [] );
		$ok = $this->inner->casPut( $title, $expected, $text, $summary, $actor );
		if ( $ok && count( $this->inner->revisions[$title] ?? [] ) > $had ) {
			$this->saves[] = $title;
		}
		return $ok;
	}
	public function appendAs( string $title, string $line, string $summary, string $actor ): string {
		return $this->inner->appendAs( $title, $line, $summary, $actor );
	}
}

$scratch = sys_get_temp_dir() . '/custos-fleet-' . getmypid();
register_shutdown_function( static function () use ( $scratch ): void {
	foreach ( glob( "$scratch/*/*" ) ?: [] as $f ) {
		unlink( $f );
	}
	foreach ( glob( "$scratch/*" ) ?: [] as $d ) {
		rmdir( $d );
	}
	@rmdir( $scratch );
} );
$n = 0;
$fresh = static function () use ( $scratch, &$n ): array {
	$store = new FwStore( new FileStore( $scratch . '/s' . ( ++$n ) ) );
	$titles = new PageTitles( 'Principia Machina/UWC', 'Principia Machina' );
	return [ $store, $titles, new FleetWriter( $store, $titles ) ];
};
$titles = new PageTitles( 'Principia Machina/UWC', 'Principia Machina' );
$main = $titles->topPerformers();
$snap = $titles->topPerformers( '2026-11' );
// The Calculator's text of a result, as an opaque answer: PHP reads nothing in it.
$answer = "ROW 1 model-a 0.91\nROW 2 model-b 0.88";
$page = PageTexts::topPerformers( '2026-11', $answer, 'PUBLISHED' );
$snapText = PageTexts::topPerformers( '2026-11', $answer );

// FW1: the snapshot first, the page last, each once, as Custos's revision.
[ $s, , $w ] = $fresh();
$saved = $w->publish( '2026-11', $snapText, $page );
G::ok( $saved === [ $snap, $main ] && $s->saves === [ $snap, $main ] && $s->get( $snap ) === $snapText && $s->get( $main ) === $page,
	'FW1 a publication saves the snapshot first and the page last, each once', implode( ' | ', $s->saves ) );

// FW2: a state change writes the page alone, the month and the performers as written; no snapshot.
[ $s, , $w ] = $fresh();
$w->publish( '2026-11', $snapText, $page );
$s->saves = [];
$failing = PageTexts::topPerformersState( $s->get( $main ), 'SOURCE FAILING source-one' );
$w->stateOnly( '2026-11', $failing, $s->get( $main ) );
G::ok( $s->saves === [ $main ] && PageTexts::readTopState( $s->get( $main ) ) === 'SOURCE FAILING source-one'
	&& Blocks::one( $s->get( $main ), PageTexts::PERFORMERS ) === $answer && Blocks::one( $s->get( $main ), PageTexts::MONTH ) === '2026-11'
	&& $s->get( $snap ) === $snapText,
	'FW2 a state change writes the page alone: one save, the state block moves, the month, the performers and the snapshot as before' );

// FW3: a base that moved before the first save: BASE MOVED, nothing saved.
[ $s ] = $fresh();
$s->put( $main, 'a hand edit', 'x' );
$before = $s->saves;
$moved = false;
try {
	// the page moves between the writer's read and its check: simulate with a store that moves it on the first re-read
	$racing = new class( $s ) implements PageStore {
		public int $gets = 0;
		public function __construct( private FwStore $s ) {
		}
		public function get( string $title ): ?string {
			$t = $this->s->get( $title );
			if ( ++$this->gets === 2 ) {
				$this->s->put( $title, 'moved', 'x' );
			}
			return $t;
		}
		public function exists( string $title ): bool {
			return $this->s->exists( $title );
		}
		public function put( string $title, string $text, string $summary ): void {
			$this->s->put( $title, $text, $summary );
		}
		public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
			return $this->s->casPut( $title, $expected, $text, $summary, $actor );
		}
		public function appendAs( string $title, string $line, string $summary, string $actor ): string {
			return $this->s->appendAs( $title, $line, $summary, $actor );
		}
	};
	( new FleetWriter( $racing, $titles ) )->publish( '2026-11', $snapText, $page );
} catch ( PageFault $e ) {
	$moved = str_contains( $e->getMessage(), 'BASE MOVED' );
}
G::ok( $moved && $s->saves === $before && $s->get( $snap ) === null && $s->get( $main ) === 'moved', 'FW3 a base that moved before the first save refuses the whole write, nothing saved' );

// FW3: a publication between the caller's read and stateOnly() is not overwritten (the caller's page is the base); a page of another month is refused.
[ $s, , $w ] = $fresh();
$w->publish( '2026-11', $snapText, $page );
$read = $s->get( $main );
$next = PageTexts::topPerformers( '2026-12', $answer, 'PUBLISHED' );
$w->publish( '2026-12', PageTexts::topPerformers( '2026-12', $answer ), $next );
$s->saves = [];
G::refuses( static fn () => $w->stateOnly( '2026-12', PageTexts::topPerformersState( $read, 'SOURCE FAILING s' ), $read ), PageFault::class, 'MONTH MISMATCH',
	'FW3 a state change built on a page whose month is not the one named is refused' );
$read2 = $s->get( $main );
$w->publish( '2026-12', PageTexts::topPerformers( '2026-12', $answer ), $next );
$s->put( $main, $read2 . "\n<!-- raced -->", 'x' );
G::refuses( static fn () => $w->stateOnly( '2026-12', PageTexts::topPerformersState( $read2, 'SOURCE FAILING s' ), $read2 ), PageFault::class, 'BASE MOVED',
	'FW3 a page changed after the caller read it is not overwritten by a state change' );
G::ok( $s->saves === [] && str_contains( (string)$s->get( $main ), 'raced' ), 'FW3 the racing text stands, nothing saved' );

// FW4: the page moves between the snapshot's save and its own: BASE MOVED, the page not written.
[ $s, , $w ] = $fresh();
$s->before[$main] = static function () use ( $s, $main ): void {
	$s->put( $main, 'an edit between', 'x' );
};
G::refuses( static fn () => $w->publish( '2026-11', $snapText, $page ), PageFault::class, 'BASE MOVED', 'FW4 a page that moves while the write saves is refused' );
G::ok( $s->saves === [ $snap ] && $s->get( $main ) === 'an edit between',
	'FW4 the snapshot alone was saved, the page (the commit marker) not written over the edit' );

// FW5: a month's snapshot is not rewritten with other text; a retry with the same text passes; a state change before any publication has no page to read.
[ $s, , $w ] = $fresh();
$w->publish( '2026-11', $snapText, $page );
$s->saves = [];
G::refuses( static fn () => $w->publish( '2026-11', PageTexts::topPerformers( '2026-11', 'other' ), $page ), PageFault::class, 'SNAPSHOT EXISTS',
	'FW5 a snapshot is never rewritten with other text' );
$w->publish( '2026-11', $snapText, $page );
G::ok( $s->saves === [], 'FW5 the same texts again save nothing' );
G::refuses( static fn () => PageTexts::topPerformersState( null, 'SOURCE FAILING x' ), PageFault::class, 'no month',
	'FW5 a state change with no prior page writes nothing' );
G::refuses( static fn () => $w->publish( '2026-13', $snapText, $page ), PageFault::class, 'not a month', 'FW5 a month outside YYYY-MM is refused before any read' );

// FW6: the texts are the Calculator's answer carried whole; a payload that could open or close a block, an empty answer, a state outside its form are refused; no JSON of PHP's own.
$src = (string)file_get_contents( dirname( __DIR__ ) . '/includes/FleetWriter.php' ) . (string)file_get_contents( dirname( __DIR__ ) . '/includes/PageTexts.php' );
G::ok( Blocks::one( $page, PageTexts::PERFORMERS ) === $answer && Blocks::one( $snapText, PageTexts::PERFORMERS ) === $answer
	&& PageTexts::readTopState( $snapText ) === null && PageTexts::readTopState( $page ) === 'PUBLISHED'
	&& preg_match( '/json_encode|json_decode/', $src ) === 0,
	'FW6 the performers are the Calculator\'s text carried through byte for byte, the snapshot has no state block, and the writer and texts read and write no JSON' );
G::refuses( static fn () => PageTexts::topPerformers( '2026-11', "x</pre>\ny", 'PUBLISHED' ), PageFault::class, 'payload', 'FW6 a payload that closes a block is refused' );
G::refuses( static fn () => PageTexts::topPerformers( '2026-11', '', 'PUBLISHED' ), PageFault::class, 'none given', 'FW6 an empty answer is refused' );
G::refuses( static fn () => PageTexts::topPerformers( '2026-11', $answer, 'MAYBE' ), PageFault::class, 'not a top performer state', 'FW6 a state outside its form is refused' );

exit( G::report( 'fleet writer' ) );
