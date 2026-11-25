<?php
/**
 * reaudit_job.php: the cases RA1 to RA10 of the re-audit job (ReauditJob's body through the batch
 * frame) on the built pcalc, over FileStore and FileJobRunStore. A successor is made by hand (the
 * landing that makes one does not exist yet): the successor QQ and its source RR, their pages
 * written from the cases of vectors/reaudit_corpus.json. Its own runner until the harness takes
 * the cases in.
 *
 *   php custos/tests/reaudit_job.php
 *
 * Without .lake/build/bin/pcalc every case is skipped with its reason. Command line only.
 */

declare( strict_types=1 );

require_once __DIR__ . '/bootstrap.php';

use Custos\BatchJob;
use Custos\Blocks;
use Custos\Calculator;
use Custos\PageStore;
use Custos\PageTexts;
use Custos\PageTitles;
use Custos\ReauditJob;
use Custos\ShellRunner;
use Custos\Tests\AnyResidence;
use Custos\Tests\FileJobRunStore;
use Custos\Tests\FileStore;
use Custos\Tests\ProcRunner;

// ReauditJob is a MediaWiki job class; its body needs none of MediaWiki, so the two names it extends are stood in.
if ( !interface_exists( 'MediaWiki\JobQueue\GenericParameterJob' ) ) {
	eval( 'namespace MediaWiki\JobQueue; interface GenericParameterJob {}
		abstract class Job { public $params; public $removeDuplicates = false; public $executionFlags = 0;
			public function __construct( $command, $params = [] ) { $this->params = $params; }
			public function setLastError( $e ) {} }' );
}

$root = dirname( __DIR__, 2 );
$built = "$root/.lake/build/bin/pcalc";
if ( !is_file( $built ) || !is_executable( $built ) ) {
	G::skip( 'RA the re-audit job', 'no built pcalc in this clone (.lake/build/bin/pcalc); the re-audit job needs the Calculator itself' );
	exit( G::report( 'reaudit_job' ) );
}
echo "RA: on .lake/build/bin/pcalc\n";

$scratch = sys_get_temp_dir() . '/custos-reaudit-' . getmypid();
register_shutdown_function( static function () use ( $scratch ): void {
	foreach ( glob( "$scratch/*/*" ) ?: [] as $f ) {
		unlink( $f );
	}
	foreach ( glob( "$scratch/*" ) ?: [] as $d ) {
		rmdir( $d );
	}
	@rmdir( $scratch );
} );

$version = preg_match( '/^def version : String := "([^"]+)"$/m', (string)file_get_contents( "$root/Principia/Basic.lean" ), $m ) ? $m[1] : '';
$want = [ 'version' => $version, 'digest' => Calculator::digestOf( $built ) ];

/** The Calculator's runner: the built pcalc, every start logged, and a hook run before the batch's start. */
final class RaRunner implements ShellRunner {
	/** @var string[][] */
	public array $log = [];
	/** @var string[] the batch's answer lines */
	public array $answers = [];
	/** @var callable|null */
	public $beforeBatch = null;
	private ProcRunner $proc;
	public function __construct() {
		$this->proc = new ProcRunner();
	}
	public function run( array $argv, string $stdin ): array {
		$this->log[] = array_slice( $argv, 1 );
		$batch = array_slice( $argv, 1 ) === [ 'record', 'reaudit_batch' ];
		if ( $batch && $this->beforeBatch !== null ) {
			( $this->beforeBatch )();
		}
		$r = $this->proc->run( $argv, $stdin );
		if ( $batch ) {
			$this->answers[] = $r[1];
		}
		return $r;
	}
}

/** A store that logs each save made, in order. */
final class RaStore implements PageStore {
	/** @var string[] */
	public array $saves = [];
	public function __construct( public FileStore $inner ) {
	}
	public function get( string $title ): ?string {
		return $this->inner->get( $title );
	}
	public function exists( string $title ): bool {
		return $this->inner->exists( $title );
	}
	public function put( string $title, string $text, string $summary ): void {
		$this->saves[] = $title;
		$this->inner->put( $title, $text, $summary );
	}
	public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
		$ok = $this->inner->casPut( $title, $expected, $text, $summary, $actor );
		if ( $ok ) {
			$this->saves[] = $title;
		}
		return $ok;
	}
	public function appendAs( string $title, string $line, string $summary, string $actor ): string {
		$this->saves[] = $title;
		return $this->inner->appendAs( $title, $line, $summary, $actor );
	}
}

$flags = JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE;
$tool = new Calculator( $built, $want, new ProcRunner(), 'cli', new AnyResidence() );
/** The Calculator's canonical text of a value: the test's own calls, never the run's. */
$canon = static fn ( mixed $v ): string => (string)$tool->call( 'canonical', 'canonical_json', '{"value":' . json_encode( $v, $flags ) . '}' )['value'];

$corpus = json_decode( (string)file_get_contents( "$root/vectors/reaudit_corpus.json" ), false, 512, JSON_THROW_ON_ERROR );
$cases = [];
foreach ( $corpus->cases as $c ) {
	$cases[substr( $c->name, 0, 4 )] = $c;
}
$titles = new PageTitles( 'Principia Machina/UWC', 'Principia Machina' );
$runs = new FileJobRunStore( "$scratch/runs" );
$now = (int)gmmktime( 12, 0, 0, 10, 30, 2026 );
$tps = '0.4.0';
$params = [ 'successor' => 'QQ', 'source' => 'RR', 'gap_prefix' => 'QG', 'promotion_id' => 'QQ-90' ];
$digestA = str_repeat( 'a', 64 );
$digestB = str_repeat( 'b', 64 );

/** The badge page of $prefix over $n records: LIVE (or RETIRED), open volume 1, the seed's STRUCTURE TEST LINE. */
$badgeOf = static fn ( string $prefix, int $n, bool $retired = false ): string => PageTexts::badge( $prefix, [
	'calculator_digest' => $digestA, 'calculator_version' => '0.1.0', 'last_push' => '2026-09-28T12:00:00Z',
	'last_release' => null, 'record_count' => $n, 'research_assembly' => $digestB ], $retired, 1, PageTexts::STRUCTURE_NONE );

/** A store holding the successor QQ and its source RR as the case $id gives them. */
$n = 0;
$seed = static function ( string $id, bool $retired = false ) use ( &$n, $scratch, $cases, $titles, $canon, $badgeOf ): RaStore {
	$a = $cases[$id]->args;
	$store = new RaStore( new FileStore( $scratch . '/s' . ( ++$n ) ) );
	foreach ( [ 'QQ' => [ $a->dst_tfk, $a->dst_records ], 'RR' => [ $a->src_tfk, $a->src_records ] ] as $p => [ $tfk, $records ] ) {
		$t = $canon( $tfk );
		foreach ( PageTitles::ZONES as $zone ) {
			$store->inner->put( $titles->researchAssembly( $p, $zone ), Blocks::render( 'assembly', $t ) . "\n", 'seed' );
		}
		$store->inner->put( $titles->registerVolume( $p, 1 ), PageTexts::register( $p, 1, $canon( $records ) ), 'seed' );
		$store->inner->put( $titles->index( $p ), $badgeOf( $p, count( $records ), $p === 'QQ' && $retired ), 'seed' );
	}
	return $store;
};

/** One run through the frame on a fresh Calculator object: [answer, runner, store, enqueued]. */
$run = static function ( RaStore $store, array $p, ?callable $before = null, ?array $expect = null )
	use ( $built, $want, $runs, $titles, $tps, $now ): array {
	$runner = new RaRunner();
	$runner->beforeBatch = $before;
	$calc = new Calculator( $built, $expect ?? $want, $runner, 'cli', new AnyResidence() );
	$enqueued = [];
	$body = ReauditJob::bodyOf( $store, $titles, $p, $tps, static fn (): int => $now,
		static function ( array $q ) use ( &$enqueued ): void {
			$enqueued[] = $q;
		} );
	$frame = new BatchJob( $calc, $runs, [ 'min_address_space' => 0 ], [ BatchJob::REAUDIT => $body ],
		static fn (): int => $now, static fn (): array => [ 7, 1000000 ], static function (): void {
		} );
	return [ $frame->run( BatchJob::REAUDIT ), $runner, $calc, $enqueued ];
};
$batchCalls = static fn ( RaRunner $r ): int => count( array_filter( $r->log, static fn ( array $a ): bool => $a === [ 'record', 'reaudit_batch' ] ) );
$ids = static fn ( array $records ): array => array_map( static fn ( $r ) => is_array( $r ) ? $r[0] : $r->ID, $records );
$regQQ = $titles->registerVolume( 'QQ', 1 );
$badgeQQ = $titles->index( 'QQ' );

// RA1: nothing pending (the job enqueued with no parameters, as Custos:Job enqueues it): NOTHING DUE, no batch, nothing written.
$s = $seed( 'RX03' );
[ $a, $rn ] = $run( $s, [] );
G::ok( $a['outcome'] === 'NOTHING DUE' && $a['detail'] === ReauditJob::NONE_PENDING && $batchCalls( $rn ) === 0 && $s->saves === []
	&& $runs->get( $a['id'] )['outcome'] === 'NOTHING DUE',
	'RA1 no successor pending: NOTHING DUE (' . ReauditJob::NONE_PENDING . '), no reaudit_batch call, no page written', json_encode( $a ) );

// RA2: every inherited record passes its re-check. Nothing promoted (RX16): DONE, the register as given, nothing written.
// Re-promoted (RX02): DONE, every record's STATUS kept as the copy set it, the PROMOTION record appended.
$s = $seed( 'RX16' );
$before = $s->get( $regQQ );
[ $a, $rn ] = $run( $s, $params );
$s2 = $seed( 'RX02' );
[ $a2 ] = $run( $s2, $params );
$given = $cases['RX02']->args->dst_records;
$after = json_decode( (string)PageTexts::readRegister( $s2->get( $regQQ ) ), false, 512, JSON_THROW_ON_ERROR );
$kept = count( $after ) === count( $given ) + 1;
foreach ( $given as $i => $g ) {
	$kept = $kept && $after[$i]->ID === $g->ID && ( $after[$i]->STATUS ?? null ) === ( $g->STATUS ?? null );
}
G::ok( $a['outcome'] === 'DONE' && $a['detail'] === 'the re-audit changed nothing; no page written' && $s->saves === []
	&& $s->get( $regQQ ) === $before && $batchCalls( $rn ) === 1
	&& $a2['outcome'] === 'DONE' && $kept && is_array( $after[count( $given )] ) && $after[count( $given )][1] === 'PROMOTION'
	&& $s2->saves === [ $regQQ, $badgeQQ ],
	'RA2 every inherited record passes: DONE with every word kept; nothing promoted writes nothing, a re-promotion appends its PROMOTION record',
	json_encode( [ $a, $a2, $s2->saves ] ) );

// RA3: a failed re-check (RX03): its STATUS set by status_next on HOLD, one gap record opened, nothing struck.
$s = $seed( 'RX03' );
[ $a, $rn ] = $run( $s, $params );
$given = $cases['RX03']->args->dst_records;
$after = json_decode( (string)PageTexts::readRegister( $s->get( $regQQ ) ), false, 512, JSON_THROW_ON_ERROR );
$answer = json_decode( rtrim( $rn->answers[0] ?? '', "\n" ), false, 512, JSON_THROW_ON_ERROR );
$gaps = array_values( array_filter( $after, static fn ( $r ) => is_object( $r ) && ( $r->CLASS ?? '' ) === 'NAMED_GAP' ) );
$struck = array_filter( $after, static fn ( $r ) => is_object( $r ) && in_array( $r->STATUS ?? '', [ 'STRUCK', 'REFUTED' ], true ) );
G::ok( $a['outcome'] === 'DONE' && $answer[1]->STATUS === [ [ 'QQ-30', 'HELD' ] ] && count( $gaps ) === 1 && $gaps[0]->ID === 'QG-2'
	&& $gaps[0]->STATE === 'OPEN' && $gaps[0]->TRIGGER === 'the re-audit of QQ under RR' && $gaps[0]->LANDED === '2026-10-30T12:00:00Z'
	&& array_slice( $ids( $after ), 0, count( $given ) ) === $ids( $given ) && $struck === []
	&& $after[1]->ID === 'QQ-30' && $after[1]->STATUS === 'HELD',
	'RA3 a failed re-check: STATUS HELD by status_next on HOLD, one gap record QG-2 opened (OPEN, the trigger and the run\'s time), every record kept, nothing struck',
	json_encode( [ $a, $answer[1]->STATUS ?? null ] ) );

// RA4: one BASE MOVED (the register changed while the batch ran) enqueues the job again once, DEFERRED, nothing saved;
// the second (the run carrying moved 1) is REFUSED, nothing saved, not enqueued; the run enqueued, its base still, lands.
$s = $seed( 'RX03' );
$moved = null;
$move = static function () use ( $s, $regQQ, &$moved ): void {
	$moved = $s->get( $regQQ ) . "\n";
	$s->inner->tamper( $regQQ, $moved );
};
$badgeBefore = $s->get( $badgeQQ );
[ $m1, , , $q1 ] = $run( $s, $params, $move );
$p1 = $q1[0] ?? [];
[ $m2, , , $q2 ] = $run( $s, $p1, $move );
$unsaved = $s->saves === [] && $s->get( $regQQ ) === $moved && $s->get( $badgeQQ ) === $badgeBefore;
$s3 = $seed( 'RX03' );
[ $m3, , , $q3 ] = $run( $s3, $p1 );
G::ok( $m1['outcome'] === 'DEFERRED' && str_starts_with( $m1['detail'], 'BASE MOVED' ) && count( $q1 ) === 1
	&& $p1 === $params + [ 'moved' => 1 ] && $m2['outcome'] === 'REFUSED' && str_starts_with( $m2['detail'], 'BASE MOVED a second time' )
	&& $q2 === [] && $unsaved && json_decode( $m2['counts'], true )['moved'] === 2
	&& $m3['outcome'] === 'DONE' && $q3 === [] && $s3->saves === [ $regQQ, $badgeQQ ],
	'RA4 one BASE MOVED: DEFERRED, nothing saved, enqueued again once with moved 1; a second: REFUSED, nothing saved, not enqueued; the retry with its base still lands',
	json_encode( [ $m1, $m2, $m3, $q1 ] ) );

// RA5: one pcalc start per run beside the frame's (version, governor admit): one record reaudit_batch, no other call.
$s = $seed( 'RX03' );
[ $a, $rn, $calc ] = $run( $s, $params );
G::ok( $rn->log === [ [ 'version' ], [ 'governor', 'admit' ], [ 'record', 'reaudit_batch' ] ] && $calc->starts === 3,
	'RA5 one Calculator call per run: version and governor admit (the frame\'s), then record reaudit_batch once; no canonical, digest or view call', json_encode( $rn->log ) );

// RA6: the run record's counts, and the volume written equal to REGISTER byte for byte, the badge last with REGISTER's count.
$answer = json_decode( rtrim( $rn->answers[0], "\n" ), false, 512, JSON_THROW_ON_ERROR );
$register = $canon( $answer[1]->REGISTER );
$row = $runs->get( $a['id'] );
$badgeAfter = json_decode( (string)PageTexts::readBadge( $s->get( $badgeQQ ) ), true );
$badgeSeed = json_decode( (string)PageTexts::readBadge( $badgeOf( 'QQ', count( $cases['RX03']->args->dst_records ) ) ), true );
$expected = [ 'checks' => count( $answer[1]->CHECKS ), 'held' => 1, 'gaps' => 1, 'promoted' => count( $answer[1]->PROMOTED ),
	'records' => count( $answer[1]->REGISTER ), 'pages' => 2, 'moved' => 0 ];
G::ok( $row['outcome'] === 'DONE' && $row['counts'] === json_encode( $expected ) && $row['detail'] === $a['detail']
	&& PageTexts::readRegister( $s->get( $regQQ ) ) === $register && str_contains( $rn->answers[0], '"REGISTER":' . $register . ',"STATUS"' )
	&& $register !== $canon( $cases['RX03']->args->dst_records )
	&& $s->saves === [ $regQQ, $badgeQQ ] && $badgeAfter === array_replace( $badgeSeed, [ 'record_count' => $expected['records'] ] )
	&& PageTexts::facts( $s->get( $badgeQQ ) ) === [ 'retired' => false, 'open_volume' => 1 ]
	&& PageTexts::readStructure( $s->get( $badgeQQ ) ) === PageTexts::STRUCTURE_NONE,
	'RA6 the run record: DONE with the counts (checks, held, gaps, promoted, records, pages, moved); the volume written is REGISTER byte for byte, the badge last with its record_count, the rest carried',
	json_encode( [ $row, $expected, $badgeAfter ] ) );

// RA7: the batch's refusal (a PROMOTION ID already in the register, REC-57): REFUSED with the Calculator's word, nothing written.
$s = $seed( 'RX02' );
[ $a ] = $run( $s, [ 'promotion_id' => 'QQ-2' ] + $params );
G::ok( $a['outcome'] === 'REFUSED' && str_contains( $a['detail'], 'REC-57' ) && $s->saves === [],
	'RA7 the batch refuses (REC-57, the PROMOTION ID already in the register): REFUSED with the Calculator\'s word, nothing written', json_encode( $a ) );

// RA8: a successor that is not LIVE: REFUSED before the batch, nothing written.
$s = $seed( 'RX03', true );
[ $a, $rn ] = $run( $s, $params );
G::ok( $a['outcome'] === 'REFUSED' && $batchCalls( $rn ) === 0 && $s->saves === [],
	'RA8 a successor not LIVE: REFUSED, no reaudit_batch call, nothing written', json_encode( $a ) );

// RA9: parameters out of form (a gap prefix, a PROMOTION ID, moved): REFUSED, nothing read.
$bad = [];
foreach ( [ [ 'gap_prefix' => 'Q G' ], [ 'promotion_id' => 'QQ 90' ], [ 'moved' => 2 ], [ 'source' => null ] ] as $over ) {
	$s = $seed( 'RX03' );
	[ $a, $rn ] = $run( $s, $over + $params );
	$bad[] = $a['outcome'] === 'REFUSED' && str_contains( $a['detail'], 'nothing read' ) && $batchCalls( $rn ) === 0 && $s->saves === [];
}
G::ok( $bad === [ true, true, true, true ], 'RA9 parameters out of form: REFUSED, nothing read, no reaudit_batch call', json_encode( $bad ) );

// RA10: a Calculator that is not the expected one: INTEGRITY HALT, never started, nothing written.
$s = $seed( 'RX03' );
[ $a, $rn ] = $run( $s, $params, null, [ 'digest' => str_repeat( '0', 64 ) ] + $want );
G::ok( $a['outcome'] === 'INTEGRITY HALT' && $rn->log === [] && $s->saves === [],
	'RA10 a digest mismatch: INTEGRITY HALT, the binary never started, nothing written', json_encode( $a ) );

exit( G::report( 'reaudit_job' ) );
