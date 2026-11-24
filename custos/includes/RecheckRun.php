<?php
/**
 * RecheckRun: one run of the bibliography recheck, RecheckJob's body, after the frame's context
 * check and lane-5 admission (docs/design/pma_custos_jobs.md "Bibliography recheck"):
 *  1. the REGISTRY DECLARATIONS: the block pma-registries of the DECLARATIONS volumes under the
 *     Declarer's root (Volume 1 upward to the first absent page; the latest volume that carries the
 *     block holds them), read through `canonical canonical_json`; none, or an empty list: NOTHING
 *     DUE, detail NO DECLARATION;
 *  2. the entries: of every UWC whose INDEX AND BADGE page states LIVE and whose DRAFT UWC page
 *     states the BIBLIOGRAPHY SETTING ON or CLOSED, each bibliography volume (Volume 1 upward to the
 *     first absent page), its block pma-bibliography read through `canonical canonical_json`; a
 *     volume that does not read, or an entry without its bib_id, item and identifiers, is passed
 *     over and counted unread. Only the OPEN volume's entries are rechecked: the last volume (its
 *     successor absent) holding fewer than BIBLIO VOLUME SIZE entries (a volume whose entries are all
 *     landed is FROZEN, TPS 5.21.8, 5.21.22); a UWC whose last volume is full, or does not read, has
 *     none. The entries of a FROZEN volume are counted `frozen`, and `biblio recheck_urls` over them
 *     with the day's cap spent (so nothing is taken) counts those due, `frozen_due`, named in the
 *     detail: reported, never looked up, never written (Permissions gives a FROZEN volume no write);
 *  3. `biblio recheck_urls` over the open volumes' entries with the day's lookups so far (read before
 *     anything else of the run, today()): the entries taken (oldest CHECK date first, within BIBLIO
 *     RECHECK BATCH and BIBLIO LOOKUP CAP) and their first-round URLs;
 *  4. each URL fetched through the Fetcher (FetchGuard's guards), then `biblio recheck_batch` with
 *     every lookup of the run; a second-round lookup it names is fetched and the call made again, at
 *     most self::ROUNDS calls. A lookup past BIBLIO LOOKUP TIME, the day's cap or the run's own
 *     allowance (self::RUN_ALLOWANCE) is not made,
 *     and a fetch refused or failed is no answer (status and text null): the Calculator keeps the
 *     prior lines (FAILED). Only the FetchFault's word is read, so no contact value reaches a page,
 *     the run record or an answer;
 *  5. for each UWC with an entry CHANGED, one landing (PageWriter, the open volume named to its
 *     fence, the successor's absence read again at commit), block `recheck-<date>`: its open
 *     volume, rewritten whole as `canonical
 *     canonical_json` writes the entries with the two lines the Calculator answered, then its INDEX
 *    AND BADGE page last, the commit marker, carried as read. An entry UNCHANGED, PENDING, FAILED or
 *     REFUSED writes nothing. A volume, or the INDEX AND BADGE page, whose text at landing is not the
 *     text the run read in step 2 (a UWC retired since, say) refuses that UWC's landing, nothing of it
 *     saved (counted moved); the other UWCs land.
 * PHP compares nothing: the CHECK and NOTICES lines are the Calculator's answer, written as given.
 * Each entry goes to the Calculator under a run key of its own (`bib_id` there is a label), so the
 * entries of two UWCs never meet in one key.
 *
 * The host a lookup may reach is the declared template's own (the block pma-registries on the
 * DECLARATIONS page), checked by FetchGuard on every hop. The other values the fetch needs (PACING,
 * TIMEOUT, where the contact value goes) are this class's table by registry kind until the
 * declaration's form carries them: `biblio url` admits kind, name and template alone.
 *
 * The day's cap across runs: today() counts every recheck run begun this UTC day but this one: an
 * ended run by its lookups, a run not ended (running now, or killed: a timeout, a fatal error, the
 * process ended) at self::RUN_ALLOWANCE, the most lookups a run makes, whatever it has made. The
 * frame inserts a run's row before its body runs, and RecheckJob runs outside a transaction round,
 * so the row is seen by every run that reads after it: of two runs at once the one that reads later
 * counts the other's allowance, and the day's lookups stay within BIBLIO LOOKUP CAP. What is left:
 * a killed run's allowance stays reserved for the rest of the day (the cap errs low, never high);
 * a run begun before midnight UTC counts its lookups to the day it began.
 *
 * Counts in the run record: uwcs, volumes, unread, frozen, frozen_due, due, taken, backlog, lookups (made), not_made,
 * failed (by FetchFault word in fetch_words), changed, unchanged, pending, refused, entries_failed,
 * pages (saved), moved, lookups_today (the day's count after this run), digests (each raw download's
 * SHA-256; the download itself is neither stored nor published). Every row the run ends carries them,
 * the early NOTHING DUE and REFUSED included; a fault after a lookup was made ends the run FAULT (or
 * INTEGRITY HALT) here, with the counts, so the lookups it made still count for the day.
 */

namespace Custos;

use JsonException;
use stdClass;
use Throwable;

final class RecheckRun {
	/** The landing block's prefix; the run's UTC date follows. */
	public const BLOCK = 'recheck-';
	public const NO_DECLARATION = 'NO DECLARATION';
	public const NONE_DUE = 'none due';
	/** BIBLIO LOOKUP TIME (seconds) and BIBLIO LOOKUP CAP (lookups a day), BibliographyTuning in Principia/Parameters.lean. */
	public const LOOKUP_TIME = 120;
	public const LOOKUP_CAP = 2000;
	/** The most `recheck_batch` calls of a run: the first round and the second rounds it names. */
	public const ROUNDS = 3;
	/** BIBLIO RECHECK BATCH (identifiers a run), BibliographyTuning in Principia/Parameters.lean. */
	public const RECHECK_BATCH = 50;
	/** The most lookups one run makes, and what an unended run of the day counts for: a batch a round. */
	public const RUN_ALLOWANCE = self::ROUNDS * self::RECHECK_BATCH;
	/** BIBLIO VOLUME SIZE, entries a bibliography volume (biblioVolumeSize in Principia/Parameters.lean). */
	public const BIBLIO_VOLUME_SIZE = 5;
	/** The most volumes read of one page series. */
	public const MAX_VOLUMES = 1000;
	/** The run records looked back over (of every batch job) for the day's count of lookups. */
	public const LOOK_BACK = 500;
	/** Seconds for one fetch, redirects included. */
	public const TIMEOUT = 30;
	/** PACING by registry kind, seconds between two calls to one registry (arXiv: 3); 1 for a kind not named. */
	public const PACING = [ 'ARXIV' => 3 ];
	/** Where a registry's contact value goes, by registry kind; none is sent for a kind not named. */
	public const CONTACT = [
		'DOI-RA' => [ 'in' => 'agent' ],
		'DOI-CROSSREF' => [ 'in' => 'agent' ],
		'DOI-DATACITE' => [ 'in' => 'agent' ],
		'PMID' => [ 'in' => 'query', 'param' => 'email' ],
		'PMCID' => [ 'in' => 'query', 'param' => 'email' ],
	];
	private const JSON = JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_PRESERVE_ZERO_FRACTION | JSON_THROW_ON_ERROR;

	/**
	 * The body the frame runs: fn( Calculator ): array{outcome, detail, counts}.
	 *
	 * @param callable():string[] $prefixes the UWCs' record prefixes
	 * @param callable|null $clock fn(): int, seconds (default: time); the run's date and its lookup time
	 */
	public static function bodyOf( PageStore $store, PageTitles $titles, Fetcher $fetcher, JobRunStore $runs,
		callable $prefixes, ?callable $clock = null
	): callable {
		$clock ??= static fn (): int => time();
		// $own: the run's own row, which the frame passes (BatchJob::run); null when no frame runs it.
		return static function ( Calculator $calc, ?int $own = null ) use ( $store, $titles, $fetcher, $runs, $prefixes, $clock ): array {
			// PHP writes a float as its shortest text only under serialize_precision -1, as Landing sets it.
			$precision = (string)ini_get( 'serialize_precision' );
			ini_set( 'serialize_precision', '-1' );
			$run = new self( $calc, $store, $titles, $fetcher, $runs, $clock, $own );
			try {
				return $run->run( $prefixes );
			} catch ( Throwable $e ) {
				return $run->fault( $e );
			} finally {
				ini_set( 'serialize_precision', $precision );
			}
		};
	}

	/** The JSON of every request the run builds. */
	public static function json( mixed $v ): string {
		return json_encode( $v, self::JSON );
	}

	/** @var callable */
	private $clock;
	private int $started = 0;
	private string $date = '';
	private int $prior = 0;
	private array $counts = [ 'uwcs' => 0, 'volumes' => 0, 'unread' => 0, 'frozen' => 0, 'frozen_due' => 0, 'due' => 0, 'taken' => 0, 'backlog' => 0,
		'lookups' => 0, 'not_made' => 0, 'failed' => 0, 'changed' => 0, 'unchanged' => 0, 'pending' => 0,
		'refused' => 0, 'entries_failed' => 0, 'pages' => 0, 'moved' => 0, 'lookups_today' => 0 ];
	/** @var array<string,int> */
	private array $words = [];
	/** @var string[] */
	private array $digests = [];
	/** @var array<string,array{0:string,1:int,2:int}> run key => [prefix, volume, index] */
	private array $where = [];
	/** @var array<string,array<int,array{text:string,entries:array}>> prefix => volume => its text as read, its entries */
	private array $volumes = [];
	/** @var array<string,int> prefix => its open bibliography volume, the one the run may write */
	private array $open = [];
	/** @var stdClass[] the entries of FROZEN volumes, as recheck_urls reads them: reported, never looked up */
	private array $frozen = [];
	/** @var array<string,string> prefix => its INDEX AND BADGE page's text as the run read it */
	private array $badges = [];
	/** @var array<string,stdClass> registry kind => its first declaration */
	private array $byKind = [];

	public function __construct( private Calculator $calc, private PageStore $store, private PageTitles $titles,
		private Fetcher $fetcher, private JobRunStore $runs, callable $clock, private ?int $own = null
	) {
		$this->clock = $clock;
	}

	/** @param callable():string[] $prefixes the UWCs' record prefixes, asked once the declarations are read */
	public function run( callable $prefixes ): array {
		$this->started = ( $this->clock )();
		$this->date = gmdate( 'Y-m-d', $this->started );
		$this->prior = $this->today();
		$declText = $this->declarations();
		$decls = $declText === null ? null : $this->read( $declText );
		if ( !is_array( $decls ) || $decls === [] || !array_is_list( $decls ) ) {
			return $this->answer( 'NOTHING DUE', self::NO_DECLARATION );
		}
		foreach ( $decls as $d ) {
			if ( $d instanceof stdClass && is_string( $d->kind ?? null ) && !isset( $this->byKind[$d->kind] ) ) {
				$this->byKind[$d->kind] = $d;
			}
		}
		$entries = [];
		foreach ( $prefixes() as $p ) {
			if ( is_string( $p ) && PageTitles::isPrefix( $p ) ) {
				$this->gather( $p, $entries );
			}
		}
		$this->reportFrozen( $decls );
		if ( $entries === [] ) {
			return $this->answer( 'NOTHING DUE', self::NONE_DUE );
		}
		$urls = $this->ask( 'recheck_urls', [
			'entries' => array_map( static fn ( array $e ): stdClass => (object)[ 'bib_id' => $e['key'],
				'identifiers' => $e['entry']->identifiers, 'check_line' => $e['entry']->check_line ?? null ], $entries ),
			'declarations' => $decls, 'date' => $this->date, 'lookups_today' => $this->prior ] );
		if ( isset( $urls['refused'] ) ) {
			return $this->answer( 'REFUSED', 'recheck_urls: ' . $urls['refused'] );
		}
		$this->counts['due'] = is_int( $urls['due'] ?? null ) ? $urls['due'] : 0;
		$this->counts['backlog'] = is_int( $urls['backlog'] ?? null ) ? $urls['backlog'] : 0;
		$taken = array_flip( array_map( 'strval', is_array( $urls['taken'] ?? null ) ? $urls['taken'] : [] ) );
		$this->counts['taken'] = count( $taken );
		if ( $taken === [] ) {
			return $this->answer( 'NOTHING DUE', self::NONE_DUE );
		}
		$batch = [];
		foreach ( $entries as $e ) {
			if ( isset( $taken[$e['key']] ) ) {
				$o = (object)[ 'bib_id' => $e['key'], 'item' => $e['entry']->item, 'identifiers' => $e['entry']->identifiers ];
				foreach ( [ 'check_line', 'notices_line' ] as $k ) {
					if ( isset( $e['entry']->$k ) ) {
						$o->$k = $e['entry']->$k;
					}
				}
				$batch[] = $o;
			}
		}
		$lookups = [];
		$this->fetchAll( is_array( $urls['lookups'] ?? null ) ? $urls['lookups'] : [], $lookups );
		for ( $round = 1; ; $round++ ) {
			$ans = $this->ask( 'recheck_batch', [ 'entries' => $batch, 'lookups' => array_values( $lookups ),
				'declarations' => $decls, 'date' => $this->date ] );
			if ( isset( $ans['refused'] ) ) {
				return $this->answer( 'REFUSED', 'recheck_batch: ' . $ans['refused'] );
			}
			$owed = is_array( $ans['lookups'] ?? null ) ? $ans['lookups'] : [];
			if ( $owed === [] || $round >= self::ROUNDS || !$this->fetchAll( $owed, $lookups ) ) {
				break;
			}
		}
		$states = [ 'CHANGED' => 'changed', 'UNCHANGED' => 'unchanged', 'PENDING' => 'pending', 'FAILED' => 'entries_failed',
			'REFUSED' => 'refused' ];
		$changed = [];
		foreach ( is_array( $ans['entries'] ?? null ) ? $ans['entries'] : [] as $e ) {
			$state = is_array( $e ) && is_string( $e['state'] ?? null ) ? $e['state'] : '';
			if ( isset( $states[$state] ) ) {
				$this->counts[$states[$state]]++;
			}
			$key = is_array( $e ) && is_string( $e['bib_id'] ?? null ) ? $e['bib_id'] : '';
			if ( $state === 'CHANGED' && isset( $this->where[$key] ) && is_string( $e['check_line'] ?? null ) ) {
				$changed[$key] = [ $e['check_line'], is_string( $e['notices_line'] ?? null ) ? $e['notices_line'] : null ];
			}
		}
		$this->land( $changed );
		return $this->answer( 'DONE', $this->counts['changed'] . ' changed, ' . $this->counts['pages'] . ' page(s) saved' );
	}

	/** The REGISTRY DECLARATIONS' payload: the latest DECLARATIONS volume's block pma-registries; null when none carries one. */
	private function declarations(): ?string {
		$found = null;
		for ( $v = 1; $v <= self::MAX_VOLUMES; $v++ ) {
			$text = $this->store->get( $this->titles->declarationsVolume( $v ) );
			if ( $text === null ) {
				break;
			}
			$p = PageTexts::readRegistries( $text );
			if ( $p !== null ) {
				$found = $p;
			}
		}
		return $found;
	}

	/** The entries of the UWC $p, when it is LIVE and its setting ON or CLOSED, each under a run key. */
	private function gather( string $p, array &$entries ): void {
		try {
			$badge = $this->store->get( $this->titles->index( $p ) );
			$facts = PageTexts::facts( $badge );
			if ( ( $facts['retired'] ?? true ) !== false ) {
				return;
			}
			$setting = Blocks::one( $this->store->get( $this->titles->draft( $p ) ), Landing::SETTING ) ?? Landing::SETTING_DEFAULT;
		} catch ( PageFault ) {
			$this->counts['unread']++;
			return;
		}
		if ( $setting !== 'ON' && $setting !== 'CLOSED' ) {
			return;
		}
		$this->counts['uwcs']++;
		$this->badges[$p] = $badge;
		$read = [];
		$last = null;
		for ( $v = 1; $v <= self::MAX_VOLUMES; $v++ ) {
			$text = $this->store->get( $this->titles->bibliographyVolume( $p, $v ) );
			if ( $text === null ) {
				$last = $v - 1;
				break;
			}
			try {
				$payload = PageTexts::readBibliography( $text );
			} catch ( PageFault ) {
				$this->counts['unread']++;
				continue;
			}
			$list = $payload === null ? null : $this->read( $payload );
			if ( !is_array( $list ) || !array_is_list( $list ) ) {
				$this->counts['unread']++;
				continue;
			}
			$this->counts['volumes']++;
			$read[$v] = [ 'text' => $text, 'entries' => $list ];
		}
		// The open volume: the last one (its successor absent), read, short of BIBLIO VOLUME SIZE. A UWC
		// whose volumes run past MAX_VOLUMES, whose last volume does not read or is full has none.
		$open = $last !== null && $last >= 1 && isset( $read[$last] ) && count( $read[$last]['entries'] ) < self::BIBLIO_VOLUME_SIZE
			? $last : null;
		foreach ( $read as $v => $vol ) {
			if ( $v === $open ) {
				$this->open[$p] = $v;
				$this->volumes[$p][$v] = $vol;
			}
			foreach ( $vol['entries'] as $i => $e ) {
				if ( !$e instanceof stdClass || !is_string( $e->bib_id ?? null ) || !property_exists( $e, 'item' )
					|| !( ( $e->identifiers ?? null ) instanceof stdClass )
					|| ( isset( $e->check_line ) && !is_string( $e->check_line ) )
					|| ( isset( $e->notices_line ) && !is_string( $e->notices_line ) ) ) {
					$this->counts['unread']++;
					continue;
				}
				$key = 'e' . ( count( $this->where ) + count( $this->frozen ) );
				if ( $v !== $open ) {
					$this->counts['frozen']++;
					$this->frozen[] = (object)[ 'bib_id' => $key, 'identifiers' => $e->identifiers, 'check_line' => $e->check_line ?? null ];
					continue;
				}
				$this->where[$key] = [ $p, $v, $i ];
				$entries[] = [ 'key' => $key, 'entry' => $e ];
			}
		}
	}

	/**
	 * The FROZEN volumes' entries due, counted by `biblio recheck_urls` with the day's cap spent, so
	 * that it takes none: frozen_due. A refusal counts every one of them due (the report errs high).
	 */
	private function reportFrozen( array $decls ): void {
		if ( $this->frozen === [] ) {
			return;
		}
		$r = $this->ask( 'recheck_urls', [ 'entries' => $this->frozen, 'declarations' => $decls, 'date' => $this->date,
			'lookups_today' => self::LOOKUP_CAP ] );
		$this->counts['frozen_due'] = !isset( $r['refused'] ) && is_int( $r['due'] ?? null ) ? $r['due'] : count( $this->frozen );
	}

	/**
	 * Fetch each lookup of $owed not yet in $lookups and add it with its status and text (200 and the
	 * body; null and null when the fetch failed or was not made). False when none was new.
	 */
	private function fetchAll( array $owed, array &$lookups ): bool {
		$new = false;
		foreach ( $owed as $l ) {
			if ( !is_array( $l ) ) {
				continue;
			}
			$id = implode( "\n", [ (string)( $l['bib_id'] ?? '' ), (string)( $l['kind'] ?? '' ), (string)( $l['registry'] ?? '' ) ] );
			if ( isset( $lookups[$id] ) ) {
				continue;
			}
			$new = true;
			[ $status, $text ] = $this->fetchOne( (string)( $l['registry'] ?? '' ), (string)( $l['url'] ?? '' ) );
			$lookups[$id] = [ 'bib_id' => $l['bib_id'] ?? null, 'kind' => $l['kind'] ?? null, 'identifier' => $l['identifier'] ?? null,
				'registry' => $l['registry'] ?? null, 'url' => $l['url'] ?? null, 'status' => $status, 'text' => $text ];
		}
		return $new;
	}

	/** One lookup through the Fetcher: [200, the body], or [null, null]. */
	private function fetchOne( string $registry, string $url ): array {
		$d = $this->byKind[$registry] ?? null;
		if ( $d === null || $url === '' || ( ( $this->clock )() - $this->started ) >= self::LOOKUP_TIME
			|| $this->prior + $this->counts['lookups'] >= self::LOOKUP_CAP || $this->counts['lookups'] >= self::RUN_ALLOWANCE ) {
			$this->counts['not_made']++;
			return [ null, null ];
		}
		$host = parse_url( str_replace( '{ID}', 'x', is_string( $d->template ?? null ) ? $d->template : '' ), PHP_URL_HOST );
		$source = is_string( $d->name ?? null ) && $d->name !== '' ? $d->name : $registry;
		$declared = [ 'hosts' => is_string( $host ) ? [ strtolower( $host ) ] : [], 'timeout' => self::TIMEOUT,
			'pacing' => self::PACING[$registry] ?? 1 ];
		if ( isset( self::CONTACT[$registry] ) ) {
			$declared['contact'] = self::CONTACT[$registry];
		}
		$this->counts['lookups']++;
		try {
			$body = $this->fetcher->fetch( $source, $url, $declared );
		} catch ( FetchFault $e ) {
			$this->counts['failed']++;
			$this->words[$e->word] = ( $this->words[$e->word] ?? 0 ) + 1;
			return [ null, null ];
		}
		$this->digests[] = FetchGuard::digest( $body );
		if ( !mb_check_encoding( $body, 'UTF-8' ) ) {
			$this->counts['failed']++;
			$this->words['ENCODING'] = ( $this->words['ENCODING'] ?? 0 ) + 1;
			return [ null, null ];
		}
		return [ 200, $body ];
	}

	/**
	 * One landing per UWC with an entry changed: its volumes in volume order, the badge last as read.
	 * The badge is compared first: a text other than the one gather() read (the UWC retired, or any
	 * other landing on it since) refuses the UWC's landing, BASE MOVED, nothing of it saved.
	 */
	private function land( array $changed ): void {
		$touched = [];
		foreach ( $changed as $key => [ $check, $notices ] ) {
			[ $p, $v, $i ] = $this->where[$key];
			$e = $this->volumes[$p][$v]['entries'][$i];
			$e->check_line = $check;
			if ( $notices === null ) {
				unset( $e->notices_line );
			} else {
				$e->notices_line = $notices;
			}
			$touched[$p][$v] = true;
		}
		ksort( $touched, SORT_STRING );
		$w = new PageWriter( $this->store, $this->titles );
		foreach ( $touched as $p => $vols ) {
			$p = (string)$p;
			ksort( $vols );
			try {
				$w->begin( $p, self::BLOCK . $this->date, [], [ PageClass::BIBLIOGRAPHY_OPEN ], $this->open[$p] ?? null );
				$badge = $this->titles->index( $p );
				if ( $w->read( $badge ) !== ( $this->badges[$p] ?? null ) ) {
					throw new PageFault( 'BASE MOVED: the INDEX AND BADGE page changed since the run read it; nothing saved' );
				}
				foreach ( array_keys( $vols ) as $v ) {
					$title = $this->titles->bibliographyVolume( $p, $v );
					if ( $w->read( $title ) !== $this->volumes[$p][$v]['text'] ) {
						throw new PageFault( 'BASE MOVED: a bibliography volume changed since the run read it; nothing saved' );
					}
					$text = $this->askText( 'canonical', 'canonical_json', '{"value":' . self::json( $this->volumes[$p][$v]['entries'] ) . '}' );
					if ( !is_string( $text ) ) {
						throw new PageFault( 'the Calculator did not write the volume\'s entries; nothing saved' );
					}
					$w->put( $title, PageTexts::bibliography( $p, $v, $text ) );
				}
				$w->put( $badge, $this->badges[$p] );
				$this->counts['pages'] += count( $w->commit() );
			} catch ( PageFault ) {
				$this->counts['moved']++;
			}
		}
	}

	/**
	 * The day's lookups before this run: over every recheck run begun this UTC day but this one (the
	 * row $own), the sum of the counts "lookups" of the runs ended, whatever their outcome, and
	 * self::RUN_ALLOWANCE for each run not ended (running now, or killed before it ended); or the
	 * greatest "lookups_today" of an ended run when that is more (a row's lookups_today is the count
	 * it read plus its own, so the greater errs high, never low). A row ended without the count
	 * (DEFERRED, JOB CONTEXT) made none. Rows are walked back from the latest recheck run to the
	 * first begun before today, at most self::LOOK_BACK records.
	 */
	private function today(): int {
		$cur = $this->runs->last( BatchJob::RECHECK );
		if ( $cur === null ) {
			return 0;
		}
		$day = gmdate( 'Ymd', $this->started );
		$sum = 0;
		$carried = 0;
		for ( $id = (int)$cur['id'], $n = 0; $id >= 1 && $n < self::LOOK_BACK; $id--, $n++ ) {
			$row = $id === (int)$cur['id'] ? $cur : $this->runs->get( $id );
			if ( $row === null || $row['job'] !== BatchJob::RECHECK ) {
				continue;
			}
			if ( !str_starts_with( (string)$row['started'], $day ) ) {
				break;
			}
			if ( $id === $this->own ) {
				continue;
			}
			if ( $row['outcome'] === null ) {
				$sum += self::RUN_ALLOWANCE;
				continue;
			}
			$c = json_decode( (string)$row['counts'], true );
			if ( is_array( $c ) && is_int( $c['lookups'] ?? null ) && $c['lookups'] > 0 ) {
				$sum += $c['lookups'];
			}
			if ( is_array( $c ) && is_int( $c['lookups_today'] ?? null ) && $c['lookups_today'] > $carried ) {
				$carried = $c['lookups_today'];
			}
		}
		return max( $sum, $carried );
	}

	/**
	 * A fault of the run, ended here when a lookup was made (else thrown on to the frame, which ends
	 * it as before): the outcome and detail the frame gives a fault, with the run's counts, so the day's
	 * lookups count them. The fault goes to the error channel as the frame sends it.
	 */
	private function fault( Throwable $e ): array {
		if ( $this->counts['lookups'] === 0 ) {
			throw $e;
		}
		if ( function_exists( 'wfDebugLog' ) ) {
			wfDebugLog( BatchJob::LOG, 'batch job ' . BatchJob::RECHECK . ': ' . get_class( $e ) . ': ' . $e->getMessage() );
		}
		$d = Refusal::detail( $e );
		if ( $d['refused'] === 'INTEGRITY HALT' ) {
			return $this->answer( 'INTEGRITY HALT', (string)$d['detail'] );
		}
		return $this->answer( 'FAULT', (string)( $d['detail'] ?? $d['refused'] . ': ' . ( $d['class'] ?? '' ) ) );
	}

	/**
	 * A page's payload read by the Calculator (`canonical canonical_json`) and decoded, objects as
	 * objects; null when the Calculator refuses it, or when PHP cannot hold the value it read exactly
	 * (the value written again, its canonical text is not the first), as Landing reads a text.
	 */
	private function read( string $payload ): mixed {
		$canonical = $this->askText( 'canonical', 'canonical_json', '{"value":' . $payload . '}' );
		if ( !is_string( $canonical ) ) {
			return null;
		}
		try {
			$value = json_decode( $canonical, false, 512, JSON_THROW_ON_ERROR );
			$again = self::json( $value );
		} catch ( JsonException ) {
			return null;
		}
		if ( $again !== $canonical && $this->askText( 'canonical', 'canonical_json', '{"value":' . $again . '}' ) !== $canonical ) {
			return null;
		}
		return $value;
	}

	/** The Calculator's answer to `biblio <fn>`; ['refused' => its words] for its refusal. */
	private function ask( string $fn, array $request ): array {
		$r = $this->calc->call( 'biblio', $fn, self::json( $request ) );
		if ( $r['exit'] !== 0 ) {
			return [ 'refused' => $r['refused'] . ': ' . $r['detail'] ];
		}
		if ( !is_array( $r['value'] ) ) {
			throw new CalculatorFault( "biblio $fn answered no object", CalculatorFault::ANSWER_FORM, 'biblio', $fn );
		}
		return $r['value'];
	}

	/** The Calculator's answer, or null for its refusal. */
	private function askText( string $family, string $fn, string $json ): mixed {
		$r = $this->calc->call( $family, $fn, $json );
		return $r['exit'] === 0 ? $r['value'] : null;
	}

	private function answer( string $outcome, string $detail ): array {
		$this->counts['lookups_today'] = $this->prior + $this->counts['lookups'];
		if ( $this->counts['frozen_due'] > 0 ) {
			$detail .= '; ' . $this->counts['frozen_due'] . ' due in FROZEN volumes, not rewritten';
		}
		$counts = $this->counts;
		if ( $this->words !== [] ) {
			ksort( $this->words, SORT_STRING );
			$counts['fetch_words'] = $this->words;
		}
		if ( $this->digests !== [] ) {
			$counts['digests'] = $this->digests;
		}
		return [ 'outcome' => $outcome, 'detail' => $detail, 'counts' => $counts ];
	}
}
