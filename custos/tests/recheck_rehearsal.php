<?php
/**
 * recheck_rehearsal.php: the bibliography recheck job on the rehearsal wiki, its registries' payloads canned and served locally
 * (no request leaves the machine: the Fetcher is the one below, the guards of the live class are the harness's BR cases).
 *
 *   php maintenance/run.php <path>/custos/tests/recheck_rehearsal.php --prefix <a UWC seeded by Custos:SeedUwc>
 *
 * It sets the UWC's BIBLIOGRAPHY SETTING ON, writes its bibliography volume 1 with one entry whose CHECK date is long past and the
 * DECLARATIONS volume 1 with one registry (arXiv), as the system user Custos; reads the UWCs the job would run over from the page
 * table (RecheckJob's own listing); then runs the job's body through the batch frame over this wiki's page store, run table and
 * built Calculator, as the job runner does. Prints "recheck: <outcome>, <detail>", then "recheck: volume rewritten" when the volume
 * page carries the new CHECK line and was saved once by the landing, else "recheck: FAIL ..." and exit 1. The run's last row is
 * read back by `Custos:Job --last recheck` (rehearsal.sh).
 */

declare( strict_types=1 );

use Custos\BatchJob;
use Custos\Blocks;
use Custos\Calculator;
use Custos\DbJobRunStore;
use Custos\Fetcher;
use Custos\FetchFault;
use Custos\Landing;
use Custos\MwStore;
use Custos\PageTexts;
use Custos\PageTitles;
use Custos\RecheckJob;
use Custos\RecheckRun;

if ( defined( 'RUN_MAINTENANCE_IF_MAIN' ) ) {
	if ( !class_exists( 'CustosRecheckRehearsal', false ) ) {
		/** The maintenance script maintenance/run.php runs. */
		final class CustosRecheckRehearsal extends \MediaWiki\Maintenance\Maintenance {
			public function __construct() {
				parent::__construct();
				$this->addDescription( 'Custos: the bibliography recheck job on this wiki over canned registry payloads' );
				$this->addOption( 'prefix', 'A UWC seeded by Custos:SeedUwc', true, true );
				$this->requireExtension( 'Custos' );
			}

			public function execute() {
				$p = (string)$this->getOption( 'prefix' );
				$id = '2208.00001';
				$url = 'https://export.arxiv.org/api/query?id_list=' . $id;
				$atom = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<feed xmlns=\"http://www.w3.org/2005/Atom\">\n  <id>https://arxiv.org/api/x</id>\n"
					. "  <title>arXiv Query</title>\n  <entry>\n    <id>http://arxiv.org/abs/{$id}v1</id>\n    <updated>2022-08-01T10:00:00Z</updated>\n"
					. "    <published>2022-08-01T10:00:00Z</published>\n    <title>Notes on a falling sphere</title>\n    <summary>We drop a sphere.</summary>\n"
					. "    <author>\n      <name>Ada Lovelace</name>\n    </author>\n  </entry>\n</feed>\n";
				$fetcher = new class( [ $url => $atom ] ) implements Fetcher {
					public int $calls = 0;

					public function __construct( private array $canned ) {
					}

					public function fetch( string $source, string $url, array $declared ): string {
						$this->calls++;
						return $this->canned[$url] ?? throw new FetchFault( FetchFault::TRANSPORT, $source );
					}
				};
				$config = \MediaWiki\MediaWikiServices::getInstance()->getMainConfig();
				$titles = PageTitles::fromConfig( $config );
				$store = new MwStore();
				$runs = new DbJobRunStore();
				$calc = Calculator::fromConfig( $config );
				$canon = static function ( array $v ) use ( $calc ): string {
					$r = $calc->call( 'canonical', 'canonical_json', '{"value":' . json_encode( $v, JSON_UNESCAPED_SLASHES ) . '}' );
					if ( $r['exit'] !== 0 ) {
						throw new RuntimeException( 'the Calculator did not write the fixture' );
					}
					return (string)$r['value'];
				};
				$fail = static function ( string $why ): never {
					echo "recheck: FAIL $why\n";
					exit( 1 );
				};

				$draft = $titles->draft( $p );
				$text = $store->get( $draft );
				if ( $text === null ) {
					$fail( "the UWC $p has no draft page: seed it first" );
				}
				$store->put( $draft, rtrim( $text, "\n" ) . "\n" . Blocks::render( Landing::SETTING, 'ON' ) . "\n", 'rehearsal: bibliography setting ON' );
				$entry = [ 'bib_id' => 'R1', 'identifiers' => [ 'ARXIV' => $id ], 'check_line' => "CHECK 2020-01-01 CONFIRMED ; ARXIV $id CONFIRMED",
					'item' => [ 'author' => [ [ 'family' => 'Lovelace', 'given' => 'Ada' ] ], 'issued' => [ 'date-parts' => [ [ 2022 ] ] ],
						'title' => 'Notes on a falling sphere', 'type' => 'article' ] ];
				$volume = $titles->bibliographyVolume( $p, 1 );
				$store->put( $volume, PageTexts::bibliography( $p, 1, $canon( [ $entry ] ) ), 'rehearsal: bibliography volume 1' );
				$store->put( $titles->declarationsVolume( 1 ), Blocks::render( PageTexts::REGISTRIES, $canon( [
					[ 'kind' => 'ARXIV', 'name' => 'arXiv API', 'template' => 'https://export.arxiv.org/api/query?id_list={ID}' ] ] ) ) . "\n",
					'rehearsal: registry declarations' );
				$before = $this->revisions( $volume );

				// the UWCs the job runs over: RecheckJob's own listing of the page table
				$live = new ReflectionMethod( RecheckJob::class, 'livePrefixes' );
				$prefixes = static fn (): array => $live->invoke( null, $titles );
				if ( !in_array( $p, $prefixes(), true ) ) {
					$fail( "the job's listing of live UWCs does not name $p" );
				}
				$frame = new BatchJob( $calc, $runs, BatchJob::confFrom( $config ), [
					BatchJob::RECHECK => RecheckRun::bodyOf( $store, $titles, $fetcher, $runs, $prefixes ) ] );
				$a = $frame->run( BatchJob::RECHECK );
				echo 'recheck: ' . $a['outcome'] . ', ' . $a['detail'] . "\n";
				$counts = json_decode( $a['counts'], true );
				if ( $a['outcome'] !== 'DONE' || ( $counts['changed'] ?? 0 ) !== 1 || ( $counts['pages'] ?? 0 ) !== 2 || $fetcher->calls !== 1 ) {
					$fail( 'the run did not change the one entry by one lookup and one landing: ' . $a['counts'] );
				}
				$read = json_decode( (string)PageTexts::readBibliography( $store->get( $volume ) ), true );
				$want = 'CHECK ' . gmdate( 'Y-m-d' ) . " CONFIRMED ; ARXIV $id CONFIRMED";
				if ( ( $read[0]['check_line'] ?? '' ) !== $want ) {
					$fail( 'the volume page does not carry the new CHECK line' );
				}
				if ( $this->revisions( $volume ) !== $before + 1 ) {
					$fail( 'the volume page was not saved exactly once' );
				}
				echo "recheck: volume rewritten\n";
			}

			/** The number of revisions of $title. */
			private function revisions( string $title ): int {
				$t = \MediaWiki\Title\Title::newFromText( $title );
				return (int)$this->getServiceContainer()->getConnectionProvider()->getReplicaDatabase()->newSelectQueryBuilder()
					->select( 'COUNT(*)' )->from( 'revision' )->where( [ 'rev_page' => $t->getArticleID() ] )->caller( __METHOD__ )->fetchField();
			}
		}
	}
	return CustosRecheckRehearsal::class;
}

echo "recheck_rehearsal.php runs under maintenance/run.php, on the rehearsal wiki (rehearsal.sh)\n";
exit( 1 );
