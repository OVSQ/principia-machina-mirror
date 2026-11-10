<?php
/**
 * SeedUwc: the pages of a new UWC, written in one landing by the system user Custos, the
 * Operator's act on the command line (a maintenance script is a command-line context, so
 * the Calculator may be called):
 *
 *   php maintenance/run.php Custos:SeedUwc --prefix <p> --draft <file>
 *
 * <file> holds the Research Assembly as JSON, {"TPK", "TrM", "TMS"} (v1's draft form, e.g.
 * docs/v1/tpx/TPX/examples/spring_draft.json). Written through PageWriter, the INDEX AND BADGE
 * page last: the DRAFT UWC page (the draft as the Calculator's canonical JSON), the three
 * RESEARCH ASSEMBLY pages, an empty REGISTER OPEN Volume 1, a free LOCK PAGE, and the INDEX AND
 * BADGE page (the Research Assembly's digest, `pcalc zone digest_research_assembly_of`; the
 * Calculator's version and CustosBuild's digest; state LIVE; Volume 1 open; the STRUCTURE TEST LINE
 * "STRUCTURE TEST none", TPS 5.3.47, until the first run). PHP reads no field
 * of the draft: each request is the file's bytes placed whole in an object, and each page text
 * is the Calculator's answer. Until the Calculator answers one zone of a Research Assembly, each
 * RESEARCH ASSEMBLY page carries the whole Research Assembly; its title names its zone.
 *
 * Refused, nothing written: a prefix the titles refuse, a file that cannot be read or is not
 * UTF-8, a draft the Calculator refuses, a UWC any of whose seven pages exists.
 *
 * The Calculator's residence is the live check (under /opt and /usr, root's), here as in the
 * job and in the rehearsal (custos/tests/rehearsal.sh places the binary under /opt): no switch.
 */

namespace Custos\Maintenance;

use Custos\Calculator;
use Custos\Blocks;
use Custos\MwStore;
use Custos\PageTexts;
use Custos\PageTitles;
use Custos\PageWriter;
use MediaWiki\Maintenance\Maintenance;

final class SeedUwc extends Maintenance {
	public function __construct() {
		parent::__construct();
		$this->addDescription( 'Custos: write the pages of a new UWC (the draft, the Research Assembly, Volume 1 of the register, the lock, the index and badge) in one landing' );
		$this->addOption( 'prefix', 'The UWC\'s record prefix', true, true );
		$this->addOption( 'draft', 'The file holding the Research Assembly as JSON: {"TPK", "TrM", "TMS"}', true, true );
		$this->requireExtension( 'Custos' );
	}

	public function execute() {
		$config = $this->getServiceContainer()->getMainConfig();
		$prefix = (string)$this->getOption( 'prefix' );
		$file = (string)$this->getOption( 'draft' );
		$titles = PageTitles::fromConfig( $config );
		$draft = is_file( $file ) ? file_get_contents( $file ) : false;
		if ( !is_string( $draft ) || $draft === '' || !mb_check_encoding( $draft, 'UTF-8' ) ) {
			$this->fatalError( "seed: the draft file cannot be read as UTF-8 text: $file" );
		}
		$calc = Calculator::fromConfig( $config );
		$canonical = $this->answer( $calc->call( 'canonical', 'canonical_json', '{"value":' . $draft . '}' ), 'the draft' );
		$digest = $this->answer( $calc->call( 'zone', 'digest_research_assembly_of', '{"tfk":' . $draft . '}' ), 'the Research Assembly\'s digest' );
		$build = $config->get( 'CustosBuild' );

		$pages = [ $titles->draft( $prefix ) => Blocks::render( 'draft', $canonical ) . "\n" ];
		foreach ( PageTitles::ZONES as $zone ) {
			$pages[$titles->researchAssembly( $prefix, $zone )] = Blocks::render( 'assembly', $canonical ) . "\n";
		}
		$pages[$titles->registerVolume( $prefix, 1 )] = PageTexts::register( $prefix, 1, '[]' );
		$pages[$titles->lock( $prefix )] = PageTexts::lock( $prefix, null, null, null, null );
		$badge = PageTexts::badge( $prefix, [
			'last_push' => null, 'last_release' => null,
			'calculator_version' => $calc->version(), 'calculator_digest' => (string)( $build['digest'] ?? '' ),
			'record_count' => 0, 'research_assembly' => $digest,
		], false, 1, PageTexts::STRUCTURE_NONE );

		$store = new MwStore( $this->getServiceContainer() );
		$writer = new PageWriter( $store, $titles );
		$writer->begin( $prefix, 'seed' );
		foreach ( array_merge( array_keys( $pages ), [ $titles->index( $prefix ) ] ) as $t ) {
			if ( $writer->read( $t ) !== null ) {
				$this->fatalError( "seed: the page \"$t\" exists; a UWC is seeded once; nothing written" );
			}
		}
		foreach ( $pages as $t => $text ) {
			$writer->put( $t, $text );
		}
		$writer->put( $titles->index( $prefix ), $badge );
		$saved = $writer->commit();
		foreach ( $saved as $t ) {
			$this->output( "seed: wrote $t\n" );
		}
		$this->output( 'seed: ' . count( $saved ) . " pages\n" );
	}

	/** The answer's string, or the Calculator's refusal as a fatal error. */
	private function answer( array $r, string $what ): string {
		if ( $r['exit'] !== 0 || !is_string( $r['value'] ?? null ) ) {
			$this->fatalError( "seed: the Calculator refused $what: " . ( $r['refused'] ?? '' ) . ' ' . ( $r['detail'] ?? '' ) );
		}
		return $r['value'];
	}
}

return SeedUwc::class;
