<?php
/**
 * RecheckJob: the job class `custosRecheck`, the bibliography recheck through the batch frame
 * (BatchJob), docs/design/pma_custos_jobs.md "Bibliography recheck". The run itself, its constants
 * and its body are RecheckRun's, which needs no MediaWiki class (the harness runs it); this class
 * wires the body to the wiki: the live page store, the
 * titles, the live Fetcher (LiveFetcher behind FetchGuard, BIBLIO LOOKUP TIME bounding the run) with
 * the contact values of CustosRegistryContact, and the UWCs read from the page table.
 *
 * The run: the REGISTRY DECLARATIONS (none: NOTHING DUE, NO DECLARATION); the entries of every LIVE
 * UWC whose BIBLIOGRAPHY SETTING is ON or CLOSED; `biblio recheck_urls`; the guarded fetch;
 * `biblio recheck_batch`, called again for each second round it names; one landing per UWC touched,
 * its volumes in volume order, the INDEX AND BADGE page last (RecheckRun's note).
 *
 */

namespace Custos;

use MediaWiki\Config\Config;
use MediaWiki\MediaWikiServices;
use Wikimedia\Rdbms\IExpression;
use Wikimedia\Rdbms\LikeValue;

final class RecheckJob extends BatchJobBase {
	public const TYPE = 'custosRecheck';

	protected static function jobName(): string {
		return BatchJob::RECHECK;
	}

	/**
	 * Run outside the job runner's transaction round (Job::JOB_NO_EXPLICIT_TRX_ROUND): the run's row,
	 * inserted by the frame before the body, is committed at once, so a recheck run begun at the same
	 * time sees it and counts its allowance (RecheckRun::today), and a run killed before it ends
	 * leaves its row unended, counted, instead of rolled back.
	 */
	public function __construct( array $params ) {
		parent::__construct( $params );
		$this->executionFlags |= self::JOB_NO_EXPLICIT_TRX_ROUND;
	}

	protected static function body( Config $config, JobRunStore $runs ): ?callable {
		$titles = PageTitles::fromConfig( $config );
		$guard = new FetchGuard( static fn (): float => microtime( true ),
			static function ( float $s ): void {
				usleep( (int)( $s * 1e6 ) );
			}, RecheckRun::LOOKUP_TIME );
		$fetcher = new LiveFetcher( (array)$config->get( 'CustosRegistryContact' ), $guard );
		return RecheckRun::bodyOf( new MwStore(), $titles, $fetcher, $runs, static fn (): array => self::livePrefixes( $titles ) );
	}

	/** The record prefixes of the UWCs whose INDEX AND BADGE page exists: titles `<UWC root>/<p>/Index` in the page table. */
	private static function livePrefixes( PageTitles $titles ): array {
		$probe = $titles->index( 'A' );
		$key = str_replace( ' ', '_', substr( $probe, 0, -strlen( 'A/Index' ) ) );
		$dbr = MediaWikiServices::getInstance()->getConnectionProvider()->getReplicaDatabase();
		$rows = $dbr->newSelectQueryBuilder()->select( 'page_title' )->from( 'page' )
			->where( [ 'page_namespace' => 0, $dbr->expr( 'page_title', IExpression::LIKE, new LikeValue( $key, $dbr->anyString() ) ) ] )
			->limit( 100000 )->caller( __METHOD__ )->fetchFieldValues();
		$out = [];
		foreach ( $rows as $t ) {
			$t = (string)$t;
			if ( !str_ends_with( $t, '/Index' ) ) {
				continue;
			}
			$p = substr( $t, strlen( $key ), -strlen( '/Index' ) );
			if ( !PageTitles::isPrefix( $p ) ) {
				continue;
			}
			try {
				if ( str_replace( ' ', '_', $titles->index( $p ) ) === $t ) {
					$out[] = $p;
				}
			} catch ( PageFault ) {
				continue;
			}
		}
		sort( $out, SORT_STRING );
		return array_values( array_unique( $out ) );
	}
}
