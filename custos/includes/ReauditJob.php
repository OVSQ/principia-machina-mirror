<?php
/**
 * ReauditJob: the job class `custosReaudit`, the successor's re-audit through the batch frame
 * (BatchJob), docs/design/pma_custos_jobs.md "Re-audit". The landing
 * that makes a successor (copy-forward) enqueues it with the parameters PARAMS names; a job
 * enqueued with none (Custos:Job --job reaudit) has no successor pending and answers NOTHING DUE.
 *
 * The run, after the frame's context check and lane-5 admission (bodyOf):
 *  1. the parameters: the successor's record prefix, the source's, the gap records' prefix and
 *     the PROMOTION record's ID, each in its form, else REFUSED and nothing read;
 *  2. the pages, read through the page writer's landing on the successor (block `reaudit-<run>`):
 *     the successor's INDEX AND BADGE page (LIVE, open register volume 1, as Landing reads volume 1
 *     only), its three RESEARCH ASSEMBLY pages carrying one Research Assembly, its open register
 *     volume and its DRAFT UWC page's BIBLIOGRAPHY SETTING (OFF when it states none, as Landing
 *     reads it); the source's three RESEARCH ASSEMBLY pages and its open register volume 1. A page
 *     absent or out of form ends the run REFUSED, nothing written;
 *  3. one Calculator call, `record reaudit_batch`, its request built by concatenation: the two
 *     Research Assemblies and the two registers whole as the pages hold them (PHP reads no field
 *     of them; the Calculator is the one parser, and it refuses a payload that would add or repeat
 *     a member: BAD_ARGUMENT, DUPLICATE_KEY), the setting, the PROMOTION ID, the block, the gap
 *     prefix, the trigger "the re-audit of <successor> under <source>", the run's UTC time and
 *     CustosTps. A refusal ends the run REFUSED with the Calculator's word, nothing written;
 *  4. the answer's REGISTER: the answer line decoded, written again with the job's flags and held
 *     only where that text is the answer line byte for byte, so the register's text written is the
 *     answer's own (canonical JSON writes a member as the same text wherever it stands); else
 *     REFUSED, nothing written. A REGISTER equal to the open volume's records as read changes
 *     nothing: DONE, no page written;
 *  5. one landing: the open register volume rewritten whole with REGISTER, then the INDEX AND
 *     BADGE page last, its record_count the count of REGISTER's records and every other member,
 *     the state, the open volume and the STRUCTURE TEST LINE carried as read (the badge is read in
 *     PHP only where PageTexts writes the same page again from what it read, byte for byte), both
 *     through the compare-and-set against the text read in step 2;
 *  6. a BASE MOVED (a page written changed since step 2): nothing saved; the first enqueues the
 *     job again once with the same parameters and `moved` 1, the run ending DEFERRED; a second (the
 *     run carrying `moved` 1) ends it REFUSED, for the Operator to read.
 * Nothing is struck: every STATUS is the Calculator's (`status_next` on HOLD), carried in REGISTER.
 *
 * Counts in the run record: checks (the scope's), held (STATUS pairs), gaps, promoted, records
 * (REGISTER's), pages (saved), moved (the BASE MOVED met by this job's runs, this one's included).
 */

namespace Custos;

use JsonException;
use MediaWiki\MediaWikiServices;
use Throwable;

final class ReauditJob extends BatchJobBase {
	public const TYPE = 'custosReaudit';
	/** The landing block's prefix; the run's id follows. */
	public const BLOCK = 'reaudit-';
	/** The job's parameters: the successor, the source, the gap records' prefix, the PROMOTION ID, the BASE MOVED count. */
	public const PARAMS = [ 'successor', 'source', 'gap_prefix', 'promotion_id', 'moved' ];
	public const NONE_PENDING = 'no successor pending';
	/** A record ID: a record prefix (PageTitles::isPrefix), a hyphen, a number; the Calculator judges it further. */
	private const RECORD_ID = '/\A[A-Za-z_][A-Za-z0-9_]*-[0-9]{1,9}\z/';
	/** CustosTps's form, a version word. */
	private const TPS = '/\A[0-9A-Za-z][0-9A-Za-z.+-]{0,63}\z/';
	private const JSON = JSON_UNESCAPED_SLASHES | JSON_UNESCAPED_UNICODE | JSON_UNESCAPED_LINE_TERMINATORS
		| JSON_PRESERVE_ZERO_FRACTION | JSON_THROW_ON_ERROR;

	protected static function jobName(): string {
		return BatchJob::REAUDIT;
	}

	/** The run as BatchJobBase runs it, the body given this job's parameters and the job's own re-enqueue. */
	public function run() {
		try {
			$services = MediaWikiServices::getInstance();
			$config = $services->getMainConfig();
			$body = self::bodyOf( new MwStore(), PageTitles::fromConfig( $config ), (array)$this->params,
				(string)$config->get( 'CustosTps' ), null,
				static function ( array $params ) use ( $services ): void {
					$services->getJobQueueGroup()->push( new self( $params ) );
				} );
			$frame = new BatchJob( Calculator::fromConfig( $config ), new DbJobRunStore(), BatchJob::confFrom( $config ),
				[ BatchJob::REAUDIT => $body ] );
			$answer = $frame->run( BatchJob::REAUDIT );
		} catch ( Throwable $e ) {
			$this->setLastError( Refusal::faultClass( $e ) );
			return false;
		}
		if ( in_array( $answer['outcome'], [ 'FAULT', 'INTEGRITY HALT', 'JOB CONTEXT' ], true ) ) {
			$this->setLastError( $answer['outcome'] . ': ' . $answer['detail'] );
			return false;
		}
		return true;
	}

	/**
	 * The body the frame runs: fn( Calculator, ?int $own ): array{outcome, detail, counts}; $own is
	 * the run's row, which names the landing block.
	 *
	 * @param array $params the job's parameters (PARAMS); no successor: NOTHING DUE
	 * @param string $tps CustosTps, the TPS version the gap and PROMOTION records carry
	 * @param callable|null $clock fn(): int, seconds (default: time); the records' LANDED
	 * @param callable|null $again fn( array $params ): void, the job enqueued again (null: never)
	 */
	public static function bodyOf( PageStore $store, PageTitles $titles, array $params, string $tps,
		?callable $clock = null, ?callable $again = null
	): callable {
		$clock ??= static fn (): int => time();
		return static function ( Calculator $calc, ?int $own = null ) use ( $store, $titles, $params, $tps, $clock, $again ): array {
			// PHP writes a float as its shortest text only under serialize_precision -1, as Landing sets it.
			$precision = (string)ini_get( 'serialize_precision' );
			ini_set( 'serialize_precision', '-1' );
			try {
				return self::reaudit( $calc, $store, $titles, $params, $tps, ( $clock )(), $own ?? 0, $again );
			} finally {
				ini_set( 'serialize_precision', $precision );
			}
		};
	}

	private static function reaudit( Calculator $calc, PageStore $store, PageTitles $titles, array $params, string $tps,
		int $now, int $own, ?callable $again
	): array {
		$counts = [ 'checks' => 0, 'held' => 0, 'gaps' => 0, 'promoted' => 0, 'records' => 0, 'pages' => 0, 'moved' => 0 ];
		if ( ( $params['successor'] ?? null ) === null ) {
			return [ 'outcome' => 'NOTHING DUE', 'detail' => self::NONE_PENDING, 'counts' => $counts ];
		}
		$refused = static function ( string $detail ) use ( &$counts ): array {
			return [ 'outcome' => 'REFUSED', 'detail' => $detail, 'counts' => $counts ];
		};
		foreach ( [ 'successor', 'source', 'gap_prefix' ] as $k ) {
			if ( !is_string( $params[$k] ?? null ) || !PageTitles::isPrefix( $params[$k] ) ) {
				return $refused( "the job's parameter $k is not a record prefix; nothing read" );
			}
		}
		if ( !is_string( $params['promotion_id'] ?? null ) || preg_match( self::RECORD_ID, $params['promotion_id'] ) !== 1 ) {
			return $refused( "the job's parameter promotion_id is not a record ID; nothing read" );
		}
		$moved = $params['moved'] ?? 0;
		if ( $moved !== 0 && $moved !== 1 ) {
			return $refused( "the job's parameter moved is not 0 or 1; nothing read" );
		}
		if ( preg_match( self::TPS, $tps ) !== 1 ) {
			return $refused( 'the configuration names no TPS version (CustosTps); nothing read' );
		}
		$counts['moved'] = $moved;
		$dst = $params['successor'];
		$src = $params['source'];
		$block = self::BLOCK . $own;

		// The pages, read through the landing on the successor (the texts the compare-and-set saves against).
		$w = new PageWriter( $store, $titles );
		$w->begin( $dst, $block );
		$badgeTitle = $titles->index( $dst );
		$badgeText = $w->read( $badgeTitle );
		$facts = PageTexts::facts( $badgeText );
		if ( ( $facts['retired'] ?? true ) !== false || ( $facts['open_volume'] ?? null ) !== 1 ) {
			return $refused( "there is no LIVE UWC $dst with open register volume 1; nothing written" );
		}
		$badge = self::badgeOf( $dst, $badgeText );
		if ( $badge === null ) {
			return $refused( "the INDEX AND BADGE page of $dst does not read; nothing written" );
		}
		$dstTfk = self::assembly( $w, $titles, $dst );
		$srcTfk = self::assembly( $w, $titles, $src );
		if ( $dstTfk === null || $srcTfk === null ) {
			return $refused( 'the three RESEARCH ASSEMBLY pages of ' . ( $dstTfk === null ? $dst : $src )
				. ' do not carry one Research Assembly; nothing written' );
		}
		$regTitle = $titles->registerVolume( $dst, 1 );
		$dstRecords = PageTexts::readRegister( $w->read( $regTitle ) );
		$srcFacts = PageTexts::facts( $w->read( $titles->index( $src ) ) );
		$srcRecords = ( $srcFacts['open_volume'] ?? null ) === 1
			? PageTexts::readRegister( $w->read( $titles->registerVolume( $src, 1 ) ) ) : null;
		if ( $dstRecords === null || $srcRecords === null ) {
			return $refused( 'the open register volume 1 of ' . ( $dstRecords === null ? $dst : $src ) . ' carries no register; nothing written' );
		}
		$setting = Blocks::one( $w->read( $titles->draft( $dst ) ), Landing::SETTING ) ?? Landing::SETTING_DEFAULT;
		if ( !in_array( $setting, Landing::SETTINGS, true ) ) {
			return $refused( "the DRAFT UWC page of $dst states a bibliography setting other than "
				. implode( ', ', Landing::SETTINGS ) . '; nothing written' );
		}

		// The one call: the pages' payloads whole, the job's own values written by PHP.
		$json = '{"dst_records":' . $dstRecords . ',"dst_tfk":' . $dstTfk
			. ',"landed":' . self::json( gmdate( 'Y-m-d\TH:i:s\Z', $now ) )
			. ',"landing_block":' . self::json( $block )
			. ',"prefix":' . self::json( $params['gap_prefix'] )
			. ',"promotion_id":' . self::json( $params['promotion_id'] )
			. ',"setting":' . self::json( $setting )
			. ',"src_records":' . $srcRecords . ',"src_tfk":' . $srcTfk
			. ',"tps":' . self::json( $tps )
			. ',"trigger":' . self::json( "the re-audit of $dst under $src" ) . '}';
		$r = $calc->call( 'record', 'reaudit_batch', $json );
		if ( $r['exit'] !== 0 ) {
			return $refused( 'record reaudit_batch refused the request: ' . $r['refused'] . ': ' . $r['detail'] . '; nothing written' );
		}
		if ( is_array( $r['value'] ) && ( $r['value'][0] ?? null ) === 'REFUSED' ) {
			return $refused( 'record reaudit_batch answered ' . self::cut( $r['text'] ) . '; nothing written' );
		}
		[ $answer, $register ] = self::registerOf( $r['text'] );
		if ( $answer === null ) {
			throw new CalculatorFault( 'record reaudit_batch answered outside its form', CalculatorFault::ANSWER_FORM, 'record', 'reaudit_batch' );
		}
		$counts['checks'] = count( $answer->CHECKS );
		$counts['held'] = count( $answer->STATUS );
		$counts['gaps'] = count( $answer->GAPS );
		$counts['promoted'] = count( $answer->PROMOTED );
		$counts['records'] = count( $answer->REGISTER );
		if ( $register === null ) {
			return $refused( 'the answer\'s REGISTER is not held by PHP exactly; nothing written' );
		}
		if ( $register === $dstRecords ) {
			return [ 'outcome' => 'DONE', 'detail' => 'the re-audit changed nothing; no page written', 'counts' => $counts ];
		}

		// One landing: the register volume, the badge last, against the texts read above.
		$badge['record_count'] = $counts['records'];
		$w->put( $regTitle, PageTexts::register( $dst, 1, $register ) );
		$w->put( $badgeTitle, PageTexts::badge( $dst, $badge, false, 1, PageTexts::readStructure( $badgeText ) ) );
		try {
			$counts['pages'] = count( $w->commit() );
		} catch ( PageFault $e ) {
			if ( !str_starts_with( $e->getMessage(), 'BASE MOVED' ) ) {
				throw $e;
			}
			$counts['moved'] = $moved + 1;
			if ( $moved === 0 && $again !== null ) {
				$again( [ 'successor' => $dst, 'source' => $src, 'gap_prefix' => $params['gap_prefix'],
					'promotion_id' => $params['promotion_id'], 'moved' => 1 ] );
				return [ 'outcome' => 'DEFERRED', 'counts' => $counts,
					'detail' => "BASE MOVED: a page of $dst changed while the re-audit ran; nothing saved; the job is enqueued again once" ];
			}
			return $refused( "BASE MOVED a second time: a page of $dst changed while the re-audit ran; nothing saved; for the Operator to read" );
		}
		return [ 'outcome' => 'DONE', 'counts' => $counts,
			'detail' => "{$counts['held']} held, {$counts['gaps']} gaps opened, {$counts['promoted']} promoted; the register volume and the badge written" ];
	}

	/**
	 * The Research Assembly the three RESEARCH ASSEMBLY pages of $prefix carry, its text whole; null
	 * when a page carries none or the three differ (as Landing's DIGEST GATE reads them).
	 */
	private static function assembly( PageWriter $w, PageTitles $titles, string $prefix ): ?string {
		$texts = [];
		foreach ( PageTitles::ZONES as $zone ) {
			$p = Blocks::one( $w->read( $titles->researchAssembly( $prefix, $zone ) ), 'assembly' );
			if ( $p === null ) {
				return null;
			}
			$texts[] = $p;
		}
		return count( array_unique( $texts ) ) === 1 ? $texts[0] : null;
	}

	/**
	 * The badge's members as read from the INDEX AND BADGE page $text: held only where PageTexts
	 * writes $text again from them, byte for byte (state LIVE, open volume 1, the STRUCTURE TEST
	 * LINE as read); null otherwise. The badge is Custos's own text of checked forms (PageTexts).
	 */
	private static function badgeOf( string $prefix, ?string $text ): ?array {
		try {
			$payload = PageTexts::readBadge( $text );
			$badge = $payload === null ? null : json_decode( $payload, true, 4, JSON_THROW_ON_ERROR );
			if ( !is_array( $badge ) || PageTexts::badge( $prefix, $badge, false, 1, PageTexts::readStructure( $text ) ) !== $text ) {
				return null;
			}
			return $badge;
		} catch ( JsonException | PageFault ) {
			return null;
		}
	}

	/**
	 * The answer line $text decoded (objects as objects) and REGISTER's text: [null, null] when it
	 * is not ["OK", {CHECKS, GAPS, PROMOTED, PROMOTION, REGISTER, STATUS}] with lists where lists
	 * stand; REGISTER's text null when the value written again with the job's flags is not $text
	 * byte for byte, the one case where PHP's text of a member could differ from the answer's.
	 */
	private static function registerOf( string $text ): array {
		try {
			$v = json_decode( $text, false, 512, JSON_THROW_ON_ERROR );
		} catch ( JsonException ) {
			return [ null, null ];
		}
		$a = is_array( $v ) && count( $v ) === 2 && $v[0] === 'OK' ? $v[1] : null;
		if ( !is_object( $a ) || array_keys( get_object_vars( $a ) ) !== [ 'CHECKS', 'GAPS', 'PROMOTED', 'PROMOTION', 'REGISTER', 'STATUS' ] ) {
			return [ null, null ];
		}
		foreach ( [ 'CHECKS', 'GAPS', 'PROMOTED', 'REGISTER', 'STATUS' ] as $k ) {
			if ( !is_array( $a->$k ) ) {
				return [ null, null ];
			}
		}
		try {
			return [ $a, self::json( $v ) === $text ? self::json( $a->REGISTER ) : null ];
		} catch ( JsonException ) {
			return [ $a, null ];
		}
	}

	private static function json( mixed $v ): string {
		return json_encode( $v, self::JSON );
	}

	private static function cut( string $s ): string {
		return mb_substr( $s, 0, 500 );
	}
}
