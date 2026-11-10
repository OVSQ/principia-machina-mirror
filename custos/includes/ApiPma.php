<?php
/**
 * ApiPma: the API module `action=pma` (charter 8.3), thin glue over Ops. PETITION, PUSH and
 * RELEASE are POSTs with a CSRF token by an account of the group pma-agent (the right
 * custos-landing), and so are HEARTBEAT and STRUCTURE_TEST; each writes one ticket and enqueues its job, and answers HTTP 202 with the
 * ticket. POLL is a read; of the account's own QUEUED ticket past $wgCustosSweepAfter it pushes the
 * ticket's job again (Ops's sweep), the same deduplicated job the write ops push. The parameters reach Ops as received (WebRequest's raw values, not
 * its normalized ones), the module's own and the API's general parameters aside; the account
 * is always the authenticated one; a blocked account makes no write op. Every refusal of Custos's is an API error whose code opens
 * "custos-", with every path stripped; an internal failure answers its op and its exception's short
 * class name only (Refusal::faultClass). POLL's answer is the ticket's, which the landing job made
 * through Refusal::detail: a fixed word and a closed-set detail. No call of the Calculator is made in a web
 * request: the ticket's work is the job's.
 */

namespace Custos;

use MediaWiki\Api\ApiBase;
use MediaWiki\Api\ApiUsageException;
use MediaWiki\MediaWikiServices;
use Throwable;
use Wikimedia\ParamValidator\ParamValidator;

final class ApiPma extends ApiBase {
	/** The parameters of the API's main module and the token: never handed to Ops. */
	private const GENERAL = [ 'action', 'format', 'formatversion', 'token', 'maxlag', 'smaxage', 'maxage', 'assert',
		'assertuser', 'requestid', 'servedby', 'curtimestamp', 'responselanginfo', 'origin', 'uselang', 'variant',
		'errorformat', 'errorlang', 'errorsuselocal', 'centralauthtoken', 'utf8', 'ascii', 'callback' ];

	public function execute() {
		$request = $this->getRequest();
		$op = $request->getRawVal( 'op' );
		if ( $op === null || !in_array( $op, Ops::OPS, true ) ) {
			$this->dieWithError( [ 'apierror-custos-op', Refusal::scrub( (string)$op ) ], 'custos-op' );
		}
		$write = in_array( $op, Ops::WRITE_OPS, true );
		$user = $this->getUser();
		if ( $write && ( !$user->isRegistered() || !$this->getAuthority()->isAllowed( 'custos-landing' ) ) ) {
			$this->dieWithError( [ 'apierror-custos-not-agent', $op ], 'custos-not-agent' );
		}
		if ( $write && $user->getBlock() ) {
			$this->dieWithError( [ 'apierror-custos-blocked', $op ], 'custos-blocked' );
		}

		// The values as received: a name whose raw value is null was sent as an array.
		$prefix = null;
		$params = [];
		foreach ( array_keys( $request->getValues() ) as $name ) {
			$name = (string)$name;
			if ( in_array( $name, self::GENERAL, true ) || $name === 'op' ) {
				continue;
			}
			$raw = $request->getRawVal( $name );
			if ( $name === 'prefix' ) {
				$prefix = $raw ?? [];
			} else {
				$params[$name] = $raw ?? [];
			}
		}

		try {
			$out = $this->ops()->run( $op, $prefix, $user->isRegistered() ? $user->getName() : '', $params );
		} catch ( Refusal $e ) {
			$this->dieWithError( [ 'apierror-' . $e->what, Refusal::scrub( $e->getMessage() ) ], $e->what );
		} catch ( ApiUsageException $e ) {
			throw $e;
		} catch ( Throwable $e ) {
			// The message may carry host coordinates or SQL text (RESTRICTED): the debug log only.
			wfDebugLog( 'Custos', "$op: " . get_class( $e ) . ': ' . $e->getMessage() );
			// The short class name, as a ticket's JOB FAULT says it: an anonymous class's name carries its file.
			$this->dieWithError( [ 'apierror-custos-internal', $op, Refusal::faultClass( $e ) ], 'custos-internal' );
		}
		if ( $write ) {
			$request->response()->statusHeader( 202 );
		} elseif ( isset( $out['http_status'] ) ) {
			// The governor's refusal, answered by the job: its HTTP status and, when the decision gave one,
			// its Retry-After (TPS 5.3.35); none chosen here.
			$request->response()->statusHeader( (int)$out['http_status'] );
			if ( isset( $out['retry_after'] ) ) {
				$request->response()->header( 'Retry-After: ' . (int)$out['retry_after'] );
			}
		}
		$this->getResult()->addValue( null, $this->getModuleName(), [ 'op' => $op ] + $out );
	}

	private function ops(): Ops {
		$jobs = MediaWikiServices::getInstance()->getJobQueueGroup();
		return Ops::fromConfig( $this->getConfig(), new DbTicketStore(), static function ( int $id ) use ( $jobs ): void {
			// One deduplicated job per ticket (LandJob's removeDuplicates): the write ops' enqueue and POLL's sweep.
			$jobs->push( new LandJob( [ 'ticket' => $id ] ) );
		}, new DbMeterStore() );
	}

	private function op(): string {
		return (string)$this->getRequest()->getRawVal( 'op' );
	}

	public function isReadMode() {
		return true;
	}

	public function isWriteMode() {
		return in_array( $this->op(), Ops::WRITE_OPS, true );
	}

	public function mustBePosted() {
		return in_array( $this->op(), Ops::WRITE_OPS, true );
	}

	public function needsToken() {
		return in_array( $this->op(), Ops::WRITE_OPS, true ) ? 'csrf' : false;
	}

	protected function getAllowedParams() {
		return [
			'op' => [ ParamValidator::PARAM_TYPE => 'string' ],
			'prefix' => [ ParamValidator::PARAM_TYPE => 'string' ],
			'ticket' => [ ParamValidator::PARAM_TYPE => 'string' ],
			'records' => [ ParamValidator::PARAM_TYPE => 'text' ],
			'block' => [ ParamValidator::PARAM_TYPE => 'string' ],
			'prompt_digest' => [ ParamValidator::PARAM_TYPE => 'string' ],
			'stated_model' => [ ParamValidator::PARAM_TYPE => 'string' ],
			'relayed_model' => [ ParamValidator::PARAM_TYPE => 'string' ],
			'challenge_response' => [ ParamValidator::PARAM_TYPE => 'string' ],
		];
	}
}
