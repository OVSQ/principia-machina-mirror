<?php
/**
 * Challenge: the execution challenge (TPS 5.3.19, version 1's form, docs/v1/tpc_py/tpc_challenge.py),
 * every digest the Calculator's: `pcalc digest digest_fields {"fields": [TAG, FORM, nonce]}` and
 * `pcalc digest preimage_fields` for the preimage. PHP checks the forms and compares; it computes no
 * digest. The nonce is 32 lowercase hexadecimal characters, the response 64; any other nonce is
 * refused in version 1's words, which never quote it.
 *
 *   preimage(nonce)  ["OK", the preimage text] or ["REFUSED", BAD_NONCE]
 *   response(nonce)  ["OK", 64 lowercase hexadecimal] or ["REFUSED", BAD_NONCE]
 *   verify(nonce, response)  true only for a nonce and a response in form whose digest matches
 */

namespace Custos;

final class Challenge {
	public const TAG = 'TPC-EXECUTION-CHALLENGE';
	public const FORM = '1';
	public const BAD_NONCE = 'nonce is not 32 lowercase hexadecimal characters';
	private const NONCE = '/\A[0-9a-f]{32}\z/';
	private const HEX64 = '/\A[0-9a-f]{64}\z/';

	public static function nonceOk( mixed $nonce ): bool {
		return is_string( $nonce ) && preg_match( self::NONCE, $nonce ) === 1;
	}

	public static function responseOk( mixed $response ): bool {
		return is_string( $response ) && preg_match( self::HEX64, $response ) === 1;
	}

	public static function preimage( Calculator $calc, mixed $nonce ): array {
		if ( !self::nonceOk( $nonce ) ) {
			return [ 'REFUSED', self::BAD_NONCE ];
		}
		$v = self::ask( $calc, 'preimage_fields', $nonce );
		if ( !is_string( $v ) ) {
			throw new CalculatorFault( 'the preimage is not a text', CalculatorFault::ANSWER_FORM, 'digest', 'preimage_fields' );
		}
		return [ 'OK', $v ];
	}

	public static function response( Calculator $calc, mixed $nonce ): array {
		if ( !self::nonceOk( $nonce ) ) {
			return [ 'REFUSED', self::BAD_NONCE ];
		}
		$v = self::ask( $calc, 'digest_fields', $nonce );
		if ( !self::responseOk( $v ) ) {
			throw new CalculatorFault( 'the digest is not 64 lowercase hexadecimal characters', CalculatorFault::ANSWER_FORM,
				'digest', 'digest_fields' );
		}
		return [ 'OK', $v ];
	}

	public static function verify( Calculator $calc, mixed $nonce, mixed $response ): bool {
		if ( !self::nonceOk( $nonce ) || !self::responseOk( $response ) ) {
			return false;
		}
		// A plain comparison: the expected response is no secret, the agent holds the nonce it answers.
		return self::response( $calc, $nonce )[1] === $response;
	}

	private static function ask( Calculator $calc, string $fn, string $nonce ): mixed {
		$r = $calc->call( 'digest', $fn, json_encode( [ 'fields' => [ self::TAG, self::FORM, $nonce ] ], JSON_THROW_ON_ERROR ) );
		if ( $r['exit'] !== 0 ) {
			throw new CalculatorFault( "pcalc digest $fn refused the challenge's fields", CalculatorFault::ANSWER_FORM, 'digest', $fn );
		}
		return $r['value'];
	}
}
