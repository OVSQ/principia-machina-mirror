<?php
/**
 * DigestMismatch: the Calculator's binary does not digest to the SHA-256 digest CustosBuild
 * names, so the call is refused before the binary is started. Landings halt on it (charter
 * 8.3: a digest-gate failure); it is never caught as a CalculatorFault. The ticket's answer says
 * "digest mismatch" alone (Refusal::detail); the digests go to the error channel.
 */

namespace Custos;

use RuntimeException;

final class DigestMismatch extends RuntimeException {
	public string $expected;
	public string $found;

	public function __construct( string $expected, string $found ) {
		$this->expected = $expected;
		$this->found = $found;
		parent::__construct( 'DIGEST MISMATCH: the Calculator\'s binary digests to '
			. ( $found === '' ? '(unreadable)' : $found ) . ', not the expected ' . $expected
			. '; the call is refused and the binary is not started' );
	}
}
