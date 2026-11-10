<?php
/**
 * MemNonceStore: the NonceStore in one object's memory, the default of a Landing built without a
 * store (the tests' Landing objects that never PUSH). The challenge is checked over it all the same:
 * a nonce issued by another object is not outstanding here, so its PUSH is REASONED.
 */

namespace Custos;

final class MemNonceStore implements NonceStore {
	/** @var array<string, string> */
	private array $n = [];

	public function put( string $account, string $prefix, string $nonce, int $issued ): void {
		$this->n[$prefix . "\n" . $account] = $nonce;
	}

	public function take( string $account, string $prefix ): ?string {
		$k = $prefix . "\n" . $account;
		$v = $this->n[$k] ?? null;
		unset( $this->n[$k] );
		return $v;
	}
}
