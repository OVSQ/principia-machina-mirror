<?php
/**
 * NonceStore: the seam between the landing job and the table custos_nonce (sql/custos_nonce.json):
 * the execution challenge's nonces (TPS 5.3.19, version 1's), one outstanding per account and UWC
 * prefix. The job draws each nonce (random_bytes, Landing::draw) and puts it, replacing the one
 * outstanding; a PUSH takes it, which removes it, so a nonce is answered at most once: of two takes
 * of one nonce one gets it and the other null. DbNonceStore is the live store; MemNonceStore keeps
 * the contract in one object; tests/FileNonceStore.php keeps it on disk.
 */

namespace Custos;

interface NonceStore {
	/** $nonce, issued at $issued (server time, whole seconds), now the only outstanding nonce of $account on $prefix. */
	public function put( string $account, string $prefix, string $nonce, int $issued ): void;

	/** The outstanding nonce of $account on $prefix, removed; null when none is outstanding. */
	public function take( string $account, string $prefix ): ?string;
}
