<?php
/**
 * Fetcher: the one outbound-fetch layer of the batch jobs (the cluster month and the
 * bibliography recheck). The Calculator never fetches; a job asks a Fetcher, and the harness gives
 * it FakeFetcher, which serves canned text.
 *
 * $declared (the declaration's values, never an agent's or a person's input):
 *   hosts      string[]  the only hosts a request, and each redirect hop, may name (required)
 *   timeout    int       seconds for the whole fetch, redirects included (required, at least 1)
 *   pacing     int       seconds between two calls to this source (default 0)
 *   max_bytes  int       at most 20 MB, FetchGuard::MAX_BYTES (default that)
 *   contact    array     {in: "agent"|"query", param: <name>}: where the source's contact value
 *                        (CustosRegistryContact[$source]) goes in the request (default: none sent)
 *   schema     callable  fn(string $body): bool, the declared response schema (default: none)
 *
 * Returns the body. A refused or failed fetch throws FetchFault with a word of FetchFault::WORDS.
 * The raw download is returned to the caller, which neither publishes nor stores it; its digest is
 * FetchGuard::digest( $body ), for the run record's counts.
 */

namespace Custos;

interface Fetcher {
	/**
	 * @param string $source the declared source's name, the key of pacing and of the contact value
	 * @param string $url the address, built by the job from the declared template
	 * @param array $declared see above
	 * @throws FetchFault
	 */
	public function fetch( string $source, string $url, array $declared ): string;
}
