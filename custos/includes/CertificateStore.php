<?php
/**
 * CertificateStore: the seam between Custos and the table custos_certificate
 * (sql/custos_certificate.json): one row per certified agent account, naming its Sponsor, its
 * D(IS), its D(PROMPT), its vendor family, its declared model and its state. The row is written
 * only by the Operator's maintenance script Custos:Certify (maintenance/Certify.php) at an
 * admission the Declarer declares; nothing in a web request or a job writes it.
 *
 * Admission (Landing) reads it: an agent with no row, or a row whose state is not ACTIVE, is
 * refused ADMISSION before the governor is asked; otherwise the Sponsor's seat bucket is read and
 * charged under the Sponsor's account, and the Sponsor's tickets in flight are those of every
 * agent bound to it (agentsOf). DbCertificateStore is the live store; tests/FileCertificateStore.php
 * keeps the same contract on disk.
 */

namespace Custos;

interface CertificateStore {
	/** The state of a certificate in force; any other state refuses admission. */
	public const ACTIVE = 'ACTIVE';
	/** The states a row may carry. */
	public const STATES = [ self::ACTIVE, 'SUSPENDED', 'REVOKED' ];
	/** The members of a row, as get() answers it and put() takes it. */
	public const FIELDS = [ 'agent', 'sponsor', 'd_is', 'd_prompt', 'family', 'model', 'state' ];

	/**
	 * The certificate of the agent account $agent: an array of FIELDS' members, each a string;
	 * null when there is none.
	 */
	public function get( string $agent ): ?array;

	/** The agent accounts bound to the Sponsor account $sponsor, in any state, sorted. */
	public function agentsOf( string $sponsor ): array;

	/** Write one agent's row, $row of FIELDS' members, replacing the row of that agent when present. */
	public function put( array $row ): void;
}
