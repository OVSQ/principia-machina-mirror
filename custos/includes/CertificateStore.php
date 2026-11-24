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
 *
 * The refused-PROMPT mark (the table custos_prompt_mark, sql/custos_prompt_mark.json): the landing
 * job sets it on an agent's certificate when it refuses PROMPT (a presented D(PROMPT) not the
 * certificate's, TPS 5.14.5); while it stands, every op under that certificate is refused PROMPT
 * whatever it presents. It is stored, so it outlives the job's process, and nothing in a web request
 * clears it: only put(), the write of the certificate by Custos:Certify (a re-certification), clears
 * it, together with the row's write (a row write that fails leaves the mark standing), so a mark set
 * by a refusal racing that write stands on the new row (refusing more, never less; Custos:Certify run
 * again clears it). Admission reads the mark before the certificate.
 */

namespace Custos;

interface CertificateStore {
	/** The state of a certificate in force; any other state refuses admission. */
	public const ACTIVE = 'ACTIVE';
	/** The states a row may carry. */
	public const STATES = [ self::ACTIVE, 'SUSPENDED', 'REVOKED' ];
	/** The members of a row, as get() answers it and put() takes it. */
	public const FIELDS = [ 'agent', 'sponsor', 'd_is', 'd_prompt', 'family', 'model', 'state' ];
	/** The refused-PROMPT mark's two states: it stands, or a re-certification cleared it. */
	public const MARK_STANDING = 'STANDING';
	public const MARK_CLEARED = 'CLEARED';

	/**
	 * The certificate of the agent account $agent: an array of FIELDS' members, each a string;
	 * null when there is none.
	 */
	public function get( string $agent ): ?array;

	/** The agent accounts bound to the Sponsor account $sponsor, in any state, sorted. */
	public function agentsOf( string $sponsor ): array;

	/**
	 * Write one agent's row, $row of FIELDS' members, replacing the row of that agent when present,
	 * and clear the agent's refused-PROMPT mark, if one stands (the re-certification), as one write:
	 * a row write that fails leaves the mark standing.
	 */
	public function put( array $row ): void;

	/** Whether a refused-PROMPT mark stands on the certificate of $agent. */
	public function promptMarked( string $agent ): bool;

	/**
	 * Set the refused-PROMPT mark on the certificate of $agent, at $at (server time, whole seconds);
	 * a mark standing is kept with its first time. The landing job's write at a PROMPT refusal.
	 */
	public function markPrompt( string $agent, int $at ): void;
}
