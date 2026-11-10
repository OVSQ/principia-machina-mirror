<?php
/**
 * TicketStore: the seam between Custos's ops and the table custos_ticket (sql/custos_ticket.json).
 * A ticket is one op of action=pma that changes state, written in the web request as
 * received; the job custosLand claims it, runs it out of the web request and writes its
 * answer. DbTicketStore is the live store over MediaWiki's database;
 * tests/FileTicketStore.php keeps the same contract on disk for the harness.
 *
 * A row, as every method returns it: id (int), op, account, prefix, request (the parameters
 * as received, never parsed by Custos's PHP), state (QUEUED, IN WORK or DONE), answer (null
 * until DONE), created, done (null until DONE), the two times 14 digits, YYYYMMDDHHMMSS, UTC.
 */

namespace Custos;

interface TicketStore {
	public const QUEUED = 'QUEUED';
	public const IN_WORK = 'IN WORK';
	public const DONE = 'DONE';

	/** Write one ticket in the state QUEUED; its id, greater than every id before it. */
	public function create( string $op, string $account, string $prefix, string $request ): int;

	/** The ticket's row, or null when there is none of that id. */
	public function get( int $id ): ?array;

	/**
	 * Write the answer of a ticket QUEUED or IN WORK and make it DONE. False, and nothing
	 * written, when there is no such ticket or it is already DONE: an answer is written once.
	 */
	public function answer( int $id, string $answer ): bool;

	/** The oldest QUEUED ticket, made IN WORK, its row as it now stands; null when none is QUEUED. */
	public function claimNext(): ?array;

	/**
	 * The ticket of $id made IN WORK when it is QUEUED, its row as it now stands; null when there
	 * is no such ticket or it is not QUEUED (the job custosLand claims the ticket it carries).
	 */
	public function claim( int $id ): ?array;

	/** Every ticket IN WORK, each ["id", "op", "account"], in id order (the governor's in-flight counts). */
	public function inWork(): array;

	/** The number of tickets in $state (QUEUED, IN WORK or DONE); 0 for any other word. */
	public function count( string $state ): int;
}
