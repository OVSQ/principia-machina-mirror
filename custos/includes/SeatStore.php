<?php
/**
 * SeatStore: the seam between the landing job and the table custos_seat (sql/custos_seat.json):
 * each account's seat buckets, one per kind (agent, sponsor), in the governor's form, the pair
 * [level, since] of `pcalc governor admit` (Principia/Calculator/Governor.lean, bucketOf). The
 * job reads the two buckets into the MeteredState and writes back the charge `admit` answers.
 *
 * The admission is one critical section over the agent's account and its Sponsor's: lock() of each,
 * in the order of their names, before the read of the buckets, unlock() of each after the charge is
 * written (or after a refusal or a fault, nothing written), so two jobs admitting one account, or
 * two agents of one Sponsor, never both spend the last seat. The lock is the
 * account's named lock LOCK_PREFIX . $account; two accounts never contend for one lock. Between
 * lock and unlock, get() reads what the last holder wrote, and put() and charge() are durable
 * before unlock. The admission's charge is written by charge(): both buckets or neither.
 * DbSeatStore is the live store (the database's named lock); tests/FileSeatStore.php keeps the
 * same contract on disk (flock).
 */

namespace Custos;

interface SeatStore {
	public const AGENT = 'agent';
	public const SPONSOR = 'sponsor';
	/** The named lock of an account's seats: this prefix, then the account's user name. */
	public const LOCK_PREFIX = 'custos-seat:';

	/** The bucket [level, since] of $account's $kind; [0, 0] when there is no row. */
	public function get( string $account, string $kind ): array;

	/** Write the bucket [level, since] of $account's $kind, the row made when absent. */
	public function put( string $account, string $kind, int $level, int $since ): void;

	/**
	 * Write the agent bucket $agent of the account $account and the sponsor bucket $sponsor of the
	 * account $sponsorAccount (the agent's Sponsor, read from its certificate), each [level, since],
	 * as one write: both rows or neither (a fault between them leaves both as they were).
	 */
	public function charge( string $account, array $agent, string $sponsorAccount, array $sponsor ): void;

	/**
	 * Take $account's seat lock, waiting at most $seconds (0: one try). True when taken; false
	 * when another holder kept it past the wait, and then nothing is held.
	 */
	public function lock( string $account, int $seconds ): bool;

	/** Release $account's seat lock, taken by lock(). */
	public function unlock( string $account ): void;
}
