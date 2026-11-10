<?php
/**
 * MeterStore: the governor's meter (charter 8.3, TPS 5.3.31) and what is rolled up from it, the
 * seam over the tables custos_meter (one row per governed request), custos_budget (the roll-up
 * per horizon with the pressure level) and custos_traffic (each account's traffic record, the
 * Calculator's text of it, and its stage). DbMeterStore is the live store; MemMeterStore one
 * object's memory, the default of a Landing named no store, and the harness's.
 *
 * A row is ["time", "account", "network", "op", "lane", "cpu", "wall", "memory", "bytes",
 * "landed", "weight"], every one a count but account, network and op (strings). The budget is
 * ["hour", "day", "thirty_days"] (use, thousandths of a CPU second), "requests" per horizon,
 * "rolled", "level" and "kept" (the Calculator's words). A traffic record is stored as the text the
 * Calculator answered and handed back to it as text: PHP reads no member of it. The landing job steps
 * the record by a compare and set (casTraffic), taking no lock: its write lands only on the record it
 * read, and a miss is read and stepped again, so no step is lost to another and none is written
 * twice. The budget roll-up writes only the stage beside it, conditionally (stageTraffic), and never
 * the record. putTraffic writes a record whole (the harness's and an Operator's tool, never a step).
 * A step that leaves the record's text as it was writes nothing: the stage and time beside the
 * record (ctr_stage, ctr_time) hold the last write by either writer, the step's compare and set on a
 * changed record or the roll-up's stageTraffic, and an unchanged step never writes a stage and time
 * over a stage the roll-up wrote after the step's read (a lost update). Both stores hold it.
 */

namespace Custos;

interface MeterStore {
	public const HORIZONS = [ 'hour' => 3600, 'day' => 86400, 'thirty_days' => 2592000 ];

	/** One governed request's row. */
	public function record( array $row ): void;

	/** @return list<array> the rows whose time is at least $since */
	public function rows( int $since ): array;

	/** Remove the rows whose time is before $before; @return int the rows removed */
	public function prune( int $before ): int;

	/** The roll-up: use and requests per horizon, rolled, level, kept; zeros and CLEAR before the first. */
	public function budget(): array;

	public function putBudget( array $use, array $requests, int $rolled, string $level, string $kept ): void;

	/** @return array{record: string, stage: string}|null the account's traffic record, null: none yet */
	public function traffic( string $account ): ?array;

	public function putTraffic( string $account, string $record, string $stage, int $time ): void;

	/**
	 * Write $record, $stage and $time as $account's traffic record only where the stored record is
	 * still the text $was ($was null: only where $account has no record yet), a compare and set.
	 * $record equal to $was (a step that leaves the record unchanged) writes nothing, not the stage
	 * nor the time: it only compares. @return bool true: written, or unchanged and the stored record
	 * still $was; false: the record changed since it was read (or was made, or is gone), and nothing
	 * was written
	 */
	public function casTraffic( string $account, ?string $was, string $record, string $stage, int $time ): bool;

	/**
	 * Write $stage and $time beside $account's record only where the stored record is still the text
	 * $record (a compare and set, the record itself untouched). @return bool false: the record changed
	 * since it was read, or is gone, and nothing was written
	 */
	public function stageTraffic( string $account, string $record, string $stage, int $time ): bool;

	/** @return list<string> the accounts with a traffic record */
	public function accounts(): array;
}
