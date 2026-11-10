<?php
/**
 * JobRunStore: the seam between the batch jobs' frame (BatchJob) and the table custos_job_run
 * (sql/custos_job_run.json). One row per run, written when the run begins and finished once when
 * it ends. DbJobRunStore is the live store over MediaWiki's database; tests/FileJobRunStore.php
 * keeps the same contract on disk for the harness.
 *
 * A row, as every method returns it: id (int), job (the job's name), started (14 digits,
 * YYYYMMDDHHMMSS, UTC), done (the same, null while the run has not ended), outcome (one of
 * BatchJob::OUTCOMES, null while the run has not ended), detail and counts (text; counts a JSON
 * object text).
 */

namespace Custos;

interface JobRunStore {
	/** Write one run begun; its id, greater than every id before it. */
	public function start( string $job, string $started ): int;

	/**
	 * Finish the run of $id: its outcome, detail and counts, and the time it ended. False, and nothing
	 * written, when there is no such run or it has already ended: a run is finished once.
	 */
	public function finish( int $id, string $outcome, string $detail, string $counts, string $done ): bool;

	/** The run's row, or null when there is none of that id. */
	public function get( int $id ): ?array;

	/** The latest run of the job $job by id, or null when it has none. */
	public function last( string $job ): ?array;
}
