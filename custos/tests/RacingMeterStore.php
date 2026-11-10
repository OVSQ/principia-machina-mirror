<?php
/**
 * RacingMeterStore: a MeterStore over another, for the harness's race between the budget roll-up and
 * the landing job on one account's traffic record. While $active, the first write after a read of a
 * traffic record (stageTraffic, putTraffic or casTraffic) runs $between on the store beneath first,
 * at most $times times in all: a Landing step written between the roll-up's read and its write, or
 * between another Landing step's read and its compare and set.
 */

namespace Custos\Tests;

use Closure;
use Custos\MeterStore;

final class RacingMeterStore implements MeterStore {
	public bool $active = false;
	public ?Closure $between = null;
	public int $times = 0;
	public int $fired = 0;
	private bool $armed = false;

	public function __construct( private MeterStore $inner ) {
	}

	private function race(): void {
		if ( $this->active && $this->armed && $this->between !== null && $this->fired < $this->times ) {
			( $this->between )( $this->inner );
			$this->fired++;
		}
		$this->armed = false;
	}

	public function record( array $row ): void {
		$this->inner->record( $row );
	}

	public function rows( int $since ): array {
		return $this->inner->rows( $since );
	}

	public function prune( int $before ): int {
		return $this->inner->prune( $before );
	}

	public function budget(): array {
		return $this->inner->budget();
	}

	public function putBudget( array $use, array $requests, int $rolled, string $level, string $kept ): void {
		$this->inner->putBudget( $use, $requests, $rolled, $level, $kept );
	}

	public function traffic( string $account ): ?array {
		$t = $this->inner->traffic( $account );
		$this->armed = $t !== null;
		return $t;
	}

	public function putTraffic( string $account, string $record, string $stage, int $time ): void {
		$this->race();
		$this->inner->putTraffic( $account, $record, $stage, $time );
	}

	public function casTraffic( string $account, ?string $was, string $record, string $stage, int $time ): bool {
		$this->race();
		return $this->inner->casTraffic( $account, $was, $record, $stage, $time );
	}

	public function stageTraffic( string $account, string $record, string $stage, int $time ): bool {
		$this->race();
		return $this->inner->stageTraffic( $account, $record, $stage, $time );
	}

	public function accounts(): array {
		return $this->inner->accounts();
	}
}
