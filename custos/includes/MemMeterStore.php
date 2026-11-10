<?php
/** MemMeterStore: the meter's store in one object's memory (MeterStore), for a Landing named none and the harness. */

namespace Custos;

final class MemMeterStore implements MeterStore {
	private array $rows = [];
	private ?array $budget = null;
	private array $traffic = [];

	public function record( array $row ): void {
		$this->rows[] = $row;
	}

	public function rows( int $since ): array {
		return array_values( array_filter( $this->rows, static fn ( array $r ): bool => $r['time'] >= $since ) );
	}

	public function prune( int $before ): int {
		$n = count( $this->rows );
		$this->rows = array_values( array_filter( $this->rows, static fn ( array $r ): bool => $r['time'] >= $before ) );
		return $n - count( $this->rows );
	}

	public function budget(): array {
		return $this->budget ?? self::empty();
	}

	public static function empty(): array {
		return [ 'use' => [ 'hour' => 0, 'day' => 0, 'thirty_days' => 0 ], 'requests' => [ 'hour' => 0, 'day' => 0, 'thirty_days' => 0 ],
			'rolled' => 0, 'level' => 'CLEAR', 'kept' => 'CLEAR' ];
	}

	public function putBudget( array $use, array $requests, int $rolled, string $level, string $kept ): void {
		$this->budget = [ 'use' => $use, 'requests' => $requests, 'rolled' => $rolled, 'level' => $level, 'kept' => $kept ];
	}

	public function traffic( string $account ): ?array {
		return $this->traffic[$account] ?? null;
	}

	public function putTraffic( string $account, string $record, string $stage, int $time ): void {
		$this->traffic[$account] = [ 'record' => $record, 'stage' => $stage, 'time' => $time ];
	}

	public function casTraffic( string $account, ?string $was, string $record, string $stage, int $time ): bool {
		if ( ( $this->traffic[$account]['record'] ?? null ) !== $was ) {
			return false;
		}
		if ( $record === $was ) {
			// An unchanged step writes nothing: the stage and time stay the last writer's.
			return true;
		}
		$this->traffic[$account] = [ 'record' => $record, 'stage' => $stage, 'time' => $time ];
		return true;
	}

	public function stageTraffic( string $account, string $record, string $stage, int $time ): bool {
		if ( ( $this->traffic[$account]['record'] ?? null ) !== $record ) {
			return false;
		}
		$this->traffic[$account]['stage'] = $stage;
		$this->traffic[$account]['time'] = $time;
		return true;
	}

	public function accounts(): array {
		return array_map( 'strval', array_keys( $this->traffic ) );
	}
}
