<?php
/**
 * FileSeatStore: the SeatStore on disk, for the harness: one JSON file of every bucket. The
 * contract is DbSeatStore's: the seat lock of an account is an flock on its own file beside the
 * buckets' (<file>.lock-<sha1 of the lock's name>), so two processes, or two objects in one, over
 * the same file contend for one account's lock and never for two accounts'. Each put rewrites the
 * file under a short flock of <file>.lock, so writes for two accounts never lose each other.
 *
 * For the harness's races: $afterGet runs after every get (the account and the kind), $beforeLock
 * before every lock, $beforeRow before each row charge() sets (the account and the kind; a throw
 * there faults the charge, and nothing is written); $locks false makes lock() take nothing and always succeed (the store without
 * the lock, so a race shows what the lock prevents).
 */

namespace Custos\Tests;

use Closure;
use Custos\SeatStore;

final class FileSeatStore implements SeatStore {
	private string $file;
	/** @var array<string, resource> the lock files held, by account */
	private array $held = [];
	public ?Closure $afterGet = null;
	public ?Closure $beforeLock = null;
	public ?Closure $beforeRow = null;

	public function __construct( string $file, private bool $locks = true ) {
		$this->file = $file;
	}

	public function get( string $account, string $kind ): array {
		$b = $this->all()["$kind $account"] ?? [ 0, 0 ];
		if ( $this->afterGet !== null ) {
			( $this->afterGet )( $account, $kind );
		}
		return $b;
	}

	public function put( string $account, string $kind, int $level, int $since ): void {
		$this->write( [ [ $account, $kind, [ $level, $since ] ] ] );
	}

	/** Both rows (the agent's on $account, the sponsor's on $sponsorAccount) in one rewrite of the file: a throw before it (from $beforeRow) writes neither. */
	public function charge( string $account, array $agent, string $sponsorAccount, array $sponsor ): void {
		$this->write( [ [ $account, self::AGENT, [ (int)$agent[0], (int)$agent[1] ] ],
			[ $sponsorAccount, self::SPONSOR, [ (int)$sponsor[0], (int)$sponsor[1] ] ] ], true );
	}

	/** @param list<array{string, string, array{int, int}}> $rows each row's account, kind and bucket */
	private function write( array $rows, bool $hook = false ): void {
		$g = fopen( $this->file . '.lock', 'c' );
		flock( $g, LOCK_EX );
		try {
			$all = $this->all();
			foreach ( $rows as [ $account, $kind, $b ] ) {
				if ( $hook && $this->beforeRow !== null ) {
					( $this->beforeRow )( $account, $kind );
				}
				$all["$kind $account"] = $b;
			}
			file_put_contents( $this->file . '.tmp', json_encode( $all, JSON_THROW_ON_ERROR ) );
			rename( $this->file . '.tmp', $this->file );
		} finally {
			flock( $g, LOCK_UN );
			fclose( $g );
		}
	}

	public function lock( string $account, int $seconds ): bool {
		if ( $this->beforeLock !== null ) {
			( $this->beforeLock )( $account );
		}
		if ( !$this->locks ) {
			return true;
		}
		if ( isset( $this->held[$account] ) ) {
			return false;
		}
		$h = fopen( $this->lockFile( $account ), 'c' );
		$until = microtime( true ) + max( 0, $seconds );
		while ( !flock( $h, LOCK_EX | LOCK_NB ) ) {
			if ( microtime( true ) >= $until ) {
				fclose( $h );
				return false;
			}
			usleep( 10000 );
		}
		$this->held[$account] = $h;
		return true;
	}

	public function unlock( string $account ): void {
		$h = $this->held[$account] ?? null;
		if ( $h !== null ) {
			flock( $h, LOCK_UN );
			fclose( $h );
			unset( $this->held[$account] );
		}
	}

	/** Whether this object holds $account's lock now. */
	public function holds( string $account ): bool {
		return isset( $this->held[$account] );
	}

	private function lockFile( string $account ): string {
		return $this->file . '.lock-' . sha1( SeatStore::LOCK_PREFIX . $account );
	}

	private function all(): array {
		return is_file( $this->file ) ? (array)json_decode( (string)file_get_contents( $this->file ), true ) : [];
	}
}
