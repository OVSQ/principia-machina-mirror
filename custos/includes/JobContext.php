<?php
/**
 * JobContext: the precondition on the context the landing job runs in. The address space
 * the process is given (its soft limit, read from /proc/self/limits, else posix_getrlimit) is
 * compared with CustosJobContext's min_address_space (KiB, the measured need: 2,025,138 KiB);
 * below it, or unreadable while a minimum is set, the job refuses with JOB CONTEXT and never starts
 * the binary. "unlimited" passes.
 */

namespace Custos;

final class JobContext {
	public const MIN_ADDRESS_SPACE = 2025138;

	/** The refusal's sentence, or null when the context meets the minimum. */
	public static function refusal( int $minKib, ?string $limits = null ): ?string {
		if ( $minKib <= 0 ) {
			return null;
		}
		$have = self::addressSpace( $limits );
		if ( $have === null ) {
			return "JOB CONTEXT: the address space this process is given cannot be read; the job needs $minKib KiB and does not start the Calculator";
		}
		if ( $have === PHP_INT_MAX || $have >= $minKib ) {
			return null;
		}
		return "JOB CONTEXT: the address space this process is given is $have KiB, below the $minKib KiB the job needs (CustosJobContext); the Calculator is not started";
	}

	/**
	 * The soft address-space limit in KiB, PHP_INT_MAX when unlimited, null when unreadable.
	 * $limits: the text of /proc/self/limits (null: read it).
	 */
	public static function addressSpace( ?string $limits = null ): ?int {
		$limits ??= is_readable( '/proc/self/limits' ) ? (string)file_get_contents( '/proc/self/limits' ) : '';
		if ( preg_match( '/^Max address space\s+(\S+)/m', $limits, $m ) === 1 ) {
			return $m[1] === 'unlimited' ? PHP_INT_MAX : (int)intdiv( (int)$m[1], 1024 );
		}
		if ( function_exists( 'posix_getrlimit' ) ) {
			$r = posix_getrlimit();
			$soft = is_array( $r ) ? ( $r['soft totalmem'] ?? null ) : null;
			if ( $soft === 'unlimited' ) {
				return PHP_INT_MAX;
			}
			if ( is_numeric( $soft ) ) {
				return intdiv( (int)$soft, 1024 );
			}
		}
		return null;
	}
}
