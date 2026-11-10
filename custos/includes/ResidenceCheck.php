<?php
/**
 * ResidenceCheck: the live residence check (D10 on the first unit's pull request).
 *
 * The binary's path must be absolute and in normal form, and lie under one of the roots,
 * /opt or /usr (the shell framework's sandbox executes only from there). The chain is the
 * binary, then every folder above it up to and including its root, and for /opt and /usr the
 * filesystem's root "/" too (a writer of "/" could replace /opt). Each property is checked
 * over the whole chain before the next, in this order:
 *   1. it exists and is no symbolic link; the binary a regular file, the rest folders
 *   2. its mode gives no write to group or other
 *   3. it is owned by root (uid 0)
 *   4. the running user cannot write it: is_writable() is false and the owner is not the
 *      running user (so a process running as root is always refused)
 * The first failure throws UnsafeResidence naming the property and the path. What cannot be
 * read is refused, never allowed.
 *
 * The wiki makes the check with no arguments (Calculator::fromConfig): the roots /opt and
 * /usr and all four properties. No configuration key, environment variable or file changes it:
 * the job, the maintenance scripts and the rehearsal (custos/tests/rehearsal.sh, which places
 * the binary under /opt, root's) all run this one check. Only Custos's harness makes it with a
 * fake root of its own, every property still checked, to build the unsafe residences it refuses.
 */

namespace Custos;

final class ResidenceCheck implements Residence {
	/** The live roots. No configuration key changes them. */
	public const ROOTS = [ '/opt', '/usr' ];

	/** @var string[] */
	private array $roots;

	/**
	 * @param string[] $roots absolute folders in normal form; the live check takes the default,
	 * and only the harness passes another
	 */
	public function __construct( array $roots = self::ROOTS ) {
		$this->roots = array_values( $roots );
	}

	public function check( string $path ): void {
		if ( $path === '' || $path[0] !== '/' ) {
			throw new UnsafeResidence( $path, 'is not an absolute path' );
		}
		if ( !self::normal( $path ) ) {
			throw new UnsafeResidence( $path, 'is not in normal form (an empty, "." or ".." segment)' );
		}
		$root = null;
		foreach ( $this->roots as $r ) {
			if ( strncmp( $path, $r . '/', strlen( $r ) + 1 ) === 0 ) {
				$root = $r;
				break;
			}
		}
		if ( $root === null ) {
			throw new UnsafeResidence( $path, 'is outside ' . implode( ' and ', $this->roots ) );
		}
		$chain = [ $path ];
		for ( $p = dirname( $path ); strlen( $p ) >= strlen( $root ); $p = dirname( $p ) ) {
			$chain[] = $p;
		}
		if ( in_array( $root, self::ROOTS, true ) ) {
			$chain[] = '/';
		}

		clearstatcache();
		$stat = [];
		foreach ( $chain as $i => $p ) {
			$st = @lstat( $p );
			if ( !is_array( $st ) ) {
				throw new UnsafeResidence( $p, 'cannot be read' );
			}
			$type = $st['mode'] & 0170000;
			if ( $type === 0120000 ) {
				throw new UnsafeResidence( $p, 'is a symbolic link' );
			}
			if ( $i === 0 && $type !== 0100000 ) {
				throw new UnsafeResidence( $p, 'is not a regular file' );
			}
			if ( $i > 0 && $type !== 0040000 ) {
				throw new UnsafeResidence( $p, 'is not a folder' );
			}
			$stat[$p] = $st;
		}
		foreach ( $chain as $p ) {
			if ( ( $stat[$p]['mode'] & 0022 ) !== 0 ) {
				throw new UnsafeResidence( $p, 'is writable by group or other' );
			}
		}
		foreach ( $chain as $p ) {
			if ( $stat[$p]['uid'] !== 0 ) {
				throw new UnsafeResidence( $p, 'is not owned by root' );
			}
		}
		if ( !function_exists( 'posix_geteuid' ) ) {
			throw new UnsafeResidence( $path, 'cannot be checked: the running user is unknown (no posix extension)' );
		}
		$me = posix_geteuid();
		foreach ( $chain as $p ) {
			if ( is_writable( $p ) || $stat[$p]['uid'] === $me ) {
				throw new UnsafeResidence( $p, 'is writable by the running user' );
			}
		}
	}

	/** An absolute path with no empty, "." or ".." segment and no trailing "/". */
	private static function normal( string $path ): bool {
		foreach ( explode( '/', substr( $path, 1 ) ) as $seg ) {
			if ( $seg === '' || $seg === '.' || $seg === '..' ) {
				return false;
			}
		}
		return true;
	}
}
