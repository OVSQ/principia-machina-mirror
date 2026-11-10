<?php
/**
 * UnsafeResidence: the Calculator's binary, or a folder above it, could be changed by a user
 * other than root, or lies outside the folders the shell framework's sandbox executes from, so
 * the call is refused before the digest check and the binary is not started (D10). Like
 * DigestMismatch it halts a landing; it is never caught as a CalculatorFault. Its message, which
 * carries the path, goes to the error channel only; the ticket's answer names check() (Refusal::detail).
 */

namespace Custos;

use RuntimeException;

final class UnsafeResidence extends RuntimeException {
	/** The path the property failed for: the binary or a folder above it. */
	public string $path;
	/** The property that failed, as the message words it. */
	public string $property;

	/** The checks a ticket's answer may name: the closed set of Refusal::detail's UNSAFE RESIDENCE. */
	public const PATH_CLASS = 'path class';
	public const MODE = 'mode';
	public const OWNER = 'owner';
	public const UNREADABLE = 'unreadable';
	public const UNCHECKED = 'unchecked';
	public const CHECKS = [ self::PATH_CLASS, self::MODE, self::OWNER, self::UNREADABLE, self::UNCHECKED ];
	/** Each property ResidenceCheck words, by its opening words, and the check it names. */
	private const BY_PROPERTY = [
		'is not an absolute path' => self::PATH_CLASS, 'is not in normal form' => self::PATH_CLASS,
		'is outside ' => self::PATH_CLASS, 'is a symbolic link' => self::PATH_CLASS, 'is not a regular file' => self::PATH_CLASS,
		'is not a folder' => self::PATH_CLASS, 'is writable by group or other' => self::MODE, 'is writable by the running user' => self::MODE, 'is not owned by root' => self::OWNER,
		'cannot be read' => self::UNREADABLE, 'cannot be checked' => self::UNCHECKED,
	];

	public function __construct( string $path, string $property ) {
		$this->path = $path;
		$this->property = $property;
		parent::__construct( "UNSAFE RESIDENCE: $path $property; the call is refused and the binary is not started" );
	}

	/** The check that failed, one of CHECKS, never the path: a property worded otherwise is UNCHECKED. */
	public function check(): string {
		foreach ( self::BY_PROPERTY as $opens => $check ) {
			if ( str_starts_with( $this->property, $opens ) ) {
				return $check;
			}
		}
		return self::UNCHECKED;
	}
}
