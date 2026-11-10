<?php
/**
 * Residence: the check that the Calculator's binary resides where only root can change it,
 * made before its digest is checked. The digest check reads the binary's path and the shell
 * framework then starts that path; the two read the same bytes only when no user but root can
 * write the binary or a folder above it (D10). ResidenceCheck is the live check; the harness
 * supplies others.
 */

namespace Custos;

interface Residence {
	/**
	 * Return when $path is a safe residence for the Calculator's binary.
	 *
	 * @throws UnsafeResidence naming the property that failed and the path it failed for
	 */
	public function check( string $path ): void;
}
