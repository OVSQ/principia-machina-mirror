<?php
/**
 * ShellRunner: how the Calculator's binary is started. BoxedRunner is MediaWiki's shell
 * framework, the live route; the harness supplies one over proc_open, so the Calculator's
 * own logic (the digest check, the version, the answer's reading) is tested without MediaWiki.
 */

namespace Custos;

interface ShellRunner {
	/**
	 * Run $argv (the binary's absolute path, then its arguments) with $stdin on its standard
	 * input; [exit code, standard output, standard error].
	 *
	 * @param string[] $argv
	 * @return array{0:int, 1:string, 2:string}
	 */
	public function run( array $argv, string $stdin ): array;
}
