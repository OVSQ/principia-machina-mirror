<?php
/**
 * ProcRunner: the harness's ShellRunner, proc_open with the argument list (no shell). It
 * stands in for MediaWiki's shell framework, which the rehearsal exercises through
 * BoxedRunner; it counts its starts so a test can see that a refused call started nothing.
 */

namespace Custos\Tests;

use Custos\ShellRunner;
use RuntimeException;

final class ProcRunner implements ShellRunner {
	public int $starts = 0;

	public function run( array $argv, string $stdin ): array {
		$this->starts++;
		$spec = [ 0 => [ 'pipe', 'r' ], 1 => [ 'pipe', 'w' ], 2 => [ 'pipe', 'w' ] ];
		$proc = proc_open( $argv, $spec, $pipes );
		if ( !is_resource( $proc ) ) {
			throw new RuntimeException( 'proc_open failed' );
		}
		@fwrite( $pipes[0], $stdin );   // a binary that reads no stdin closes the pipe first
		fclose( $pipes[0] );
		$out = (string)stream_get_contents( $pipes[1] );
		$err = (string)stream_get_contents( $pipes[2] );
		fclose( $pipes[1] );
		fclose( $pipes[2] );
		return [ proc_close( $proc ), $out, $err ];
	}
}
