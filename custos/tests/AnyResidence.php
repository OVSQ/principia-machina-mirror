<?php
/**
 * AnyResidence: the harness's Residence that accepts every path, so the Calculator's own
 * logic (the digest check, the version, the answer's reading) is tested on a binary in the
 * harness's scratch folder. The residence check itself is tested on ResidenceCheck (cases H).
 */

namespace Custos\Tests;

use Custos\Residence;

final class AnyResidence implements Residence {
	public int $checks = 0;

	public function check( string $path ): void {
		$this->checks++;
	}
}
