<?php
/**
 * LandRefused: a ticket's op refused by the landing job before anything is written. $word is the
 * refusal's word in the ticket's answer ({"refused": word, "detail": message, ...}); $extra
 * carries the members the answer adds (the Calculator's problems, the governor's decision).
 */

namespace Custos;

use RuntimeException;

final class LandRefused extends RuntimeException {
	public string $word;
	public array $extra;

	public function __construct( string $word, string $detail, array $extra = [] ) {
		parent::__construct( $detail );
		$this->word = $word;
		$this->extra = $extra;
	}
}
