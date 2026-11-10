<?php
/**
 * CalculatorFault: the Calculator could not be called, or answered outside its protocol (no
 * binary configured, a call inside a web request, a function name that is not a word, an
 * exit code other than 0, 1 or 2, an answer that is not one line of JSON, a version other
 * than the expected one). Nothing the Calculator would have computed is used.
 *
 * Its message (which may carry pcalc's first stderr line, a path or a value) goes to the error
 * channel only; the ticket's answer says $fault, one of FAULTS, and the call's family and function
 * (Refusal::detail).
 */

namespace Custos;

use RuntimeException;

class CalculatorFault extends RuntimeException {
	/** The faults a ticket's answer may name: the closed set of Refusal::detail's CALCULATOR FAULT. */
	public const NOT_A_WORD = 'not a word';
	public const WEB_REQUEST = 'web request';
	public const NOT_CONFIGURED = 'not configured';
	public const NO_DIGEST = 'no digest';
	public const EXIT_CODE = 'exit code';
	public const NOT_ONE_LINE = 'not one line';
	public const NOT_JSON = 'not json';
	public const NO_REFUSAL = 'no refusal';
	public const VERSION = 'version';
	public const ANSWER_FORM = 'answer form';
	public const FAULTS = [ self::NOT_A_WORD, self::WEB_REQUEST, self::NOT_CONFIGURED, self::NO_DIGEST, self::EXIT_CODE,
		self::NOT_ONE_LINE, self::NOT_JSON, self::NO_REFUSAL, self::VERSION, self::ANSWER_FORM ];

	/** One of FAULTS. */
	public string $fault;
	/** The call's family and function, "" where none was made or the name is not a word. */
	public string $family;
	public string $function;

	public function __construct( string $message, string $fault = self::ANSWER_FORM, string $family = '', string $function = '' ) {
		parent::__construct( $message );
		$this->fault = $fault;
		$this->family = $family;
		$this->function = $function;
	}
}
