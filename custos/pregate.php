<?php
/**
 * pregate.php: the PRE-GATE (charter 8.3, TPS 5.3.33), run before MediaWiki loads. The Operator wires
 * it on the server (a numbered step of the handoff): `php_value auto_prepend_file <this file>` and
 * `SetEnv CUSTOS_PREGATE_FILE <the list>`, the list the same path as $wgCustosPreGateFile.
 *
 * It reads its deny list and nothing else: the file the budget roll-up (Budget::writeDeny) writes
 * whole, a head line "# custos pre-gate deny list <time>" and one line "account<TAB><name><TAB><seconds>"
 * per CONTAINED account. A request whose User-Agent names a listed account (the Research Client's
 * form "<client>/<version> (<words>; <account>)", the account the last member in the parentheses) is
 * answered 429 with the Retry-After left of the listed one (the head's time plus its seconds, less
 * now) and ends there; RELEASE and INQUIRE of action=pma pass
 * (TPS 5.3.37: they pass at every stage). A line holds until its head's time plus its seconds; from
 * then on it passes, so a list the roll-up stopped writing never denies for longer than it said. A
 * list missing, unreadable or without its head line does nothing: every request goes on to
 * MediaWiki, whose admission still applies.
 *
 * The account is read from the User-Agent, which the client states: the PRE-GATE only ever denies, so
 * a User-Agent naming another account can deny its sender and never admit it past MediaWiki's
 * admission, which reads the authenticated account (a relaxation: the authenticated name is read
 * after MediaWiki loads, which the PRE-GATE runs before).
 */

if ( !function_exists( 'custos_pregate' ) ) {
	/**
	 * The PRE-GATE's verdict on one request: null (go on) or the Retry-After of a 429, the seconds left
	 * until the line's head time plus its seconds.
	 * @param string $list the deny list's text, or '' when missing
	 * @param int $now the request's time
	 */
	function custos_pregate( string $list, string $userAgent, ?string $action, ?string $op, int $now ): ?int {
		if ( $action === 'pma' && in_array( $op, [ 'RELEASE', 'INQUIRE' ], true ) ) {
			return null;
		}
		if ( preg_match( '/\A# custos pre-gate deny list ([0-9]{1,12})\n/', $list, $h ) !== 1 ) {
			return null;
		}
		$head = (int)$h[1];
		if ( preg_match( '/\(([^()]*)\)\s*\z/', $userAgent, $m ) !== 1 ) {
			return null;
		}
		$parts = explode( ';', $m[1] );
		$account = trim( (string)end( $parts ) );
		if ( $account === '' ) {
			return null;
		}
		foreach ( explode( "\n", $list ) as $line ) {
			$f = explode( "\t", $line );
			if ( count( $f ) === 3 && $f[0] === 'account' && $f[1] === $account && preg_match( '/\A[0-9]{1,9}\z/', $f[2] ) === 1 ) {
				// The wait left of the listed one, from the list's head to now.
				return $now < $head + (int)$f[2] ? $head + (int)$f[2] - $now : null;
			}
		}
		return null;
	}

	/** The deny list's text, at most 1 MiB, or '' when no file is named or it is missing or unreadable. */
	function custos_pregate_list( string $file ): string {
		if ( $file === '' || !is_file( $file ) ) {
			return '';
		}
		$text = @file_get_contents( $file, false, null, 0, 1048576 );
		return is_string( $text ) ? $text : '';
	}
}

if ( PHP_SAPI !== 'cli' ) {
	$custosAfter = custos_pregate( custos_pregate_list( (string)( $_SERVER['CUSTOS_PREGATE_FILE'] ?? '' ) ), (string)( $_SERVER['HTTP_USER_AGENT'] ?? '' ),
		isset( $_REQUEST['action'] ) && is_string( $_REQUEST['action'] ) ? $_REQUEST['action'] : null,
		isset( $_REQUEST['op'] ) && is_string( $_REQUEST['op'] ) ? $_REQUEST['op'] : null, time() );
	if ( $custosAfter !== null ) {
		http_response_code( 429 );
		header( 'Retry-After: ' . $custosAfter );
		header( 'Content-Type: text/plain; charset=utf-8' );
		echo "429 the account is CONTAINED; RELEASE and INQUIRE pass\n";
		exit;
	}
	unset( $custosAfter );
}
