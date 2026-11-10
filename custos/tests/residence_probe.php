<?php
/**
 * residence_probe.php: the residence check as the harness's other user sees it.
 *
 *   php custos/tests/residence_probe.php live <path>        the live check (/opt, /usr)
 *   php custos/tests/residence_probe.php <fake root> <path> the check under that root
 *
 * harness.php runs it through setpriv as uid 65534 when the harness runs as root, since
 * root can write every file and the check refuses it by design. Prints "resident", exit 0;
 * or the refusal, exit 1.
 */

declare( strict_types=1 );

require_once __DIR__ . '/bootstrap.php';

use Custos\ResidenceCheck;
use Custos\UnsafeResidence;

$top = $argv[1] ?? '';
$path = $argv[2] ?? '';
$check = $top === 'live' ? new ResidenceCheck() : new ResidenceCheck( [ $top ] );
try {
	$check->check( $path );
} catch ( UnsafeResidence $e ) {
	echo $e->getMessage(), "\n";
	exit( 1 );
}
echo "resident\n";
exit( 0 );
