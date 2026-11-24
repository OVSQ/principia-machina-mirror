<?php
/**
 * fetcher.php: the fetch layer's own test, FX1 to FX15 (docs/design/pma_custos_jobs.md, "The fetch
 * layer"), over FetchGuard, LiveFetcher with a canned resolver and a canned transport, and
 * FakeFetcher. No request leaves the machine: the default resolver and the default transport (curl)
 * are never constructed here, and FX0 reads this file's own source for it.
 *
 *   php custos/tests/fetcher.php
 *
 * Prints "fetcher: ALL PASS <n>/<n>". The cases join harness.php when the K chain's harness unit runs.
 * Command line only.
 */

declare( strict_types=1 );

require_once __DIR__ . '/bootstrap.php';

use Custos\FetchFault;
use Custos\FetchGuard;
use Custos\LiveFetcher;
use Custos\Tests\FakeFetcher;

const SOURCE = 'arxiv';
const HOST = 'registry.example';
const CONTACT = 'ops-contact@mail.example';

/** A fake clock the pacing and the timeouts read, and the sleeps it is given. */
final class Clock {
	public float $now = 1000.0;
	/** @var float[] */
	public array $slept = [];

	public function sleep( float $s ): void {
		$this->slept[] = $s;
		$this->now += $s;
	}
}

/** A transport that serves answers in order and records what it was asked. */
final class Wire {
	/** @var array<int,array> */
	public array $sent = [];
	public ?Closure $each = null;

	/** @param array<int,array|FetchFault|Throwable> $answers */
	public function __construct( private array $answers ) {
	}

	public function __invoke( string $url, string $host, string $ip, array $headers, float $timeout, int $maxBytes ): array {
		$this->sent[] = compact( 'url', 'host', 'ip', 'headers', 'timeout', 'maxBytes' );
		if ( $this->each !== null ) {
			( $this->each )();
		}
		$a = array_shift( $this->answers );
		if ( $a instanceof Throwable ) {
			throw $a;
		}
		return $a ?? [ 'status' => 200, 'location' => null, 'body' => '', 'ip' => $ip ];
	}
}

function ok200( string $body, string $ip = '93.184.216.34' ): array {
	return [ 'status' => 200, 'location' => null, 'body' => $body, 'ip' => $ip ];
}

function redir( string $to, string $ip = '93.184.216.34' ): array {
	return [ 'status' => 302, 'location' => $to, 'body' => '', 'ip' => $ip ];
}

function decl( array $more = [] ): array {
	return $more + [ 'hosts' => [ HOST, 'mirror.example' ], 'timeout' => 30 ];
}

/** A LiveFetcher over the canned wire; $ips what the resolver gives for every host. */
function live( Wire $w, Clock $c, array|Closure $ips = [ '93.184.216.34' ], array $contact = [ SOURCE => CONTACT ], ?int $runSeconds = null, ?int $runRequests = null ): LiveFetcher {
	$guard = new FetchGuard( static fn (): float => $c->now, [ $c, 'sleep' ], $runSeconds, $runRequests );
	return new LiveFetcher( $contact, $guard, is_array( $ips ) ? static fn ( string $h ): array => $ips : $ips, $w, static fn (): float => $c->now );
}

function word( callable $fn ): ?string {
	try {
		$fn();
	} catch ( FetchFault $e ) {
		return $e->word;
	}
	return null;
}

function refused( callable $fn, string $want, string $what ): void {
	$got = word( $fn );
	G::ok( $got === $want, $what, 'wanted ' . $want . ', got ' . ( $got ?? 'no refusal' ) );
}

/** Every text a fault of $fn can show: message, class, trace's strings are not read (the message is the output). */
function shown( callable $fn ): string {
	try {
		$fn();
	} catch ( Throwable $e ) {
		return get_class( $e ) . '|' . $e->getMessage() . '|' . ( $e instanceof FetchFault ? $e->word . '|' . $e->source : '' );
	}
	return '';
}

$url = 'https://' . HOST . '/api/query?id=1';

// FX0 no request leaves the machine
$self = (string)file_get_contents( __FILE__ );
G::ok( preg_match( '/curl_init|fsockopen|stream_socket_client|file_get_contents\(\s*[\'"]https?:|gethostbyname|dns_get_record/', str_replace( __FILE__, '', preg_replace( '/^.*FX0.*$/m', '', $self ) ?? '' ) ) === 0,
	'FX0 this test reaches no network function and builds no default resolver or transport' );
$ctor = preg_match_all( '/new LiveFetcher\(/', $self );
G::ok( $ctor === 1, 'FX0a LiveFetcher is built in one place, live(), always with a resolver and a transport', (string)$ctor );

// FX1 scheme
foreach ( [ 'http://' . HOST . '/a', 'ftp://' . HOST . '/a', 'file:///etc/passwd', '//' . HOST . '/a', 'https://user@' . HOST . '/a',
	'https://' . HOST . ':8443/a', 'https://' . HOST . '/a b', 'https:///a' ] as $bad ) {
	refused( static fn () => FetchGuard::checkUrl( $bad, [ HOST ] ), FetchFault::SCHEME, "FX1 refused: scheme or form of $bad" );
}
G::ok( FetchGuard::checkUrl( 'https://' . HOST . ':443/a', [ HOST ] ) === HOST, 'FX1 passed: https on port 443' );
$w = new Wire( [] );
refused( static fn () => live( $w, new Clock )->fetch( SOURCE, 'http://' . HOST . '/a', decl() ), FetchFault::SCHEME, 'FX1 the live class refuses http before any request' );
G::ok( $w->sent === [], 'FX1a no request was made for it' );

// FX2 hosts
refused( static fn () => FetchGuard::checkUrl( 'https://other.example/a', [ HOST ] ), FetchFault::HOST, 'FX2 refused: an undeclared host' );
refused( static fn () => FetchGuard::checkUrl( 'https://' . HOST . '.other.example/a', [ HOST ] ), FetchFault::HOST, 'FX2 refused: a longer name that begins with a declared host' );
refused( static fn () => FetchGuard::checkUrl( 'https://' . HOST . '@other.example/a', [ HOST ] ), FetchFault::SCHEME, 'FX2 refused: a declared host as user information' );
G::ok( FetchGuard::checkUrl( 'https://' . strtoupper( HOST ) . '/a', [ HOST ] ) === HOST, 'FX2 passed: a declared host in any case' );

// FX3 address ranges
foreach ( [ '10.1.2.3', '172.16.0.1', '172.31.255.255', '192.168.1.1', '127.0.0.1', '127.1.2.3', '169.254.169.254', '0.0.0.0', '100.64.0.1',
	'224.0.0.1', '255.255.255.255', '::1', '::', 'fe80::1', 'fc00::1', 'fd12:3456::1', 'ff02::1', '::ffff:127.0.0.1', '::ffff:10.0.0.1',
	'::ffff:169.254.169.254', '64:ff9b::7f00:1', '2002:7f00:0001::1', '2002:0a00:0001::', '::7f00:1', '::a00:1', 'fec0::1', '64:ff9b:1::1', '192.88.99.1', 'not an address', '' ] as $ip ) {
	G::ok( !FetchGuard::addressAllowed( $ip ), "FX3 refused: address \"$ip\"" );
}
foreach ( [ '93.184.216.34', '8.8.8.8', '172.32.0.1', '172.15.255.255', '2606:2800:220:1:248:1893:25c8:1946', '2a00:1450:4001::1', '::ffff:8.8.8.8', '64:ff9b::808:808' ] as $ip ) {
	G::ok( FetchGuard::addressAllowed( $ip ), "FX3 passed: address \"$ip\"" );
}

// FX4 the resolved addresses: all allowed, the connection pinned to the first
$w = new Wire( [ ok200( 'x' ) ] );
$c = new Clock;
$body = live( $w, $c, [ '93.184.216.34', '2606:2800:220:1::1' ] )->fetch( SOURCE, $url, decl() );
G::ok( $body === 'x' && $w->sent[0]['ip'] === '93.184.216.34' && $w->sent[0]['host'] === HOST, 'FX4 passed: the request is pinned to the first resolved address' );
$w = new Wire( [ ok200( 'x' ) ] );
refused( static fn () => live( $w, new Clock, [ '93.184.216.34', '10.0.0.5' ] )->fetch( SOURCE, $url, decl() ), FetchFault::ADDRESS, 'FX4 refused: one private address among the resolved ones' );
G::ok( $w->sent === [], 'FX4a no request was made for it' );
refused( static fn () => live( new Wire( [] ), new Clock, [] )->fetch( SOURCE, $url, decl() ), FetchFault::TRANSPORT, 'FX4 refused: a host that resolves to nothing' );

// FX5 the connected address is the pinned one
refused( static fn () => live( new Wire( [ ok200( 'x', '93.184.216.35' ) ] ), new Clock )->fetch( SOURCE, $url, decl() ), FetchFault::ADDRESS, 'FX5 refused: connected to another public address than the pinned one' );
refused( static fn () => live( new Wire( [ ok200( 'x', '127.0.0.1' ) ] ), new Clock )->fetch( SOURCE, $url, decl() ), FetchFault::ADDRESS, 'FX5 refused: connected to a loopback address' );
G::ok( live( new Wire( [ ok200( 'x', '2606:2800:220:1::1' ) ] ), new Clock, [ '2606:2800:220:1:0:0:0:1' ] )->fetch( SOURCE, $url, decl() ) === 'x',
	'FX5 passed: the same IPv6 address in another spelling' );

// FX6 redirects
$w = new Wire( [ redir( 'https://mirror.example/b' ), redir( '/c' ), redir( 'd' ), ok200( 'end' ) ] );
G::ok( live( $w, new Clock )->fetch( SOURCE, $url, decl() ) === 'end'
	&& [ $w->sent[1]['url'], $w->sent[2]['url'], $w->sent[3]['url'] ] === [ 'https://mirror.example/b', 'https://mirror.example/c', 'https://mirror.example/d' ],
	'FX6 passed: three hops, absolute, host-relative and path-relative, each to a declared host' );
foreach ( [ 'https://evil.example/x', 'http://' . HOST . '/x', '//evil.example/x', 'ftp://' . HOST . '/x', 'https://u@' . HOST . '/x', '', "https://" . HOST . "/x\r\nX: y" ] as $to ) {
	$w = new Wire( [ redir( $to ), ok200( 'no' ) ] );
	refused( static fn () => live( $w, new Clock )->fetch( SOURCE, $url, decl() ), FetchFault::REDIRECT, 'FX6 refused: a redirect to ' . json_encode( $to ) );
	G::ok( count( $w->sent ) === 1, 'FX6a the refused redirect was not followed' );
}
$w = new Wire( [ redir( 'https://mirror.example/b' ), ok200( 'no' ) ] );
refused( static fn () => live( $w, new Clock, static fn ( string $h ): array => [ $h === 'mirror.example' ? '10.0.0.9' : '93.184.216.34' ] )->fetch( SOURCE, $url, decl() ),
	FetchFault::ADDRESS, 'FX6b refused: a redirect to a declared host that resolves to a private address, judged again at its hop' );
G::ok( count( $w->sent ) === 1, 'FX6c the hop to it was not made' );

// FX7 hop limit
$w = new Wire( [ redir( '/1' ), redir( '/2' ), redir( '/3' ), redir( '/4' ), ok200( 'no' ) ] );
refused( static fn () => live( $w, new Clock )->fetch( SOURCE, $url, decl() ), FetchFault::REDIRECT, 'FX7 refused: a fourth hop' );
$w = new Wire( [ redir( '/1' ), redir( '/2' ), redir( '/3' ), ok200( 'yes' ) ] );
G::ok( live( $w, new Clock )->fetch( SOURCE, $url, decl() ) === 'yes', 'FX7 passed: exactly three hops' );

// FX8 time
refused( static fn () => live( new Wire( [ new FetchFault( FetchFault::TIME ) ] ), new Clock )->fetch( SOURCE, $url, decl() ), FetchFault::TIME, 'FX8 refused: the transport timed out' );
foreach ( [ 0, -1, null, '30' ] as $t ) {
	refused( static fn () => live( new Wire( [ ok200( 'x' ) ] ), new Clock )->fetch( SOURCE, $url, [ 'hosts' => [ HOST ], 'timeout' => $t ] ), FetchFault::TIME, 'FX8 refused: no usable declared timeout ' . json_encode( $t ) );
}
$c = new Clock;
$w = new Wire( [ redir( '/1' ), ok200( 'x' ) ] );
$w->each = static function () use ( $c ): void {
	$c->now += 20;
};
refused( static fn () => live( $w, $c )->fetch( SOURCE, $url, decl() ), FetchFault::TIME, 'FX8 refused: the declared time is for the whole fetch, redirects included' );
$c = new Clock;
$w = new Wire( [ ok200( 'x' ) ] );
live( $w, $c )->fetch( SOURCE, $url, decl( [ 'timeout' => 12 ] ) );
G::ok( $w->sent[0]['timeout'] === 12.0, 'FX8 passed: the transport is given the declared time' );

// FX9 size
$w = new Wire( [ ok200( str_repeat( 'a', 101 ) ) ] );
refused( static fn () => live( $w, new Clock )->fetch( SOURCE, $url, decl( [ 'max_bytes' => 100 ] ) ), FetchFault::SIZE, 'FX9 refused: a body past the declared limit' );
G::ok( live( new Wire( [ ok200( str_repeat( 'a', 100 ) ) ] ), new Clock )->fetch( SOURCE, $url, decl( [ 'max_bytes' => 100 ] ) ) === str_repeat( 'a', 100 ), 'FX9 passed: a body at the limit' );
$w = new Wire( [ ok200( 'x' ) ] );
live( $w, new Clock )->fetch( SOURCE, $url, decl( [ 'max_bytes' => 10 ** 9 ] ) );
G::ok( $w->sent[0]['maxBytes'] === 20 * 1024 * 1024, 'FX9 a declared limit above 20 MB is 20 MB' );
refused( static fn () => FetchGuard::checkSize( 20 * 1024 * 1024 + 1, 10 ** 9 ), FetchFault::SIZE, 'FX9 refused: 20 MB and a byte' );
refused( static fn () => live( new Wire( [ new FetchFault( FetchFault::SIZE ) ] ), new Clock )->fetch( SOURCE, $url, decl() ), FetchFault::SIZE, 'FX9 refused: the transport stopped reading at the limit' );

// FX10 archives
$m = [ 'data.csv' ];
G::ok( FetchGuard::archive( [ [ 'name' => 'data.csv', 'size' => 50 * 1024 * 1024 ], [ 'name' => 'other.txt', 'size' => 10 ** 12 ] ], $m ) === [ 'data.csv' ],
	'FX10 passed: a declared member at 50 MB, an undeclared one never read' );
refused( static fn () => FetchGuard::archive( [ [ 'name' => 'data.csv', 'size' => 50 * 1024 * 1024 + 1 ] ], $m ), FetchFault::ARCHIVE, 'FX10 refused: a declared member past 50 MB' );
refused( static fn () => FetchGuard::archive( array_fill( 0, 257, [ 'name' => 'a', 'size' => 1 ] ), $m ), FetchFault::ARCHIVE, 'FX10 refused: 257 entries' );
G::ok( FetchGuard::archive( array_fill( 0, 256, [ 'name' => 'a', 'size' => 1 ] ), $m ) === [], 'FX10 passed: 256 entries' );
refused( static fn () => FetchGuard::archive( [ [ 'name' => 'inner.zip', 'size' => 1 ] ], $m ), FetchFault::ARCHIVE, 'FX10 refused: a nested archive' );
refused( static fn () => FetchGuard::archive( [ [ 'name' => 'data.csv', 'size' => -1 ] ], $m ), FetchFault::ARCHIVE, 'FX10 refused: a size that is not a size' );

// FX11 pacing, one request at a time
$c = new Clock;
$f = live( new Wire( [ ok200( 'a' ), ok200( 'b' ), ok200( 'c' ), ok200( 'd' ) ] ), $c, [ '93.184.216.34' ], [] );
$f->fetch( 'arxiv', $url, decl( [ 'pacing' => 3 ] ) );
$f->fetch( 'arxiv', $url, decl( [ 'pacing' => 3 ] ) );
G::ok( $c->slept === [ 3.0 ], 'FX11 the second call to one source waits the declared 3 s', json_encode( $c->slept ) );
$f->fetch( 'crossref', $url, decl( [ 'pacing' => 3 ] ) );
G::ok( $c->slept === [ 3.0 ], 'FX11 a call to another source waits for nothing' );
$c->now += 10;
$f->fetch( 'arxiv', $url, decl( [ 'pacing' => 3 ] ) );
G::ok( $c->slept === [ 3.0 ], 'FX11 a call after the pacing has passed waits for nothing' );
$c = new Clock;
$w = new Wire( [ ok200( 'a' ), ok200( 'b' ) ] );
$f = live( $w, $c );
$w->each = static function () use ( &$f, &$inner ): void {
	if ( $inner === null ) {
		$inner = word( static fn () => $f->fetch( SOURCE, 'https://' . HOST . '/again', decl() ) );
	}
};
$inner = null;
$f->fetch( SOURCE, $url, decl() );
G::ok( $inner === FetchFault::BUSY, 'FX11 refused: a second request to one source while one is in flight', (string)$inner );
G::ok( word( static fn () => $f->fetch( SOURCE, $url, decl() ) ) !== FetchFault::BUSY, 'FX11 passed: the source is free again after the request ended' );
$w = new Wire( [ new FetchFault( FetchFault::TRANSPORT ), ok200( 'b' ) ] );
$f = live( $w, new Clock );
word( static fn () => $f->fetch( SOURCE, $url, decl() ) );
G::ok( $f->fetch( SOURCE, $url, decl() ) === 'b', 'FX11 a failed request frees the source too' );

// FX12 the run's caps
$c = new Clock;
$w = new Wire( [ ok200( 'a' ), ok200( 'b' ), ok200( 'c' ) ] );
$f = live( $w, $c, [ '93.184.216.34' ], [], 100, null );
$f->fetch( SOURCE, $url, decl() );
$c->now += 99;
$f->fetch( 'two', $url, decl() );
$c->now += 1;
refused( static fn () => $f->fetch( 'three', $url, decl() ), FetchFault::CAP, 'FX12 refused: the run\'s lookup time is spent' );
$w = new Wire( [ ok200( 'a' ), ok200( 'b' ), ok200( 'c' ) ] );
$f = live( $w, new Clock, [ '93.184.216.34' ], [], null, 2 );
$f->fetch( 'a', $url, decl() );
$f->fetch( 'b', $url, decl() );
refused( static fn () => $f->fetch( 'c', $url, decl() ), FetchFault::CAP, 'FX12 refused: the run\'s lookup count is spent' );
G::ok( count( $w->sent ) === 2, 'FX12a the request past the cap was never made' );

// FX13 certificate, status, schema
refused( static fn () => live( new Wire( [ new FetchFault( FetchFault::CERTIFICATE ) ] ), new Clock )->fetch( SOURCE, $url, decl() ), FetchFault::CERTIFICATE, 'FX13 refused: the certificate was not accepted' );
refused( static fn () => live( new Wire( [ new RuntimeException( 'SSL: self signed certificate at ' . $url ) ] ), new Clock )->fetch( SOURCE, $url, decl() ), FetchFault::TRANSPORT, 'FX13 refused: any other transport failure is TRANSPORT, its text dropped' );
refused( static fn () => live( new Wire( [ [ 'status' => 404, 'location' => null, 'body' => 'x', 'ip' => '93.184.216.34' ] ] ), new Clock )->fetch( SOURCE, $url, decl() ), FetchFault::STATUS, 'FX13 refused: a status other than 200' );
$json = static fn ( string $b ): bool => json_decode( $b ) !== null;
refused( static fn () => live( new Wire( [ ok200( '{broken' ) ] ), new Clock )->fetch( SOURCE, $url, decl( [ 'schema' => $json ] ) ), FetchFault::SCHEMA, 'FX13 refused: a payload that fails its schema, whole' );
G::ok( live( new Wire( [ ok200( '{"a":1}' ) ] ), new Clock )->fetch( SOURCE, $url, decl( [ 'schema' => $json ] ) ) === '{"a":1}', 'FX13 passed: a payload that meets its schema' );
G::ok( FetchGuard::digest( 'abc' ) === 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad', 'FX13 the digest is the SHA-256 of the raw download' );

// FX14 the contact value
$w = new Wire( [ ok200( 'x' ) ] );
live( $w, new Clock )->fetch( SOURCE, $url, decl( [ 'contact' => [ 'in' => 'agent' ] ] ) );
G::ok( in_array( 'User-Agent: ' . LiveFetcher::AGENT . ' (mailto:' . CONTACT . ')', $w->sent[0]['headers'], true ), 'FX14 passed: the contact value is sent in the agent string' );
$w = new Wire( [ ok200( 'x' ) ] );
live( $w, new Clock, [ '93.184.216.34' ], [ SOURCE => 'a+b@mail.example' ] )->fetch( SOURCE, $url, decl( [ 'contact' => [ 'in' => 'query', 'param' => 'mailto' ] ] ) );
G::ok( $w->sent[0]['url'] === $url . '&mailto=a%2Bb%40mail.example', 'FX14 passed: the contact value is sent as one encoded query parameter', $w->sent[0]['url'] );
$w = new Wire( [ ok200( 'x' ) ] );
live( $w, new Clock )->fetch( SOURCE, $url, decl() );
G::ok( strpos( json_encode( $w->sent ), CONTACT ) === false, 'FX14 passed: no contact value is sent where the declaration names no place' );
$w = new Wire( [ ok200( 'x' ) ] );
live( $w, new Clock, [ '93.184.216.34' ], [ 'other' => CONTACT ] )->fetch( SOURCE, $url, decl( [ 'contact' => [ 'in' => 'agent' ] ] ) );
G::ok( strpos( json_encode( $w->sent ), CONTACT ) === false, 'FX14 passed: a source with no value of its own is sent none' );
foreach ( [ "a@b\r\nX: y", 'a b', "a\0b" ] as $badContact ) {
	G::refuses( static fn () => live( new Wire( [] ), new Clock, [ '93.184.216.34' ], [ SOURCE => $badContact ] ), InvalidArgumentException::class, 'contact value', 'FX14 refused: a contact value that could split a header' );
}
// Everything a failing or passing fetch shows, by every fault: no contact value
$seen = [];
$faults = [ FetchFault::TIME, FetchFault::SIZE, FetchFault::CERTIFICATE, FetchFault::TRANSPORT ];
foreach ( $faults as $fw ) {
	$seen[] = shown( static fn () => live( new Wire( [ new FetchFault( $fw ) ] ), new Clock )->fetch( SOURCE, $url, decl( [ 'contact' => [ 'in' => 'agent' ] ] ) ) );
}
$seen[] = shown( static fn () => live( new Wire( [ new RuntimeException( 'failed: ' . CONTACT ) ] ), new Clock )->fetch( SOURCE, $url, decl( [ 'contact' => [ 'in' => 'agent' ] ] ) ) );
$seen[] = shown( static fn () => live( new Wire( [ redir( 'https://evil.example/?' . CONTACT ) ] ), new Clock )->fetch( SOURCE, $url, decl( [ 'contact' => [ 'in' => 'agent' ] ] ) ) );
$seen[] = shown( static fn () => live( new Wire( [ ok200( '{broken' ) ] ), new Clock )->fetch( SOURCE, $url, decl( [ 'contact' => [ 'in' => 'query', 'param' => 'mailto' ] , 'schema' => $json ] ) ) );
$f = live( new Wire( [] ), new Clock );
ob_start();
print_r( $f );
var_dump( $f );
var_export( $f );
$seen[] = ob_get_clean() . serialize( $f ) . json_encode( $f );
$seen[] = FetchGuard::scrub( 'refused: ' . CONTACT . ' and ' . rawurlencode( CONTACT ) . ' and ' . urlencode( 'a+b@mail.example' ), [ CONTACT, 'a+b@mail.example' ] );
G::ok( strpos( implode( "\n", $seen ), CONTACT ) === false && strpos( implode( "\n", $seen ), rawurlencode( CONTACT ) ) === false,
	'FX14 passed: the contact value is in no fault, no dump of the object and no scrubbed text (' . count( $seen ) . ' outputs scanned)' );
G::ok( strpos( $seen[count( $seen ) - 1], '[contact]' ) !== false && strpos( $seen[count( $seen ) - 1], 'a+b' ) === false, 'FX14 the scrub cuts raw and encoded forms' );
$msgs = [];
foreach ( FetchFault::WORDS as $fw ) {
	$msgs[] = ( new FetchFault( $fw, SOURCE ) )->getMessage();
}
G::ok( count( array_unique( $msgs ) ) === count( FetchFault::WORDS ) && preg_match( '#https?://|\d+\.\d+\.\d+\.\d+|/#', implode( ' ', $msgs ) ) === 0,
	'FX14 a fault\'s message is one fixed sentence per word: no address, host or path' );
G::ok( ( new FetchFault( 'NOT A WORD' ) )->word === FetchFault::TRANSPORT, 'FX14 a word outside the closed set is TRANSPORT' );

// FX14 (FakeFetcher): serves canned text through the guards, makes no request
$fake = new FakeFetcher( [ $url => 'canned', 'https://' . HOST . '/big' => str_repeat( 'a', 11 ), 'https://' . HOST . '/down' => new FetchFault( FetchFault::CERTIFICATE ) ] );
G::ok( $fake->fetch( SOURCE, $url, decl() ) === 'canned' && $fake->calls === [ [ SOURCE, $url ] ], 'FX14a FakeFetcher serves canned text and records the call' );
refused( static fn () => $fake->fetch( SOURCE, 'https://' . HOST . '/missing', decl() ), FetchFault::TRANSPORT, 'FX14a FakeFetcher: no canned text is a TRANSPORT fault' );
refused( static fn () => $fake->fetch( SOURCE, 'https://other.example/x', decl() ), FetchFault::HOST, 'FX14a FakeFetcher applies the host guard' );
refused( static fn () => $fake->fetch( SOURCE, 'https://' . HOST . '/big', decl( [ 'max_bytes' => 10 ] ) ), FetchFault::SIZE, 'FX14a FakeFetcher applies the size guard' );
refused( static fn () => $fake->fetch( SOURCE, 'https://' . HOST . '/down', decl() ), FetchFault::CERTIFICATE, 'FX14a FakeFetcher serves a canned failure' );
$c = new Clock;
$fake = new FakeFetcher( [ $url => 'a' ], new FetchGuard( static fn (): float => $c->now, [ $c, 'sleep' ] ) );
$fake->fetch( SOURCE, $url, decl( [ 'pacing' => 3 ] ) );
$fake->fetch( SOURCE, $url, decl( [ 'pacing' => 3 ] ) );
G::ok( $c->slept === [ 3.0 ], 'FX14a FakeFetcher obeys a declared pacing on its guard\'s clock' );

// FX15 the curl options, built by a pure function (no handle, no network)
$o = LiveFetcher::curlOptions( 'https://' . strtoupper( HOST ) . ':443/api/query?id=1#frag', HOST, '93.184.216.34', [ 'Accept: */*' ], 2.5 );
G::ok( ( $o[CURLOPT_PROXY] ?? null ) === '' && ( $o[CURLOPT_NOPROXY] ?? null ) === '*', 'FX15 passed: no proxy, so a proxy in the environment cannot bypass the pinned address' );
G::ok( ( $o[CURLOPT_URL] ?? null ) === 'https://' . HOST . '/api/query?id=1', 'FX15 passed: curl is given the URL rebuilt from the parts the guard approved, not the raw text', (string)( $o[CURLOPT_URL] ?? '' ) );
G::ok( ( $o[CURLOPT_RESOLVE] ?? null ) === [ HOST . ':443:93.184.216.34' ] && ( $o[CURLOPT_CONNECT_TO] ?? null ) === [ HOST . ':443:93.184.216.34:443' ], 'FX15 passed: the connection is pinned to the checked address (resolve and connect-to)' );
G::ok( ( $o[CURLOPT_FOLLOWLOCATION] ?? null ) === false && ( $o[CURLOPT_SSL_VERIFYPEER] ?? null ) === true && ( $o[CURLOPT_SSL_VERIFYHOST] ?? null ) === 2, 'FX15 passed: no redirect followed by curl, the certificate and host verified' );
G::ok( ( $o[CURLOPT_PROTOCOLS_STR] ?? $o[CURLOPT_PROTOCOLS] ?? null ) === ( defined( 'CURLOPT_PROTOCOLS_STR' ) ? 'https' : CURLPROTO_HTTPS ), 'FX15 passed: https the only protocol (the string form where curl has it, else the bit mask)' );
G::ok( ( $o[CURLOPT_TIMEOUT_MS] ?? null ) === 2500 && ( $o[CURLOPT_HTTPHEADER] ?? null ) === [ 'Accept: */*' ], 'FX15 passed: the time limit and the headers' );
G::ok( LiveFetcher::curlOptions( 'https://' . HOST . '?x=1', HOST, '93.184.216.34', [], 1.0 )[CURLOPT_URL] === 'https://' . HOST . '/?x=1', 'FX15 passed: an empty path is rebuilt as /' );
refused( static fn () => LiveFetcher::curlOptions( 'https://other.example/a', HOST, '93.184.216.34', [], 1.0 ), FetchFault::HOST, 'FX15 refused: a URL whose host is not the checked one' );
refused( static fn () => LiveFetcher::curlOptions( 'http://' . HOST . '/a', HOST, '93.184.216.34', [], 1.0 ), FetchFault::SCHEME, 'FX15 refused: a URL that is not https' );
// FX15b a slow name lookup counts against the time limit, and no request follows it
$c5 = new Clock;
$w5 = new Wire( [ ok200( 'x' ) ] );
refused( static function () use ( $c5, $w5, $url ): void {
	live( $w5, $c5, static function ( string $h ) use ( $c5 ): array {
		$c5->now += 31;
		return [ '93.184.216.34' ];
	} )->fetch( SOURCE, $url, decl() );
}, FetchFault::TIME, 'FX15b refused: a name lookup that outlasts the time limit' );
G::ok( $w5->sent === [], 'FX15b no request was made after it' );
// FX15a no contact value reaches an exception's trace arguments
$keep = ini_get( 'zend.exception_ignore_args' );
ini_set( 'zend.exception_ignore_args', '0' );
$args = [];
foreach ( [ [ 'in' => 'agent' ], [ 'in' => 'query', 'param' => 'mailto' ] ] as $place ) {
	try {
		live( new Wire( [ new RuntimeException( 'down' ) ] ), new Clock )->fetch( SOURCE, $url, decl( [ 'contact' => $place ] ) );
	} catch ( FetchFault $e ) {
		$t = $e->getTrace();
		array_walk_recursive( $t, static function ( $v ) use ( &$args ): void {
			if ( is_string( $v ) ) {
				$args[] = $v;
			}
		} );
	}
}
ini_set( 'zend.exception_ignore_args', (string)$keep );
G::ok( $args !== [] && strpos( implode( "\n", $args ), 'mail.example' ) === false, 'FX15a passed: no contact value in the arguments of a fault\'s trace (' . count( $args ) . ' strings read)' );

// The configuration entry
$ext = json_decode( (string)file_get_contents( dirname( __DIR__ ) . '/extension.json' ), true, 16, JSON_THROW_ON_ERROR );
G::ok( ( $ext['config']['CustosRegistryContact']['value'] ?? null ) === [] && ( $ext['config']['CustosRegistryContact']['merge_strategy'] ?? '' ) === 'provide_default',
	'FX14b extension.json carries CustosRegistryContact, empty by default (no contact value shipped)' );

exit( G::report( 'fetcher' ) );
