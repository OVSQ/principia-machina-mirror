<?php
/**
 * FetchFault: a fetch the layer refused or could not complete. $word is one of WORDS, the closed
 * set the jobs map to SOURCE FAILING; $source is the declared source's name (a registry or a
 * dataset, as the declaration names it) or ''. The message is a fixed sentence per word: never a
 * host, an address, a URL, a query, the contact value or the transport's own text.
 */

namespace Custos;

use RuntimeException;

final class FetchFault extends RuntimeException {
	public const SCHEME = 'SCHEME';
	public const HOST = 'HOST';
	public const ADDRESS = 'ADDRESS';
	public const REDIRECT = 'REDIRECT';
	public const TIME = 'TIME';
	public const SIZE = 'SIZE';
	public const ARCHIVE = 'ARCHIVE';
	public const CERTIFICATE = 'CERTIFICATE';
	public const CAP = 'CAP';
	public const BUSY = 'BUSY';
	public const SCHEMA = 'SCHEMA';
	public const STATUS = 'STATUS';
	public const TRANSPORT = 'TRANSPORT';

	/** Every word a FetchFault carries. */
	public const WORDS = [
		self::SCHEME, self::HOST, self::ADDRESS, self::REDIRECT, self::TIME, self::SIZE, self::ARCHIVE,
		self::CERTIFICATE, self::CAP, self::BUSY, self::SCHEMA, self::STATUS, self::TRANSPORT,
	];

	private const SENTENCES = [
		self::SCHEME => 'the address is not an HTTPS address of the allowed form',
		self::HOST => 'the host is not one the declaration names',
		self::ADDRESS => 'the host resolved to, or connected to, an address outside the allowed ranges',
		self::REDIRECT => 'a redirect left the declared hosts or passed the hop limit',
		self::TIME => 'the declared time ran out',
		self::SIZE => 'the download passed the size limit',
		self::ARCHIVE => 'the archive broke a limit or held a member the declaration does not name',
		self::CERTIFICATE => 'the certificate was not accepted',
		self::CAP => 'the run\'s lookup time or lookup count cap was reached',
		self::BUSY => 'a request to this source was already in flight',
		self::SCHEMA => 'the payload failed its declared response schema',
		self::STATUS => 'the source answered a status other than success',
		self::TRANSPORT => 'the request could not be completed',
	];

	public readonly string $word;
	public readonly string $source;

	public function __construct( string $word, string $source = '' ) {
		$word = in_array( $word, self::WORDS, true ) ? $word : self::TRANSPORT;
		parent::__construct( "fetch refused: $word: " . self::SENTENCES[$word] );
		$this->word = $word;
		$this->source = $source;
	}
}
