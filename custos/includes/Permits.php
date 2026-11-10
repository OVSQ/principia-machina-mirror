<?php
/**
 * Permits: the permissions table, read from custos/permits.json, the file
 * scripts/permits_table.py generates from the built Calculator's `pcalc permissions table {}`
 * (every cell `permits` on its arguments: the theorem `table_lookup_eq_permits`,
 * Principia/Calculator/Permissions.lean). custos-tests checks the file byte for byte against the
 * binary and its digest, custos/permits.sha256.
 *
 * This is the one place Custos's PHP reads JSON: the file is the repository's, written by the
 * Calculator and shipped with the extension, never a page's text (README, "The permits table").
 * It is read once per request cycle and kept in a static.
 *
 * admits() answers a request whose facts are partly unknown: it admits only when, for every
 * value an unknown fact may take, one of the asker's words is PERMITTED. A cell the table lacks,
 * or a word it does not carry, refuses.
 */

namespace Custos;

final class Permits {
	/** The context words, as the Calculator's domain spells them. */
	public const POLICIES = [ null, 'OPEN', 'CLOSED' ];
	public const DOSSIER_READS = [ 'USER ONLY', 'USER AND AGENT', 'NEITHER' ];
	public const LOCK_STATES = [ null, 'HOLDER', 'COWORKER' ];

	private static ?self $loaded = null;

	/** @param array $cells asker => class => op => list of 96 words; @param array $index context key => position */
	private function __construct( private array $cells, private array $index ) {
	}

	/** The extension's own table, read once per request cycle. @throws PageFault */
	public static function table(): self {
		return self::$loaded ??= self::fromFile( dirname( __DIR__ ) . '/permits.json' );
	}

	/** @throws PageFault */
	public static function fromFile( string $path ): self {
		$text = is_file( $path ) ? file_get_contents( $path ) : false;
		if ( !is_string( $text ) ) {
			throw new PageFault( 'the permits table is not readable' );
		}
		return self::fromText( $text );
	}

	/** @throws PageFault */
	public static function fromText( string $text ): self {
		try {
			$t = json_decode( $text, true, 8, JSON_THROW_ON_ERROR );
		} catch ( \JsonException $e ) {
			throw new PageFault( 'the permits table is not JSON' );
		}
		if ( !is_array( $t ) || !is_array( $t['cells'] ?? null ) || !is_array( $t['contexts'] ?? null ) ) {
			throw new PageFault( 'the permits table carries no cells or contexts' );
		}
		$index = [];
		foreach ( $t['contexts'] as $i => $words ) {
			if ( !is_array( $words ) ) {
				throw new PageFault( 'a context of the permits table is not a list' );
			}
			$index[self::key( $words )] = $i;
		}
		if ( count( $index ) !== count( $t['contexts'] ) ) {
			throw new PageFault( 'two contexts of the permits table are the same' );
		}
		return new self( $t['cells'], $index );
	}

	/** A context's key: its words sorted (each word of the domain is distinct). */
	private static function key( array $words ): string {
		sort( $words, SORT_STRING );
		return implode( "\n", $words );
	}

	/** A context's words, in any order. */
	public static function words( ?string $policy, bool $listed, ?string $dossier, bool $head, bool $reauth ): array {
		$w = [];
		if ( $policy !== null ) {
			$w[] = $policy;
		}
		if ( $listed ) {
			$w[] = 'LISTED';
		}
		if ( $dossier !== null ) {
			$w[] = 'NAMED';
			$w[] = $dossier;
		}
		if ( $head ) {
			$w[] = 'QUEUE HEAD';
		}
		if ( $reauth ) {
			$w[] = 'REAUTHENTICATED';
		}
		return $w;
	}

	/** The cell: true PERMITTED, false REFUSED, null when the table lacks it. */
	public function cell( string $asker, string $class, string $op, array $context ): ?bool {
		$i = $this->index[self::key( $context )] ?? null;
		$w = $i === null ? null : ( $this->cells[$asker][$class][$op][$i] ?? null );
		return $w === 'PERMITTED' ? true : ( $w === 'REFUSED' ? false : null );
	}

	/**
	 * Whether the request is admitted. $askers: the asker words the account definitely holds
	 * (it is permitted what any one of them is). $facts: each fact a list of the values it may
	 * take, one value when it is known: "lock" (an agent account's lock state: null, HOLDER,
	 * COWORKER; [] for a user account), "policy", "listed", "dossier" (null: the title names
	 * not the asker), "head", "reauth". Admitted only when every combination is PERMITTED for
	 * one of the askers (the agent's lock state among them); an empty list of a fact admits
	 * nothing.
	 */
	public function admits( array $askers, string $class, string $op, array $facts ): bool {
		$locks = $facts['lock'] ?? [];
		foreach ( [ 'policy', 'listed', 'dossier', 'head', 'reauth' ] as $f ) {
			if ( !is_array( $facts[$f] ?? null ) || $facts[$f] === [] ) {
				return false;
			}
		}
		foreach ( $locks === [] ? [ false ] : $locks as $lock ) {
			$who = $askers;
			if ( $lock !== false ) {
				$who[] = $lock ?? 'AGENT';
			}
			if ( $who === [] ) {
				return false;
			}
			foreach ( $facts['policy'] as $p ) {
				foreach ( $facts['listed'] as $l ) {
					foreach ( $facts['dossier'] as $d ) {
						foreach ( $facts['head'] as $h ) {
							foreach ( $facts['reauth'] as $r ) {
								$ctx = self::words( $p, $l, $d, $h, $r );
								$any = false;
								foreach ( $who as $a ) {
									if ( $this->cell( $a, $class, $op, $ctx ) === true ) {
										$any = true;
										break;
									}
								}
								if ( !$any ) {
									return false;
								}
							}
						}
					}
				}
			}
		}
		return true;
	}
}
