<?php
/**
 * Certify: one agent's certificate written to the table custos_certificate, the Operator's act on
 * the command line at an admission the Declarer declares. The only writer of the table:
 *
 *   php maintenance/run.php Custos:Certify --agent <account> --sponsor <account> --d-is <hex64>
 *       --d-prompt <hex64> --family <vendor family> --model <declared model> [--state <state>]
 *
 * Inserts the agent's row, or replaces it whole when one is there (a new Sponsor, a new D(PROMPT),
 * a state SUSPENDED or REVOKED). Prints one line, `certify: <agent> sponsor <sponsor>`; prints no
 * secret (a certificate holds none: two account names, two digests, two words and a state).
 *
 * Refused, nothing written: an account name empty, holding a control character or longer than 255
 * bytes; an agent named as its own Sponsor; a digest not 64 lowercase hexadecimal digits; a family
 * longer than 64 bytes or a model longer than 255, or either empty; a state not ACTIVE, SUSPENDED
 * or REVOKED (default ACTIVE).
 *
 * Admission (Landing) reads the row: an agent with none, or one not ACTIVE, is refused ADMISSION
 * before the governor is asked; otherwise its Sponsor's seats are charged. The rehearsal
 * (custos/tests/rehearsal.sh) and the live exercise (the acceptance script of the rehearsal wiki) seed their agents'
 * rows through this script.
 */

namespace Custos\Maintenance;

use Custos\CertificateStore;
use Custos\DbCertificateStore;
use MediaWiki\Maintenance\Maintenance;

final class Certify extends Maintenance {
	public function __construct() {
		parent::__construct();
		$this->addDescription( 'Custos: write one agent\'s certificate (its Sponsor, D(IS), D(PROMPT), vendor family, declared model, state), replacing the agent\'s row when present' );
		$this->addOption( 'agent', 'The agent account\'s user name', true, true );
		$this->addOption( 'sponsor', 'The Sponsor account\'s user name', true, true );
		$this->addOption( 'd-is', 'D(IS), 64 lowercase hexadecimal digits', true, true );
		$this->addOption( 'd-prompt', 'D(PROMPT), 64 lowercase hexadecimal digits', true, true );
		$this->addOption( 'family', 'The vendor family', true, true );
		$this->addOption( 'model', 'The declared model', true, true );
		$this->addOption( 'state', 'ACTIVE (default), SUSPENDED or REVOKED', false, true );
		$this->requireExtension( 'Custos' );
	}

	public function execute() {
		$row = [
			'agent' => (string)$this->getOption( 'agent' ),
			'sponsor' => (string)$this->getOption( 'sponsor' ),
			'd_is' => (string)$this->getOption( 'd-is' ),
			'd_prompt' => (string)$this->getOption( 'd-prompt' ),
			'family' => (string)$this->getOption( 'family' ),
			'model' => (string)$this->getOption( 'model' ),
			'state' => (string)$this->getOption( 'state', CertificateStore::ACTIVE ),
		];
		$why = self::refusal( $row );
		if ( $why !== null ) {
			$this->fatalError( "certify: $why; nothing written" );
		}
		( new DbCertificateStore() )->put( $row );
		$this->output( "certify: {$row['agent']} sponsor {$row['sponsor']}\n" );
	}

	/** Why $row may not be written, or null when it may. */
	public static function refusal( array $row ): ?string {
		foreach ( [ 'agent' => 255, 'sponsor' => 255, 'family' => 64, 'model' => 255 ] as $f => $max ) {
			$v = $row[$f];
			if ( $v === '' || strlen( $v ) > $max || preg_match( '/[\x00-\x1f\x7f]/', $v ) || !mb_check_encoding( $v, 'UTF-8' ) ) {
				return "the $f is empty, longer than $max bytes, not UTF-8 or holds a control character";
			}
		}
		if ( $row['agent'] === $row['sponsor'] ) {
			return 'an agent is not its own Sponsor';
		}
		foreach ( [ 'd_is' => 'D(IS)', 'd_prompt' => 'D(PROMPT)' ] as $f => $name ) {
			if ( !preg_match( '/\A[0-9a-f]{64}\z/', $row[$f] ) ) {
				return "$name is not 64 lowercase hexadecimal digits";
			}
		}
		if ( !in_array( $row['state'], CertificateStore::STATES, true ) ) {
			return 'the state is not one of ' . implode( ', ', CertificateStore::STATES );
		}
		return null;
	}
}

return Certify::class;
