<?php
/**
 * BoxedRunner: one call through MediaWiki's shell framework in the boxed form test T2
 * measured (ops/t2/shell_lib.php): the shell command factory's createBoxed(), the network
 * disabled, firejail's default seccomp filter (where the wiki's restriction method is
 * firejail), a route name, the request on stdin. Without a remote Shellbox service it runs
 * locally in a fresh temporary folder under the wiki's $wgMaxShell* limits.
 */

namespace Custos;

use MediaWiki\MediaWikiServices;
use MediaWiki\Shell\CommandFactory;

final class BoxedRunner implements ShellRunner {
	/** The Shellbox service name (local unless the wiki configures a remote one). */
	public const SERVICE = 'custos';
	/** The route name the call carries in the shell framework's logs. */
	public const ROUTE = 'custos-pcalc';

	private CommandFactory $factory;

	public function __construct( ?CommandFactory $factory = null ) {
		$this->factory = $factory ?? MediaWikiServices::getInstance()->getShellCommandFactory();
	}

	public function run( array $argv, string $stdin ): array {
		$result = $this->factory->createBoxed( self::SERVICE )
			->disableNetwork()
			->firejailDefaultSeccomp()
			->routeName( self::ROUTE )
			->params( $argv )
			->stdin( $stdin )
			->execute();
		return [ (int)$result->getExitCode(), (string)$result->getStdout(), (string)$result->getStderr() ];
	}
}
