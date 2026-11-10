<?php
/**
 * MwStore: the PageStore over MediaWiki's services. Custos writes every page as the system
 * user "Custos", except a casPut or an appendAs, whose revision is the named account's own
 * (a Holder's lock edit, the Declarer's line). Thin glue: no digest, no record shape and no
 * chain rule lives here; those are the Calculator's. MediaWiki 1.46.
 */

namespace Custos;

use MediaWiki\CommentStore\CommentStoreComment;
use MediaWiki\Content\TextContent;
use MediaWiki\Content\WikitextContent;
use MediaWiki\MediaWikiServices;
use MediaWiki\Revision\RevisionRecord;
use MediaWiki\Revision\SlotRecord;
use MediaWiki\Title\Title;
use MediaWiki\User\User;
use RuntimeException;

final class MwStore implements PageStore {
	/** The system user every write of Custos's own is made as. */
	public const SYSTEM_USER = 'Custos';

	private MediaWikiServices $services;
	private ?User $custos = null;

	public function __construct( ?MediaWikiServices $services = null ) {
		$this->services = $services ?? MediaWikiServices::getInstance();
	}

	public function get( string $title ): ?string {
		$rev = $this->services->getRevisionLookup()->getRevisionByTitle( $this->title( $title ) );
		if ( $rev === null ) {
			return null;
		}
		$content = $rev->getContent( SlotRecord::MAIN, RevisionRecord::RAW );
		return $content instanceof TextContent ? $content->getText() : null;
	}

	public function exists( string $title ): bool {
		return $this->title( $title )->exists();
	}

	public function put( string $title, string $text, string $summary ): void {
		if ( $this->get( $title ) === $text ) {
			return;
		}
		if ( !$this->save( $title, $text, $summary, $this->custos(), null ) ) {
			throw new RuntimeException( "the page \"$title\" was not saved" );
		}
	}

	/**
	 * The page's latest revision is pinned as the parent (grabParentRevision); the parent's text
	 * must equal $expected, and the save is conditional on that parent still being the latest,
	 * so a racing edit fails as an edit conflict and nothing is written.
	 */
	public function casPut( string $title, ?string $expected, string $text, string $summary, string $actor ): bool {
		$page = $this->services->getWikiPageFactory()->newFromTitle( $this->title( $title ) );
		$updater = $page->newPageUpdater( $this->account( $actor ) );
		$parent = $updater->grabParentRevision();
		$current = null;
		if ( $parent !== null ) {
			$content = $parent->getContent( SlotRecord::MAIN, RevisionRecord::RAW );
			$current = $content instanceof TextContent ? $content->getText() : null;
			if ( $current === null ) {
				return false;
			}
		}
		if ( $current !== $expected ) {
			return false;
		}
		if ( $current === $text ) {
			return true;
		}
		$updater->setContent( SlotRecord::MAIN, new WikitextContent( $text ) );
		$updater->saveRevision( CommentStoreComment::newUnsavedComment( $summary ),
			EDIT_INTERNAL | EDIT_FORCE_BOT | ( $parent !== null ? EDIT_UPDATE : EDIT_NEW ) );
		return $updater->wasSuccessful();
	}

	public function appendAs( string $title, string $line, string $summary, string $actor ): string {
		$current = $this->get( $title ) ?? '';
		$new = $current === '' ? $line : $current . "\n" . $line;
		if ( !$this->save( $title, $new, $summary, $this->account( $actor ), $current === '' ? null : $current ) ) {
			throw new RuntimeException( "the page \"$title\" was not saved" );
		}
		return $new;
	}

	private function title( string $title ): Title {
		$t = $this->services->getTitleFactory()->newFromText( $title );
		if ( $t === null ) {
			throw new RuntimeException( "not a title: $title" );
		}
		return $t;
	}

	private function custos(): User {
		if ( $this->custos === null ) {
			$user = User::newSystemUser( self::SYSTEM_USER, [ 'steal' => true ] );
			if ( $user === null ) {
				throw new RuntimeException( 'the system user ' . self::SYSTEM_USER . ' cannot be made' );
			}
			$this->custos = $user;
		}
		return $this->custos;
	}

	/** The named registered account; Custos when there is none of that name. */
	private function account( string $name ): User {
		$user = $this->services->getUserFactory()->newFromName( $name );
		return ( $user !== null && $user->isRegistered() ) ? $user : $this->custos();
	}

	/** One save; with $expected, the parent read is pinned so a racing edit fails the save. */
	private function save( string $title, string $text, string $summary, User $user, ?string $expected ): bool {
		$page = $this->services->getWikiPageFactory()->newFromTitle( $this->title( $title ) );
		$updater = $page->newPageUpdater( $user );
		if ( $expected !== null ) {
			$updater->grabParentRevision();
		}
		$updater->setContent( SlotRecord::MAIN, new WikitextContent( $text ) );
		$updater->saveRevision( CommentStoreComment::newUnsavedComment( $summary ), EDIT_INTERNAL | EDIT_FORCE_BOT );
		return $updater->wasSuccessful();
	}
}
