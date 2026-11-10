<?php
/** RecheckJob: the job class `custosRecheck`, the bibliography recheck through the batch frame (BatchJob). NOT BUILT until its unit. */

namespace Custos;

final class RecheckJob extends BatchJobBase {
	public const TYPE = 'custosRecheck';

	protected static function jobName(): string {
		return BatchJob::RECHECK;
	}
}
