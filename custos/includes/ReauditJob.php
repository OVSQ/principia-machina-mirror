<?php
/** ReauditJob: the job class `custosReaudit`, the re-audit through the batch frame (BatchJob). NOT BUILT until its unit. */

namespace Custos;

final class ReauditJob extends BatchJobBase {
	public const TYPE = 'custosReaudit';

	protected static function jobName(): string {
		return BatchJob::REAUDIT;
	}
}
