<?php
/** ClusterJob: the job class `custosCluster`, the cluster month through the batch frame (BatchJob). NOT BUILT until its unit. */

namespace Custos;

final class ClusterJob extends BatchJobBase {
	public const TYPE = 'custosCluster';

	protected static function jobName(): string {
		return BatchJob::CLUSTER;
	}
}
