package org.libpetri.runtime;

import org.libpetri.core.*;

import java.util.List;
import java.util.Map;

/** {@link AbstractExecutorSnapshotTest} against the reference executor. */
class BitmapExecutorSnapshotTest extends AbstractExecutorSnapshotTest {
    @Override
    protected PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, Options options
    ) {
        var builder = BitmapNetExecutor.builder(net, initial);
        if (options.restore() != null) builder.restore(options.restore());
        if (options.environment() != null) builder.environment(options.environment());
        if (options.environmentPlaces() != null) builder.environmentPlaces(options.environmentPlaces());
        if (options.eventStore() != null) builder.eventStore(options.eventStore());
        if (options.executor() != null) builder.orchestratorExecutor(options.executor());
        return builder.build();
    }

    @Override
    protected void snapshotCap(PetriNetExecutor executor, java.time.Duration cap) {
        ((BitmapNetExecutor) executor).snapshotWaitNanosForTesting(cap.toNanos());
    }

    @Override
    protected boolean parked(PetriNetExecutor executor) {
        return ((BitmapNetExecutor) executor).parkedForTesting();
    }

    @Override
    protected long markingRequests(PetriNetExecutor executor) {
        return ((BitmapNetExecutor) executor).markingRequestsForTesting();
    }
}
