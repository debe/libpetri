package org.libpetri.runtime;

import org.libpetri.core.*;
import org.libpetri.event.EventStore;
import java.util.List;
import java.util.Map;

/** {@link AbstractTerminationReasonTest} against the reference executor. */
class BitmapTerminationReasonTest extends AbstractTerminationReasonTest {
    @Override
    protected PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial) {
        return BitmapNetExecutor.builder(net, initial).build();
    }

    @Override
    protected PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store
    ) {
        return BitmapNetExecutor.builder(net, initial).eventStore(store).build();
    }

    @Override
    protected PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store,
        ExecutionEnvironment environment
    ) {
        var builder = BitmapNetExecutor.builder(net, initial);
        if (store != null) builder.eventStore(store);
        if (environment != null) builder.environment(environment);
        return builder.build();
    }
}
