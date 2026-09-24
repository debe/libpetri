package org.libpetri.runtime;

import org.libpetri.core.*;
import org.libpetri.event.EventStore;

import java.util.List;
import java.util.Map;
import java.util.Set;

/** {@link AbstractTerminalPlaceTest} against the production executor. */
class PrecompiledTerminalPlaceTest extends AbstractTerminalPlaceTest {
    @Override
    protected PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, Set<EnvironmentPlace<?>> environmentPlaces,
        EventStore store, ExecutionEnvironment environment
    ) {
        var builder = PrecompiledNetExecutor.builder(net, initial).environmentPlaces(environmentPlaces);
        if (store != null) builder.eventStore(store);
        if (environment != null) builder.environment(environment);
        return builder.build();
    }
}
