package org.libpetri.runtime;

import org.libpetri.core.*;
import org.libpetri.event.EventStore;
import java.util.List;
import java.util.Map;

/** {@link AbstractTerminationReasonTest} against the production executor. */
class PrecompiledTerminationReasonTest extends AbstractTerminationReasonTest {
    @Override
    protected PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial) {
        return PrecompiledNetExecutor.builder(net, initial).build();
    }

    @Override
    protected PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store
    ) {
        return PrecompiledNetExecutor.builder(net, initial).eventStore(store).build();
    }
}
