package org.libpetri.runtime;

import java.util.List;
import java.util.Map;
import java.util.Set;

import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Token;
import org.libpetri.event.EventStore;

class BitmapNetExecutorEnvironmentTest extends AbstractNetExecutorEnvironmentTest {

    @Override
    protected PetriNetExecutor createExecutor(PetriNet net, Map<Place<?>, List<Token<?>>> initial) {
        return BitmapNetExecutor.create(net, initial);
    }

    @Override
    protected PetriNetExecutor createLongRunning(PetriNet net, Map<Place<?>, List<Token<?>>> initial, Set<EnvironmentPlace<?>> envPlaces) {
        return BitmapNetExecutor.builder(net, initial).environmentPlaces(envPlaces).longRunning(true).build();
    }

    @Override
    protected PetriNetExecutor createLongRunningWithStore(PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store, Set<EnvironmentPlace<?>> envPlaces) {
        return BitmapNetExecutor.builder(net, initial).eventStore(store).environmentPlaces(envPlaces).longRunning(true).build();
    }
}
