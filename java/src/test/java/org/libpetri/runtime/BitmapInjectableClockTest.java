package org.libpetri.runtime;

import org.libpetri.core.*;

import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** {@link AbstractInjectableClockTest} against the reference executor. */
class BitmapInjectableClockTest extends AbstractInjectableClockTest {

    @Override
    protected PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, ExecutionEnvironment env
    ) {
        return BitmapNetExecutor.builder(net, initial).environment(env).build();
    }

    @Override
    protected PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, ExecutionEnvironment env,
        Duration deadlineTolerance, Set<EnvironmentPlace<?>> envPlaces
    ) {
        return BitmapNetExecutor.builder(net, initial)
            .environment(env)
            .deadlineTolerance(deadlineTolerance)
            .environmentPlaces(envPlaces)
            .build();
    }
}
