package org.libpetri.runtime;

import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.time.Duration;
import java.util.concurrent.CompletableFuture;

import org.libpetri.core.Arc;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.Transition;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Token;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

@Timeout(60)
class PrecompiledNetExecutorEngineTest extends AbstractNetExecutorEngineTest {

    @Override
    protected PetriNetExecutor createExecutor(PetriNet net, Map<Place<?>, List<Token<?>>> initial) {
        return PrecompiledNetExecutor.create(net, initial);
    }

    @Override
    protected PetriNetExecutor createExecutor(PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store) {
        return PrecompiledNetExecutor.create(net, initial, store);
    }

    @Override
    protected PetriNetExecutor createExecutorWithEnv(PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store, Set<EnvironmentPlace<?>> envPlaces) {
        return PrecompiledNetExecutor.builder(net, initial).eventStore(store).environmentPlaces(envPlaces).build();
    }

    @Override
    protected PetriNetExecutor createExecutorWithEnv(PetriNet net, Map<Place<?>, List<Token<?>>> initial, Set<EnvironmentPlace<?>> envPlaces) {
        return PrecompiledNetExecutor.builder(net, initial).environmentPlaces(envPlaces).build();
    }

    @Override
    protected PetriNetExecutor createExecutorWithHandler(PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store, ActionFailureHandler handler) {
        return PrecompiledNetExecutor.builder(net, initial).eventStore(store).uncaughtActionHandler(handler).build();
    }

    /**
     * NU-054: the relay check is part of output validation, so it is skipped exactly where
     * output validation is ([CONC-026]): with {@code skipOutputValidation} a wrong-name token is
     * deposited without a failure.
     */
    @Test
    void nuRelay_checkSkippedWithOutputValidation() {
        var a = Place.of("A", NuMsg.class);
        var b = Place.of("B", NuMsg.class);
        var out = Place.of("OUT", NuMsg.class);
        var join = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (NuMsg m) -> NameId.of(m.cid()))
                .key(b, (NuMsg m) -> NameId.of(m.cid()))
                .relayTo(out, (NuMsg m) -> NameId.of(m.cid()))
                .build())
            .outputs(Arc.Out.place(out))
            .action(ctx -> {
                ctx.output(out, new NuMsg("OTHER"));
                return CompletableFuture.completedFuture(null);
            })
            .build();
        var net = PetriNet.builder("nuRelaySkip").transitions(join).build();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            a, List.of(Token.of(new NuMsg("X"))), b, List.of(Token.of(new NuMsg("X"))));
        var store = EventStore.inMemory();
        try (var executor = PrecompiledNetExecutor.builder(net, initial)
                .eventStore(store).skipOutputValidation(true).build()) {
            var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();
            assertEquals(1, result.tokenCount(out), "skipped validation deposits the token");
            assertTrue(store.events().stream().noneMatch(e -> e instanceof NetEvent.TransitionFailed));
        }
    }

}
