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
import static org.junit.jupiter.api.Assertions.assertThrows;
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

    /**
     * [CONC-026] AC4 to AC6: the skip covers a single-leaf spec, a composite one and the [IO-016]
     * AC4 warning, but not a write to an undeclared place ([CORE-063]) and not the build-time
     * [IO-012] check.
     */
    @Test
    void skipOutputValidation_coversTheLeafButNotAnUndeclaredWrite() {
        var go1 = Place.of("GO1", String.class);
        var go2 = Place.of("GO2", String.class);
        var go3 = Place.of("GO3", String.class);
        var p = Place.of("P", String.class);
        var a = Place.of("A", String.class);
        var b = Place.of("B", String.class);
        var stray = Place.of("STRAY", String.class);
        var go4 = Place.of("GO4", String.class);
        var many = Place.of("MANY", String.class);
        var silent = Transition.builder("silent").inputs(Arc.In.one(go1)).outputs(Arc.Out.place(p))
            .action(_ -> CompletableFuture.completedFuture(null)).build();
        var half = Transition.builder("half").inputs(Arc.In.one(go2)).outputs(Arc.Out.and(a, b))
            .action(ctx -> { ctx.output(a, "a"); return CompletableFuture.completedFuture(null); }).build();
        var undeclared = Transition.builder("undeclared").inputs(Arc.In.one(go3)).outputs(Arc.Out.place(p))
            .action(ctx -> { ctx.output(stray, "x"); return CompletableFuture.completedFuture(null); }).build();
        var twice = Transition.builder("twice").inputs(Arc.In.one(go4)).outputs(Arc.Out.place(many))
            .action(ctx -> {
                ctx.output(many, "m1");
                ctx.output(many, "m2");
                return CompletableFuture.completedFuture(null);
            }).build();
        var net = PetriNet.builder("skip").transitions(silent, half, undeclared, twice).place(stray).build();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            go1, List.of(Token.of("1")), go2, List.of(Token.of("2")), go3, List.of(Token.of("3")),
            go4, List.of(Token.of("4")));
        var store = EventStore.inMemory();
        try (var executor = PrecompiledNetExecutor.builder(net, initial)
                .eventStore(store).skipOutputValidation(true).build()) {
            var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();
            assertEquals(0, result.tokenCount(p), "the leaf is not checked: nothing written, nothing deposited");
            assertEquals(1, result.tokenCount(a), "a partial And write is deposited");
            assertEquals(0, result.tokenCount(b));
            var failed = store.events().stream()
                .filter(e -> e instanceof NetEvent.TransitionFailed)
                .map(e -> ((NetEvent.TransitionFailed) e).transitionName())
                .toList();
            assertEquals(List.of("undeclared"), failed, "only the undeclared write fails (CORE-063)");
            assertEquals(2, result.tokenCount(many), "both tokens into the one claimed place land");
            var warnings = store.events().stream()
                .filter(e -> e instanceof NetEvent.LogMessage lm && lm.message().contains("(IO-016)"))
                .toList();
            assertTrue(warnings.isEmpty(), "no IO-016 warning under the skip: " + warnings);
        }
        // AC6: building an IO-012-ambiguous spec fails before any executor exists.
        assertThrows(IllegalArgumentException.class, () -> Transition.builder("t")
            .inputs(Arc.In.one(go1)).outputs(Arc.Out.xor(p, p)).build());
    }

}
