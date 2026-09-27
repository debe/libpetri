package org.libpetri.runtime;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletableFuture;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.SmtVerifier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [CORE-037] dead-arc warning: a read, inhibitor or reset arc on a place nothing can mark is
 * reported once per arc — by both executors at construction, through the [CORE-072] AC4
 * log-message channel, and by the verifier as a {@code WARNING:} report line. Never an error.
 */
class DeadArcWarningTest {

    private static final Place<String> A = Place.of("a", String.class);
    private static final Place<String> B = Place.of("b", String.class);
    private static final Place<String> X = Place.of("x", String.class);

    private static final String TAIL =
        ": no transition produces into or consumes from it and it starts empty; ";

    enum Backend {
        BITMAP {
            @Override
            PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial,
                                    Set<EnvironmentPlace<?>> env, EventStore store) {
                return BitmapNetExecutor.builder(net, initial).environmentPlaces(env).eventStore(store).build();
            }
        },
        PRECOMPILED {
            @Override
            PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial,
                                    Set<EnvironmentPlace<?>> env, EventStore store) {
                return PrecompiledNetExecutor.builder(net, initial).environmentPlaces(env).eventStore(store).build();
            }
        };

        abstract PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial,
                                         Set<EnvironmentPlace<?>> env, EventStore store);
    }

    private static Transition.Builder kill() {
        return Transition.builder("kill").inputs(In.one(A)).outputs(Out.place(B))
            .action(ctx -> CompletableFuture.completedFuture(null));
    }

    private static PetriNet net(Transition... ts) {
        return PetriNet.builder("dead-arcs").transitions(ts).build();
    }

    private static List<NetEvent.LogMessage> warnings(Backend backend, PetriNet net,
                                                      Map<Place<?>, List<Token<?>>> initial,
                                                      Set<EnvironmentPlace<?>> env) throws Exception {
        var store = EventStore.inMemory();
        try (var executor = backend.create(net, initial, env, store)) {
            return store.eventsOfType(NetEvent.LogMessage.class).stream()
                .filter(e -> "libpetri.runtime".equals(e.loggerName()))
                .toList();
        }
    }

    private static Map<Place<?>, List<Token<?>>> seedA() {
        return Map.of(A, List.of(Token.of("go")));
    }

    @ParameterizedTest
    @EnumSource(Backend.class)
    void deadResetArc_warnsOnceAtConstruction(Backend backend) throws Exception {
        var w = warnings(backend, net(kill().reset(X).build()), seedA(), Set.of());

        assertEquals(1, w.size(), w.toString());
        assertEquals("WARN", w.get(0).level());
        assertEquals("kill", w.get(0).transitionName());
        assertEquals("reset arc of 'kill' on 'x'" + TAIL + "the arc has no effect.", w.get(0).message());
    }

    @ParameterizedTest
    @EnumSource(Backend.class)
    void deadReadAndInhibitorArcs_nameTheirEffect(Backend backend) throws Exception {
        var read = warnings(backend, net(kill().read(X).build()), seedA(), Set.of());
        assertEquals(List.of("read arc of 'kill' on 'x'" + TAIL + "the transition can never be enabled."),
            read.stream().map(NetEvent.LogMessage::message).toList());

        var inhibitor = warnings(backend, net(kill().inhibitor(X).build()), seedA(), Set.of());
        assertEquals(List.of("inhibitor arc of 'kill' on 'x'" + TAIL + "the arc never blocks."),
            inhibitor.stream().map(NetEvent.LogMessage::message).toList());
    }

    @ParameterizedTest
    @EnumSource(Backend.class)
    void oneMessagePerArc_inTransitionThenKindOrder(Backend backend) throws Exception {
        var first = Transition.builder("first").inputs(In.one(B)).reset(X).inhibitor(X)
            .action(ctx -> CompletableFuture.completedFuture(null)).build();
        var w = warnings(backend, net(kill().read(X).build(), first), seedA(), Set.of());

        assertEquals(List.of(
                "read arc of 'kill' on 'x'" + TAIL + "the transition can never be enabled.",
                "inhibitor arc of 'first' on 'x'" + TAIL + "the arc never blocks.",
                "reset arc of 'first' on 'x'" + TAIL + "the arc has no effect."),
            w.stream().map(NetEvent.LogMessage::message).toList());
    }

    @ParameterizedTest
    @EnumSource(Backend.class)
    void noWarning_whenSeededInjectedConsumedOrProduced(Backend backend) throws Exception {
        var net = net(kill().reset(X).build());
        var seeded = Map.<Place<?>, List<Token<?>>>of(A, List.of(Token.of("go")), X, List.of(Token.of("s")));
        assertTrue(warnings(backend, net, seeded, Set.of()).isEmpty(), "seeded by the initial marking");
        assertTrue(warnings(backend, net, seedA(), Set.of(EnvironmentPlace.of(X))).isEmpty(),
            "an environment place");

        var consumer = Transition.builder("drain").inputs(In.one(X))
            .action(ctx -> CompletableFuture.completedFuture(null)).build();
        assertTrue(warnings(backend, net(kill().reset(X).build(), consumer), seedA(), Set.of()).isEmpty(),
            "consumed by another transition");

        var producer = Transition.builder("fill").inputs(In.one(B)).outputs(Out.xor(A, X))
            .action(ctx -> CompletableFuture.completedFuture(null)).build();
        assertTrue(warnings(backend, net(kill().reset(X).build(), producer), seedA(), Set.of()).isEmpty(),
            "produced on one XOR branch");
    }

    @Test
    void verifierReport_carriesOneWarningLinePerDeadArc() {
        var net = StructureOnly.bind(net(kill().reset(X).build()));
        var result = SmtVerifier.forNet(net)
            .initialMarking(MarkingState.builder().tokens(A, 1).build())
            .property(SmtProperty.placeBound(B, 1))
            .verify();

        assertTrue(result.report().contains(
                "WARNING: reset arc of 'kill' on 'x'" + TAIL + "the arc has no effect.\n"),
            result.report());
        assertTrue(result.isProven(), "a warning never changes the verdict:\n" + result.report());

        var seeded = SmtVerifier.forNet(net)
            .initialMarking(MarkingState.builder().tokens(A, 1).tokens(X, 1).build())
            .property(SmtProperty.placeBound(B, 1))
            .verify();
        assertFalse(seeded.report().contains("WARNING: reset arc"), seeded.report());
    }
}
