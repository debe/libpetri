package org.libpetri.smt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import org.libpetri.analysis.InFlight;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.TimePetriNetAnalyzer;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;
import org.libpetri.runtime.BitmapNetExecutor;
import org.libpetri.runtime.Marking;
import org.libpetri.runtime.PrecompiledNetExecutor;
import org.libpetri.smt.opennet.OpenNetContract;
import org.libpetri.smt.opennet.OpenNetOptions;
import org.libpetri.smt.opennet.OpenNetVerifier;

import java.time.Duration;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * In-flight actions and the atomic-firing premise of verification ([VER-004], [EXEC-001],
 * [EXEC-003]).
 *
 * <p>The executor consumes a firing's inputs when the action starts and deposits its outputs when
 * the action completes, and other transitions fire in between. For monotone arcs that
 * interleaving is one of the atomic model's own runs. It is not when another transition tests one
 * of the in-flight transition's places with an inhibitor, reset, {@code all} or {@code atLeast}
 * arc. Mirrors {@code rust/libpetri/tests/inflight_atomicity.rs}.
 */
class InFlightTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<Integer> P = Place.of("p", Integer.class);
    private static final Place<Integer> Q = Place.of("q", Integer.class);
    private static final Place<Integer> R = Place.of("r", Integer.class);
    private static final Place<Integer> GO = Place.of("go", Integer.class);
    private static final Place<Integer> REQ = Place.of("req", Integer.class);
    private static final Place<Integer> BUSY = Place.of("busy", Integer.class);

    /** Forwards a token into {@code into} after 50 ms. */
    private static TransitionAction slow(Place<Integer> into) {
        return ctx -> CompletableFuture.runAsync(
            () -> ctx.output(into, 1), CompletableFuture.delayedExecutor(50, TimeUnit.MILLISECONDS));
    }

    /** Forwards a token into {@code into} inline. */
    private static TransitionAction quick(Place<Integer> into) {
        return ctx -> {
            ctx.output(into, 1);
            return CompletableFuture.completedFuture(null);
        };
    }

    /** {@code t: p + go → p}, priority 1, so it starts before {@code u}; {@code u: q + <test of p> → r}. */
    private static PetriNet net(String name, TransitionAction action, Function<Transition.Builder, Transition.Builder> test) {
        var t = Transition.builder("t").priority(1).inputs(In.one(P), In.one(GO)).outputs(Out.place(P)).action(action).build();
        var u = test.apply(Transition.builder("u")).outputs(Out.place(R)).action(quick(R)).build();
        return PetriNet.builder(name).transitions(t, u).build();
    }

    private record Case(String name, Function<TransitionAction, PetriNet> build, int p, SmtProperty property) {}

    private static List<Case> cases() {
        return List.of(
            new Case("inhibitor", a -> net("inflight-inhibitor", a, b -> b.inputs(In.one(Q)).inhibitors(P)), 1,
                new SmtProperty.Unreachable(Set.of(R))),
            new Case("reset", a -> net("inflight-reset", a, b -> b.inputs(In.one(Q)).resets(P)), 1,
                new SmtProperty.MutualExclusion(P, R)),
            new Case("all", a -> net("inflight-all", a, b -> b.inputs(In.all(P), In.one(Q))), 2,
                new SmtProperty.MutualExclusion(P, R)),
            new Case("atLeast", a -> net("inflight-at-least", a, b -> b.inputs(In.atLeast(2, P), In.one(Q))), 3,
                new SmtProperty.MutualExclusion(P, R)));
    }

    /** {@code start: req + inhibitor(busy) → busy}, the usual one-at-a-time guard. */
    private static PetriNet guardNet(TransitionAction action) {
        return PetriNet.builder("inflight-guard").transitions(
            Transition.builder("start").inputs(In.one(REQ)).inhibitors(BUSY).outputs(Out.place(BUSY)).action(action).build()
        ).build();
    }

    private static Map<Place<?>, List<Token<?>>> tokens(Map<Place<Integer>, Integer> counts) {
        var out = new HashMap<Place<?>, List<Token<?>>>();
        counts.forEach((place, n) -> {
            var list = new ArrayList<Token<?>>();
            for (int i = 0; i < n; i++) {
                list.add(Token.of(1));
            }
            out.put(place, list);
        });
        return out;
    }

    private static Marking run(boolean precompiled, PetriNet net, Map<Place<?>, List<Token<?>>> initial) {
        if (precompiled) {
            try (var ex = PrecompiledNetExecutor.create(net, initial)) {
                return ex.run(Duration.ofSeconds(5)).toCompletableFuture().join();
            }
        }
        try (var ex = BitmapNetExecutor.create(net, initial)) {
            return ex.run(Duration.ofSeconds(5)).toCompletableFuture().join();
        }
    }

    private static int count(Marking m, Place<Integer> place) {
        return m.peekTokens(place).size();
    }

    @ParameterizedTest
    @ValueSource(booleans = {false, true})
    void anAsyncActionLetsANonMonotoneTestSeeItsInputEmpty(boolean precompiled) {
        for (var c : cases()) {
            var m = run(precompiled, c.build().apply(slow(P)), tokens(Map.of(P, c.p(), Q, 1, GO, 1)));
            assertEquals(1, count(m, R), c.name() + ": u fired while t was in flight");
            assertEquals(1, count(m, P), c.name() + ": t deposited after u");
        }
    }

    /**
     * Java invokes an action inline and deposits a completed future's outputs inside the firing
     * pass, but a drain later in the same pass does not see the deposit ([EXEC-003] AC5): reset,
     * {@code all} and {@code atLeast} reach {@code {p, r}} without any asynchronous action. The
     * inhibitor does not, since {@code u} was not ready when the pass began.
     */
    @ParameterizedTest
    @ValueSource(booleans = {false, true})
    void aSyncActionInterleavesWithADrainInTheSamePass(boolean precompiled) {
        for (var c : cases()) {
            var m = run(precompiled, c.build().apply(quick(P)), tokens(Map.of(P, c.p(), Q, 1, GO, 1)));
            boolean atomic = !(count(m, R) > 0 && count(m, P) > 0);
            assertEquals(c.name().equals("inhibitor"), atomic, c.name() + ": p=" + count(m, P) + " r=" + count(m, R));
        }
    }

    /**
     * Java does not start a transition again while it is in flight (TypeScript neither; Rust
     * does), so the one-transition guard holds here. Two guarded transitions still both start.
     * Which of the two an executor does is not specified; the split covers both.
     */
    @ParameterizedTest
    @ValueSource(booleans = {false, true})
    void theGuardHoldsForOneTransitionNotForTwo(boolean precompiled) {
        var one = run(precompiled, guardNet(slow(BUSY)), tokens(Map.of(REQ, 2)));
        assertEquals(1, count(one, BUSY));
        var req2 = Place.of("req2", Integer.class);
        var two = PetriNet.builder("inflight-two-guards").transitions(
            Transition.builder("start").inputs(In.one(REQ)).inhibitors(BUSY).outputs(Out.place(BUSY)).action(slow(BUSY)).build(),
            Transition.builder("start2").inputs(In.one(req2)).inhibitors(BUSY).outputs(Out.place(BUSY)).action(slow(BUSY)).build()
        ).build();
        var both = run(precompiled, two, tokens(Map.of(REQ, 1, req2, 1)));
        assertEquals(2, count(both, BUSY));
    }

    @Test
    void theSplitAppliesToTransitionsWhoseOutputIsTestedNonMonotonically() {
        var n = cases().getFirst().build().apply(slow(P));
        assertEquals(List.of("t"), InFlight.transitions(n, Set.of()));
        var split = assertInstanceOf(InFlight.Outcome.Split.class, InFlight.split(n, Set.of(), Set.of()));
        assertEquals(List.of("t", "complete:t", "u"), split.net().transitions().stream().map(Transition::name).toList());
        assertEquals(List.of("p", "go", "q", "r", "inflight:t"), split.net().places().stream().map(Place::name).toList());
        assertInstanceOf(InFlight.Outcome.Atomic.class, InFlight.split(split.net(), Set.of(), Set.of()));
        assertEquals(List.of(), InFlight.transitions(n, Set.of("t")));
    }

    @Test
    void theAnalyzerFiresTheSplitTransitionInTwoSteps() {
        var result = TimePetriNetAnalyzer.forNet(guardNet(slow(BUSY)))
            .initialMarking(MarkingState.builder().tokens(REQ, 2).build())
            .goalPlaces(BUSY)
            .build()
            .analyze();
        assertTrue(result.report().contains("In-flight actions (VER-004): start is verified in two steps"), result.report());
    }

    private static SmtVerificationResult verify(PetriNet net, MarkingState m0, SmtProperty property, int classes, boolean atomic) {
        return SmtVerifier.forNet(net)
            .initialMarking(m0)
            .property(property)
            .enumerationMaxClasses(classes)
            .assumeAtomicFiring(atomic)
            .timeout(Duration.ofSeconds(30))
            .verify();
    }

    @ParameterizedTest
    @ValueSource(ints = {50_000, 0})
    @EnabledIf("z3Available")
    void whatTheExecutorReachesIsNotProvenAway(int classes) {
        for (var c : cases()) {
            var m0 = MarkingState.builder().tokens(P, c.p()).tokens(Q, 1).tokens(GO, 1).build();
            var result = verify(c.build().apply(slow(P)), m0, c.property(), classes, false);
            assertTrue(result.isViolated(), c.name() + ": " + result.verdict() + "\n" + result.report());
        }
    }

    @Test
    @EnabledIf("z3Available")
    void theGuardIsTwoStartsThenTwoCompletions() {
        var result = verify(guardNet(slow(BUSY)), MarkingState.builder().tokens(REQ, 2).build(),
            new SmtProperty.PlaceBound(BUSY, 1), 50_000, false);
        assertTrue(result.isViolated(), result.report());
        assertEquals(List.of("start", "start", "complete:start", "complete:start"), result.counterexampleTransitions());
        assertTrue(result.report().contains("In-flight actions (VER-004): start is verified in two steps"), result.report());
    }

    @ParameterizedTest
    @ValueSource(ints = {50_000, 0})
    @EnabledIf("z3Available")
    void assumeAtomicFiringRestoresTheAtomicVerdict(int classes) {
        var result = verify(guardNet(slow(BUSY)), MarkingState.builder().tokens(REQ, 2).build(),
            new SmtProperty.PlaceBound(BUSY, 1), classes, true);
        assertTrue(result.isProven(), result.report());
        assertTrue(result.report().contains("ASSUMPTION: every firing is atomic (the assume-atomic-firing option)"),
            result.report());
    }

    @Test
    void aNetWithoutNonMonotoneTestsOfOutputsScriptsTheSameEitherWay() {
        var a = Place.of("a", Integer.class);
        var b = Place.of("b", Integer.class);
        var n = PetriNet.builder("plain")
            .transitions(Transition.builder("t").inputs(In.one(a)).outputs(Out.place(b)).action(quick(b)).build())
            .build();
        Function<Boolean, String> scripts = atomic -> SmtVerifier.forNet(n)
            .initialMarking(MarkingState.builder().tokens(a, 1).build())
            .property(new SmtProperty.PlaceBound(b, 1))
            .assumeAtomicFiring(atomic)
            .encodeScripts().horn();
        assertEquals(scripts.apply(false), scripts.apply(true));
    }

    @Test
    @EnabledIf("z3Available")
    void aNuJoinTheSplitWouldCutInTwoIsRefused() {
        var a = Place.of("a", String.class);
        var b = Place.of("b", String.class);
        var joined = Place.of("joined", String.class);
        var late = Place.of("late", Integer.class);
        var join = Transition.builder("join")
            .inputs(In.one(a), In.one(b))
            .match(MatchSpec.builder().key(a, NameId::of).key(b, NameId::of).build())
            .outputs(Out.place(joined))
            .action(ctx -> {
                ctx.output(joined, "");
                return CompletableFuture.completedFuture(null);
            })
            .build();
        var watch = Transition.builder("watch").inputs(In.one(late)).inhibitors(joined)
            .action(ctx -> CompletableFuture.completedFuture(null)).build();
        var n = PetriNet.builder("nu-in-flight").transitions(join, watch).build();
        var result = verify(n, MarkingState.builder().tokens(late, 1).build(), new SmtProperty.PlaceBound(joined, 1), 50_000, false);
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(), result.report());
        assertTrue(unknown.reason().contains("transition 'join'") && unknown.reason().contains("ν-join"), unknown.reason());
    }

    /**
     * The split is redone when an input of it changes on a verifier already used: the verifier
     * once kept the first call's split (or its absence) and ignored a later
     * {@code assumeAtomicFiring}.
     */
    @ParameterizedTest
    @ValueSource(ints = {50_000, 0})
    @EnabledIf("z3Available")
    void aReusedVerifierFollowsAssumeAtomicFiring(int classes) {
        var verifier = SmtVerifier.forNet(guardNet(slow(BUSY)))
            .initialMarking(MarkingState.builder().tokens(REQ, 2).build())
            .property(new SmtProperty.PlaceBound(BUSY, 1))
            .enumerationMaxClasses(classes)
            .timeout(Duration.ofSeconds(30));
        var atomic = verifier.assumeAtomicFiring(true).verify();
        assertTrue(atomic.isProven(), atomic.report());
        var split = verifier.assumeAtomicFiring(false).verify();
        assertTrue(split.isViolated(), split.report());
        assertTrue(split.report().contains("In-flight actions (VER-004): start is verified in two steps"), split.report());
        assertFalse(split.report().contains("ASSUMPTION: every firing is atomic"), split.report());
        var again = verifier.assumeAtomicFiring(true).verify();
        assertTrue(again.isProven(), again.report());
        assertTrue(again.report().contains("ASSUMPTION: every firing is atomic"), again.report());
    }

    /**
     * A verifier reused across a change of {@code assumeAtomicFiring} or {@code carrierPlaces}
     * scripts what a fresh verifier with the same settings scripts, terminal places included:
     * the terminal rewrite is redone on the new split and excuses exactly the new net's places.
     */
    @Test
    void aReusedVerifierScriptsAsAFreshOne() {
        var n = terminalGuardNet();
        Function<SmtVerifier, SmtVerifier> base = v -> v
            .initialMarking(MarkingState.builder().tokens(REQ, 2).build())
            .property(SmtProperty.deadlockFree());
        var fresh = Map.of(
            true, base.apply(SmtVerifier.forNet(n)).assumeAtomicFiring(true).encodeScripts(),
            false, base.apply(SmtVerifier.forNet(n)).assumeAtomicFiring(false).encodeScripts());
        var reused = base.apply(SmtVerifier.forNet(n));
        for (boolean atomic : new boolean[] {true, false, true, false}) {
            assertEquals(fresh.get(atomic), reused.assumeAtomicFiring(atomic).encodeScripts(), "atomic=" + atomic);
        }
        var carriers = base.apply(SmtVerifier.forNet(n)).carrierPlaces(REQ).encodeScripts();
        assertEquals(carriers, reused.carrierPlaces(REQ).encodeScripts());
    }

    /**
     * The guard net with a {@code stop} into a terminal place, so the terminal rewrite runs after
     * the split and excuses every place of the split net.
     */
    private static PetriNet terminalGuardNet() {
        var done = Place.of("done", Integer.class);
        return PetriNet.builder("inflight-reuse")
            .transitions(
                Transition.builder("start").inputs(In.one(REQ)).inhibitors(BUSY).outputs(Out.place(BUSY)).action(slow(BUSY)).build(),
                Transition.builder("stop").inputs(In.one(BUSY)).outputs(Out.place(done)).action(quick(done)).build())
            .terminal(done)
            .build();
    }

    /**
     * Back to atomic firings after a split, a reused verifier's terminal excuses only the places
     * of the net it now verifies: the split's {@code inflight:start} is gone from the property.
     */
    @Test
    @EnabledIf("z3Available")
    void aReusedVerifierExcusesOnlyTheNewNetsPlaces() {
        var n = terminalGuardNet();
        Function<SmtVerifier, SmtVerifier> base = v -> v
            .initialMarking(MarkingState.builder().tokens(REQ, 2).build())
            .property(SmtProperty.deadlockFree())
            .timeout(Duration.ofSeconds(30));
        var reused = base.apply(SmtVerifier.forNet(n));
        var split = reused.assumeAtomicFiring(false).verify();
        assertTrue(propertyLine(split).contains("inflight:start"), split.report());
        var atomic = reused.assumeAtomicFiring(true).verify();
        var fresh = base.apply(SmtVerifier.forNet(n)).assumeAtomicFiring(true).verify();
        assertEquals(propertyLine(fresh), propertyLine(atomic));
        assertFalse(propertyLine(atomic).contains("inflight:"), atomic.report());
    }

    private static String propertyLine(SmtVerificationResult result) {
        return result.report().lines().filter(l -> l.startsWith("Property: ")).findFirst().orElseThrow();
    }

    @ParameterizedTest
    @ValueSource(ints = {50_000, 0})
    @EnabledIf("z3Available")
    void theOpenNetVerifierSplitsToo(int maxClasses) {
        var contract = OpenNetContract.builder()
            .initialMarking(m -> m.tokens(REQ, 2))
            .expect("busy", 1, BUSY)
            .rest(REQ)
            .build();
        var split = OpenNetVerifier.verifyOpenNet(guardNet(slow(BUSY)), contract, OpenNetOptions.DEFAULT.withMaxClasses(maxClasses));
        assertTrue(split.isViolated(), split.report());
        assertTrue(split.report().contains("In-flight actions (VER-004): start is verified in two steps"), split.report());
        var atomic = OpenNetVerifier.verifyOpenNet(guardNet(slow(BUSY)), contract,
            OpenNetOptions.DEFAULT.withMaxClasses(maxClasses).withAssumeAtomicFiring(true));
        assertTrue(atomic.isProven(), atomic.report());
        assertTrue(atomic.report().contains("ASSUMPTION: every firing is atomic"), atomic.report());
    }
}
