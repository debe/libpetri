package org.libpetri.smt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.PrioritySemantics;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
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
import java.util.OptionalInt;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a verification tests beyond the arcs of its net ([VER-004]): a terminal stop that abandons
 * an action in flight under a {@code QuiescentCount} lower bound (F1), conflict priority reading
 * whether a pruner is enabled (F2), Route B's instant actions under {@code assumeNoReaping} (F3)
 * and a counterexample that restarts a transition in flight ([CONC-002], F7). Each witness first
 * runs on both executors, so the verdict is held against what the executor does. Mirrors the
 * fix-round witnesses of {@code rust/libpetri/tests/inflight_atomicity.rs}.
 */
class SplitDemandTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static Place<Integer> unit(String name) {
        return Place.of(name, Integer.class);
    }

    private static final Place<String> X = Place.of("X", String.class);
    private static final Place<String> Y = Place.of("Y", String.class);
    private static final Place<String> J = Place.of("J", String.class);
    private static final Place<Integer> SEED = unit("SEED");

    /** Writes a token into {@code into} after {@code ms}. */
    private static TransitionAction slow(Place<Integer> into, long ms) {
        return ctx -> CompletableFuture.runAsync(
            () -> ctx.output(into, 1), CompletableFuture.delayedExecutor(ms, TimeUnit.MILLISECONDS));
    }

    /** Writes a token into {@code into} inline. */
    private static TransitionAction inline(Place<Integer> into) {
        return ctx -> {
            ctx.output(into, 1);
            return CompletableFuture.completedFuture(null);
        };
    }

    /**
     * The ν pair every conflict witness carries, so Route B decides it: {@code MINT: SEED -> X, Y}
     * writes one fresh name into both, and {@code JOIN} joins them by name into {@code J}.
     */
    private static List<Transition> nuPair(int joinPriority) {
        var mint = Transition.builder("MINT").inputs(In.one(SEED)).outputs(Out.and(Out.place(X), Out.place(Y)))
            .action(ctx -> {
                var n = ctx.freshName().value();
                ctx.output(X, n);
                ctx.output(Y, n);
                return CompletableFuture.completedFuture(null);
            })
            .build();
        var join = Transition.builder("JOIN").priority(joinPriority).inputs(In.one(X), In.one(Y))
            .match(MatchSpec.builder().key(X, NameId::of).key(Y, NameId::of).build())
            .outputs(Out.place(J))
            .action(ctx -> {
                ctx.output(J, ctx.input(X));
                return CompletableFuture.completedFuture(null);
            })
            .build();
        return List.of(mint, join);
    }

    private static PetriNet net(String name, List<Transition> transitions) {
        return PetriNet.builder(name).transitions(transitions.toArray(new Transition[0])).build();
    }

    /** F1: {@code t: a -> ok} (100 ms), {@code f: s -> done} (10 ms), {@code done} terminal. */
    private static PetriNet terminalAbandonNet() {
        return PetriNet.builder("terminal-abandon")
            .transitions(
                Transition.builder("t").inputs(In.one(unit("a"))).outputs(Out.place(unit("ok"))).action(slow(unit("ok"), 100)).build(),
                Transition.builder("f").inputs(In.one(unit("s"))).outputs(Out.place(unit("done"))).action(slow(unit("done"), 10)).build())
            .terminal(unit("done"))
            .build();
    }

    /**
     * F2 (a). {@code t: a -> p} (50 ms), {@code H: p + b -> ok} priority 10,
     * {@code L: b + inhibitor(a) -> bad} priority 0. While {@code t} is in flight {@code a} is empty
     * and {@code p} not yet marked, so {@code L} fires.
     */
    private static PetriNet conflictFeederNet() {
        var ts = new ArrayList<>(List.of(
            Transition.builder("t").inputs(In.one(unit("a"))).outputs(Out.place(unit("p"))).action(slow(unit("p"), 50)).build(),
            Transition.builder("H").priority(10).inputs(In.one(unit("p")), In.one(unit("b")))
                .outputs(Out.place(unit("ok"))).action(inline(unit("ok"))).build(),
            Transition.builder("L").inputs(In.one(unit("b"))).inhibitors(unit("a"))
                .outputs(Out.place(unit("bad"))).action(inline(unit("bad"))).build()));
        ts.addAll(nuPair(0));
        return net("conflict-feeder", ts);
    }

    /**
     * F2 (b). {@code H: c -> ok} priority 10 (100 ms), {@code L: c -> bad} priority 0,
     * {@code g: s + inhibitor(c) -> c}. {@code g} refills {@code c} while {@code H} is in flight;
     * the Java executors do not start {@code H} again then, so {@code L} takes the refill.
     */
    private static PetriNet conflictRestartNet() {
        var ts = new ArrayList<>(List.of(
            Transition.builder("H").priority(10).inputs(In.one(unit("c")))
                .outputs(Out.place(unit("ok"))).action(slow(unit("ok"), 100)).build(),
            Transition.builder("L").inputs(In.one(unit("c"))).outputs(Out.place(unit("bad"))).action(inline(unit("bad"))).build(),
            Transition.builder("g").inputs(In.one(unit("s"))).inhibitors(unit("c"))
                .outputs(Out.place(unit("c"))).action(inline(unit("c"))).build()));
        ts.addAll(nuPair(0));
        return net("conflict-restart", ts);
    }

    /**
     * F3. {@code t: a -> p} {@code deadline(20)} (150 ms), {@code h: p + b -> ok}
     * {@code deadline(20)}, {@code v: b -> bad} {@code delayed(60)}. {@code t} is still running at
     * 60 ms, so {@code v} takes {@code b}.
     */
    private static PetriNet longActionNet() {
        var ts = new ArrayList<>(List.of(
            Transition.builder("t").inputs(In.one(unit("a"))).outputs(Out.place(unit("p")))
                .timing(Timing.deadline(Duration.ofMillis(20))).action(slow(unit("p"), 150)).build(),
            Transition.builder("h").inputs(In.one(unit("p")), In.one(unit("b"))).outputs(Out.place(unit("ok")))
                .timing(Timing.deadline(Duration.ofMillis(20))).action(inline(unit("ok"))).build(),
            Transition.builder("v").inputs(In.one(unit("b"))).outputs(Out.place(unit("bad")))
                .timing(Timing.delayed(Duration.ofMillis(60))).action(inline(unit("bad"))).build()));
        ts.addAll(nuPair(0));
        return net("long-action", ts);
    }

    /** {@code start: req + inhibitor(busy) -> busy} (50 ms), the usual one-at-a-time guard. */
    private static PetriNet guardNet() {
        return PetriNet.builder("inflight-guard").transitions(
            Transition.builder("start").inputs(In.one(unit("req"))).inhibitors(unit("busy"))
                .outputs(Out.place(unit("busy"))).action(slow(unit("busy"), 50)).build()).build();
    }

    // ==================== what the executors do ====================

    private static Map<Place<?>, List<Token<?>>> tokens(String... names) {
        var out = new HashMap<Place<?>, List<Token<?>>>();
        for (var n : names) {
            out.computeIfAbsent(unit(n), _ -> new ArrayList<>()).add(Token.of(1));
        }
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

    private static int count(Marking m, String place) {
        return m.peekTokens(unit(place)).size();
    }

    @ParameterizedTest
    @ValueSource(booleans = {false, true})
    void aTerminalStopAbandonsAnActionInFlight(boolean precompiled) {
        var m = run(precompiled, terminalAbandonNet(), tokens("a", "s"));
        assertEquals(List.of(0, 0, 1), List.of(count(m, "a"), count(m, "ok"), count(m, "done")));
    }

    @ParameterizedTest
    @ValueSource(booleans = {false, true})
    void aConflictPrunerFedByAnActionInFlightDoesNotPreEmpt(boolean precompiled) {
        var m = run(precompiled, conflictFeederNet(), tokens("a", "b", "SEED"));
        assertEquals(1, count(m, "bad"), "L fired while t was in flight");
    }

    @ParameterizedTest
    @ValueSource(booleans = {false, true})
    void javaDoesNotRestartAPrunerInFlight(boolean precompiled) {
        var m = run(precompiled, conflictRestartNet(), tokens("c", "s", "SEED"));
        assertEquals(List.of(1, 1), List.of(count(m, "ok"), count(m, "bad")), "L took the refill");
    }

    @ParameterizedTest
    @ValueSource(booleans = {false, true})
    void aLongActionLetsADelayedTransitionWin(boolean precompiled) {
        var m = run(precompiled, longActionNet(), tokens("a", "b", "SEED"));
        assertEquals(1, count(m, "bad"));
    }

    // ==================== what the verifier says ====================

    private static MarkingState state(String... names) {
        var b = MarkingState.builder();
        var counts = new HashMap<String, Integer>();
        for (var n : names) {
            counts.merge(n, 1, Integer::sum);
        }
        counts.forEach((n, c) -> b.tokens(unit(n), c));
        return b.build();
    }

    /**
     * F1: the terminal stop abandons {@code t}, so {@code QuiescentCount([a, ok], 1, 1)} is
     * violated, on the enumeration route and on the SMT pipeline alone. A lower bound the terminal
     * waives needs no split.
     */
    @Test
    @EnabledIf("z3Available")
    void aQuiescentCountSeesTheActionATerminalStopAbandons() {
        var property = SmtProperty.quiescentCount(List.of(unit("a"), unit("ok")), 1, OptionalInt.of(1));
        for (int classes : new int[] {50_000, 0}) {
            var result = SmtVerifier.forNet(terminalAbandonNet()).initialMarking(state("a", "s"))
                .property(property).enumerationMaxClasses(classes).timeout(Duration.ofSeconds(30)).verify();
            assertTrue(result.isViolated(), result.verdict() + " via " + result.route() + "\n" + result.report());
            assertTrue(result.report().contains(
                "a terminal place stops the net without waiting for an action in flight (EXEC-042) and the "
                    + "property's lower bound counts a place one of them deposits into"), result.report());
        }
        var waived = SmtProperty.quiescentCount(List.of(unit("a"), unit("ok")), 1, OptionalInt.of(1), List.of(unit("done")));
        var result = SmtVerifier.forNet(terminalAbandonNet()).initialMarking(state("a", "s"))
            .property(waived).timeout(Duration.ofSeconds(30)).verify();
        assertTrue(result.isProven(), result.report());
    }

    private static SmtVerificationResult verifyConflict(PetriNet net, MarkingState m0, boolean atomic) {
        return SmtVerifier.forNet(net)
            .initialMarking(m0)
            .property(SmtProperty.unreachable(Set.of(unit("bad"))))
            .mintTransitions("MINT")
            .prioritySemantics(PrioritySemantics.CONFLICT)
            .assumeAtomicFiring(atomic)
            .timeout(Duration.ofSeconds(30))
            .verify();
    }

    /** F2 (a): {@code t} feeds the pruner {@code H}, so {@code t} is split, and {@code L} fires while it is in flight. */
    @Test
    void conflictPrioritySplitsTheFeederOfAPruner() {
        var result = verifyConflict(conflictFeederNet(), state("a", "b", "SEED"), false);
        assertTrue(result.isViolated(), result.verdict() + "\n" + result.report());
        assertTrue(result.report().contains("In-flight actions (VER-004): t, H are verified in two steps"), result.report());
        assertTrue(result.report().contains(
            "conflict priority (NU-052) reads whether a pruning transition is enabled"), result.report());
        var atomic = verifyConflict(conflictFeederNet(), state("a", "b", "SEED"), true);
        assertTrue(atomic.isProven(), atomic.report());
        assertTrue(atomic.report().contains("ASSUMPTION: every firing is atomic"), atomic.report());
    }

    /** F2 (b): {@code H} in flight pre-empts nothing, so {@code L} takes the refill. */
    @Test
    void aPrunerInFlightPreEmptsNothing() {
        var result = verifyConflict(conflictRestartNet(), state("c", "s", "SEED"), false);
        assertTrue(result.isViolated(), result.verdict() + "\n" + result.report());
        assertTrue(result.counterexampleTransitions().contains("L"), result.counterexampleTransitions().toString());
    }

    /** F2 fallback: a ν-join pruner cannot be split, so the pruning is off and the report says why. */
    @Test
    void conflictPriorityIsOffWhenAPrunerCannotBeSplit() {
        var ts = new ArrayList<>(nuPair(10));
        ts.add(Transition.builder("DRAIN").priority(-10).inputs(In.one(X))
            .outputs(Out.place(unit("DEAD"))).action(inline(unit("DEAD"))).build());
        var net = net("conflict-join", ts);
        java.util.function.Function<PrioritySemantics, SmtVerificationResult> run = semantics -> SmtVerifier.forNet(net)
            .initialMarking(state("SEED"))
            .property(SmtProperty.unreachable(Set.of(unit("DEAD"))))
            .mintTransitions("MINT")
            .fragmentMode(FragmentMode.EXTENDED)
            .prioritySemantics(semantics)
            .verify();
        var conflict = run.apply(PrioritySemantics.CONFLICT);
        var none = run.apply(PrioritySemantics.NONE);
        assertTrue(conflict.report().contains("Conflict priority (NU-052) is off:"), conflict.report());
        assertTrue(conflict.report().contains("cannot be split: it"), conflict.report());
        assertEquals(none.verdict().getClass(), conflict.verdict().getClass(), conflict.report() + "\n" + none.report());
    }

    /**
     * F3: under {@code assumeNoReaping} Route B keeps the latest bounds and gives an action no
     * duration, so it proves {@code bad} unreachable while the executor marks it. The verdict says
     * so. Read reap-aware, the default, it is violated.
     */
    @Test
    void routeBUnderAssumeNoReapingNamesItsInstantActions() {
        java.util.function.Function<Boolean, SmtVerificationResult> run = strict -> SmtVerifier.forNet(longActionNet())
            .initialMarking(state("a", "b", "SEED"))
            .property(SmtProperty.unreachable(Set.of(unit("bad"))))
            .mintTransitions("MINT")
            .assumeNoReaping(strict)
            .verify();
        var strict = run.apply(true);
        assertTrue(strict.isProven(), strict.report());
        assertTrue(strict.report().contains(
            "ASSUMPTION: no transition is reaped (the assume-no-reaping option), none fires after its latest "
                + "bound, and an action takes no time, i.e. an on-time executor with atomic firings."), strict.report());
        assertFalse(strict.report().contains("sound AND complete"), strict.report());
        assertTrue(strict.report().contains("exact only for an on-time executor whose actions take no time"),
            strict.report());
        var byDefault = run.apply(false);
        assertTrue(byDefault.isViolated(), byDefault.report());
    }

    /**
     * F7 on the guard net: a counterexample that starts {@code start} twice says that only the
     * Rust executor does that; one without a restart carries no such note.
     */
    @Test
    @EnabledIf("z3Available")
    void aSplitVerdictNamesARestart() {
        var result = SmtVerifier.forNet(guardNet()).initialMarking(state("req", "req"))
            .property(SmtProperty.placeBound(unit("busy"), 1)).timeout(Duration.ofSeconds(30)).verify();
        assertTrue(result.isViolated(), result.report());
        assertTrue(result.report().contains(
            "NOTE (CONC-002): the counterexample starts 'start' again while its earlier firing is still in "
                + "flight (inflight:start marked)."), result.report());
        assertFalse(result.report().contains("ctx.flush()"), result.report());
        // `t: p + go -> p` in flight lets `u` see `p` empty: violated, with no restart.
        var inhibitorNet = PetriNet.builder("inflight-inhibitor").transitions(
            Transition.builder("t").priority(1).inputs(In.one(unit("p")), In.one(unit("go")))
                .outputs(Out.place(unit("p"))).action(slow(unit("p"), 50)).build(),
            Transition.builder("u").inputs(In.one(unit("q"))).inhibitors(unit("p"))
                .outputs(Out.place(unit("r"))).action(inline(unit("r"))).build()).build();
        var plain = SmtVerifier.forNet(inhibitorNet).initialMarking(state("p", "q", "go"))
            .property(SmtProperty.unreachable(Set.of(unit("r")))).timeout(Duration.ofSeconds(30)).verify();
        assertTrue(plain.isViolated(), plain.report());
        assertFalse(plain.report().contains("NOTE (CONC-002)"), plain.report());
    }

    /** F7 on the open-net route: the graph's witness starts {@code start} twice. */
    @Test
    void anOpenNetWitnessNamesARestart() {
        var contract = OpenNetContract.builder()
            .initialMarking(m -> m.tokens(unit("req"), 2))
            .expect("busy", 1, unit("busy"))
            .rest(unit("req"))
            .build();
        var result = OpenNetVerifier.verifyOpenNet(guardNet(), contract, OpenNetOptions.DEFAULT);
        assertTrue(result.isViolated(), result.report());
        assertTrue(result.report().contains(
            "NOTE (CONC-002): the counterexample starts 'start' again while its earlier firing is still in "
                + "flight (inflight:start marked)."), result.report());
    }
}
