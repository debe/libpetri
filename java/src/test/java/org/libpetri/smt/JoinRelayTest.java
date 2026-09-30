package org.libpetri.smt;

import org.libpetri.analysis.AllMints;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.UnaryOperator;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.NameFragment;
import org.libpetri.core.Arc;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.SmtVerificationResult.Route;

/**
 * NU-054 join relay in the analysis: fragment rules (AC4), the join chain (AC3), BASE ignoring
 * the declaration (AC5), the PNID fixtures of the spec's test derivation (transcribed from
 * {@code research/net-metrics/validation/pnid/src/nets.ts}), a correlated self-loop, and Route A
 * against Route B on every fixture both decide (AC6). The cross-language script parity of the
 * relay fixtures ({@code spec/verification-fixtures/nu-relay-fixtures.json}, built through
 * {@link Net}) is diffed against the Rust goldens by
 * {@link SmtScriptParityTest#relayScriptParity()}.
 */
class JoinRelayTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    // ── net builder (the pnid NetBuilder, plus relay declarations) ─────────────────────────

    /** Structure-only net over String places whose token is its own name. */
    static final class Net {
        private final String name;
        private final Map<String, Place<String>> places = new LinkedHashMap<>();
        private final List<Transition> transitions = new ArrayList<>();

        Net(String name) {
            this.name = name;
        }

        Place<String> p(String n) {
            return places.computeIfAbsent(n, k -> Place.of(k, String.class));
        }

        /** Every input consumed once, every output produced once; match keys and relays by name. */
        Net t(String tName, List<String> ins, List<String> outs, List<String> match, List<String> relays) {
            var b = Transition.builder(tName);
            b.inputs(ins.stream().map(n -> (Arc.In) Arc.In.one(p(n))).toArray(Arc.In[]::new));
            if (!outs.isEmpty()) {
                b.outputs(outs.size() == 1 ? Arc.Out.place(p(outs.get(0)))
                    : Arc.Out.and(outs.stream().map(this::p).toArray(Place<?>[]::new)));
            }
            if (!match.isEmpty()) {
                var ms = MatchSpec.builder();
                for (var k : match) ms.key(p(k), (String v) -> NameId.of(v));
                for (var r : relays) ms.relayTo(p(r), (String v) -> NameId.of(v));
                b.match(ms.build());
            }
            transitions.add(b.build());
            return this;
        }

        Net t(String tName, List<String> ins, List<String> outs) {
            return t(tName, ins, outs, List.of(), List.of());
        }

        Net add(Transition t) {
            transitions.add(t);
            return this;
        }

        PetriNet build() {
            return StructureOnly.bind(PetriNet.builder(name).transitions(transitions.toArray(new Transition[0])).build());
        }
    }

    private static List<String> l(String... xs) {
        return List.of(xs);
    }

    // ── fixtures ──────────────────────────────────────────────────────────────────────────

    /** AC3 join chain: {@code fork: S -> A, B, D}; {@code j1: A, B -> C} relaying to C; {@code j2: C, D -> done}. */
    static Net chain(boolean relay) {
        return new Net("join-chain")
            .t("fork", l("S"), l("A", "B", "D"))
            .t("j1", l("A", "B"), l("C"), l("A", "B"), relay ? l("C") : l())
            .t("j2", l("C", "D"), l("done"), l("C", "D"), l());
    }

    /** AC3 variant: D is filled by a second, independent mint. */
    static Net chainIndependentD() {
        return new Net("join-chain-independent")
            .t("fork", l("S"), l("A", "B"))
            .t("fork2", l("S2"), l("D"))
            .t("j1", l("A", "B"), l("C"), l("A", "B"), l("C"))
            .t("j2", l("C", "D"), l("done"), l("C", "D"), l());
    }

    /** P Fig. 12(c), closure 2 ({@code closure2} in nets.ts); {@code e} relays to {@code P5}. */
    static Net fig12c(boolean relay) {
        return new Net("P-Fig12c-closure2")
            .t("a", l("R"), l("P1", "OR"))
            .t("b", l("P1"), l("B1", "B2"))
            .t("c", l("B1"), l("C1"))
            .t("d", l("B2"), l("D1"))
            .t("e", l("C1", "D1"), l("P5"), l("C1", "D1"), relay ? l("P5") : l())
            .t("f", l("P5", "OR"), l("R"), l("P5", "OR"), l())
            .t("g", l("P5", "OR"), l("R"), l("P5", "OR"), l());
    }

    static final List<String> FIG12C_CARRIERS = l("P1", "B1", "B2", "C1", "D1");

    /** P Fig. 6(a) N1, correlated ({@code n1Corr}); B relays to Y1, w, q and D to Y2, r. */
    static Net n1Corr(boolean relay) {
        return new Net("P-Fig6a-N1-corr")
            .t("A", l("SUPPLY"), l("Y1", "p"))
            .t("B", l("p", "Y1"), l("Y1", "w", "q"), l("p", "Y1"), relay ? l("Y1", "w", "q") : l())
            .t("C", l("Y1"), l("Y2"))
            .t("D", l("q", "w", "Y2"), l("Y2", "r"), l("q", "w", "Y2"), relay ? l("Y2", "r") : l())
            .t("E", l("Y2", "r"), l("E_done"), l("Y2", "r"), l());
    }

    /** S union N ⊕ M ({@code tjnUnion}); b relays to its carrier q. */
    static Net sUnion(boolean relay) {
        return new Net("S-union-NplusM")
            .t("a", l("SUPPLY"), l("p"))
            .t("b", l("p", "s"), l("q"), l("p", "s"), relay ? l("q") : l())
            .t("c", l("q"), l("s", "r"))
            .t("d", l("r"), l("d_done"));
    }

    /**
     * Correlated self-loop: {@code B} joins {@code p, Y} and writes the name back onto its own
     * key {@code Y} and onto {@code q}; {@code D} joins {@code q, Y}. With {@code independentQ}
     * the q token comes from a second mint instead, so D never finds one name on both.
     */
    static Net selfLoop(boolean independentQ) {
        var n = new Net(independentQ ? "self-loop-independent" : "self-loop")
            .t("A", l("S"), l("p", "Y"));
        if (independentQ) {
            n.t("A2", l("T"), l("q"))
             .t("B", l("p", "Y"), l("Y", "x"), l("p", "Y"), l("Y"));
        } else {
            n.t("B", l("p", "Y"), l("Y", "q"), l("p", "Y"), l("Y", "q"));
        }
        return n.t("D", l("q", "Y"), l("done"), l("q", "Y"), l());
    }

    // ── helpers ───────────────────────────────────────────────────────────────────────────

    private record Q(Net net, Map<String, Integer> m0, SmtProperty property, List<String> sinks,
                     List<String> budgets, List<String> carriers, FragmentMode mode) {}

    private static SmtVerificationResult verify(Q q, boolean withBudget, int nuMaxClasses) {
        return verify(q, withBudget, nuMaxClasses, Duration.ofSeconds(60));
    }

    private static SmtVerificationResult verify(Q q, boolean withBudget, int nuMaxClasses, Duration timeout) {
        return verify(q, withBudget, nuMaxClasses, timeout, true);
    }

    private static SmtVerificationResult verify(
            Q q, boolean withBudget, int nuMaxClasses, Duration timeout, boolean linearBound) {
        var net = q.net.build();
        var v = SmtVerifier.forNet(net).mintTransitions(AllMints.names(net))
            .linearBound(linearBound)
            .initialMarking(m -> q.m0.forEach((p, c) -> m.tokens(q.net.p(p), c)))
            .property(q.property)
            .fragmentMode(q.mode)
            .nuMaxClasses(nuMaxClasses)
            .timeout(timeout);
        if (!q.sinks.isEmpty()) v.sinkPlaces(q.sinks.stream().map(q.net::p).toArray(Place<?>[]::new));
        if (withBudget && !q.budgets.isEmpty()) v.budgetPlaces(q.budgets.stream().map(q.net::p).toArray(Place<?>[]::new));
        if (!q.carriers.isEmpty()) v.carrierPlaces(q.carriers.stream().map(q.net::p).toArray(Place<?>[]::new));
        return v.verify();
    }

    private static String verdict(SmtVerificationResult r) {
        return r.isProven() ? "proven" : r.isViolated() ? "violated" : "unknown";
    }

    private static boolean isQuiescence(SmtProperty p) {
        return p instanceof SmtProperty.DeadlockFree || p instanceof SmtProperty.JoinedOrDeadLettered;
    }

    /**
     * Route B and Route A on the same query. Quiescence: Route B by default, Route A by forcing
     * Route B to truncate (budget declared). Reachability-safety: Route A with the budget
     * declared, Route B without it.
     */
    private static void assertRoutesAgree(Q q, String expected) {
        assertRoutes(q, expected, false);
    }

    /** As {@link #assertRoutesAgree}, but Route A may answer unknown within a short timeout. */
    private static void assertRoutesAgreeOrUnknown(Q q, String expected) {
        assertRoutes(q, expected, true);
    }

    private static void assertRoutes(Q q, String expected, boolean routeAMayBeUnknown) {
        SmtVerificationResult routeB;
        SmtVerificationResult routeA;
        if (isQuiescence(q.property)) {
            routeB = verify(q, true, 100_000);
            routeA = verify(q, true, 1,
                Duration.ofSeconds(expected.equals("proven") || routeAMayBeUnknown ? 10 : 60));
            assertTrue(routeA.report().contains("Route A"), "Route A must decide:\n" + routeA.report());
        } else {
            routeB = verify(q, false, 100_000);
            // Without the linear bound, which now runs ahead of the coloured encoding ([VER-015])
            // and would prove fig12c's OR bound structurally before Route A is asked.
            routeA = verify(q, true, 100_000, Duration.ofSeconds(60), false);
            assertEquals(Route.SMT, routeA.route(), "Route A must decide:\n" + routeA.report());
        }
        assertEquals(Route.NU_SCG, routeB.route(), "Route B must decide:\n" + routeB.report());
        assertEquals(expected, verdict(routeB), q.net.name + " Route B:\n" + routeB.report());
        System.out.println("[NU-054 routes] " + q.net.name + " " + q.property + " m0=" + q.m0
            + ": Route B " + verdict(routeB) + ", Route A " + verdict(routeA));
        // Spacer does not converge on the proven quiescence queries within the timeout (it
        // returns unknown, as in TypeScript): a known solver limit, not a disagreement. Every
        // other case must match exactly, and Route A must never contradict Route B.
        if ((isQuiescence(q.property) && expected.equals("proven")) || routeAMayBeUnknown) {
            assertTrue(verdict(routeA).equals(expected) || verdict(routeA).equals("unknown"),
                q.net.name + " Route A contradicts Route B:\n" + routeA.report());
        } else {
            assertEquals(expected, verdict(routeA), q.net.name + " Route A:\n" + routeA.report());
        }
    }

    private static FragmentMode EXT = FragmentMode.EXTENDED;

    // ── AC4: fragment rules ───────────────────────────────────────────────────────────────

    @Test
    void extendedAcceptsTheChainOnlyWithTheRelayDeclared() {
        assertNotNull(NameFragment.classify(chain(true).build(), EXT, Set.of(), AllMints.of(chain(true).build())));
        assertNull(NameFragment.classify(chain(false).build(), EXT, Set.of(), AllMints.of(chain(false).build())),
            "a join writing an undeclared coloured place is a re-mint");
        assertNull(NameFragment.classify(chain(true).build(), FragmentMode.BASE, Set.of(), AllMints.of(chain(true).build())),
            "BASE ignores the relay declaration");
    }

    @Test
    void relayTargetConsumedOffKeyBySameJoin_isRejected() {
        // j1 also consumes its relay target C through a non-key input.
        var n = new Net("off-key-relay")
            .t("fork", l("S"), l("A", "B"))
            .t("j1", l("A", "B", "C"), l("C"), l("A", "B"), l("C"));
        assertNull(NameFragment.classify(n.build(), EXT, Set.of(), AllMints.of(n.build())));
    }

    @Test
    void relayTargetWithReadInhibitorOrReset_isRejected() {
        for (var arc : List.<UnaryOperator<Transition.Builder>>of(
                b -> b.read(Place.of("C", String.class)),
                b -> b.inhibitor(Place.of("C", String.class)),
                b -> b.reset(Place.of("C", String.class)))) {
            var n = chain(true);
            n.add(arc.apply(Transition.builder("watch").inputs(Arc.In.one(n.p("W")))
                .outputs(Arc.Out.place(n.p("W2")))).build());
            assertNull(NameFragment.classify(n.build(), EXT, Set.of(), AllMints.of(n.build())));
        }
    }

    // ── AC3: the join chain, through Route B ──────────────────────────────────────────────

    @Test
    void chain_doneIsReachableAndTheNetIsDeadlockFree_viaRouteB() {
        var reach = verify(new Q(chain(true), Map.of("S", 1),
            SmtProperty.unreachable(Set.of(chain(true).p("done"))), l(), l(), l(), EXT), false, 100_000);
        assertEquals(Route.NU_SCG, reach.route(), reach.report());
        assertTrue(reach.isViolated(), reach.report());

        var dlf = verify(new Q(chain(true), Map.of("S", 2), SmtProperty.deadlockFree(), l("done"), l(), l(), EXT),
            false, 100_000);
        assertEquals(Route.NU_SCG, dlf.route(), dlf.report());
        assertTrue(dlf.isProven(), dlf.report());
    }

    @Test
    void chain_independentMintNeverReachesDone() {
        var n = chainIndependentD();
        var r = verify(new Q(n, Map.of("S", 1, "S2", 1), SmtProperty.unreachable(Set.of(n.p("done"))),
            l(), l(), l(), EXT), false, 100_000);
        assertEquals(Route.NU_SCG, r.route(), r.report());
        assertTrue(r.isProven(), "no two different names are equated:\n" + r.report());
    }

    @Test
    @EnabledIf("z3Available")
    void chain_routesAgree() {
        assertRoutesAgree(new Q(chain(true), Map.of("S", 1),
            SmtProperty.unreachable(Set.of(chain(true).p("done"))), l(), l("S"), l(), EXT), "violated");
        assertRoutesAgree(new Q(chain(true), Map.of("S", 2), SmtProperty.deadlockFree(),
            l("done"), l("S"), l(), EXT), "proven");
        var n = chainIndependentD();
        assertRoutesAgree(new Q(n, Map.of("S", 1, "S2", 1), SmtProperty.unreachable(Set.of(n.p("done"))),
            l(), l("S", "S2"), l(), EXT), "proven");
    }

    // ── PNID fixtures ─────────────────────────────────────────────────────────────────────

    private static Q fig12cDeadlock(boolean relay, int k, FragmentMode mode) {
        return new Q(fig12c(relay), Map.of("R", k), SmtProperty.deadlockFree(), l("R"), l("R"), FIG12C_CARRIERS, mode);
    }

    private static Q fig12cBound(boolean relay, int k) {
        return new Q(fig12c(relay), Map.of("R", k), SmtProperty.placeBound(fig12c(relay).p("OR"), 2),
            l("R"), l("R"), FIG12C_CARRIERS, EXT);
    }

    @Test
    void fig12c_withoutTheRelay_extendedDeclines() {
        var r = verify(fig12cDeadlock(false, 1, EXT), true, 100_000);
        assertFalse(r.isProven() || r.isViolated(), r.report());
        assertTrue(r.report().contains("ν-net Route B (EXTENDED) declined"), r.report());
    }

    @Test
    void fig12c_withTheRelay_deadlockFreeProvenByRouteB() {
        // Paper label (Fig. 12(c)): identifier sound, bounded — deadlockFree expected proven.
        for (int k : new int[] {1, 2}) {
            var r = verify(fig12cDeadlock(true, k, EXT), true, 100_000);
            assertEquals(Route.NU_SCG, r.route(), "k=" + k + "\n" + r.report());
            assertTrue(r.isProven(), "k=" + k + "\n" + r.report());
        }
    }

    @Test
    void fig12c_withTheRelay_boundOrDecidedByRouteB() {
        // Paper label: bounded — placeBound(OR, 2) expected proven. Without a declared budget a
        // reachability-safety query goes to Route B.
        for (int k : new int[] {1, 2}) {
            var r = verify(fig12cBound(true, k), false, 100_000);
            assertEquals(Route.NU_SCG, r.route(), "k=" + k + "\n" + r.report());
            assertTrue(r.isProven(), "k=" + k + "\n" + r.report());
        }
    }

    @Test
    @EnabledIf("z3Available")
    void fig12c_routesAgree() {
        for (int k : new int[] {1, 2}) {
            assertRoutesAgree(fig12cDeadlock(true, k, EXT), "proven");
            assertRoutesAgree(fig12cBound(true, k), "proven");
        }
    }

    /** AC5: under BASE a relay declaration changes no verdict, and the report names it. */
    @Test
    void fig12c_base_ignoresTheDeclarationAndSaysSo() {
        var with = verify(fig12cDeadlock(true, 1, FragmentMode.BASE), true, 100_000);
        var without = verify(fig12cDeadlock(false, 1, FragmentMode.BASE), true, 100_000);
        assertEquals(verdict(without), verdict(with), with.report());
        assertEquals(without.route(), with.route());
        assertTrue(with.report().contains("NOTE: ν relay declarations ignored under BASE fragment mode (NU-054): "
            + "'e' -> 'P5'; select fragmentMode(EXTENDED) to analyse the joins as relays."), with.report());
        assertFalse(without.report().contains("NU-054"), without.report());
    }

    private static Q n1Deadlock(int k) {
        return new Q(n1Corr(true), Map.of("SUPPLY", k), SmtProperty.deadlockFree(), l("E_done"), l("SUPPLY"), l(), EXT);
    }

    @Test
    void n1Correlated_deadlockViolatedWithTraceAC() {
        // Spec NU-054 expects Violated with A, C (C moves the case's Y1 token before B joins on
        // it, stranding p). The paper labels N1 identifier sound: see the report.
        for (int k : new int[] {1, 2}) {
            var r = verify(n1Deadlock(k), true, 100_000);
            assertEquals(Route.NU_SCG, r.route(), "k=" + k + "\n" + r.report());
            assertTrue(r.isViolated(), "k=" + k + "\n" + r.report());
            if (k == 1) assertEquals(l("A", "C"), r.counterexampleTransitions(), r.report());
        }
    }

    @Test
    @EnabledIf("z3Available")
    void n1Correlated_routesAgree() {
        assertRoutesAgree(n1Deadlock(1), "violated");
        // k = 2: Spacer finds the violation locally but not always within the timeout on a
        // slower CI machine. Route A may answer unknown there, never the opposite verdict.
        assertRoutesAgreeOrUnknown(n1Deadlock(2), "violated");
    }

    private static Q unionDeadlock(boolean relay, int k) {
        return new Q(sUnion(relay), Map.of("SUPPLY", k), SmtProperty.deadlockFree(), l("d_done"), l("SUPPLY"), l("q"), EXT);
    }

    @Test
    void sUnion_deadlockViolatedWithTraceA_viaRouteB() {
        var before = verify(unionDeadlock(false, 1), true, 100_000);
        assertTrue(before.report().contains("ν-net Route B (EXTENDED) declined"), before.report());
        for (int k : new int[] {1, 2}) {
            var r = verify(unionDeadlock(true, k), true, 100_000);
            assertEquals(Route.NU_SCG, r.route(), "k=" + k + "\n" + r.report());
            assertTrue(r.isViolated(), "k=" + k + "\n" + r.report());
            if (k == 1) assertEquals(l("a"), r.counterexampleTransitions(), r.report());
        }
    }

    @Test
    @EnabledIf("z3Available")
    void sUnion_routesAgree() {
        for (int k : new int[] {1, 2}) assertRoutesAgree(unionDeadlock(true, k), "violated");
    }

    // ── correlated self-loop ──────────────────────────────────────────────────────────────

    private static Q selfLoopDeadlock(boolean independentQ, int k) {
        var m0 = independentQ ? Map.of("S", k, "T", k) : Map.of("S", k);
        return new Q(selfLoop(independentQ), m0, SmtProperty.deadlockFree(), l("done"),
            independentQ ? l("S", "T") : l("S"), l(), EXT);
    }

    @Test
    void selfLoop_relayedNameReachesTheNextJoin() {
        for (int k : new int[] {1, 2}) {
            var ok = verify(selfLoopDeadlock(false, k), true, 100_000);
            assertEquals(Route.NU_SCG, ok.route(), ok.report());
            assertTrue(ok.isProven(), "k=" + k + "\n" + ok.report());
            var stuck = verify(selfLoopDeadlock(true, k), true, 100_000);
            assertEquals(Route.NU_SCG, stuck.route(), stuck.report());
            assertTrue(stuck.isViolated(), "k=" + k + "\n" + stuck.report());
        }
    }

    @Test
    @EnabledIf("z3Available")
    void selfLoop_routesAgree() {
        for (int k : new int[] {1, 2}) {
            assertRoutesAgree(selfLoopDeadlock(false, k), "proven");
        }
        // k = 1 only: at k = 2 the covering semiflow gives six colour slots and Spacer does not
        // find the violation within 60 s (unknown, never a contradiction).
        assertRoutesAgree(selfLoopDeadlock(true, 1), "violated");
    }

    // ── A join's timeout writes into a relay target ───────────────────────────────────────

    /**
     * The AC3 join chain with {@code j1}'s relay into {@code C} written two ways: by the action, or
     * by the executor on timeout ({@code timeoutChild}). {@code j1} also consumes the uncoloured
     * {@code Z}, so a forward of a non-key input can be stated.
     */
    private static PetriNet chainWithTimeout(java.util.function.Function<Net, Arc.Out> timeoutChild) {
        var n = new Net("chain-timeout").t("fork", l("S"), l("A", "B", "D"), l(), l());
        var ms = MatchSpec.builder();
        ms.key(n.p("A"), (String v) -> NameId.of(v));
        ms.key(n.p("B"), (String v) -> NameId.of(v));
        ms.relayTo(n.p("C"), (String v) -> NameId.of(v));
        n.add(Transition.builder("j1")
            .inputs(Arc.In.one(n.p("A")), Arc.In.one(n.p("B")), Arc.In.one(n.p("Z")))
            .outputs(Arc.Out.xor(Arc.Out.place(n.p("C")),
                Arc.Out.timeout(Duration.ofMillis(10), timeoutChild.apply(n))))
            .match(ms.build())
            .build());
        n.t("j2", l("C", "D"), l("done"), l("C", "D"), l());
        return n.build();
    }

    private static SmtVerificationResult chainTimeoutDeadlock(PetriNet net) {
        var place = (java.util.function.Function<String, Place<?>>) name -> net.places().stream()
            .filter(p -> p.name().equals(name)).findFirst().orElseThrow();
        return SmtVerifier.forNet(net)
            .enumerationMaxClasses(0)
            .initialMarking(m -> m.tokens(place.apply("S"), 1).tokens(place.apply("Z"), 1))
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(place.apply("done"))
            .budgetPlaces(place.apply("S"))
            .fragmentMode(EXT)
            .timeout(Duration.ofSeconds(2))
            .verify();
    }

    /**
     * The executor checks every token a join deposits in a relay target, timeout branches included
     * (NU-054). A unit token ({@code Out.place} under {@code Timeout}) or a forward of a non-key
     * input carries no name or another one, so that firing fails and deposits nothing: {@code A}
     * and {@code B} are gone, {@code D} is stranded and the net deadlocks. The name layer would
     * relay the matched name into {@code C} instead and let {@code j2} fire, a wrong
     * {@code Proven}. Only a forward of a match key relays the matched name, and only that timeout
     * write keeps the join in the fragment, for Route B and for Route A's coloured encoding.
     */
    @Test
    @EnabledIf("z3Available")
    void aJoinTimeoutWriteIntoARelayTargetMustForwardAKey() {
        var unit = chainWithTimeout(n -> Arc.Out.place(n.p("C")));
        var other = chainWithTimeout(n -> Arc.Out.forwardInput(n.p("Z"), n.p("C")));
        for (var net : List.of(unit, other)) {
            var r = chainTimeoutDeadlock(net);
            assertFalse(r.isProven(), r.report());
            assertTrue(r.report().contains("Route B (EXTENDED) declined"), r.report());
            assertFalse(r.report().contains("ν-encoding: name-coloured"), r.report());
            assertNull(NameFragment.classify(net, EXT, Set.of(), AllMints.of(net)));
        }
        var key = chainWithTimeout(n -> Arc.Out.forwardInput(n.p("A"), n.p("C")));
        assertNotNull(NameFragment.classify(key, EXT, Set.of(), AllMints.of(key)));
        var r = chainTimeoutDeadlock(key);
        assertEquals(Route.NU_SCG, r.route(), r.report());
        assertTrue(r.isProven(), r.report());
    }
}
