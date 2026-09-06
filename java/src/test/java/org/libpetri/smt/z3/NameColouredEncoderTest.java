package org.libpetri.smt.z3;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;

import org.junit.jupiter.api.Test;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.IncidenceMatrix;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.invariant.PInvariantComputer;

/**
 * Z3-free conformance for the name-coloured fragment gate
 * ({@link NameColouredEncoder#buildPlan}). Pins the P-semiflow colour-slot bound (a
 * genuine unbounded colour leak must fall back to the sound over-approximation) plus the
 * NU-053 fragment extensions: the EXTENDED coloured-consumer roles (drain / carrier
 * relay), the relay-must-not-refund rule, and XOR-expanded output branches no longer
 * blocking the plan.
 */
class NameColouredEncoderTest {

    /**
     * A budget-bounded mint→join net (same-mint scatter-gather). The mint consumes
     * 1 budget and stamps the fresh colour into both correlated inputs; the join
     * refunds 1 budget (conserving) or 2 (inflating, into a second budget place).
     */
    private static PetriNet mintJoinNet(boolean inflating) {
        var budget1 = Place.of("budget1", Integer.class);
        var budget2 = Place.of("budget2", Integer.class);
        var a = Place.of("branchA", String.class);
        var b = Place.of("branchB", String.class);

        var mint = Transition.builder("mint")
            .inputs(Arc.In.one(budget1))
            .outputs(Arc.Out.and(a, b))
            .build();
        Arc.Out joinOut = inflating ? Arc.Out.and(budget1, budget2) : Arc.Out.place(budget1);
        var join = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(joinOut)
            .build();
        return PetriNet.builder("mintJoin").transitions(mint, join).build();
    }

    /**
     * A mint→join net plus an EXTENDED coloured drain: a non-match transition that
     * consumes one correlated input {@code a} (count 1) into a plain sink. Rejected under
     * BASE (a non-match consumer of a coloured place), admitted under EXTENDED.
     */
    private static PetriNet mintJoinDrainNet() {
        var budget1 = Place.of("budget1", Integer.class);
        var a = Place.of("a", String.class);
        var b = Place.of("b", String.class);
        var sink = Place.of("sink", String.class);

        var mint = Transition.builder("mint")
            .inputs(Arc.In.one(budget1))
            .outputs(Arc.Out.and(a, b))
            .build();
        var join = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(budget1))
            .build();
        var drain = Transition.builder("drain")
            .inputs(Arc.In.one(a))
            .outputs(Arc.Out.place(sink))
            .build();
        return PetriNet.builder("mintJoinDrain").transitions(mint, join, drain).build();
    }

    /**
     * A mint→join net with an EXTENDED carrier relay: the fork co-mints into the carrier
     * place {@code carrier} and the join input {@code b}; a relay threads {@code carrier}'s
     * name into the other join input {@code a}; the join correlates {@code a} and {@code b}.
     * {@code carrier} is coloured only when declared as a carrier place under EXTENDED. When
     * {@code relayRefunds}, the relay also refunds budget — which must be rejected, since a
     * relay keeps the colour live.
     */
    private static PetriNet mintRelayJoinNet(boolean relayRefunds) {
        var budget1 = Place.of("budget1", Integer.class);
        var carrier = Place.of("carrier", String.class);
        var a = Place.of("a", String.class);
        var b = Place.of("b", String.class);

        var mint = Transition.builder("mint")
            .inputs(Arc.In.one(budget1))
            .outputs(Arc.Out.and(carrier, b))
            .build();
        Arc.Out relayOut = relayRefunds ? Arc.Out.and(a, budget1) : Arc.Out.place(a);
        var relay = Transition.builder("relay")
            .inputs(Arc.In.one(carrier))
            .outputs(relayOut)
            .build();
        var join = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(budget1))
            .build();
        return PetriNet.builder("mintRelayJoin").transitions(mint, relay, join).build();
    }

    /**
     * A mint→join net plus a plain XOR transition (uncoloured), which expands to two flat
     * rows — exercising NU-053 Part 3 (no 1:1 net↔flat assumption).
     */
    private static PetriNet mintJoinXorNet() {
        var budget1 = Place.of("budget1", Integer.class);
        var a = Place.of("a", String.class);
        var b = Place.of("b", String.class);
        var src = Place.of("src", Integer.class);
        var x = Place.of("x", Integer.class);
        var y = Place.of("y", Integer.class);

        var mint = Transition.builder("mint")
            .inputs(Arc.In.one(budget1))
            .outputs(Arc.Out.and(a, b))
            .build();
        var join = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(budget1))
            .build();
        var branch = Transition.builder("branch")
            .inputs(Arc.In.one(src))
            .outputs(Arc.Out.xor(x, y))
            .build();
        return PetriNet.builder("mintJoinXor").transitions(mint, join, branch).build();
    }

    /**
     * A leaky fork ([NU-053] S2): the mint co-mints its colour into the join inputs
     * {@code a}, {@code b} AND a declared carrier {@code c}, but the join only re-collects
     * {@code a}, {@code b} and nothing ever consumes {@code c}. The colour outlives the
     * budget the join refunds, so the real net can hold more than k live colours while the
     * k-colour encoding gets stuck at the freshness guard — an under-approximation that
     * could report a false PROVEN.
     */
    private static PetriNet mintLeakyCarrierNet() {
        var budget1 = Place.of("budget1", Integer.class);
        var a = Place.of("a", String.class);
        var b = Place.of("b", String.class);
        var c = Place.of("c", String.class);

        var mint = Transition.builder("mint")
            .inputs(Arc.In.one(budget1))
            .outputs(Arc.Out.and(a, b, c))
            .build();
        var join = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(budget1))
            .build();
        return PetriNet.builder("mintLeakyCarrier").transitions(mint, join).build();
    }

    private static NameColouredEncoder.ColouredPlan planFor(
            PetriNet net, FragmentMode mode, String... carriers) {
        return planFor(net, mode, 1, carriers);
    }

    private static NameColouredEncoder.ColouredPlan planFor(
            PetriNet net, FragmentMode mode, int budgetTokens, String... carriers) {
        var flat = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var initial = MarkingState.builder()
            .tokens(Place.of("budget1", Integer.class), budgetTokens)
            .build();
        var matrix = IncidenceMatrix.from(flat);
        var semiflows = PInvariantComputer.computePSemiflows(matrix, flat, initial);
        return NameColouredEncoder.buildPlan(
            net, flat, initial, Set.of("budget1", "budget2"), mode, Set.of(carriers), semiflows);
    }

    @Test
    void zeroBudgetYieldsTheExactZeroSlotPlan() {
        // NU-053 AC6: with no budget token the covering semiflow's initial sum is zero, and
        // k = 0 is an exact plan rather than a fallback — no coloured token can ever exist
        // (Semiflow.lean, vacuous_colour_layer).
        var plan = planFor(mintJoinNet(false), FragmentMode.BASE, 0);
        assertNotNull(plan, "k = 0 is a plan, not a fallback");
        assertEquals(0, plan.k);
    }

    @Test
    void budgetConservingJoinTakesExactPath() {
        // Refund (1) == mint cost (1): live names ≤ k, so the exact name-coloured
        // encoding is used.
        assertNotNull(planFor(mintJoinNet(false), FragmentMode.BASE));
    }

    @Test
    void budgetRefundToNonmintingPlaceStaysBounded() {
        // [NU-053] A join that refunds an extra token to a NON-minting place keeps the
        // minting budget conserved, so at most one colour is live — the net is
        // colour-bounded and the P-semiflow bound admits it. (The old budget-Φ heuristic
        // wrongly rejected any refund exceeding the mint cost; genuine colour leaks — where
        // a co-minted place accumulates distinct colours — are covered by
        // extendedLeakyCarrierFanoutRejected, which still falls back.)
        assertNotNull(planFor(mintJoinNet(true), FragmentMode.BASE));
    }

    @Test
    void extendedDrainRejectedUnderBaseAdmittedUnderExtended() {
        // A non-match consumer of a coloured place is out-of-fragment under BASE and
        // admitted as a drain under EXTENDED.
        var net = mintJoinDrainNet();
        assertNull(planFor(net, FragmentMode.BASE));
        assertNotNull(planFor(net, FragmentMode.EXTENDED));
    }

    @Test
    void extendedCarrierRelayAdmittedOnlyUnderExtended() {
        // The carrier place is coloured only when declared under EXTENDED; then the relay
        // threading its name to the join input is an admitted Consume.
        var net = mintRelayJoinNet(false);
        assertNull(planFor(net, FragmentMode.BASE));
        assertNotNull(planFor(net, FragmentMode.EXTENDED, "carrier"));
    }

    @Test
    void extendedRelayRefundingBudgetRejected() {
        // A relay keeps the colour live; if it also refunded budget the freed token could
        // mint a (k+1)-th live colour. buildPlan must reject it.
        var net = mintRelayJoinNet(true);
        assertNull(planFor(net, FragmentMode.EXTENDED, "carrier"));
    }

    @Test
    void extendedLeakyCarrierFanoutRejected() {
        // [NU-053] S2: the mint fans its colour into a, b AND carrier c, but the refunding
        // join only re-collects a, b — c is never consumed, so the colour outlives its
        // refunded budget and the real net can hold more than k live colours. buildPlan
        // must reject this (null → sound over-approximation) rather than certify an exact
        // plan the quiescence gate would trust for a false Proven. Contrast the admitted
        // carrier-relay case, where the fork's carrier branch is relayed back into a join
        // input (atomic re-collection).
        assertNull(planFor(mintLeakyCarrierNet(), FragmentMode.EXTENDED, "c"));
    }

    @Test
    void xorTransitionNoLongerBlocksThePlan() {
        // A plain XOR transition expands to two flat rows; NU-053 Part 3 drops the old 1:1
        // net↔flat rejection so the mint→join fragment is still recognised.
        assertNotNull(planFor(mintJoinXorNet(), FragmentMode.BASE));
    }

    /**
     * The coloured quiescence arms ([VER-002] DeadlockFree / TerminatesAtSink, [NU-040]
     * JoinedOrDeadLettered) had NO test in any language before the VER-002 split — a
     * drift in them would have passed every gate, because the shared fixtures either
     * route to Route B or use {@code place-bound}. Mirrors Rust's
     * {@code coloured_quiescence_arms_differ_by_property}.
     */
    @Test
    void colouredQuiescenceArmsDifferByProperty() {
        var net = mintJoinNet(false);
        var flat = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var initial = MarkingState.builder()
            .tokens(Place.of("budget1", Integer.class), 1)
            .build();
        var plan = planFor(net, FragmentMode.BASE);
        assertNotNull(plan, "mint→join is in-fragment");

        var branchA = Place.of("branchA", String.class);
        var branchB = Place.of("branchB", String.class);
        Set<Place<?>> sinks = Set.of(branchA);

        String tas = violationTerm(
            encodeColoured(plan, flat, initial, SmtProperty.terminatesAtSink(), sinks));
        // Derive the sink-is-empty clause from TerminatesAtSink's own output rather than
        // reaching into the encoder's private aggregate() helper: it is the clause the
        // arm appends last, over branchA's colour slots.
        var m = Pattern.compile("\\(= \\(\\+[^()]*\\) 0\\)").matcher(tas);
        assertTrue(m.find(), () -> "TerminatesAtSink must emit a sink-is-empty term:\n" + tas);
        String sinkIsEmpty = m.group();
        assertTrue(tas.endsWith(sinkIsEmpty + ")"),
            () -> "the sink clause is the arm's last conjunct:\n" + tas);

        String dl = violationTerm(
            encodeColoured(plan, flat, initial, SmtProperty.deadlockFree(), sinks));
        assertNotEquals(tas, dl, "the two VER-002 properties must encode differently");
        assertFalse(dl.contains(sinkIsEmpty),
            () -> "strict DeadlockFree must not require the sink to be empty:\n" + dl);
        assertTrue(dl.contains("(or (>= "),
            () -> "DeadlockFree must offer a stranded-token disjunction:\n" + dl);

        String jdl = violationTerm(encodeColoured(
            plan, flat, initial, SmtProperty.joinedOrDeadLettered(branchB), sinks));
        assertNotEquals(dl, jdl, "the NU-040 arm must not reuse the DeadlockFree clause");
        assertFalse(jdl.contains(sinkIsEmpty),
            () -> "NU-040 AC4: a declared sink must not excuse a stranded group:\n" + jdl);
    }

    private static String encodeColoured(
            NameColouredEncoder.ColouredPlan plan, FlatNet flat, MarkingState initial,
            SmtProperty property, Set<Place<?>> sinks) {
        var encoding = NameColouredEncoder.encode(plan, flat, initial, property, List.of(), sinks);
        assertNotNull(encoding, "in-fragment net encodes");
        return encoding.smt2();
    }

    /** The {@code Bad(M)} term of the script's error rule, without the Reachable guard. */
    private static String violationTerm(String smt2) {
        int error = smt2.indexOf(")\n      Error)))");
        assertTrue(error > 0, "the script carries an error rule");
        int reachable = smt2.lastIndexOf("(Reachable ", error);
        return smt2.substring(smt2.indexOf(") ", reachable) + 2, error);
    }
}
