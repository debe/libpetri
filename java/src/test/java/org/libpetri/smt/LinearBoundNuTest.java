package org.libpetri.smt;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.SmtVerificationResult.Route;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [VER-015] on a ν-net: the linear state-equation bound runs before the name-coloured encoding
 * ([NU-053]). The flat, name-blind state equation over-approximates the ν semantics, so its
 * structural Proven is sound there too. A property it cannot prove still reaches the coloured
 * encoding. PNID R2-3 ({@code research/net-metrics/validation/pnid/src/probe-slots.ts}): these
 * trivially true bounds timed out on Route A.
 */
@EnabledIf("z3Available")
class LinearBoundNuTest {

    /**
     * The report line the coloured plan's slot bound writes, and only it (the ν-encoding line
     * spells it {@code colour-slot bound}, lower case and without the colon).
     */
    private static final String SLOT_BOUND = "Colour-slot bound: ";

    private static int occurrences(String haystack, String needle) {
        return haystack.split(java.util.regex.Pattern.quote(needle), -1).length - 1;
    }

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static SmtVerificationResult verify(
            JoinRelayTest.Net n, Map<String, Integer> m0, SmtProperty property,
            List<String> budgets, List<String> carriers) {
        var v = SmtVerifier.forNet(n.build())
            .initialMarking(m -> m0.forEach((p, c) -> m.tokens(n.p(p), c)))
            .property(property)
            .fragmentMode(FragmentMode.EXTENDED)
            .budgetPlaces(budgets.stream().map(n::p).toArray(Place<?>[]::new))
            .timeout(Duration.ofSeconds(8));
        if (!carriers.isEmpty()) v.carrierPlaces(carriers.stream().map(n::p).toArray(Place<?>[]::new));
        return v.verify();
    }

    /** probe-slots.ts at budget 2: the first place neither a budget nor initially marked, bound 1000. */
    @Test
    void trivialBoundsOnPnidNuNets_areProvenStructurallyBeforeTheColouredEncoding() {
        record Case(JoinRelayTest.Net net, String budget, String target, List<String> carriers) {}
        var results = new ArrayList<SmtVerificationResult>();
        for (var c : List.of(
                new Case(JoinRelayTest.fig12c(true), "R", "P1", JoinRelayTest.FIG12C_CARRIERS),
                new Case(JoinRelayTest.n1Corr(true), "SUPPLY", "Y1", List.of()),
                new Case(JoinRelayTest.sUnion(true), "SUPPLY", "p", List.of("q")))) {
            var r = verify(c.net, Map.of(c.budget, 2), SmtProperty.placeBound(c.net.p(c.target), 1000),
                List.of(c.budget), c.carriers);
            System.out.println("[VER-015 on ν] " + c.net.build().name() + " bound(" + c.target + "<=1000): "
                + r.verdict() + " " + r.route() + " " + r.elapsed().toMillis() + " ms");
            results.add(r);
        }
        for (var r : results) {
            assertTrue(r.isProven(), r.report());
            assertEquals(Route.STRUCTURAL, r.route(), r.report());
            assertTrue(r.report().contains("PROVEN (structural)"), r.report());
            assertTrue(r.report().contains("(VER-015)"), r.report());
            // The coloured plan is built after the bound, so a structural Proven never runs its
            // slot-bound simplex, and nothing enumerates semiflows.
            assertFalse(r.report().contains(SLOT_BOUND), r.report());
            assertFalse(r.report().contains("semiflow"), r.report());
            assertTrue(r.elapsed().compareTo(Duration.ofSeconds(2)) < 0,
                "a structural proof, far under the 8 s timeout: " + r.elapsed());
        }
    }

    @Test
    void aNuPropertyTheLinearBoundCannotProve_stillReachesTheColouredEncoding() {
        // Name-blind, done is reachable (j1, j2 fire across the two mints), so the linear bound
        // has nothing to say; the exact coloured encoding proves it (JoinRelayTest.chain_routesAgree).
        var n = JoinRelayTest.chainIndependentD();
        var r = verify(n, Map.of("S", 1, "S2", 1), SmtProperty.unreachable(Set.of(n.p("done"))),
            List.of("S", "S2"), List.of());
        assertTrue(r.isProven(), r.report());
        assertEquals(Route.SMT, r.route(), r.report());
        assertTrue(r.report().contains("ν-encoding: name-coloured (colour-slot bound"), r.report());
        assertEquals(1, occurrences(r.report(), SLOT_BOUND), r.report());
        assertTrue(r.report().contains(" (re-checked in exact arithmetic)\n"), r.report());

        // A false bound: the linear bound cannot prove it, Route A finds the violation as before.
        var fig = JoinRelayTest.fig12c(true);
        var v = verify(fig, Map.of("R", 2), SmtProperty.placeBound(fig.p("OR"), 1), List.of("R"),
            JoinRelayTest.FIG12C_CARRIERS);
        assertTrue(v.isViolated(), v.report());
        assertEquals(Route.SMT, v.route(), v.report());
        assertTrue(v.report().contains("ν-encoding: name-coloured (colour-slot bound k=6;"), v.report());
        assertTrue(v.report().contains("  Colour-slot bound: LP optimum 6 over "), v.report());
        assertTrue(v.report().contains(", so k=6 (re-checked in exact arithmetic)\n"), v.report());
        assertEquals(1, occurrences(v.report(), SLOT_BOUND), v.report());
        assertFalse(v.report().contains("semiflow"), v.report());
    }

    @Test
    void aNuNetThePlanRefuses_neverSolvesTheSlotBound() {
        // mB consumes the budget place S2, so it is a declared mint; mA writes A from the plain
        // place W and is not one (NU-010). The plan refuses the net at the classification, which
        // needs no colour-slot bound, so the simplex behind that bound never runs.
        Place<String> w = Place.of("W", String.class);
        Place<String> s2 = Place.of("S2", String.class);
        Place<String> a = Place.of("A", String.class);
        Place<String> b = Place.of("B", String.class);
        Place<String> done = Place.of("DONE", String.class);
        var net = StructureOnly.bind(PetriNet.builder("undeclared_producer").transitions(
            Transition.builder("mA").inputs(In.one(w)).outputs(Out.place(a)).build(),
            Transition.builder("mB").inputs(In.one(s2)).outputs(Out.place(b)).build(),
            Transition.builder("J").inputs(In.one(a), In.one(b))
                .match(MatchSpec.builder().key(a, (String x) -> NameId.of(x)).key(b, (String x) -> NameId.of(x)).build())
                .outputs(Out.place(done)).build()).build());
        var r = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(w, 1).tokens(s2, 1))
            .property(SmtProperty.placeBound(done, 0))
            .budgetPlaces(s2)
            .timeout(Duration.ofSeconds(8))
            .verify();
        assertFalse(r.isProven(), r.report());
        assertFalse(r.report().contains("ν-encoding: name-coloured"), r.report());
        assertNotEquals(Route.NU_SCG, r.route(), r.report());
        assertFalse(r.report().contains(SLOT_BOUND), r.report());
    }

    @Test
    void encodeScripts_emitsTheBoundScriptWhenAColouredPlanExists() {
        var n = JoinRelayTest.fig12c(true);
        var scripts = SmtVerifier.forNet(n.build())
            .initialMarking(m -> m.tokens(n.p("R"), 2))
            .property(SmtProperty.placeBound(n.p("P1"), 1000))
            .fragmentMode(FragmentMode.EXTENDED)
            .budgetPlaces(n.p("R"))
            .carrierPlaces(JoinRelayTest.FIG12C_CARRIERS.stream().map(n::p).toArray(Place<?>[]::new))
            .encodeScripts();
        assertTrue(scripts.coloured(), "the fixture is on the name-coloured encoding");
        assertNotNull(scripts.bound(), "verify() sends the bound query first, so the script is emitted");
    }
}
