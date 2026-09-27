package org.libpetri.smt;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.core.Place;
import org.libpetri.smt.SmtVerificationResult.Route;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
        assertTrue(r.report().contains("ν-encoding: name-coloured (exact within budget"), r.report());

        // A false bound: the linear bound cannot prove it, Route A finds the violation as before.
        var fig = JoinRelayTest.fig12c(true);
        var v = verify(fig, Map.of("R", 2), SmtProperty.placeBound(fig.p("OR"), 1), List.of("R"),
            JoinRelayTest.FIG12C_CARRIERS);
        assertTrue(v.isViolated(), v.report());
        assertEquals(Route.SMT, v.route(), v.report());
        assertTrue(v.report().contains("ν-encoding: name-coloured (exact within budget"), v.report());
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
