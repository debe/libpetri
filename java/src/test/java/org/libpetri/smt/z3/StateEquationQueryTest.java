package org.libpetri.smt.z3;

import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.SmtVerifier;
import org.libpetri.smt.z3.StateEquationQuery.Candidate;
import org.libpetri.smt.z3.StateEquationQuery.MarkingInequality;
import org.libpetri.smt.z3.StateEquationQuery.Origin;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.math.BigInteger;
import java.time.Duration;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.smt.z3.StateEquationNets.*;

/**
 * [VER-018] the state-equation query: encoding, candidate decoding, and the renderings of a
 * refinement. Mirrors the query case of
 * {@code typescript/tests/verification/state-equation-phase.test.ts}; the script text itself
 * is pinned against the Rust goldens by {@code StateEquationQueryGoldenTest}.
 */
class StateEquationQueryTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    @Test
    void encodesTheQueryWithTheRefinementsAndReadsACandidateBack() {
        var join = joinWithSkip();
        var flat = join.flat();
        var refinement = inequality(flat, 0, "hasdata", 1, "ready0", -1, "ready1", -1);
        String script = StateEquationQuery.encode(flat, join.m0(), SmtProperty.deadlockFree(),
            Set.of(join.done(), join.skipped()), List.of(), List.of(refinement));
        assertTrue(script.contains("(set-logic QF_LIA)"));
        assertTrue(script.contains("(declare-const n" + (flat.transitionCount() - 1) + " Int)"));
        int h = indexOf(flat, "hasdata");
        int r0 = indexOf(flat, "ready0");
        int r1 = indexOf(flat, "ready1");
        assertTrue(script.contains("(assert (<= (+ m" + h + " (- m" + r0 + ") (- m" + r1 + ")) 0))"), script);

        Candidate candidate = StateEquationQuery.decodeCandidate(
            "sat\n(\n  (define-fun m" + h + " () Int\n    1)\n  (define-fun n0 () Int\n    1)\n)",
            flat.placeCount(), flat.transitionCount());
        assertNotNull(candidate);
        assertEquals(1, candidate.marking()[h]);
        assertEquals(1, candidate.counts()[0]);
        assertFalse(StateEquationQuery.holdsAt(refinement, candidate.marking()));
        assertEquals("hasdata <= ready0 + ready1", StateEquationQuery.formatInequality(flat, refinement));

        String certificate = StateEquationQuery.refinementCertificate(
            flat.placeCount(), flat.transitionCount(), List.of(refinement));
        assertTrue(certificate.contains("(x!" + (flat.placeCount() + flat.transitionCount() - 1) + " Int)"));
        assertTrue(certificate.contains("(<= (+ x!" + h + " (- x!" + r0 + ") (- x!" + r1 + ")) 0)"), certificate);
    }

    @Test
    void readsATrapTheOtherWayRound() {
        var flat = joinWithSkip().flat();
        var trap = new MarkingInequality(inequality(flat, -1, "start", -1, "done", -1).weights(),
            BigInteger.ONE.negate(), Origin.TRAP);
        assertEquals("done + start >= 1", StateEquationQuery.formatInequality(flat, trap));
        String certificate = StateEquationQuery.refinementCertificate(flat.placeCount(), 0, List.of(trap));
        assertTrue(certificate.endsWith("Bool\n    (>= (+ x!4 x!9) 1))"), certificate);
        // No refinement: the body is `true`; several: one conjunct per line.
        assertEquals("(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool\n    true)",
            StateEquationQuery.refinementCertificate(1, 1, List.of()));
        var weighted = inequality(flat, -2, "done", 2, "start", -3);
        assertEquals("2*done <= -2 + 3*start", StateEquationQuery.formatInequality(flat, weighted));
        assertEquals("(define-fun Reachable ((x!0 Int) (x!1 Int) (x!2 Int) (x!3 Int) (x!4 Int) (x!5 Int) "
                + "(x!6 Int) (x!7 Int) (x!8 Int) (x!9 Int)) Bool\n"
                + "    (and (>= (+ x!4 x!9) 1)\n"
                + "         (<= (+ (* 2 x!4) (* (- 3) x!9)) (- 2))))",
            StateEquationQuery.refinementCertificate(flat.placeCount(), 0, List.of(trap, weighted)));
        assertEquals("0 >= 0", StateEquationQuery.formatInequality(flat, inequality(flat, 0)));
        assertEquals("done <= 0", StateEquationQuery.formatInequality(flat, inequality(flat, 0, "done", 1)));
    }

    @Test
    void holdsAtIsExactAndReadsAMissingPlaceAsEmpty() {
        var huge = new MarkingInequality(
            List.of(BigInteger.valueOf(Long.MAX_VALUE), BigInteger.valueOf(Long.MAX_VALUE)),
            BigInteger.valueOf(Long.MAX_VALUE).multiply(BigInteger.TWO), Origin.INDUCTIVE);
        // The sum is 2·(2^63 − 1): a wrapped long would read it negative and pass the next one too.
        assertTrue(StateEquationQuery.holdsAt(huge, new long[] {1, 1}));
        assertFalse(StateEquationQuery.holdsAt(huge, new long[] {2, 1}));
        var positive = new MarkingInequality(List.of(BigInteger.ONE, BigInteger.ONE), BigInteger.ZERO, Origin.INDUCTIVE);
        assertTrue(StateEquationQuery.holdsAt(positive, new long[0]));
        assertFalse(StateEquationQuery.holdsAt(positive, new long[] {1}));
    }

    @Test
    void decodesTheModelAsTheTypeScriptPortDoes() {
        // The negation form, a line break before the literal, and definitions of other names.
        var c = StateEquationQuery.decodeCandidate(
            "sat\n((define-fun m0 () Int (- 3)) (define-fun n2 () Int\n  7) (define-fun x0 () Int 1) "
                + "(define-fun m1 () Real 1.0))", 3, 3);
        assertEquals(new Candidate(new long[] {-3, 0, 0}, new long[] {0, 0, 7}), c);
        // An index past the net is skipped; with nothing else defined there is no candidate.
        assertNull(StateEquationQuery.decodeCandidate("sat\n((define-fun m9 () Int 4) (define-fun n9 () Int 4))", 3, 3));
        assertEquals(new Candidate(new long[] {0, 0, 0}, new long[] {0, 3, 0}), StateEquationQuery.decodeCandidate(
            "sat\n((define-fun m99999999999999999999 () Int 2) (define-fun n1 () Int 3))", 3, 3));
        assertNull(StateEquationQuery.decodeCandidate("unsat", 3, 3));
        // TypeScript holds a candidate in doubles: up to 2^53 − 1 decodes, beyond it the whole
        // model does not, even on a place the net does not have.
        assertEquals(new Candidate(new long[] {9007199254740991L, 0, 0}, new long[] {-9007199254740991L, 0, 0}),
            StateEquationQuery.decodeCandidate("sat\n((define-fun m0 () Int 9007199254740991) "
                + "(define-fun n0 () Int (- 9007199254740991)))", 3, 3));
        assertNull(StateEquationQuery.decodeCandidate("sat\n((define-fun m0 () Int 9007199254740992))", 3, 3));
        assertNull(StateEquationQuery.decodeCandidate(
            "sat\n((define-fun m7 () Int 9007199254740992) (define-fun m0 () Int 1))", 3, 3));
    }

    /**
     * Every model of the unrefined join query strands {@code hasdata} after a merge, so the join
     * inequality excludes each of them, and with it the query has no model left.
     */
    @Test
    @EnabledIf("z3Available")
    void theJoinInequalityRefutesEveryCandidateOfTheJoinQuery() throws Exception {
        var join = joinWithSkip();
        var flat = join.flat();
        var solver = Z3Solver.resolve();
        var refinement = inequality(flat, 0, "hasdata", 1, "ready0", -1, "ready1", -1);
        String unrefined = StateEquationQuery.encode(flat, join.m0(), SmtProperty.deadlockFree(),
            Set.of(join.done(), join.skipped()), List.of(), List.of());
        String reply = solver.run(unrefined, "state-equation", Duration.ofSeconds(30), List.of()).stdout();
        assertEquals("sat", SmtText.classifyFirstLine(reply), reply);
        var candidate = StateEquationQuery.decodeCandidate(reply, flat.placeCount(), flat.transitionCount());
        assertNotNull(candidate, reply);
        assertTrue(candidate.marking()[indexOf(flat, "hasdata")] >= 1, candidate::toString);
        assertFalse(StateEquationQuery.holdsAt(refinement, candidate.marking()));

        String refined = StateEquationQuery.encode(flat, join.m0(), SmtProperty.deadlockFree(),
            Set.of(join.done(), join.skipped()), List.of(), List.of(refinement));
        reply = solver.run(refined, "state-equation", Duration.ofSeconds(30), List.of()).stdout();
        assertEquals("unsat", SmtText.classifyFirstLine(reply), reply);
    }
}
