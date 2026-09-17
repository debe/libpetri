package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.z3.AbstractReplayer;
import org.libpetri.smt.z3.SmtEncoder;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.OptionalInt;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [VER-002] QuiescentCount: a token count at every quiescent marking, its lower bound waived
 * while a marker holds a token.
 *
 * <p>Two jobs share a budget of two: {@code start} takes a unit, {@code finish} refunds it.
 * With {@code abort} a running job may stop the run instead, keeping its unit; {@code start}
 * is inhibited by {@code halt}. Flat place order: budget, done, halt, jobs, running. Mirrors
 * {@code typescript/tests/verification/quiescent-count.test.ts}.
 */
class QuiescentCountTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<String> BUDGET = Place.of("budget", String.class);
    private static final Place<String> DONE = Place.of("done", String.class);
    private static final Place<String> HALT = Place.of("halt", String.class);
    private static final Place<String> JOBS = Place.of("jobs", String.class);
    private static final Place<String> RUNNING = Place.of("running", String.class);

    private static PetriNet jobsNet(boolean refund, boolean abort) {
        var transitions = new ArrayList<Transition>();
        transitions.add(Transition.builder("start").inputs(In.one(JOBS), In.one(BUDGET)).inhibitors(HALT)
            .outputs(Out.place(RUNNING)).build());
        transitions.add(Transition.builder("finish").inputs(In.one(RUNNING))
            .outputs(refund ? Out.and(BUDGET, DONE) : Out.place(DONE)).build());
        if (abort) {
            transitions.add(Transition.builder("abort").inputs(In.one(RUNNING)).outputs(Out.place(HALT)).build());
        }
        // `halt` is declared by the inhibitor even without `abort`, so a waiver on it resolves.
        return StructureOnly.bind(PetriNet.builder("jobs").transitions(transitions.toArray(new Transition[0])).build());
    }

    private static MarkingState m0() {
        return MarkingState.builder().tokens(JOBS, 2).tokens(BUDGET, 2).build();
    }

    private static SmtProperty.QuiescentCount count(
            List<Place<?>> places, int min, OptionalInt max, List<Place<?>> waivedBy) {
        return SmtProperty.quiescentCount(places, min, max, waivedBy);
    }

    private static MarkingState marking(Object... placeCounts) {
        var b = MarkingState.builder();
        for (int i = 0; i < placeCounts.length; i += 2) {
            b.tokens((Place<?>) placeCounts[i], (Integer) placeCounts[i + 1]);
        }
        return b.build();
    }

    // === The property ===

    @Test
    void validatesItsBounds_andDescribesItself() {
        var above = assertThrows(IllegalArgumentException.class,
            () -> count(List.of(BUDGET), 2, OptionalInt.of(1), List.of()));
        assertTrue(above.getMessage().contains("0 <= min <= max, got 2..1"), above.getMessage());
        assertThrows(IllegalArgumentException.class, () -> count(List.of(BUDGET), -1, OptionalInt.of(1), List.of()));
        assertThrows(IllegalArgumentException.class, () -> count(List.of(BUDGET), -1, OptionalInt.empty(), List.of()));
        // An unbounded max never conflicts with min, however large.
        assertTrue(count(List.of(BUDGET), Integer.MAX_VALUE, OptionalInt.empty(), List.of()).max().isEmpty());

        assertEquals("Quiescent count: exactly 2 across {budget}; lower bound waived while {halt} is marked",
            count(List.of(BUDGET), 2, OptionalInt.of(2), List.of(HALT)).description());
        assertEquals("Quiescent count: at least 1 across {budget, done}",
            SmtProperty.quiescentCount(List.of(BUDGET, DONE), 1, OptionalInt.empty()).description());
        assertEquals("Quiescent count: at most 3 across {jobs}; lower bound waived while {halt, done} is marked",
            count(List.of(JOBS), 0, OptionalInt.of(3), List.of(HALT, DONE)).description());
        assertEquals("between 1 and 3", SmtProperty.countPhrase(1, OptionalInt.of(3)));
        assertEquals("any number", SmtProperty.countPhrase(0, OptionalInt.empty()));
        assertEquals("exactly 0", SmtProperty.countPhrase(0, OptionalInt.of(0)));
        assertEquals("exactly 1 across {done, budget}", SmtProperty.countAcross(1, OptionalInt.of(1), List.of(DONE, BUDGET)));
    }

    @Test
    void encodesTheCountClauseOnTopOfQuiescence_placesAndWaiversInIndexOrder() {
        var flat = flat(jobsNet(true, true));
        java.util.function.Function<SmtProperty, String> encode = prop ->
            violationTerm(SmtEncoder.encode(flat, m0(), prop, List.of(), Set.of(), false).smt2());
        String both = encode.apply(count(List.of(DONE, BUDGET), 1, OptionalInt.of(3), List.of(HALT)));
        assertTrue(both.contains("(or (and (< (+ m0 m1) 1) (= m2 0)) (> (+ m0 m1) 3))"), both);
        // Quiescence first: the inhibitor on `start` is a reason it is disabled.
        assertTrue(both.startsWith("(and (or (< m0 1) (< m3 1) (> m2 0))"), both);
        String lower = encode.apply(count(List.of(DONE, BUDGET), 2, OptionalInt.empty(), List.of()));
        assertTrue(lower.endsWith("\n         (< (+ m0 m1) 2))"), lower);
        assertFalse(lower.contains("(> (+ m0 m1)"), "an unbounded max has no upper clause: " + lower);
        String upper = encode.apply(count(List.of(DONE, BUDGET), 0, OptionalInt.of(2), List.of(HALT)));
        assertTrue(upper.endsWith("\n         (> (+ m0 m1) 2))"), upper);
        assertEquals("false", encode.apply(count(List.of(DONE, BUDGET), 0, OptionalInt.empty(), List.of(HALT))));
    }

    @Test
    void isDecidedByTheReplayerExactlyAsTheEncoderStatesIt() {
        var flat = flat(jobsNet(true, true));
        record Bad(FlatNet flat) {
            boolean at(int[] state, int min, OptionalInt max, List<Place<?>> waivedBy) {
                return AbstractReplayer.violates(flat, count(List.of(BUDGET), min, max, waivedBy), Set.of(), state);
            }
        }
        var bad = new Bad(flat);
        var two = OptionalInt.of(2);
        // [budget, done, halt, jobs, running]
        assertTrue(bad.at(new int[] {0, 2, 0, 0, 0}, 2, two, List.of(HALT)));             // quiescent, below, no waiver
        assertFalse(bad.at(new int[] {1, 1, 1, 0, 0}, 2, two, List.of(HALT)));            // below, but halt waives it
        assertTrue(bad.at(new int[] {1, 1, 1, 0, 0}, 2, two, List.of()));                 // below, nothing waives it
        assertTrue(bad.at(new int[] {3, 0, 0, 0, 0}, 2, two, List.of(HALT)));             // above: never waived
        assertTrue(bad.at(new int[] {3, 0, 1, 0, 0}, 2, two, List.of(HALT)));             // ... not even while halt is marked
        assertFalse(bad.at(new int[] {2, 0, 0, 1, 0}, 0, OptionalInt.of(1), List.of(HALT))); // not quiescent: start is enabled
        assertFalse(bad.at(new int[] {2, 2, 0, 0, 0}, 2, two, List.of(HALT)));            // meets it
        assertFalse(bad.at(new int[] {9, 0, 0, 0, 0}, 2, OptionalInt.empty(), List.of())); // an unbounded max has no upper bound
        // A place named twice is counted once, as the encoder's index order reads it.
        var twice = count(List.of(BUDGET, BUDGET), 2, two, List.of());
        assertTrue(AbstractReplayer.violates(flat, twice, Set.of(), new int[] {1, 0, 0, 0, 0}));
    }

    // === The graph routes' reading of a count ===

    @Test
    void tokensAcross_countsEachPlaceOnce() {
        var m = marking(BUDGET, 2, DONE, 3);
        assertEquals(5, GraphDecision.tokensAcross(m, List.of(BUDGET, DONE, BUDGET)));
        assertEquals(0, GraphDecision.tokensAcross(m, List.of(HALT)));
        assertEquals(0, GraphDecision.tokensAcross(m, List.of()));
    }

    @Test
    void countViolation_waivesOnlyTheLowerBound() {
        var two = OptionalInt.of(2);
        var budget = List.of(BUDGET);
        var halt = List.of(HALT);
        assertEquals(GraphDecision.CountBound.LOWER, GraphDecision.countViolation(marking(BUDGET, 1), budget, 2, two, halt));
        assertNull(GraphDecision.countViolation(marking(BUDGET, 1, HALT, 1), budget, 2, two, halt));
        assertEquals(GraphDecision.CountBound.UPPER, GraphDecision.countViolation(marking(BUDGET, 3), budget, 2, two, halt));
        assertEquals(GraphDecision.CountBound.UPPER,
            GraphDecision.countViolation(marking(BUDGET, 3, HALT, 1), budget, 2, two, halt));
        assertNull(GraphDecision.countViolation(marking(BUDGET, 2), budget, 2, two, halt));
        assertNull(GraphDecision.countViolation(marking(BUDGET, 99), budget, 0, OptionalInt.empty(), halt));
        assertEquals(GraphDecision.CountBound.LOWER,
            GraphDecision.countViolation(MarkingState.empty(), budget, 1, OptionalInt.empty(), halt));
    }

    @Test
    void decideOverClasses_readsQuiescentClassesOnly() {
        var markings = List.of(marking(BUDGET, 1), marking(BUDGET, 1, HALT, 1), MarkingState.empty());
        var quiescent = List.of(false, true, true);
        var view = new GraphDecision.ClassView() {
            @Override
            public int count() {
                return markings.size();
            }

            @Override
            public MarkingState markingOf(int i) {
                return markings.get(i);
            }

            @Override
            public boolean isQuiescent(int i) {
                return quiescent.get(i);
            }
        };
        // Class 0 is below but not quiescent, class 1 is waived: the empty class 2 witnesses.
        assertEquals(2, GraphDecision.decideOverClasses(
            view, count(List.of(BUDGET), 2, OptionalInt.of(2), List.of(HALT)), Set.of(), List.of()));
        assertEquals(-1, GraphDecision.decideOverClasses(
            view, count(List.of(BUDGET), 0, OptionalInt.of(1), List.of(HALT)), Set.of(), List.of()));
    }

    // === The enumeration route ===

    private static SmtVerificationResult verify(PetriNet net, int min, int max, List<Place<?>> waivedBy) {
        return SmtVerifier.forNet(net).initialMarking(m0())
            .property(count(List.of(BUDGET), min, OptionalInt.of(max), waivedBy))
            .timeout(Duration.ofSeconds(30)).verify();
    }

    @Test
    void enumeration_provesARefundedBudget_andFindsTheOneAJobKeeps() {
        var proven = verify(jobsNet(true, false), 2, 2, List.of(HALT));
        assertTrue(proven.isProven(), proven.report());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, proven.route());
        assertTrue(proven.report().contains(
            "Property: Quiescent count: exactly 2 across {budget}; lower bound waived while {halt} is marked\n"),
            proven.report());

        var kept = verify(jobsNet(false, false), 2, 2, List.of(HALT));
        assertTrue(kept.isViolated(), kept.report());
        assertTrue(kept.counterexampleTrace().getLast().tokens(BUDGET) < 2, kept.report());
    }

    @Test
    void enumeration_waivesTheLowerBoundWhileTheMarkerIsMarked_andOnlyThen() {
        var waived = verify(jobsNet(true, true), 2, 2, List.of(HALT));
        assertTrue(waived.isProven(), waived.report());
        var strict = verify(jobsNet(true, true), 2, 2, List.of());
        assertTrue(strict.isViolated(), strict.report());
        assertTrue(strict.counterexampleTrace().getLast().hasTokens(HALT), strict.report());
        // The upper bound is never waived.
        var atMostOne = verify(jobsNet(true, true), 0, 1, List.of(HALT));
        assertTrue(atMostOne.isViolated(), atMostOne.report());
    }

    // === The SMT route ===

    private static SmtVerificationResult verifyIc3(PetriNet net) {
        return SmtVerifier.forNet(net).initialMarking(m0())
            .property(count(List.of(BUDGET), 2, OptionalInt.of(2), List.of(HALT)))
            // The IC3/PDR path is under test; the phases of VER-018/019 would decide first.
            .stateEquationPhase(false).firingBound(false)
            .enumerationMaxClasses(0).timeout(Duration.ofSeconds(30)).verify();
    }

    @Test
    @EnabledIf("z3Available")
    void theStateEquationPhaseDecidesIt_proofAndWitness() {
        var proven = SmtVerifier.forNet(jobsNet(true, true)).initialMarking(m0())
            .property(count(List.of(BUDGET), 2, OptionalInt.of(2), List.of(HALT)))
            .enumerationMaxClasses(0).timeout(Duration.ofSeconds(30)).verify();
        assertTrue(proven.isProven(), proven.report());
        assertEquals("state-equation", ((SmtVerificationResult.Verdict.Proven) proven.verdict()).method(), proven.report());
        assertTrue(proven.report().contains("  Certificate check: PASSED (init, consecution, safety)"), proven.report());

        var kept = SmtVerifier.forNet(jobsNet(false, false)).initialMarking(m0())
            .property(count(List.of(BUDGET), 2, OptionalInt.of(2), List.of(HALT)))
            .enumerationMaxClasses(0).timeout(Duration.ofSeconds(30)).verify();
        assertTrue(kept.isViolated(), kept.report());
        assertEquals(Boolean.TRUE, kept.counterexampleConfirmed(), kept.report());
    }

    @Test
    @EnabledIf("z3Available")
    void ic3DecidesItToo_andItsCertificatePassesTheCheck() {
        var proven = verifyIc3(jobsNet(true, true));
        assertTrue(proven.isProven(), proven.report());
        assertEquals("IC3/PDR", ((SmtVerificationResult.Verdict.Proven) proven.verdict()).method(), proven.report());
        assertTrue(proven.report().contains("  Certificate check: PASSED (init, consecution, safety)"), proven.report());

        var kept = verifyIc3(jobsNet(false, false));
        assertTrue(kept.isViolated(), kept.report());
        assertEquals(Boolean.TRUE, kept.counterexampleConfirmed(), kept.report());
    }

    /**
     * A count or a waiver over a place the net does not declare is refused before any route:
     * a mistyped waiver would never be marked and would silently make the lower bound
     * unconditional.
     */
    @Test
    void refusesACountOrAWaiverOverAPlaceTheNetDoesNotDeclare() {
        var ghost = Place.of("ghost", String.class);
        var hlat = Place.of("hlat", String.class);
        for (var property : List.of(
                count(List.of(ghost), 1, OptionalInt.of(1), List.of()),
                count(List.of(BUDGET), 1, OptionalInt.of(1), List.of(hlat)))) {
            var r = SmtVerifier.forNet(jobsNet(true, false)).initialMarking(m0()).property(property)
                .timeout(Duration.ofSeconds(30)).verify();
            var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, r.verdict(), r.report());
            String named = property.places().contains(ghost) ? "'ghost'" : "'hlat'";
            assertTrue(unknown.reason().contains(named), unknown.reason());
        }
    }

    // === helpers ===

    private static FlatNet flat(PetriNet net) {
        return NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.alwaysAvailable());
    }

    /** The {@code Bad(M)} term of the script's error rule, without the Reachable guard. */
    private static String violationTerm(String smt2) {
        int error = smt2.indexOf(")\n      Error)))");
        assertTrue(error > 0, "the script carries an error rule");
        int reachable = smt2.lastIndexOf("(Reachable ", error);
        return smt2.substring(smt2.indexOf(") ", reachable) + 2, error);
    }
}
