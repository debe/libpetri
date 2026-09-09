package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.PrioritySemantics;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.fixtures.VerificationNets;
import org.libpetri.smt.z3.AbstractReplayer;
import org.libpetri.smt.z3.SmtEncoder;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.time.Duration;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [VER-014] conditional sinks: a token may rest in a place while a marker is marked.
 *
 * <p>The net: {@code p0(1) → t → AND(a, b); a → ta → done | halt; b → tb → done} unless
 * {@code halt} is marked. Reachable quiescent markings: {@code {done:2}},
 * {@code {halt:1, done:1}}, {@code {halt:1, b:1}}. The last one is the designed terminal
 * that a plain sink declaration cannot excuse: {@code b} holds pending work the halt
 * legitimately stopped. Mirrors {@code typescript/tests/verification/conditional-sinks.test.ts}.
 */
class ConditionalSinksTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<String> P0 = Place.of("p0", String.class);
    private static final Place<String> A = Place.of("a", String.class);
    private static final Place<String> B = Place.of("b", String.class);
    private static final Place<String> DONE = Place.of("done", String.class);
    private static final Place<String> HALT = Place.of("halt", String.class);
    private static final Place<String> GHOST = Place.of("ghost", String.class);

    private static PetriNet haltNet() {
        var t = Transition.builder("t").inputs(In.one(P0)).outputs(Out.and(A, B)).build();
        var ta = Transition.builder("ta").inputs(In.one(A)).outputs(Out.xor(DONE, HALT)).build();
        var tb = Transition.builder("tb").inputs(In.one(B)).inhibitors(HALT).outputs(Out.place(DONE)).build();
        return StructureOnly.bind(PetriNet.builder("haltNet").transitions(t, ta, tb).build());
    }

    private static MarkingState m0() {
        return MarkingState.builder().tokens(P0, 1).build();
    }

    private static FlatNet flat(PetriNet net) {
        return NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.alwaysAvailable());
    }

    private static RestSet.ConditionalSinks when(Place<?> marker, Place<?>... places) {
        return new RestSet.ConditionalSinks(marker, new LinkedHashSet<>(List.of(places)));
    }

    private static Set<Place<?>> sinks(Place<?>... places) {
        return new LinkedHashSet<>(List.of(places));
    }

    private static MarkingState marking(Object... placeCounts) {
        var b = MarkingState.builder();
        for (int i = 0; i < placeCounts.length; i += 2) {
            b.tokens((Place<?>) placeCounts[i], (Integer) placeCounts[i + 1]);
        }
        return b.build();
    }

    // === Rest set ===

    @Test
    void strandingExcuses_sinksAndMarkersNeverStrand_conditionalPlacesNameTheirMarkers() {
        var flat = flat(haltNet());
        int[][] ex = RestSet.strandingExcuses(flat, sinks(DONE), List.of(when(HALT, B)));
        assertNull(ex[flat.indexOf(DONE)]);
        assertNull(ex[flat.indexOf(HALT)]);
        assertArrayEquals(new int[] {flat.indexOf(HALT)}, ex[flat.indexOf(B)]);
        assertArrayEquals(new int[0], ex[flat.indexOf(A)]);
        assertArrayEquals(new int[0], ex[flat.indexOf(P0)]);
    }

    @Test
    void strandingExcuses_twoMarkersExcusingOnePlace_listedInPlaceIndexOrderOnceEach() {
        var flat = flat(haltNet());
        int[][] ex = RestSet.strandingExcuses(flat, Set.of(),
            List.of(when(HALT, B), when(DONE, B), when(HALT, B)));
        int[] expected = {flat.indexOf(DONE), flat.indexOf(HALT)};
        java.util.Arrays.sort(expected);
        assertArrayEquals(expected, ex[flat.indexOf(B)]);
    }

    @Test
    void strandingExcuses_unresolvedMarkerOrPlaceContributesNothing() {
        var flat = flat(haltNet());
        int[][] ex = RestSet.strandingExcuses(flat, sinks(GHOST), List.of(when(GHOST, B, GHOST)));
        assertArrayEquals(new int[0], ex[flat.indexOf(B)]);
    }

    @Test
    void strandsToken_markerExcusesItsPlacesOnlyWhileMarked() {
        var cond = List.of(when(HALT, B));
        var s = sinks(DONE);
        assertFalse(RestSet.strandsToken(marking(HALT, 1, B, 1), s, cond));
        assertTrue(RestSet.strandsToken(marking(B, 1), s, cond));
        assertTrue(RestSet.strandsToken(marking(HALT, 1, A, 1), s, cond));
        assertFalse(RestSet.strandsToken(marking(HALT, 1), s, cond));
        assertFalse(RestSet.strandsToken(marking(DONE, 2), s, cond));
        assertFalse(RestSet.strandsToken(MarkingState.empty(), s, cond));
    }

    @Test
    void describeSinks_rendersDeclarationsInOrder() {
        var h = Place.of("h", String.class);
        var p = Place.of("p", String.class);
        assertNull(RestSet.describeSinks(Set.of(), List.of()));
        assertEquals("sinks: a, b", RestSet.describeSinks(sinks(A, B), List.of()));
        assertEquals("sinks: a; when h: b; when p",
            RestSet.describeSinks(sinks(A), List.of(when(h, B), when(p))));
        assertEquals("when h: a, b", RestSet.describeSinks(Set.of(), List.of(when(h, A, B))));
    }

    // === Encoder and replay agree ===

    @Test
    void flatEncoder_conjoinsTheMarkerBeingUnmarkedIntoTheStrandedDisjunct() {
        var flat = flat(haltNet());
        String b = "m" + flat.indexOf(B);
        String halt = "m" + flat.indexOf(HALT);
        String done = "m" + flat.indexOf(DONE);
        String bad = SmtEncoder.encode(flat, m0(), SmtProperty.deadlockFree(), List.of(), sinks(DONE),
            false, List.of(when(HALT, B)), false).smt2();
        assertTrue(bad.contains("(and (>= " + b + " 1) (= " + halt + " 0))"), bad);
        assertFalse(bad.contains("(>= " + done + " 1)"), bad);
        assertFalse(bad.contains("(>= " + halt + " 1)"), bad);
        // Without the declaration the same place is an unconditional disjunct.
        String plain = SmtEncoder.encode(flat, m0(), SmtProperty.deadlockFree(), List.of(), sinks(DONE), false).smt2();
        assertTrue(plain.contains("(>= " + b + " 1)"), plain);
        assertTrue(plain.contains("(>= " + halt + " 1)"), plain);
    }

    @Test
    void encodeWithoutConditionalSinks_isByteIdenticalToBefore() {
        var flat = flat(haltNet());
        var before = SmtEncoder.encode(flat, m0(), SmtProperty.deadlockFree(), List.of(), sinks(DONE), false);
        var after = SmtEncoder.encode(flat, m0(), SmtProperty.deadlockFree(), List.of(), sinks(DONE), false,
            List.of(), false);
        assertEquals(before.smt2(), after.smt2());
    }

    @Test
    void replayer_readsTheSamePredicateTheEncoderEmits() {
        var flat = flat(haltNet());
        var cond = List.of(when(HALT, B));
        int[] haltedWithB = AbstractReplayer.toVector(flat, marking(HALT, 1, B, 1));
        int[] haltedWithA = AbstractReplayer.toVector(flat, marking(HALT, 1, A, 1));
        // {halt:1, b:1} is quiescent (tb is inhibited): stranded without the excuse, at rest with it.
        assertTrue(AbstractReplayer.violates(flat, SmtProperty.deadlockFree(), sinks(DONE), haltedWithB));
        assertFalse(AbstractReplayer.violates(flat, SmtProperty.deadlockFree(), sinks(DONE), cond, haltedWithB));
        // {halt:1, a:1} is not quiescent (ta can fire), so never a violation.
        assertFalse(AbstractReplayer.violates(flat, SmtProperty.deadlockFree(), sinks(DONE), cond, haltedWithA));
        // TerminatesAtSink ignores the conditional declaration.
        assertTrue(AbstractReplayer.violates(flat, SmtProperty.terminatesAtSink(), sinks(DONE), cond, haltedWithB));
    }

    @Test
    void routeB_decidesTheSamePredicateOnANuNet() {
        // nuMixedTerminal quiesces at {done:1, stuck:1}: violated with `done` a plain sink,
        // proven once `stuck` may rest while `done` is marked.
        var built = VerificationNets.nuMixedTerminal();
        var stuck = Place.of("stuck", String.class);
        java.util.function.Function<List<RestSet.ConditionalSinks>, NuScgVerifier.Outcome> run = cond ->
            NuScgVerifier.verify(built.net(), built.initialMarking(), SmtProperty.deadlockFree(), sinks(DONE),
                Set.of(), built.environmentMode(), 10_000, FragmentMode.BASE, Set.of(),
                PrioritySemantics.NONE, cond);
        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, run.apply(List.of()).verdict());
        assertInstanceOf(SmtVerificationResult.Verdict.Proven.class, run.apply(List.of(when(DONE, stuck))).verdict());
    }

    // === End to end ===

    private static SmtVerifier base(PetriNet net) {
        return SmtVerifier.forNet(net).initialMarking(m0()).property(SmtProperty.deadlockFree())
            // Explicit opt-out, not an oversight: [VER-017]'s enumeration route closes these
            // small untimed nets and would decide them with no solver at all, leaving the
            // conditional-sink encoder and replay paths these tests pin unexercised.
            .enumerationMaxClasses(0)
            .sinkPlaces(DONE).timeout(Duration.ofSeconds(30));
    }

    @Test
    @EnabledIf("z3Available")
    void aHaltThatStrandsPendingWork_isAViolationUntilTheWorkIsExcusedUnderTheHalt() {
        var net = haltNet();

        var plain = base(net).verify();
        assertTrue(plain.isViolated(), plain.report());
        assertEquals(Boolean.TRUE, plain.counterexampleConfirmed(), plain.report());
        assertEquals(1, plain.counterexampleTrace().getLast().tokens(HALT), plain.report());

        // The marker alone: halt is at rest, b is still stranded under it.
        var markerOnly = base(net).sinkPlacesWhen(HALT).verify();
        assertTrue(markerOnly.isViolated(), markerOnly.report());
        assertEquals(1, markerOnly.counterexampleTrace().getLast().tokens(B), markerOnly.report());

        // b may rest while halted: nothing is stranded in any quiescent marking.
        var excused = base(net).sinkPlacesWhen(HALT, B).verify();
        assertTrue(excused.isProven(), excused.report());
        assertTrue(excused.report().contains("Property: Deadlock-freedom (sinks: done; when halt: b)"),
            excused.report());

        // TerminatesAtSink reads only the unconditional sinks: {halt:1, b:1} marks none.
        var reaches = base(net).property(SmtProperty.terminatesAtSink()).sinkPlacesWhen(HALT, B).verify();
        assertTrue(reaches.isViolated(), reaches.report());
    }

    @Test
    @EnabledIf("z3Available")
    void aMarkerThatIsNotMarkedAtQuiescence_excusesNothing() {
        var built = VerificationNets.deadEndChain();
        var p0 = Place.of("p0", String.class);
        var p2 = Place.of("p2", String.class);
        java.util.function.Supplier<SmtVerifier> chain = () -> SmtVerifier.forNet(built.net())
            .initialMarking(built.initialMarking()).property(SmtProperty.deadlockFree())
            // Explicit opt-out, not an oversight: [VER-017]'s enumeration route closes this
            // small untimed net and would decide it with no solver at all, leaving the
            // conditional-sink encoder and replay paths this test pins unexercised.
            .enumerationMaxClasses(0)
            .timeout(Duration.ofSeconds(30));
        // p0 is empty by the time the chain quiesces at {p2:1}.
        var unmarked = chain.get().sinkPlacesWhen(p0, p2).verify();
        assertTrue(unmarked.isViolated(), unmarked.report());
        // p2 as its own marker: the resting token is the designed terminal.
        var marker = chain.get().sinkPlacesWhen(p2).verify();
        assertTrue(marker.isProven(), marker.report());
        assertTrue(marker.report().contains("Property: Deadlock-freedom (when p2)"), marker.report());
    }
}
