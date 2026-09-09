package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.StateClassGraph;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.z3.CounterexampleDecoder;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [VER-017] bounded state-space enumeration, [VER-003] AC4 the deciding route,
 * [VER-006] AC6 vacuous quiescence, and the "a defect is never a verdict" discipline.
 *
 * <p>A pipeline {@code p0 -> t0 -> p1 -> ... -> pn}: the reachable state space is one class
 * per stage, but its <em>diameter</em> is the length, which is what makes the fixpoint
 * search expensive and enumeration trivial. Mirrors
 * {@code typescript/tests/verification/scg-verifier.test.ts}.
 */
class ScgVerifierTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private record Pipeline(PetriNet net, List<Place<String>> places, MarkingState m0) {}

    private static Pipeline pipeline(int n) {
        return pipeline(n, false);
    }

    private static Pipeline pipeline(int n, boolean timed) {
        var places = new ArrayList<Place<String>>();
        places.add(Place.of("p0", String.class));
        var transitions = new ArrayList<Transition>();
        for (int i = 0; i < n; i++) {
            var next = Place.of("p" + (i + 1), String.class);
            places.add(next);
            var b = Transition.builder("t" + i)
                .inputs(In.one(places.get(i)))
                .outputs(Out.place(next));
            transitions.add((timed ? b.timing(Timing.delayed(Duration.ofMillis(10))) : b).build());
        }
        var net = StructureOnly.bind(PetriNet.builder("pipeline" + n)
            .transitions(transitions.toArray(new Transition[0])).build());
        return new Pipeline(net, List.copyOf(places),
            MarkingState.builder().tokens(places.get(0), 1).build());
    }

    // === The route ===

    @Test
    void decidesDeadlockFreedomExactly_withNoSolverAtAll() {
        var p = pipeline(6);
        var result = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
            .property(SmtProperty.deadlockFree()).sinkPlaces(p.places().get(6))
            .timeout(Duration.ofSeconds(30)).verify();

        assertTrue(result.isProven(), result.report());
        assertEquals("state-space enumeration (VER-017)",
            ((SmtVerificationResult.Verdict.Proven) result.verdict()).method());
        assertTrue(result.report().contains("=== Bounded state-space enumeration (VER-017) ==="),
            result.report());
        assertTrue(result.report().contains("  State classes: 7"), result.report());
        // No solver phase ran at all.
        assertFalse(result.report().contains("Phase 4: IC3/PDR"), result.report());
        assertFalse(result.report().contains("Solver: z3"), result.report());
    }

    @Test
    void reportsAViolationWithARealFiringSequence() {
        // The token comes to rest in p6, which is NOT declared a sink: stranded.
        var p = pipeline(6);
        var result = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
            .property(SmtProperty.deadlockFree()).timeout(Duration.ofSeconds(30)).verify();

        assertTrue(result.isViolated(), result.report());
        assertEquals(List.of("t0", "t1", "t2", "t3", "t4", "t5"), result.counterexampleTransitions());
        assertEquals(1, result.counterexampleTrace().getLast().tokens(p.places().get(6)));
    }

    @Test
    void decidesReachabilitySafetyOverTheSameGraph() {
        var p = pipeline(4);
        var bound = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
            .property(SmtProperty.placeBound(p.places().get(4), 1))
            .timeout(Duration.ofSeconds(30)).verify();
        assertTrue(bound.isProven(), bound.report());

        var unreach = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
            .property(SmtProperty.unreachable(Set.of(p.places().get(0), p.places().get(4))))
            .timeout(Duration.ofSeconds(30)).verify();
        assertTrue(unreach.isProven(), unreach.report());
    }

    @Test
    @EnabledIf("z3Available")
    void declinesPastItsClassBudget_andSaysSo_leavingTheSmtPipelineToAnswer() {
        var p = pipeline(6);
        var result = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
            .property(SmtProperty.deadlockFree()).sinkPlaces(p.places().get(6))
            .enumerationMaxClasses(3) // the graph has 7 classes
            .timeout(Duration.ofSeconds(30)).verify();
        assertTrue(result.report().contains("Bounded state-space enumeration truncated at 3 classes"),
            result.report());
        assertTrue(result.report().contains("Phase 1: Flattening net..."), result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void enumerationMaxClassesZeroTurnsTheRouteOff() {
        var p = pipeline(4);
        var result = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
            .property(SmtProperty.deadlockFree()).sinkPlaces(p.places().get(4))
            .enumerationMaxClasses(0).timeout(Duration.ofSeconds(30)).verify();
        assertFalse(result.report().contains("Bounded state-space enumeration"), result.report());
        assertTrue(result.report().contains("Phase 1: Flattening net..."), result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void isSkippedOnATimedNet_whoseEnumerationWouldBeTheWeakerTimedClaim() {
        var timed = pipeline(4, true);
        assertFalse(ScgVerifier.isUntimed(timed.net()));
        assertTrue(ScgVerifier.isUntimed(pipeline(4).net()));

        var result = SmtVerifier.forNet(timed.net()).initialMarking(timed.m0())
            .property(SmtProperty.deadlockFree()).sinkPlaces(timed.places().get(4))
            .timeout(Duration.ofSeconds(30)).verify();
        assertFalse(result.report().contains("Bounded state-space enumeration"), result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void isSkippedWhenEnvironmentPlacesAreRegistered() {
        var in = EnvironmentPlace.of(Place.of("IN", String.class));
        var out = Place.of("OUT", String.class);
        var t = Transition.builder("T").inputs(In.one(in.place())).outputs(Out.place(out)).build();
        var net = StructureOnly.bind(PetriNet.builder("env").transitions(t).build());
        var result = SmtVerifier.forNet(net).initialMarking(MarkingState.empty())
            .property(SmtProperty.placeBound(out, 5))
            .environmentPlaces(in).environmentMode(EnvironmentAnalysisMode.alwaysAvailable())
            .timeout(Duration.ofSeconds(30)).verify();
        assertFalse(result.report().contains("Bounded state-space enumeration"), result.report());
    }

    @Test
    void isSkippedForANuNet_whichHasItsOwnExactRoute() {
        // [VER-017] AC5: a ν-net goes to Route B ([VER-012]), which subsumes this route.
        var source = Place.of("source", String.class);
        var a = Place.of("nuA", String.class);
        var b = Place.of("nuB", String.class);
        var merged = Place.of("merged", String.class);
        var fork = Transition.builder("fork").inputs(In.one(source))
            .outputs(Out.and(a, b)).build();
        var join = Transition.builder("join").inputs(In.one(a), In.one(b))
            .match(org.libpetri.core.MatchSpec.builder()
                .key(a, (String x) -> org.libpetri.core.NameId.of(x))
                .key(b, (String x) -> org.libpetri.core.NameId.of(x))
                .build())
            .outputs(Out.place(merged)).build();
        var net = StructureOnly.bind(PetriNet.builder("nu").transitions(fork, join).build());

        var result = SmtVerifier.forNet(net)
            .initialMarking(MarkingState.builder().tokens(source, 1).build())
            .property(SmtProperty.deadlockFree()).sinkPlaces(merged)
            .timeout(Duration.ofSeconds(30)).verify();
        assertFalse(result.report().contains("Bounded state-space enumeration"), result.report());
        assertEquals(SmtVerificationResult.Route.NU_SCG, result.route(), result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void isSkippedWhenThePropertyNamesAPlaceTheNetNeverDeclares() {
        // The graph decides the property over markings, and a place the net never declares
        // is simply always empty there — so `unreachable` (and every bound) would close the
        // graph and hand back a PROVEN that says nothing about the net. That is the vacuous
        // certification the unresolved-place refusal exists to prevent, and it has to be
        // reached before the route is picked, not only inside the encoder.
        var p = pipeline(3);
        var ghost = Place.of("ghost", String.class);

        var result = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
            .property(SmtProperty.unreachable(Set.of(ghost)))
            .timeout(Duration.ofSeconds(30)).verify();

        assertFalse(result.report().contains("Bounded state-space enumeration"), result.report());
        assertEquals(SmtVerificationResult.Route.UNAVAILABLE, result.route(), result.report());
        assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(), result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void stillRunsWhenTheNamedPlaceIsDeclaredOnlyByAResetArc() {
        // The guard above reads NetFlattener.declaredPlaces, not PetriNet.places(): the
        // builder auto-adds input, output, inhibitor and read places but NOT a reset arc's,
        // so net.places() alone would call a perfectly real place unresolved and send the
        // net down the SMT pipeline for nothing.
        var p0 = Place.of("p0", String.class);
        var p1 = Place.of("p1", String.class);
        var scratch = Place.of("scratch", String.class); // reached only through the reset arc
        var t = Transition.builder("t0").inputs(In.one(p0)).outputs(Out.place(p1))
            .reset(scratch).build();
        var net = StructureOnly.bind(PetriNet.builder("resetOnly").transitions(t).build());
        assertFalse(net.places().contains(scratch), "fixture premise: the builder omits reset places");
        assertTrue(NetFlattener.declaredPlaces(net).contains(scratch));

        var result = SmtVerifier.forNet(net)
            .initialMarking(MarkingState.builder().tokens(p0, 1).build())
            .property(SmtProperty.placeBound(scratch, 1))
            .timeout(Duration.ofSeconds(30)).verify();

        assertTrue(result.report().contains("Bounded state-space enumeration"), result.report());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, result.route(), result.report());
        assertTrue(result.isProven(), result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void namesTheDecidingRoute_andSaysInvariantsWereNotComputed() {
        // A consumer reading fields rather than the report must be able to tell why
        // `invariants` is empty: not computed on this route, rather than none exist.
        var p = pipeline(4);
        var enumerated = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
            .property(SmtProperty.deadlockFree()).sinkPlaces(p.places().get(4))
            .timeout(Duration.ofSeconds(30)).verify();
        assertEquals(SmtVerificationResult.Route.ENUMERATION, enumerated.route());
        assertEquals(List.of(), enumerated.invariants());
        assertTrue(enumerated.report()
            .contains("  P-invariants: not computed (no encoding is built on this route)"),
            enumerated.report());

        var solved = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
            .property(SmtProperty.deadlockFree()).sinkPlaces(p.places().get(4))
            .enumerationMaxClasses(0).timeout(Duration.ofSeconds(30)).verify();
        assertNotEquals(SmtVerificationResult.Route.ENUMERATION, solved.route());
    }

    @Test
    void anEnumerationCounterexampleIsOrdered_soItReportsAsConfirmed() {
        // The graph path is a firing sequence: nothing to replay, and a consumer keying
        // "are these steps ordered" off the field gets the right answer.
        var p = pipeline(4);
        var result = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
            .property(SmtProperty.deadlockFree()).timeout(Duration.ofSeconds(30)).verify();
        assertTrue(result.isViolated(), result.report());
        assertEquals(Boolean.TRUE, result.counterexampleConfirmed());
        assertEquals(List.of("t0", "t1", "t2", "t3"), result.counterexampleTransitions());
    }

    @Test
    void theRouteFunctionItselfReportsTruncationRatherThanAVerdict() {
        var p = pipeline(6);
        var truncated = ScgVerifier.verify(
            p.net(), p.m0(), SmtProperty.deadlockFree(), Set.of(p.places().get(6)), 3, List.of());
        assertInstanceOf(ScgVerifier.Outcome.Truncated.class, truncated);
        var decided = ScgVerifier.verify(
            p.net(), p.m0(), SmtProperty.deadlockFree(), Set.of(p.places().get(6)), 1000, List.of());
        assertInstanceOf(ScgVerifier.Outcome.Decided.class, decided);
        assertInstanceOf(SmtVerificationResult.Verdict.Proven.class,
            ((ScgVerifier.Outcome.Decided) decided).verdict());
    }

    @Test
    @EnabledIf("z3Available")
    void bothRoutesReturnTheSameVerdictOnTheSameNet() {
        var p = pipeline(5);
        record Case(SmtProperty property, List<Place<String>> sinks) {}
        var cases = List.of(
            new Case(SmtProperty.deadlockFree(), List.of(p.places().get(5))),
            new Case(SmtProperty.placeBound(p.places().get(5), 1), List.of()));
        for (var c : cases) {
            var enumerated = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
                .property(c.property()).sinkPlaces(c.sinks().toArray(new Place<?>[0]))
                .timeout(Duration.ofSeconds(30)).verify();
            var solved = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
                .property(c.property()).sinkPlaces(c.sinks().toArray(new Place<?>[0]))
                .enumerationMaxClasses(0).timeout(Duration.ofSeconds(30)).verify();
            assertTrue(enumerated.report().contains("Bounded state-space enumeration"),
                enumerated.report());
            assertFalse(solved.report().contains("Bounded state-space enumeration"), solved.report());
            assertEquals(solved.verdict().getClass(), enumerated.verdict().getClass(),
                enumerated.report() + "\n---\n" + solved.report());
        }
    }

    // === [VER-006] AC6: an open net never comes to rest ===

    private static PetriNet openNet(EnvironmentPlace<String> src, Place<String> in, Place<String> done) {
        var trigger = Transition.builder("trigger").inputs(In.one(src.place()))
            .outputs(Out.place(in)).build();
        var step = Transition.builder("step").inputs(In.one(in)).outputs(Out.place(done)).build();
        return StructureOnly.bind(PetriNet.builder("open").transitions(trigger, step).build());
    }

    @Test
    @EnabledIf("z3Available")
    void warnsThatAQuiescencePropertyIsVacuous_whenNothingCanEverBeQuiescent() {
        var src = EnvironmentPlace.of(Place.of("src", String.class));
        var in = Place.of("in", String.class);
        var done = Place.of("done", String.class);
        var result = SmtVerifier.forNet(openNet(src, in, done)).initialMarking(MarkingState.empty())
            .property(SmtProperty.deadlockFree()).sinkPlaces(done)
            .environmentPlaces(src).environmentMode(EnvironmentAnalysisMode.alwaysAvailable())
            .enumerationMaxClasses(0).timeout(Duration.ofSeconds(30)).verify();

        // True, but only because the trigger is always enabled — never a deadlock.
        assertTrue(result.isProven(), result.report());
        assertTrue(result.report().contains("NOTE: no marking of this net can be quiescent"),
            result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void saysNothingOfTheKindForAClosedNet_whoseQuiescenceIsReal() {
        var p = pipeline(3);
        // enumerationMaxClasses(0) so the SMT pipeline (which prints the note) actually
        // runs: the enumeration route would otherwise answer first and print no phases.
        var result = SmtVerifier.forNet(p.net()).initialMarking(p.m0())
            .property(SmtProperty.deadlockFree()).sinkPlaces(p.places().get(3))
            .enumerationMaxClasses(0).timeout(Duration.ofSeconds(30)).verify();
        assertFalse(result.report().contains("no marking of this net can be quiescent"),
            result.report());
    }

    // === Programming errors are never verdicts ===

    @Test
    void reThrowsADefect_andPassesEverythingElseThrough() {
        assertThrows(NullPointerException.class,
            () -> ProgrammingError.rethrowIfProgrammingError(new NullPointerException("null place")));
        assertThrows(ClassCastException.class,
            () -> ProgrammingError.rethrowIfProgrammingError(new ClassCastException("not a Place")));
        assertThrows(IndexOutOfBoundsException.class,
            () -> ProgrammingError.rethrowIfProgrammingError(new IndexOutOfBoundsException(7)));
        // A deep net overflowing the stack IS the capacity limit `Unknown` reports.
        assertDoesNotThrow(() -> ProgrammingError.rethrowIfProgrammingError(new StackOverflowError()));
        // The conditions the catches were written for pass through untouched.
        assertDoesNotThrow(
            () -> ProgrammingError.rethrowIfProgrammingError(new IllegalStateException("z3 exited 1")));
        assertDoesNotThrow(
            () -> ProgrammingError.rethrowIfProgrammingError(new ArithmeticException("long overflow")));
    }

    @Test
    void aReplayerDefectSurfacesInsteadOfReadingAsAnExhaustedSearch() {
        // assessCounterexample catches to keep a replayer fault from crashing the verifier;
        // a defect there must still reach the caller.
        var p = pipeline(2);
        FlatNet flat = NetFlattener.flatten(
            p.net(), Set.of(), EnvironmentAnalysisMode.alwaysAvailable());
        var states = new java.util.HashSet<MarkingState>();
        states.add(p.m0());
        var decoded = new CounterexampleDecoder.DecodedStates(states, null);
        assertThrows(NullPointerException.class, () -> SmtVerifier.assessCounterexample(
            flat, null, decoded, SmtProperty.deadlockFree(), Set.of()));
    }

    // === Reset arcs in the enumeration route ([VER-010] AC2) ===

    // A reset arc on a place the same transition also consumes: both executors run this,
    // so the enumeration route must too. It used to clear the PRE-firing count after the
    // inputs had already drawn, overdrawing and throwing.

    private record ResetAndInput(PetriNet net, Place<Integer> p, Place<Integer> q) {}

    private static ResetAndInput resetAndInput(java.util.function.Function<Place<Integer>, In> inputSpec) {
        var p = Place.of("p", Integer.class);
        var q = Place.of("q", Integer.class);
        var t = Transition.builder("t")
            .inputs(inputSpec.apply(p))
            .resets(p)
            .outputs(Out.place(q))
            .build();
        return new ResetAndInput(
            StructureOnly.bind(PetriNet.builder("reset-input").transitions(t).build()), p, q);
    }

    @Test
    void decidesANetWhoseTransitionConsumesAndResetsTheSamePlace_one() {
        var f = resetAndInput(In::one);
        var result = SmtVerifier.forNet(f.net())
            .initialMarking(MarkingState.builder().tokens(f.p(), 3).build())
            .property(SmtProperty.placeBound(f.q(), 5))
            .timeout(Duration.ofSeconds(30)).verify();
        assertTrue(result.isProven(), result.report());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, result.route(), result.report());
    }

    @Test
    void decidesANetWhoseTransitionConsumesAndResetsTheSamePlace_all() {
        var f = resetAndInput(In::all);
        var result = SmtVerifier.forNet(f.net())
            .initialMarking(MarkingState.builder().tokens(f.p(), 3).build())
            .property(SmtProperty.placeBound(f.q(), 5))
            .timeout(Duration.ofSeconds(30)).verify();
        assertTrue(result.isProven(), result.report());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, result.route(), result.report());
    }

    @Test
    void drainsThePlaceExactlyAsTheExecutorsDo_theTransitionFiresOnce() {
        var f = resetAndInput(In::one);
        var graph = StateClassGraph.build(
            f.net(), MarkingState.builder().tokens(f.p(), 3).build(), 1000);
        // p goes 3 -> 0 (the input takes one, the reset clears the rest), q gets exactly 1,
        // and t cannot re-enable on a residue.
        var counts = graph.stateClasses().stream()
            .map(sc -> sc.marking().tokens(f.p()))
            .distinct().sorted().toList();
        assertEquals(List.of(0, 3), counts, counts.toString());
        assertTrue(graph.stateClasses().stream().allMatch(sc -> sc.marking().tokens(f.q()) <= 1));
    }

    // === The structural shortcut refuses nets it does not govern ===

    // Commoner's theorem governs ORDINARY nets. The siphon/trap fixpoints read only the
    // pre/post vectors, so on a net with a read, inhibitor or reset arc, or an arc weight
    // above one, they answer about a strictly more permissive net — and turning that answer
    // into PROVEN is a false proof. Each net below is genuinely dead at its initial
    // marking; both executors confirm it. `enumerationMaxClasses(0)` is what makes the
    // structural gate the route under test.

    private static SmtVerificationResult runDeadlockFree(PetriNet net, MarkingState m0) {
        return SmtVerifier.forNet(net).initialMarking(m0)
            .property(SmtProperty.deadlockFree())
            .enumerationMaxClasses(0)
            .timeout(Duration.ofSeconds(30)).verify();
    }

    private static void assertNotProvenStructurally(SmtVerificationResult result) {
        boolean structural = result.verdict() instanceof SmtVerificationResult.Verdict.Proven proven
            && "structural".equals(proven.method());
        assertFalse(structural,
            "a dead net was proven deadlock-free structurally:\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void aReadArc_theGateUsedToProveANetThatCannotFireAtAll() {
        // t1 needs a token in g to fire, and only t2 can put one there, but t2 needs g too.
        var a = Place.of("a", Integer.class);
        var g = Place.of("g", Integer.class);
        var t1 = Transition.builder("t1").inputs(In.one(a)).reads(g).outputs(Out.place(g)).build();
        var t2 = Transition.builder("t2").inputs(In.one(g)).outputs(Out.place(a)).build();
        var net = StructureOnly.bind(
            PetriNet.builder("read-gate").transitions(t1, t2).build());
        assertNotProvenStructurally(
            runDeadlockFree(net, MarkingState.builder().tokens(a, 1).build()));
    }

    @Test
    @EnabledIf("z3Available")
    void anArcWeightAboveOne() {
        var a = Place.of("a", Integer.class);
        var t = Transition.builder("t").inputs(In.exactly(2, a)).outputs(Out.place(a)).build();
        var net = StructureOnly.bind(PetriNet.builder("weighted").transitions(t).build());
        assertNotProvenStructurally(
            runDeadlockFree(net, MarkingState.builder().tokens(a, 1).build()));
    }

    @Test
    @EnabledIf("z3Available")
    void anInhibitorArc() {
        var a = Place.of("a", Integer.class);
        var b = Place.of("b", Integer.class);
        var t = Transition.builder("t").inputs(In.one(a)).inhibitors(b).outputs(Out.place(a)).build();
        var net = StructureOnly.bind(PetriNet.builder("inhibited").transitions(t).build());
        // b holds the inhibiting token, so t is disabled from the start: the net is dead.
        assertNotProvenStructurally(
            runDeadlockFree(net, MarkingState.builder().tokens(a, 1).tokens(b, 1).build()));
    }

    @Test
    void stillTakesTheShortcutOnAnOrdinaryNet_whereTheTheoremDoesHold() {
        // A token circulating a ring: every siphon holds a marked trap, and nothing about
        // the net is outside what the fixpoints model.
        var a = Place.of("a", Integer.class);
        var b = Place.of("b", Integer.class);
        var t1 = Transition.builder("t1").inputs(In.one(a)).outputs(Out.place(b)).build();
        var t2 = Transition.builder("t2").inputs(In.one(b)).outputs(Out.place(a)).build();
        var net = StructureOnly.bind(PetriNet.builder("ring").transitions(t1, t2).build());
        var result = runDeadlockFree(net, MarkingState.builder().tokens(a, 1).build());
        assertTrue(result.isProven(), result.report());
        assertEquals(SmtVerificationResult.Route.STRUCTURAL, result.route(), result.report());
        assertEquals("structural",
            ((SmtVerificationResult.Verdict.Proven) result.verdict()).method(), result.report());
    }
}
