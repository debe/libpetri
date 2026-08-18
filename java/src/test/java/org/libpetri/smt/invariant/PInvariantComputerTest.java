package org.libpetri.smt.invariant;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.fixtures.PaperNetworks;
import org.libpetri.smt.encoding.IncidenceMatrix;
import org.libpetri.smt.encoding.NetFlattener;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

class PInvariantComputerTest {

    @Test
    void circularNet_findsConservationInvariant() {
        // A -> B -> A (token-conserving circular net)
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);

        var t1 = Transition.builder("Forward")
            .inputs(In.one(pA))
            .outputs(Out.place(pB))
            .build();
        var t2 = Transition.builder("Back")
            .inputs(In.one(pB))
            .outputs(Out.place(pA))
            .build();

        var net = PetriNet.builder("Circular").transitions(t1, t2).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);

        var marking = MarkingState.builder().tokens(pA, 1).build();
        var invariants = PInvariantComputer.compute(matrix, flatNet, marking);

        assertFalse(invariants.isEmpty(), "Should find at least one P-invariant");

        // The invariant should be A + B = 1 (or proportional)
        var inv = invariants.getFirst();
        int idxA = flatNet.indexOf(pA);
        int idxB = flatNet.indexOf(pB);

        assertEquals(inv.weights()[idxA], inv.weights()[idxB],
            "Weights should be equal for circular net");
        assertEquals(1, inv.constant(), "Constant should be 1 (initial A=1, B=0)");
    }

    @Test
    void pipelineNet_findsInvariant() {
        // A -> B -> C (simple pipeline)
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);
        var pC = Place.of("C", String.class);

        var t1 = Transition.builder("T1")
            .inputs(In.one(pA))
            .outputs(Out.place(pB))
            .build();
        var t2 = Transition.builder("T2")
            .inputs(In.one(pB))
            .outputs(Out.place(pC))
            .build();

        var net = PetriNet.builder("Pipeline").transitions(t1, t2).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);

        var marking = MarkingState.builder().tokens(pA, 2).build();
        var invariants = PInvariantComputer.compute(matrix, flatNet, marking);

        // A + B + C = 2 (conservation law)
        assertFalse(invariants.isEmpty(), "Pipeline should have a conservation invariant");
        var inv = invariants.getFirst();
        assertEquals(2, inv.constant(), "Total tokens should be 2");
    }

    @Test
    void isCoveredByInvariants_trueForConservingNet() {
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);

        var t1 = Transition.builder("T1").inputs(In.one(pA)).outputs(Out.place(pB)).build();
        var t2 = Transition.builder("T2").inputs(In.one(pB)).outputs(Out.place(pA)).build();

        var net = PetriNet.builder("Circular").transitions(t1, t2).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);

        var marking = MarkingState.builder().tokens(pA, 1).build();
        var invariants = PInvariantComputer.compute(matrix, flatNet, marking);

        assertTrue(PInvariantComputer.isCoveredByInvariants(invariants, flatNet.placeCount()),
            "All places in circular net should be covered by invariants");
    }

    @Test
    void emptyNet_noInvariants() {
        var p = Place.of("A", String.class);
        var net = PetriNet.builder("Empty").places(p).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);

        var invariants = PInvariantComputer.compute(matrix, flatNet, MarkingState.empty());
        // Net with no transitions — PInvariantComputer short-circuits (T==0),
        // returning empty list. All places are trivially bounded but the
        // Farkas algorithm has no columns to eliminate.
        assertTrue(invariants.isEmpty(), "No transitions means no P-invariants computed");
    }

    // === Exact re-validation (validateExact) ===

    @Test
    void validateExact_dropsFabricatedNonInvariant() {
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);
        var t1 = Transition.builder("T1").inputs(In.one(pA)).outputs(Out.place(pB)).build();
        var net = PetriNet.builder("Pipeline").transitions(t1).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);
        var marking = MarkingState.builder().tokens(pA, 1).build();

        int idxA = flatNet.indexOf(pA);
        int[] weights = new int[flatNet.placeCount()];
        weights[idxA] = 1;
        // Not an invariant: y*C = -1 at T1 (A consumed without a balancing weight on B),
        // though the constant y*M0 = 1 is correct.
        var bogus = new PInvariant(weights, 1, Set.of(idxA));

        var validation = PInvariantComputer.validateExact(List.of(bogus), matrix, flatNet, marking);

        assertTrue(validation.valid().isEmpty(), "Fabricated non-invariant must be dropped");
        assertEquals(1, validation.dropped().size());
        var reason = validation.dropped().getFirst();
        assertTrue(reason.contains("y*C"), "Reason should name the failing check: " + reason);
        assertTrue(reason.contains("T1"), "Reason should name the transition column: " + reason);
    }

    @Test
    void validateExact_dropsCandidateOnLongOverflow() {
        var p1 = Place.of("P1", String.class);
        var p2 = Place.of("P2", String.class);
        var p3 = Place.of("P3", String.class);
        var sink = Place.of("Sink", String.class);
        var t = Transition.builder("Huge")
            .inputs(In.exactly(Integer.MAX_VALUE, p1),
                    In.exactly(Integer.MAX_VALUE, p2),
                    In.exactly(Integer.MAX_VALUE, p3))
            .outputs(Out.place(sink))
            .build();
        var net = PetriNet.builder("Overflow").transitions(t).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);

        int[] weights = new int[flatNet.placeCount()];
        weights[flatNet.indexOf(p1)] = Integer.MAX_VALUE;
        weights[flatNet.indexOf(p2)] = Integer.MAX_VALUE;
        weights[flatNet.indexOf(p3)] = Integer.MAX_VALUE;
        // Each product -(2^31-1)^2 fits a long, but the third addExact in the running
        // y*C sum exceeds Long.MIN_VALUE and throws.
        var huge = new PInvariant(weights, 0,
            Set.of(flatNet.indexOf(p1), flatNet.indexOf(p2), flatNet.indexOf(p3)));

        var validation = PInvariantComputer.validateExact(
            List.of(huge), matrix, flatNet, MarkingState.empty());

        assertTrue(validation.valid().isEmpty(), "Overflowing candidate must be dropped");
        assertEquals(1, validation.dropped().size());
        // ONE overflow reason for the whole pipeline, at extraction and at the exact
        // recheck alike, naming the place whose term could not be recomputed — the
        // recheck must not invent a wording no sibling implementation has.
        assertTrue(validation.dropped().getFirst().contains(
            "weight overflow at place 'P3' "
            + "(exact value outside this implementation's integer extraction range)"),
            "Reason should be the canonical overflow wording: " + validation.dropped().getFirst());
    }

    @Test
    void validateExact_dropsCandidateOnConstantOverflow_sameCanonicalReason() {
        // The y*C recheck passes (single transition, weights balanced), so the drop
        // happens in the y*M0 recompute — which must report the same canonical
        // wording, not a stage-specific one.
        var p1 = Place.of("P1", String.class);
        var p2 = Place.of("P2", String.class);
        var p3 = Place.of("P3", String.class);
        var t1 = Transition.builder("T1").inputs(In.one(p1)).outputs(Out.place(p2)).build();
        var t2 = Transition.builder("T2").inputs(In.one(p2)).outputs(Out.place(p3)).build();
        var net = PetriNet.builder("ConstantOverflow").transitions(t1, t2).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);
        // y = (MAX, MAX, MAX) is a genuine conservation law of P1 -> P2 -> P3
        // (y*C = 0 on both columns), but three MAX*MAX terms overflow the long y*M0.
        int[] weights = new int[flatNet.placeCount()];
        weights[flatNet.indexOf(p1)] = Integer.MAX_VALUE;
        weights[flatNet.indexOf(p2)] = Integer.MAX_VALUE;
        weights[flatNet.indexOf(p3)] = Integer.MAX_VALUE;
        var marking = MarkingState.builder()
            .tokens(p1, Integer.MAX_VALUE).tokens(p2, Integer.MAX_VALUE)
            .tokens(p3, Integer.MAX_VALUE).build();
        var candidate = new PInvariant(weights, 0,
            Set.of(flatNet.indexOf(p1), flatNet.indexOf(p2), flatNet.indexOf(p3)));

        var validation = PInvariantComputer.validateExact(
            List.of(candidate), matrix, flatNet, marking);

        assertTrue(validation.valid().isEmpty(), "Overflowing candidate must be dropped");
        assertEquals(1, validation.dropped().size());
        assertTrue(validation.dropped().getFirst().contains(
            "weight overflow at place '"),
            "Reason should be the canonical overflow wording: " + validation.dropped().getFirst());
        assertTrue(validation.dropped().getFirst().contains(
            "(exact value outside this implementation's integer extraction range)"),
            validation.dropped().getFirst());
    }

    @Test
    void validateExact_dropReasonUsesAnAsciiHyphenSeparator() {
        // The rendered report line is "<description> - <reason>" with an ASCII
        // hyphen-minus. An em dash here would break the byte-for-byte diff against
        // the TypeScript, Rust and Python reports.
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);
        var t1 = Transition.builder("T1").inputs(In.one(pA)).outputs(Out.place(pB)).build();
        var t2 = Transition.builder("T2").inputs(In.one(pB)).outputs(Out.place(pA)).build();
        var net = PetriNet.builder("Circular").transitions(t1, t2).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);
        var marking = MarkingState.builder().tokens(pA, 1).build();
        int[] weights = new int[flatNet.placeCount()];
        weights[flatNet.indexOf(pA)] = 1;
        weights[flatNet.indexOf(pB)] = 1;
        var wrongConstant = new PInvariant(weights, 2,
            Set.of(flatNet.indexOf(pA), flatNet.indexOf(pB)));

        var dropped = PInvariantComputer.validateExact(
            List.of(wrongConstant), matrix, flatNet, marking).dropped().getFirst();

        assertEquals(
            PInvariantComputer.describe(wrongConstant, flatNet)
            + " - constant 2 does not match exact y*M0 = 1",
            dropped);
        assertFalse(dropped.contains("\u2014"), "no em dash in a canonical report line: " + dropped);
    }

    @Test
    void validateExact_dropsConstantMismatch() {
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);
        var t1 = Transition.builder("T1").inputs(In.one(pA)).outputs(Out.place(pB)).build();
        var t2 = Transition.builder("T2").inputs(In.one(pB)).outputs(Out.place(pA)).build();
        var net = PetriNet.builder("Circular").transitions(t1, t2).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);
        var marking = MarkingState.builder().tokens(pA, 1).build();

        int idxA = flatNet.indexOf(pA);
        int idxB = flatNet.indexOf(pB);
        int[] weights = new int[flatNet.placeCount()];
        weights[idxA] = 1;
        weights[idxB] = 1;
        // y*C = 0 holds, but the exact y*M0 is 1, not 2.
        var wrongConstant = new PInvariant(weights, 2, Set.of(idxA, idxB));

        var validation = PInvariantComputer.validateExact(
            List.of(wrongConstant), matrix, flatNet, marking);

        assertTrue(validation.valid().isEmpty(), "Wrong-constant candidate must be dropped");
        assertEquals(1, validation.dropped().size());
        assertTrue(validation.dropped().getFirst().contains("constant"),
            "Reason should name the constant mismatch: " + validation.dropped().getFirst());
    }

    @Test
    void validateExact_keepsGenuineInvariantsUnchanged() {
        var net = PaperNetworks.createExtendedTpn();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);
        var marking = MarkingState.builder()
            .tokens(Place.of("Pending", String.class), 1).build();

        var invariants = PInvariantComputer.compute(matrix, flatNet, marking);
        assertFalse(invariants.isEmpty(), "Fixture should yield invariants");
        var validation = PInvariantComputer.validateExact(invariants, matrix, flatNet, marking);
        assertEquals(invariants, validation.valid(), "Genuine invariants must pass unchanged");
        assertTrue(validation.dropped().isEmpty());

        var semiflows = PInvariantComputer.computePSemiflows(matrix, flatNet, marking);
        var semiValidation = PInvariantComputer.validateExact(semiflows, matrix, flatNet, marking);
        assertEquals(semiflows, semiValidation.valid(), "Genuine semiflows must pass unchanged");
        assertTrue(semiValidation.dropped().isEmpty());
    }

    @Test
    void compute_dropsRowsOutsideTheIntExtractionRange() {
        // Chain A -(65539)-> B -(65537)-> C with unit outputs. The genuine conservation
        // law is A + 65539*B + (65539*65537)*C, and 65539*65537 = 4295229443 does not fit
        // int: the row cannot be narrowed to a weight vector at all. It must be dropped
        // at extraction with the overflow reason — narrowing wraps, and a wrapped
        // "invariant" conjoined into a CHC rule body prunes reachable successors.
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);
        var pC = Place.of("C", String.class);
        var t1 = Transition.builder("T1")
            .inputs(In.exactly(65539, pA)).outputs(Out.place(pB)).build();
        var t2 = Transition.builder("T2")
            .inputs(In.exactly(65537, pB)).outputs(Out.place(pC)).build();
        var net = PetriNet.builder("Truncation").transitions(t1, t2).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);
        var marking = MarkingState.builder().tokens(pA, 1).build();

        var extraction = PInvariantComputer.computeChecked(matrix, flatNet, marking);
        assertEquals(1, extraction.dropped().size(),
            "the out-of-range row must be dropped, not narrowed: " + extraction.dropped());
        assertEquals(
            "weight overflow at place 'C' "
            + "(exact value outside this implementation's integer extraction range)",
            extraction.dropped().getFirst());
        assertTrue(PInvariantComputer.compute(matrix, flatNet, marking).isEmpty(),
            "no wrapped candidate may reach a caller of compute()");

        // The exact re-validation gate stays the backstop for whatever does get through.
        var validation = PInvariantComputer.validateExact(
            extraction.valid(), matrix, flatNet, marking);
        assertTrue(validation.valid().isEmpty());
        assertTrue(validation.dropped().isEmpty());
    }

    // === H1 linearity guard (lean/Libpetri/Strengthening.lean) ===

    @Test
    void validateExact_dropsConsumeAllWitness_strengtheningH1() {
        // The Lean witness (`consume_all_hypothesis_is_necessary`): T: all(P0) -> P1,
        // M0 = (2, 0). The linearized incidence column is (-1, +1), so y = (1, 1) with
        // constant 2 passes the numeric y*C = 0 gate — yet a real firing drains BOTH
        // tokens (the encoder's M' = post arm), y*M drops 2 -> 1, and the conjoined
        // equality would prune the genuine successor (0, 1): the false-Proven shape.
        // The H1 guard must drop the candidate before it reaches an encoder.
        var p0 = Place.of("P0", String.class);
        var p1 = Place.of("P1", String.class);
        var t = Transition.builder("T").inputs(In.all(p0)).outputs(Out.place(p1)).build();
        var net = PetriNet.builder("LeanWitness").transitions(t).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);
        var marking = MarkingState.builder().tokens(p0, 2).build();

        var computed = PInvariantComputer.compute(matrix, flatNet, marking);
        assertFalse(computed.isEmpty(), "Elimination emits y = (1,1) against the linearized column");

        var validation = PInvariantComputer.validateExact(computed, matrix, flatNet, marking);
        assertTrue(validation.valid().isEmpty(), "y = (1,1) must not survive the H1 guard");
        assertEquals(1, validation.dropped().size());
        var reason = validation.dropped().getFirst();
        assertTrue(reason.contains("consume-all/reset place"), "Reason should name the arm: " + reason);
        assertTrue(reason.contains("'P0'"), "Reason should name the place: " + reason);
        assertTrue(reason.contains("Strengthening.lean H1"), "Reason should cite H1: " + reason);

        // Same validator on the semiflow path (C2): the Farkas semiflow y = (1,1) over
        // P0 must be dropped identically.
        var semiflows = PInvariantComputer.computePSemiflows(matrix, flatNet, marking);
        assertFalse(semiflows.isEmpty(), "Farkas emits the y = (1,1) semiflow");
        var semiValidation = PInvariantComputer.validateExact(semiflows, matrix, flatNet, marking);
        assertTrue(semiValidation.valid().isEmpty(), "Semiflow over P0 must be dropped by H1 too");
        assertTrue(semiValidation.dropped().getFirst().contains("Strengthening.lean H1"));
    }

    @Test
    void validateExact_dropsResetPlaceSupport_strengtheningH1() {
        // Reset analogue: R never enters the pre-vector, so its incidence column is all
        // zeros and y = e_R passes y*C = 0 with constant 1 — yet firing T clears R
        // (M'[R] = post[R] = 0), falsifying the "invariant". The guard must drop e_R
        // while keeping the genuinely linear P0 + P1 conservation law untouched.
        var p0 = Place.of("P0", String.class);
        var p1 = Place.of("P1", String.class);
        var r = Place.of("R", String.class);
        var t = Transition.builder("T")
            .inputs(In.one(p0)).reset(r).outputs(Out.place(p1)).build();
        var net = PetriNet.builder("ResetWitness").transitions(t).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);
        var marking = MarkingState.builder().tokens(p0, 1).tokens(r, 1).build();

        var computed = PInvariantComputer.compute(matrix, flatNet, marking);
        assertEquals(2, computed.size(), "Elimination finds P0 + P1 = 1 and R = 1");

        var validation = PInvariantComputer.validateExact(computed, matrix, flatNet, marking);
        assertEquals(1, validation.valid().size(), "Only the reset-free law may survive");
        var kept = validation.valid().getFirst();
        assertEquals(0, kept.weights()[flatNet.indexOf(r)],
            "The surviving invariant must have zero weight on the reset place");
        assertEquals(1, validation.dropped().size());
        var reason = validation.dropped().getFirst();
        assertTrue(reason.contains("consume-all/reset place"), "Reason should name the arm: " + reason);
        assertTrue(reason.contains("'R'"), "Reason should name the place: " + reason);
        assertTrue(reason.contains("Strengthening.lean H1"), "Reason should cite H1: " + reason);
    }

    @Test
    void validateExact_keepsExactlyN_linearConsumption() {
        // In.Exactly(2) consumes exactly 2 tokens (Arc.In#consumptionCount) — the
        // linear multi-token arm. The incidence column (-2, +1) tells the whole truth
        // about a firing, so y = (1, 2) is a genuine invariant: NOT dropped.
        var p0 = Place.of("P0", String.class);
        var p1 = Place.of("P1", String.class);
        var t = Transition.builder("T").inputs(In.exactly(2, p0)).outputs(Out.place(p1)).build();
        var net = PetriNet.builder("ExactlyLinear").transitions(t).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);
        var marking = MarkingState.builder().tokens(p0, 2).build();

        var computed = PInvariantComputer.compute(matrix, flatNet, marking);
        assertFalse(computed.isEmpty(), "Elimination finds P0 + 2*P1 = 2");

        var validation = PInvariantComputer.validateExact(computed, matrix, flatNet, marking);
        assertEquals(computed, validation.valid(), "Linear exactly(n) consumption must pass the guard");
        assertTrue(validation.dropped().isEmpty());
    }

    @Test
    void validateExact_dropsAtLeastSupport_drainSemantics() {
        // Verified semantics note: In.AtLeast(n) does NOT consume exactly n. It waits
        // for n and then DRAINS the place — Arc.In#consumptionCount returns `available`
        // for AtLeast, spec/02-input-output-specs.md IO-007 mandates it ("AtLeast(3) on
        // place with 7 tokens; verify all 7 consumed"), NetFlattener flags it in
        // FlatTransition#consumeAll, and SmtEncoder gives it the non-linear M' = post
        // arm. Strengthening.lean's H1 (`ZeroOnNonlinear`) accordingly names In::All
        // and In::AtLeast together. So atLeast support is dropped exactly like all():
        // from M0 = (3, 0), y = (1, 2) passes y*C = 0 against the linearized column
        // (-2, +1), yet one firing drains all 3 tokens and y*M falls 3 -> 2.
        var p0 = Place.of("P0", String.class);
        var p1 = Place.of("P1", String.class);
        var t = Transition.builder("T").inputs(In.atLeast(2, p0)).outputs(Out.place(p1)).build();
        var net = PetriNet.builder("AtLeastDrain").transitions(t).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);
        var marking = MarkingState.builder().tokens(p0, 3).build();

        var computed = PInvariantComputer.compute(matrix, flatNet, marking);
        assertFalse(computed.isEmpty(), "Elimination emits y = (1,2) against the linearized column");

        var validation = PInvariantComputer.validateExact(computed, matrix, flatNet, marking);
        assertTrue(validation.valid().isEmpty(),
            "atLeast(n) drains its place — its support must not survive the H1 guard");
        assertEquals(1, validation.dropped().size());
        var reason = validation.dropped().getFirst();
        assertTrue(reason.contains("consume-all/reset place"), "Reason should name the arm: " + reason);
        assertTrue(reason.contains("Strengthening.lean H1"), "Reason should cite H1: " + reason);
    }
}
