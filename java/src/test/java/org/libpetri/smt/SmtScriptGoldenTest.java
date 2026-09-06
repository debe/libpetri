package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.z3.CertificateChecker;
import org.libpetri.smt.z3.NameColouredEncoder;
import org.libpetri.smt.z3.SmtEncoder;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * VER-013 AC1: the scripts this verifier sends to z3 are byte-identical to the Rust
 * reference. The goldens under {@code src/test/resources/smt-golden/} were written by
 * the Rust verifier ({@code LIBPETRI_SMT_DUMP}) for the nets rebuilt here; a diff is a
 * parity finding in whichever emitter drifted, never a reason to edit the golden.
 *
 * <p>No solver is needed: the encoders are pure text.
 */
class SmtScriptGoldenTest {

    private static String golden(String name) {
        try (InputStream in = SmtScriptGoldenTest.class.getResourceAsStream("/smt-golden/" + name)) {
            assertNotNull(in, "missing golden " + name);
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new AssertionError(e);
        }
    }

    /** The certificate block a golden certificate script carries (its third block). */
    private static String certificateOf(String script) {
        int start = script.indexOf("(define-fun");
        int end = script.indexOf("\n\n(declare-const");
        return script.substring(start, end);
    }

    private static FlatNet flatten(PetriNet net) {
        return NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
    }

    // --- chain: p0(1) -> p1, placeBound(p1, 0) ---

    @Test
    void chain_hornScriptMatchesRust() {
        var p0 = Place.of("p0", Integer.class);
        var p1 = Place.of("p1", Integer.class);
        var t = Transition.builder("t").inputs(In.one(p0)).outputs(Out.place(p1)).build();
        var net = PetriNet.builder("chain").transitions(t).build();
        var flat = flatten(net);
        var m0 = MarkingState.builder().tokens(p0, 1).build();
        var invariants = SmtVerifier.encoderInvariants(flat, m0, false);

        var encoding = SmtEncoder.encode(flat, m0, SmtProperty.placeBound(p1, 0), invariants, Set.of(), true);
        assertEquals(golden("chain-horn.smt2"), encoding.smt2());
    }

    // --- arcs: inhibitor + read + reset + at-least + sink + env alwaysAvailable ---

    private static final Place<Integer> A = Place.of("A", Integer.class);
    private static final Place<Integer> B = Place.of("B", Integer.class);
    private static final Place<Integer> C = Place.of("C", Integer.class);
    private static final Place<Integer> R = Place.of("R", Integer.class);
    private static final Place<Integer> S = Place.of("S", Integer.class);
    private static final Place<Integer> E = Place.of("E", Integer.class);

    private static PetriNet arcsNet() {
        var t1 = Transition.builder("t1")
            .inputs(In.one(A), In.one(E))
            .inhibitors(B)
            .reads(C)
            .resets(R)
            .outputs(Out.place(S))
            .build();
        var t2 = Transition.builder("t2")
            .inputs(In.atLeast(1, B))
            .outputs(Out.and(A, R))
            .build();
        return PetriNet.builder("arcs").transitions(t1, t2).build();
    }

    /**
     * The {@code arcs-*} goldens were written by Rust for {@code deadlockFree()} with a
     * declared sink, BEFORE the [VER-002] split. Those exact bytes are now the encoding
     * of {@link SmtProperty.TerminatesAtSink} — the property that inherited the old
     * permissive predicate unchanged — so the test is retargeted rather than the goldens
     * regenerated. Nothing is lost: the arc encoding (inhibitor / read / reset / at-least)
     * and the VER-006 injection relaxation live in the shared quiescence core, which both
     * properties conjoin, and strict {@code DeadlockFree} stays pinned byte for byte by
     * the shared fixture goldens under {@code spec/verification-fixtures/scripts/}.
     */
    @Test
    void arcs_terminatesAtSinkWithSinkAndInjection_matchesRust() {
        var flat = NetFlattener.flatten(arcsNet(), Set.of(EnvironmentPlace.of(E)),
            EnvironmentAnalysisMode.alwaysAvailable());
        var m0 = MarkingState.builder().tokens(A, 1).tokens(C, 1).tokens(B, 2).build();
        var invariants = SmtVerifier.encoderInvariants(flat, m0, false);

        var encoding = SmtEncoder.encode(
            flat, m0, SmtProperty.terminatesAtSink(), invariants, Set.of(S), true);
        assertEquals(golden("arcs-horn.smt2"), encoding.smt2());

        var certGolden = golden("arcs-certificate.smt2");
        assertEquals(certGolden, CertificateChecker.vcScript(
            certificateOf(certGolden), flat, m0, SmtProperty.terminatesAtSink(), Set.of(S),
            invariants));
    }

    @Test
    void arcs_unreachableWithBoundedInjection_matchesRust() {
        var flat = NetFlattener.flatten(arcsNet(), Set.of(EnvironmentPlace.of(E)),
            EnvironmentAnalysisMode.bounded(2));
        var m0 = MarkingState.builder().tokens(A, 1).build();
        var invariants = SmtVerifier.encoderInvariants(flat, m0, false);
        var property = SmtProperty.unreachable(Set.of(S, A));

        var encoding = SmtEncoder.encode(flat, m0, property, invariants, Set.of(), true);
        assertEquals(golden("unreach-horn.smt2"), encoding.smt2());

        var certGolden = golden("unreach-certificate.smt2");
        assertEquals(certGolden, CertificateChecker.vcScript(
            certificateOf(certGolden), flat, m0, property, Set.of(), invariants));
    }

    // --- mutual exclusion on a one-token cycle ---

    @Test
    void mutex_cycle_matchesRust() {
        var x = Place.of("X", Integer.class);
        var y = Place.of("Y", Integer.class);
        var xy = Transition.builder("XtoY").inputs(In.one(x)).outputs(Out.place(y)).build();
        var yx = Transition.builder("YtoX").inputs(In.one(y)).outputs(Out.place(x)).build();
        var flat = flatten(PetriNet.builder("cycle").transitions(xy, yx).build());
        var m0 = MarkingState.builder().tokens(x, 1).build();
        var invariants = SmtVerifier.encoderInvariants(flat, m0, false);
        // Listed Y-first on purpose: the script orders the places by index.
        var property = SmtProperty.mutualExclusion(y, x);

        var encoding = SmtEncoder.encode(flat, m0, property, invariants, Set.of(), true);
        assertEquals(golden("mutex-horn.smt2"), encoding.smt2());

        var certGolden = golden("mutex-certificate.smt2");
        assertEquals(certGolden, CertificateChecker.vcScript(
            certificateOf(certGolden), flat, m0, property, Set.of(), invariants));
    }

    // --- ν scatter-gather, budget declared: the name-coloured encoder ---

    @Test
    void nuScatterGather_colouredScriptMatchesRust() {
        var source = Place.of("source", Integer.class);
        var budget = Place.of("budget", Integer.class);
        var pending = Place.of("pending", Integer.class);
        var a = Place.of("branchA", String.class);
        var b = Place.of("branchB", String.class);
        var merged = Place.of("merged", String.class);
        var fork = Transition.builder("fork")
            .inputs(In.one(source), In.one(budget))
            .outputs(Out.and(a, b, pending))
            .build();
        var join = Transition.builder("join")
            .inputs(In.one(a), In.one(b), In.one(pending))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(Out.and(merged, budget))
            .build();
        var net = PetriNet.builder("nu").transitions(fork, join).build();
        var flat = flatten(net);
        var m0 = MarkingState.builder().tokens(source, 3).tokens(budget, 2).build();
        var invariants = SmtVerifier.encoderInvariants(flat, m0, false);
        var semiflows = SmtVerifier.validatedSemiflows(flat, m0);

        var plan = NameColouredEncoder.buildPlan(
            net, flat, m0, Set.of("budget"), FragmentMode.BASE, Set.of(), semiflows);
        assertNotNull(plan, "the scatter-gather net is in the coloured fragment");
        var encoding = NameColouredEncoder.encode(
            plan, flat, m0, SmtProperty.branchPlaceBound(budget, 2), invariants, Set.of());
        assertNotNull(encoding);
        assertEquals(golden("nu-bound-horn-coloured.smt2"), encoding.smt2());
    }
}
