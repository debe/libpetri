package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.z3.CertificateChecker;
import org.libpetri.smt.z3.CounterexampleDecoder;
import org.libpetri.smt.z3.SmtEncoder;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [VER-016] state equation with firing counters.
 *
 * <p>The fork-or-halt net of the [VER-015] tests: {@code p0(1) → f → AND(a, b) | halt;
 * a → ga → ra; b → gb → rb; ra + rb → join → done}. Places in flat order: a, b, done, halt,
 * p0, ra, rb. Mirrors {@code typescript/tests/verification/state-equation.test.ts}.
 */
class StateEquationTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<String> P0 = Place.of("p0", String.class);
    private static final Place<String> A = Place.of("a", String.class);
    private static final Place<String> B = Place.of("b", String.class);
    private static final Place<String> RA = Place.of("ra", String.class);
    private static final Place<String> RB = Place.of("rb", String.class);
    private static final Place<String> HALT = Place.of("halt", String.class);
    private static final Place<String> DONE = Place.of("done", String.class);

    private static PetriNet forkOrHalt() {
        return LinearBoundTest.forkOrHalt();
    }

    private static MarkingState m0() {
        return LinearBoundTest.m0();
    }

    private static FlatNet flat(PetriNet net) {
        return LinearBoundTest.flat(net);
    }

    private static SmtProperty target() {
        return SmtProperty.unreachable(Set.of(RA, RB, HALT));
    }

    private static List<String> mVars(FlatNet flat, String suffix) {
        var out = new ArrayList<String>();
        for (int i = 0; i < flat.placeCount(); i++) {
            out.add("m" + i + suffix);
        }
        return out;
    }

    private static int count(String haystack, String needle) {
        int n = 0;
        for (int at = haystack.indexOf(needle); at >= 0; at = haystack.indexOf(needle, at + needle.length())) {
            n++;
        }
        return n;
    }

    // === Encoding ===

    @Test
    void isOffByDefault_andByteIdenticalToThePositionalEncode() {
        var flat = flat(forkOrHalt());
        var positional = SmtEncoder.encode(flat, m0(), target(), List.of(), Set.of(), true);
        var named = SmtEncoder.encode(flat, m0(), target(), List.of(), Set.of(), true, List.of(), false);
        assertEquals(positional.smt2(), named.smt2());
        assertEquals(0, named.counterCount());
    }

    @Test
    void addsOneCounterPerFlatTransition_zeroAtTheStart_incrementedByItsOwnRule() {
        var flat = flat(forkOrHalt());
        int p = flat.placeCount();
        int t = flat.transitionCount(); // f expands to two flat transitions
        assertEquals(5, t);
        var enc = SmtEncoder.encode(flat, m0(), target(), List.of(), Set.of(), false, List.of(), true);
        assertEquals(t, enc.counterCount());
        assertTrue(enc.smt2().contains("(declare-fun Reachable (" + String.join(" ", List.of("Int").stream()
            .flatMap(s -> java.util.stream.Stream.generate(() -> s).limit(p + t)).toList()) + ") Bool)"));
        // Init: M0 then T zeros.
        String m0Line = enc.smt2().lines().filter(l -> l.startsWith("(assert (Reachable ")).findFirst().orElseThrow();
        assertEquals(p + t, m0Line.strip().split(" ").length - 2);
        assertTrue(m0Line.endsWith(" 0 0 0 0 0))"), m0Line);
        // Rule k increments n_k and copies the others; counters are non-negative.
        assertTrue(enc.smt2().contains("(= n0p (+ n0 1))"));
        assertTrue(enc.smt2().contains("(= n1p n1)"));
        assertTrue(enc.smt2().contains("(>= n4p 0)"));
        // Counters are quantified in every rule and unconstrained in the error rule.
        assertTrue(enc.smt2().contains("(n0 Int)"));
        assertTrue(enc.smt2().contains("(n0p Int)"));
        String errorRule = enc.smt2().substring(enc.smt2().lastIndexOf("(assert (forall"));
        assertTrue(errorRule.contains("(Reachable " + String.join(" ", mVars(flat, "")) + " n0 n1 n2 n3 n4)"), errorRule);
        assertFalse(errorRule.contains("n0p"), errorRule);
    }

    @Test
    void conjoinsTheMarkingEquationOverEveryExactPlace_inTransitionOrder() {
        var flat = flat(forkOrHalt());
        var conds = SmtEncoder.stateEquationConditions(
            flat, m0(), List.of("n0", "n1", "n2", "n3", "n4"), mVars(flat, ""));
        assertEquals(flat.placeCount(), conds.size());
        // f's branches are flat transitions 0 (AND(a,b)) and 1 (halt), in enumeration order.
        assertTrue(conds.contains("(= m" + flat.indexOf(P0) + " (+ 1 (- n0) (- n1)))"), conds.toString());
        assertTrue(conds.contains("(= m" + flat.indexOf(HALT) + " (+ 0 n1))"), conds.toString());
        assertTrue(conds.contains("(= m" + flat.indexOf(A) + " (+ 0 n0 (- n2)))"), conds.toString());
        assertTrue(conds.contains("(= m" + flat.indexOf(DONE) + " (+ 0 n4))"), conds.toString());
        // The encoding carries them over the primed variables in every transition rule.
        var enc = SmtEncoder.encode(flat, m0(), target(), List.of(), Set.of(), false, List.of(), true);
        assertEquals(5, count(enc.smt2(), "(= m" + flat.indexOf(P0) + "p (+ 1 (- n0p) (- n1p)))"));
    }

    @Test
    void leavesConsumeAllAndInjectedPlacesOutOfTheEquation() {
        var q = Place.of("q", String.class);
        var r = Place.of("r", String.class);
        var s = Place.of("s", String.class);
        var envPlace = Place.of("env", String.class);
        var env = EnvironmentPlace.of(envPlace);
        var t = Transition.builder("t").inputs(In.all(q)).outputs(Out.place(r)).build();
        var u = Transition.builder("u").inputs(In.one(envPlace)).outputs(Out.place(s)).build();
        var net = StructureOnly.bind(PetriNet.builder("mixed").transitions(t, u).build());
        var flat = NetFlattener.flatten(net, Set.of(env), EnvironmentAnalysisMode.alwaysAvailable());
        var exact = SmtEncoder.equationPlaces(flat).stream().map(i -> flat.places().get(i).name()).toList();
        assertEquals(List.of("r", "s"), exact);
        var enc = SmtEncoder.encode(flat, MarkingState.builder().tokens(q, 2).build(),
            SmtProperty.mutualExclusion(r, s), List.of(), Set.of(), false, List.of(), true);
        assertFalse(enc.smt2().contains("(= m" + flat.indexOf(q) + "p (+ 2"), enc.smt2());
        assertFalse(enc.smt2().contains("(= m" + flat.indexOf(envPlace) + "p (+ 0"), enc.smt2());
        // The injection rule carries the counters unchanged.
        assertTrue(enc.smt2().contains("(= n0p n0)\n            (= n1p n1)"), enc.smt2());
    }

    @Test
    void theRawStepRelationMovesTheCountersButCarriesNoEquation() {
        var flat = flat(forkOrHalt());
        String step = SmtEncoder.encodeStepRelationSmt2(flat, true);
        assertTrue(step.contains("(= n2p (+ n2 1))"), step);
        assertFalse(step.contains("(+ 1 (- n0p) (- n1p))"), step);
        assertFalse(SmtEncoder.encodeStepRelationSmt2(flat).contains("n0"));
    }

    @Test
    void theCertificateCandidateReStatesTheEquation_andTheVcsRangeOverTheCounters() {
        var flat = flat(forkOrHalt());
        int p = flat.placeCount();
        String script = CertificateChecker.vcScript(SmtVerifier.placeholderCertificate(p + 5), flat, m0(),
            target(), Set.of(), List.of(), List.of(), true);
        assertTrue(script.contains("(declare-const n4 Int)"), script);
        assertTrue(script.contains("(declare-const n4p Int)"), script);
        assertTrue(script.contains("(= m" + flat.indexOf(P0) + " (+ 1 (- n0) (- n1)))"), script);
        assertTrue(script.contains("(= m" + flat.indexOf(P0) + "p (+ 1 (- n0p) (- n1p)))"), script);
        assertTrue(script.contains("(>= n0 0)"), script);
    }

    @Test
    void theDecoderReadsTheMarkingFromTheLeadingPlacesOfACounterCarryingFact() {
        var flat = flat(forkOrHalt());
        var args = new ArrayList<String>();
        for (var place : flat.places()) {
            args.add(place.name().equals("a") || place.name().equals("b") ? "1" : "0");
        }
        String fact = "(Reachable " + String.join(" ", args) + " 1 0 0 0 0)";
        assertEquals(0, CounterexampleDecoder.decodeStateSet(fact, flat).size());
        var withCounters = CounterexampleDecoder.decodeStateSet(fact, flat, 5);
        assertEquals(1, withCounters.size());
        var m = withCounters.iterator().next();
        assertEquals(1, m.tokens(A));
        assertEquals(1, m.tokens(B));
        assertEquals(2, m.placesWithTokens().size());
    }

    // === End to end ===

    @Test
    @EnabledIf("z3Available")
    void aProvenDeadlockFreedom_keepsItsVerdictAndPassesTheCertificateCheck() {
        // Explicit opt-out, not an oversight: [VER-017]'s enumeration route would prove
        // this by closing the graph, and the report lines under test are emitted only by
        // the encoding path the state equation strengthens.
        var result = SmtVerifier.forNet(forkOrHalt()).initialMarking(m0())
            .enumerationMaxClasses(0)
            .property(SmtProperty.deadlockFree()).sinkPlaces(DONE, HALT).stateEquation(true)
            .timeout(Duration.ofSeconds(30)).verify();
        assertTrue(result.isProven(), result.report());
        assertTrue(result.report().contains("State equation: encoded over 5 firing counters (VER-016)"), result.report());
        assertTrue(result.report().contains("Certificate check: PASSED (init, consecution, safety)"), result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void aGenuineViolation_staysViolatedAndItsCounterexampleReplays() {
        // Explicit opt-out, not an oversight: the replay this asserts on runs only on the
        // encoding path, which [VER-017]'s enumeration route would bypass.
        var result = SmtVerifier.forNet(forkOrHalt()).initialMarking(m0())
            .enumerationMaxClasses(0)
            .property(SmtProperty.deadlockFree()).sinkPlaces(DONE).stateEquation(true)
            .timeout(Duration.ofSeconds(30)).verify();
        assertTrue(result.isViolated(), result.report());
        assertEquals(Boolean.TRUE, result.counterexampleConfirmed(), result.report());
        assertEquals(1, result.counterexampleTrace().getLast().tokens(HALT), result.report());
    }

    @Test
    void encodeScripts_reflectsTheOption() {
        var off = SmtVerifier.forNet(forkOrHalt()).initialMarking(m0()).property(SmtProperty.deadlockFree())
            .sinkPlaces(DONE).encodeScripts();
        var on = SmtVerifier.forNet(forkOrHalt()).initialMarking(m0()).property(SmtProperty.deadlockFree())
            .sinkPlaces(DONE).stateEquation(true).encodeScripts();
        assertFalse(off.horn().contains("n0p"));
        assertTrue(on.horn().contains("n0p"));
        assertTrue(on.certificate().contains("(x!7 Int)"));
        assertFalse(off.certificate().contains("(x!7 Int)"));
    }
}
