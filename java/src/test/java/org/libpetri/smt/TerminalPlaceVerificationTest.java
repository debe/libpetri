package org.libpetri.smt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.TimePetriNetAnalyzer;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.core.internal.TerminalEncoding;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.opennet.OpenNetContract;
import org.libpetri.smt.opennet.OpenNetVerifier;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.core.Arc.In.one;
import static org.libpetri.core.Arc.Out.and;
import static org.libpetri.core.Arc.Out.place;

/**
 * <b>EXEC-042</b> AC7/AC8 with <b>VER-014</b> "Net-declared terminals": every verifier applies
 * a net's terminal places without the caller restating them, and a net without terminal places
 * encodes exactly as before.
 */
class TerminalPlaceVerificationTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<String> IN = Place.of("in", String.class);
    private static final Place<String> A = Place.of("a", String.class);
    private static final Place<String> B = Place.of("b", String.class);
    private static final Place<String> DONE = Place.of("done", String.class);
    private static final Place<String> LATE = Place.of("late", String.class);

    /**
     * The net of EXEC-042 AC2: a fork whose one arm marks {@code done} while the other arm's
     * action may still be in flight.
     */
    private static PetriNet.Builder fork() {
        return PetriNet.builder("fork").transitions(
            Transition.builder("fork").inputs(one(IN)).outputs(and(A, B)).build(),
            Transition.builder("finish").inputs(one(A)).outputs(place(DONE)).build(),
            Transition.builder("straggler").inputs(one(B)).outputs(place(LATE)).build());
    }

    private static final MarkingState START = MarkingState.builder().tokens(IN, 1).build();

    private static SmtVerificationResult deadlockFree(PetriNet net, boolean enumeration) {
        var verifier = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(START)
            .property(SmtProperty.deadlockFree());
        if (!enumeration) verifier.enumerationMaxClasses(0); // the SMT encoders, not the graph
        return verifier.verify();
    }

    @Test
    @EnabledIf("z3Available")
    void withoutTheDeclarationTheForkIsADeadlockViolation_EXEC042_AC7() {
        var net = fork().build();
        assertTrue(deadlockFree(net, false).isViolated(),
            "EXEC-042 AC7: without the declaration the net strands its other work");
        assertTrue(deadlockFree(net, true).isViolated(), "on the enumeration route too");
    }

    @Test
    @EnabledIf("z3Available")
    void withTheDeclarationDeadlockFreedomIsProvenWithNoSinkOption_EXEC042_AC7() {
        var net = fork().terminal(DONE).build();
        var smt = deadlockFree(net, false);
        assertTrue(smt.isProven(),
            "EXEC-042 AC7 / VER-014: a net-declared terminal is applied by the verifier itself — "
                + "no sinkPlaces or sinkPlacesWhen from the caller.\n" + smt.report());
        assertTrue(deadlockFree(net, true).isProven(), "on the enumeration route too");
    }

    @Test
    void aNetWithoutTerminalsIsVerifiedAsTheSameInstance_EXEC042_AC8() {
        var net = fork().build();
        assertSame(net, TerminalEncoding.inhibited(net),
            "EXEC-042 AC8: a net without terminals is not rebuilt, so its scripts are byte-identical "
                + "(the committed goldens pin the bytes: SmtScriptParityTest, SmtScriptGoldenTest)");
    }

    @Test
    void theTerminalEncodingIsTheHandWrittenOne_VER014() {
        // What the verifier does for a terminal equals what a caller would have had to write:
        // 'done' inhibits every transition, is a sink, and excuses every place.
        var declared = StructureOnly.bind(fork().terminal(DONE).build());
        var auto = SmtVerifier.forNet(declared).initialMarking(START).encodeScripts();

        var handWritten = StructureOnly.bind(PetriNet.builder("fork").transitions(
            Transition.builder("fork").inputs(one(IN)).outputs(and(A, B)).inhibitor(DONE).build(),
            Transition.builder("finish").inputs(one(A)).outputs(place(DONE)).inhibitor(DONE).build(),
            Transition.builder("straggler").inputs(one(B)).outputs(place(LATE)).inhibitor(DONE).build())
            .place(DONE)
            .build());
        var all = NetFlattener.declaredPlaces(declared).toArray(new Place<?>[0]);
        var manual = SmtVerifier.forNet(handWritten).initialMarking(START)
            .sinkPlaces(DONE).sinkPlacesWhen(DONE, all).encodeScripts();

        assertEquals(manual, auto, "VER-014 'Net-declared terminals': the encodings are identical");
    }

    @Test
    void theGoalAnalyzerSeesTheRunStopAtTheTerminal_EXEC042() {
        // Once 'done' is marked nothing fires: every such class is dead.
        var net = StructureOnly.bind(fork().terminal(DONE).build());
        var scg = TimePetriNetAnalyzer.forNet(net).initialMarking(START).goalPlaces(DONE).build()
            .analyze().stateClassGraph();
        var terminal = scg.stateClasses().stream().filter(sc -> sc.marking().tokens(DONE) > 0).toList();
        assertFalse(terminal.isEmpty(), "the premise: 'done' is reachable");
        assertTrue(terminal.stream().allMatch(sc -> scg.successors(sc).isEmpty()),
            "no class with 'done' marked has a successor");
    }

    @Test
    @EnabledIf("z3Available")
    void theOpenNetRouteMergesTheTerminalAsADesignedTerminal_EXEC042_VER022() {
        var contract = OpenNetContract.builder().initialTokens(IN, 1).build();
        var without = OpenNetVerifier.verifyOpenNet(StructureOnly.bind(fork().build()), contract);
        assertTrue(without.isViolated(),
            "without the declaration the internal places are stranded at quiescence\n" + without.report());

        var with = OpenNetVerifier.verifyOpenNet(StructureOnly.bind(fork().terminal(DONE).build()), contract);
        assertTrue(with.isProven(),
            "VER-022: the net's terminal is merged as a designed terminal excusing every place\n"
                + with.report());
    }
}
