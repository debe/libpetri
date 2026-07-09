package org.libpetri.smt;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Set;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.NameFragment;
import org.libpetri.core.Arc;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

/**
 * Verify-locally-first proof of the {@link FragmentMode#EXTENDED} &nu;-fragment
 * (name-blind coloured-consumer role + fork-threaded co-mint), on a minimal fixture
 * reproducing the Marvin text guard-join + straggler-drain shape that
 * {@link NameFragment#classify} rejects today.
 *
 * <p>The fixture: a fork ({@code MINT}) mints ONE name into two carriers; two relays
 * thread it to the two join inputs; {@code RELAY_B} XOR-forks to a non-coloured
 * "suspicious" branch (a guard violation), so the safe branch reaches the &nu;-join
 * ({@code JOIN}, matched by name) while the violation branch leaves {@code COL_A} a
 * straggler that a dead-letter {@code DRAIN_A} must clear.
 *
 * <ul>
 *   <li><b>BASE</b>: {@code DRAIN_A} (a non-match consumer of coloured {@code COL_A})
 *       takes the net out of fragment ({@code classify == null}); deadlock-freedom is
 *       downgraded to UNKNOWN.</li>
 *   <li><b>EXTENDED</b>: the fork-threaded co-mint gives {@code COL_A}/{@code COL_B}
 *       the SAME name (so the join is enabled), and the drain clears the straggler on
 *       the violation branch — deadlock-freedom is genuinely PROVEN.</li>
 *   <li><b>EXTENDED, drain removed</b>: the violation branch strands {@code COL_A} — a
 *       genuine deadlock counterexample.</li>
 * </ul>
 */
class FragmentExtensionTest {

    private static final Place<String> SEED = Place.of("SEED", String.class);
    private static final Place<String> CARRIER_A = Place.of("CARRIER_A", String.class);
    private static final Place<String> CARRIER_B = Place.of("CARRIER_B", String.class);
    private static final Place<String> COL_A = Place.of("COL_A", String.class);
    private static final Place<String> COL_B = Place.of("COL_B", String.class);
    private static final Place<String> OUT = Place.of("OUT", String.class);
    private static final Place<String> DEADLETTER = Place.of("DEADLETTER", String.class);
    private static final Place<String> SUSPICIOUS = Place.of("SUSPICIOUS", String.class);

    private static final Set<String> CARRIERS = Set.of("CARRIER_A", "CARRIER_B");

    /** @param withDrain include the {@code COL_A} dead-letter drain (else the straggler strands). */
    private static PetriNet fixture(boolean withDrain) {
        var mint = Transition.builder("MINT")
            .inputs(Arc.In.one(SEED))
            .outputs(Arc.Out.and(CARRIER_A, CARRIER_B))     // co-mint: one fresh name into both carriers
            .build();
        var relayA = Transition.builder("RELAY_A")
            .inputs(Arc.In.one(CARRIER_A))
            .outputs(Arc.Out.place(COL_A))                  // relay: thread the name to COL_A
            .build();
        var relayB = Transition.builder("RELAY_B")
            .inputs(Arc.In.one(CARRIER_B))
            .outputs(Arc.Out.xor(COL_B, SUSPICIOUS))        // safe -> COL_B (thread); violation -> SUSPICIOUS (drop)
            .build();
        var join = Transition.builder("JOIN")
            .inputs(Arc.In.one(COL_A), Arc.In.one(COL_B))
            .match(MatchSpec.builder()
                .key(COL_A, (String s) -> NameId.of(s))
                .key(COL_B, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(OUT))
            .build();
        var builder = PetriNet.builder("fragmentFixture").transitions(mint, relayA, relayB, join);
        if (withDrain) {
            // Dead-letter the straggler COL_A together with the violation token SUSPICIOUS — so the
            // drain fires ONLY once the guard violation has actually happened (SUSPICIOUS present),
            // never preempting a valid join or a not-yet-produced COL_B. This is the faithful model of
            // DiscardStaleResponse draining a response whose turn went to a guard violation.
            builder.transition(Transition.builder("DRAIN_A")
                .inputs(Arc.In.one(COL_A), Arc.In.one(SUSPICIOUS))
                .outputs(Arc.Out.place(DEADLETTER))
                .build());
        }
        return builder.build();
    }

    private static MarkingState seedOneTurn() {
        return MarkingState.builder().tokens(SEED, 1).build();
    }

    static boolean z3Available() {
        try {
            Class.forName("com.microsoft.z3.Context").getDeclaredConstructor().newInstance();
            return true;
        } catch (Exception | LinkageError e) {
            return false;
        }
    }

    @Test
    void baseFragmentRejectsTheDrain() {
        // The drain — a non-match transition consuming coloured COL_A — trips the R5
        // out-of-fragment rule under BASE (carrier declarations are ignored).
        assertNull(NameFragment.classify(fixture(true)));
        assertNull(NameFragment.classify(fixture(true), FragmentMode.BASE, CARRIERS));
    }

    @Test
    void extendedFragmentAcceptsDrainAndCoMint() {
        assertNotNull(NameFragment.classify(fixture(true), FragmentMode.EXTENDED, CARRIERS));
        assertNotNull(NameFragment.classify(fixture(false), FragmentMode.EXTENDED, CARRIERS));
    }

    @Test
    @EnabledIf("z3Available")
    void baseDeadlockFreeIsUnknown() {
        var r = SmtVerifier.forNet(fixture(true))
            .initialMarking(seedOneTurn())
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(OUT, DEADLETTER)
            .verify();
        // hasMatch + quiescence property + out-of-BASE-fragment (the drain) -> name-blind
        // SMT verdict is downgraded to UNKNOWN (not a genuine proof).
        assertFalse(r.isProven(),
            "BASE must NOT prove deadlock-freedom on this fork-threaded ν-net (it is UNKNOWN):\n" + r.report());
        assertFalse(r.isViolated());
    }

    // Not @EnabledIf("z3Available"): a deadlockFree query on a matched net routes
    // through the solver-free Route B name-partition quotient and never touches Z3.
    @Test
    void extendedProvesNoStall() {
        var r = SmtVerifier.forNet(fixture(true))
            .initialMarking(seedOneTurn())
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(OUT, DEADLETTER)
            .fragmentMode(FragmentMode.EXTENDED)
            .carrierPlaces(CARRIER_A, CARRIER_B)
            .verify();
        assertTrue(r.isProven(),
            "EXTENDED must genuinely PROVE deadlock-freedom: the fork-threaded co-mint enables the "
            + "name-join and the drain clears the violation-branch straggler.\n" + r.report());
        // The verdict must come from Route B (the name-partition quotient), not a
        // silent name-blind SMT fall-back.
        assertTrue(r.report().contains("Route B"),
            "EXTENDED PROVEN must be decided via Route B, not the SMT fall-back:\n" + r.report());
    }

    @Test
    void extendedFindsGenuineStallWhenDrainRemoved() {
        var r = SmtVerifier.forNet(fixture(false)) // no DRAIN_A -> the violation branch strands COL_A
            .initialMarking(seedOneTurn())
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(OUT, DEADLETTER)
            .fragmentMode(FragmentMode.EXTENDED)
            .carrierPlaces(CARRIER_A, CARRIER_B)
            .verify();
        assertTrue(r.isViolated(),
            "EXTENDED must find the GENUINE stall: the violation branch leaves a COL_A straggler with "
            + "no drain, so the net deadlocks.\n" + r.report());
        assertTrue(r.report().contains("Route B"),
            "EXTENDED VIOLATED must be decided via Route B, not the SMT fall-back:\n" + r.report());
    }

    /**
     * Blocker-1/2 regression: a coloured consumer at {@code In.exactly(2)} would
     * re-emit two name-symbols into a coloured output while the base marking adds
     * only one (over-counting the name layer), or drop a base-enabled firing when
     * name-blind. {@link NameFragment#classify} must reject count != 1 under
     * EXTENDED so the verifier falls back to the sound over-approximation.
     */
    @Test
    void extendedRejectsColouredConsumerAtCountTwo() {
        var drain2 = Transition.builder("DRAIN2")
            .inputs(Arc.In.exactly(2, COL_A))    // consumes a coloured place at count 2
            .outputs(Arc.Out.place(DEADLETTER))
            .build();
        var net = PetriNet.builder("countTwo").transitions(joinTransition(), drain2).build();
        assertNull(NameFragment.classify(net, FragmentMode.EXTENDED, Set.of()),
            "a coloured consumer at count 2 must be rejected under EXTENDED");
    }

    /**
     * A reset arc on a coloured place makes classify return {@code null} in BOTH
     * modes: the reset would zero the place while the name layer keeps its symbol,
     * breaking the count == name-total invariant.
     */
    @Test
    void resetOnColouredPlaceRejectedBothModes() {
        var scratch = Place.of("SCRATCH", String.class);
        var clear = Transition.builder("CLEAR")
            .inputs(Arc.In.one(scratch))
            .resets(COL_A)                       // reset arc on a coloured (match-key) place
            .build();
        var net = PetriNet.builder("resetColoured").transitions(joinTransition(), clear).build();
        assertNull(NameFragment.classify(net, FragmentMode.BASE, Set.of()),
            "reset on a coloured place is rejected under BASE");
        assertNull(NameFragment.classify(net, FragmentMode.EXTENDED, Set.of()),
            "reset on a coloured place is rejected under EXTENDED");
    }

    /**
     * A mistyped carrier name would silently make two fork branches mint independent
     * names, so the join never becomes name-enabled and the verifier could report a
     * false deadlock. {@link SmtVerifier#carrierPlaces} must fail loudly instead.
     */
    @Test
    void carrierValidationThrowsOnUnknownPlace() {
        var stranger = Place.of("STRANGER", String.class);
        assertThrows(IllegalArgumentException.class,
            () -> SmtVerifier.forNet(fixture(true)).carrierPlaces(stranger));
    }

    /** The name-by-name &nu;-join over the two coloured inputs, reused by classify tests. */
    private static Transition joinTransition() {
        return Transition.builder("JOIN")
            .inputs(Arc.In.one(COL_A), Arc.In.one(COL_B))
            .match(MatchSpec.builder()
                .key(COL_A, (String s) -> NameId.of(s))
                .key(COL_B, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(OUT))
            .build();
    }
}
