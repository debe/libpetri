package org.libpetri.smt;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.time.Duration;

import org.junit.jupiter.api.Test;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.PrioritySemantics;
import org.libpetri.core.Arc;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;

/**
 * Verify-locally-first proof of {@link PrioritySemantics#CONFLICT} (NU-052) on a minimal fixture
 * reproducing the Marvin guard-join vs. timed dead-letter-drain conflict.
 *
 * <p>Fixture: a fork ({@code MINT}) co-mints ONE fresh name into the two join inputs {@code COL_A}
 * and {@code COL_B}; an <b>immediate, default-priority</b> &nu;-{@code JOIN} matches them into
 * {@code OUT}; a <b>delayed, lower-priority</b> {@code DRAIN_A} consumes {@code COL_A} into
 * {@code DEADLETTER}. {@code DRAIN_A} and {@code JOIN} conflict on {@code COL_A}.
 *
 * <ul>
 *   <li><b>NONE</b> (priority/timing-blind, default): the graph explores {@code DRAIN_A} firing
 *       while the join is enabled and matched, consuming {@code COL_A} and stranding {@code COL_B}
 *       — a spurious stall the eager, priority-ordered executor cannot exhibit (the join is
 *       immediate and higher-priority). VIOLATED.</li>
 *   <li><b>CONFLICT</b>: {@code DRAIN_A} is pruned while the higher-priority, no-later-ready join
 *       is enabled, so the join always fires. PROVEN via Route B.</li>
 *   <li><b>CONFLICT, genuine orphan</b>: when {@code COL_A} really has no matching {@code COL_B}
 *       the join is not enabled, so nothing prunes the drain — and with the drain removed the
 *       orphan strands. CONFLICT still reports that real deadlock (it does not over-prune).</li>
 * </ul>
 */
class NuScgPriorityTest {

    private static final Place<String> SEED = Place.of("SEED", String.class);
    private static final Place<String> COL_A = Place.of("COL_A", String.class);
    private static final Place<String> COL_B = Place.of("COL_B", String.class);
    private static final Place<String> OUT = Place.of("OUT", String.class);
    private static final Place<String> DEADLETTER = Place.of("DEADLETTER", String.class);

    /**
     * @param coMintBoth mint one name into both join inputs (true) or only {@code COL_A} (orphan)
     * @param withDrain  include the delayed, low-priority {@code COL_A} dead-letter drain
     */
    private static PetriNet fixture(boolean coMintBoth, boolean withDrain) {
        var mint = Transition.builder("MINT")
            .inputs(Arc.In.one(SEED))
            .outputs(coMintBoth ? Arc.Out.and(COL_A, COL_B) : Arc.Out.place(COL_A))
            .build();
        var join = Transition.builder("JOIN")               // immediate, priority 0
            .inputs(Arc.In.one(COL_A), Arc.In.one(COL_B))
            .match(MatchSpec.builder()
                .key(COL_A, (String s) -> NameId.of(s))
                .key(COL_B, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(OUT))
            .build();
        var builder = PetriNet.builder("priorityFixture").transitions(mint, join);
        if (withDrain) {
            builder.transition(Transition.builder("DRAIN_A")  // delayed, lower priority, conflicts on COL_A
                .inputs(Arc.In.one(COL_A))
                .timing(Timing.delayed(Duration.ofSeconds(5)))
                .priority(-10)
                .outputs(Arc.Out.place(DEADLETTER))
                .build());
        }
        return builder.build();
    }

    private static MarkingState seedOneTurn() {
        return MarkingState.builder().tokens(SEED, 1).build();
    }

    private static SmtVerifier verifier(PetriNet net) {
        return SmtVerifier.forNet(net)
            .initialMarking(seedOneTurn())
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(OUT, DEADLETTER)
            .fragmentMode(FragmentMode.EXTENDED);
    }

    @Test
    void priorityBlindDefaultReportsSpuriousStall() {
        var r = verifier(fixture(true, true)).verify(); // NONE is the default
        assertTrue(r.report().contains("Route B"),
            "must be decided via Route B (EXTENDED accepted):\n" + r.report());
        assertTrue(r.isViolated(),
            "priority-blind NONE must report the spurious stall: the drain steals the matched "
            + "COL_A and strands COL_B.\n" + r.report());
    }

    @Test
    void conflictPriorityProvesNoStall() {
        var r = verifier(fixture(true, true))
            .prioritySemantics(PrioritySemantics.CONFLICT)
            .verify();
        assertTrue(r.report().contains("Route B"),
            "must be decided via Route B:\n" + r.report());
        assertTrue(r.isProven(),
            "CONFLICT must PROVE no-stall: the immediate, higher-priority join preempts the delayed "
            + "drain, so COL_A is never stolen from a live join.\n" + r.report());
    }

    @Test
    void conflictPriorityStillFindsGenuineStall() {
        // A real orphan (COL_A with no matching COL_B) and no drain: the join can never fire and
        // COL_A strands. CONFLICT must NOT hide this — the join is not enabled, so nothing is pruned.
        var r = verifier(fixture(false, false))
            .prioritySemantics(PrioritySemantics.CONFLICT)
            .verify();
        assertTrue(r.report().contains("Route B"),
            "must be decided via Route B:\n" + r.report());
        assertTrue(r.isViolated(),
            "CONFLICT must still find a GENUINE stall: an orphan COL_A with no join and no drain "
            + "strands.\n" + r.report());
    }

    @Test
    void conflictPriorityLetsTheDrainFireForARealOrphan() {
        // A real orphan WITH the drain present: CONFLICT does not prune the drain (the join is not
        // enabled), so the orphan is dead-lettered and the net is deadlock-free.
        var r = verifier(fixture(false, true))
            .prioritySemantics(PrioritySemantics.CONFLICT)
            .verify();
        assertTrue(r.isProven(),
            "CONFLICT must let the drain clear a genuine orphan (join not enabled → drain not "
            + "pruned).\n" + r.report());
        assertFalse(r.report().contains("declined"), r.report());
    }
}
