package org.libpetri.smt;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.time.Duration;
import java.util.Set;

import org.junit.jupiter.api.Test;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.NameFragment;
import org.libpetri.analysis.NameStateClassGraph;
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

    // ===== NU-052 Part A: DBM residual-earliest prune + multiplicity guard =====

    /**
     * A DELAYED higher-priority join (delayed 100) and a DELAYED lower-priority drain (delayed 200)
     * conflicting on {@code COL_A}. The old {@code earliest()==0} guard could not prune a non-immediate
     * H; the residual-earliest predicate can. Built directly against {@link NameStateClassGraph} so we
     * observe the prune as reachability of {@code DEADLETTER}.
     */
    private static PetriNet delayedFixture() {
        var mint = Transition.builder("MINT")
            .inputs(Arc.In.one(SEED))
            .outputs(Arc.Out.and(COL_A, COL_B))
            .build();
        var join = Transition.builder("JOIN")                 // delayed 100, default priority
            .inputs(Arc.In.one(COL_A), Arc.In.one(COL_B))
            .timing(Timing.delayed(Duration.ofMillis(100)))
            .match(MatchSpec.builder()
                .key(COL_A, (String s) -> NameId.of(s))
                .key(COL_B, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(OUT))
            .build();
        var drain = Transition.builder("DRAIN_A")             // delayed 200, lower priority
            .inputs(Arc.In.one(COL_A))
            .timing(Timing.delayed(Duration.ofMillis(200)))
            .priority(-10)
            .outputs(Arc.Out.place(DEADLETTER))
            .build();
        return PetriNet.builder("delayedPriorityFixture").transitions(mint, join, drain).build();
    }

    private static boolean reachesDeadletter(PetriNet net, MarkingState initial, PrioritySemantics ps) {
        var fragment = NameFragment.classify(net, FragmentMode.EXTENDED, Set.of());
        var graph = NameStateClassGraph.build(
            net, initial, fragment, 10_000, Set.of(), EnvironmentAnalysisMode.ignore(), ps);
        for (int i = 0; i < graph.classCount(); i++) {
            if (graph.markingOf(i).tokens(DEADLETTER) > 0) {
                return true;
            }
        }
        return false;
    }

    @Test
    void delayedConflictPrunesLowerPriority() {
        var net = delayedFixture();
        var initial = MarkingState.builder().tokens(SEED, 1).build();
        assertTrue(reachesDeadletter(net, initial, PrioritySemantics.NONE),
            "NONE must explore the drain and reach DEADLETTER");
        assertFalse(reachesDeadletter(net, initial, PrioritySemantics.CONFLICT),
            "CONFLICT must prune the DELAYED lower-priority drain (residual-earliest): the delayed "
            + "join becomes ready first and takes COL_A");
    }

    @Test
    void multiplicityTwoTokensDoesNotPrune() {
        // SEED=2 lets MINT co-mint two distinct names, so COL_A can hold 2 tokens. With both demands
        // (join + drain, 1 each) satisfiable at once, the drain does NOT compete and must not be
        // pruned — DEADLETTER stays reachable even under CONFLICT.
        var net = delayedFixture();
        var initial = MarkingState.builder().tokens(SEED, 2).build();
        assertTrue(reachesDeadletter(net, initial, PrioritySemantics.CONFLICT),
            "CONFLICT must NOT prune when the shared COL_A holds enough tokens (2) for both the join "
            + "and the drain (multiplicity)");
    }

    @Test
    void readArcOnSharedPlaceIsNotAConsumptionConflict() {
        // NU-052 criterion 4: a READ arc on the shared place is not a consumption conflict, so
        // CONFLICT must NOT prune the lower-priority consumer. H (priority 10) merely READS SH;
        // DRAIN (priority -10) CONSUMES SH into DEADLETTER. Because sharesConsumedInput counts only
        // consumed inputs, H does not rob DRAIN of SH → DEADLETTER stays reachable even under
        // CONFLICT. (If H consumed SH this would be a genuine conflict and CONFLICT would prune it.)
        // A never-fired ν-JOIN (its coloured inputs start empty) makes the net a ν-net so it
        // classifies into a NameFragment; the SH conflict itself is plain/uncoloured (coloured
        // places may not carry read arcs — classify's soundness guard).
        var sh = Place.of("SH", String.class);
        var tokH = Place.of("TOK_H", String.class);
        var join = Transition.builder("JOIN")
            .inputs(Arc.In.one(COL_A), Arc.In.one(COL_B))
            .match(MatchSpec.builder()
                .key(COL_A, (String s) -> NameId.of(s))
                .key(COL_B, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(OUT))
            .build();
        var h = Transition.builder("H")             // higher priority, only READS SH
            .inputs(Arc.In.one(tokH))
            .reads(sh)
            .priority(10)
            .outputs(Arc.Out.place(OUT))
            .build();
        var drain = Transition.builder("DRAIN")     // lower priority, CONSUMES SH
            .inputs(Arc.In.one(sh))
            .priority(-10)
            .outputs(Arc.Out.place(DEADLETTER))
            .build();
        var net = PetriNet.builder("readArcFixture").transitions(join, h, drain).build();
        var initial = MarkingState.builder().tokens(tokH, 1).tokens(sh, 1).build();

        assertTrue(reachesDeadletter(net, initial, PrioritySemantics.NONE),
            "NONE must explore the drain and reach DEADLETTER");
        assertTrue(reachesDeadletter(net, initial, PrioritySemantics.CONFLICT),
            "CONFLICT must NOT prune when H only READS the shared place (no consumption conflict) "
            + "— DEADLETTER stays reachable");
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
