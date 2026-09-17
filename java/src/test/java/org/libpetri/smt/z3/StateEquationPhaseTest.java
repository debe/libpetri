package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Transition;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.SmtVerifier;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.z3.StateEquationPhase.Options;
import org.libpetri.smt.z3.StateEquationPhase.Phase;
import org.libpetri.smt.z3.StateEquationPhase.StateEquationOutcome;
import org.libpetri.smt.z3.StateEquationPhase.StateEquationSolver;
import org.libpetri.smt.z3.StateEquationQuery.Candidate;
import org.libpetri.smt.z3.StateEquationQuery.MarkingInequality;
import org.libpetri.smt.z3.StateEquationQuery.Origin;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.time.Duration;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.smt.z3.StateEquationNets.*;

/**
 * [VER-018] the refinement loop of the state-equation phase: the order it settles a candidate
 * in — witness, trap, inductive inequality, relative inequality — every reason it steps aside
 * with, and the candidate as the report prints it. Mirrors the phase tests of the Rust port
 * ({@code rust/libpetri-verification/src/state_equation_phase.rs}), whose assertions are the
 * TypeScript port's; the phase through {@code SmtVerifier} is
 * {@code StateEquationPhaseVerifierTest}'s.
 */
class StateEquationPhaseTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    /** {@code ab: a → b}, {@code ba: b → a} from {@code {a: 1}}: {@code {a, b}} is an initially marked trap. */
    static FlatNet abLoop() {
        var a = place("a");
        var b = place("b");
        return flatten(PetriNet.builder("loop").transitions(
            Transition.builder("ab").inputs(In.one(a)).outputs(Out.place(b)).build(),
            Transition.builder("ba").inputs(In.one(b)).outputs(Out.place(a)).build()).build());
    }

    static int transition(FlatNet flat, String name) {
        for (int t = 0; t < flat.transitionCount(); t++) {
            if (flat.transitions().get(t).name().equals(name)) {
                return t;
            }
        }
        throw new IllegalArgumentException("no transition " + name);
    }

    /**
     * A {@code sat} model defining the named places ({@code marking}: name, value pairs) and
     * transitions ({@code counts}: name, value pairs), as z3 prints one.
     */
    static String model(FlatNet flat, List<Object> marking, List<Object> counts) {
        var defs = new ArrayList<String>();
        for (int i = 0; i < marking.size(); i += 2) {
            defs.add("  (define-fun m" + indexOf(flat, (String) marking.get(i)) + " () Int\n    " + marking.get(i + 1) + ")");
        }
        for (int i = 0; i < counts.size(); i += 2) {
            defs.add("  (define-fun n" + transition(flat, (String) counts.get(i)) + " () Int\n    " + counts.get(i + 1) + ")");
        }
        return "sat\n(\n" + String.join("\n", defs) + "\n)";
    }

    /** A weighting {@code a·M <= b} ({@code name, weight} pairs) as the synthesis queries' model prints it. */
    static String weighting(FlatNet flat, int bound, Object... nameWeights) {
        var defs = new ArrayList<String>();
        for (int i = 0; i < nameWeights.length; i += 2) {
            int w = (Integer) nameWeights[i + 1];
            String literal = w < 0 ? "(- " + (-w) + ")" : String.valueOf(w);
            defs.add("(define-fun a" + indexOf(flat, (String) nameWeights[i]) + " () Int " + literal + ")");
        }
        defs.add("(define-fun b () Int " + bound + ")");
        return "sat\n(" + String.join(" ", defs) + ")";
    }

    /**
     * A scripted solver: hands out the replies in order — a reply, or an exception to throw — and
     * records which query each call was ({@code state-equation}, {@code inductive} or
     * {@code relative}, read off the script's header), with the dump phase and the timeout.
     */
    static final class Stub implements StateEquationSolver {
        final Deque<Object> replies;
        final List<String> labels = new ArrayList<>();
        final List<Phase> phases = new ArrayList<>();
        final List<Long> timeouts = new ArrayList<>();

        Stub(Object... replies) {
            this.replies = new ArrayDeque<>(Arrays.asList(replies));
        }

        @Override
        public String run(String script, Phase phase, long timeoutMs) throws Exception {
            String header = script.lines().findFirst().orElse("");
            String label;
            if (header.startsWith("; State-equation phase")) {
                label = "state-equation";
            } else if (header.startsWith("; Inductive-inequality refinement relative")) {
                label = "relative";
            } else if (header.startsWith("; Inductive-inequality refinement")) {
                label = "inductive";
            } else {
                throw new AssertionError("an unexpected script: " + header);
            }
            labels.add(label);
            phases.add(phase);
            timeouts.add(timeoutMs);
            Object reply = replies.poll();
            if (reply == null) {
                throw new AssertionError("no reply scripted for this query");
            }
            if (reply instanceof Exception e) {
                throw e;
            }
            return (String) reply;
        }
    }

    static StateEquationOutcome phase(JoinWithSkip join, Stub stub, Options options) {
        return StateEquationPhase.runStateEquationPhase(join.flat(), join.m0(), SmtProperty.deadlockFree(),
            Set.of(join.done(), join.skipped()), List.of(), stub, options);
    }

    static StateEquationOutcome phase(QueueAndBundle queue, boolean cancellable, Stub stub, Options options) {
        return StateEquationPhase.runStateEquationPhase(queue.flat(), queue.m0(), SmtProperty.deadlockFree(),
            queue.sinks(cancellable), List.of(), stub, options);
    }

    static <T extends StateEquationOutcome> T as(Class<T> kind, StateEquationOutcome outcome) {
        assertInstanceOf(kind, outcome, () -> "got " + outcome);
        return kind.cast(outcome);
    }

    /** The join's spurious candidate: {@code mergeSkip} fired after the data arrived. */
    static String skippedAfterData(FlatNet flat) {
        return model(flat, List.of("hasdata", 1, "skipped", 1),
            List.of("route_b0", 1, "armAData", 1, "armBEmpty", 1, "mergeSkip", 1));
    }

    @Test
    void describesACandidateAsTheReportPrintsIt() {
        var flat = joinWithSkip().flat();
        var candidate = StateEquationQuery.decodeCandidate(skippedAfterData(flat), flat.placeCount(), flat.transitionCount());
        assertEquals("hasdata=1, skipped=1 after route_b0 x1, armAData x1, armBEmpty x1, mergeSkip x1",
            StateEquationPhase.describeCandidate(flat, candidate));
        var nothing = new Candidate(new long[flat.placeCount()], new long[flat.transitionCount()]);
        assertEquals("{} after no firing", StateEquationPhase.describeCandidate(flat, nothing));
        // A negative value is printed as the model has it, not hidden as a zero would be.
        assertEquals("a=-1 after ab x2",
            StateEquationPhase.describeCandidate(abLoop(), new Candidate(new long[] {-1, 0}, new long[] {2})));
    }

    /**
     * The join's round: the candidate has no witness and no trap, the inductive query finds
     * {@code hasdata <= ready0 + ready1}, and the query asked again is {@code unsat}.
     */
    @Test
    void provesAfterAnInductiveInequalityExcludesTheCandidate() {
        var join = joinWithSkip();
        var flat = join.flat();
        var stub = new Stub(skippedAfterData(flat),
            weighting(flat, 0, "hasdata", 1, "ready0", -1, "ready1", -1), "unsat");
        var outcome = phase(join, stub, Options.DEFAULT);
        var refinement = inequality(flat, 0, "hasdata", 1, "ready0", -1, "ready1", -1);
        assertEquals(new StateEquationOutcome.Proven(List.of(refinement), 3), outcome);
        assertEquals(List.of("state-equation", "inductive", "state-equation"), stub.labels);
        assertEquals(List.of(Phase.STATE_EQUATION, Phase.INVARIANT, Phase.STATE_EQUATION), stub.phases);
        assertTrue(stub.timeouts.stream().allMatch(t -> t > 0 && t <= 60_000), stub.timeouts::toString);
    }

    /**
     * The queue's bound holds only relative to the equation: the exact query answers
     * {@code unsat}, the relative one {@code 3*out + q <= 3}, which the phase takes without the
     * exact re-check — that re-check rejects it — and labels relative.
     */
    @Test
    void takesARelativeInequalityWithoutTheExactReCheck() {
        var queue = queueAndBundle(3, false);
        var flat = queue.flat();
        var candidate = model(flat, List.of("budget", 2, "out", 1, "q", 1),
            List.of("produce", 1, "signal", 1, "bundleEmpty", 1));
        var stub = new Stub(candidate, "unsat", weighting(flat, 3, "out", 3, "q", 1), "unsat");
        var outcome = phase(queue, false, stub, Options.DEFAULT);
        var relative = inequality(flat, 3, "out", 3, "q", 1);
        assertFalse(InvariantSynthesis.checkInductiveExact(flat, marking(flat, "budget", 3, "src", 1), relative));
        assertEquals("3*out + q <= 3", StateEquationQuery.formatInequality(flat, relative));
        assertEquals(new StateEquationOutcome.Proven(List.of(relative.withOrigin(Origin.RELATIVE)), 4), outcome);
        assertEquals(List.of("state-equation", "inductive", "relative", "state-equation"), stub.labels);
        assertEquals(Phase.INVARIANT, stub.phases.get(2));
    }

    /** A trap is found without the solver: the second query follows the first directly. */
    @Test
    void refinesWithATrapBeforeAskingForAnInequality() {
        var flat = abLoop();
        var m0 = MarkingState.builder().tokens(place("a"), 1).build();
        var stub = new Stub(model(flat, List.of(), List.of("ab", 1)), "unsat");
        var proven = as(StateEquationOutcome.Proven.class, StateEquationPhase.runStateEquationPhase(
            flat, m0, SmtProperty.deadlockFree(), Set.of(), List.of(), stub));
        assertEquals(2, proven.queries());
        assertEquals(1, proven.refinements().size());
        assertEquals(Origin.TRAP, proven.refinements().getFirst().origin());
        assertEquals("a + b >= 1", StateEquationQuery.formatInequality(flat, proven.refinements().getFirst()));
        assertEquals(List.of("state-equation", "state-equation"), stub.labels);
    }

    /** A candidate a run within its counts realises is the violation, with that run. */
    @Test
    void reportsTheRunACandidateRealises() {
        var queue = queueAndBundle(3, true);
        var flat = queue.flat();
        var stub = new Stub(model(flat, List.of("q", 3, "cancelled", 1), List.of("produce", 3, "cancel", 1)));
        var violated = as(StateEquationOutcome.Violated.class, phase(queue, true, stub, Options.DEFAULT));
        assertEquals(List.of("produce", "produce", "produce", "cancel"), violated.steps());
        assertEquals(5, violated.states().size());
        assertEquals(3, violated.states().get(4)[indexOf(flat, "q")]);
        assertTrue(violated.refinements().isEmpty());
        assertEquals(1, violated.queries());
    }

    /** Every way the phase steps aside, with the reason the report prints and the candidate it stopped on. */
    @Test
    void stepsAsideWithTheReasonAndTheCandidateItStoppedOn() {
        var join = joinWithSkip();
        var flat = join.flat();
        String sat = skippedAfterData(flat);
        Candidate decoded = StateEquationQuery.decodeCandidate(sat, flat.placeCount(), flat.transitionCount());
        var none = List.<MarkingInequality>of();

        assertEquals(new StateEquationOutcome.Inconclusive("z3 hard timeout after 61s", none, 1, null),
            phase(join, new Stub(new Exception("z3 hard timeout after 61s")), Options.DEFAULT));
        assertEquals(new StateEquationOutcome.Inconclusive("the state-equation query answered unknown", none, 1, null),
            phase(join, new Stub("unknown"), Options.DEFAULT));
        assertEquals(new StateEquationOutcome.Inconclusive("the state-equation query answered unknown", none, 1, null),
            phase(join, new Stub(""), Options.DEFAULT));
        assertEquals(new StateEquationOutcome.Inconclusive("the state-equation model could not be decoded", none, 1, null),
            phase(join, new Stub("sat\n(error \"model is not available\")"), Options.DEFAULT));
        assertEquals(new StateEquationOutcome.Inconclusive("refinement budget exhausted (0 refinements)", none, 1, decoded),
            phase(join, new Stub(sat), Options.DEFAULT.withMaxRefinements(0)));
        assertEquals(new StateEquationOutcome.Inconclusive("the inductive-inequality query answered unknown", none, 2, decoded),
            phase(join, new Stub(sat, "unknown"), Options.DEFAULT));
        assertEquals(new StateEquationOutcome.Inconclusive("Z3 error: boom", none, 2, decoded),
            phase(join, new Stub(sat, new Exception("Z3 error: boom")), Options.DEFAULT));
        assertEquals(new StateEquationOutcome.Inconclusive("the inductive-inequality model could not be decoded", none, 2, decoded),
            phase(join, new Stub(sat, "sat\n((define-fun a5 () Int 1))"), Options.DEFAULT));
        // Arm B raises hasdata without ready0: not inductive.
        String weaker = weighting(flat, 0, "hasdata", 1, "ready0", -1);
        assertEquals(new StateEquationOutcome.Inconclusive("an inductive inequality failed the exact re-check", none, 2, decoded),
            phase(join, new Stub(sat, weaker), Options.DEFAULT));
        // Inductive — nothing feeds `start` — but the candidate satisfies it too: no progress,
        // so no refinement.
        String vacuous = weighting(flat, 1, "start", 1);
        assertTrue(InvariantSynthesis.checkInductiveExact(flat, marking(flat, "start", 1), inequality(flat, 1, "start", 1)));
        assertEquals(new StateEquationOutcome.Inconclusive("an inductive inequality failed the exact re-check", none, 2, decoded),
            phase(join, new Stub(sat, vacuous), Options.DEFAULT));
        // The weight bound in the reason: M0 holds one token, so the default of 8.
        assertEquals(new StateEquationOutcome.Inconclusive(
                "no trap and no inductive inequality with weights within ±8 excludes the candidate", none, 3, decoded),
            phase(join, new Stub(sat, "unsat", "unsat"), Options.DEFAULT));
        assertEquals("no trap and no inductive inequality with weights within ±2 excludes the candidate",
            as(StateEquationOutcome.Inconclusive.class,
                phase(join, new Stub(sat, "unsat", "unsat"), Options.DEFAULT.withWeightBound(2))).reason());
        assertEquals(new StateEquationOutcome.Inconclusive("an inductive inequality does not exclude its candidate", none, 3, decoded),
            phase(join, new Stub(sat, "unsat", vacuous), Options.DEFAULT));
        // A refinement kept before the phase stepped aside is still reported.
        String joinInequality = weighting(flat, 0, "hasdata", 1, "ready0", -1, "ready1", -1);
        assertEquals(new StateEquationOutcome.Inconclusive("the state-equation query answered unknown",
                List.of(inequality(flat, 0, "hasdata", 1, "ready0", -1, "ready1", -1)), 3, null),
            phase(join, new Stub(sat, joinInequality, "unknown"), Options.DEFAULT));
        // No budget, no query: the phase never counts one it did not send.
        var spent = new Stub();
        assertEquals(new StateEquationOutcome.Inconclusive("time budget of 0 ms exhausted", none, 0, null),
            phase(join, spent, Options.DEFAULT.withBudgetMs(0)));
        assertTrue(spent.labels.isEmpty());
    }

    /** The weight bound grows with the tokens {@code M0} holds, so a queue of twelve may weigh its flag by twelve. */
    @Test
    void theDefaultWeightBoundGrowsWithTheInitialTokens() {
        var queue = queueAndBundle(12, false);
        var flat = queue.flat();
        var candidate = model(flat, List.of("budget", 11, "out", 1, "q", 1),
            List.of("produce", 1, "signal", 1, "bundleEmpty", 1));
        var outcome = as(StateEquationOutcome.Inconclusive.class,
            phase(queue, false, new Stub(candidate, "unsat", "unsat"), Options.DEFAULT));
        assertEquals("no trap and no inductive inequality with weights within ±13 excludes the candidate", outcome.reason());
    }

    @Test
    void rethrowsADefectInTheSolverRatherThanReportIt() {
        var join = joinWithSkip();
        assertThrows(NullPointerException.class,
            () -> phase(join, new Stub(new NullPointerException("a defect")), Options.DEFAULT));
        assertThrows(IllegalArgumentException.class, () -> Options.DEFAULT.withMaxRefinements(-1));
    }

    /**
     * The transport the verifier uses: one z3 process per script; an {@code (error …)} other than a
     * missing model, or a reply without a verdict line, is the failure the phase reports.
     */
    static StateEquationSolver z3() throws Exception {
        var solver = Z3Solver.resolve();
        return (script, phase, timeoutMs) -> {
            var reply = solver.run(script, phase.label(), Duration.ofMillis(timeoutMs), List.of());
            String unexpected = (reply.stdout() + "\n" + reply.stderr()).lines()
                .map(SmtText::errorLine)
                .filter(line -> line != null && !line.contains("model is not available"))
                .findFirst()
                .orElse(null);
            if (unexpected != null) {
                throw new Exception("z3 reported an error: " + unexpected);
            }
            if (SmtText.classifyFirstLine(reply.stdout()) == null) {
                throw new Exception(Z3Process.failureReason(reply, Z3Solver.timeoutMs(Duration.ofMillis(timeoutMs))));
            }
            return reply.stdout();
        };
    }

    /**
     * [VER-018]'s test derivation, at the phase: the join proves after one inductive inequality,
     * the queue after one relative to the equation, and the cancellable queue is violated by the
     * run {@code produce, produce, produce, cancel}.
     */
    @Test
    @EnabledIf("z3Available")
    void decidesTheJoinAndTheQueuesThroughZ3() throws Exception {
        var options = Options.DEFAULT.withBudgetMs(30_000);
        var property = SmtProperty.deadlockFree();

        var join = joinWithSkip();
        var joinProof = as(StateEquationOutcome.Proven.class, StateEquationPhase.runStateEquationPhase(join.flat(),
            join.m0(), property, Set.of(join.done(), join.skipped()), List.of(), z3(), options));
        assertEquals(List.of("hasdata <= ready0 + ready1"),
            joinProof.refinements().stream().map(r -> StateEquationQuery.formatInequality(join.flat(), r)).toList());
        assertEquals(Origin.INDUCTIVE, joinProof.refinements().getFirst().origin());
        assertEquals(3, joinProof.queries());

        var queue = queueAndBundle(3, false);
        var queueProof = as(StateEquationOutcome.Proven.class, StateEquationPhase.runStateEquationPhase(queue.flat(),
            queue.m0(), property, queue.sinks(false), List.of(), z3(), options));
        // The refinements before it depend on the models z3 returns (4.11 also adds `out + q <= 3`).
        assertEquals(Optional.of(Origin.RELATIVE), queueProof.refinements().stream()
            .filter(r -> StateEquationQuery.formatInequality(queue.flat(), r).equals("3*out + q <= 3"))
            .findFirst().map(r -> r.origin()));

        var cancellable = queueAndBundle(3, true);
        var flat = cancellable.flat();
        var violated = as(StateEquationOutcome.Violated.class, StateEquationPhase.runStateEquationPhase(flat,
            cancellable.m0(), property, cancellable.sinks(true), List.of(), z3(), options));
        assertEquals("cancel", violated.steps().getLast());
        int[] last = violated.states().getLast();
        assertTrue(last[indexOf(flat, "q")] > 0);
        assertTrue(AbstractReplayer.violationPredicate(flat, property, cancellable.sinks(true), List.of()).test(last));
    }
}
