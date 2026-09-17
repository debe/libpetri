package org.libpetri.smt.opennet;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.StateClassGraph;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.SmtVerificationResult.Verdict;
import org.libpetri.smt.SmtVerifier;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.OptionalInt;
import java.util.Set;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [VER-022] open-net verification against a contract. Mirrors
 * {@code typescript/tests/verification/open-net.test.ts}, plus the report pins of the Rust port.
 *
 * <p>The subnet under test is a node gadget in the shape n8n-libpetri compiles: one input edge
 * carrying data or empty, one output with two outgoing edges, a shared budget and a halt.
 *
 * <pre>
 * X/start: one(X/in) one(_budget) one(X/idle) inhibitor(_halt) → X/running
 * X/run:   one(X/running) → and( xor( and( xor(and(e1/data, e2/data), and(e1/empty, e2/empty)), X/routed ),
 *                                     and(_halt, _budget) ),
 *                                X/idle )
 * X/done:  one(X/routed) → and(_budget, X/done)
 * X/skip:  one(X/in_empty) inhibitor(_halt) → and(e1/empty, e2/empty, X/skipped)
 * </pre>
 */
class OpenNetVerificationTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    /** A token-producing action for structural fixtures: it never runs. */
    private static final TransitionAction PRODUCES = TransitionAction.transform(_ -> null);

    private static Place<Object> place(String name) {
        return Place.of(name, Object.class);
    }

    private static final Place<Object> IN = place("X/in");
    private static final Place<Object> IN_EMPTY = place("X/in_empty");
    private static final Place<Object> IDLE = place("X/idle");
    private static final Place<Object> BUDGET = place("_budget");
    private static final Place<Object> HALT = place("_halt");
    private static final Place<Object> RUNNING = place("X/running");
    private static final Place<Object> ROUTED = place("X/routed");
    private static final Place<Object> DONE = place("X/done");
    private static final Place<Object> SKIPPED = place("X/skipped");
    private static final Place<Object> E1_DATA = place("e1/data");
    private static final Place<Object> E1_EMPTY = place("e1/empty");
    private static final Place<Object> E2_DATA = place("e2/data");
    private static final Place<Object> E2_EMPTY = place("e2/empty");
    private static final Place<Object> TRACE = place("X/trace");

    /**
     * @param skipForgetsE2 the skip writes e1's empty but nothing for e2: an edge with neither data nor empty
     * @param runWritesBoth the run's data branch also writes e1's empty
     * @param noRefund      done keeps the budget unit
     * @param leak          the run leaves a token on an internal place nothing consumes
     * @param spin          a transition that can fire forever while the node runs
     * @param timedStart    the start is delayed; the untimed claim must not care
     */
    record Defects(boolean skipForgetsE2, boolean runWritesBoth, boolean noRefund, boolean leak, boolean spin,
                   boolean timedStart) {
        static final Defects NONE = new Defects(false, false, false, false, false, false);

        Defects withSkipForgetsE2() {
            return new Defects(true, runWritesBoth, noRefund, leak, spin, timedStart);
        }

        Defects withRunWritesBoth() {
            return new Defects(skipForgetsE2, true, noRefund, leak, spin, timedStart);
        }

        Defects withNoRefund() {
            return new Defects(skipForgetsE2, runWritesBoth, true, leak, spin, timedStart);
        }

        Defects withLeak() {
            return new Defects(skipForgetsE2, runWritesBoth, noRefund, true, spin, timedStart);
        }

        Defects withSpin() {
            return new Defects(skipForgetsE2, runWritesBoth, noRefund, leak, true, timedStart);
        }

        Defects withTimedStart() {
            return new Defects(skipForgetsE2, runWritesBoth, noRefund, leak, spin, true);
        }
    }

    static PetriNet gadget() {
        return gadget(Defects.NONE);
    }

    static PetriNet gadget(Defects defects) {
        var startBuilder = Transition.builder("X/start")
            .inputs(In.one(IN), In.one(BUDGET), In.one(IDLE)).inhibitor(HALT)
            .outputs(Out.place(RUNNING)).action(PRODUCES);
        if (defects.timedStart()) {
            startBuilder.timing(Timing.delayed(Duration.ofMillis(50)));
        }
        var start = startBuilder.build();
        Out data = defects.runWritesBoth()
            ? Out.and(E1_DATA, E1_EMPTY, E2_DATA)
            : Out.and(E1_DATA, E2_DATA);
        Out routes = Out.xor(data, Out.and(E1_EMPTY, E2_EMPTY));
        Out success = defects.leak()
            ? Out.and(routes, Out.place(ROUTED), Out.place(TRACE))
            : Out.and(routes, Out.place(ROUTED));
        var run = Transition.builder("X/run").inputs(In.one(RUNNING))
            .outputs(Out.and(Out.xor(success, Out.and(HALT, BUDGET)), Out.place(IDLE))).action(PRODUCES).build();
        var done = Transition.builder("X/done").inputs(In.one(ROUTED))
            .outputs(defects.noRefund() ? Out.place(DONE) : Out.and(BUDGET, DONE))
            .action(PRODUCES).build();
        var skip = Transition.builder("X/skip").inputs(In.one(IN_EMPTY)).inhibitor(HALT)
            .outputs(defects.skipForgetsE2()
                ? Out.and(E1_EMPTY, SKIPPED)
                : Out.and(E1_EMPTY, E2_EMPTY, SKIPPED))
            .action(PRODUCES).build();
        var transitions = new ArrayList<>(List.of(start, run, done, skip));
        if (defects.spin()) {
            transitions.add(Transition.builder("X/spin").inputs(In.one(RUNNING))
                .outputs(Out.place(RUNNING)).action(PRODUCES).build());
        }
        return PetriNet.builder("X").transitions(transitions.toArray(new Transition[0])).build();
    }

    /** The node contract as n8n-libpetri states it. */
    record Terms(boolean terminal, int budget, boolean termination) {
        static final Terms DEFAULT = new Terms(true, 1, true);

        Terms withoutTerminal() {
            return new Terms(false, budget, termination);
        }

        Terms withBudget(int k) {
            return new Terms(terminal, k, termination);
        }

        Terms withoutTermination() {
            return new Terms(terminal, budget, false);
        }
    }

    static OpenNetContract contract() {
        return contract(Terms.DEFAULT);
    }

    static OpenNetContract contract(Terms terms) {
        int k = terms.budget();
        var builder = OpenNetContract.builder()
            .initialMarking(m -> m.tokens(IDLE, 1).tokens(BUDGET, k))
            .arrive(1, IN, IN_EMPTY)
            .arriveAtMost(1, HALT)
            .expect("e1", 1, E1_DATA, E1_EMPTY)
            .expect("e2", 1, E2_DATA, E2_EMPTY)
            .expect("idle", 1, IDLE)
            .expect("budget", k, BUDGET)
            .expect("history", 1, DONE, SKIPPED);
        if (terms.terminal()) {
            builder.terminal(HALT, IN, IN_EMPTY);
        }
        if (!terms.termination()) {
            builder.requireTermination(false);
        }
        return builder.build();
    }

    private static OpenNetResult verify(PetriNet net, OpenNetContract c) {
        return OpenNetVerifier.verifyOpenNet(net, c);
    }

    private static final OpenNetOptions SMT_ONLY = OpenNetOptions.DEFAULT.withMaxClasses(0);

    private static List<String> subjects(OpenNetResult r) {
        return r.violations().stream().map(ContractViolation::subject).toList();
    }

    private static String reason(OpenNetResult r) {
        return r.verdict() instanceof Verdict.Unknown(var reason) ? reason : null;
    }

    // ==================== graph route ====================

    @Nested
    class GraphRouteTests {

        @Test
        void provesAWellFormedGadgetHaltsIncluded() {
            var r = verify(gadget(), contract());
            assertTrue(r.isProven(), r.report());
            assertEquals(OpenNetResult.Route.ENUMERATION, r.route());
            assertTrue(r.graphComplete());
            assertEquals(List.of(), r.violations());
            assertTrue(r.report().contains("=== OPEN-NET CONTRACT VERIFICATION (VER-022) ==="));
            assertTrue(r.report().contains("e1 = exactly 1 across {e1/data, e1/empty}"));
            assertTrue(r.report().contains("Terminal: when _halt: X/in, X/in_empty"));
        }

        @Test
        void provesItForABudgetOfTwoAsWell() {
            var r = verify(gadget(), contract(Terms.DEFAULT.withBudget(2)));
            assertTrue(r.isProven(), r.report());
        }

        @Test
        void namesTheEdgeABrokenSkipLeavesWithNeitherDataNorEmptyWithItsPortTrace() {
            var r = verify(gadget(Defects.NONE.withSkipForgetsE2()), contract());
            assertTrue(r.isViolated(), r.report());
            assertEquals(List.of("e2"), subjects(r));
            var v = r.violations().getFirst();
            assertEquals(ContractViolation.Kind.CLAUSE, v.kind());
            assertEquals("exactly 1 across {e2/data, e2/empty} at quiescence, found 0", v.detail());
            assertTrue(v.confirmed());
            // Shortest witness: the empty arrives, the halt is declined, the skip fires.
            assertEquals(List.of("X/skip", "env:arrive[0]:X/in_empty", "env:decline[1]"),
                v.transitions().stream().sorted().toList());
            assertEquals(v.transitions().size() + 1, v.markings().size());
            var skip = v.portTrace().stream().filter(s -> s.transition().equals("X/skip")).findFirst().orElseThrow();
            assertNull(skip.environment());
            assertEquals(List.of(
                new ContractViolation.PortChange("X/in_empty", -1),
                new ContractViolation.PortChange("e1/empty", 1),
                new ContractViolation.PortChange("X/skipped", 1)), skip.changes());
            assertEquals(EnvironmentStep.Kind.ARRIVAL, v.portTrace().stream()
                .filter(s -> s.transition().equals("env:arrive[0]:X/in_empty")).findFirst().orElseThrow().environment());
            var last = v.markings().getLast();
            assertEquals(0, last.tokens(E2_EMPTY) + last.tokens(E2_DATA));
            assertTrue(r.report().contains("[e2] clause: exactly 1 across {e2/data, e2/empty} at quiescence, found 0"));
            assertTrue(r.report().contains("Port trace:"));
        }

        @Test
        void aDeclaredSkipWaivesTheOutputEdgeASkippingNodeNeverWritesAndKeepsItsUpperBound() {
            // The very net the case above calls broken. Whether writing no output edge is a defect
            // or a designed skip is the contract's to say, not the verifier's: a node that can
            // legitimately skip needs its edge clauses conditional on having run, which is what a
            // terminal on X/skipped states. The upper bounds are not waived, so a double write is
            // still caught.
            var declared = OpenNetContract.builder()
                .initialMarking(m -> m.tokens(IDLE, 1).tokens(BUDGET, 1))
                .arrive(1, IN, IN_EMPTY)
                .arriveAtMost(1, HALT)
                .expect("e1", 1, E1_DATA, E1_EMPTY)
                .expect("e2", 1, E2_DATA, E2_EMPTY)
                .expect("idle", 1, IDLE)
                .expect("budget", 1, BUDGET)
                .expect("history", 1, DONE, SKIPPED)
                .terminal(HALT, IN, IN_EMPTY)
                .terminal(SKIPPED)
                .build();
            assertTrue(verify(gadget(Defects.NONE.withSkipForgetsE2()), declared).isProven());
            // Still a violation when the run writes an edge twice: that breaks an upper bound.
            var both = verify(gadget(Defects.NONE.withRunWritesBoth()), declared);
            assertTrue(both.isViolated(), both.report());
            assertEquals(List.of("e1"), subjects(both));
        }

        @Test
        void reportsAnEdgeThatReceivesBothDataAndEmptyAndKeepsThatBoundUnderAHalt() {
            var r = verify(gadget(Defects.NONE.withRunWritesBoth()), contract());
            assertTrue(r.isViolated(), r.report());
            assertEquals(List.of("e1"), subjects(r));
            assertTrue(r.violations().getFirst().detail().contains("found 2"));
        }

        @Test
        void reportsABudgetUnitTheGadgetKeeps() {
            var r = verify(gadget(Defects.NONE.withNoRefund()), contract());
            assertEquals(List.of("budget"), subjects(r), r.report());
            assertEquals("exactly 1 across {_budget} at quiescence, found 0", r.violations().getFirst().detail());
        }

        @Test
        void namesAnInternalPlaceARunLeavesATokenOn() {
            var r = verify(gadget(Defects.NONE.withLeak()), contract());
            assertEquals(List.of(List.of("stranded", "X/trace")),
                r.violations().stream().map(v -> List.of(v.kind().label(), v.subject())).toList(), r.report());
        }

        @Test
        void reportsARunThatNeverComesToRestAsALasso() {
            var r = verify(gadget(Defects.NONE.withSpin()), contract());
            assertEquals(List.of(ContractViolation.Kind.TERMINATION),
                r.violations().stream().map(ContractViolation::kind).toList(), r.report());
            var v = r.violations().getFirst();
            assertTrue(v.cycleStart().isPresent());
            int cycleStart = v.cycleStart().getAsInt();
            assertEquals(List.of("X/spin"), v.transitions().subList(cycleStart, v.transitions().size()));
            assertEquals(Report.markingText(v.markings().get(cycleStart)), Report.markingText(v.markings().getLast()));
            assertTrue(r.report().contains("Firing sequence: env:arrive[0]:X/in, X/start, then repeating X/spin"));
        }

        @Test
        void withTerminationWaivedTheSameSpinningGadgetMeetsItsContract() {
            var r = verify(gadget(Defects.NONE.withSpin()), contract(Terms.DEFAULT.withoutTermination()));
            assertTrue(r.isProven(), r.report());
        }

        @Test
        void makesTheUntimedClaimADelayedStartChangesNothing() {
            var plain = verify(gadget(), contract());
            var timed = verify(gadget(Defects.NONE.withTimedStart()), contract());
            assertTrue(timed.isProven(), timed.report());
            assertEquals(plain.classCount(), timed.classCount());
        }

        @Test
        void withoutADesignedTerminalAHaltStrandsTheArrivalAndWaivesNothing() {
            var r = verify(gadget(), contract(Terms.DEFAULT.withoutTerminal()));
            assertTrue(r.isViolated(), r.report());
            // Clauses in contract order, then stranded places in code-point order.
            assertEquals(List.of("e1", "e2", "history", "X/in", "X/in_empty", "_halt"), subjects(r));
        }

        @Test
        void aClauseOverPlacesTheNetNeverWritesCountsZeroThereAndTheReportSaysSo() {
            var c = OpenNetContract.builder()
                .initialMarking(m -> m.tokens(IDLE, 1).tokens(BUDGET, 1))
                .arrive(1, IN, IN_EMPTY)
                .expect("e1", 1, E1_DATA, E1_EMPTY)
                .expect("e2", 1, E2_DATA, E2_EMPTY)
                .expect("e3", 1, place("e3/data"), place("e3/empty"))
                .expect("idle", 1, IDLE)
                .expect("budget", 1, BUDGET)
                .expect("history", 1, DONE, SKIPPED)
                .rest(HALT)
                .build();
            var r = verify(gadget(), c);
            assertTrue(subjects(r).contains("e3"), r.report());
            assertTrue(r.report().contains("Not declared by the net: e3/data, e3/empty"));
        }

        @Test
        void deliversExactlyNArrivalsAndAtMostNMayDeliverNone() {
            var q = place("q");
            var out = place("out");
            var relay = PetriNet.builder("relay").transitions(
                Transition.builder("t").inputs(In.one(q)).outputs(Out.place(out)).action(PRODUCES).build()
            ).build();
            var exactly = verify(relay, OpenNetContract.builder().arrive(2, q).expect("out", 2, out).build());
            assertTrue(exactly.isProven(), exactly.report());

            var atMost = verify(relay, OpenNetContract.builder().arriveAtMost(2, q).expect("out", 2, out).build());
            assertTrue(atMost.isViolated(), atMost.report());
            assertEquals("exactly 2 across {out} at quiescence, found 0", atMost.violations().getFirst().detail());

            var between = verify(relay,
                OpenNetContract.builder().arriveAtMost(2, q).expectBetween("out", 0, 2, out).build());
            assertTrue(between.isProven(), between.report());
        }

        @Test
        void aGraphThatDoesNotCloseIsUnknownWithoutTheSmtRouteAndSaysWhy() {
            var r = OpenNetVerifier.verifyOpenNet(gadget(), contract(),
                OpenNetOptions.DEFAULT.withMaxClasses(3).withSmt(false));
            assertInstanceOf(Verdict.Unknown.class, r.verdict());
            assertFalse(r.graphComplete());
            assertEquals("the state-class graph did not close within 3 classes, and the SMT route is disabled",
                reason(r));
        }
    }

    // ==================== the closure and the contract ====================

    @Nested
    class ClosureAndContract {

        @Test
        void closesTheNetWithOrdinaryPlacesAndTransitions() {
            var closed = OpenNetClosure.closeOpenNet(gadget(), contract());
            assertEquals(1, closed.initialMarking().tokens(place("env:arrivals[0]")));
            assertEquals(1, closed.initialMarking().tokens(place("env:optional[1]")));
            assertEquals(1, closed.initialMarking().tokens(IDLE));
            assertEquals(List.of(
                "env:arrive[0]:X/in", "env:arrive[0]:X/in_empty", "env:arrive?[1]:_halt", "env:decline[1]"),
                List.copyOf(closed.environment().keySet()));
            assertEquals(new EnvironmentStep.Decline(1), closed.environment().get("env:decline[1]"));
            assertEquals(List.of(), closed.undeclared());
            assertEquals(1, closed.net().places().stream().filter(p -> p.name().equals("X/in")).count());
        }

        @Test
        void refusesANetWhoseNamesTheClosureWouldReuse() {
            var clash = PetriNet.builder("clash").transitions(
                Transition.builder("t").inputs(In.one(place("env:arrivals[0]"))).build()
            ).build();
            var e = assertThrows(IllegalArgumentException.class,
                () -> OpenNetClosure.closeOpenNet(clash, OpenNetContract.builder().arrive(1, place("q")).build()));
            assertTrue(e.getMessage().contains("already declares"), e.getMessage());
        }

        @Test
        void validatesTheContractAsItIsBuilt() {
            assertMessage("max >= 1", () -> OpenNetContract.builder().arriveAtMost(0, IN));
            assertMessage("0 <= min <= max", () -> OpenNetContract.builder().arriveBetween(2, 1, IN));
            // The reference passes `Infinity`, which an `int` cannot hold; a negative count is the
            // bound a Java caller can get wrong, and the message says why a bound is finite.
            assertMessage("finite", () -> OpenNetContract.builder().arrive(-1, IN));
            assertMessage("names no place", () -> OpenNetContract.builder().arrive(1));
            assertMessage("duplicate clause name 'a'",
                () -> OpenNetContract.builder().expect("a", 1, IDLE).expect("a", 1, BUDGET));
            assertMessage("0 <= min <= max", () -> OpenNetContract.builder().expectBetween("a", 2, 1, IDLE));
            assertMessage("needs a name", () -> OpenNetContract.builder().expect("", 1, IDLE));
        }

        @Test
        void phrasesCountsTheWayTheReportPrintsThem() {
            assertEquals("exactly 1", SmtProperty.countPhrase(1, OptionalInt.of(1)));
            assertEquals("at most 1", SmtProperty.countPhrase(0, OptionalInt.of(1)));
            assertEquals("at least 2", SmtProperty.countPhrase(2, OptionalInt.empty()));
            assertEquals("any number", SmtProperty.countPhrase(0, OptionalInt.empty()));
            assertEquals("between 1 and 3", SmtProperty.countPhrase(1, OptionalInt.of(3)));
        }

        @Test
        void listsThePortsInFirstMentionOrderMarkersIncluded() {
            assertEquals(List.of(
                "X/idle", "_budget", "X/in", "X/in_empty", "_halt", "e1/data", "e1/empty", "e2/data", "e2/empty",
                "X/done", "X/skipped"), contract().places().stream().map(Place::name).toList());
        }

        @Test
        void keepsTheInitialTokensInTheOrderTheyWereNamed() {
            // Every form keeps the order a caller states, as the reference's marking builder does:
            // "_budget" before "X/idle" although "X/idle" comes first by code point.
            var named = OpenNetContract.builder().initialTokens(BUDGET, 1).initialTokens(IDLE, 1)
                .initialTokens(BUDGET, 2).build();
            assertEquals(List.of("_budget", "X/idle"), named.places().stream().map(Place::name).toList());
            assertEquals(2, named.initialMarking().tokens(BUDGET));
            var configured = OpenNetContract.builder().initialMarking(m -> m.tokens(BUDGET, 1).tokens(IDLE, 1)).build();
            assertEquals(List.of("_budget", "X/idle"), configured.places().stream().map(Place::name).toList());
            var marking = OpenNetContract.builder()
                .initialMarking(MarkingState.builder().tokens(BUDGET, 1).tokens(IDLE, 1).build()).build();
            assertEquals(List.of("_budget", "X/idle"), marking.places().stream().map(Place::name).toList());
        }

        /**
         * The port trace lists a firing's changes in the contract's order, which starts with the
         * initial marking's: {@code b} before {@code a}, as the reference prints it.
         */
        @Test
        void listsAPortTracesChangesInTheInitialMarkingsOrder() {
            var a = place("a");
            var b = place("b");
            var out = place("out");
            var pair = PetriNet.builder("pair").transitions(
                Transition.builder("t").inputs(In.one(b), In.one(a)).outputs(Out.place(out)).action(PRODUCES).build()
            ).build();
            var configured = OpenNetContract.builder()
                .initialMarking(m -> m.tokens(b, 1).tokens(a, 1)).expect("out", 2, out).build();
            var marking = OpenNetContract.builder()
                .initialMarking(MarkingState.builder().tokens(b, 1).tokens(a, 1).build()).expect("out", 2, out).build();
            for (var c : List.of(configured, marking)) {
                var r = verify(pair, c);
                assertEquals(List.of("out"), subjects(r), r.report());
                assertTrue(r.report().contains("      1. t  b -1, a -1, out +1\n"), r.report());
            }
        }

        @Test
        void registersAnArcLessExcusedPlaceSoBothRoutesResolveIt() {
            var c = OpenNetContract.builder()
                .initialTokens(IDLE, 1)
                .initialTokens(BUDGET, 1)
                .arrive(1, IN, IN_EMPTY)
                .arriveAtMost(1, HALT)
                .expect("history", 1, DONE, SKIPPED)
                .terminal(HALT, IN, IN_EMPTY, place("ghost"))
                .rest(place("ghost2"))
                .build();
            var closed = OpenNetClosure.closeOpenNet(gadget(), c);
            assertEquals(List.of("ghost2", "ghost"), closed.undeclared());
            assertTrue(closed.net().places().stream().anyMatch(p -> p.name().equals("ghost")));
            var r = verify(gadget(), c);
            assertTrue(r.report().contains(
                "Not declared by the net: ghost2, ghost (no arc touches them; a clause there counts zero)"), r.report());
        }

        @Test
        void resolvesContractPlacesByNameWhateverTheirTokenType() {
            // The reference keys places by name. A contract that names the gadget's places with
            // another token type still means those places, so the verdict is the same.
            var typed = OpenNetContract.builder()
                .initialMarking(m -> m.tokens(Place.of("X/idle", String.class), 1)
                    .tokens(Place.of("_budget", String.class), 1))
                .arrive(1, Place.of("X/in", String.class), Place.of("X/in_empty", String.class))
                .arriveAtMost(1, Place.of("_halt", String.class))
                .expect("e1", 1, Place.of("e1/data", String.class), Place.of("e1/empty", String.class))
                .expect("e2", 1, Place.of("e2/data", String.class), Place.of("e2/empty", String.class))
                .expect("idle", 1, Place.of("X/idle", String.class))
                .expect("budget", 1, Place.of("_budget", String.class))
                .expect("history", 1, Place.of("X/done", String.class), Place.of("X/skipped", String.class))
                .terminal(Place.of("_halt", String.class), Place.of("X/in", String.class),
                    Place.of("X/in_empty", String.class))
                .build();
            var closed = OpenNetClosure.closeOpenNet(gadget(), typed);
            assertEquals(List.of(), closed.undeclared());
            assertEquals(1, closed.initialMarking().tokens(IDLE));
            var r = verify(gadget(), typed);
            assertTrue(r.isProven(), r.report());
            assertEquals(verify(gadget(), contract()).report(), r.report());
        }
    }

    private static void assertMessage(String fragment, org.junit.jupiter.api.function.Executable build) {
        var e = assertThrows(IllegalArgumentException.class, build);
        assertTrue(e.getMessage().contains(fragment), e.getMessage());
    }

    // ==================== environment transitions ====================

    // A node that asks its environment and runs again on every answer: N/run either finishes or
    // sends a request; the environment answers at most twice, from a budget of its own, or ends.
    private static final Place<Object> N_IN = place("N/in");
    private static final Place<Object> N_RUNNING = place("N/running");
    private static final Place<Object> N_REQUEST = place("N/request");
    private static final Place<Object> N_REPLY = place("N/reply");
    private static final Place<Object> N_DONE = place("N/done");
    private static final Place<Object> ROUNDS = place("env/rounds");
    private static final Place<Object> ENDED = place("env/ended");

    static PetriNet node() {
        return PetriNet.builder("N").transitions(
            Transition.builder("N/start").inputs(In.one(N_IN)).outputs(Out.place(N_RUNNING)).action(PRODUCES).build(),
            Transition.builder("N/resume").inputs(In.one(N_REPLY)).outputs(Out.place(N_RUNNING)).action(PRODUCES).build(),
            Transition.builder("N/run").inputs(In.one(N_RUNNING)).outputs(Out.xor(Out.place(N_REQUEST), Out.place(N_DONE)))
                .action(PRODUCES).build()
        ).build();
    }

    // No actions: an environment transition never runs, so passthrough() is fine even with outputs.
    private static final Transition AGAIN = Transition.builder("env/again")
        .inputs(In.one(N_REQUEST), In.one(ROUNDS)).outputs(Out.place(N_REPLY)).build();
    private static final Transition END = Transition.builder("env/end")
        .inputs(In.one(N_REQUEST)).outputs(Out.place(ENDED)).build();

    static OpenNetContract nodeContract(int doneAtLeast) {
        return OpenNetContract.builder()
            .initialMarking(m -> m.tokens(ROUNDS, 2))
            .arrive(1, N_IN)
            .expectBetween("done", doneAtLeast, 1, N_DONE)
            .environment(AGAIN, END)
            .build();
    }

    /** {@link #nodeContract} with env/again and env/end on {@code Place<String>}s named like the node's places. */
    static OpenNetContract stringTypedNodeContract(int doneAtLeast) {
        var request = Place.of("N/request", String.class);
        var again = Transition.builder("env/again")
            .inputs(In.one(request), In.one(Place.of("env/rounds", String.class)))
            .outputs(Out.place(Place.of("N/reply", String.class))).build();
        var end = Transition.builder("env/end")
            .inputs(In.one(request)).outputs(Out.place(Place.of("env/ended", String.class))).build();
        return OpenNetContract.builder()
            .initialMarking(m -> m.tokens(ROUNDS, 2))
            .arrive(1, N_IN)
            .expectBetween("done", doneAtLeast, 1, N_DONE)
            .environment(again, end)
            .build();
    }

    /** A node that asks its environment once and finishes on the answer. */
    static PetriNet askOnce() {
        return PetriNet.builder("N").transitions(
            Transition.builder("N/start").inputs(In.one(N_IN)).outputs(Out.place(place("N/running1"))).action(PRODUCES).build(),
            Transition.builder("N/ask").inputs(In.one(place("N/running1"))).outputs(Out.place(N_REQUEST)).action(PRODUCES).build(),
            Transition.builder("N/resume").inputs(In.one(N_REPLY)).outputs(Out.place(place("N/running2"))).action(PRODUCES).build(),
            Transition.builder("N/finish").inputs(In.one(place("N/running2"))).outputs(Out.place(N_DONE)).action(PRODUCES).build()
        ).build();
    }

    /**
     * {@link #askOnce} must never finish, against an environment that answers: violated. The
     * answer is on {@code Place<String>}s named like the node's places when {@code stringTyped}.
     */
    static OpenNetContract neverFinishes(boolean stringTyped) {
        var answer = stringTyped
            ? Transition.builder("env/answer").inputs(In.one(Place.of("N/request", String.class)))
                .outputs(Out.place(Place.of("N/reply", String.class))).build()
            : Transition.builder("env/answer").inputs(In.one(N_REQUEST)).outputs(Out.place(N_REPLY)).build();
        return OpenNetContract.builder()
            .arrive(1, N_IN)
            .expectBetween("done", 0, 0, N_DONE)
            .rest(N_REQUEST, N_REPLY)
            .environment(answer)
            .build();
    }

    @Nested
    class EnvironmentTransitions {

        @Test
        void provesANodeAgainstAnEnvironmentThatAnswersWhatItSendsAndNeverStrandsTheEnvironment() {
            var r = verify(node(), nodeContract(0));
            // env/rounds keeps what the environment did not spend and env/ended keeps the ended
            // exchanges: both are the environment's own places, so neither is stranded.
            assertTrue(r.isProven(), r.report());
            assertTrue(r.report().contains("Environment transitions: env/again, env/end"));
        }

        @Test
        void marksTheEnvironmentTransitionsInThePortTrace() {
            var r = verify(node(), nodeContract(1));
            assertEquals(List.of("done"), subjects(r), r.report());
            var step = r.violations().getFirst().portTrace().stream()
                .filter(s -> s.transition().equals("env/end")).findFirst().orElseThrow();
            assertEquals(EnvironmentStep.Kind.TRANSITION, step.environment());
            assertEquals(List.of(
                new ContractViolation.PortChange("N/request", -1),
                new ContractViolation.PortChange("env/ended", 1)), step.changes());
            assertTrue(Pattern.compile("\\d+\\. env/end \\[environment\\] {2}N/request -1, env/ended \\+1")
                .matcher(r.report()).find(), r.report());
        }

        @Test
        void keepsTheEnvironmentsOwnPlacesApartAndOutOfTheUndeclaredList() {
            var closed = OpenNetClosure.closeOpenNet(node(), nodeContract(0));
            assertEquals(new EnvironmentStep.Transition(), closed.environment().get("env/again"));
            assertEquals(List.of("env/ended", "env/rounds"),
                closed.environmentPlaces().stream().map(Place::name).sorted().toList());
            assertEquals(List.of(), closed.undeclared());
        }

        @Test
        void refusesAnEnvironmentTransitionNamedLikeOneOfTheNetsOrDeclaredTwice() {
            var clash = Transition.builder("N/run").inputs(In.one(N_REQUEST)).build();
            var e = assertThrows(IllegalArgumentException.class, () -> OpenNetClosure.closeOpenNet(node(),
                OpenNetContract.builder().arrive(1, N_IN).environment(clash).build()));
            assertTrue(e.getMessage().contains("already declares"), e.getMessage());
            assertMessage("duplicate environment transition 'env/end'",
                () -> OpenNetContract.builder().environment(END, END));
        }

        @Test
        void resolvesAnEnvironmentTransitionsPlacesByNameWhateverTheirTokenType() {
            // The reference keys places by name, so an environment transition on String-typed
            // places named like the node's Object-typed ones touches the node's places. Keyed by
            // Place equality it would touch a second N/request the node never marks: the node's
            // request would strand, and an answer on the second N/reply could never resume it.
            var closed = OpenNetClosure.closeOpenNet(node(), stringTypedNodeContract(0));
            for (var name : List.of("N/request", "N/reply", "env/rounds")) {
                assertEquals(1, closed.net().places().stream().filter(p -> p.name().equals(name)).count(), name);
            }
            var proven = verify(node(), stringTypedNodeContract(0));
            assertTrue(proven.isProven(), proven.report());
            assertEquals(verify(node(), nodeContract(0)).report(), proven.report());
            assertEquals(verify(node(), nodeContract(1)).report(), verify(node(), stringTypedNodeContract(1)).report());

            var violated = verify(askOnce(), neverFinishes(true));
            assertEquals(List.of("done"), subjects(violated), violated.report());
            assertEquals(verify(askOnce(), neverFinishes(false)).report(), violated.report());
        }

        @Test
        @EnabledIf("org.libpetri.smt.opennet.OpenNetVerificationTest#z3Available")
        void resolvesAnEnvironmentTransitionsPlacesByNameOnTheSmtRouteToo() {
            var proven = OpenNetVerifier.verifyOpenNet(node(), stringTypedNodeContract(0), SMT_ONLY);
            assertTrue(proven.isProven(), proven.report());
            assertEquals(OpenNetVerifier.verifyOpenNet(node(), nodeContract(0), SMT_ONLY).report(), proven.report());

            var violated = OpenNetVerifier.verifyOpenNet(askOnce(), neverFinishes(true), SMT_ONLY);
            assertEquals(List.of("done"), subjects(violated), violated.report());
            assertEquals(OpenNetVerifier.verifyOpenNet(askOnce(), neverFinishes(false), SMT_ONLY).report(),
                violated.report());
        }

        /**
         * The report is byte-identical to the reference's for the same net and contract: this is
         * its text, markings in {@code localeCompare} order and the port trace in the contract's
         * first-mention order.
         */
        @Test
        void reportMatchesTheReferenceForAnEnvironmentStepInThePortTrace() {
            var r = verify(node(), nodeContract(1));
            assertEquals("""
                === OPEN-NET CONTRACT VERIFICATION (VER-022) ===

                Net: N, closed by 3 environment transitions over 1 arrival groups
                Contract:
                  Initial marking: {env/rounds:2}
                  Arrivals: exactly 1 onto {N/in}
                  At quiescence: done = exactly 1 across {N/done}
                  Environment transitions: env/again, env/end
                  Termination: every run comes to rest

                === State-class graph (untimed, priority-blind) ===
                  Classes: 16, closed

                === RESULT ===
                VIOLATED: 1 part of the contract broken
                  [done] clause: exactly 1 across {N/done} at quiescence, found 0
                    Port trace:
                      1. env:arrive[0]:N/in [environment arrival]  N/in +1
                      2. N/start  N/in -1
                      3. N/run  N/request +1
                      4. env/end [environment]  N/request -1, env/ended +1
                    Firing sequence: env:arrive[0]:N/in, N/start, N/run, env/end
                    Quiescent marking: {env/ended:1, env/rounds:2}""", r.report());
        }
    }

    // ==================== the report ====================

    @Nested
    class ReportText {

        /** A lasso whose stem is an arrival: the port trace marks where the cycle starts, and the firing sequence says what repeats. */
        @Test
        void reportMatchesTheReferenceForALasso() {
            var a = place("a");
            var b = place("b");
            var ping = PetriNet.builder("ping").transitions(
                Transition.builder("t1").inputs(In.one(a)).outputs(Out.place(b)).action(PRODUCES).build(),
                Transition.builder("t2").inputs(In.one(b)).outputs(Out.place(a)).action(PRODUCES).build()
            ).build();
            var c = OpenNetContract.builder().arrive(1, a).expectBetween("ab", 0, OptionalInt.empty(), a, b).build();
            assertEquals("""
                === OPEN-NET CONTRACT VERIFICATION (VER-022) ===

                Net: ping, closed by 1 environment transitions over 1 arrival groups
                Contract:
                  Initial marking: {}
                  Arrivals: exactly 1 onto {a}
                  At quiescence: ab = any number across {a, b}
                  Termination: every run comes to rest

                === State-class graph (untimed, priority-blind) ===
                  Classes: 3, closed

                === RESULT ===
                VIOLATED: 1 part of the contract broken
                  [termination] termination: a run can repeat t1 → t2 forever without coming to rest
                    Port trace:
                      1. env:arrive[0]:a [environment arrival]  a +1
                      -- the cycle starts here --
                      2. t1  a -1, b +1
                      3. t2  a +1, b -1
                    Firing sequence: env:arrive[0]:a, then repeating t1, t2
                    Marking on the cycle: {a:1}""", verify(ping, c).report());
        }

        /** The order Node's {@code localeCompare} gives these names: the reference's {@code MarkingState.toString} order. */
        @Test
        void markingTextListsPlacesInLocaleOrder() {
            var m = MarkingState.builder()
                .tokens(place("X/in"), 1)
                .tokens(place("_halt"), 1)
                .tokens(place("env:arrivals[0]"), 1)
                .tokens(place("x/in"), 1)
                .tokens(place("X/In"), 1)
                .tokens(place("env/ended"), 1)
                .tokens(place("e1/data"), 2)
                .tokens(place("N/in"), 1)
                .tokens(place("X/in_empty"), 1)
                .tokens(place("_budget"), 1)
                .build();
            assertEquals(
                "{_budget:1, _halt:1, e1/data:2, env:arrivals[0]:1, env/ended:1, N/in:1, x/in:1, X/in:1, X/In:1, X/in_empty:1}",
                Report.markingText(m));
            assertEquals("{}", Report.markingText(MarkingState.empty()));
        }

        /** Every printable ASCII character alone, sorted, as Node sorts it. */
        @Test
        void localeOrderMatchesTheReferenceOnPrintableAscii() {
            var chars = new ArrayList<String>();
            for (char c = 32; c < 127; c++) {
                chars.add(String.valueOf(c));
            }
            chars.sort(Report::localeOrder);
            assertEquals(" _-,;:!?.'\"()[]{}@*/\\&#%`^+<=>|~$0123456789aAbBcCdDeEfFgGhHiIjJkKlLmMnNoOpPqQrRsStTuUvVwWxXyYzZ",
                String.join("", chars));
            var words = new ArrayList<>(List.of("ab1", "AB", "Ab", "aB", "ab", "a1b", "a/b", "a-b", "a_b", "a b"));
            words.sort(Report::localeOrder);
            assertEquals(List.of("a b", "a_b", "a-b", "a/b", "a1b", "ab", "aB", "Ab", "AB", "ab1"), words);
        }
    }

    // ==================== untimed exploration (VER-004, used by VER-022) ====================

    @Test
    void untimedExplorationReachesAMarkingTheTimingExcludes() {
        var p = place("p");
        var a = place("a");
        var b = place("b");
        var t1 = Transition.builder("t1").inputs(In.one(p)).outputs(Out.place(a))
            .timing(Timing.deadline(Duration.ofMillis(5))).action(PRODUCES).build();
        var t2 = Transition.builder("t2").inputs(In.one(p)).outputs(Out.place(b))
            .timing(Timing.delayed(Duration.ofMillis(10))).action(PRODUCES).build();
        var net = PetriNet.builder("race").transitions(t1, t2).build();
        var m0 = MarkingState.builder().tokens(p, 1).build();
        var timed = StateClassGraph.build(net, m0, 100);
        var untimed = StateClassGraph.build(net, m0, 100, Set.of(), EnvironmentAnalysisMode.ignore(),
            StateClassGraph.Options.UNTIMED);
        assertFalse(timed.stateClasses().stream().anyMatch(sc -> sc.marking().hasTokens(b)));
        assertTrue(untimed.stateClasses().stream().anyMatch(sc -> sc.marking().hasTokens(b)));
    }

    // ==================== a ν-net skips the name-blind graph ====================

    // Two independent mints give COL_A and COL_B different names, so the ν-join can never fire and
    // both strand. The state-class graph ignores the match, fires the join anyway, and used to
    // report this contract proven by enumeration — a false proof. SmtVerifier says violated.
    private static final Place<Object> SEED_A = place("SEED_A");
    private static final Place<Object> SEED_B = place("SEED_B");
    private static final Place<String> COL_A = Place.of("COL_A", String.class);
    private static final Place<String> COL_B = Place.of("COL_B", String.class);
    private static final Place<String> OUT = Place.of("OUT", String.class);

    static PetriNet twoMints() {
        return PetriNet.builder("twoMints").transitions(
            Transition.builder("MINT_A").inputs(In.one(SEED_A)).outputs(Out.place(COL_A)).action(PRODUCES).build(),
            Transition.builder("MINT_B").inputs(In.one(SEED_B)).outputs(Out.place(COL_B)).action(PRODUCES).build(),
            Transition.builder("JOIN").inputs(In.one(COL_A), In.one(COL_B))
                .match(MatchSpec.builder().key(COL_A, (String s) -> NameId.of(s)).key(COL_B, (String s) -> NameId.of(s)).build())
                .outputs(Out.place(OUT)).action(PRODUCES).build()
        ).build();
    }

    static OpenNetContract twoMintsContract() {
        return OpenNetContract.builder()
            .initialMarking(m -> m.tokens(SEED_A, 1).tokens(SEED_B, 1))
            .rest(OUT)
            .build();
    }

    @Nested
    class NuNet {

        @Test
        @EnabledIf("org.libpetri.smt.opennet.OpenNetVerificationTest#z3Available")
        void doesNotProveAJoinThatCanNeverMatchAndSaysWhyItSkippedTheGraph() {
            var r = verify(twoMints(), twoMintsContract());
            assertTrue(r.isViolated(), r.report());
            assertEquals(OpenNetResult.Route.SMT, r.route());
            assertEquals(0, r.classCount());
            assertTrue(r.report().contains(
                "State-class graph: skipped (the closed net declares match (ν-join) transitions, which the graph does not model)"),
                r.report());
        }

        @Test
        void isUnknownNamingTheReasonWhenTheSmtRouteIsDisabled() {
            var r = OpenNetVerifier.verifyOpenNet(twoMints(), twoMintsContract(), OpenNetOptions.DEFAULT.withSmt(false));
            assertInstanceOf(Verdict.Unknown.class, r.verdict());
            assertTrue(reason(r).contains(
                "the state-class graph was skipped: the closed net declares match (ν-join) transitions"), reason(r));
        }
    }

    // ==================== SMT route ====================

    @Nested
    @EnabledIf("org.libpetri.smt.opennet.OpenNetVerificationTest#z3Available")
    class SmtRouteTests {

        @Test
        void withTerminationWaivedProvesTheWellFormedGadgetThroughExistingProperties() {
            var r = OpenNetVerifier.verifyOpenNet(gadget(), contract(Terms.DEFAULT.withoutTermination()), SMT_ONLY);
            assertTrue(r.isProven(), r.report());
            assertEquals(OpenNetResult.Route.SMT, r.route());
            assertTrue(r.report().contains("=== SMT route ==="));
            assertTrue(r.report().contains("State-class graph: skipped"));
        }

        @Test
        void decidesTerminationByAFiringBoundWhenTheGraphIsNotBuilt() {
            var r = OpenNetVerifier.verifyOpenNet(gadget(), contract(), SMT_ONLY);
            assertTrue(r.isProven(), r.report());
            assertTrue(Pattern.compile("\\[termination] Firing bound \\(VER-019\\): every run has at most \\d+ firings")
                .matcher(r.report()).find(), r.report());
        }

        @Test
        void leavesTerminationUndecidedWhenNoFiringBoundExistsAndNamesWhatRepeats() {
            var r = OpenNetVerifier.verifyOpenNet(gadget(Defects.NONE.withSpin()), contract(), SMT_ONLY);
            assertInstanceOf(Verdict.Unknown.class, r.verdict(), r.report());
            assertTrue(reason(r).contains("termination: no firing bound: the marking equation lets X/spin repeat"),
                reason(r));
        }

        @Test
        void namesTheBrokenEdgeOnTheSmtRouteToo() {
            var r = OpenNetVerifier.verifyOpenNet(gadget(Defects.NONE.withSkipForgetsE2()),
                contract(Terms.DEFAULT.withoutTermination()), SMT_ONLY);
            assertTrue(r.isViolated(), r.report());
            assertEquals(OpenNetResult.Route.SMT, r.route());
            assertTrue(subjects(r).contains("e2"), r.report());
        }

        @Test
        void decidesALowerBoundAbove1ThroughTheQuiescentCount() {
            var r = OpenNetVerifier.verifyOpenNet(gadget(), contract(Terms.DEFAULT.withBudget(2)), SMT_ONLY);
            assertTrue(r.isProven(), r.report());
            assertTrue(r.report().contains(
                "[budget] Quiescent count: exactly 2 across {_budget}; lower bound waived while {_halt} is marked: proven"),
                r.report());
        }

        @Test
        void carriesTheCertificatesItsProvenQueriesReturnedLabelledByContractPart() {
            var r = OpenNetVerifier.verifyOpenNet(gadget(), contract(Terms.DEFAULT.withoutTermination()), SMT_ONLY);
            assertTrue(r.isProven(), r.report());
            // The proof evidence is the conjunction of the parts' invariants, not nothing.
            String invariant = r.verdict() instanceof Verdict.Proven(var _, var inv) ? inv : null;
            assertNotNull(invariant, r.report());
            assertTrue(invariant.contains("[stranding]"), invariant);
        }

        @Test
        void skipsACountClauseNoMarkingCanFailAndSaysSoRatherThanGoingSilent() {
            var anything = OpenNetContract.builder()
                .initialMarking(m -> m.tokens(IDLE, 1).tokens(BUDGET, 1))
                .arrive(1, IN, IN_EMPTY)
                .arriveAtMost(1, HALT)
                .expect("e1", 1, E1_DATA, E1_EMPTY)
                .expect("e2", 1, E2_DATA, E2_EMPTY)
                .expect("idle", 1, IDLE)
                .expect("budget", 1, BUDGET)
                // Between 0 and ∞ across the history places: every marking satisfies it.
                .expectBetween("history", 0, OptionalInt.empty(), DONE, SKIPPED)
                .terminal(HALT, IN, IN_EMPTY)
                .requireTermination(false)
                .build();
            var r = OpenNetVerifier.verifyOpenNet(gadget(), anything, SMT_ONLY);
            assertTrue(r.isProven(), r.report());
            assertTrue(r.report().contains(
                "[history] any number across {X/done, X/skipped} at quiescence: proven (no query needed)"), r.report());
        }

        @Test
        void namesTheStrandedPlaceOnTheSmtRouteTooWithTheSameWideningTheGraphApplies() {
            // The stranding attribution is the one predicate the two routes compute by different
            // means, and getting it wrong is how a per-place row reports a stranding the complete
            // graph proves cannot happen: it has to ask "marked AND unexcused", not "marked". The
            // graph route reaches the same verdict on this gadget above, so the two are diffable.
            var r = OpenNetVerifier.verifyOpenNet(gadget(Defects.NONE.withLeak()),
                contract(Terms.DEFAULT.withoutTermination()), SMT_ONLY);
            assertTrue(r.isViolated(), r.report());
            assertEquals(OpenNetResult.Route.SMT, r.route());
            assertEquals(List.of(List.of("stranded", "X/trace")),
                r.violations().stream().map(v -> List.of(v.kind().label(), v.subject())).toList(), r.report());
            // Nothing excused by the terminal is named: _halt's excused arrivals may rest.
            assertTrue(r.violations().getFirst().detail().contains("X/trace holds a token at quiescence"));
        }

        @Test
        void reportsTheCountABrokenGadgetLeavesFoundByTheSolver() {
            var r = OpenNetVerifier.verifyOpenNet(gadget(Defects.NONE.withNoRefund()),
                contract(Terms.DEFAULT.withoutTermination()), SMT_ONLY);
            assertTrue(r.isViolated(), r.report());
            var budget = r.violations().stream().filter(v -> v.subject().equals("budget")).findFirst().orElseThrow();
            assertTrue(budget.detail().startsWith("exactly 1 across {_budget} at quiescence"), budget.detail());
        }
    }
}
