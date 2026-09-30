package org.libpetri.smt.opennet;

import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.internal.TerminalEncoding;
import org.libpetri.analysis.InFlight;
import org.libpetri.core.internal.VerificationDeadline;
import org.libpetri.smt.Reaping;
import org.libpetri.smt.SmtVerifier;
import org.libpetri.smt.SmtVerificationResult.Verdict;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import org.libpetri.smt.encoding.NetFlattener;

/**
 * A subnet verified on its own against a contract, with its ports played by the environment
 * ([VER-022]).
 *
 * <p>The subnet is closed with the environment its contract describes
 * ({@link OpenNetClosure#closeOpenNet}), and the closed net's untimed state-class graph is
 * enumerated. When the graph closes, the verdict is exact. When it does not, a violation found
 * among the explored classes is still real, and the rest of the contract goes to the SMT
 * pipeline, through the properties it already has.
 *
 * <p>A caller that builds its nets from a fixed vocabulary of subnets gets one proof per
 * subnet, and each proof costs what the subnet costs rather than what the interleavings of the
 * whole net cost. Turning those proofs into a claim about the composed net is the caller's own
 * theorem; this entry proves the pieces.
 *
 * <pre>{@code
 * OpenNetResult result = OpenNetVerifier.verifyOpenNet(net, contract);
 * if (!result.isProven()) {
 *     System.out.println(result.report());
 * }
 * }</pre>
 */
public final class OpenNetVerifier {

    private OpenNetVerifier() {}

    private static final String METHOD_ENUMERATION = "open-net contract by state-space enumeration (VER-022)";
    private static final String METHOD_SMT = "open-net contract by the SMT pipeline (VER-022)";

    /** Why the graph was not built on a net with match transitions. Report text, so identical to the reference's. */
    private static final String GRAPH_SKIPPED_MATCH =
        "the closed net declares match (ν-join) transitions, which the graph does not model";
    /** Why the graph was not built when the class budget is zero. */
    private static final String GRAPH_SKIPPED_BUDGET = "class budget 0";
    /** Why the graph was not built on a net whose in-flight actions the split cannot express. */
    private static final String GRAPH_SKIPPED_IN_FLIGHT =
        "the closed net has in-flight actions the verifier cannot split (VER-004)";

    /** {@link #verifyOpenNet(PetriNet, OpenNetContract, OpenNetOptions)} with {@link OpenNetOptions#DEFAULT}. */
    public static OpenNetResult verifyOpenNet(PetriNet net, OpenNetContract contract) {
        return verifyOpenNet(net, contract, OpenNetOptions.DEFAULT);
    }

    /**
     * Verifies {@code net} in isolation against {@code contract} ([VER-022]).
     *
     * <p>{@code Proven} means that, in every run of the environment the contract assumes, every
     * quiescent marking meets the contract, and (unless termination is waived) every run comes
     * to rest. The claim is untimed, priority-blind and value-blind, like every route's
     * ([VER-004]). {@code Violated} lists every broken part with a shortest witness, and
     * {@code Unknown} says why neither route decided.
     *
     * @throws IllegalStateException    when the net violates [CORE-043], as every verifier does
     * @throws IllegalArgumentException when the closure's names collide with the net's, or when the
     *     {@code configureSmt} hook declares a mint transition or a carrier place the closed net
     *     does not have (checked on a probe verifier before either route runs, [NU-010])
     */
    public static OpenNetResult verifyOpenNet(PetriNet net, OpenNetContract contract, OpenNetOptions options) {
        long start = System.nanoTime();
        var closed = OpenNetClosure.closeOpenNet(net, contract);
        // [NU-051] / [NU-010]: the carrier places and mint transitions a configureSmt hook declares,
        // read off a probe verifier of the closed net. The split below refuses a writer into a
        // carrier as the SMT route's own would, and a declared mint that is not in the net is
        // rejected here, before either route runs, as SmtVerifier.mintTransitions rejects it.
        var carriers = options.configureSmt().apply(SmtVerifier.forNet(closed.net())).configuredCarrierPlaces();
        // [VER-004]: a transition whose output another tests non-monotonically is verified as a
        // start and a completion step. The environment's steps stay atomic. Before the terminal
        // rewrite, so a terminal counts as a test, inhibits the completion steps too and excuses
        // the in-flight places.
        var environment = closed.environment().keySet();
        String inFlightLine = null;
        String inFlightRefusal = null;
        if (options.assumeAtomicFiring()) {
            var split = InFlight.transitions(closed.net(), environment);
            if (!split.isEmpty()) {
                inFlightLine = InFlight.atomicAssumptionNote(split);
            }
        } else {
            switch (InFlight.split(closed.net(), carriers, environment)) {
                case InFlight.Outcome.Atomic _ -> {}
                case InFlight.Outcome.Split(var rewritten, var split) -> {
                    closed = closed.withNet(rewritten);
                    inFlightLine = InFlight.splitNote(split);
                }
                case InFlight.Outcome.Refused(var reason) -> inFlightRefusal = reason;
            }
        }
        // EXEC-042 / VER-014: the net's own terminal places, applied without the caller
        // restating them. Each inhibits every transition of the closed net (the environment's
        // too: after a terminal stop the runtime admits nothing), and is merged as a designed
        // terminal excusing every place of the closed net.
        if (!closed.net().terminals().isEmpty()) {
            contract = contract.withDesignedTerminals(closed.net().terminals(),
                NetFlattener.declaredPlaces(closed.net()));
            closed = closed.withNet(TerminalEncoding.inhibited(closed.net()));
        }
        int maxClasses = options.maxClasses();
        // [TIME-013]: the closed net's reapable transitions, named before the SMT route strips its
        // timing; none are read so under `assumeNoReaping`.
        Set<String> reapableInNet = Reaping.reapableTransitions(closed.net());
        Set<String> reapable = options.assumeNoReaping() ? Set.of() : reapableInNet;
        String reapingLine = reapableInNet.isEmpty() ? null
            : options.assumeNoReaping() ? Reaping.noReapingAssumptionNote(reapableInNet)
            : Reaping.reapAwareNote(reapableInNet);
        String reaping = reapingLine == null ? inFlightLine
            : inFlightLine == null ? reapingLine
            : reapingLine + "\n" + inFlightLine;
        // Every place a port trace may mention: the contract's own, plus the closure's. [VER-022]
        // reserves "port" for a place the environment shares with the subnet, which is narrower.
        List<Place<?>> tracedPlaces = closed.canonical(contract.places());
        // The graph is name-blind: it fires a ν-join on any two tokens, whether or not their
        // names match. For a quiescence contract that is no approximation in either direction — it
        // reaches markings the net cannot (the join's output) and misses ones it does (the inputs
        // a join that cannot match leaves stranded), so neither its `proven` nor its `violated`
        // can stand. The same exclusion as [VER-017] condition 1; the SMT pipeline has exact
        // routes for a ν-net.
        boolean declaresMatch = closed.net().transitions().stream().anyMatch(t -> t.matchSpec() != null);
        String graphSkipped = inFlightRefusal != null ? GRAPH_SKIPPED_IN_FLIGHT
            : declaresMatch ? GRAPH_SKIPPED_MATCH : maxClasses > 0 ? null : GRAPH_SKIPPED_BUDGET;
        // [VER-013] cancellation: an interrupt of this thread stops the graph at its next
        // class, and no further query starts (the SMT route's verifiers see it themselves).
        var stop = VerificationDeadline.unlimited("open-net state-class graph");
        GraphRoute.Outcome graph = null;
        String cancelled = null;
        if (graphSkipped == null) {
            var finalClosed = closed;
            var finalContract = contract;
            try {
                stop.check();
                graph = ScopedValue.where(VerificationDeadline.carrier(), stop)
                    .call(() -> GraphRoute.decideOnGraph(finalClosed, finalContract, maxClasses, tracedPlaces, reapable));
            } catch (VerificationDeadline.Cancelled e) {
                cancelled = e.reason();
            }
        }

        var assembly = new Assembly(net, closed, contract, maxClasses, graph, graphSkipped, reaping, start);
        // (The restart notes of [CONC-002] join `reaping` per result, in Assembly.result.)
        if (inFlightRefusal != null) {
            return assembly.result(new Verdict.Unknown(inFlightRefusal), OpenNetResult.Route.ENUMERATION, List.of(), null);
        }
        if (cancelled != null) {
            return assembly.result(new Verdict.Unknown(cancelled), OpenNetResult.Route.ENUMERATION, List.of(), null);
        }
        if (graph != null) {
            if (!graph.violations().isEmpty()) {
                return assembly.result(new Verdict.Violated(), OpenNetResult.Route.ENUMERATION, graph.violations(), null);
            }
            if (graph.complete()) {
                // No invariant: the closed graph proves the contract by exhausting its classes,
                // and the classes themselves are the evidence. There is no certificate here to
                // lose.
                return assembly.result(new Verdict.Proven(METHOD_ENUMERATION, null),
                    OpenNetResult.Route.ENUMERATION, List.of(), null);
            }
        }
        String why = graph != null
            ? "the state-class graph did not close within " + maxClasses + " classes"
            : GRAPH_SKIPPED_BUDGET.equals(graphSkipped)
                ? "the state-class graph was skipped"
                : "the state-class graph was skipped: " + graphSkipped;
        if (!options.smt()) {
            return assembly.result(new Verdict.Unknown(why + ", and the SMT route is disabled"),
                OpenNetResult.Route.ENUMERATION, List.of(), null);
        }

        var smt = SmtRoute.decideViaSmt(
            closed, contract, tracedPlaces, options.configureSmt(), options.terminationTimeout(), reapable,
            options.assumeAtomicFiring());
        if (!smt.violations().isEmpty()) {
            return assembly.result(new Verdict.Violated(), OpenNetResult.Route.SMT, smt.violations(), smt.lines());
        }
        if (smt.undecided().isEmpty()) {
            return assembly.result(new Verdict.Proven(METHOD_SMT, combineCertificates(smt.certificates())),
                OpenNetResult.Route.SMT, List.of(), smt.lines());
        }
        return assembly.result(
            new Verdict.Unknown(why + "; left undecided by the SMT route: " + String.join("; ", smt.undecided())),
            OpenNetResult.Route.SMT, List.of(), smt.lines());
    }

    /** What every result shares: the inputs its report reads, and the clock. */
    private record Assembly(
        PetriNet net,
        ClosedNet closed,
        OpenNetContract contract,
        int maxClasses,
        GraphRoute.Outcome graph,
        String graphSkipped,
        String reaping,
        long startNanos
    ) {
        OpenNetResult result(
                Verdict verdict, OpenNetResult.Route route, List<ContractViolation> violations, List<String> smtLines
        ) {
            // [CONC-002]: a witness that starts a transition while an earlier firing of it is in
            // flight is a run of the Rust executor only.
            var notes = new ArrayList<String>();
            if (reaping != null) {
                notes.add(reaping);
            }
            for (var v : violations) {
                var note = InFlight.restartNote(v.markings(), v.transitions());
                if (note != null && !notes.contains(note)) {
                    notes.add(note);
                }
            }
            String report = Report.render(new Report.Input(
                net, closed, contract, maxClasses, graph, graphSkipped, smtLines,
                notes.isEmpty() ? null : String.join("\n", notes), verdict, violations));
            return new OpenNetResult(
                verdict,
                violations,
                route,
                graph == null ? 0 : graph.classCount(),
                graph != null && graph.complete(),
                report,
                closed.net(),
                closed.initialMarking(),
                Duration.ofNanos(System.nanoTime() - startNanos));
        }
    }

    /**
     * The route's certificates as one invariant, each labelled with the part of the contract it
     * proves. The whole verdict is their conjunction, so keeping them apart keeps them readable.
     *
     * <p>{@code null} when no query returned one. That is weaker evidence, not a weaker verdict:
     * a part proven by a bound or by enumeration has no invariant to give.
     */
    private static String combineCertificates(List<SmtRoute.SubjectCertificate> certificates) {
        if (certificates.isEmpty()) {
            return null;
        }
        var labelled = new ArrayList<String>(certificates.size());
        for (var c : certificates) {
            labelled.add("[" + c.subject() + "] " + c.invariant());
        }
        return String.join("\n", labelled);
    }
}
