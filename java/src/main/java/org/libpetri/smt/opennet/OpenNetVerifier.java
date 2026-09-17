package org.libpetri.smt.opennet;

import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.smt.SmtVerificationResult.Verdict;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;

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
     * @throws IllegalArgumentException when the closure's names collide with the net's
     */
    public static OpenNetResult verifyOpenNet(PetriNet net, OpenNetContract contract, OpenNetOptions options) {
        long start = System.nanoTime();
        var closed = OpenNetClosure.closeOpenNet(net, contract);
        int maxClasses = options.maxClasses();
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
        String graphSkipped = declaresMatch ? GRAPH_SKIPPED_MATCH : maxClasses > 0 ? null : GRAPH_SKIPPED_BUDGET;
        var graph = graphSkipped == null
            ? GraphRoute.decideOnGraph(closed, contract, maxClasses, tracedPlaces)
            : null;

        var assembly = new Assembly(net, closed, contract, maxClasses, graph, graphSkipped, start);
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
            closed, contract, tracedPlaces, options.configureSmt(), options.terminationTimeout());
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
        long startNanos
    ) {
        OpenNetResult result(
                Verdict verdict, OpenNetResult.Route route, List<ContractViolation> violations, List<String> smtLines
        ) {
            String report = Report.render(new Report.Input(
                net, closed, contract, maxClasses, graph, graphSkipped, smtLines, verdict, violations));
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
