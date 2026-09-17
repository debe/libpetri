package org.libpetri.smt.opennet;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.smt.GraphDecision;
import org.libpetri.smt.RestSet;
import org.libpetri.smt.ScgVerifier;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.SmtVerificationResult;
import org.libpetri.smt.SmtVerificationResult.Verdict;
import org.libpetri.smt.SmtVerifier;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.z3.AbstractReplayer;
import org.libpetri.smt.z3.BoundedRun;
import org.libpetri.smt.z3.Z3Process;
import org.libpetri.smt.z3.Z3Solver;

import java.math.BigInteger;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.OptionalInt;
import java.util.Set;
import java.util.function.Function;
import java.util.function.UnaryOperator;

/**
 * The contract asked of the SMT pipeline, for a closed net whose graph does not close
 * ([VER-022]).
 *
 * <p>Each part of the contract is one query on the closed net, and each decides exactly the
 * predicate the graph route reads:
 * <ul>
 *   <li><b>stranding</b>: {@code deadlockFree()} with the clause places, the rest places and
 *       the environment's own places as sinks, and each terminal as a conditional sink
 *       ([VER-014]);</li>
 *   <li><b>a count clause</b>: {@code quiescentCount(places, min, max, markers)} ([VER-002]),
 *       with every terminal marker as a waiver;</li>
 *   <li><b>termination</b>: the firing-bound ranking of [VER-019] on the closed net. Weights
 *       that every firing lowers bound the length of every run by what they give the initial
 *       marking, so no run goes on forever. When there are none, the part is undecided and the
 *       reason names the firings the marking equation lets repeat.</li>
 * </ul>
 */
final class SmtRoute {

    private SmtRoute() {}

    /**
     * What the SMT route found.
     *
     * @param undecided    the parts of the contract no query decided, each with its reason
     * @param lines        one report line per query
     * @param certificates the inductive invariant each proven query returned, in query order.
     *                     These are the route's proof evidence: a proven open-net verdict is
     *                     their conjunction, one certificate per part of the contract
     */
    record Outcome(
        List<ContractViolation> violations,
        List<String> undecided,
        List<String> lines,
        List<SubjectCertificate> certificates
    ) {
        Outcome {
            violations = List.copyOf(violations);
            undecided = List.copyOf(undecided);
            lines = List.copyOf(lines);
            certificates = List.copyOf(certificates);
        }
    }

    /** One part of the contract and the invariant that proved it. */
    record SubjectCertificate(String subject, String invariant) {}

    /**
     * One query.
     *
     * @param onViolated the violation a {@code Violated} verdict means
     */
    private record Query(
        String subject,
        SmtProperty property,
        List<Place<?>> sinks,
        List<RestSet.ConditionalSinks> conditional,
        Function<SmtVerificationResult, ContractViolation.Witness> onViolated
    ) {}

    /**
     * A part of the contract: a query to run, or a clause no marking can fail.
     *
     * <p>A count clause of {@code [0, ∞]} is the second kind: {@link GraphDecision#countViolation}
     * never reports it, so neither route can find it broken. Its places still act as sinks of the
     * stranding query ({@link QuiescencePredicate#restDeclarationOf}). Asking anyway could only
     * turn {@code Proven} into {@code Unknown} on a slow solver; the report line keeps the skip
     * visible.
     */
    private sealed interface Part {
        record Ask(Query query) implements Part {}

        record Vacuous(String subject, String detail) implements Part {}
    }

    /** Runs one query per part of the contract, in contract order, then the firing bound. */
    static Outcome decideViaSmt(
            ClosedNet closed,
            OpenNetContract contract,
            List<Place<?>> tracedPlaces,
            UnaryOperator<SmtVerifier> configure,
            Duration terminationTimeout
    ) {
        var violations = new ArrayList<ContractViolation>();
        var undecided = new ArrayList<String>();
        var lines = new ArrayList<String>();
        var certificates = new ArrayList<SubjectCertificate>();
        var net = untimed(closed.net());
        for (var part : partsFor(closed, contract)) {
            switch (part) {
                case Part.Vacuous(var subject, var detail) ->
                    lines.add("  [" + subject + "] " + detail + ": proven (no query needed)");
                case Part.Ask(var q) -> {
                    var verifier = SmtVerifier.forNet(net)
                        .initialMarking(closed.initialMarking())
                        .property(q.property())
                        .sinkPlaces(q.sinks().toArray(new Place<?>[0]))
                        // The graph route already enumerated as far as its budget allows.
                        .enumerationMaxClasses(0);
                    for (var c : q.conditional()) {
                        verifier = verifier.sinkPlacesWhen(c.marker(), c.places().toArray(new Place<?>[0]));
                    }
                    var result = configure.apply(verifier).verify();
                    String head = "  [" + q.subject() + "] " + q.property().description() + ": ";
                    switch (result.verdict()) {
                        case Verdict.Unknown(var reason) -> {
                            lines.add(head + "unknown (" + reason + ")");
                            undecided.add(q.subject() + ": " + reason);
                        }
                        case Verdict.Violated() -> {
                            lines.add(head + "violated");
                            violations.add(ContractViolation.of(closed, tracedPlaces, q.onViolated().apply(result)));
                        }
                        case Verdict.Proven(var _, var invariant) -> {
                            lines.add(head + "proven");
                            // A proven part may or may not come with a certificate: the
                            // enumeration and bound phases prove without one. Keep the ones that
                            // do rather than dropping the evidence.
                            if (invariant != null) {
                                certificates.add(new SubjectCertificate(q.subject(), invariant));
                            }
                        }
                    }
                }
            }
        }
        if (contract.requiresTermination()) {
            var termination = terminationByRanking(closed, terminationTimeout);
            if (termination.proven()) {
                lines.add("  [termination] Firing bound (VER-019): " + termination.text());
            } else {
                lines.add("  [termination] Firing bound (VER-019): undecided (" + termination.text() + ")");
                undecided.add("termination: " + termination.text());
            }
        }
        return new Outcome(violations, undecided, lines, certificates);
    }

    /**
     * {@code net} with every transition {@code immediate}, so each query decides the untimed claim
     * ([VER-004]). The flat encoders ignore timing, but a ν-net's quiescence query goes to the
     * name-aware graph (NU-050), which keeps it and would prove the weaker timed claim.
     */
    private static PetriNet untimed(PetriNet net) {
        if (ScgVerifier.isUntimed(net)) {
            return net;
        }
        var transitions = new ArrayList<Transition>(net.transitions().size());
        for (var t : net.transitions()) {
            if (t.timing() instanceof Timing.Immediate) {
                transitions.add(t);
                continue;
            }
            var b = Transition.builder(t.name())
                .inputs(t.inputSpecs().toArray(new Arc.In[0]))
                .outputs(t.outputSpec())
                .match(t.matchSpec())
                .priority(t.priority())
                .action(t.action());
            t.inhibitors().forEach(b::inhibitorArc);
            t.reads().forEach(b::readArc);
            t.resets().forEach(b::resetArc);
            transitions.add(b.build());
        }
        return PetriNet.builder(net.name())
            .places(net.places().toArray(new Place<?>[0]))
            .transitions(transitions.toArray(new Transition[0]))
            .build();
    }

    private static List<Part> partsFor(ClosedNet closed, OpenNetContract contract) {
        // Derived once: the stranding query's sinks and the attribution of its witness must be
        // the same declaration, and the graph route reads that one too.
        var rest = QuiescencePredicate.restDeclarationOf(contract, closed);
        var markers = QuiescencePredicate.waiverMarkers(contract, closed);

        var stranding = new Query(
            "stranding",
            SmtProperty.deadlockFree(),
            rest.sinks(),
            rest.conditional(),
            result -> {
                // The verdict does not depend on the replay — the solver's `sat` is the
                // violation. The attribution does: without a confirmed quiescent marking there
                // is nothing to read the stranded places off, so the finding names the query
                // rather than guessing a place.
                var last = quiescentMarking(result);
                var stranded = new ArrayList<String>();
                if (last != null) {
                    for (var p : QuiescencePredicate.strandedNames(last, rest)) {
                        stranded.add(p.name());
                    }
                }
                String joined = String.join(", ", stranded);
                return witness(result, ContractViolation.Kind.STRANDED,
                    stranded.isEmpty() ? "stranding" : joined,
                    stranded.isEmpty()
                        ? "the solver found a reachable quiescent marking that leaves a token where the contract lets none rest"
                        : joined + " " + (stranded.size() == 1 ? "holds" : "hold")
                            + " a token at quiescence, and nothing in the contract lets one rest there");
            });

        var parts = new ArrayList<Part>();
        parts.add(new Part.Ask(stranding));

        for (var clause : contract.clauses()) {
            String across = SmtProperty.countAcross(clause.min(), clause.max(), clause.places());
            if (clause.min() == 0 && clause.max().isEmpty()) {
                parts.add(new Part.Vacuous(clause.name(), across + " at quiescence"));
                continue;
            }
            var places = QuiescencePredicate.clausePlaces(clause, closed);
            parts.add(new Part.Ask(new Query(
                clause.name(),
                SmtProperty.quiescentCount(places, clause.min(), clause.max(), markers),
                List.of(),
                List.of(),
                result -> {
                    var last = quiescentMarking(result);
                    return witness(result, ContractViolation.Kind.CLAUSE, clause.name(), last == null
                        ? across + " at quiescence: the solver found a quiescent marking outside it"
                        : across + " at quiescence, found " + GraphDecision.tokensAcross(last, places));
                })));
        }
        return parts;
    }

    /** The last marking of a replay-confirmed counterexample: the quiescent one it reached. */
    private static MarkingState quiescentMarking(SmtVerificationResult result) {
        var trace = result.counterexampleTrace();
        return Boolean.TRUE.equals(result.counterexampleConfirmed()) && trace != null && !trace.isEmpty()
            ? trace.getLast()
            : null;
    }

    private static ContractViolation.Witness witness(
            SmtVerificationResult result, ContractViolation.Kind kind, String subject, String detail
    ) {
        return new ContractViolation.Witness(
            kind,
            subject,
            detail,
            result.counterexampleTransitions() == null ? List.of() : result.counterexampleTransitions(),
            result.counterexampleTrace() == null ? List.of() : result.counterexampleTrace(),
            OptionalInt.empty(),
            Boolean.TRUE.equals(result.counterexampleConfirmed()));
    }

    /**
     * Whether termination was proven, with the proof in words; otherwise why it stays
     * undecided.
     */
    private record Termination(boolean proven, String text) {}

    /** A reply's stdout, or the reason there is none. Exactly one is non-null. */
    private record Answer(String stdout, String failure) {}

    /**
     * Termination by the firing-bound ranking of [VER-019]: weights {@code r ≥ 0} that every
     * firing of the closed net lowers by at least one, re-checked in exact arithmetic. No run
     * then has more than {@code r·M0} firings. When there are none, the Farkas alternative names
     * the firings the marking equation lets repeat.
     */
    private static Termination terminationByRanking(ClosedNet closed, Duration timeout) {
        FlatNet flat = NetFlattener.flatten(closed.net(), Set.of(), EnvironmentAnalysisMode.ignore());
        int[] initial = AbstractReplayer.toVector(flat, closed.initialMarking());
        Z3Solver solver;
        try {
            solver = Z3Solver.resolve();
        } catch (Z3Solver.Z3Unavailable e) {
            return new Termination(false, e.getMessage());
        }

        var ranking = ask(solver, BoundedRun.encodeRankingQuery(flat, initial), timeout);
        if (ranking.failure() != null) {
            return new Termination(false, ranking.failure());
        }
        switch (firstLine(ranking.stdout())) {
            case "sat" -> {
                List<BigInteger> weights = BoundedRun.decodeRanking(ranking.stdout(), flat.placeCount());
                var bound = weights == null ? null : BoundedRun.checkRankingExact(flat, initial, weights);
                if (bound == null) {
                    return new Termination(false, "the firing-bound ranking failed the exact re-check");
                }
                return new Termination(true, "every run has at most " + bound.bound() + " firings ("
                    + BoundedRun.formatRanking(flat, bound) + " drops on every firing)");
            }
            case "unsat" -> {
                var vector = ask(solver, BoundedRun.encodeRepeatableVectorQuery(flat), timeout);
                List<Integer> repeat = vector.failure() != null || !"sat".equals(firstLine(vector.stdout()))
                    ? null
                    : BoundedRun.decodeRepeatableVector(vector.stdout(), flat.transitionCount());
                if (repeat == null || repeat.isEmpty()) {
                    return new Termination(false, "no firing bound: no weights drop on every firing");
                }
                var names = new ArrayList<String>(repeat.size());
                for (int t : repeat) {
                    names.add(flat.transitions().get(t).name());
                }
                return new Termination(false,
                    "no firing bound: the marking equation lets " + String.join(", ", names) + " repeat");
            }
            default -> {
                return new Termination(false, "the firing-bound query answered unknown");
            }
        }
    }

    /**
     * One script through one z3 process ({@code ranking} in the dump), as the reference asks
     * it: a reply whose first line is a {@code (check-sat)} answer, or the transport's reason
     * there is none.
     */
    private static Answer ask(Z3Solver solver, String script, Duration timeout) {
        Z3Process.Reply reply;
        try {
            reply = solver.run(script, "ranking", timeout, List.of());
        } catch (Z3Process.Z3ProcessException e) {
            return new Answer(null, e.getMessage());
        }
        return switch (firstLine(reply.stdout())) {
            case "sat", "unsat", "unknown" -> new Answer(reply.stdout(), null);
            default -> new Answer(null, Z3Process.failureReason(reply, Z3Solver.timeoutMs(timeout)));
        };
    }

    /**
     * The first non-blank line of a reply, trimmed. Unlike the verifier's own classification,
     * which finds the answer anywhere in the reply, the reference reads the first line only, so
     * a reply that opens with anything else is a failure here.
     */
    private static String firstLine(String stdout) {
        return stdout.lines().map(String::strip).filter(l -> !l.isEmpty()).findFirst().orElse("");
    }
}
