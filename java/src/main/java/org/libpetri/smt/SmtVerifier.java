package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.IncidenceMatrix;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.invariant.PInvariant;
import org.libpetri.smt.invariant.PInvariantComputer;
import org.libpetri.smt.invariant.StructuralCheck;
import org.libpetri.smt.z3.CounterexampleDecoder;
import org.libpetri.smt.z3.SmtEncoder;
import org.libpetri.smt.z3.SpacerRunner;

import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.stream.Collectors;
import java.util.function.Consumer;
import java.util.regex.Pattern;

/**
 * IC3/PDR-based safety verifier for Petri nets using Z3's Spacer engine.
 *
 * <p>This verifier proves safety properties (especially deadlock-freedom)
 * without enumerating all reachable states. IC3 constructs inductive
 * invariants incrementally, which works well for bounded nets with
 * resource exclusion and mutual blocking patterns.
 *
 * <p><b>Key design decisions:</b>
 * <ul>
 *   <li>Operates on the marking projection (integer vectors) - no timing</li>
 *   <li>An untimed deadlock-freedom proof is <em>stronger</em> than needed
 *       (timing can only restrict behavior)</li>
 *   <li>Guards (Java Predicates) are ignored - over-approximation is sound
 *       for safety properties</li>
 *   <li>If a counterexample is found, it may be spurious in timed/guarded
 *       semantics - the report notes this</li>
 * </ul>
 *
 * <h3>Example</h3>
 * <pre>{@code
 * var result = SmtVerifier.forNet(net)
 *     .initialMarking(m -> m.tokens(pending, 1))
 *     .property(SmtProperty.deadlockFree())
 *     .timeout(Duration.ofSeconds(60))
 *     .verify();
 *
 * if (result.isProven()) {
 *     System.out.println("Deadlock-free!");
 * }
 * }</pre>
 *
 * <h3>Verification Pipeline</h3>
 * <ol>
 *   <li><b>Flatten</b> - expand XOR, index places, build pre/post vectors</li>
 *   <li><b>Structural pre-check</b> - siphon/trap analysis (may prove early)</li>
 *   <li><b>P-invariants</b> - compute conservation laws for strengthening</li>
 *   <li><b>SMT encode + query</b> - IC3/PDR via Z3 Spacer</li>
 *   <li><b>Decode result</b> - proof or counterexample trace</li>
 * </ol>
 *
 * @see SmtProperty
 * @see SmtVerificationResult
 */
public final class SmtVerifier {

    private final PetriNet net;
    private MarkingState initialMarking = MarkingState.empty();
    private SmtProperty property = SmtProperty.deadlockFree();
    private final Set<EnvironmentPlace<?>> environmentPlaces = new HashSet<>();
    private final Set<Place<?>> sinkPlaces = new HashSet<>();
    private EnvironmentAnalysisMode environmentMode = EnvironmentAnalysisMode.ignore();
    private Duration timeout = Duration.ofSeconds(60);

    private SmtVerifier(PetriNet net) {
        this.net = Objects.requireNonNull(net);
    }

    /**
     * Creates a verifier for the given net.
     */
    public static SmtVerifier forNet(PetriNet net) {
        return new SmtVerifier(net);
    }

    /**
     * Sets the initial marking.
     */
    public SmtVerifier initialMarking(MarkingState marking) {
        this.initialMarking = Objects.requireNonNull(marking);
        return this;
    }

    /**
     * Sets the initial marking via a builder configurator.
     */
    public SmtVerifier initialMarking(Consumer<MarkingState.Builder> configurator) {
        var builder = MarkingState.builder();
        configurator.accept(builder);
        this.initialMarking = builder.build();
        return this;
    }

    /**
     * Sets the safety property to verify.
     */
    public SmtVerifier property(SmtProperty property) {
        this.property = Objects.requireNonNull(property);
        return this;
    }

    /**
     * Declares environment places.
     */
    @SafeVarargs
    public final SmtVerifier environmentPlaces(EnvironmentPlace<?>... places) {
        this.environmentPlaces.addAll(Arrays.asList(places));
        return this;
    }

    /**
     * Sets the environment analysis mode.
     */
    public SmtVerifier environmentMode(EnvironmentAnalysisMode mode) {
        this.environmentMode = Objects.requireNonNull(mode);
        return this;
    }

    /**
     * Declares expected sink (terminal) places for deadlock-freedom analysis.
     * Markings where any sink place has a token are not considered deadlocks.
     */
    @SafeVarargs
    public final SmtVerifier sinkPlaces(Place<?>... places) {
        this.sinkPlaces.addAll(Arrays.asList(places));
        return this;
    }

    /**
     * Sets the solver timeout.
     */
    public SmtVerifier timeout(Duration timeout) {
        this.timeout = Objects.requireNonNull(timeout);
        return this;
    }

    /**
     * Runs the verification pipeline.
     *
     * @return the verification result
     */
    public SmtVerificationResult verify() {
        var start = Instant.now();
        var report = new StringBuilder();
        report.append("=== IC3/PDR SAFETY VERIFICATION ===\n\n");
        report.append("Net: ").append(net.name()).append("\n");
        report.append("Property: ").append(propertyDescription()).append("\n");
        report.append("Timeout: ").append(timeout.toSeconds()).append("s\n\n");

        // Phase 1: Flatten
        report.append("Phase 1: Flattening net...\n");
        FlatNet flatNet = NetFlattener.flatten(net, environmentPlaces, environmentMode);
        report.append("  Places: ").append(flatNet.placeCount()).append("\n");
        report.append("  Transitions (expanded): ").append(flatNet.transitionCount()).append("\n");
        if (!flatNet.environmentBounds().isEmpty()) {
            report.append("  Environment bounds: ").append(flatNet.environmentBounds().size()).append(" places\n");
        }
        report.append("\n");

        // Phase 2: Structural pre-check
        report.append("Phase 2: Structural pre-check (siphon/trap)...\n");
        var structResult = StructuralCheck.check(flatNet, initialMarking);
        String structResultStr = switch (structResult) {
            case StructuralCheck.Result.NoPotentialDeadlock() -> "no potential deadlock";
            case StructuralCheck.Result.PotentialDeadlock(var siphon) -> "potential deadlock (siphon: " + siphon + ")";
            case StructuralCheck.Result.Inconclusive(var reason) -> "inconclusive (" + reason + ")";
        };
        report.append("  Result: ").append(structResultStr).append("\n\n");

        // If structural check proves deadlock-freedom for DeadlockFree property
        // (only valid when no sink places — structural check doesn't account for sinks)
        if (property instanceof SmtProperty.DeadlockFree
                && sinkPlaces.isEmpty()
                && structResult instanceof StructuralCheck.Result.NoPotentialDeadlock) {
            report.append("=== RESULT ===\n\n");
            report.append("PROVEN (structural): Deadlock-freedom verified by Commoner's theorem.\n");
            report.append("  All siphons contain initially marked traps.\n");
            return buildResult(
                new SmtVerificationResult.Verdict.Proven("structural", null),
                report.toString(), List.of(), List.of(), List.of(), List.of(),
                Duration.between(start, Instant.now()),
                new SmtVerificationResult.SmtStatistics(
                    flatNet.placeCount(), flatNet.transitionCount(), 0, structResultStr)
            );
        }

        // Phase 3: P-invariants
        report.append("Phase 3: Computing P-invariants...\n");
        var matrix = IncidenceMatrix.from(flatNet);
        var invariants = PInvariantComputer.compute(matrix, flatNet, initialMarking);
        report.append("  Found: ").append(invariants.size()).append(" P-invariant(s)\n");
        boolean structurallyBounded = PInvariantComputer.isCoveredByInvariants(invariants, flatNet.placeCount());
        report.append("  Structurally bounded: ").append(structurallyBounded ? "YES" : "NO").append("\n");
        for (var inv : invariants) {
            report.append("  ").append(formatInvariant(inv, flatNet)).append("\n");
        }
        report.append("\n");

        // Phase 4: SMT encode + query via Spacer
        report.append("Phase 4: IC3/PDR verification via Z3 Spacer...\n");

        try (var runner = new SpacerRunner(timeout)) {
            var ctx = runner.context();
            var fp = runner.fixedpoint();

            var encoding = SmtEncoder.encode(ctx, fp, flatNet, initialMarking, property, invariants, sinkPlaces);
            var queryResult = runner.query(encoding.errorExpr(), encoding.reachableDecl());

            return switch (queryResult) {
                case SpacerRunner.QueryResult.Proven(var formula, var levels) -> {
                    report.append("  Status: UNSAT (property holds)\n\n");

                    // Decode IC3-synthesized invariants with place name substitution
                    var discoveredInvariants = new ArrayList<String>();
                    if (formula != null) {
                        discoveredInvariants.add(substituteNames(formula, flatNet));
                    }
                    for (var level : levels) {
                        discoveredInvariants.add(substituteNames(level, flatNet));
                    }

                    // Phase 5: Inductive invariant
                    if (!discoveredInvariants.isEmpty()) {
                        report.append("Phase 5: Inductive invariant (discovered by IC3)\n");
                        report.append("  Spacer synthesized: ").append(discoveredInvariants.getFirst()).append("\n");
                        report.append("  This formula is INDUCTIVE: preserved by all transitions.\n");
                        if (discoveredInvariants.size() > 1) {
                            report.append("  Per-level clauses:\n");
                            for (int i = 1; i < discoveredInvariants.size(); i++) {
                                report.append("    ").append(discoveredInvariants.get(i)).append("\n");
                            }
                        }
                        report.append("\n");
                    }

                    report.append("=== RESULT ===\n\n");
                    report.append("PROVEN (IC3/PDR): ").append(propertyDescription()).append("\n");
                    report.append("  Z3 Spacer proved no reachable state violates the property.\n");
                    report.append("  NOTE: Verification ignores timing constraints and Java guards.\n");
                    report.append("  An untimed proof is STRONGER than a timed one ");
                    report.append("(timing only restricts behavior).\n");

                    yield buildResult(
                        new SmtVerificationResult.Verdict.Proven("IC3/PDR",
                            formula != null ? substituteNames(formula, flatNet) : null),
                        report.toString(), invariants, List.copyOf(discoveredInvariants), List.of(), List.of(),
                        Duration.between(start, Instant.now()),
                        new SmtVerificationResult.SmtStatistics(
                            flatNet.placeCount(), flatNet.transitionCount(),
                            invariants.size(), structResultStr)
                    );
                }

                case SpacerRunner.QueryResult.Violated(var answer) -> {
                    report.append("  Status: SAT (counterexample found)\n\n");

                    // Decode counterexample
                    var decoded = CounterexampleDecoder.decode(answer, flatNet);

                    report.append("=== RESULT ===\n\n");
                    report.append("VIOLATED: ").append(propertyDescription()).append("\n");
                    if (!decoded.trace().isEmpty()) {
                        report.append("  Counterexample trace (").append(decoded.trace().size()).append(" states):\n");
                        for (int i = 0; i < decoded.trace().size(); i++) {
                            report.append("    ").append(i).append(": ").append(decoded.trace().get(i)).append("\n");
                        }
                    }
                    if (!decoded.transitions().isEmpty()) {
                        report.append("  Firing sequence: ").append(decoded.transitions()).append("\n");
                    }
                    report.append("\n  WARNING: This counterexample is in UNTIMED semantics.\n");
                    report.append("  It may be spurious if timing constraints prevent this sequence.\n");
                    report.append("  Java guards are also ignored in this analysis.\n");

                    yield buildResult(
                        new SmtVerificationResult.Verdict.Violated(),
                        report.toString(), invariants, List.of(), decoded.trace(), decoded.transitions(),
                        Duration.between(start, Instant.now()),
                        new SmtVerificationResult.SmtStatistics(
                            flatNet.placeCount(), flatNet.transitionCount(),
                            invariants.size(), structResultStr)
                    );
                }

                case SpacerRunner.QueryResult.Unknown(var reason) -> {
                    report.append("  Status: UNKNOWN (").append(reason).append(")\n\n");
                    report.append("=== RESULT ===\n\n");
                    report.append("UNKNOWN: Could not determine ").append(propertyDescription()).append("\n");
                    report.append("  Reason: ").append(reason).append("\n");

                    yield buildResult(
                        new SmtVerificationResult.Verdict.Unknown(reason),
                        report.toString(), invariants, List.of(), List.of(), List.of(),
                        Duration.between(start, Instant.now()),
                        new SmtVerificationResult.SmtStatistics(
                            flatNet.placeCount(), flatNet.transitionCount(),
                            invariants.size(), structResultStr)
                    );
                }
            };
        } catch (com.microsoft.z3.Z3Exception e) {
            report.append("  ERROR: ").append(e.getMessage()).append("\n\n");
            report.append("=== RESULT ===\n\n");
            report.append("UNKNOWN: Z3 solver error: ").append(e.getMessage()).append("\n");

            return buildResult(
                new SmtVerificationResult.Verdict.Unknown("Z3 error: " + e.getMessage()),
                report.toString(), invariants, List.of(), List.of(), List.of(),
                Duration.between(start, Instant.now()),
                new SmtVerificationResult.SmtStatistics(
                    flatNet.placeCount(), flatNet.transitionCount(),
                    invariants.size(), structResultStr)
            );
        }
    }

    private String propertyDescription() {
        return switch (property) {
            case SmtProperty.DeadlockFree() -> sinkPlaces.isEmpty()
                ? "Deadlock-freedom"
                : "Deadlock-freedom (sinks: " + sinkPlaces.stream()
                    .map(Place::name).collect(Collectors.joining(", ")) + ")";
            case SmtProperty.MutualExclusion me ->
                "Mutual exclusion of " + me.p1().name() + " and " + me.p2().name();
            case SmtProperty.PlaceBound pb ->
                "Place " + pb.place().name() + " bounded by " + pb.bound();
            case SmtProperty.Unreachable ur ->
                "Unreachability of marking with tokens in " + ur.places();
        };
    }

    /**
     * Substitutes Z3 variable names (m0, m1, ...) with place names in a formula string.
     * Uses word-boundary regex to avoid matching inside Z3 internal identifiers.
     */
    private static String substituteNames(String formula, FlatNet flatNet) {
        for (int i = flatNet.placeCount() - 1; i >= 0; i--) {
            formula = Pattern.compile("\\bm" + i + "\\b").matcher(formula)
                .replaceAll(flatNet.places().get(i).name());
        }
        return formula;
    }

    private static String formatInvariant(PInvariant inv, FlatNet flatNet) {
        var sb = new StringBuilder();
        boolean first = true;
        for (int idx : inv.support()) {
            if (!first) sb.append(" + ");
            if (inv.weights()[idx] != 1) sb.append(inv.weights()[idx]).append("*");
            sb.append(flatNet.places().get(idx).name());
            first = false;
        }
        sb.append(" = ").append(inv.constant());
        return sb.toString();
    }

    private static SmtVerificationResult buildResult(
            SmtVerificationResult.Verdict verdict, String report,
            List<PInvariant> invariants, List<String> discoveredInvariants,
            List<MarkingState> trace, List<String> transitions,
            Duration elapsed, SmtVerificationResult.SmtStatistics stats
    ) {
        return new SmtVerificationResult(verdict, report, invariants, discoveredInvariants, trace, transitions, elapsed, stats);
    }
}
