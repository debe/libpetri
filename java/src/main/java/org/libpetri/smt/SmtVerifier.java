package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.PrioritySemantics;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.internal.OutputActionCheck;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.IncidenceMatrix;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.invariant.PInvariant;
import org.libpetri.smt.invariant.PInvariantComputer;
import org.libpetri.smt.invariant.StructuralCheck;
import org.libpetri.smt.z3.AbstractReplayer;
import org.libpetri.smt.z3.CertificateChecker;
import org.libpetri.smt.z3.CounterexampleDecoder;
import org.libpetri.smt.z3.NameColouredEncoder;
import org.libpetri.smt.z3.SmtEncoder;
import org.libpetri.smt.z3.SpacerRunner;
import org.libpetri.smt.z3.Z3Solver;

import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.stream.Collectors;
import java.util.function.Consumer;
import java.util.function.Supplier;

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
    private final Set<String> budgetPlaces = new HashSet<>();
    private EnvironmentAnalysisMode environmentMode = EnvironmentAnalysisMode.alwaysAvailable();

    /**
     * Why a {@code Proven} is refused under {@link EnvironmentAnalysisMode#ignore()}
     * ([VER-006]). Shared by every route that can return {@code Proven}, so the two
     * guards cannot drift apart.
     */
    private static final String IGNORE_MODE_VACUITY_REASON =
        "environment places present but not modeled (mode=ignore); "
        + "a proof would be vacuous — use EnvironmentAnalysisMode.alwaysAvailable() "
        + "or bounded(k) to model external injection";
    private Duration timeout = Duration.ofSeconds(60);
    private int nuMaxClasses = 100_000;
    private FragmentMode fragmentMode = FragmentMode.BASE;
    private final Set<String> carrierPlaces = new HashSet<>();
    private PrioritySemantics prioritySemantics = PrioritySemantics.NONE;
    private boolean certificateCheck = true;
    private boolean counterexampleReplay = true;
    private boolean semiflowInvariants = false;
    private CertificateCheck certificateChecker = CertificateChecker::check;
    private Z3Solver solver = null;
    private Set<MarkingState> replayStateSetOverride = null;
    private int replayNodeBudget = AbstractReplayer.DEFAULT_NODE_BUDGET;

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
     * Declares &nu;-net budget places (NU-040): places whose token count bounds
     * the live correlation pool (they gate fresh-name minting). Declaring at
     * least one places the net in the decidable bounded fragment, so
     * reachability-safety properties over its &nu;-joins are verified (the
     * matched transitions are over-approximated). Without any budget place, a
     * net that mints fresh names is treated as unbounded and the verifier
     * returns {@code Unknown} (NU-050).
     */
    @SafeVarargs
    public final SmtVerifier budgetPlaces(Place<?>... places) {
        for (var p : places) {
            this.budgetPlaces.add(p.name());
        }
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
     * Sets the class-count cap for the &nu;-aware state-class-graph analysis
     * (NU-050, Route B). When the symbolic name-aware graph would exceed this, the
     * analysis truncates and the verdict is {@code Unknown} (the live correlation
     * pool is not structurally bounded). Default 100_000.
     */
    public SmtVerifier nuMaxClasses(int max) {
        this.nuMaxClasses = max;
        return this;
    }

    /**
     * Selects the &nu;-name-correlation fragment for the Route-B analyzer (NU-050).
     * {@link FragmentMode#BASE} (default) is the shipped mint&rarr;matched-join
     * fragment; {@link FragmentMode#EXTENDED} additionally admits name-blind
     * coloured-consumers (drain / relay) and the {@link #carrierPlaces} that thread
     * a minted name from a fork to the join inputs, so fork-threaded &nu;-nets with
     * dead-letter drains become decidable. Opt-in; BASE preserves prior behavior.
     */
    public SmtVerifier fragmentMode(FragmentMode mode) {
        this.fragmentMode = Objects.requireNonNull(mode);
        return this;
    }

    /**
     * Declares carrier places (EXTENDED fragment only): intermediate places that
     * carry a name minted at a fork onward to a &nu;-join input. They join the
     * coloured (name-partitioned) set so a single fresh name is threaded through
     * them (rather than each producer minting an independent colour). Ignored under
     * {@link FragmentMode#BASE}.
     *
     * <p>Each declared place must belong to {@code net}: a mistyped carrier name
     * would silently make two fork branches mint independent names, so the join
     * never becomes name-enabled and the verifier could report a confident false
     * deadlock. This method therefore throws {@link IllegalArgumentException} naming
     * the offending place rather than proceeding.
     *
     * @throws IllegalArgumentException if a declared place is not in {@code net}
     */
    @SafeVarargs
    public final SmtVerifier carrierPlaces(Place<?>... places) {
        var netPlaceNames = new HashSet<String>();
        for (var np : net.places()) {
            netPlaceNames.add(np.name());
        }
        for (var p : places) {
            if (!netPlaceNames.contains(p.name())) {
                throw new IllegalArgumentException(
                    "declared carrier place '" + p.name() + "' is not in the net");
            }
            this.carrierPlaces.add(p.name());
        }
        return this;
    }

    /**
     * Selects how the Route-B name-aware analyzer treats transition priority
     * (NU-052). Defaults to {@link PrioritySemantics#NONE} (priority-blind, the
     * shipped sound over-approximation). {@link PrioritySemantics#CONFLICT} models
     * the executor's conflict-only priority resolution, pruning a lower-priority
     * transition when a ready, conflicting, strictly-higher-priority one is enabled
     * — which removes the spurious stalls a timed dead-letter-drain idiom otherwise
     * produces against the priority-blind default. Only affects the ν-net Route B
     * path (a net with a match transition).
     */
    public SmtVerifier prioritySemantics(PrioritySemantics semantics) {
        this.prioritySemantics = Objects.requireNonNull(semantics);
        return this;
    }

    /**
     * Enables or disables the IC3 certificate check (default: enabled).
     *
     * <p>When enabled, a PROVEN verdict from the flat IC3/PDR path is only
     * reported after the Spacer-synthesized inductive invariant has been
     * independently re-validated with a plain solver. The candidate is
     * {@code R' = I AND invs} — Spacer's invariant conjoined with the validated
     * P-invariant equalities, which the check re-proves rather than trusts:
     * initiation ({@code NOT R'(M0)} unsat), consecution against the
     * <em>unstrengthened</em> step relation ({@code R'(M) AND T(M,M') AND NOT
     * R'(M')} unsat — no invariant conjuncts in {@code T}), and safety
     * ({@code R'(M) AND Bad(M)} unsat). If any condition fails, or the
     * certificate is missing or unparseable, the verdict is downgraded to
     * UNKNOWN with the failing condition named — a proof is never silently
     * trusted. The check applies only to the flat count encoding; structural
     * early proofs and the name-coloured (ν) encoding path are not covered.
     */
    public SmtVerifier certificateCheck(boolean enabled) {
        this.certificateCheck = enabled;
        return this;
    }

    /**
     * Also hands the validated <b>P-semiflows</b> to the encoders as invariants
     * ([VER-007]; default: disabled — the encoders then see only the null-space basis).
     *
     * <p>Every validated semiflow is a conservation law in its own right ({@code y >= 0},
     * {@code y*C = 0}, {@code y*M0} exact, zero weight on every reset / consume-all place),
     * and the Farkas enumeration returns the <em>minimal</em> laws of the net. The
     * null-space basis the encoders get by default is one basis of many: Gaussian
     * elimination hands back mixed-sign rows (discarded as not semi-positive) or rows that
     * fold a reset place into a chain whose other combinations avoid it (dropped by the H1
     * guard). On a net with a few reset arcs that can lose every law of the chains those
     * arcs touch, and without them IC3 has to rediscover the conservation of each chain —
     * on a ~100-place net it does not within any practical budget.
     *
     * <p><b>Turn this on if the net has any {@code all()} / {@code atLeast(n)} or reset
     * arc on a busy place</b> — draining an input queue is the everyday case. Every basis
     * row whose support touches such a place fails the H1 guard and is dropped, so the
     * encoders run on a deficient invariant set and nothing in the report says a law is
     * missing beyond the {@code Dropped} lines.
     *
     * <p>This reaches the <b>name-coloured</b> encoder ([NU-050]) as well as the flat one,
     * and it matters most there. On a 113-place ν-net, whole-net deadlock-freedom went
     * from {@code Unknown} after 50 minutes to {@code Proven} in about 15 seconds with
     * this option as the only change; on the flat path, reachability-safety queries that
     * timed out at 120 s close in about a second.
     *
     * <p>Soundness is unchanged: the semiflows pass the same exact re-validation as the
     * basis rows, the union is pure strengthening (Lean {@code Semiflow.lean},
     * {@code semiflow_union_sound}), and the certificate check re-proves the strengthened
     * invariant. That check is flat-path only — a coloured {@code Proven} reports
     * {@code Certificate check: not applicable (name-coloured encoding)}.
     */
    public SmtVerifier semiflowInvariants(boolean enabled) {
        this.semiflowInvariants = enabled;
        return this;
    }

    /**
     * Test seam: runs this verification against a specific z3 executable instead of
     * resolving {@code LIBPETRI_Z3} / {@code PATH} (the JVM cannot change its own
     * environment). Package-private — not API.
     */
    SmtVerifier solver(Z3Solver solver) {
        this.solver = Objects.requireNonNull(solver);
        return this;
    }

    /**
     * True if a usable {@code z3} executable resolves: {@code LIBPETRI_Z3} if set, else
     * {@code z3} on {@code PATH}, at or above {@link Z3Solver#MIN_VERSION} (VER-013).
     * Without one every SMT path returns {@code Unknown}; the test suites use this to
     * skip loudly rather than fail.
     */
    public static boolean z3Available() {
        try {
            Z3Solver.resolve();
            return true;
        } catch (Z3Solver.Z3Unavailable _) {
            return false;
        }
    }

    /**
     * Test seam: replaces the certificate-check implementation. Package-private —
     * used to inject a corrupted-certificate outcome without depending on
     * Spacer's answer shape.
     */
    SmtVerifier certificateChecker(CertificateCheck checker) {
        this.certificateChecker = Objects.requireNonNull(checker);
        return this;
    }

    /**
     * Test seam: substitutes the decoded state set handed to the abstract replay,
     * so the C4 paths that end in {@link AbstractReplayer.ReplayOutcome.Exhausted}
     * (nothing decoded, M0 absent, segment budget spent) can be driven without a
     * doctored solver. Package-private — not API.
     */
    SmtVerifier replayStateSetOverride(Set<MarkingState> states) {
        this.replayStateSetOverride = Set.copyOf(states);
        return this;
    }

    /** Test seam: shrinks the replay's node budget. Package-private — not API. */
    SmtVerifier replayNodeBudget(int budget) {
        this.replayNodeBudget = budget;
        return this;
    }

    /**
     * Enables or disables abstract counterexample replay (default: enabled).
     *
     * <p>When enabled, a VIOLATED verdict from the flat IC3/PDR path is
     * cross-checked before it is reported: the markings decoded from Spacer's
     * derivation (an order-free set — the derivation traversal order is not an
     * execution order) are chained by {@link AbstractReplayer} into an actual
     * run of the abstract semantics, from the initial marking to a marking
     * satisfying the property-violation predicate, bridging consecutive
     * decoded states with a bounded search. A successful chain confirms the
     * counterexample ({@link SmtVerificationResult#counterexampleConfirmed()} is
     * {@code TRUE}) and the replay-ordered trace is reported; a completed search
     * that finds no chain downgrades the verdict to UNKNOWN (spurious
     * counterexample or decoder mismatch — the abstraction is untimed and
     * value-blind, VER-004); a search that cannot decide keeps VIOLATED and
     * reports {@code FALSE}. Disabling it here leaves the field {@code null}.
     * The replay never invokes Z3.
     */
    public SmtVerifier counterexampleReplay(boolean enabled) {
        this.counterexampleReplay = enabled;
        return this;
    }

    /**
     * Runs the verification pipeline.
     *
     * @return the verification result
     * @throws IllegalStateException per [CORE-043] — this encoder reads token production from
     *     the {@code Arc.Out} spec, never from the bound action, so a net that could not produce
     *     at run time would otherwise verify green
     */
    public SmtVerificationResult verify() {
        OutputActionCheck.requireOutputProducingActions(net);
        var start = Instant.now();
        var report = new StringBuilder();
        report.append("=== IC3/PDR SAFETY VERIFICATION ===\n\n");
        report.append("Net: ").append(net.name()).append("\n");
        report.append("Property: ").append(propertyDescription()).append("\n");
        report.append("Timeout: ").append(timeout.toSeconds()).append("s\n\n");

        // ν-net awareness (NU-040, NU-050). A transition with a match spec joins
        // by name equality; the untimed encoder over-approximates that (name
        // equality assumed satisfiable). The over-approximation is sound for
        // reachability-safety bounds (Proven holds — the real net fires strictly
        // fewer joins) but NOT for quiescence-based properties, which name-blind
        // firing distorts. The applyNuGuard step turns those cases into Unknown.
        boolean hasMatch = net.transitions().stream().anyMatch(t -> t.matchSpec() != null);
        boolean nuBounded = !budgetPlaces.isEmpty();

        // ν-net Route B (NU-050): the name-aware state-class-graph name-partition
        // quotient decides ν-join correlation EXACTLY — including name×time and
        // quiescence — without a budget. It "fills the gaps" the SMT / Route A path
        // cannot answer exactly: quiescence properties on a ν-net, and unbudgeted
        // reachability-safety. Budgeted, untimed reachability-safety in Route A's
        // fragment stays on Route A below (this trigger is false there). If the net
        // is outside the supported fragment, NuScgVerifier returns null and we fall
        // through to the existing pipeline (which applies the sound Unknown
        // downgrade for these cases).
        if (hasMatch && (!isReachabilitySafety(property) || !nuBounded)) {
            var outcome = NuScgVerifier.verify(
                net, initialMarking, property, sinkPlaces, environmentPlaces, environmentMode, nuMaxClasses,
                fragmentMode, carrierPlaces, prioritySemantics);
            // Route B truncating to Unknown on a bounded quiescence ν-net is not the final
            // word: defer to the scalable Route A coloured IC3/PDR encoder (NU-053) below
            // instead of returning Unknown here.
            boolean deferToRouteA = outcome != null
                && outcome.verdict() instanceof SmtVerificationResult.Verdict.Unknown
                && !isReachabilitySafety(property)
                && nuBounded;
            if (outcome != null && !deferToRouteA) {
                report.append("=== ν-net Route B: name-aware state-class graph (NU-050) ===\n");
                report.append("  Name-partition state classes: ").append(outcome.classCount()).append("\n");
                report.append(outcome.note());
                if (!outcome.transitions().isEmpty()) {
                    report.append("  Counterexample trace: ").append(outcome.trace().size())
                          .append(" states, ").append(outcome.transitions().size()).append(" transitions\n");
                }
                // [VER-006] binds every route that can return Proven, not only the SMT
                // encoding. Under Ignore the name-partition graph treats an environment
                // place as an ordinary empty one, so a bound that holds only because
                // injection never happens is exactly the vacuous proof the guard exists
                // to refuse — and Route B reaches this return without passing the guard
                // on the solver path below.
                var routeBVerdict = outcome.verdict();
                if (routeBVerdict instanceof SmtVerificationResult.Verdict.Proven
                        && !environmentPlaces.isEmpty()
                        && environmentMode instanceof EnvironmentAnalysisMode.Ignore) {
                    report.append("  Downgraded to UNKNOWN: ")
                          .append(IGNORE_MODE_VACUITY_REASON).append("\n");
                    routeBVerdict = new SmtVerificationResult.Verdict.Unknown(
                        IGNORE_MODE_VACUITY_REASON);
                }
                return buildResult(
                    routeBVerdict, report.toString(), List.of(), List.of(),
                    outcome.trace(), outcome.transitions(),
                    Duration.between(start, Instant.now()),
                    new SmtVerificationResult.SmtStatistics(
                        net.places().size(), net.transitions().size(), 0, "n/a (ν name-partition SCG)"));
            } else if (deferToRouteA) {
                report.append("ν-net Route B inconclusive (name-partition truncated); deferring to "
                    + "Route A coloured IC3/PDR (NU-053).\n");
            }
            // EXTENDED was requested but the net falls outside the coloured-consumer
            // fragment (classify returned null). Surface a short note instead of a
            // silent fall-back, then continue on the sound over-approximation path.
            if (fragmentMode == FragmentMode.EXTENDED && !deferToRouteA) {
                report.append("ν-net Route B (EXTENDED) declined: net outside coloured-consumer "
                    + "fragment (a coloured place consumed count != 1 or by multiple inputs, carries "
                    + "reset/read/inhibitor arc, or a join re-mints a coloured place); verified via "
                    + "sound over-approximation instead.\n\n");
            }
        }

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
        // (only valid when no sink places — structural check doesn't account for sinks).
        // Skipped when environment places are registered: the siphon/trap analysis runs
        // on the closed net and is blind to env injection (VER-006), so its early proof
        // could be unsound — fall through to the (injection-aware) SMT encoding instead.
        if (property instanceof SmtProperty.DeadlockFree
                && !hasMatch
                && sinkPlaces.isEmpty()
                && environmentPlaces.isEmpty()
                && structResult instanceof StructuralCheck.Result.NoPotentialDeadlock) {
            report.append("=== RESULT ===\n\n");
            report.append("PROVEN (structural): Deadlock-freedom verified by Commoner's theorem.\n");
            report.append("  All siphons contain initially marked traps.\n");
            report.append("  Certificate check: not applicable (structural proof)\n");
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
        // Exact re-validation gate: the elimination in PInvariantComputer uses unchecked
        // long arithmetic, and a numerically wrong invariant conjoined into the CHC
        // transition-rule body REMOVES reachable successors — i.e. it can certify a false
        // PROVEN. computeChecked already drops rows whose exact weight or constant does
        // not fit the int extraction range; only candidates whose y*C = 0 and
        // constant = y*M0 also re-verify exactly may reach an encoder. Both drop channels
        // are reported below.
        var extraction = PInvariantComputer.computeChecked(matrix, flatNet, initialMarking);
        var invariantValidation = PInvariantComputer.validateExact(
            extraction.valid(), matrix, flatNet, initialMarking);
        var invariants = invariantValidation.valid();
        // P-semiflows (non-negative conservation laws) bound the simultaneously-live
        // colour count that sets the name-coloured encoder's slot count k (see
        // NameColouredEncoder.buildPlan / colourSlotBound). Same exact gate: a wrong
        // semiflow would under-bound k and unsound the coloured encoding.
        var semiflowValidation = PInvariantComputer.validateExact(
            PInvariantComputer.computePSemiflows(matrix, flatNet, initialMarking),
            matrix, flatNet, initialMarking);
        var semiflows = semiflowValidation.valid();
        report.append("  Found: ").append(invariants.size()).append(" P-invariant(s)\n");
        if (semiflowInvariants) {
            // See #semiflowInvariants(boolean): the minimal conservation laws, as extra
            // invariants for the encoder.
            var strengthened = new ArrayList<>(invariants);
            int added = 0;
            for (var sf : semiflows) {
                if (!strengthened.contains(sf)) {
                    strengthened.add(sf);
                    added++;
                }
            }
            invariants = List.copyOf(strengthened);
            report.append("  Semiflows encoded as invariants: ").append(added).append("\n");
        }
        // VER-013: canonical invariant order (support, weights, constant), so the
        // strengthened rule bodies and the certificate candidate read the same in every
        // implementation whatever order the elimination produced them in.
        invariants = canonicalInvariantOrder(invariants);
        boolean structurallyBounded = PInvariantComputer.isCoveredByInvariants(invariants, flatNet.placeCount());
        report.append("  Structurally bounded: ").append(structurallyBounded ? "YES" : "NO").append("\n");
        for (var inv : invariants) {
            report.append("  ").append(PInvariantComputer.describe(inv, flatNet)).append("\n");
        }
        for (var reason : extraction.dropped()) {
            report.append("  Dropped invariant: ").append(reason).append("\n");
        }
        for (var reason : invariantValidation.dropped()) {
            report.append("  Dropped invariant: ").append(reason).append("\n");
        }
        for (var reason : semiflowValidation.dropped()) {
            report.append("  Dropped semiflow: ").append(reason).append("\n");
        }
        int droppedTotal = extraction.dropped().size()
            + invariantValidation.dropped().size() + semiflowValidation.dropped().size();
        if (droppedTotal > 0) {
            report.append("  Dropped: ").append(droppedTotal)
                .append(" candidate(s) failed exact re-validation (excluded from encoding)\n");
        }
        report.append("\n");

        // Phase 4: SMT encode + query via Spacer
        report.append("Phase 4: IC3/PDR verification via Z3 Spacer...\n");

        // VER-013: one z3 process per query. Resolve the executable before any
        // encoding work so a missing or too-old solver is reported as such.
        Z3Solver z3;
        try {
            z3 = solver != null ? solver : Z3Solver.resolve();
        } catch (Z3Solver.Z3Unavailable e) {
            String reason = e.getMessage();
            report.append("  Solver: z3 unavailable (").append(reason).append(")\n");
            report.append("  Status: UNKNOWN (").append(reason).append(")\n\n");
            report.append("=== RESULT ===\n\n");
            report.append("UNKNOWN: Could not determine ").append(propertyDescription()).append("\n");
            report.append("  Reason: ").append(reason).append("\n");
            return buildResult(
                new SmtVerificationResult.Verdict.Unknown(reason),
                report.toString(), invariants, List.of(), List.of(), List.of(),
                Duration.between(start, Instant.now()),
                new SmtVerificationResult.SmtStatistics(
                    flatNet.placeCount(), flatNet.transitionCount(),
                    invariants.size(), structResultStr));
        }
        report.append("  Solver: z3 ").append(z3.version()).append("\n");

        // ν-net exact refinement (NU-050 #1, Route A). For a budget-bounded ν-net in
        // the supported mint→matched-join fragment, encode names as a finite colour
        // set (k = the declared budget) with exact same-colour join matching, instead
        // of the name-blind over-approximation — this rules out spurious
        // counterexamples that would equate two distinct names. Reachability-safety AND
        // quiescence (NU-053) properties are both routed here; a net outside the
        // fragment keeps the flat encoding.
        var colouredAttempt = colouredAttempt(flatNet, invariants, () -> semiflows);
        NameColouredEncoder.ColouredPlan colouredPlan = colouredAttempt.plan();

        SmtEncoder.SmtEncoding encoding;
        if (colouredPlan != null) {
            report.append("  ν-encoding: name-coloured (exact within budget k=")
                .append(colouredPlan.k()).append("; ")
                .append(colouredPlan.colouredCount()).append(" coloured place(s))\n");
            encoding = colouredAttempt.encoding();
            if (encoding == null) {
                // The property names a place that does not resolve in the net (e.g. a
                // typo'd bound/pending place). Emitting the encoding anyway would certify
                // a vacuous PROVEN; refuse and report Unknown so a mis-named place never
                // silently certifies.
                String reason = "property names a place that does not resolve in the net; "
                    + "refusing to certify (the encoding would be vacuously proven)";
                report.append("  Status: UNKNOWN (unresolved property place)\n\n");
                report.append("=== RESULT ===\n\n");
                report.append("UNKNOWN: ").append(reason).append("\n");
                return buildResult(
                    new SmtVerificationResult.Verdict.Unknown(reason),
                    report.toString(), invariants, List.of(), List.of(), List.of(),
                    Duration.between(start, Instant.now()),
                    new SmtVerificationResult.SmtStatistics(
                        flatNet.placeCount(), flatNet.transitionCount(),
                        invariants.size(), structResultStr));
            }
        } else {
            // A property naming a place outside the net would encode to a vacuous
            // violation predicate (`false` proves anything). Refuse, as the coloured path
            // does, so a mis-named place never silently certifies.
            String unresolved = unresolvedPropertyPlace(flatNet, property);
            if (unresolved != null) {
                String reason = "property names a place that does not resolve in the net ('"
                    + unresolved + "'); refusing to certify (the encoding would be vacuously proven)";
                report.append("  Status: UNKNOWN (unresolved property place)\n\n");
                report.append("=== RESULT ===\n\n");
                report.append("UNKNOWN: ").append(reason).append("\n");
                return buildResult(
                    new SmtVerificationResult.Verdict.Unknown(reason),
                    report.toString(), invariants, List.of(), List.of(), List.of(),
                    Duration.between(start, Instant.now()),
                    new SmtVerificationResult.SmtStatistics(
                        flatNet.placeCount(), flatNet.transitionCount(),
                        invariants.size(), structResultStr));
            }
            // C3: request the refutation proof the replay decoder reads.
            encoding = SmtEncoder.encode(
                flatNet, initialMarking, property, invariants, sinkPlaces, counterexampleReplay);
        }
        String phase = colouredPlan != null ? "horn-coloured" : "horn";
        var queryResult = SpacerRunner.run(z3, timeout, encoding.smt2(), phase);

        var smtResult = switch (queryResult) {
            case SpacerRunner.QueryResult.Proven(var formula) -> {
                // Guard against silent vacuous proofs (VER-006): in Ignore mode the
                // encoding does not model env injection, so env-gated transitions never
                // fire and ANY safety bound is trivially "proven". Refuse to certify —
                // downgrade to UNKNOWN with actionable guidance.
                if (!environmentPlaces.isEmpty()
                        && environmentMode instanceof EnvironmentAnalysisMode.Ignore) {
                    String reason = IGNORE_MODE_VACUITY_REASON;
                    report.append("  Status: UNSAT, but vacuous under ignore mode\n\n");
                    report.append("=== RESULT ===\n\n");
                    report.append("UNKNOWN: ").append(reason).append("\n");
                    yield buildResult(
                        new SmtVerificationResult.Verdict.Unknown(reason),
                        report.toString(), invariants, List.of(), List.of(), List.of(),
                        Duration.between(start, Instant.now()),
                        new SmtVerificationResult.SmtStatistics(
                            flatNet.placeCount(), flatNet.transitionCount(),
                            invariants.size(), structResultStr)
                    );
                }

                report.append("  Status: UNSAT (property holds)\n\n");

                // Certificate check (flat count encoding only): independently
                // re-validate the IC3 certificate in a second z3 run before the
                // PROVEN verdict is trusted. The coloured (NameColouredEncoder)
                // path is not covered, and structural early proofs return before
                // this phase. Any failure downgrades to UNKNOWN; the checker and
                // this block never propagate an exception.
                if (colouredPlan != null) {
                    report.append("  Certificate check: not applicable (name-coloured encoding)\n\n");
                } else if (!certificateCheck) {
                    report.append("  Certificate check: not applicable (disabled)\n\n");
                } else {
                    CertificateChecker.Result certOutcome;
                    if (formula == null) {
                        certOutcome = new CertificateChecker.Result.Unavailable(
                            "no inductive invariant (define-fun block) could be extracted from the z3 model");
                    } else {
                        try {
                            certOutcome = certificateChecker.run(
                                formula, flatNet, initialMarking, property, sinkPlaces,
                                invariants, z3, timeout);
                        } catch (RuntimeException e) {
                            // A checker that throws must not fail the pipeline.
                            certOutcome = new CertificateChecker.Result.Unavailable(
                                "certificate check threw: " + e);
                        }
                    }
                    String downgrade = certificateDowngradeReason(certOutcome);
                    if (downgrade == null) {
                        report.append("  Certificate check: PASSED (init, consecution, safety)\n\n");
                    } else {
                        report.append("  Certificate check: FAILED\n\n");
                        report.append("=== RESULT ===\n\n");
                        report.append("UNKNOWN: ").append(downgrade).append("\n");
                        yield buildResult(
                            new SmtVerificationResult.Verdict.Unknown(downgrade),
                            report.toString(), invariants, List.of(), List.of(), List.of(),
                            Duration.between(start, Instant.now()),
                            new SmtVerificationResult.SmtStatistics(
                                flatNet.placeCount(), flatNet.transitionCount(),
                                invariants.size(), structResultStr));
                    }
                }

                // The inductive invariant is the (define-fun …) block of the model,
                // verbatim (the certificate the check above re-validated).
                List<String> discoveredInvariants = formula != null ? List.of(formula) : List.of();

                // Phase 5: Inductive invariant
                if (formula != null) {
                    report.append("Phase 5: Inductive invariant (discovered by IC3)\n");
                    report.append("  Spacer synthesized:\n");
                    formula.lines().forEach(line -> report.append("    ").append(line).append("\n"));
                    report.append("  This formula is INDUCTIVE: preserved by all transitions.\n\n");
                }

                report.append("=== RESULT ===\n\n");
                report.append("PROVEN (IC3/PDR): ").append(propertyDescription()).append("\n");
                report.append("  Z3 Spacer proved no reachable state violates the property.\n");
                report.append("  NOTE: Verification ignores timing constraints and Java guards.\n");
                report.append("  An untimed proof is STRONGER than a timed one ");
                report.append("(timing only restricts behavior).\n");

                yield buildResult(
                    new SmtVerificationResult.Verdict.Proven("IC3/PDR", formula),
                    report.toString(), invariants, discoveredInvariants, List.of(), List.of(),
                    Duration.between(start, Instant.now()),
                    new SmtVerificationResult.SmtStatistics(
                        flatNet.placeCount(), flatNet.transitionCount(),
                        invariants.size(), structResultStr)
                );
            }

            case SpacerRunner.QueryResult.Violated(var answer) -> {
                report.append("  Status: SAT (counterexample found)\n\n");

                // Decode the counterexample as an order-free marking set; the
                // execution order is reconstructed by the abstract replay below.
                var decoded = CounterexampleDecoder.decode(answer, flatNet);
                if (decoded.note() != null) {
                    report.append("  Counterexample decoding: ").append(decoded.note()).append("\n");
                }
                List<MarkingState> decodedList = List.copyOf(decoded.states());

                var stats = new SmtVerificationResult.SmtStatistics(
                    flatNet.placeCount(), flatNet.transitionCount(),
                    invariants.size(), structResultStr);

                if (!counterexampleReplay) {
                    report.append("  Counterexample replay: disabled (counterexampleReplay(false))\n\n");
                    report.append("=== RESULT ===\n\n");
                    report.append("VIOLATED: ").append(propertyDescription()).append("\n");
                    appendDecodedStates(report, decoded);
                    appendUntimedCaveat(report);
                    // Replay did not apply, so the tri-state stays null (not false).
                    yield buildResult(
                        new SmtVerificationResult.Verdict.Violated(),
                        report.toString(), invariants, List.of(),
                        decodedList, List.of(), null,
                        Duration.between(start, Instant.now()), stats);
                }

                // Counterexample replay (C3): confirm the decoded states as an
                // actual abstract run, or refuse to report a violation the
                // abstraction itself cannot reproduce.
                var assessment = assessCounterexample(
                    flatNet, initialMarking, decoded, property, sinkPlaces,
                    replayStateSetOverride, replayNodeBudget);
                yield switch (assessment) {
                    case ReplayAssessment.Confirmed(var trace, var firings) -> {
                        report.append("  Counterexample replay: CONFIRMED — the decoded states chain ")
                              .append("into an abstract run reaching the violation.\n\n");
                        report.append("=== RESULT ===\n\n");
                        report.append("VIOLATED: ").append(propertyDescription()).append("\n");
                        report.append("  Replay-ordered trace (").append(trace.size()).append(" states):\n");
                        for (int i = 0; i < trace.size(); i++) {
                            report.append("    ").append(i).append(": ").append(trace.get(i));
                            if (i > 0) {
                                report.append("   [").append(firings.get(i - 1)).append("]");
                            }
                            report.append("\n");
                        }
                        appendUntimedCaveat(report);
                        yield buildResult(
                            new SmtVerificationResult.Verdict.Violated(),
                            report.toString(), invariants, List.of(), trace, firings, Boolean.TRUE,
                            Duration.between(start, Instant.now()), stats);
                    }
                    case ReplayAssessment.Unconfirmed(var note) -> {
                        report.append("  Counterexample replay: not confirmed — ").append(note).append("\n\n");
                        report.append("=== RESULT ===\n\n");
                        report.append("VIOLATED: ").append(propertyDescription()).append("\n");
                        report.append("  NOTE: ").append(note).append("\n");
                        appendDecodedStates(report, decoded);
                        appendUntimedCaveat(report);
                        yield buildResult(
                            new SmtVerificationResult.Verdict.Violated(),
                            report.toString(), invariants, List.of(),
                            decodedList, List.of(), Boolean.FALSE,
                            Duration.between(start, Instant.now()), stats);
                    }
                    case ReplayAssessment.Downgraded(var reason) -> {
                        report.append("  Counterexample replay: FAILED\n");
                        appendDecodedStates(report, decoded);
                        report.append("\n=== RESULT ===\n\n");
                        report.append("UNKNOWN: ").append(reason).append("\n");
                        // The replay APPLIED and refuted the trace, which is strictly
                        // more informative than "did not apply": FALSE, never null.
                        yield buildResult(
                            new SmtVerificationResult.Verdict.Unknown(reason),
                            report.toString(), invariants, List.of(), List.of(), List.of(),
                            Boolean.FALSE, Duration.between(start, Instant.now()), stats);
                    }
                };
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
        return applyNuGuard(smtResult, hasMatch, nuBounded, colouredPlan != null);
    }

    private String propertyDescription() {
        return switch (property) {
            case SmtProperty.DeadlockFree() -> sinkPlaces.isEmpty()
                ? "Deadlock-freedom"
                : "Deadlock-freedom (sinks: " + sinkPlaces.stream()
                    .map(Place::name).collect(Collectors.joining(", ")) + ")";
            case SmtProperty.TerminatesAtSink() -> sinkPlaces.isEmpty()
                ? "Terminates at a declared sink"
                : "Terminates at a declared sink (sinks: " + sinkPlaces.stream()
                    .map(Place::name).collect(Collectors.joining(", ")) + ")";
            case SmtProperty.MutualExclusion me ->
                "Mutual exclusion of " + me.p1().name() + " and " + me.p2().name();
            case SmtProperty.PlaceBound pb ->
                "Place " + pb.place().name() + " bounded by " + pb.bound();
            case SmtProperty.Unreachable ur ->
                "Unreachability of marking with tokens in " + ur.places();
            case SmtProperty.BranchPlaceBound bpb ->
                "Branch place bound (ν-budget): " + bpb.place().name() + " <= " + bpb.bound();
            case SmtProperty.JoinedOrDeadLettered jdl ->
                "Joined-or-dead-lettered: " + jdl.pending().name() + " = 0 at quiescence";
        };
    }

    /**
     * The SMT-LIB2 scripts {@link #verify()} would send to z3 for this configuration,
     * without running a solver (VER-013 AC1): the HORN query (flat, or name-coloured
     * when a declared budget puts the net on Route A's exact encoding) and, for the
     * flat encoding, the certificate-check script built around
     * {@link #placeholderCertificate}. This is what the cross-language golden tests
     * diff byte for byte. Route B, the structural pre-check and the unresolved-place
     * refusal are bypassed: it is what Route A encodes.
     *
     * @param horn        the HORN query, flat or name-coloured
     * @param certificate the certificate-check script around the placeholder
     *                    certificate; {@code null} for the name-coloured encoding
     * @param coloured    whether {@code horn} is the name-coloured encoding
     */
    public record EncodedScripts(String horn, String certificate, boolean coloured) {}

    /**
     * {@code (define-fun Reachable ((x!0 Int) …) Bool true)}: the certificate stand-in
     * the golden certificate scripts are built around (a real certificate is solver
     * output and never part of a golden).
     */
    public static String placeholderCertificate(int placeCount) {
        var params = new ArrayList<String>(placeCount);
        for (int i = 0; i < placeCount; i++) {
            params.add("(x!" + i + " Int)");
        }
        return "(define-fun Reachable (" + String.join(" ", params) + ") Bool\n    true)";
    }

    /**
     * The name-coloured plan and its encoding, or a null plan when the net is outside
     * the fragment ([NU-050]) and a null encoding when the property names a place the
     * net does not resolve.
     *
     * <p>{@link #verify()} and {@link #encodeScripts()} share this deliberately. They
     * used to invoke {@code buildPlan} and {@code encode} separately, a few hundred
     * lines apart, so handing the encoder the wrong one of the two lists changed only
     * one of them — and the script-parity goldens are generated from
     * {@code encodeScripts}. Unifying the invocation closes that. It does not make the
     * two paths identical: each still computes its own invariant and semiflow lists, so
     * they can still drift through the arguments rather than through the call.
     *
     * @param invariants what the encoder conjoins into every rule body: the null-space
     *                   basis, unioned with the semiflows when [VER-007] is enabled
     * @param semiflows  supplies the gate-validated semiflows, which set the colour-slot
     *                   bound {@code k} ([NU-053]) and are <em>not</em> the same list.
     *                   Deferred so a flat net never pays for the enumeration.
     */
    private ColouredAttempt colouredAttempt(
            FlatNet flatNet, List<PInvariant> invariants, Supplier<List<PInvariant>> semiflows) {
        boolean hasMatch = net.transitions().stream().anyMatch(t -> t.matchSpec() != null);
        boolean nuBounded = !budgetPlaces.isEmpty();
        if (!hasMatch || !nuBounded) {
            return new ColouredAttempt(null, null);
        }
        // Supplied rather than passed by value: Java evaluates arguments eagerly, so a
        // plain parameter would run the Farkas enumeration on every encodeScripts()
        // call, including the flat nets that never reach this line.
        var plan = NameColouredEncoder.buildPlan(
            net, flatNet, initialMarking, budgetPlaces, fragmentMode, carrierPlaces,
            semiflows.get());
        if (plan == null) {
            return new ColouredAttempt(null, null);
        }
        return new ColouredAttempt(plan, NameColouredEncoder.encode(
            plan, flatNet, initialMarking, property, invariants, sinkPlaces));
    }

    /** A coloured plan and the encoding built from it; see {@link #colouredAttempt}. */
    private record ColouredAttempt(
        NameColouredEncoder.ColouredPlan plan,
        SmtEncoder.SmtEncoding encoding
    ) {}

    /** See {@link EncodedScripts}. */
    public EncodedScripts encodeScripts() {
        OutputActionCheck.requireOutputProducingActions(net);
        FlatNet flatNet = NetFlattener.flatten(net, environmentPlaces, environmentMode);
        var invariants = encoderInvariants(flatNet, initialMarking, semiflowInvariants);
        var coloured = colouredAttempt(
            flatNet, invariants, () -> validatedSemiflows(flatNet, initialMarking));
        if (coloured.encoding() != null) {
            return new EncodedScripts(coloured.encoding().smt2(), null, true);
        }
        String horn = SmtEncoder.encode(
            flatNet, initialMarking, property, invariants, sinkPlaces, counterexampleReplay).smt2();
        String certificate = CertificateChecker.vcScript(
            placeholderCertificate(flatNet.placeCount()), flatNet, initialMarking, property,
            sinkPlaces, invariants);
        return new EncodedScripts(horn, certificate, false);
    }

    /** The name of the first place the property names that is not in the flat net, or {@code null}. */
    private static String unresolvedPropertyPlace(FlatNet flatNet, SmtProperty property) {
        List<Place<?>> named = switch (property) {
            case SmtProperty.DeadlockFree() -> List.of();
            case SmtProperty.TerminatesAtSink() -> List.of();
            case SmtProperty.MutualExclusion me -> List.of(me.p1(), me.p2());
            case SmtProperty.PlaceBound pb -> List.of(pb.place());
            case SmtProperty.BranchPlaceBound bpb -> List.of(bpb.place());
            case SmtProperty.Unreachable ur -> List.copyOf(ur.places());
            case SmtProperty.JoinedOrDeadLettered jdl -> List.of(jdl.pending());
        };
        for (var place : named) {
            if (flatNet.indexOf(place) < 0) {
                return place.name();
            }
        }
        return null;
    }

    /**
     * The invariants exactly as {@link #verify} hands them to the encoders: the checked
     * null-space rows that pass the exact gate, plus the validated semiflows when
     * {@code semiflowInvariants} is on, in canonical order. Package-private for the
     * script-parity tests.
     */
    static List<PInvariant> encoderInvariants(
            FlatNet flatNet, MarkingState initialMarking, boolean semiflowInvariants
    ) {
        var matrix = IncidenceMatrix.from(flatNet);
        var extraction = PInvariantComputer.computeChecked(matrix, flatNet, initialMarking);
        List<PInvariant> invariants = PInvariantComputer.validateExact(
            extraction.valid(), matrix, flatNet, initialMarking).valid();
        if (semiflowInvariants) {
            var semiflows = PInvariantComputer.validateExact(
                PInvariantComputer.computePSemiflows(matrix, flatNet, initialMarking),
                matrix, flatNet, initialMarking).valid();
            var strengthened = new ArrayList<>(invariants);
            for (var sf : semiflows) {
                if (!strengthened.contains(sf)) {
                    strengthened.add(sf);
                }
            }
            invariants = strengthened;
        }
        return canonicalInvariantOrder(invariants);
    }

    /** The validated P-semiflows the coloured plan is built from (script-parity tests). */
    static List<PInvariant> validatedSemiflows(FlatNet flatNet, MarkingState initialMarking) {
        var matrix = IncidenceMatrix.from(flatNet);
        return PInvariantComputer.validateExact(
            PInvariantComputer.computePSemiflows(matrix, flatNet, initialMarking),
            matrix, flatNet, initialMarking).valid();
    }

    /**
     * The invariants in canonical order (VER-013): by ascending support, then weights,
     * then constant, each compared lexicographically. The same order the Rust and
     * TypeScript verifiers apply, so the strengthened scripts are byte-identical.
     */
    static List<PInvariant> canonicalInvariantOrder(List<PInvariant> invariants) {
        var sorted = new ArrayList<>(invariants);
        sorted.sort((a, b) -> {
            int c = compareLex(sortedSupport(a), sortedSupport(b));
            if (c != 0) {
                return c;
            }
            c = Arrays.compare(a.weights(), b.weights());
            if (c != 0) {
                return c;
            }
            return Integer.compare(a.constant(), b.constant());
        });
        return List.copyOf(sorted);
    }

    private static int[] sortedSupport(PInvariant inv) {
        return inv.support().stream().mapToInt(Integer::intValue).sorted().toArray();
    }

    private static int compareLex(int[] a, int[] b) {
        return Arrays.compare(a, b);
    }

    /** Result for a path where abstract replay does not apply (confirmed = null). */
    private static SmtVerificationResult buildResult(
            SmtVerificationResult.Verdict verdict, String report,
            List<PInvariant> invariants, List<String> discoveredInvariants,
            List<MarkingState> trace, List<String> transitions,
            Duration elapsed, SmtVerificationResult.SmtStatistics stats
    ) {
        return buildResult(verdict, report, invariants, discoveredInvariants,
            trace, transitions, null, elapsed, stats);
    }

    private static SmtVerificationResult buildResult(
            SmtVerificationResult.Verdict verdict, String report,
            List<PInvariant> invariants, List<String> discoveredInvariants,
            List<MarkingState> trace, List<String> transitions,
            Boolean counterexampleConfirmed,
            Duration elapsed, SmtVerificationResult.SmtStatistics stats
    ) {
        return new SmtVerificationResult(verdict, report, invariants, discoveredInvariants,
            trace, transitions, counterexampleConfirmed, elapsed, stats);
    }

    /**
     * ν-net soundness guard (NU-040, NU-050). Applied only when the net contains
     * match (ν-join) transitions, and only to a Proven/Violated verdict (an
     * existing Unknown is left as-is).
     *
     * <ul>
     *   <li>Quiescence-based properties (deadlock / joined-or-dead-lettered):
     *       the name-blind over-approximation over-fires joins, so it sees fewer
     *       quiescent states and may miss a real stranded marking — downgraded
     *       to Unknown (exact quiescence reasoning is deferred to the SCG
     *       name-partition quotient).</li>
     *   <li>Reachability-safety with unbounded fresh names (no budget declared):
     *       reachability over unbounded fresh names is undecidable — Unknown.</li>
     *   <li>Bounded reachability-safety in the name-coloured fragment
     *       ({@code exact}): name equality is encoded exactly via bounded
     *       name-colouring, so the verdict is sound <em>and</em> complete within
     *       the budget — no spurious different-name counterexample. The verdict is
     *       kept and the exact-path note is appended.</li>
     *   <li>Bounded reachability-safety outside that fragment: {@code Proven} is
     *       sound; a {@code Violated} may be spurious — the verdict is kept and the
     *       over-approximation caveat is appended.</li>
     * </ul>
     */
    private SmtVerificationResult applyNuGuard(
            SmtVerificationResult result, boolean hasMatch, boolean nuBounded, boolean exact
    ) {
        if (!hasMatch || result.verdict() instanceof SmtVerificationResult.Verdict.Unknown) {
            return result;
        }
        // Exact path (NU-050 #1 / NU-053, Route A) is checked FIRST: name equality is
        // encoded exactly via bounded name-colouring, so the verdict is sound AND complete
        // within the budget bound — no spurious different-name counterexample. This holds
        // for reachability-safety AND quiescence (deadlock / joined-or-dead-lettered), so
        // the quiescence downgrade below does NOT apply when an exact coloured plan was
        // used — the colour-aware deadlock encoding does not over-fire joins.
        if (exact) {
            String note = "\nNote: ν-join name equality is encoded exactly via bounded name-colouring "
                + "(k = budget); the verdict is sound and complete within the budget bound — no "
                + "spurious different-name counterexample (NU-050 #1 / NU-053).\n";
            return new SmtVerificationResult(
                result.verdict(), result.report() + note, result.invariants(),
                result.discoveredInvariants(), result.counterexampleTrace(),
                result.counterexampleTransitions(), result.counterexampleConfirmed(),
                result.elapsed(), result.statistics());
        }
        if (!isReachabilitySafety(property)) {
            return downgradeToUnknown(result,
                "ν-matching transitions present and the property depends on quiescence "
                + "(deadlock / joined-or-dead-lettered); the name-blind over-approximation "
                + "cannot decide it soundly — deferred to the exact ν-analysis (NU-050)");
        }
        if (!nuBounded) {
            return downgradeToUnknown(result,
                "ν-matching transitions present with unbounded fresh names (no budget place "
                + "declared via budgetPlaces(...)); reachability over unbounded fresh names is "
                + "undecidable (NU-040) — declare the budget place(s) that gate minting to "
                + "verify within the bounded fragment");
        }
        // Bounded reachability-safety outside the name-coloured fragment: `Proven` is
        // sound; a `Violated` counterexample may be spurious pending the exact ν-analysis.
        String note = "\nNote: matched (ν-join) transitions are over-approximated (name equality "
            + "assumed satisfiable). 'Proven' is sound; a 'Violated' counterexample may be "
            + "spurious pending the exact ν-analysis (NU-050).\n";
        return new SmtVerificationResult(
            result.verdict(), result.report() + note, result.invariants(),
            result.discoveredInvariants(), result.counterexampleTrace(),
            result.counterexampleTransitions(), result.counterexampleConfirmed(),
            result.elapsed(), result.statistics());
    }

    private static SmtVerificationResult downgradeToUnknown(
            SmtVerificationResult result, String reason
    ) {
        String report = result.report() + "\nDowngraded to UNKNOWN: " + reason + "\n";
        return new SmtVerificationResult(
            new SmtVerificationResult.Verdict.Unknown(reason), report, result.invariants(),
            List.of(), List.of(), List.of(), null, result.elapsed(), result.statistics());
    }

    /**
     * Whether a property is a <em>reachability-safety</em> property — one whose
     * violation is a reachable bad marking. For these the matched-transition
     * over-approximation is sound for {@code Proven}. Quiescence-based
     * properties (deadlock, terminates-at-sink, joined-or-dead-lettered) are
     * not: their violation
     * involves the absence of enabled transitions, which the name-blind
     * over-approximation distorts unsafely (NU-050).
     */
    private static boolean isReachabilitySafety(SmtProperty property) {
        return switch (property) {
            case SmtProperty.PlaceBound _ -> true;
            case SmtProperty.BranchPlaceBound _ -> true;
            case SmtProperty.MutualExclusion _ -> true;
            case SmtProperty.Unreachable _ -> true;
            case SmtProperty.DeadlockFree _ -> false;
            case SmtProperty.TerminatesAtSink _ -> false;
            case SmtProperty.JoinedOrDeadLettered _ -> false;
        };
    }

    /**
     * Assessment of a decoded counterexample by abstract replay. Package-private
     * and free of Z3 types, so the verdict mapping is testable without the
     * native library (mirror of the {@link #certificateDowngradeReason} design).
     */
    sealed interface ReplayAssessment {
        /** The decoded states chain into an abstract run reaching the violation. */
        record Confirmed(List<MarkingState> trace, List<String> firings) implements ReplayAssessment {}

        /** The replay could not decide; the VIOLATED verdict stands, unconfirmed. */
        record Unconfirmed(String note) implements ReplayAssessment {}

        /** The search found no chain at all; the verdict must not be trusted. */
        record Downgraded(String reason) implements ReplayAssessment {}
    }

    /**
     * Maps a decode result to the replay assessment. Pure — no Z3 call: the
     * property-violation predicate is evaluated Java-side by
     * {@link AbstractReplayer#violates}.
     *
     * <p>Only a search that RAN TO COMPLETION and found no chain withdraws the
     * verdict ({@link ReplayAssessment.Downgraded}): the abstraction is untimed
     * and value-blind (VER-004 over-approximation), so such a counterexample is
     * spurious or the decoder mis-read the derivation. A search that could not
     * decide — nothing decoded, M0 not among the decoded states, budget
     * exhausted — leaves VIOLATED standing as
     * {@link ReplayAssessment.Unconfirmed}: nothing contradicts the solver.
     */
    static ReplayAssessment assessCounterexample(
            FlatNet flatNet, MarkingState initialMarking,
            CounterexampleDecoder.DecodedStates decoded,
            SmtProperty property, Set<Place<?>> sinkPlaces
    ) {
        return assessCounterexample(flatNet, initialMarking, decoded, property, sinkPlaces,
            null, AbstractReplayer.DEFAULT_NODE_BUDGET);
    }

    /**
     * {@link #assessCounterexample(FlatNet, MarkingState, CounterexampleDecoder.DecodedStates,
     * SmtProperty, Set)} with the two test seams applied: {@code stateSetOverride}
     * replaces the decoded anchor set when non-null, {@code nodeBudget} the replay's
     * node budget.
     */
    static ReplayAssessment assessCounterexample(
            FlatNet flatNet, MarkingState initialMarking,
            CounterexampleDecoder.DecodedStates decoded,
            SmtProperty property, Set<Place<?>> sinkPlaces,
            Set<MarkingState> stateSetOverride, int nodeBudget
    ) {
        Set<MarkingState> states =
            stateSetOverride != null ? stateSetOverride : decoded.states();
        if (states.isEmpty()) {
            return new ReplayAssessment.Unconfirmed(
                "no counterexample states could be decoded from the Spacer answer, so the "
                + "abstract replay could not run; the verdict stands, unconfirmed");
        }
        AbstractReplayer.ReplayOutcome outcome;
        try {
            outcome = AbstractReplayer.replay(
                flatNet, initialMarking, states, property, sinkPlaces,
                AbstractReplayer.MAX_SEGMENT_STEPS, nodeBudget);
        } catch (RuntimeException e) {
            // A replayer bug must leave the verdict alone, never crash it and never
            // withdraw it on the strength of a bug.
            outcome = new AbstractReplayer.ReplayOutcome.Exhausted("replay threw: " + e);
        }
        return switch (outcome) {
            case AbstractReplayer.ReplayOutcome.Confirmed(var trace, var firings) ->
                new ReplayAssessment.Confirmed(trace, firings);
            case AbstractReplayer.ReplayOutcome.Exhausted(var why) ->
                new ReplayAssessment.Unconfirmed(
                    "the abstract replay could not run to completion (" + why
                    + "); the verdict stands, unconfirmed");
            case AbstractReplayer.ReplayOutcome.NoChain _ ->
                new ReplayAssessment.Downgraded(REPLAY_NO_CHAIN_REASON);
        };
    }

    /**
     * The canonical UNKNOWN reason for a completed replay that found no chain —
     * byte-identical across the Java, TypeScript, Rust and Python verifiers.
     */
    static final String REPLAY_NO_CHAIN_REASON =
        "counterexample replay found no firing chain to the violation under the "
        + "abstract semantics, so VIOLATED is withheld";

    /** Decoded-state listing for the report, in proof-text order (not a firing order). */
    private static void appendDecodedStates(
            StringBuilder report, CounterexampleDecoder.DecodedStates decoded
    ) {
        if (!decoded.states().isEmpty()) {
            report.append("  Decoded states (proof order, ")
                  .append(decoded.states().size()).append(" markings):\n");
            for (var state : decoded.states()) {
                report.append("    - ").append(state).append("\n");
            }
        }
    }

    /** The standing abstraction caveat on every reported counterexample. */
    private static void appendUntimedCaveat(StringBuilder report) {
        report.append("\n  WARNING: This counterexample is in UNTIMED semantics.\n");
        report.append("  It may be spurious if timing constraints prevent this sequence.\n");
        report.append("  Java guards are also ignored in this analysis.\n");
    }

    /**
     * Signature of the certificate check invoked on a flat-encoding PROVEN
     * verdict. Package-private so tests can inject outcomes without a solver; the
     * default implementation is {@link CertificateChecker#check}.
     */
    @FunctionalInterface
    interface CertificateCheck {
        CertificateChecker.Result run(
            String certificate,
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            List<PInvariant> invariants,
            Z3Solver solver,
            Duration timeout);
    }

    /**
     * Maps a certificate-check outcome to the UNKNOWN downgrade reason, or
     * {@code null} when the PROVEN verdict stands. Package-private (static, no
     * Z3 involvement) so the verdict plumbing is testable without the native
     * library.
     */
    static String certificateDowngradeReason(CertificateChecker.Result outcome) {
        return switch (outcome) {
            case CertificateChecker.Result.Passed() -> null;
            case CertificateChecker.Result.Failed(var vc, var detail) ->
                // The " - <detail>" clause is UNCONDITIONAL: a conditional one would
                // let Java render a reason shape no sibling implementation can.
                "certificate check failed: " + vc.label() + " was not UNSAT"
                    + " - " + detail
                    + "; the IC3 certificate could not be independently re-validated "
                    + "against the unstrengthened step relation, so PROVEN is withheld";
            case CertificateChecker.Result.Unavailable(var reason) ->
                "certificate check could not run: " + reason
                    + "; PROVEN is withheld without an independently validated certificate";
        };
    }
}
