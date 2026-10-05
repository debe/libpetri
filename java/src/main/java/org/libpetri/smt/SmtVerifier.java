package org.libpetri.smt;

import org.libpetri.analysis.InFlight;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.NameFragment;
import org.libpetri.analysis.PrioritySemantics;
import org.libpetri.analysis.StateClassGraph;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.core.internal.ArcDiagnostics;
import org.libpetri.core.internal.CodePointOrder;
import org.libpetri.core.internal.OutputActionCheck;
import org.libpetri.core.internal.TerminalEncoding;
import org.libpetri.core.internal.VerificationDeadline;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;
import org.libpetri.smt.encoding.IncidenceMatrix;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.invariant.PInvariant;
import org.libpetri.smt.invariant.PInvariantComputer;
import org.libpetri.smt.invariant.StructuralCheck;
import org.libpetri.smt.opennet.ClosedNetSteps;
import org.libpetri.smt.opennet.OpenNetClosure;
import org.libpetri.smt.opennet.OpenNetContract;
import org.libpetri.smt.z3.AbstractReplayer;
import org.libpetri.smt.z3.BoundedRun;
import org.libpetri.smt.z3.CertificateChecker;
import org.libpetri.smt.z3.CounterexampleDecoder;
import org.libpetri.smt.z3.LinearBound;
import org.libpetri.smt.z3.NameColouredEncoder;
import org.libpetri.smt.z3.SlotBoundLp;
import org.libpetri.smt.z3.SmtEncoder;
import org.libpetri.smt.z3.SmtText;
import org.libpetri.smt.z3.SpacerRunner;
import org.libpetri.smt.z3.StateEquationPhase;
import org.libpetri.smt.z3.StateEquationQuery;
import org.libpetri.smt.z3.Z3Process;
import org.libpetri.smt.z3.Z3Solver;

import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;

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
 *   <li><b>Bounded state-space enumeration</b> - on an untimed net with no &nu;-joins and
 *       no environment places, build the state-class graph up to
 *       {@link #enumerationMaxClasses(int)} and read the verdict off it; the rest of the
 *       pipeline runs only when the graph exceeds the budget ([VER-017])</li>
 *   <li><b>Flatten</b> - expand XOR, index places, build pre/post vectors</li>
 *   <li><b>Structural pre-check</b> - siphon/trap analysis (may prove early)</li>
 *   <li><b>P-invariants</b> - compute conservation laws for strengthening</li>
 *   <li><b>Linear state-equation bound</b> - a reachability-safety property whose
 *       violation exceeds a decreasing conservation law {@code y·M <= y·M0} is proven
 *       structurally from one linear query, before any fixpoint search, a &nu;-net's
 *       name-coloured one included ([VER-015];
 *       {@link #linearBound(boolean)})</li>
 *   <li><b>State-equation phase</b> - one linear query over the marking equation, refined
 *       with traps and inductive inequalities until it proves the property, finds a run that
 *       violates it, or steps aside ([VER-018]; {@link #stateEquationPhase(boolean)})</li>
 *   <li><b>Firing bound</b> - when a ranking bounds every run, a bounded model check to that
 *       length decides the property ([VER-019]; {@link #firingBound(boolean)})</li>
 *   <li><b>SMT encode + query</b> - IC3/PDR via Z3 Spacer, optionally over the state
 *       equation with firing counters ([VER-016]; {@link #stateEquation(boolean)}) and
 *       reading quiescent markings against the declared and conditional sinks
 *       ([VER-014]; {@link #sinkPlaces(Place...)}, {@link #sinkPlacesWhen(Place, Place...)})</li>
 *   <li><b>Decode result</b> - proof or counterexample trace</li>
 * </ol>
 *
 * @see SmtProperty
 * @see SmtVerificationResult
 */
public final class SmtVerifier {

    /**
     * Not final: {@link #prepare()} swaps in the arrivals closure, the in-flight split
     * ([VER-004]) and the terminal encoding ([EXEC-042]).
     */
    private PetriNet net;
    /**
     * The net as the caller passed it, before any rewrite: with {@link #inFlightSplit}, the
     * {@link StateSpaceCache} key, since the rewrites build a new instance per verification.
     */
    private final PetriNet callerNet;
    private StateSpaceCache stateSpaceCache = null;
    /** The marking every route reads: the caller's, closed under {@code arrivals(k)} when that applied. */
    private MarkingState initialMarking = MarkingState.empty();
    /** The initial marking as the caller set it, before the arrivals closure. */
    private MarkingState callerMarking = MarkingState.empty();
    /** The environment places as the caller declared them, before the arrivals closure. */
    private final Set<EnvironmentPlace<?>> callerEnvironmentPlaces = new LinkedHashSet<>();
    /** The inputs the arrivals closure last ran on; {@code null} before the first call. */
    private ArrivalsInputs arrivalsInputs = null;

    /** What the arrivals closure of [VER-006] depends on besides the net. */
    private record ArrivalsInputs(
        EnvironmentAnalysisMode mode, List<EnvironmentPlace<?>> places, MarkingState marking) {}
    private SmtProperty property = SmtProperty.deadlockFree();
    /** Registration order: {@code arrivals(k)} numbers its sources by it ([VER-006]). */
    private final Set<EnvironmentPlace<?>> environmentPlaces = new LinkedHashSet<>();
    /** The {@code arrivals(k)} rewrite {@link #applyArrivals()} applied, or {@code null}. */
    private ArrivalsRewrite arrivals = null;
    /** Declaration order: the report renders the sinks as they were declared ([VER-014]). */
    private final Set<Place<?>> sinkPlaces = new LinkedHashSet<>();
    /** Conditional sinks by marker, in declaration order; repeated markers accumulate. */
    private final Map<Place<?>, Set<Place<?>>> conditionalSinks = new LinkedHashMap<>();
    /** The places {@link #applyNetTerminals()} added to each terminal's excused set, not the caller. */
    private final Map<Place<?>, Set<Place<?>>> terminalExcused = new HashMap<>();
    private final Set<String> budgetPlaces = new HashSet<>();
    /** Transitions declared to mint a fresh ν-name (NU-010); see {@link #mintTransitions}. */
    private final Set<String> mintTransitions = new HashSet<>();
    private EnvironmentAnalysisMode environmentMode = EnvironmentAnalysisMode.alwaysAvailable();

    /**
     * Why a {@code Proven} is refused under {@link EnvironmentAnalysisMode#ignore()}
     * ([VER-006]). Shared by every route that can return {@code Proven}, so the two
     * guards cannot drift apart.
     */
    private static final String IGNORE_MODE_VACUITY_REASON =
        "environment places present but not modeled (mode=ignore); "
        + "a proof would be vacuous — use alwaysAvailable() or bounded(k) to model external injection";

    /**
     * The [VER-006] AC6 note: a quiescence verdict on a net that can never come to rest is
     * vacuously true. Shared by Route B and the solver path so the two cannot drift apart.
     */
    static final String QUIESCENCE_VACUITY_NOTE =
        "NOTE: no marking of this net can be quiescent — a transition is "
        + "enabled in every marking (an environment-gated one under modelled injection, "
        + "VER-006). Every quiescence property is therefore vacuously true here, and a "
        + "`proven` says nothing about the net.";
    private Duration timeout = Duration.ofSeconds(60);
    private int nuMaxClasses = 100_000;
    private FragmentMode fragmentMode = FragmentMode.BASE;
    private final Set<String> carrierPlaces = new HashSet<>();
    private PrioritySemantics prioritySemantics = PrioritySemantics.NONE;
    private boolean certificateCheck = true;
    private boolean counterexampleReplay = true;
    private SemiflowMode semiflowInvariants = SemiflowMode.OFF;
    private int enumerationMaxClasses = 50_000;
    private boolean linearBound = true;
    private boolean stateEquation = false;
    private boolean stateEquationPhase = true;
    private boolean firingBound = true;
    private CertificateCheck certificateChecker = CertificateChecker::check;
    private Z3Solver solver = null;
    private Set<MarkingState> replayStateSetOverride = null;
    private int replayNodeBudget = AbstractReplayer.DEFAULT_NODE_BUDGET;
    private Duration totalBudget = null;
    private boolean timedCounterexampleCheck = false;
    /** Quiescence read strictly, as if no transition were reaped ([TIME-013]); see {@link #assumeNoReaping}. */
    private boolean assumeNoReaping = false;
    /**
     * The reapable transitions named by the open-net route before it strips the timing
     * ([VER-022]); {@code null} names them off {@link #callerNet}.
     */
    private Set<String> reapableOverride = null;
    /** Every firing read as one step ([VER-004]); see {@link #assumeAtomicFiring}. */
    private boolean assumeAtomicFiring = false;
    /** The transitions modelling the environment of a closed open net ([VER-022]), left atomic. */
    private Set<String> environmentSteps = Set.of();
    /** The report line of the in-flight split ([VER-004]), once {@link #applyInFlight} ran. */
    private String inFlightLine = null;
    /** Why the in-flight split cannot express this net ([VER-004]); every route declines when set. */
    private String inFlightRefusal = null;
    /**
     * The net after the arrivals closure and before every later rewrite, kept so the in-flight
     * split can be redone from it when its inputs change; {@code null} before the first call.
     */
    private PetriNet preSplitNet = null;
    /** The inputs the current in-flight split was computed from; {@code null} before the first call. */
    private InFlightInputs inFlightInputs = null;
    /**
     * Conflict priority ([NU-052]) turned off for this configuration, because a transition the
     * pruning needs split cannot be ({@link #applyInFlight}); see {@link #effectivePriority()}.
     */
    private boolean conflictOff = false;

    /**
     * What the in-flight split of [VER-004] depends on besides the net: the options, and the
     * demands of the property ({@link InFlight#quiescentCountDemand}) and of conflict priority
     * ({@link InFlight#conflictDemand}).
     */
    private record InFlightInputs(
        boolean atomic, Set<String> carriers, Set<String> environment,
        InFlight.SplitDemand terminal, InFlight.SplitDemand conflict) {}
    /** The transitions the in-flight split rewrote ([VER-004]), in net order; empty when none was. */
    private List<String> inFlightSplit = List.of();
    /**
     * The route the running step of the calling {@link #verify()} belongs to, for the result of a
     * budget exhaustion or a cancellation. Bound per call, never an instance field, so calls
     * sharing one verifier on different threads cannot see each other's step.
     */
    private static final ScopedValue<RunningRoute> RUNNING_ROUTE = ScopedValue.newInstance();

    /** The per-call holder of the running route; written and read on the verifying thread only. */
    private static final class RunningRoute {
        SmtVerificationResult.Route route = SmtVerificationResult.Route.UNAVAILABLE;
    }

    private SmtVerifier(PetriNet net) {
        this.net = Objects.requireNonNull(net);
        this.callerNet = net;
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
        this.callerMarking = Objects.requireNonNull(marking);
        this.initialMarking = marking;
        return this;
    }

    /**
     * Sets the initial marking via a builder configurator.
     */
    public SmtVerifier initialMarking(Consumer<MarkingState.Builder> configurator) {
        var builder = MarkingState.builder();
        configurator.accept(builder);
        return initialMarking(builder.build());
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
        this.callerEnvironmentPlaces.addAll(Arrays.asList(places));
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
     * Declares expected sink (terminal) places for deadlock-freedom analysis
     * ([VER-002]): a token resting in one is never stranded, and
     * {@link SmtProperty.TerminatesAtSink} asks whether one of them was reached.
     */
    @SafeVarargs
    public final SmtVerifier sinkPlaces(Place<?>... places) {
        this.sinkPlaces.addAll(Arrays.asList(places));
        return this;
    }

    /**
     * Declares places where a token may rest <b>while {@code marker} holds a token</b>
     * ([VER-014]) — a designed terminal such as a halt or pause marker, under which the
     * work it interrupted legitimately stays where it was delivered.
     *
     * <p>{@link SmtProperty.DeadlockFree} then reads a quiescent marking against the union
     * of the declared sinks, the markers, and every conditional set whose marker is marked:
     * a token in {@code p} is stranded only when none of those excuse it. The marker itself
     * is at rest whenever it is marked, so {@code sinkPlacesWhen(halt)} with no further
     * places excuses exactly the halt token. Repeated calls for one marker accumulate;
     * declarations for several markers union. {@link SmtProperty.TerminatesAtSink} is
     * unaffected and reads only {@link #sinkPlaces}.
     *
     * <pre>{@code
     * SmtVerifier.forNet(net)
     *     .property(SmtProperty.deadlockFree())
     *     .sinkPlaces(done)                       // may always rest
     *     .sinkPlacesWhen(halt, inbox, pending)   // may rest once the run halted
     *     .sinkPlacesWhen(pause, inbox)           // may rest while paused
     * }</pre>
     *
     * <p>An unresolved marker or place contributes nothing, as an unresolved sink does: a
     * mistyped marker makes the property stricter, never laxer.
     */
    @SafeVarargs
    public final SmtVerifier sinkPlacesWhen(Place<?> marker, Place<?>... places) {
        Objects.requireNonNull(marker);
        this.conditionalSinks.computeIfAbsent(marker, _ -> new LinkedHashSet<>())
            .addAll(Arrays.asList(places));
        return this;
    }

    /**
     * What the {@code arrivals(min, max)} rewrite of [VER-006] did.
     *
     * @param min      the mandatory part of the total per environment place
     * @param k        the most per environment place
     * @param places   the environment places, by name, in registration order
     * @param injected the places an injection transition feeds ({@code places}, or none when
     *                 {@code k} is {@code 0})
     */
    private record ArrivalsRewrite(int min, int k, List<String> places, List<String> injected) {}

    /**
     * The {@code arrivals(k)} rewrite ([VER-006]): closes the net over its environment places
     * with the optional arrival group of [VER-022] ({@link OpenNetClosure#closeOpenNet},
     * {@code min = 0}, {@code max = k}) — the {@code i}-th registered place {@code P} gets a
     * source {@code env:optional[i]} holding {@code k} tokens, an injection transition
     * {@code env:arrive?[i]:P} and a decline {@code env:decline[i]} with no output — before any route
     * and before the terminal rewrite, so terminals inhibit the injection transitions as they
     * inhibit every other. Afterwards the verifier has no environment places. {@link #prepare()}
     * runs it on the caller's net and marking, again whenever the mode, the environment places or
     * the marking change.
     *
     * <p>{@code arrivals(min, max)} maps onto the arrival group {@code min..max} instead: the
     * closure adds a mandatory source {@code env:arrivals[i]} holding {@code min} with
     * {@code env:arrive[i]:P}, and omits the optional source when {@code min = max}.
     */
    private void applyArrivals() {
        if (!(environmentMode instanceof EnvironmentAnalysisMode.Arrivals(int min, int k)) || environmentPlaces.isEmpty()) {
            return;
        }
        var byName = new LinkedHashMap<String, Place<?>>();
        for (var ep : environmentPlaces) {
            byName.putIfAbsent(ep.place().name(), ep.place());
        }
        var names = List.copyOf(byName.keySet());
        if (k > 0) {
            var contract = OpenNetContract.builder().initialMarking(initialMarking);
            for (var p : byName.values()) {
                // At most k beyond the min mandatory ones: every other arrival is optional, so a
                // run may rest after any number of them from min to k once the rest are
                // declined — for quiescence as for safety.
                contract.arriveBetween(min, k, p);
            }
            var closed = OpenNetClosure.closeOpenNet(net, contract.build());
            net = closed.net();
            initialMarking = closed.initialMarking();
        }
        arrivals = new ArrivalsRewrite(min, k, names, k > 0 ? names : List.of());
        environmentPlaces.clear();
    }

    /**
     * Why no ν route may decide this net ([VER-006] AC10), or {@code null}: under
     * {@code arrivals(k)} an injection transition producing into a coloured place (a match key
     * or carrier) would be classified as a mint, making two arrivals that may carry one name
     * distinct — which can hide a reachable join, an unsound {@code Proven}.
     */
    private String colouredArrivalReason() {
        if (arrivals == null || arrivals.injected().isEmpty()) {
            return null;
        }
        // Every producer of a coloured place counts as declared here: the question is which
        // places are coloured, not whether the mints are declared.
        var fragment = NameFragment.classify(net, fragmentMode, carrierPlaces, everyTransition(net));
        if (fragment == null) {
            return null;
        }
        for (var p : arrivals.injected()) {
            if (fragment.isColoured(p)) {
                return "environment place '" + p + "' carries ν-names (a match key or carrier place) and is fed "
                    + "by arrivals(k): an injected token's name is unknown, so an arrival is not a fresh mint; "
                    + "refusing to decide it by name (VER-006)";
            }
        }
        return null;
    }

    /**
     * Applies the net's own terminal places ([EXEC-042], [VER-014] "Net-declared terminals"):
     * each terminal place inhibits every transition, is a sink, and excuses every place as a
     * conditional-sink marker. The caller restates nothing.
     *
     * <p>A net without terminals is left untouched — the same instance, the same sink lists —
     * so its scripts stay byte-identical. The encoded net declares no terminals, so a second
     * call is a no-op. When {@link #prepare()} redoes the in-flight split it calls this again on
     * the new split, and each terminal's excused set is rebuilt from the new net's places, so the
     * {@code inflight:} places of an earlier split stop being excused.
     */
    private void applyNetTerminals() {
        if (net.terminals().isEmpty()) {
            return;
        }
        var terminals = List.copyOf(net.terminals());
        var all = NetFlattener.declaredPlaces(net);
        net = TerminalEncoding.inhibited(net);
        for (var p : terminals) {
            sinkPlaces.add(p);
            // The caller's own entries first, then this net's places, in the order a fresh
            // verifier would build, so a redone split scripts as a fresh verifier would.
            var excused = conditionalSinks.computeIfAbsent(p, _ -> new LinkedHashSet<>());
            var previous = terminalExcused.getOrDefault(p, Set.of());
            var rebuilt = new LinkedHashSet<Place<?>>();
            for (var q : excused) {
                if (!previous.contains(q)) {
                    rebuilt.add(q);
                }
            }
            var added = new LinkedHashSet<Place<?>>();
            for (var q : all) {
                if (rebuilt.add(q)) {
                    added.add(q);
                }
            }
            excused.clear();
            excused.addAll(rebuilt);
            terminalExcused.put(p, added);
        }
    }

    /**
     * The rewrites every call starts with ({@link #applyArrivals()}, {@link #applyInertPlaces()},
     * {@link #applyInFlight}, {@link #applyNetTerminals()}). The arrivals closure runs again, and
     * every rewrite after it, when the environment mode, the environment places or the initial
     * marking changed since the last call. The rest are redone from {@link #preSplitNet} whenever an input of the split changed since the
     * last call ({@link #assumeAtomicFiring}, {@link #carrierPlaces}, the environment steps), so a
     * verifier reused after changing one of them does not keep the old split. Otherwise they are
     * idempotent. The lock makes the rewrite safe when several threads share this verifier, and
     * publishes what it wrote.
     */
    private synchronized void prepare() {
        // [VER-006]: the closure depends on the mode, the environment places and the marking. When
        // one changed since the last call, every rewrite is redone from the caller's net.
        var arrivalsKey = new ArrivalsInputs(environmentMode, List.copyOf(callerEnvironmentPlaces), callerMarking);
        if (!arrivalsKey.equals(arrivalsInputs)) {
            if (arrivalsInputs != null) {
                net = callerNet;
                initialMarking = callerMarking;
                environmentPlaces.clear();
                environmentPlaces.addAll(callerEnvironmentPlaces);
                arrivals = null;
                preSplitNet = null;
            }
            arrivalsInputs = arrivalsKey;
            applyArrivals();
        }
        boolean first = preSplitNet == null;
        if (first) {
            preSplitNet = net;
        }
        var conflict = conflictPruningApplies(preSplitNet)
            ? InFlight.conflictDemand(preSplitNet) : InFlight.SplitDemand.NONE;
        var inputs = new InFlightInputs(assumeAtomicFiring, Set.copyOf(carrierPlaces), environmentSteps,
            quiescentCountDemand(preSplitNet), conflict);
        if (!first && inputs.equals(inFlightInputs)) {
            applyInertPlaces();
            return;
        }
        net = preSplitNet;
        inFlightInputs = inputs;
        applyInertPlaces();
        applyInFlight(inputs.terminal(), inputs.conflict());
        applyNetTerminals();
    }

    /** {@link InFlight#quiescentCountDemand} of this verifier's property on {@code net} ([EXEC-042], F1). */
    private InFlight.SplitDemand quiescentCountDemand(PetriNet net) {
        if (!(property instanceof SmtProperty.QuiescentCount(var places, int min, var _, var waivedBy))) {
            return InFlight.SplitDemand.NONE;
        }
        return InFlight.quiescentCountDemand(net,
            places.stream().map(Place::name).toList(), min, waivedBy.stream().map(Place::name).toList());
    }

    /**
     * Whether Route B will read {@link PrioritySemantics#CONFLICT} ([NU-052]): it is selected, the
     * net has a &nu;-join and a property Route B takes (a quiescence one, or any without a declared
     * budget place), and no transition is read as reapable, since Route B turns the pruning off
     * itself on a net with one ({@link NuScgVerifier#verifyReaping}). No other route reads it.
     */
    private boolean conflictPruningApplies(PetriNet net) {
        return prioritySemantics == PrioritySemantics.CONFLICT
            && net.transitions().stream().anyMatch(t -> t.matchSpec() != null)
            && (!isReachabilitySafety(property) || budgetPlaces.isEmpty())
            && reapableSet().isEmpty();
    }

    /**
     * The priority semantics Route B applies: {@link #prioritySemantics}, unless the in-flight split
     * turned conflict priority off for this configuration ([NU-052], [VER-004]).
     */
    private PrioritySemantics effectivePriority() {
        return conflictOff ? PrioritySemantics.NONE : prioritySemantics;
    }

    /**
     * The in-flight split ([VER-004]): every transition whose output some transition tests
     * non-monotonically becomes a start and a completion step ({@link InFlight#split}). A net with
     * no such transition is left untouched, the same instance, so its scripts stay byte-identical.
     * One the split cannot express is recorded, and no route answers. After the inert places and
     * before the terminal rewrite, so a terminal's inhibitor counts as a test and also inhibits
     * each completion step. The transitions the arrivals closure added model the environment and
     * stay atomic. {@link #prepare()} runs it on the unsplit net, again whenever its inputs change.
     *
     * <p>Two readings add to the split ({@link InFlight.SplitDemand}): a {@code QuiescentCount}
     * with a lower bound on a net with a terminal place ({@code terminal}), and conflict priority
     * where Route B applies it ({@code conflict}). When a transition the conflict demand adds
     * cannot be split, conflict priority is turned off for this verification instead
     * ({@link #effectivePriority()}) and the report says why ({@link InFlight#conflictOffNote}).
     */
    private void applyInFlight(InFlight.SplitDemand terminal, InFlight.SplitDemand conflict) {
        inFlightLine = null;
        inFlightRefusal = null;
        inFlightSplit = List.of();
        conflictOff = false;
        var environment = new HashSet<>(environmentSteps);
        if (arrivals != null) {
            var own = new HashSet<String>();
            callerNet.transitions().forEach(t -> own.add(t.name()));
            for (var t : net.transitions()) {
                if (!own.contains(t.name())) {
                    environment.add(t.name());
                }
            }
        }
        var base = InFlight.transitions(net, environment);
        var withTerminal = InFlight.transitions(net, environment, terminal);
        boolean conflictReason = !conflict.forced().isEmpty();
        var demand = terminal.union(conflict);
        if (assumeAtomicFiring) {
            var split = InFlight.transitions(net, environment, demand);
            if (!split.isEmpty()) {
                inFlightLine = InFlight.atomicAssumptionNoteFor(split,
                    new InFlight.SplitReasons(!base.isEmpty(), withTerminal.size() > base.size(), conflictReason));
            }
            return;
        }
        // [NU-052]: the pruning holds only with every pruner and its feeders split. When one of them
        // cannot be, the pruning is off, not the verification.
        String off = null;
        if (conflictReason) {
            var split = InFlight.transitions(net, environment, demand);
            var unsplittable = InFlight.firstUnsplittable(net, carrierPlaces, split);
            if (unsplittable != null) {
                off = InFlight.conflictOffNote(unsplittable.transition(), unsplittable.cause());
                conflictOff = true;
                conflictReason = false;
                demand = terminal;
            }
        }
        var reasons = new InFlight.SplitReasons(!base.isEmpty(), withTerminal.size() > base.size(), conflictReason);
        switch (InFlight.split(net, carrierPlaces, environment, demand)) {
            case InFlight.Outcome.Atomic _ -> inFlightLine = off;
            case InFlight.Outcome.Split(var rewritten, var split) -> {
                net = rewritten;
                inFlightSplit = List.copyOf(split);
                var note = InFlight.splitNoteFor(split, reasons);
                inFlightLine = off == null ? note : off + "\n" + note;
            }
            case InFlight.Outcome.Refused(var reason) -> inFlightRefusal = reason;
        }
    }

    /**
     * Declares every place the initial marking marks and the net does not as an <b>inert</b>
     * place — no arc touches it — so every route sees the token the executors retain
     * ([CORE-072], [VER-001]): {@code deadlockFree} finds it stranded unless a sink excuses it,
     * {@code placeBound} counts it, and it is its own P-invariant. Before, only the state-space
     * routes saw it: the flat encoding dropped it, so a stray token could turn a {@code Violated}
     * into a {@code Proven} depending on the class budget. After the arrivals closure, whose
     * places the net declares, and before the terminal rewrite, so a terminal excuses it as it
     * excuses every place.
     *
     * <p>A marking that names only declared places leaves the net untouched — the same instance
     * — so its scripts stay byte-identical ([VER-013]). Idempotent.
     */
    private void applyInertPlaces() {
        net = withInertMarkedPlaces(net, initialMarking);
    }

    /**
     * {@code net} with each place {@code marking} marks but {@code net} does not declare (by
     * name, reset-only places counting as declared) appended as a place with no arcs, in the
     * marking's listing order after the declared places; {@code net} itself when there is none.
     * The flattener orders places by name, so the listing order reaches no encoding.
     */
    static PetriNet withInertMarkedPlaces(PetriNet net, MarkingState marking) {
        var declared = new HashSet<String>();
        for (var p : NetFlattener.declaredPlaces(net)) {
            declared.add(p.name());
        }
        var inert = new ArrayList<Place<?>>();
        for (var p : marking.placesWithTokens()) {
            if (declared.add(p.name())) {
                inert.add(p);
            }
        }
        if (inert.isEmpty()) {
            return net;
        }
        var places = new ArrayList<Place<?>>(net.places());
        places.addAll(inert);
        var builder = PetriNet.builder(net.name()).places(places.toArray(new Place<?>[0]));
        net.transitions().forEach(builder::transition);
        net.terminals().forEach(builder::terminal);
        return builder.build();
    }

    /** The conditional sink declarations in declaration order ([VER-014]). */
    private List<RestSet.ConditionalSinks> conditionalSinkList() {
        var out = new ArrayList<RestSet.ConditionalSinks>(conditionalSinks.size());
        for (var entry : conditionalSinks.entrySet()) {
            out.add(new RestSet.ConditionalSinks(entry.getKey(), entry.getValue()));
        }
        return List.copyOf(out);
    }

    /**
     * Declares &nu;-net budget places (NU-040): places whose token count bounds
     * the live correlation pool (they gate fresh-name minting). Declaring at
     * least one places the net in the decidable bounded fragment, so
     * reachability-safety properties over its &nu;-joins are verified (the
     * matched transitions are over-approximated). Without any budget place, a
     * net that mints fresh names is treated as unbounded and the verifier
     * returns {@code Unknown} (NU-050).
     *
     * <p>The declaration also states the mint contract of NU-010 for every transition that
     * consumes the place: where such a transition writes a coloured place (a match key,
     * carrier or relay target) without consuming one, its action writes a name it minted with
     * {@code freshName()} in that firing. The &nu; routes read those writes as fresh names.
     * See {@link #mintTransitions(String...)}.
     */
    @SafeVarargs
    public final SmtVerifier budgetPlaces(Place<?>... places) {
        for (var p : places) {
            this.budgetPlaces.add(p.name());
        }
        return this;
    }

    /**
     * Declares transitions that mint (NU-010): where such a transition writes a coloured place
     * (a match key, carrier or relay target) without consuming one, its action writes a name it
     * minted with {@code freshName()} in that firing.
     *
     * <p>The &nu; routes (Route A and Route B of NU-050) read such a write as a fresh name, and
     * they cannot check that an action does so: an action may as well copy a correlation id out
     * of its input, as the built-in {@code fork()} does, and two copies of one id join at run
     * time. So a transition that writes a coloured place without consuming one is read as a mint
     * only when it is declared, here or by consuming a declared {@link #budgetPlaces budget
     * place}. An undeclared one keeps the net off both routes, and the verifier answers through
     * the name-blind over-approximation. What the executor writes on timeout is never a mint,
     * declared or not (IO-013, IO-014).
     *
     * @throws IllegalArgumentException if a name is not a transition of the net, with the reason
     *     {@code declared mint transition 'frok' not in the net (NU-010)} naming every such
     *     name ({@link NameFragment#unknownMintReason})
     */
    public SmtVerifier mintTransitions(String... names) {
        String unknown = NameFragment.unknownMintReason(net, Arrays.asList(names));
        if (unknown != null) {
            throw new IllegalArgumentException(unknown);
        }
        this.mintTransitions.addAll(Arrays.asList(names));
        return this;
    }

    /**
     * The carrier places declared with {@link #carrierPlaces}, by name. Read by the open-net
     * verifier, which splits its closed net with them ([VER-022], [VER-004]).
     */
    public Set<String> configuredCarrierPlaces() {
        return Set.copyOf(carrierPlaces);
    }

    /** The transitions declared with {@link #mintTransitions}, by name ([NU-010]). */
    public Set<String> configuredMintTransitions() {
        return Set.copyOf(mintTransitions);
    }

    /** {@link #mintTransitions(String...)} by transition. */
    public SmtVerifier mintTransitions(Transition... transitions) {
        var names = new String[transitions.length];
        for (int i = 0; i < transitions.length; i++) {
            names[i] = transitions[i].name();
        }
        return mintTransitions(names);
    }

    /**
     * The transitions the &nu; routes may read as mints (NU-010): the declared ones and those
     * consuming a declared budget place.
     */
    private Set<String> declaredMints() {
        return NameFragment.declaredMints(net, budgetPlaces, mintTransitions);
    }

    /** Every transition name of {@code net}. */
    private static Set<String> everyTransition(PetriNet net) {
        var out = new HashSet<String>();
        for (var t : net.transitions()) {
            out.add(t.name());
        }
        return out;
    }

    /**
     * Sets the solver timeout.
     */
    public SmtVerifier timeout(Duration timeout) {
        this.timeout = Objects.requireNonNull(timeout);
        return this;
    }

    /**
     * Sets an optional <b>total</b> wall-clock budget for one {@link #verify()} call ([VER-013];
     * default: none).
     *
     * <p>{@link #timeout(Duration)} is a per-query budget: each solver phase gets its own
     * (the bound query, the state-equation phase and its certificate check, the firing bound
     * (half), the fixpoint query and its certificate check), so the worst case is several times
     * the timeout, plus the solver-free work (enumeration, Route B, the siphon/trap search, the
     * semiflow enumeration, the colour-slot simplex), which no timeout bounds at all. This
     * option bounds the whole call: the deadline starts when {@code verify()} is entered, and
     * the colour-slot simplex runs as its own step, {@code colour-slot bound}, with a
     * checkpoint before every pivot. Every z3 process gets the smaller of
     * its own budget and what is left (its {@code -t}, {@code -T} and watchdog derive from that),
     * no process starts once nothing is left, and the solver-free graph builds and loops poll the
     * deadline and stop when it passes.
     *
     * <p>When it runs out the verdict is {@code Unknown} with the reason
     * {@code total verification budget of <N> ms exhausted during <phase>}, naming the step that
     * was running or about to start, and the report ends with the same line. A verdict reached
     * before the deadline stands. A state-space build it cuts off is not a class-budget
     * truncation: a {@link #stateSpaceCache(StateSpaceCache) cache} entry is left as it was found.
     *
     * <p>Under a total budget the fixpoint query no longer gets its full {@link #timeout} after
     * the firing-bound phase ([VER-019]): it gets what the earlier phases left. Unset, the
     * pipeline is unchanged.
     *
     * @param budget the budget for the whole call, or {@code null} for none
     * @throws IllegalArgumentException if {@code budget} is negative
     */
    public SmtVerifier totalBudget(Duration budget) {
        if (budget != null && budget.isNegative()) {
            throw new IllegalArgumentException("total budget must not be negative: " + budget);
        }
        this.totalBudget = budget;
        return this;
    }

    /**
     * Checks a {@code Violated} counterexample of a timed net against the <b>timed</b> state-class
     * graph ([VER-023]; default: disabled), and reports the outcome in
     * {@link SmtVerificationResult#counterexampleTiming()}.
     *
     * <p>Every route but Route B decides over the untimed abstraction ([VER-004]), so on a timed
     * net a counterexample may be a sequence the clocks forbid — a watchdog that fires after
     * 5 ms against an answer due within 2 ms. When this is on, the verdict is {@code Violated},
     * the net is timed, it has no environment places and the route did not already explore timed
     * behaviour, the verifier builds the timed state-class graph of the same net and initial
     * marking, up to {@link #enumerationMaxClasses(int)} classes and within the
     * {@link #totalBudget(Duration) total budget}, and decides the same property over it with the
     * same predicate the enumeration route uses:
     * <ul>
     *   <li>a violating class is reachable, in the closed graph or in the explored prefix of a
     *       truncated one ([VER-017]) — {@code TIMED_CONFIRMED}, and the counterexample is
     *       replaced with the shortest timed path to it;</li>
     *   <li>the graph closes with none — {@code SPURIOUS_UNDER_TIMING}: the property holds under
     *       timing, a timed claim only;</li>
     *   <li>the graph does not close and its prefix holds none, or the total budget runs out, or
     *       the call is cancelled — {@code TIMED_UNDECIDED}.</li>
     * </ul>
     * The verdict is never changed: the untimed claim is the contract. The timed claim assumes an
     * on-time executor with atomic firings (no transition reaped or fired after its latest bound, no
     * action duration), and the report says so. The timed graph grows
     * with every relative ordering of concurrent clocks, so the check is opt-in; it does not use
     * the {@link #stateSpaceCache(StateSpaceCache) state-space cache}.
     */
    public SmtVerifier timedCounterexampleCheck(boolean enabled) {
        this.timedCounterexampleCheck = enabled;
        return this;
    }

    /**
     * Assumes an <em>on-time executor</em>: no transition is reaped and none fires after its latest
     * bound ([VER-002], [VER-004], [TIME-006], [TIME-013]; default {@code false}).
     *
     * <p>A {@code deadline} / {@code window} transition still enabled past its latest bound plus
     * the executor's tolerance is reaped: disabled, its tokens left in place, and not re-enabled
     * until one of its input places changes. A late executor can therefore come to rest at a
     * marking that still enables it. By default every quiescence property ({@code deadlockFree},
     * {@code terminatesAtSink}, {@code quiescentCount}, {@code joinedOrDeadLettered} and the
     * conditional sinks of [VER-014]) is evaluated at every <em>reap-quiescent</em> marking (one
     * where every enabled transition is reapable) on every route, so a {@code Proven} holds for
     * late executors too. A late executor also fires an {@code exact} transition after its bound,
     * so Route B, the one route that keeps timing, drops the latest bound of every deadline, window
     * and exact transition for every property.
     *
     * <p>{@code true} restores the strict quiescence (no transition enabled) and Route B's
     * strong-semantics graph, and the report of a net with such a transition then says the verdict
     * assumes an on-time executor. Route B also reads each firing as one instant step, so a verdict
     * it reaches this way assumes that an action takes no time as well, and its report says so. A net timed only with {@code immediate} and {@code delayed}
     * verifies identically either way.
     */
    public SmtVerifier assumeNoReaping(boolean assume) {
        this.assumeNoReaping = assume;
        return this;
    }

    /**
     * Assumes <em>atomic firings</em>: no transition tests a place while an action that writes it
     * is in flight ([VER-004], [EXEC-003]; default {@code false}).
     *
     * <p>The executor consumes a firing's inputs when its action starts and deposits its outputs
     * when the action completes; an asynchronous action leaves that gap open while it runs, and a
     * synchronous one until the end of its firing pass. By default every transition whose output
     * some transition tests with an inhibitor, reset or draining input ({@code all},
     * {@code atLeast}), or that marks a terminal place, is verified in two steps: a start that
     * consumes and marks {@code inflight:<name>}, and an immediate {@code complete:<name>} that
     * deposits ({@link InFlight}). A net with no such transition verifies identically either way.
     *
     * <p>Two readings split more. A {@code quiescentCount} with a lower bound, on a net with a
     * terminal place that does not waive it, also splits every transition depositing into a place
     * it counts or a waiver place: the terminal stop abandons an action in flight, and its
     * deposit never lands ([EXEC-042]). {@link PrioritySemantics#CONFLICT} on Route B also splits
     * every pruning transition and every transition depositing into its input or read places
     * ([NU-052]), and turns itself off, with a report line, when one of them cannot be split.
     *
     * <p>{@code true} reads every firing as one step again, and the report of a net with such a
     * transition then says the verdict rests on that assumption.
     *
     * <p>A counterexample of the split net may start a transition again while an earlier firing of
     * it is in flight. The Rust executor does that; the Java and TypeScript executors never do, so
     * on them such a counterexample may be a false alarm, and the report says so ([CONC-002]).
     */
    public SmtVerifier assumeAtomicFiring(boolean assume) {
        this.assumeAtomicFiring = assume;
        return this;
    }

    /**
     * Takes what the open-net route knows about the closed net it hands this verifier ([VER-022]):
     * the transitions that model the environment, which the in-flight split leaves atomic
     * ([VER-004]), and the reapable transitions of the timed net whose untimed copy this verifier
     * reads ([TIME-013]). Only {@link org.libpetri.smt.opennet} can make a {@link ClosedNetSteps},
     * so no other caller can exempt a transition from the split or replace the reapable set.
     *
     * @param steps the closed net's environment steps and reapable transitions
     */
    public SmtVerifier closedNetSteps(ClosedNetSteps steps) {
        Objects.requireNonNull(steps, "steps");
        this.environmentSteps = steps.environment();
        this.reapableOverride = steps.reapable();
        return this;
    }

    /** The reapable transitions the caller's net has, whether or not they are read so. */
    private Set<String> reapableInNet() {
        return reapableOverride != null ? reapableOverride : Reaping.reapableTransitions(callerNet);
    }

    /**
     * The transitions whose latest bound a late executor overruns ([TIME-006], [TIME-013]): every
     * deadline, window and exact transition, none under {@link #assumeNoReaping}. Route B drops
     * their latest bound ({@link Reaping#relaxLate}).
     */
    private Set<String> lateSet() {
        return assumeNoReaping ? Set.of() : Reaping.lateTransitions(net);
    }

    /** The transitions whose enabledness does not keep a marking from resting: none under {@link #assumeNoReaping}. */
    private Set<String> reapableSet() {
        return assumeNoReaping ? Set.of() : reapableInNet();
    }

    /** The flat net every encoder reads, its reapable transitions marked. */
    private FlatNet flatNet() {
        var reapable = reapableSet();
        return NetFlattener.flatten(net, environmentPlaces, environmentMode, t -> reapable.contains(t.name()));
    }

    /**
     * The report line on reaping ([TIME-013]) for a net with a reapable transition: the reap-aware
     * reading of a quiescence property, or the on-time executor a verdict reached under
     * {@link #assumeNoReaping} rests on. On a ν-net Route B also reads the latest bounds
     * ([TIME-006]), so there an exact transition alone makes the assumption line appear.
     * {@code null} when the net has no such transition or lateness cannot bear on the verdict (a
     * marking property off Route B). {@code routeB} picks the assumption line of a verdict Route B
     * reached, which also assumes that an action takes no time ({@link Reaping#noReapingRouteBNote}).
     */
    private String reapingLine(boolean routeB) {
        var inNet = reapableInNet();
        boolean hasMatch = net.transitions().stream().anyMatch(t -> t.matchSpec() != null);
        var lateInNet = new java.util.LinkedHashSet<>(inNet);
        if (hasMatch) {
            lateInNet.addAll(Reaping.lateTransitions(net));
        }
        if (lateInNet.isEmpty()) {
            return null;
        }
        if (isReachabilitySafety(property) && !hasMatch) {
            return null;
        }
        if (assumeNoReaping && routeB) {
            return Reaping.noReapingRouteBNote(lateInNet);
        }
        if (assumeNoReaping) {
            return Reaping.noReapingAssumptionNote(lateInNet);
        }
        // Route B's own note says which latest bounds it lifted.
        return inNet.isEmpty() ? null : Reaping.reapAwareNote(inNet);
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
     *
     * <p>The pruning holds only while no pruning transition, and no transition depositing into
     * the input or read places of one, has an action in flight. The verifier splits them
     * ([VER-004], {@link InFlight#conflictDemand}), and a pruner in flight pre-empts nothing.
     * When one of them cannot be split (a &nu;-join, a writer into a coloured place), conflict
     * priority is off for the verification and the report says why.
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
        return semiflowInvariants(enabled ? SemiflowMode.ON : SemiflowMode.OFF);
    }

    /**
     * How the [VER-007] semiflow union is decided.
     *
     * <p>{@link #AUTO} exists because the enumeration is worst-case exponential and the two
     * useful cases are told apart by a fact the pipeline already has — whether the
     * null-space basis lost a law to the H1 guard.
     */
    public enum SemiflowMode {
        /** Never compute or union the semiflows (the default). */
        OFF,
        /** Always compute them and union the gate-validated ones into the encoders' list. */
        ON,
        /** Union exactly when the basis lost a law to the H1 guard; skip the cost otherwise. */
        AUTO
    }

    /**
     * {@link #semiflowInvariants(boolean)} with the {@link SemiflowMode#AUTO} setting also
     * available ([VER-007]).
     *
     * <p>{@code AUTO} decides whether the semiflows would add <b>information to the
     * encoding</b>, which is not the same question as whether they would appear in
     * {@link SmtVerificationResult#invariants()} for a caller who reads them.
     *
     * <p>A complete basis spans every conservation law of the net, so a semiflow it spans
     * constrains nothing further and IC3 gains nothing from it — that is why {@code AUTO}
     * skips the enumeration there. But the basis is the <em>signed</em> null-space, and a law
     * it spans need not appear in it in <b>non-negative</b> form; only the Farkas enumeration
     * produces that. A caller inspecting the invariant list for a law of a given shape — "a
     * non-negative law weighting the budget place and every running place positively" — can
     * therefore find nothing on a net that plainly has one. Such a caller should ask for the
     * union explicitly with {@link SemiflowMode#ON}: {@code AUTO} is the setting to prefer for
     * verification, not for harvesting.
     */
    public SmtVerifier semiflowInvariants(SemiflowMode mode) {
        this.semiflowInvariants = Objects.requireNonNull(mode);
        return this;
    }

    /**
     * Sets the class budget for the bounded state-space enumeration route ([VER-017];
     * default 50 000). {@code 0} disables the route, so every query goes to the SMT
     * pipeline.
     *
     * <p>When the state-class graph closes within the budget the property is decided
     * exactly — sound and complete — and no solver runs. This is what makes a long pipeline
     * tractable: IC3 needs a frame per stage and its cost climbs with the cube of the
     * length, while enumeration is linear in the reachable state space. A forty-node chain
     * (370 places, 1 967 classes) takes 410 s on the fixpoint path and 0.11 s here.
     *
     * <p>The route declines when the graph exceeds the budget, and the SMT pipeline then
     * runs unchanged — it can only add verdicts, never remove them. It is skipped for
     * &nu;-nets, which have their own exact route (NU-050, Route B), for nets with
     * environment places, whose injection the graph does not model, and for <b>timed</b>
     * nets, where its verdict would be the weaker timed claim rather than the untimed one
     * the encoders make ([VER-004]).
     */
    public SmtVerifier enumerationMaxClasses(int max) {
        this.enumerationMaxClasses = max;
        return this;
    }

    /**
     * Shares a state-space cache with other verifications ([VER-017] "Reusing the state space
     * across queries"; default: none).
     *
     * <p>The state-class graph of the enumeration route depends only on the net and its
     * initial marking, so every query on the same net and marking that passes the same
     * {@code cache} reads one graph instead of building its own. A remembered truncation
     * works the same way: a later query whose budget is no larger declines at once instead
     * of paying the full attempt again. Entries are keyed by this verifier's net, by
     * identity, and the initial marking; see {@link StateSpaceCache} for the budget rules
     * and the thread-safety guarantees.
     *
     * <p>The verdict, the witness and the route are the same with and without a cache; the
     * report adds one line when a cached graph or a cached truncation was used. Without a
     * cache the behaviour is unchanged.
     *
     * @param cache the cache to read and fill, owned by the caller; {@code null} for none
     */
    public SmtVerifier stateSpaceCache(StateSpaceCache cache) {
        this.stateSpaceCache = cache;
        return this;
    }

    /**
     * Enables or disables the linear state-equation bound phase ([VER-015]; default:
     * enabled). A reachability-safety property whose violating markings exceed some
     * {@code y·M <= y·M0} with {@code y >= 0}, {@code y·C <= 0} is then proven
     * structurally, from one linear query re-checked in exact integer arithmetic, before
     * any fixpoint search. Disable it to force the IC3/PDR path — for its certificate, or
     * to exercise the fixpoint engine itself.
     */
    public SmtVerifier linearBound(boolean enabled) {
        this.linearBound = enabled;
        return this;
    }

    /**
     * Encodes the <b>state equation</b> with firing counters ([VER-016]; default:
     * disabled — the encoding then carries places only).
     *
     * <p>The flat encoding gains one counter {@code n_t} per flat transition and every
     * transition rule conjoins the marking equation {@code M' = M0 + C·n'} for each place
     * whose column is exact (no consume-all / reset arc, not injected). Every linear
     * consequence of the marking equation — the equality laws of [VER-005]/[VER-007]
     * <b>and</b> the inequality laws {@code y·M <= y·M0} ({@code y >= 0, y·C <= 0}) and
     * their mixed-sign kin, which are what an <em>ordering</em> argument ("both join slots
     * armed means every upstream stage has run, so nothing can still halt") looks like in
     * linear arithmetic — is then available to Spacer as a fact rather than a lemma it has
     * to invent. On a 50-place agent-dispatch workflow, proper completion under
     * conditional sinks went from {@code Unknown} after 120 s to {@code Proven} in 1.5 s
     * with this as the only change; a 53-place pipeline stage before a join,
     * {@code Unknown} at 300 s, proves in under a second.
     *
     * <p>The cost is a larger state (places + transitions) and a slower witness search on
     * genuinely violated properties (about 1.5× on the nets above), so it is opt-in.
     * Soundness is unchanged: the counters are exact bookkeeping, the equation holds on
     * every reachable state by construction ({@code Strengthening.lean}, the same shape as
     * the equality laws), and the certificate check re-proves it against the raw step
     * relation, whose only counter knowledge is the increment. Not applied to the
     * name-coloured encoding or Route B, which the report says when it applies.
     *
     * <p>Not {@link #stateEquationPhase(boolean)}, which is the separate [VER-018] pre-phase
     * that can decide the property outright instead of the fixpoint query, and is on by
     * default.
     */
    public SmtVerifier stateEquation(boolean enabled) {
        this.stateEquation = enabled;
        return this;
    }

    /**
     * Enables or disables the state-equation phase ([VER-018]; default: enabled).
     *
     * <p>Before the fixpoint query, one linear query asks whether a marking the marking
     * equation admits can violate the property: {@code M = M0 + C·n} over firing counts
     * {@code n >= 0}, with an upper bound on a place a consume-all or reset arc clears.
     * {@code unsat} proves the property. A {@code sat} candidate is settled cheapest first: a
     * real run within its firing counts that reaches a violation (violated, with that run as
     * the counterexample); an initially marked trap it leaves empty; or a linear inequality
     * {@code a·M <= b}, kept by every step of the exact step relation, guards and clearing
     * included, that excludes it. The refinement is added and the query asked again.
     *
     * <p>The proof is {@code SE ∧ refinements}, re-proven by the certificate check against the
     * raw step relation before it is reported, and the report prints each refinement — on a
     * workflow join, {@code Merge/hasdata <= Merge/ready_0 + Merge/ready_1}: a data token never
     * outlives its input's ready token, because the skip is inhibited by it. On compiled
     * workflow nets of 30–370 places this takes tens of milliseconds where the fixpoint query
     * took minutes.
     *
     * <p>When nothing settles a candidate, the phase steps aside and the pipeline continues
     * unchanged. Flat path only: skipped for a &nu;-net and under {@code Ignore} with
     * environment places. Disable it to force the fixpoint path.
     *
     * <p>Runs within the full {@link #timeout}, and its certificate check gets its own, as on
     * the fixpoint path. Not {@link #stateEquation(boolean)}, which adds firing counters
     * <em>inside</em> the fixpoint encoding and is off by default.
     */
    public SmtVerifier stateEquationPhase(boolean enabled) {
        this.stateEquationPhase = enabled;
        return this;
    }

    /**
     * Enables or disables the firing-bound phase ([VER-019]; default: enabled).
     *
     * <p>When weights {@code r >= 0} exist that every firing lowers by at least one, no run
     * has more than {@code K = r·M0} firings, and a bounded model check of {@code K} exact
     * steps decides the property: a violating run is the counterexample, and none at depth
     * {@code K} is a proof for every run. The depth doubles from 8, so a short counterexample
     * is found early — the case the fixpoint query handles worst, a quiescence violation deep
     * in a workflow net. A net without such weights is reported as unbounded, naming the
     * transitions the marking equation lets repeat, and left to the fixpoint query.
     *
     * <p>A proof from this phase carries no inductive invariant for the certificate check; the
     * ranking is re-checked in exact integer arithmetic and the counterexample is replayed.
     * Runs after the state-equation phase, on the same nets, within half the timeout. Disable
     * it to force the fixpoint path. [VER-019] requires both phases to default the same way in
     * every implementation, because a verdict they reach carries a different method and report
     * from the same verdict reached by the fixpoint query.
     */
    public SmtVerifier firingBound(boolean enabled) {
        this.firingBound = enabled;
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
     * <h3>Cancellation ([VER-013])</h3>
     * Interrupting the thread that runs this method cancels it — Java's own cancellation idiom;
     * there is no token. The running {@code z3} process is destroyed at once and reaped, no
     * further process starts, the state-space builds and long solver-free loops stop at their
     * next deadline poll, and the result is {@code Unknown} with the reason
     * {@code verification cancelled during <phase>} (the report ends with the same line). A
     * thread already interrupted when the call starts gets that result at once, for the phase
     * {@code net preparation}. The polls read the interrupt status without clearing it, so the
     * flag is still set when this method returns. A verdict reached before the interrupt stands.
     * A build stopped this way is not a class-budget truncation: a
     * {@link #stateSpaceCache(StateSpaceCache) state-space cache} is left as it was found.
     *
     * @return the verification result
     * @throws IllegalStateException per [CORE-043] — this encoder reads token production from
     *     the {@code Arc.Out} spec, never from the bound action, so a net that could not produce
     *     at run time would otherwise verify green
     */
    public SmtVerificationResult verify() {
        var report = new StringBuilder();
        var entered = Instant.now();
        // [VER-013] a deadline is bound for every call: the total budget when one is set, which
        // starts here, before the terminal rewrite, so all of the call's work counts against it;
        // otherwise an unlimited one that stops only on cancellation (an interrupt of this
        // thread). Bound for the call only, on this thread.
        var bound = totalBudget == null
            ? VerificationDeadline.unlimited()
            : new VerificationDeadline(saturatingMillis(totalBudget));
        var running = new RunningRoute();
        try {
            // A call cancelled before it starts returns at once.
            if (VerificationDeadline.cancelled()) {
                throw new VerificationDeadline.Cancelled(bound);
            }
            return ScopedValue.where(VerificationDeadline.carrier(), bound)
                .where(RUNNING_ROUTE, running)
                .call(() -> finish(withCounterexampleTiming(pipeline(report), report)));
        } catch (VerificationDeadline.Stopped e) {
            String reason = e.reason();
            report.append("\n=== RESULT ===\n\n");
            report.append("UNKNOWN: ").append(reason).append("\n");
            String why = e instanceof VerificationDeadline.Cancelled
                ? "n/a (verification cancelled)" : "n/a (total verification budget exhausted)";
            return buildResult(
                new SmtVerificationResult.Verdict.Unknown(reason), report.toString(),
                List.of(), List.of(), List.of(), List.of(),
                Duration.between(entered, Instant.now()),
                new SmtVerificationResult.SmtStatistics(
                    net.places().size(), net.transitions().size(), 0, why),
                running.route);
        }
    }

    /**
     * The report lines that depend on the result: Route B's assumption line in place of the
     * generic one under {@link #assumeNoReaping} ([TIME-013], [VER-004]), and at the end the
     * restart note of a counterexample that starts a transition while an earlier firing of it is
     * in flight ([CONC-002], {@link InFlight#restartNote}).
     */
    private SmtVerificationResult finish(SmtVerificationResult result) {
        var report = result.report();
        if (result.route() == SmtVerificationResult.Route.NU_SCG) {
            var plain = reapingLine(false);
            var routeB = reapingLine(true);
            int at = plain == null ? -1 : report.indexOf(plain);
            if (at >= 0 && !plain.equals(routeB)) {
                report = report.substring(0, at) + routeB + report.substring(at + plain.length());
            }
        }
        if (result.verdict() instanceof SmtVerificationResult.Verdict.Violated) {
            var note = InFlight.restartNote(result.counterexampleTrace(), result.counterexampleTransitions());
            if (note != null) {
                report = report + (report.endsWith("\n") ? "" : "\n") + note + "\n";
            }
        }
        if (report.equals(result.report())) {
            return result;
        }
        return new SmtVerificationResult(result.verdict(), result.route(), report, result.invariants(),
            result.discoveredInvariants(), result.counterexampleTrace(), result.counterexampleTransitions(),
            result.counterexampleConfirmed(), result.counterexampleTiming(), result.elapsed(), result.statistics());
    }

    /** {@code d} in milliseconds, saturating where a {@link Duration} holds more than a long does. */
    private static long saturatingMillis(Duration d) {
        try {
            return d.toMillis();
        } catch (ArithmeticException _) {
            return d.isNegative() ? 0 : Long.MAX_VALUE;
        }
    }

    /**
     * Names the step about to run for a total-budget exhaustion or a cancellation ([VER-013]) and
     * refuses to start it once the call must stop. A no-op outside {@link #verify()}.
     */
    private static void enter(String phase, SmtVerificationResult.Route route) {
        var deadline = VerificationDeadline.current();
        if (deadline != null) {
            deadline.enter(phase);
            if (RUNNING_ROUTE.isBound()) {
                RUNNING_ROUTE.get().route = route;
            }
        }
    }

    /** The pipeline of {@link #verify()}, writing its report into {@code report}. */
    private SmtVerificationResult pipeline(StringBuilder report) {
        OutputActionCheck.requireOutputProducingActions(net);
        prepare();
        var start = Instant.now();
        report.append("=== IC3/PDR SAFETY VERIFICATION ===\n\n");
        report.append("Net: ").append(net.name()).append("\n");
        String propDesc = propertyDescription();
        report.append("Property: ").append(propDesc).append("\n");
        var bound = VerificationDeadline.current();
        if (bound != null && bound.limited()) {
            report.append("Total budget: ").append(bound.budgetMs()).append(" ms\n");
        }
        report.append("Timeout: ").append(timeout.toSeconds()).append("s\n\n");
        if (arrivals != null) {
            if (arrivals.injected().isEmpty()) {
                report.append("Environment: arrivals(0) — nothing is injected; the environment places are "
                    + "ordinary places (VER-006)\n\n");
            } else {
                // One entry per non-empty source, as closeOpenNet adds them: mandatory, then optional.
                int min = arrivals.min();
                int max = arrivals.k();
                var closures = new ArrayList<String>();
                for (int i = 0; i < arrivals.injected().size(); i++) {
                    var p = arrivals.injected().get(i);
                    if (min > 0) {
                        closures.add("env:arrive[" + i + "]:" + p + " from env:arrivals[" + i + "] (exactly " + min + ")");
                    }
                    if (max > min) {
                        closures.add("env:arrive?[" + i + "]:" + p + " from env:optional[" + i + "] (at most "
                            + (max - min) + ")");
                    }
                }
                report.append("Environment: arrivals(").append(min > 0 ? min + ".." + max : String.valueOf(max))
                    .append(") — net closed before any route: ")
                    .append(String.join(", ", closures)).append(" (VER-006)\n\n");
            }
        }
        // [TIME-013]: how the verdict reads reaping, on a net that has a reapable transition.
        // The line of a verdict off Route B; finish() swaps in Route B's when it decided.
        var reaping = reapingLine(false);
        if (reaping != null) {
            report.append(reaping).append("\n\n");
        }
        // [VER-004]: the transitions verified in two steps, or the assumption that none need it.
        if (inFlightLine != null) {
            report.append(inFlightLine).append("\n\n");
        }
        // [CORE-037]: a read, inhibitor or reset arc on a place nothing can mark acts on
        // nothing. A warning only — never a verdict.
        var envPlaces = new HashSet<Place<?>>();
        environmentPlaces.forEach(ep -> envPlaces.add(ep.place()));
        var arrivalPlaces = arrivals == null ? Set.<String>of() : Set.copyOf(arrivals.places());
        Predicate<Place<?>> isEnvironment = p -> envPlaces.contains(p) || arrivalPlaces.contains(p.name());
        // The caller's net, not the terminal rewrite: its synthetic inhibitors are not the
        // caller's arcs.
        var deadArcs = ArcDiagnostics.deadArcs(callerNet.transitions(), isEnvironment, initialMarking::hasTokens);
        for (var dead : deadArcs) {
            report.append("WARNING: ").append(dead.message()).append("\n");
        }
        if (!deadArcs.isEmpty()) {
            report.append("\n");
        }
        List<RestSet.ConditionalSinks> conditional = conditionalSinkList();

        // Before ANY route. A property naming a place the net does not declare is not a
        // question about the net: every route answers it vacuously and each in its own way
        // — the flat encoder would emit a `false` violation term that proves anything, the
        // linear bound would drop the conjunct and separate a strictly stronger demand, the
        // enumeration route would find no class marking a place that cannot be marked. All
        // three then report PROVEN. The flat encoding's own refusal (Phase 4) sits below
        // the ν route, the linear bound and the enumeration route, all of which return
        // first, so it guards only the path that never needed it. Refusing once, here, is
        // the only placement the refusal cannot be routed around.
        // [VER-013]: a call already out of budget (or cancelled) before it starts says so, ahead
        // of any refusal; the phase is still "net preparation".
        VerificationDeadline.checkpoint();
        String absentPlace = unresolvedPropertyPlace(net, property);
        if (absentPlace != null) {
            String reason = "property names a place that does not resolve in the net ('"
                + absentPlace + "'); refusing to certify (the encoding would be vacuously proven)";
            report.append("=== RESULT ===\n\n");
            report.append("UNKNOWN: ").append(reason).append("\n");
            return buildResult(
                new SmtVerificationResult.Verdict.Unknown(reason),
                report.toString(), List.of(), List.of(), List.of(), List.of(),
                Duration.between(start, Instant.now()),
                new SmtVerificationResult.SmtStatistics(
                    net.places().size(), net.transitions().size(), 0,
                    "n/a (unresolved property place)"),
                SmtVerificationResult.Route.UNAVAILABLE);
        }

        // [VER-006] AC3: every route below models a bounded(k) environment place as a source
        // holding at most k, which is the executor only within the premises. Outside them a
        // PROVEN can miss a firing and a VIOLATED can report a rest the executor never
        // reaches, so no route answers.
        String outsidePremises = boundedPremiseViolation(net, initialMarking, environmentPlaces, environmentMode);
        if (outsidePremises != null) {
            report.append("=== RESULT ===\n\n");
            report.append("UNKNOWN: ").append(outsidePremises).append("\n");
            return buildResult(
                new SmtVerificationResult.Verdict.Unknown(outsidePremises),
                report.toString(), List.of(), List.of(), List.of(), List.of(),
                Duration.between(start, Instant.now()),
                new SmtVerificationResult.SmtStatistics(
                    net.places().size(), net.transitions().size(), 0,
                    "n/a (bounded(k) premises)"),
                SmtVerificationResult.Route.UNAVAILABLE);
        }

        // [VER-004]: every route fires a transition atomically. A net whose in-flight actions
        // matter and that the split cannot express gets no answer from any of them.
        if (inFlightRefusal != null) {
            report.append("=== RESULT ===\n\n");
            report.append("UNKNOWN: ").append(inFlightRefusal).append("\n");
            return buildResult(
                new SmtVerificationResult.Verdict.Unknown(inFlightRefusal),
                report.toString(), List.of(), List.of(), List.of(), List.of(),
                Duration.between(start, Instant.now()),
                new SmtVerificationResult.SmtStatistics(
                    net.places().size(), net.transitions().size(), 0,
                    "n/a (in-flight actions)"),
                SmtVerificationResult.Route.UNAVAILABLE);
        }

        // ν-net awareness (NU-040, NU-050). A transition with a match spec joins
        // by name equality; the untimed encoder over-approximates that (name
        // equality assumed satisfiable). The over-approximation is sound for
        // reachability-safety bounds (Proven holds — the real net fires strictly
        // fewer joins) but NOT for quiescence-based properties, which name-blind
        // firing distorts. The applyNuGuard step turns those cases into Unknown.
        boolean hasMatch = net.transitions().stream().anyMatch(t -> t.matchSpec() != null);
        boolean nuBounded = !budgetPlaces.isEmpty();
        // [NU-010]: a transition that writes a coloured place without consuming one and is not
        // declared to mint keeps the net off both ν routes. Name it where a route declines or the
        // ν guard answers Unknown.
        String undeclaredPointer = null;
        if (hasMatch) {
            var undeclared = NameFragment.undeclaredMints(net, fragmentMode, carrierPlaces, declaredMints());
            if (!undeclared.isEmpty()) {
                undeclaredPointer = NameFragment.undeclaredMintsPointer(undeclared);
            }
        }

        // NU-054: BASE reads a join's coloured output as a re-mint whatever it declares, so a
        // relay declaration changes nothing there. Say so, and name the mode that uses it.
        if (hasMatch && fragmentMode == FragmentMode.BASE) {
            var ignored = relayDeclarations(net);
            if (!ignored.isEmpty()) {
                report.append("NOTE: ν relay declarations ignored under BASE fragment mode (NU-054): ")
                      .append(String.join(", ", ignored))
                      .append("; select fragmentMode(EXTENDED) to analyse the joins as relays.\n\n");
            }
        }

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
            enter("Route B (ν name-partition graph)", SmtVerificationResult.Route.NU_SCG);
            // [VER-006] AC8: under modelled injection the graph holds an environment place as
            // an inexhaustible input with a frozen count and no injected names, so a verdict
            // that observes either is vacuous. Decline before building it, and do not defer to
            // Route A: it declines under injection too, and the reason would be lost.
            var mints = declaredMints();
            var fragment = NuScgVerifier.supportedFragment(
                net, initialMarking, fragmentMode, carrierPlaces, mints);
            boolean quiescenceVacuous = !isReachabilitySafety(property)
                && SmtEncoder.quiescenceUnreachable(
                    flatNet());
            // An arrival into a coloured place declines whether or not the mints are declared.
            String colouredArrival = NuScgVerifier.supportedFragment(
                net, initialMarking, fragmentMode, carrierPlaces, everyTransition(net)) == null
                ? null : colouredArrivalReason();
            String envObservation = colouredArrival != null ? colouredArrival : fragment == null ? null : routeBEnvObservation(
                net, fragment, property, sinkPlaces, conditional, environmentPlaces, environmentMode,
                effectivePriority(), quiescenceVacuous);
            if (envObservation != null) {
                report.append("=== ν-net Route B: name-aware state-class graph (NU-050) ===\n");
                report.append("  Declined under environment injection: ").append(envObservation).append("\n");
                return buildResult(
                    new SmtVerificationResult.Verdict.Unknown(envObservation), report.toString(),
                    List.of(), List.of(), List.of(), List.of(),
                    Duration.between(start, Instant.now()),
                    new SmtVerificationResult.SmtStatistics(
                        net.places().size(), net.transitions().size(), 0, "n/a (ν name-partition SCG)"),
                    SmtVerificationResult.Route.NU_SCG);
            }
            var outcome = NuScgVerifier.verifyReaping(
                net, initialMarking, property, sinkPlaces, environmentPlaces, environmentMode, nuMaxClasses,
                fragmentMode, carrierPlaces, mints, effectivePriority(), conditional, reapableSet(), lateSet());
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
                // NU-010, NU-051: the actions whose writes the verdict trusts.
                if (fragment != null) {
                    report.append(NameFragment.contractNote(fragment.mints(), fragment.relays()));
                }
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
                        && ignoresEnvironment()) {
                    report.append("  Downgraded to UNKNOWN: ")
                          .append(IGNORE_MODE_VACUITY_REASON).append("\n");
                    routeBVerdict = new SmtVerificationResult.Verdict.Unknown(
                        IGNORE_MODE_VACUITY_REASON);
                }
                if (quiescenceVacuous) {
                    report.append("  ").append(QUIESCENCE_VACUITY_NOTE).append("\n");
                }
                return buildResult(
                    routeBVerdict, report.toString(), List.of(), List.of(),
                    outcome.trace(), outcome.transitions(),
                    Duration.between(start, Instant.now()),
                    new SmtVerificationResult.SmtStatistics(
                        net.places().size(), net.transitions().size(), 0, "n/a (ν name-partition SCG)"),
                    SmtVerificationResult.Route.NU_SCG);
            } else if (deferToRouteA) {
                report.append("ν-net Route B inconclusive (name-partition truncated); deferring to "
                    + "Route A coloured IC3/PDR (NU-053).\n");
            }
            // EXTENDED was requested but the net falls outside the coloured-consumer
            // fragment (classify returned null). Surface a short note instead of a
            // silent fall-back, then continue on the sound over-approximation path.
            if (undeclaredPointer != null && !deferToRouteA) {
                report.append("ν-net Route B declined: ").append(undeclaredPointer).append(".\n\n");
            } else if (fragmentMode == FragmentMode.EXTENDED && !deferToRouteA) {
                report.append("ν-net Route B (EXTENDED) declined: net outside coloured-consumer "
                    + "fragment (a coloured place consumed count != 1 or by multiple inputs, carries a "
                    + "reset/read/inhibitor arc, or a join writes a coloured place it does not declare "
                    + "as a relay target); verified via sound over-approximation instead.\n\n");
            }
        }

        // Bounded state-space enumeration ([VER-017]): when the state-class graph closes
        // within the budget it decides the property exactly, with no solver at all — the
        // answer for the narrow, deep state spaces a workflow net produces, where IC3 needs
        // a frame per pipeline stage. Skipped for ν-nets (Route B above is their exact
        // route) and for nets with environment places, whose injection the graph does not
        // model; on truncation the SMT pipeline below runs unchanged.
        if (!hasMatch
                && environmentPlaces.isEmpty()
                && enumerationMaxClasses > 0
                && ScgVerifier.isUntimed(net)) {
            enter("state-space enumeration", SmtVerificationResult.Route.ENUMERATION);
            ScgVerifier.Outcome enumerated;
            // Under arrivals(k) the graph is of the closed net, which depends on the environment
            // places as well as on the caller's net and marking: it would share a cache entry
            // with a query that closed the net over other places, so the cache is not used.
            boolean cached = stateSpaceCache != null && (arrivals == null || arrivals.injected().isEmpty());
            if (!cached) {
                if (stateSpaceCache != null) {
                    report.append("Bounded state-space enumeration: state-space cache not used — the net was "
                        + "closed by arrivals(k) (VER-006, VER-017).\n");
                }
                enumerated = ScgVerifier.verify(
                    net, initialMarking, property, sinkPlaces, enumerationMaxClasses, conditional);
            } else {
                // Keyed by the caller's net and the in-flight split ([VER-004]): the inert-place,
                // split and terminal rewrites are a new instance per verification, but a
                // deterministic function of the net they rewrote and the transitions split. A key
                // without the split would let a graph of the atomic net, built under
                // assumeAtomicFiring, answer a query that runs on the split net.
                var encoded = net;
                var lookup = stateSpaceCache.lookup(callerNet, inFlightSplit, initialMarking,
                    enumerationMaxClasses, budget -> StateClassGraph.build(encoded, initialMarking, budget));
                // A lookup answered as truncated still reads the graph it has — the truncated
                // build, or a cached one at least as large — as an explored prefix: a violation
                // in it stands, nothing is proven from it ([VER-017]).
                enumerated = ScgVerifier.decide(lookup.graph(), property, sinkPlaces, conditional, !lookup.closed());
                if (enumerated instanceof ScgVerifier.Outcome.Truncated) {
                    enumerated = new ScgVerifier.Outcome.Truncated(lookup.classCount());
                }
                if (lookup.fromCache()) {
                    report.append(lookup.closed()
                        ? "Bounded state-space enumeration: reused cached state space ("
                            + lookup.classCount() + " classes) (VER-017).\n"
                        : enumerated instanceof ScgVerifier.Outcome.Decided
                            ? "Bounded state-space enumeration: cached truncation at " + enumerationMaxClasses
                                + " classes (VER-017); its explored prefix (" + lookup.graph().size()
                                + " classes) was read.\n"
                            : "Bounded state-space enumeration: cached truncation at "
                                + enumerationMaxClasses
                                + " classes (VER-017); verifying via the SMT pipeline.\n");
                }
            }
            if (enumerated instanceof ScgVerifier.Outcome.Decided decided) {
                report.append("=== Bounded state-space enumeration (VER-017) ===\n");
                report.append("  State classes: ").append(decided.classCount()).append("\n");
                report.append("  P-invariants: not computed (no encoding is built on this route)\n");
                report.append(decided.truncated()
                    ? GraphDecision.prefixNote("state-class graph", enumerationMaxClasses)
                    : ScgVerifier.NOTE_ENUMERATED);
                if (!decided.transitions().isEmpty()) {
                    report.append("  Counterexample trace: ").append(decided.trace().size())
                          .append(" states, ").append(decided.transitions().size())
                          .append(" transitions\n");
                }
                return buildResult(
                    decided.verdict(), report.toString(), List.of(), List.of(),
                    decided.trace(), decided.transitions(),
                    // The graph path IS a firing sequence, so a violation is ordered and
                    // confirmed by construction; there is nothing left to replay.
                    decided.verdict() instanceof SmtVerificationResult.Verdict.Violated
                        ? Boolean.TRUE : null,
                    Duration.between(start, Instant.now()),
                    new SmtVerificationResult.SmtStatistics(
                        net.places().size(), net.transitions().size(), 0,
                        "n/a (state-space enumeration)"),
                    SmtVerificationResult.Route.ENUMERATION);
            }
            report.append("Bounded state-space enumeration truncated at ")
                  .append(enumerationMaxClasses)
                  .append(" classes (VER-017); verifying via the SMT pipeline.\n");
        }

        // [IO-014]: a timeout forward of an All / AtLeast input deposits the whole drained
        // batch, a marking-dependent count. Route B and the enumeration above resolve it from
        // the marking each firing drains, exactly as the executor does
        // (BranchOutcomes.Deposit.Drained), so they decide such a net. Every route below reads
        // the flat net, whose post vectors are constants — the structural pre-check, the
        // P-invariants, the linear bound, the VER-018 / VER-019 phases, the CHC fixpoint query
        // and Route A — so a Proven from any of them would be about a different net. Refuse
        // here, after the graph routes and before the first linear one: every exit below this
        // point is then covered ([VER-003] AC5).
        var drained = org.libpetri.analysis.BranchOutcomes.drainedForward(net);
        if (drained.isPresent()) {
            String reason = drained.get().reason();
            report.append("=== RESULT ===\n\n");
            report.append("UNKNOWN: ").append(reason).append("\n");
            return buildResult(
                new SmtVerificationResult.Verdict.Unknown(reason),
                report.toString(), List.of(), List.of(), List.of(), List.of(),
                Duration.between(start, Instant.now()),
                new SmtVerificationResult.SmtStatistics(
                    net.places().size(), net.transitions().size(), 0,
                    "n/a (drained forward)"),
                SmtVerificationResult.Route.UNAVAILABLE);
        }

        // Phase 1: Flatten
        enter("flattening", SmtVerificationResult.Route.SMT);
        report.append("Phase 1: Flattening net...\n");
        FlatNet flatNet = flatNet();
        report.append("  Places: ").append(flatNet.placeCount()).append("\n");
        report.append("  Transitions (expanded): ").append(flatNet.transitionCount()).append("\n");
        if (!flatNet.environmentBounds().isEmpty()) {
            report.append("  Environment bounds: ").append(flatNet.environmentBounds().size()).append(" places\n");
        }
        report.append("\n");

        // Phase 2: Structural pre-check
        report.append("Phase 2: Structural pre-check (siphon/trap)...\n");
        // The structural check only proves DeadlockFree, and only when no sink places
        // (conditional or not) are declared: it does not account for sinks. Environment
        // places rule it out too: the siphon/trap analysis runs on the closed net and is
        // blind to env injection (VER-006), so fall through to the (injection-aware) SMT
        // encoding instead. Nets Commoner's theorem does not govern are excluded as well,
        // see {@link #commonerApplies}. The siphon search is exponential, so it runs only
        // when its result can decide the verdict.
        // Commoner's theorem rules out dead markings only: a net with a reapable transition can
        // also rest where one is still enabled ([VER-002], [TIME-013]), so the encoders, which
        // read that, decide it.
        boolean structuralCandidate = property instanceof SmtProperty.DeadlockFree
                && !hasMatch
                && flatNet.transitions().stream().noneMatch(FlatTransition::reapable)
                && commonerApplies(flatNet)
                && sinkPlaces.isEmpty()
                && conditional.isEmpty()
                && environmentPlaces.isEmpty();
        enter("structural pre-check", SmtVerificationResult.Route.SMT);
        var structResult = structuralCandidate ? StructuralCheck.check(flatNet, initialMarking) : null;
        String structResultStr = switch (structResult) {
            case null -> "n/a (not a deadlock-freedom proof candidate)";
            case StructuralCheck.Result.NoPotentialDeadlock() -> "no potential deadlock";
            case StructuralCheck.Result.PotentialDeadlock(var siphon) -> "potential deadlock (siphon: " + siphon + ")";
            case StructuralCheck.Result.Inconclusive(var reason) -> "inconclusive (" + reason + ")";
        };
        report.append("  Result: ").append(structResultStr).append("\n\n");

        if (structuralCandidate && structResult instanceof StructuralCheck.Result.NoPotentialDeadlock) {
            report.append("=== RESULT ===\n\n");
            report.append("PROVEN (structural): Deadlock-freedom verified by Commoner's theorem.\n");
            report.append("  All siphons contain initially marked traps.\n");
            report.append("  Certificate check: not applicable (structural proof)\n");
            return buildResult(
                new SmtVerificationResult.Verdict.Proven("structural", null),
                report.toString(), List.of(), List.of(), List.of(), List.of(),
                Duration.between(start, Instant.now()),
                new SmtVerificationResult.SmtStatistics(
                    flatNet.placeCount(), flatNet.transitionCount(), 0, structResultStr),
                SmtVerificationResult.Route.STRUCTURAL
            );
        }

        // Phase 3: P-invariants
        enter("P-invariant computation", SmtVerificationResult.Route.SMT);
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
        // P-semiflows (non-negative conservation laws), validated by the same exact gate
        // before the union may conjoin them.
        //
        // Computed ONLY when the union will read them ([VER-007] AC2). Nothing else does: the
        // colour-slot bound of the name-coloured encoder ([NU-053]) is a linear program over
        // the incidence matrix (SlotBoundLp), not a semiflow search. The Farkas enumeration is
        // worst-case exponential: the minimal semiflows of `k` independent diamonds in series
        // number 2^k, measured at 2 048 for eleven and past the backstop beyond thirteen. So
        // running it for a caller who did not ask for it is a large cost, and on a wide net
        // an uncatchable one: the heap it exhausts kills the process rather than returning a
        // verdict.
        // Skipping it is invisible to every other phase.
        //
        // AUTO ([VER-007]): compute them exactly when the basis LOST a law to the H1 guard,
        // which is the condition the option exists for — a consume-all / reset arc on a busy
        // place drops every basis row whose support touches it, and the semiflows are the
        // minimal laws that avoid it. On a net with a complete basis they add nothing and
        // cost the enumeration, so AUTO skips them there. The drops are already known at
        // this point, so this decides in ONE pass rather than running the pipeline twice to
        // read its own report.
        boolean basisLostALaw = invariantValidation.dropped().stream()
            .anyMatch(r -> r.contains("Strengthening.lean H1"));
        boolean unionWanted = semiflowInvariants == SemiflowMode.ON
            || (semiflowInvariants == SemiflowMode.AUTO && basisLostALaw);
        var semiflowValidation = unionWanted
            ? PInvariantComputer.validateExact(
                PInvariantComputer.computePSemiflows(matrix, flatNet, initialMarking),
                matrix, flatNet, initialMarking)
            : new PInvariantComputer.Validation(List.of(), List.of());
        var semiflows = semiflowValidation.valid();
        report.append("  Found: ").append(invariants.size()).append(" P-invariant(s)\n");
        if (semiflowInvariants == SemiflowMode.AUTO) {
            report.append(basisLostALaw
                ? "  Semiflow union: ON (auto — the basis lost a law to the H1 guard)\n"
                : "  Semiflow union: off (auto — the basis is complete, so the semiflows would "
                    + "add no constraint the encoding does not already have; they may still "
                    + "differ in FORM)\n");
        }
        if (unionWanted) {
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

        // A quiescence property on a net that can never come to rest is vacuously true:
        // the verdict would be Proven whatever the net does ([VER-006] AC6). Say so, or the
        // caller reads an empty claim as a guarantee about their workflow.
        if (!isReachabilitySafety(property) && SmtEncoder.quiescenceUnreachable(flatNet)) {
            report.append("  ").append(QUIESCENCE_VACUITY_NOTE).append("\n");
        }

        // Phase 4: SMT encode + query via Spacer
        report.append("Phase 4: IC3/PDR verification via Z3 Spacer...\n");

        var stats = new SmtVerificationResult.SmtStatistics(
            flatNet.placeCount(), flatNet.transitionCount(), invariants.size(), structResultStr);

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
            report.append("UNKNOWN: Could not determine ").append(propDesc).append("\n");
            report.append("  Reason: ").append(reason).append("\n");
            return buildResult(
                new SmtVerificationResult.Verdict.Unknown(reason),
                report.toString(), invariants, List.of(), List.of(), List.of(),
                Duration.between(start, Instant.now()), stats,
                SmtVerificationResult.Route.UNAVAILABLE);
        }
        report.append("  Solver: z3 ").append(z3.version()).append("\n");

        if (hasMatch && nuBounded && !flatNet.environmentInjection().isEmpty()) {
            report.append("  ν-encoding: name-blind over-approximation (the name-coloured encoding does not\n")
                .append("  model environment injection, VER-006)\n");
        }
        String colouredArrival = hasMatch && nuBounded ? colouredArrivalReason() : null;
        if (colouredArrival != null) {
            report.append("  ν-encoding: name-blind over-approximation (").append(colouredArrival).append(")\n");
        }

        // Linear state-equation bound (VER-015): a reachability-safety property whose
        // violating markings exceed some `y·M <= y·M0` with `y >= 0`, `y·C <= 0` is
        // proven structurally, without the fixpoint search — the ordering arguments IC3
        // does not invent on pipeline-shaped nets. It runs before the name-coloured encoding
        // too ([NU-053]): the flat state equation is name-blind and over-approximates the ν
        // semantics, so its Proven is sound on a ν-net, and a trivially true bound no longer
        // waits out the coloured query's timeout. Not proven → the coloured encoding decides
        // as before. Skipped under Ignore with environment places, where VER-006 refuses
        // every Proven.
        if (linearBound
                && isReachabilitySafety(property)
                && !ignoresEnvironment()) {
            enter("linear bound", SmtVerificationResult.Route.SMT);
            String proof = linearBoundProof(flatNet, z3, report);
            if (proof != null) {
                report.append("  Certificate check: not applicable (structural proof)\n\n");
                report.append("=== RESULT ===\n\n");
                report.append("PROVEN (structural): ").append(propDesc).append("\n");
                report.append("  Linear state-equation bound: y >= 0 with y.C <= 0 gives y.M <= y.M0 on every\n");
                report.append("  reachable marking, and the violating markings exceed it (VER-015).\n");
                report.append("  ").append(proof).append("\n");
                return applyNuGuard(buildResult(
                    new SmtVerificationResult.Verdict.Proven("structural", null),
                    report.toString(), invariants, List.of(), List.of(), List.of(),
                    Duration.between(start, Instant.now()), stats,
                    SmtVerificationResult.Route.STRUCTURAL), hasMatch, nuBounded, false, undeclaredPointer);
            }
        }

        // State-equation phase ([VER-018]), then the firing bound ([VER-019]): flat path only.
        // Not on a ν-net, whose matched transitions the flat encoding treats name-blind and
        // which has exact routes of its own, and not under Ignore with environment places,
        // where [VER-006] refuses every Proven. Neither phase returns through applyNuGuard,
        // which is safe only because this requires !hasMatch, where that guard is the identity.
        boolean flatPhases = !hasMatch && !ignoresEnvironment();
        if (flatPhases && stateEquationPhase) {
            enter("state-equation phase", SmtVerificationResult.Route.SMT);
            var decided = stateEquationDecision(flatNet, z3, report, propDesc, conditional, invariants, stats, start);
            if (decided != null) {
                return decided;
            }
        }
        if (flatPhases && firingBound) {
            enter("firing-bound phase", SmtVerificationResult.Route.SMT);
            var decided = firingBoundDecision(flatNet, z3, report, propDesc, conditional, invariants, stats, start);
            if (decided != null) {
                return decided;
            }
        }

        // ν-net exact refinement (NU-050 #1, Route A). For a budget-bounded ν-net in
        // the supported mint→matched-join fragment, encode names as a finite colour
        // set (k = the colour-slot bound: the floor of a linear program's optimum, re-checked
        // exactly, which bounds the coloured tokens and so the live names) with exact
        // same-colour join matching, instead of the name-blind over-approximation. This
        // rules out spurious counterexamples that would equate two distinct names.
        // Reachability-safety AND quiescence (NU-053) properties are both routed here; a net
        // outside the fragment keeps the flat encoding.
        //
        // Built only after the linear bound, which never needs it: a structural Proven skips
        // the plan and its slot-bound simplex. Nothing above reads the plan.
        var colouredAttempt = colouredAttempt(flatNet, invariants, coloured -> {
            // The simplex is a solver-free loop under [VER-013]: its own step, and a checkpoint
            // before every pivot. A stop already due ends the query here, charged to the step
            // before.
            enter("colour-slot bound", SmtVerificationResult.Route.SMT);
            return SlotBoundLp.solve(flatNet, initialMarking, coloured);
        }, slot -> {
            String line = slot.reportLine();
            if (line != null) {
                report.append(line).append("\n");
            }
        });
        NameColouredEncoder.ColouredPlan colouredPlan = colouredAttempt.plan();

        SmtEncoder.SmtEncoding encoding;
        if (colouredPlan != null) {
            report.append("  ν-encoding: name-coloured (colour-slot bound k=")
                .append(colouredPlan.k()).append("; ")
                .append(colouredPlan.colouredCount()).append(" coloured place(s))\n");
            report.append(NameFragment.contractNote(colouredPlan.mints(), colouredPlan.relays()));
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
                        invariants.size(), structResultStr),
                    SmtVerificationResult.Route.UNAVAILABLE);
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
                        invariants.size(), structResultStr),
                    SmtVerificationResult.Route.UNAVAILABLE);
            }
            // C3: request the refutation proof the replay decoder reads.
            encoding = SmtEncoder.encode(
                flatNet, initialMarking, property, invariants, sinkPlaces, counterexampleReplay,
                conditional, stateEquation);
            if (stateEquation) {
                report.append("  State equation: encoded over ").append(encoding.counterCount())
                    .append(" firing counters (VER-016)\n");
            }
        }
        if (stateEquation && colouredPlan != null) {
            report.append("  State equation: not applied (name-coloured encoding)\n");
        }
        String phase = colouredPlan != null ? "horn-coloured" : "horn";
        enter("IC3/PDR query", SmtVerificationResult.Route.SMT);
        var queryResult = SpacerRunner.run(z3, timeout, encoding.smt2(), phase);

        var smtResult = switch (queryResult) {
            case SpacerRunner.QueryResult.Proven(var formula) -> {
                // Guard against silent vacuous proofs (VER-006): in Ignore mode the
                // encoding does not model env injection, so env-gated transitions never
                // fire and ANY safety bound is trivially "proven". Refuse to certify —
                // downgrade to UNKNOWN with actionable guidance.
                if (ignoresEnvironment()) {
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
                        enter("certificate check", SmtVerificationResult.Route.SMT);
                        try {
                            certOutcome = certificateChecker.run(
                                formula, flatNet, initialMarking, property, sinkPlaces,
                                invariants, z3, timeout, conditional, stateEquation);
                        } catch (RuntimeException e) {
                            // A checker that throws must not fail the pipeline — but a
                            // DEFECT there is not a verification outcome: laundering it
                            // into "certificate unavailable" would make the bug a
                            // permanently plausible weaker answer (see ProgrammingError).
                            ProgrammingError.rethrowIfProgrammingError(e);
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
                report.append("PROVEN (IC3/PDR): ").append(propDesc).append("\n");
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
                var decoded = CounterexampleDecoder.decode(answer, flatNet, encoding.counterCount());
                if (decoded.note() != null) {
                    report.append("  Counterexample decoding: ").append(decoded.note()).append("\n");
                }
                List<MarkingState> decodedList = List.copyOf(decoded.states());

                // The initial marking itself violates: the counterexample is the empty firing
                // sequence, whatever the proof text holds. Spacer's refutation for it has no
                // ground Reachable step to decode, and a Violated with no trace cannot be
                // replayed by anyone, so it is reported as [] from M0, confirmed by evaluating
                // Bad(M0) — the check the replay would make first — with or without the replay
                // enabled. Flat count encoding only.
                if (colouredPlan == null && AbstractReplayer.violates(
                        flatNet, property, sinkPlaces, conditional,
                        AbstractReplayer.toVector(flatNet, initialMarking))) {
                    report.append("  Counterexample: the initial marking violates the property ")
                          .append("(empty firing sequence)\n\n");
                    report.append("=== RESULT ===\n\n");
                    report.append("VIOLATED: ").append(propDesc).append("\n");
                    appendUntimedCaveat(report);
                    yield buildResult(
                        new SmtVerificationResult.Verdict.Violated(),
                        report.toString(), invariants, List.of(),
                        List.of(AbstractReplayer.toMarking(flatNet,
                            AbstractReplayer.toVector(flatNet, initialMarking))),
                        List.of(), Boolean.TRUE,
                        Duration.between(start, Instant.now()), stats);
                }

                if (!counterexampleReplay) {
                    report.append("  Counterexample replay: disabled (counterexampleReplay(false))\n\n");
                    report.append("=== RESULT ===\n\n");
                    report.append("VIOLATED: ").append(propDesc).append("\n");
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
                    flatNet, initialMarking, decoded, property, sinkPlaces, conditional,
                    replayStateSetOverride, replayNodeBudget);
                yield switch (assessment) {
                    case ReplayAssessment.Confirmed(var trace, var firings) -> {
                        report.append("  Counterexample replay: CONFIRMED — the decoded states chain ")
                              .append("into an abstract run reaching the violation.\n\n");
                        report.append("=== RESULT ===\n\n");
                        report.append("VIOLATED: ").append(propDesc).append("\n");
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
                        report.append("VIOLATED: ").append(propDesc).append("\n");
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
                report.append("UNKNOWN: Could not determine ").append(propDesc).append("\n");
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
        return applyNuGuard(smtResult, hasMatch, nuBounded, colouredPlan != null, undeclaredPointer);
    }

    /**
     * Sets {@link SmtVerificationResult#counterexampleTiming()} on a {@code Violated} result, and
     * runs the timed counterexample check of [VER-023] when it is enabled and applies. Applied
     * once, to whatever the pipeline returned, like the &nu; guard; never changes a verdict.
     */
    private SmtVerificationResult withCounterexampleTiming(SmtVerificationResult result, StringBuilder report) {
        if (!(result.verdict() instanceof SmtVerificationResult.Verdict.Violated)) {
            return result;
        }
        boolean hasMatch = net.transitions().stream().anyMatch(t -> t.matchSpec() != null);
        SmtVerificationResult.CounterexampleTiming timing;
        if (ScgVerifier.isUntimed(net)) {
            timing = SmtVerificationResult.CounterexampleTiming.UNTIMED_NET;
        } else if (result.route() == SmtVerificationResult.Route.NU_SCG) {
            timing = SmtVerificationResult.CounterexampleTiming.TIMED_EXACT;
        } else if (!timedCounterexampleCheck || !environmentPlaces.isEmpty() || hasMatch) {
            // Environment injection and ν name correlation are outside what the plain timed
            // graph models, so the check does not apply there.
            timing = SmtVerificationResult.CounterexampleTiming.UNTIMED_ABSTRACTION;
        } else {
            return timedCheck(result);
        }
        return withTiming(result, timing, result.report(),
            result.counterexampleTrace(), result.counterexampleTransitions());
    }

    /**
     * The timed counterexample check ([VER-023]): the timed state-class graph of the same net
     * (terminal rewrite included) and initial marking, under the enumeration class budget and
     * the total budget, decided with the enumeration route's predicate.
     */
    private SmtVerificationResult timedCheck(SmtVerificationResult result) {
        var report = new StringBuilder(result.report());
        report.append("\n=== Timed counterexample check (VER-023) ===\n");
        StateClassGraph graph;
        try {
            VerificationDeadline.checkpoint();
            graph = StateClassGraph.build(net, initialMarking, Math.max(0, enumerationMaxClasses),
                Set.of(), EnvironmentAnalysisMode.ignore(), StateClassGraph.Options.TIMED);
        } catch (VerificationDeadline.Stopped e) {
            // The verdict was reached before the stop and stands; only the check is undecided.
            if (e instanceof VerificationDeadline.Cancelled) {
                report.append("  UNDECIDED: verification was cancelled before the timed state-class graph closed.\n");
            } else {
                report.append("  UNDECIDED: the total verification budget of ").append(e.deadline().budgetMs())
                    .append(" ms ran out before the timed state-class graph closed.\n");
            }
            return withTiming(result, SmtVerificationResult.CounterexampleTiming.TIMED_UNDECIDED,
                report.toString(), result.counterexampleTrace(), result.counterexampleTransitions());
        }
        // A truncated graph is read as its explored prefix ([VER-017]): a violating class in it
        // confirms the counterexample; SPURIOUS_UNDER_TIMING needs a closed graph.
        // [TIME-013]: a class also rests where every enabled transition is reapable. The graph
        // fires every transition on time, so it does not hold the runs a late executor takes
        // after a reap: SPURIOUS_UNDER_TIMING means no on-time run reaches a violating rest.
        var outcome = ScgVerifier.decide(graph, property, sinkPlaces, conditionalSinkList(), false, reapableSet());
        if (!(outcome instanceof ScgVerifier.Outcome.Decided decided)) {
            report.append("  UNDECIDED: the timed state-class graph exceeded ")
                .append(enumerationMaxClasses).append(" classes (enumerationMaxClasses).\n");
            return withTiming(result, SmtVerificationResult.CounterexampleTiming.TIMED_UNDECIDED,
                report.toString(), result.counterexampleTrace(), result.counterexampleTransitions());
        }
        report.append("  Timed state classes: ").append(decided.classCount()).append("\n");
        if (decided.verdict() instanceof SmtVerificationResult.Verdict.Violated) {
            report.append(decided.truncated()
                ? "  CONFIRMED: the timed state-class graph, truncated at " + enumerationMaxClasses
                    + " classes (enumerationMaxClasses), reaches a violating class in its explored prefix.\n"
                : "  CONFIRMED: the timed state-class graph reaches a violating class.\n");
            report.append("  The counterexample trace and firing sequence of this result are REPLACED by the ")
                .append("shortest timed-graph path:\n");
            var trace = decided.trace();
            report.append("  Counterexample trace (timed, ").append(trace.size()).append(" states):\n");
            for (int i = 0; i < trace.size(); i++) {
                report.append("    ").append(i).append(": ").append(trace.get(i)).append("\n");
            }
            if (!decided.transitions().isEmpty()) {
                report.append("  Firing sequence: ").append(String.join(" -> ", decided.transitions())).append("\n");
            }
            // The path is an ordered firing sequence, confirmed by construction ([VER-023], as
            // for the enumeration route).
            return withTiming(result, SmtVerificationResult.CounterexampleTiming.TIMED_CONFIRMED,
                report.toString(), decided.trace(), decided.transitions(), Boolean.TRUE);
        }
        report.append("  SPURIOUS UNDER TIMING: the timed state-class graph closed with ")
            .append(decided.classCount()).append(" classes and none of them violates the property, so it ")
            .append("holds under the net's timing — a timed claim only.\n");
        report.append("  The verdict stays VIOLATED: the untimed semantics is the contract (VER-004). The ")
            .append("untimed counterexample above is kept.\n");
        report.append(TIMED_CHECK_ASSUMPTION);
        return withTiming(result, SmtVerificationResult.CounterexampleTiming.SPURIOUS_UNDER_TIMING,
            report.toString(), result.counterexampleTrace(), result.counterexampleTransitions());
    }

    /**
     * What a {@code SPURIOUS_UNDER_TIMING} of [VER-023] assumes. The timed graph fires every transition
     * by its latest bound and each firing takes no time, so its claim covers neither an executor that
     * runs late (and reaps or fires late, [TIME-006], [TIME-013]) nor actions whose duration lets
     * other firings interleave.
     */
    private static final String TIMED_CHECK_ASSUMPTION = "  The timed claim assumes an on-time executor with "
        + "atomic firings: no transition is reaped or fires after its latest bound, and an action takes no "
        + "time. A late executor or a long action can still reach the untimed counterexample.\n";

    private static SmtVerificationResult withTiming(
            SmtVerificationResult r, SmtVerificationResult.CounterexampleTiming timing, String report,
            List<MarkingState> trace, List<String> transitions) {
        return withTiming(r, timing, report, trace, transitions, r.counterexampleConfirmed());
    }

    private static SmtVerificationResult withTiming(
            SmtVerificationResult r, SmtVerificationResult.CounterexampleTiming timing, String report,
            List<MarkingState> trace, List<String> transitions, Boolean confirmed) {
        return new SmtVerificationResult(r.verdict(), r.route(), report, r.invariants(),
            r.discoveredInvariants(), trace, transitions, confirmed, timing,
            r.elapsed(), r.statistics());
    }

    /**
     * Runs the linear state-equation bound query ([VER-015]) and re-checks its answer in
     * exact integer arithmetic. Returns the bound as the report prints it when one
     * separates the violation, {@code null} otherwise (no bound, solver inconclusive, or
     * a model that failed the re-check — each named in the report). Never the last word:
     * {@code null} hands over to the fixpoint query.
     */
    private String linearBoundProof(FlatNet flatNet, Z3Solver z3, StringBuilder report) {
        String script = LinearBound.encode(flatNet, initialMarking, property);
        if (script == null) {
            return null;
        }
        Z3Process.Reply reply;
        try {
            reply = z3.run(script, "bound", timeout, List.of());
        } catch (Z3Process.Z3ProcessException e) {
            report.append("  Linear state-equation bound: inconclusive (").append(e.getMessage()).append(")\n");
            return null;
        }
        String stdout = reply.stdout().strip();
        String verdict = SmtText.classifyFirstLine(stdout);
        if (verdict == null) {
            report.append("  Linear state-equation bound: inconclusive (")
                .append(Z3Process.failureReason(reply, Z3Solver.timeoutMs(timeout))).append(")\n");
            return null;
        }
        switch (verdict) {
            case "sat" -> {
                var y = LinearBound.decode(stdout, flatNet.placeCount());
                var bound = y == null ? null : LinearBound.checkExact(flatNet, initialMarking, property, y);
                if (bound == null) {
                    report.append("  Linear state-equation bound: inconclusive (solver model failed the exact re-check)\n");
                    return null;
                }
                String rendered = LinearBound.formatBound(flatNet, bound) + "; violation needs "
                    + LinearBound.formatDemand(flatNet, property, bound);
                report.append("  Linear state-equation bound: ").append(rendered).append("\n");
                report.append("  Status: bound excludes every violating marking (re-checked in exact integer arithmetic)\n");
                return rendered;
            }
            case "unsat" -> {
                report.append("  Linear state-equation bound: none separates the violation\n");
                return null;
            }
            default -> {
                report.append("  Linear state-equation bound: inconclusive (Z3 answered unknown)\n");
                return null;
            }
        }
    }

    /**
     * Whether the net has environment places the analysis is not modelling ([VER-006]
     * {@code Ignore}). Every route that can return {@code Proven} has to refuse one here — a
     * proof over a frozen environment is vacuous — so the rule is named once rather than
     * spelled out at each guard. See {@link #IGNORE_MODE_VACUITY_REASON}.
     */
    private boolean ignoresEnvironment() {
        return !environmentPlaces.isEmpty() && environmentMode instanceof EnvironmentAnalysisMode.Ignore;
    }

    /** The timeout in milliseconds, saturating where a {@link Duration} holds more than a long does. */
    private long timeoutMillis() {
        try {
            return timeout.toMillis();
        } catch (ArithmeticException _) {
            return Long.MAX_VALUE;
        }
    }

    /**
     * One script through the transport as the phases of [VER-018] and [VER-019] ask it,
     * returning stdout. Throws when the reply has no verdict line, and when z3 reported an
     * error other than the {@code model is not available} a {@code (get-model)} after
     * {@code unsat} always draws — an errored assert silently drops out of the query, so the
     * verdict line alone would answer a different question.
     */
    private static String runPhaseScript(Z3Solver z3, String script, String phase, long timeoutMs)
            throws Z3Process.Z3ProcessException, PhaseSolverException {
        Duration budget = Duration.ofMillis(timeoutMs);
        var reply = z3.run(script, phase, budget, List.of());
        String unexpected = (reply.stdout() + "\n" + reply.stderr()).lines()
            .map(SmtText::errorLine)
            .filter(line -> line != null && !line.contains("model is not available"))
            .findFirst()
            .orElse(null);
        if (unexpected != null) {
            throw new PhaseSolverException("z3 reported an error: " + unexpected);
        }
        if (SmtText.classifyFirstLine(reply.stdout()) == null) {
            throw new PhaseSolverException(Z3Process.failureReason(reply, Z3Solver.timeoutMs(budget)));
        }
        return reply.stdout();
    }

    /** A phase query whose reply cannot be read; the message is the phase's inconclusive reason. */
    private static final class PhaseSolverException extends Exception {
        PhaseSolverException(String message) {
            super(message);
        }
    }

    /**
     * Runs the state-equation phase ([VER-018]). Returns the final result when it decided the
     * property — a {@code Proven} only once the certificate check passed — and {@code null}
     * when it stepped aside, with the reason in the report.
     */
    private SmtVerificationResult stateEquationDecision(
            FlatNet flatNet, Z3Solver z3, StringBuilder report, String propDesc,
            List<RestSet.ConditionalSinks> conditional, List<PInvariant> invariants,
            SmtVerificationResult.SmtStatistics stats, Instant start
    ) {
        report.append("  State-equation phase (VER-018):\n");
        var outcome = StateEquationPhase.runStateEquationPhase(
            flatNet, initialMarking, property, sinkPlaces, conditional,
            (script, phase, ms) -> runPhaseScript(z3, script, phase.label(), ms),
            StateEquationPhase.Options.DEFAULT.withBudgetMs(timeoutMillis()));
        for (var r : outcome.refinements()) {
            report.append("    Refinement (").append(r.origin().label()).append("): ")
                .append(StateEquationQuery.formatInequality(flatNet, r)).append("\n");
        }
        report.append("    Queries: ").append(outcome.queries()).append("\n");
        switch (outcome) {
            case StateEquationPhase.StateEquationOutcome.Inconclusive inconclusive -> {
                report.append("    Status: inconclusive (").append(inconclusive.reason()).append(")\n");
                if (inconclusive.candidate() != null) {
                    report.append("    Unsettled candidate: ")
                        .append(StateEquationPhase.describeCandidate(flatNet, inconclusive.candidate()))
                        .append("\n");
                }
                return null;
            }
            case StateEquationPhase.StateEquationOutcome.Violated violated -> {
                report.append("    Status: a run within the candidate's firing counts reaches a violation\n");
                return witnessResult(flatNet, violated.states(), violated.steps(), report, propDesc,
                    invariants, stats, start);
            }
            case StateEquationPhase.StateEquationOutcome.Proven proven -> {
                report.append("    Status: no marking the equation admits violates the property\n");
                var refinements = proven.refinements();
                String certificate = StateEquationQuery.refinementCertificate(
                    flatNet.placeCount(), flatNet.transitionCount(), refinements);
                if (certificateCheck) {
                    // No P-invariants and the counter-augmented step relation forced: the
                    // refinement certificate has to stand on its own, and its arity is places +
                    // transitions, so the VCs need the relation that carries the counters. The
                    // seam is the fixpoint path's, so a test can drive this check's failure too.
                    CertificateChecker.Result checked;
                    try {
                        checked = certificateChecker.run(
                            certificate, flatNet, initialMarking, property, sinkPlaces, List.of(),
                            z3, timeout, conditional, true);
                    } catch (RuntimeException e) {
                        ProgrammingError.rethrowIfProgrammingError(e);
                        checked = new CertificateChecker.Result.Unavailable("certificate check threw: " + e);
                    }
                    String reason = certificateDowngradeReason(checked);
                    if (reason != null) {
                        // Never a verdict: the fixpoint query still runs, and the failure stays
                        // in the report where a test over the fixtures can see it.
                        report.append("    Certificate check: FAILED (").append(reason).append(")\n");
                        return null;
                    }
                    // Two spaces, not four: this line is pinned verbatim by [VER-018] AC1 and
                    // matches the fixpoint path. The FAILED line above is nested under the phase.
                    report.append("  Certificate check: PASSED (init, consecution, safety)\n");
                } else {
                    report.append("  Certificate check: not applicable (disabled)\n");
                }
                report.append("\n");
                report.append("=== RESULT ===\n\n");
                report.append("PROVEN (state equation): ").append(propDesc).append("\n");
                report.append("  Every reachable marking satisfies the marking equation over ")
                    .append(flatNet.transitionCount()).append(" firing counters")
                    .append(refinements.isEmpty() ? "" : " and the refinements above")
                    .append(", and none of those markings violates the property (VER-018).\n");
                report.append("  NOTE: Verification ignores timing constraints.\n");
                var readable = new ArrayList<String>(refinements.size());
                for (var r : refinements) {
                    readable.add(StateEquationQuery.formatInequality(flatNet, r));
                }
                return buildResult(
                    new SmtVerificationResult.Verdict.Proven("state-equation", certificate),
                    report.toString(), invariants, List.copyOf(readable), List.of(), List.of(),
                    Duration.between(start, Instant.now()), stats);
            }
        }
    }

    /**
     * Runs the firing-bound phase ([VER-019]). Returns the final result when it decided the
     * property and {@code null} when it stepped aside, with the reason in the report.
     */
    private SmtVerificationResult firingBoundDecision(
            FlatNet flatNet, Z3Solver z3, StringBuilder report, String propDesc,
            List<RestSet.ConditionalSinks> conditional, List<PInvariant> invariants,
            SmtVerificationResult.SmtStatistics stats, Instant start
    ) {
        report.append("  Firing bound (VER-019):\n");
        // Half the timeout: a short counterexample is found in seconds, while a proof to a deep
        // bound on a wide net can outlast any budget, and the fixpoint query after this phase
        // still gets its full one — unless a total budget ([VER-013]) is set, when it gets what
        // is left. The phase itself refuses a net with DECLARED environment
        // injection, whether or not the flat net resolves the place.
        var outcome = BoundedRun.runFiringBoundPhase(
            flatNet, initialMarking, property, sinkPlaces, conditional,
            (script, phase, ms) -> runPhaseScript(z3, script, phase.label(), ms),
            BoundedRun.Options.DEFAULT.withBudgetMs(Math.max(1, Math.floorDiv(timeoutMillis(), 2))));
        switch (outcome) {
            case BoundedRun.FiringBoundOutcome.Unbounded unbounded -> {
                if (unbounded.repeatable() == null) {
                    report.append("    Status: no firing bound (no weights decrease on every firing); not attempted\n");
                } else {
                    var names = new ArrayList<String>();
                    for (int t : unbounded.repeatable()) {
                        names.add(flatNet.transitions().get(t).name());
                    }
                    report.append("    Status: no firing bound — the marking equation lets ")
                        .append(String.join(", ", names)).append(" repeat; not attempted\n");
                }
                return null;
            }
            case BoundedRun.FiringBoundOutcome.Inconclusive inconclusive -> {
                if (inconclusive.bound() != null) {
                    appendFiringBound(report, flatNet, inconclusive.bound());
                }
                if (!inconclusive.depths().isEmpty()) {
                    report.append("    Depths: ").append(formatDepths(inconclusive.depths())).append("\n");
                }
                report.append("    Status: inconclusive (").append(inconclusive.reason()).append(")\n");
                return null;
            }
            case BoundedRun.FiringBoundOutcome.Violated violated -> {
                appendFiringBound(report, flatNet, violated.bound());
                report.append("    Depths: ").append(formatDepths(violated.depths())).append("\n");
                report.append("    Status: a bounded run reaches a violation (replayed)\n");
                return witnessResult(flatNet, violated.states(), violated.steps(), report, propDesc,
                    invariants, stats, start);
            }
            case BoundedRun.FiringBoundOutcome.Proven proven -> {
                appendFiringBound(report, flatNet, proven.bound());
                report.append("    Depths: ").append(formatDepths(proven.depths())).append("\n");
                report.append("    Status: no run of at most the bound reaches a violation, and no run is longer\n");
                report.append("  Certificate check: not applicable (bounded model check to the firing bound)\n");
                report.append("\n");
                report.append("=== RESULT ===\n\n");
                report.append("PROVEN (bounded model check): ").append(propDesc).append("\n");
                report.append("  No run has more than ").append(proven.bound().bound())
                    .append(" firings, and none of at most that many reaches a violation (VER-019).\n");
                report.append("  NOTE: Verification ignores timing constraints.\n");
                return buildResult(
                    new SmtVerificationResult.Verdict.Proven("bounded-model-check", null),
                    report.toString(), invariants, List.of(), List.of(), List.of(),
                    Duration.between(start, Instant.now()), stats);
            }
        }
    }

    /** {@code    Bound: 5 firings (budget + s + 2*src drops on every firing)} ([VER-019] AC1). */
    private static void appendFiringBound(StringBuilder report, FlatNet flatNet, BoundedRun.FiringBound bound) {
        report.append("    Bound: ").append(bound.bound()).append(" firings (")
            .append(BoundedRun.formatRanking(flatNet, bound)).append(" drops on every firing)\n");
    }

    /** {@code 8 none, 16 violation}: each depth the bounded model check answered, in order. */
    private static String formatDepths(List<BoundedRun.DepthStep> steps) {
        var parts = new ArrayList<String>(steps.size());
        for (var d : steps) {
            parts.add(d.depth() + " " + (d.answer() == BoundedRun.DepthAnswer.SAT ? "violation" : "none"));
        }
        return String.join(", ", parts);
    }

    /**
     * A {@code Violated} result for a run the phases of [VER-018] and [VER-019] found and
     * replayed. A firing sequence re-executed under the exact abstract semantics is confirmed by
     * construction, so there is nothing left for the counterexample replay to do.
     */
    private static SmtVerificationResult witnessResult(
            FlatNet flatNet, List<int[]> states, List<String> steps, StringBuilder report, String propDesc,
            List<PInvariant> invariants, SmtVerificationResult.SmtStatistics stats, Instant start
    ) {
        var trace = new ArrayList<MarkingState>(states.size());
        for (int[] state : states) {
            trace.add(AbstractReplayer.toMarking(flatNet, state));
        }
        report.append("\n");
        report.append("=== RESULT ===\n\n");
        report.append("VIOLATED: ").append(propDesc).append("\n");
        report.append("  Counterexample trace (replay order, ").append(trace.size()).append(" states):\n");
        for (int i = 0; i < trace.size(); i++) {
            report.append("    ").append(i).append(": ").append(trace.get(i)).append("\n");
        }
        if (!steps.isEmpty()) {
            report.append("  Firing sequence: ").append(String.join(" -> ", steps)).append("\n");
        }
        report.append("\n  WARNING: This counterexample is in UNTIMED semantics.\n");
        report.append("  It may be spurious if timing constraints prevent this sequence.\n");
        return buildResult(
            new SmtVerificationResult.Verdict.Violated(),
            report.toString(), invariants, List.of(), List.copyOf(trace), List.copyOf(steps), Boolean.TRUE,
            Duration.between(start, Instant.now()), stats);
    }

    /**
     * The property as the report names it, followed by the sink declarations in
     * declaration order when any exist — {@code (sinks: a, b; when h: c, d; when p)}
     * ([VER-014]).
     */
    private String propertyDescription() {
        String sinkDesc = RestSet.describeSinks(sinkPlaces, conditionalSinkList());
        String base = property.description();
        return sinkDesc == null ? base : base + " (" + sinkDesc + ")";
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
     * @param bound       the linear state-equation bound query ([VER-015]), present exactly
     *                    when {@link #verify()} would send it: enabled, not refused by
     *                    [VER-006], and a property with a linear demand — also ahead of the
     *                    name-coloured encoding ([NU-053]);
     *                    {@code null} otherwise (the quiescence properties)
     * @param stateEquation the first query of the state-equation phase ([VER-018]), before any
     *                    refinement, present exactly when {@link #verify()} would send it;
     *                    {@code null} where the phase does not run (the name-coloured encoding,
     *                    a &nu;-net, {@code Ignore} with environment places, or the phase
     *                    disabled)
     */
    public record EncodedScripts(
        String horn, String certificate, boolean coloured, String bound, String stateEquation) {}

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
     * @param invariants  what the encoder conjoins into every rule body: the null-space
     *                    basis, unioned with the semiflows when [VER-007] is enabled
     * @param lp          solves the colour-slot program of [NU-053] ({@link SlotBoundLp});
     *                    {@code buildPlan} calls it only after every structural refusal
     * @param onSlotBound receives the re-checked bound. {@code verify()} runs the solve as its
     *                    own step and reports the bound; {@code encodeScripts()} solves bare and
     *                    reports nothing
     */
    private ColouredAttempt colouredAttempt(
            FlatNet flatNet, List<PInvariant> invariants,
            Function<int[], SlotBoundLp.LpAnswer> lp, Consumer<SlotBoundLp.SlotBound> onSlotBound) {
        boolean hasMatch = net.transitions().stream().anyMatch(t -> t.matchSpec() != null);
        boolean nuBounded = !budgetPlaces.isEmpty();
        // The name-coloured encoding has no injection rule ([VER-006]): its environment
        // places would stay empty and every verdict would describe the closed net. Decline,
        // so the flat encoding, which models injection, answers soundly.
        if (!hasMatch || !nuBounded || !flatNet.environmentInjection().isEmpty()) {
            return new ColouredAttempt(null, null);
        }
        // [VER-006] AC10: an arrival into a coloured place is not a mint.
        if (colouredArrivalReason() != null) {
            return new ColouredAttempt(null, null);
        }
        // A function rather than an answer: buildPlan calls it only after its structural
        // checks, so a net they refuse never runs the simplex.
        var plan = NameColouredEncoder.buildPlan(
            net, flatNet, initialMarking, declaredMints(), fragmentMode, carrierPlaces,
            lp, onSlotBound);
        if (plan == null) {
            return new ColouredAttempt(null, null);
        }
        return new ColouredAttempt(plan, NameColouredEncoder.encode(
            plan, flatNet, initialMarking, property, invariants, sinkPlaces, conditionalSinkList()));
    }

    /** A coloured plan and the encoding built from it; see {@link #colouredAttempt}. */
    private record ColouredAttempt(
        NameColouredEncoder.ColouredPlan plan,
        SmtEncoder.SmtEncoding encoding
    ) {}

    /** See {@link EncodedScripts}. */
    public EncodedScripts encodeScripts() {
        OutputActionCheck.requireOutputProducingActions(net);
        prepare();
        FlatNet flatNet = flatNet();
        // AUTO decides from the same fact here as in verify() — whether the basis lost a law
        // to the H1 guard — so the script this reports is the script that would be sent.
        // Deciding it differently (AUTO read as OFF) made the parity goldens pin something
        // the pipeline never emits for a net where AUTO unions ([VER-007] AC2).
        var invariants = encoderInvariants(flatNet, initialMarking, semiflowInvariants);
        // The colour-slot bound is solved bare: no deadline is bound here, so the simplex's
        // checkpoints do nothing and the script carries the k verify() would use.
        var coloured = colouredAttempt(
            flatNet, invariants, c -> SlotBoundLp.solve(flatNet, initialMarking, c), _ -> {});
        // The bound query (VER-015) exactly when verify() would send it: enabled, not refused
        // by VER-006, and a property with a linear demand (else null), on the flat path and
        // ahead of the name-coloured encoding alike.
        String bound = linearBound
                && !ignoresEnvironment()
            ? LinearBound.encode(flatNet, initialMarking, property)
            : null;
        var conditional = conditionalSinkList();
        // The state-equation query ([VER-018]) exactly when verify() would send it, so this
        // mirrors `flatPhases` there — no plan conjunct, since a net without match transitions
        // never has one.
        boolean hasMatch = net.transitions().stream().anyMatch(t -> t.matchSpec() != null);
        String stateEquationQuery = !hasMatch
                && stateEquationPhase
                && !ignoresEnvironment()
            ? StateEquationQuery.encode(flatNet, initialMarking, property, sinkPlaces, conditional, List.of())
            : null;
        if (coloured.encoding() != null) {
            return new EncodedScripts(coloured.encoding().smt2(), null, true, bound, stateEquationQuery);
        }
        var flat = SmtEncoder.encode(
            flatNet, initialMarking, property, invariants, sinkPlaces, counterexampleReplay,
            conditional, stateEquation);
        String certificate = CertificateChecker.vcScript(
            placeholderCertificate(flatNet.placeCount() + flat.counterCount()), flatNet,
            initialMarking, property, sinkPlaces, invariants, conditional, stateEquation);
        return new EncodedScripts(flat.smt2(), certificate, false, bound, stateEquationQuery);
    }

    /**
     * Why Route B (NU-050) would observe an environment place it does not model, or {@code null}
     * when its verdict stands ([VER-006] AC8). Under {@code AlwaysAvailable} / {@code Bounded(k)}
     * the name-partition graph holds an environment place as an inexhaustible input: its count
     * stays frozen and it carries no injected names. The rules are checked in a fixed order and
     * names are scanned in code-point order, so every implementation names the same culprit.
     * {@code Ignore} is left to the existing vacuity downgrade.
     */
    static String routeBEnvObservation(
            PetriNet net,
            NameFragment fragment,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode,
            PrioritySemantics prioritySemantics,
            boolean quiescenceVacuous
    ) {
        if (environmentPlaces.isEmpty() || environmentMode instanceof EnvironmentAnalysisMode.Ignore) {
            return null;
        }
        // Only environment places the net declares: an undeclared one has nothing to observe.
        var declared = new HashSet<String>();
        net.places().forEach(p -> declared.add(p.name()));
        var envNames = new TreeSet<String>(CodePointOrder.COMPARATOR);
        environmentPlaces.forEach(ep -> {
            if (declared.contains(ep.name())) {
                envNames.add(ep.name());
            }
        });
        var transitions = new ArrayList<>(net.transitions());
        transitions.sort(Comparator.comparing(Transition::name, CodePointOrder.COMPARATOR));

        // 1. A coloured environment place: the graph injects no names into it.
        for (var p : envNames) {
            if (fragment.isColoured(p)) {
                return routeBEnvReason(p, "carries ν-names (a match key or carrier place)");
            }
        }
        // 2. An inhibitor arc tests the frozen count.
        for (var p : envNames) {
            for (var t : transitions) {
                if (t.inhibitors().stream().anyMatch(a -> a.place().name().equals(p))) {
                    return routeBEnvReason(p, "is tested by an inhibitor arc of transition '" + t.name() + "'");
                }
            }
        }
        // 3. Conflict-priority pruning compares against the frozen count.
        if (prioritySemantics == PrioritySemantics.CONFLICT) {
            for (var p : envNames) {
                long consumers = transitions.stream()
                    .filter(t -> t.inputSpecs().stream().anyMatch(a -> a.place().name().equals(p)))
                    .count();
                if (consumers >= 2) {
                    return routeBEnvReason(p, "is a consumed input shared under conflict priority");
                }
            }
        }
        // 4. The property reads the frozen count.
        var observed = new HashSet<String>();
        if (isReachabilitySafety(property)) {
            propertyPlaces(property).forEach(pl -> observed.add(pl.name()));
        } else if (!quiescenceVacuous) {
            switch (property) {
                case SmtProperty.DeadlockFree() -> {
                    var sinks = new HashSet<String>();
                    sinkPlaces.forEach(pl -> sinks.add(pl.name()));
                    for (var p : envNames) {
                        if (!sinks.contains(p)) {
                            observed.add(p);
                        }
                    }
                    conditionalSinks.forEach(cs -> observed.add(cs.marker().name()));
                }
                case SmtProperty.TerminatesAtSink() -> sinkPlaces.forEach(pl -> observed.add(pl.name()));
                default -> propertyPlaces(property).forEach(pl -> observed.add(pl.name()));
            }
        }
        for (var p : envNames) {
            if (observed.contains(p)) {
                return routeBEnvReason(p, "is read by the property");
            }
        }
        return null;
    }

    private static String routeBEnvReason(String place, String why) {
        return "environment place '" + place + "' " + why + "; the name-partition state-class graph "
            + "(NU-050, Route B) models an environment place only as an inexhaustible input, not its "
            + "token count or the names injected into it; refusing to certify (VER-006)";
    }

    /** The places a property names — the ones that must resolve for its verdict to mean anything. */
    private static List<Place<?>> propertyPlaces(SmtProperty property) {
        return switch (property) {
            case SmtProperty.DeadlockFree() -> List.of();
            case SmtProperty.TerminatesAtSink() -> List.of();
            case SmtProperty.MutualExclusion me -> List.of(me.p1(), me.p2());
            case SmtProperty.PlaceBound pb -> List.of(pb.place());
            case SmtProperty.BranchPlaceBound bpb -> List.of(bpb.place());
            case SmtProperty.Unreachable ur -> List.copyOf(ur.places());
            case SmtProperty.JoinedOrDeadLettered jdl -> List.of(jdl.pending());
            // The waivers too: a mistyped waiver would never be marked, so it would silently
            // turn a waived lower bound into an unconditional one.
            case SmtProperty.QuiescentCount qc -> {
                var named = new ArrayList<Place<?>>(qc.places());
                named.addAll(qc.waivedBy());
                yield named;
            }
        };
    }

    /**
     * Whether Commoner's theorem governs this net, so a siphon/trap answer may be turned
     * into a PROVEN.
     *
     * <p>The theorem — every siphon contains an initially marked trap implies
     * deadlock-freedom — is about an <strong>ordinary</strong> net, one where the only
     * reason a transition is disabled is an input place with too few tokens. The siphon and
     * trap fixpoints in {@link StructuralCheck} are computed from the pre/post vectors alone
     * and never read {@code readPlaces}, {@code inhibitorPlaces}, {@code resetPlaces} or
     * {@code consumeAll}, so on a net carrying any of those the analysis answers a question
     * about a DIFFERENT, strictly more permissive net: dropping a read or inhibitor arc can
     * only add firings, which is the wrong direction for a deadlock proof. An arc weight
     * above one is the same problem — a place holding one token satisfies {@code m >= 1} but
     * not {@code exactly(2)}.
     *
     * <p>Each of these was demonstrated to produce a PROVEN for a net both executors run to
     * a dead marking: {@code t1: one(a) read(g) -> g} with {@code t2: one(g) -> a} from
     * {@code {a:1}}; {@code t: exactly(2, a) -> a} from {@code {a:1}}; {@code t: one(a)
     * inhibitor(b) -> a} from {@code {a:1, b:1}}. Refusing the shortcut costs a fixpoint
     * query and sends those nets to a route that models what disables them.
     */
    private static boolean commonerApplies(FlatNet flatNet) {
        for (var ft : flatNet.transitions()) {
            if (ft.readPlaces().length > 0
                    || ft.inhibitorPlaces().length > 0
                    || ft.resetPlaces().length > 0) {
                return false;
            }
            for (boolean all : ft.consumeAll()) {
                if (all) {
                    return false;
                }
            }
            for (int weight : ft.preVector()) {
                if (weight > 1) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * VER-006 AC3: why the {@code bounded(k)} model does not describe the executor on this
     * net, or {@code null} when it does. Every route models a {@code bounded(k)} environment
     * place as a source holding at most k: the flat encoding caps each successor there at k,
     * the state-class graphs enable an environment input exactly when it demands at most k,
     * and the quiescence clause calls a demand above k permanently disabled. That holds only
     * when the initial marking holds at most k on each environment place and no transition
     * deposits into one. Environment places are checked in code-point order, the initial
     * marking first; the depositing transition named is the first in code-point order, a
     * completion step {@code complete:<t>} named as {@code t}.
     */
    static String boundedPremiseViolation(
            PetriNet net, MarkingState initialMarking,
            Collection<EnvironmentPlace<?>> environmentPlaces, EnvironmentAnalysisMode mode) {
        if (!(mode instanceof EnvironmentAnalysisMode.Bounded(int k)) || environmentPlaces.isEmpty()) {
            return null;
        }
        var places = environmentPlaces.stream()
            .map(EnvironmentPlace::place)
            .sorted(Comparator.comparing(Place::name, CodePointOrder.COMPARATOR))
            .toList();
        for (var place : places) {
            int held = initialMarking.tokens(place);
            if (held > k) {
                return boundedPremiseReason(place.name(), k,
                    "the initial marking holds " + held + " tokens there, more than " + k);
            }
        }
        for (var place : places) {
            // A split transition deposits through its completion step; name the transition
            // itself ([VER-004]).
            var depositor = net.transitions().stream()
                .filter(t -> t.outputPlaces().contains(place))
                .map(t -> InFlight.sourceTransition(net, t.name()))
                .min(CodePointOrder.COMPARATOR);
            if (depositor.isPresent()) {
                return boundedPremiseReason(place.name(), k,
                    "transition '" + depositor.get() + "' deposits into it");
            }
        }
        return null;
    }

    private static String boundedPremiseReason(String place, int k, String what) {
        return "environment place '" + place + "' is outside the Bounded(" + k + ") premises (VER-006 AC3): "
            + what + ". Every route models it as a source holding at most " + k
            + ", so a verdict would not describe the executor";
    }

    /** The name of the first place the property names that is not in the flat net, or {@code null}. */
    private static String unresolvedPropertyPlace(FlatNet flatNet, SmtProperty property) {
        for (var place : propertyPlaces(property)) {
            if (flatNet.indexOf(place) < 0) {
                return place.name();
            }
        }
        return null;
    }

    /**
     * The same question as {@link #unresolvedPropertyPlace(FlatNet, SmtProperty)}, asked
     * before Phase 1 has a flat net: the name of the first place the property names that the
     * net does not declare, or {@code null}. Reads
     * {@link NetFlattener#declaredPlaces(PetriNet)} — the very set the flattener indexes —
     * so the two guards agree on what "resolves" means, reset-arc places included.
     */
    private static String unresolvedPropertyPlace(PetriNet net, SmtProperty property) {
        var declared = NetFlattener.declaredPlaces(net);
        for (var place : propertyPlaces(property)) {
            if (!declared.contains(place)) {
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
        return encoderInvariants(flatNet, initialMarking,
            semiflowInvariants ? SemiflowMode.ON : SemiflowMode.OFF);
    }

    /**
     * The same list, deciding {@link SemiflowMode#AUTO} the way {@link #verify} decides it:
     * union exactly when the basis LOST a law to the H1 guard ([VER-007]). {@code verify}
     * reads that fact off its own drop list; this recomputes it from the same validation,
     * so the reported script and the sent script cannot disagree.
     */
    static List<PInvariant> encoderInvariants(
            FlatNet flatNet, MarkingState initialMarking, SemiflowMode mode
    ) {
        var matrix = IncidenceMatrix.from(flatNet);
        var extraction = PInvariantComputer.computeChecked(matrix, flatNet, initialMarking);
        var validation = PInvariantComputer.validateExact(
            extraction.valid(), matrix, flatNet, initialMarking);
        List<PInvariant> invariants = validation.valid();
        boolean basisLostALaw = validation.dropped().stream()
            .anyMatch(r -> r.contains("Strengthening.lean H1"));
        if (mode == SemiflowMode.ON || (mode == SemiflowMode.AUTO && basisLostALaw)) {
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
            trace, transitions, null, elapsed, stats, SmtVerificationResult.Route.SMT);
    }

    /** {@link #buildResult} on a route other than the SMT pipeline ([VER-003] AC4). */
    private static SmtVerificationResult buildResult(
            SmtVerificationResult.Verdict verdict, String report,
            List<PInvariant> invariants, List<String> discoveredInvariants,
            List<MarkingState> trace, List<String> transitions,
            Duration elapsed, SmtVerificationResult.SmtStatistics stats,
            SmtVerificationResult.Route route
    ) {
        return buildResult(verdict, report, invariants, discoveredInvariants,
            trace, transitions, null, elapsed, stats, route);
    }

    private static SmtVerificationResult buildResult(
            SmtVerificationResult.Verdict verdict, String report,
            List<PInvariant> invariants, List<String> discoveredInvariants,
            List<MarkingState> trace, List<String> transitions,
            Boolean counterexampleConfirmed,
            Duration elapsed, SmtVerificationResult.SmtStatistics stats
    ) {
        return buildResult(verdict, report, invariants, discoveredInvariants,
            trace, transitions, counterexampleConfirmed, elapsed, stats,
            SmtVerificationResult.Route.SMT);
    }

    private static SmtVerificationResult buildResult(
            SmtVerificationResult.Verdict verdict, String report,
            List<PInvariant> invariants, List<String> discoveredInvariants,
            List<MarkingState> trace, List<String> transitions,
            Boolean counterexampleConfirmed,
            Duration elapsed, SmtVerificationResult.SmtStatistics stats,
            SmtVerificationResult.Route route
    ) {
        return new SmtVerificationResult(verdict, route, report, invariants, discoveredInvariants,
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
            SmtVerificationResult result, boolean hasMatch, boolean nuBounded, boolean exact, String undeclared
    ) {
        if (!hasMatch || result.verdict() instanceof SmtVerificationResult.Verdict.Unknown) {
            return result;
        }
        // Coloured path (NU-050 #1 / NU-053, Route A) is checked FIRST: name equality is
        // encoded by name-colouring over the colour-slot bound, so no counterexample equates
        // two distinct names. This holds for reachability-safety AND quiescence (deadlock /
        // joined-or-dead-lettered), so the quiescence downgrade below does NOT apply when a
        // coloured plan was used: the colour-aware deadlock encoding does not over-fire joins.
        // The verdict rests on the mint and relay contracts (NU-010, NU-051).
        if (exact) {
            String note = "\nNote: ν-join name equality is encoded by name-colouring over k colour slots, "
                + "k bounding the live names: a join fires only on one colour, so no counterexample "
                + "equates two different names (NU-050 #1 / NU-053). The verdict assumes the mint and "
                + "relay contracts named above.\n";
            return new SmtVerificationResult(
                result.verdict(), result.route(), result.report() + note, result.invariants(),
                result.discoveredInvariants(), result.counterexampleTrace(),
                result.counterexampleTransitions(), result.counterexampleConfirmed(),
                result.elapsed(), result.statistics());
        }
        if (!isReachabilitySafety(property)) {
            return downgradeToUnknown(result, withPointer(
                "ν-matching transitions present and the property depends on quiescence "
                + "(deadlock / joined-or-dead-lettered); the name-blind over-approximation "
                + "cannot decide it soundly — deferred to the exact ν-analysis (NU-050)", undeclared));
        }
        if (!nuBounded) {
            return downgradeToUnknown(result, withPointer(
                "ν-matching transitions present with unbounded fresh names (no budget place "
                + "declared via budgetPlaces(...)); reachability over unbounded fresh names is "
                + "undecidable (NU-040) — declare the budget place(s) that gate minting to "
                + "verify within the bounded fragment", undeclared));
        }
        // Bounded reachability-safety outside the name-coloured fragment: `Proven` is
        // sound; a `Violated` counterexample may be spurious pending the exact ν-analysis.
        String note = "\nNote: matched (ν-join) transitions are over-approximated (name equality "
            + "assumed satisfiable). 'Proven' is sound; a 'Violated' counterexample may be "
            + "spurious pending the exact ν-analysis (NU-050).\n";
        return new SmtVerificationResult(
            result.verdict(), result.route(), result.report() + note, result.invariants(),
            result.discoveredInvariants(), result.counterexampleTrace(),
            result.counterexampleTransitions(), result.counterexampleConfirmed(),
            result.elapsed(), result.statistics());
    }

    /** {@code reason}, then the undeclared-mint pointer when there is one ([NU-010]). */
    private static String withPointer(String reason, String undeclared) {
        return undeclared == null ? reason : reason + "; " + undeclared;
    }

    private static SmtVerificationResult downgradeToUnknown(
            SmtVerificationResult result, String reason
    ) {
        String report = result.report() + "\nDowngraded to UNKNOWN: " + reason + "\n";
        return new SmtVerificationResult(
            new SmtVerificationResult.Verdict.Unknown(reason), result.route(), report,
            result.invariants(), List.of(), List.of(), List.of(), null, result.elapsed(),
            result.statistics());
    }

    /**
     * Whether a property is a <em>reachability-safety</em> property — one whose
     * violation is a reachable bad marking. For these the matched-transition
     * over-approximation is sound for {@code Proven}. Quiescence-based
     * properties (deadlock, terminates-at-sink, joined-or-dead-lettered,
     * quiescent-count) are not: their violation
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
            case SmtProperty.QuiescentCount _ -> false;
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
            List.of(), null, AbstractReplayer.DEFAULT_NODE_BUDGET);
    }

    /**
     * {@link #assessCounterexample(FlatNet, MarkingState, CounterexampleDecoder.DecodedStates,
     * SmtProperty, Set)} with the conditional sink declarations ([VER-014]) and the two
     * test seams applied: {@code stateSetOverride} replaces the decoded anchor set when
     * non-null, {@code nodeBudget} the replay's node budget.
     */
    static ReplayAssessment assessCounterexample(
            FlatNet flatNet, MarkingState initialMarking,
            CounterexampleDecoder.DecodedStates decoded,
            SmtProperty property, Set<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks,
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
                flatNet, initialMarking, states, property, sinkPlaces, conditionalSinks,
                AbstractReplayer.MAX_SEGMENT_STEPS, nodeBudget);
        } catch (RuntimeException | StackOverflowError e) {
            // A replay that ran out of room degrades like a truncated search — it never
            // withdraws a verdict on its own, and a StackOverflowError on a deep net IS
            // that capacity limit. A replayer DEFECT is not: it would be
            // indistinguishable from an exhausted search and so invisible forever, which
            // is why ProgrammingError re-throws it (the TypeScript verifier makes the
            // same split, re-throwing TypeError and keeping RangeError).
            ProgrammingError.rethrowIfProgrammingError(e);
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
            Duration timeout,
            List<RestSet.ConditionalSinks> conditionalSinks,
            boolean stateEquation);
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

    /**
     * Every relay declaration of {@code net} as {@code '<transition>' -> '<place>'}, in
     * transition then declaration order (NU-054) — what the BASE-mode report names as ignored.
     */
    private static List<String> relayDeclarations(PetriNet net) {
        var out = new ArrayList<String>();
        for (var t : net.transitions()) {
            if (t.matchSpec() == null) continue;
            for (var relay : t.matchSpec().relays()) {
                out.add("'" + t.name() + "' -> '" + relay.place().name() + "'");
            }
        }
        return out;
    }
}
