package org.libpetri.smt;

import org.libpetri.analysis.MarkingState;
import org.libpetri.smt.invariant.PInvariant;

import java.time.Duration;
import java.util.List;

/**
 * Result of SMT-based verification.
 *
 * @param verdict                  proven, violated, or unknown
 * @param route                    which route decided this verdict ([VER-003]). Read it before
 *     concluding anything from an <b>empty</b> {@code invariants}: off {@link Route#SMT} that
 *     means "not computed", never "none exist". A non-empty list is real whatever the route says.
 * @param report                   human-readable analysis report
 * @param invariants               P-invariants found during analysis
 * @param discoveredInvariants     IC3-synthesized inductive invariants (empty if not proven by IC3)
 * @param counterexampleTrace      marking trace to error (empty if proven)
 * @param counterexampleTransitions firing sequence to error (empty if proven)
 * @param counterexampleConfirmed  whether the counterexample <b>replays in the untimed
 *     abstraction</b> ([VER-003], [VER-004]) — the outcome of the abstract counterexample replay
 *     ({@link org.libpetri.smt.z3.AbstractReplayer}), as a TRI-STATE. It says nothing about
 *     timing: a {@code TRUE} trace of a timed net may be impossible once the clocks are read,
 *     which is what {@code counterexampleTiming} reports. The
 *     canonical definition lives on the Rust {@code VerificationResult}; this
 *     restates it:
 *     <ul>
 *       <li>{@code TRUE} — the replay chained an abstract firing run from M0 to a
 *           property-violating marking; {@code counterexampleTrace} is that run,
 *           in firing order.</li>
 *       <li>{@code FALSE} — the replay applied and did NOT confirm the
 *           counterexample. Two shapes, reported the same way:
 *           <ul>
 *             <li>it could not conclude (nothing decodable, M0 not among the
 *                 decoded states, or a budget exhausted) — VIOLATED stands,
 *                 unconfirmed, on Spacer's SAT answer alone;</li>
 *             <li>it refuted the trace outright (no firing chain reaches the
 *                 violation) — the verdict is downgraded to UNKNOWN. A refutation
 *                 is strictly more informative than "did not apply", so it reports
 *                 {@code FALSE}, never {@code null}.</li>
 *           </ul></li>
 *       <li>{@code null} — replay did not apply: a non-violated verdict that no
 *           replay touched, replay disabled via
 *           {@link SmtVerifier#counterexampleReplay(boolean)}, or the coloured
 *           &nu;-encoding / Route B path, whose state shapes are outside the flat
 *           replayer's scope.</li>
 *     </ul>
 * @param counterexampleTiming     how the counterexample relates to the net's timing
 *     ([VER-003], [VER-023]); {@code null} unless the verdict is {@link Verdict.Violated}. See
 *     {@link CounterexampleTiming}. The verdict itself is never changed by it: the untimed claim
 *     is the contract ([VER-004]).
 * @param elapsed                  wall-clock time for verification
 * @param statistics               solver statistics
 */
public record SmtVerificationResult(
    Verdict verdict,
    Route route,
    String report,
    List<PInvariant> invariants,
    List<String> discoveredInvariants,
    List<MarkingState> counterexampleTrace,
    List<String> counterexampleTransitions,
    Boolean counterexampleConfirmed,
    CounterexampleTiming counterexampleTiming,
    Duration elapsed,
    SmtStatistics statistics
) {

    /**
     * The result without a {@code counterexampleTiming} ({@code null}): the component list
     * before [VER-023], kept so code that built a result by hand still compiles.
     */
    public SmtVerificationResult(
        Verdict verdict,
        Route route,
        String report,
        List<PInvariant> invariants,
        List<String> discoveredInvariants,
        List<MarkingState> counterexampleTrace,
        List<String> counterexampleTransitions,
        Boolean counterexampleConfirmed,
        Duration elapsed,
        SmtStatistics statistics
    ) {
        this(verdict, route, report, invariants, discoveredInvariants, counterexampleTrace,
            counterexampleTransitions, counterexampleConfirmed, null, elapsed, statistics);
    }

    /**
     * How a {@link Verdict.Violated} counterexample relates to the net's timing ([VER-003],
     * [VER-023]).
     *
     * <p>Every route but Route B decides over the <b>untimed</b> abstraction ([VER-004]): a
     * counterexample it returns is a firing sequence that ignores the clocks, and on a timed
     * net the clocks may forbid it. This field says which case a violation is, and whether the
     * opt-in {@link SmtVerifier#timedCounterexampleCheck(boolean) timed check} looked. It never
     * changes the verdict.
     */
    public enum CounterexampleTiming {
        /** Every transition is {@code immediate}: timing cannot affect the trace. */
        UNTIMED_NET,
        /**
         * The net is timed, and the counterexample comes from the untimed model without a check
         * under timing — the timed check is off, or does not apply (environment places, whose
         * injection the timed graph does not model, or a &nu;-net decided off Route B, whose
         * name correlation it does not model).
         */
        UNTIMED_ABSTRACTION,
        /**
         * The deciding route already explores timed behaviour — Route B's &nu; name-partition
         * state-class graph on a timed net — so the trace is a run of the timed semantics. The
         * graph ignores priority, so it is not necessarily a run the executor takes.
         */
        TIMED_EXACT,
        /**
         * The timed check ran and the timed state-class graph reaches a violating class. The
         * counterexample trace and transitions are <b>replaced</b> with the shortest path to it in
         * the timed graph, and the report says so. That path is an ordered firing sequence, so
         * {@code counterexampleConfirmed} is {@code TRUE}. The timed graph ignores priority: a net
         * that relies on priority to exclude the path can still get this outcome.
         */
        TIMED_CONFIRMED,
        /**
         * The timed check ran, the timed state-class graph closed, and no class of it violates
         * the property: it holds under timing — a timed claim only. The verdict stays
         * {@code Violated} (the untimed claim is the contract), the untimed trace is kept, and
         * the report states it with the class count.
         */
        SPURIOUS_UNDER_TIMING,
        /**
         * The timed check ran but did not finish: the timed graph exceeded
         * {@link SmtVerifier#enumerationMaxClasses(int)}, or the
         * {@link SmtVerifier#totalBudget(Duration) total budget} ran out.
         */
        TIMED_UNDECIDED
    }

    /**
     * Which route decided a verdict ([VER-003]).
     *
     * <p>The routes do equivalent work by different means, and a consumer reading the
     * result's fields rather than its report needs to know which one answered:
     * {@link #ENUMERATION} and {@link #NU_SCG} decide by exploring a finite graph and
     * compute no P-invariants at all.
     *
     * <p>The rule for {@link SmtVerificationResult#invariants()} is about the <em>empty</em>
     * case only: an empty list from a route other than {@link #SMT} means "not computed",
     * not "the net has none". A non-empty list is always real — {@link #UNAVAILABLE} in
     * particular still carries the invariants the pipeline computed before it found no
     * usable solver, and {@link #STRUCTURAL} carries whatever the proof rested on.
     */
    public enum Route {
        /** The IC3/PDR pipeline: flatten, invariants, encode, solve ([VER-001]). */
        SMT,
        /** Bounded state-space enumeration ([VER-017]). */
        ENUMERATION,
        /** The &nu; name-partition state-class graph ([VER-012], Route B). */
        NU_SCG,
        /** A structural proof — Commoner's theorem, or the linear bound of [VER-015]. */
        STRUCTURAL,
        /** No route could run (no solver, an unresolved property place). */
        UNAVAILABLE
    }

    /**
     * Verification verdict.
     */
    public sealed interface Verdict {
        /**
         * Property proven safe. No reachable state violates it.
         *
         * @param method             how it was proven ("IC3/PDR", "structural", "P-invariant")
         * @param inductiveInvariant the raw IC3-synthesized inductive invariant formula (may be null)
         */
        record Proven(String method, String inductiveInvariant) implements Verdict {}

        /**
         * Property violated. A counterexample trace is available; whether replay
         * confirmed it is carried by
         * {@link SmtVerificationResult#counterexampleConfirmed()}, not by the
         * verdict.
         */
        record Violated() implements Verdict {}

        /**
         * Could not determine.
         *
         * @param reason explanation (timeout, resource limit, etc.)
         */
        record Unknown(String reason) implements Verdict {}
    }

    /**
     * Solver statistics.
     *
     * @param places             number of places in flattened net
     * @param transitions        number of transitions in flattened net
     * @param invariantsFound    number of P-invariants found
     * @param structuralResult   result of structural pre-check
     */
    public record SmtStatistics(
        int places,
        int transitions,
        int invariantsFound,
        String structuralResult
    ) {}

    /**
     * Returns true if the property was proven safe.
     */
    public boolean isProven() {
        return verdict instanceof Verdict.Proven;
    }

    /**
     * Returns true if a counterexample was found.
     */
    public boolean isViolated() {
        return verdict instanceof Verdict.Violated;
    }
}
