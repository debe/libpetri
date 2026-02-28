package org.libpetri.core;

import java.time.Duration;

/**
 * Firing timing specification for transitions.
 *
 * <p>This sealed hierarchy encodes when a transition can/must fire after becoming enabled.
 * The clock starts when the transition becomes fully enabled (all inputs present, no inhibitors).
 *
 * <p>Based on classical Time Petri Net (TPN) semantics:
 * <ul>
 *   <li>Transition CANNOT fire before earliest time (lower bound)</li>
 *   <li>Transition MUST fire by deadline OR become disabled (upper bound)</li>
 * </ul>
 *
 * <p>The runtime enforces both {@link #earliest()} (delay before firing) and
 * {@link #latest()} (deadline after which the transition is force-disabled).
 *
 * @see In for input specifications
 * @see Out for output specifications
 */
public sealed interface Timing permits
        Timing.Immediate,
        Timing.Deadline,
        Timing.Delayed,
        Timing.Window,
        Timing.Exact,
        Timing.Unconstrained {

    /** Maximum duration used for "unconstrained" intervals (~100 years) */
    Duration MAX_DURATION = Duration.ofDays(365 * 100);

    /**
     * Immediate firing: can fire as soon as enabled, no deadline.
     * Equivalent to interval [0, ∞).
     */
    record Immediate() implements Timing {}

    /**
     * Immediate with deadline: can fire immediately, must fire by deadline.
     * Equivalent to interval [0, by].
     *
     * <p>Use this for "respond within X time" scenarios.
     */
    record Deadline(Duration by) implements Timing {
        public Deadline {
            if (by == null || by.isNegative() || by.isZero()) {
                throw new IllegalArgumentException("Deadline must be positive: " + by);
            }
        }
    }

    /**
     * Delayed firing: must wait, then can fire anytime.
     * Equivalent to interval [after, ∞).
     *
     * <p>Use this for "wait at least X before acting" scenarios.
     */
    record Delayed(Duration after) implements Timing {
        public Delayed {
            if (after == null || after.isNegative()) {
                throw new IllegalArgumentException("Delay must be non-negative: " + after);
            }
        }
    }

    /**
     * Time window: can fire within [earliest, latest].
     * This is the classical TPN firing interval.
     *
     * <p>Use this for "between X and Y time" scenarios.
     */
    record Window(Duration earliest, Duration latest) implements Timing {
        public Window {
            if (earliest == null || earliest.isNegative()) {
                throw new IllegalArgumentException("Earliest must be non-negative: " + earliest);
            }
            if (latest == null || latest.compareTo(earliest) < 0) {
                throw new IllegalArgumentException(
                        "Latest (%s) must be >= earliest (%s)".formatted(latest, earliest)
                );
            }
        }
    }

    /**
     * Exact timing: fires at precisely the specified time.
     * Equivalent to interval [at, at].
     *
     * <p>Use this for "fire exactly at X time" scenarios.
     */
    record Exact(Duration at) implements Timing {
        public Exact {
            if (at == null || at.isNegative()) {
                throw new IllegalArgumentException("Exact time must be non-negative: " + at);
            }
        }
    }

    /**
     * No timing constraint: fire anytime after enabling.
     * Equivalent to interval [0, ∞).
     *
     * @deprecated Use {@link Immediate} instead. Unconstrained has identical semantics
     *             to Immediate (both represent [0, ∞)) and adds no additional value.
     *             This variant will be removed in a future version.
     */
    @Deprecated(since = "1.0", forRemoval = true)
    record Unconstrained() implements Timing {}

    // ==================== Factory Methods ====================

    /**
     * Creates an immediate timing: can fire as soon as enabled.
     *
     * @return Immediate timing spec
     */
    static Immediate immediate() {
        return new Immediate();
    }

    /**
     * Creates a deadline timing: must fire by the specified time.
     *
     * @param by the deadline duration
     * @return Deadline timing spec
     */
    static Deadline deadline(Duration by) {
        return new Deadline(by);
    }

    /**
     * Creates a delayed timing: must wait before firing.
     *
     * @param after the minimum delay
     * @return Delayed timing spec
     */
    static Delayed delayed(Duration after) {
        return new Delayed(after);
    }

    /**
     * Creates a window timing: can fire within [earliest, latest].
     *
     * @param earliest minimum delay before firing
     * @param latest maximum time before must fire
     * @return Window timing spec
     */
    static Window window(Duration earliest, Duration latest) {
        return new Window(earliest, latest);
    }

    /**
     * Creates an exact timing: fires at precisely the specified time.
     *
     * @param at the exact firing time
     * @return Exact timing spec
     */
    static Exact exact(Duration at) {
        return new Exact(at);
    }

    /**
     * Creates an unconstrained timing: no timing requirements.
     *
     * @return Unconstrained timing spec
     * @deprecated Use {@link #immediate()} instead. Unconstrained has identical semantics
     *             to Immediate and will be removed in a future version.
     */
    @Deprecated(since = "1.0", forRemoval = true)
    static Unconstrained unconstrained() {
        return new Unconstrained();
    }

    // ==================== Query Methods ====================

    /**
     * Returns the earliest time the transition can fire after enabling.
     *
     * @return the lower bound of the firing window
     */
    default Duration earliest() {
        return switch (this) {
            case Immediate() -> Duration.ZERO;
            case Deadline(_) -> Duration.ZERO;
            case Delayed(var after) -> after;
            case Window(var e, _) -> e;
            case Exact(var at) -> at;
            case Unconstrained() -> Duration.ZERO;
        };
    }

    /**
     * Returns the latest time by which the transition must fire (or be disabled).
     * Returns ~100 years for unconstrained deadlines.
     *
     * @return the upper bound of the firing window
     */
    default Duration latest() {
        return switch (this) {
            case Immediate() -> MAX_DURATION;
            case Deadline(var by) -> by;
            case Delayed(_) -> MAX_DURATION;
            case Window(_, var l) -> l;
            case Exact(var at) -> at;
            case Unconstrained() -> MAX_DURATION;
        };
    }

    /**
     * Returns true if this timing has a finite deadline that should be considered.
     *
     * @return true if deadline is finite
     */
    default boolean hasDeadline() {
        return switch (this) {
            case Immediate() -> false;
            case Deadline(_) -> true;
            case Delayed(_) -> false;
            case Window(_, _) -> true;
            case Exact(_) -> true;
            case Unconstrained() -> false;
        };
    }

}
