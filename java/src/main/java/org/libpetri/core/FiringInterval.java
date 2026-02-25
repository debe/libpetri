package org.libpetri.core;

import java.time.Duration;

/**
 * Time Petri Net firing interval [α, β].
 * <p>
 * α = earliest firing time (minimum delay before transition MAY fire)
 * β = latest firing time (deadline - transition MUST fire or be disabled)
 * <p>
 * For immediate firing with deadline: use [0, β]
 * For exact timing: use [α, α]
 *
 * @deprecated Use {@link Timing} instead, which provides a more expressive sealed interface
 *             following the pattern of {@link In} and {@link Out}.
 */
@Deprecated(forRemoval = true)
public record FiringInterval(Duration earliest, Duration latest) {

    /** Maximum duration used for "unconstrained" intervals (~100 years) */
    private static final Duration MAX_DURATION = Timing.MAX_DURATION;

    public FiringInterval {
        if (earliest.isNegative()) {
            throw new IllegalArgumentException(
                "Invalid firing interval: earliest time must be non-negative (got %s)".formatted(earliest)
            );
        }
        if (latest.compareTo(earliest) < 0) {
            throw new IllegalArgumentException(
                "Invalid firing interval: latest (%s) must be >= earliest (%s)".formatted(latest, earliest)
            );
        }
    }

    /** Immediate firing with deadline: [0, β] */
    public static FiringInterval immediate(Duration deadline) {
        return new FiringInterval(Duration.ZERO, deadline);
    }

    /** Exact timing: [α, α] - fires exactly at time α */
    public static FiringInterval exact(Duration time) {
        return new FiringInterval(time, time);
    }

    /** No time constraint: [0, ∞) */
    public static FiringInterval unconstrained() {
        return new FiringInterval(Duration.ZERO, MAX_DURATION);
    }

    /** Check if the transition can fire (earliest time reached). */
    public boolean canFire(Duration elapsed) {
        return elapsed.compareTo(earliest) >= 0;
    }

    /** Check if the transition MUST fire (deadline reached). */
    public boolean mustFire(Duration elapsed) {
        return elapsed.compareTo(latest) >= 0;
    }

    /** Get the deadline (latest firing time). */
    public Duration deadline() {
        return latest;
    }

    /** Check if deadline is effectively infinite (no meaningful timeout needed). */
    public boolean hasFiniteDeadline() {
        return latest.compareTo(MAX_DURATION) < 0;
    }
}
