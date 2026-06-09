package org.libpetri.smt;

import org.libpetri.core.Place;

import java.util.Set;

/**
 * Safety properties that can be verified via IC3/PDR.
 *
 * <p>Each property is encoded as an error condition: if a reachable state
 * violates the property, Spacer finds a counterexample. If no violation
 * is reachable, the property is proven.
 */
public sealed interface SmtProperty {

    /**
     * Deadlock-freedom: no reachable marking has all transitions disabled.
     *
     * <p>This is the primary property for Petri net verification.
     * A deadlock means the net is stuck with no possible progress.
     */
    record DeadlockFree() implements SmtProperty {}

    /**
     * Mutual exclusion: two places never have tokens simultaneously.
     *
     * <p>Useful for verifying resource exclusion properties.
     */
    record MutualExclusion(Place<?> p1, Place<?> p2) implements SmtProperty {}

    /**
     * Place bound: a place never exceeds a given token count.
     *
     * <p>Useful for verifying bounded buffer properties.
     */
    record PlaceBound(Place<?> place, int bound) implements SmtProperty {}

    /**
     * Unreachability: the given set of places never all have tokens simultaneously.
     *
     * <p>A marking where all specified places have tokens is an error state.
     */
    record Unreachable(Set<Place<?>> places) implements SmtProperty {}

    /**
     * Branch / budget place bound: a &nu;-net budget or fork-branch place never
     * exceeds {@code bound} tokens — the bounded-budget decidability lever
     * (NU-040).
     *
     * <p>Encodes identically to {@link PlaceBound} (a linear-integer count
     * bound), but names the &nu;-net intent: the live correlation pool is
     * bounded, keeping the well-structured transition system finite. The
     * matched-transition over-approximation is sound for this safety bound —
     * a {@code Proven} verdict holds for the real net, which fires strictly
     * fewer joins than the over-approximation.
     */
    record BranchPlaceBound(Place<?> place, int bound) implements SmtProperty {}

    /**
     * Joined-or-dead-lettered: every forked name is eventually joined or
     * dead-lettered, so no reachable <em>quiescent</em> (deadlocked) marking
     * still holds a token in {@code pending} (NU-040).
     *
     * <p>Violated when a reachable marking is both quiescent and has
     * {@code pending >= 1} — a stranded correlation group.
     */
    record JoinedOrDeadLettered(Place<?> pending) implements SmtProperty {}

    // Factory methods

    static DeadlockFree deadlockFree() {
        return new DeadlockFree();
    }

    static MutualExclusion mutualExclusion(Place<?> p1, Place<?> p2) {
        return new MutualExclusion(p1, p2);
    }

    static PlaceBound placeBound(Place<?> place, int bound) {
        return new PlaceBound(place, bound);
    }

    static Unreachable unreachable(Set<Place<?>> places) {
        return new Unreachable(Set.copyOf(places));
    }

    static BranchPlaceBound branchPlaceBound(Place<?> place, int bound) {
        return new BranchPlaceBound(place, bound);
    }

    static JoinedOrDeadLettered joinedOrDeadLettered(Place<?> pending) {
        return new JoinedOrDeadLettered(pending);
    }
}
