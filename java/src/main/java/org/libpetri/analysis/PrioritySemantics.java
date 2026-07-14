package org.libpetri.analysis;

/**
 * Selects how the Route-B name-aware state-class graph
 * ({@link NameStateClassGraph}) treats transition priority when enumerating the
 * enabled transitions of a class (NU-052).
 *
 * <p>{@link #NONE} is the default and reproduces the shipped behavior byte-for-byte:
 * every base-enabled transition is expanded, so the analysis is a sound
 * over-approximation that ignores priority (and treats a delayed low-priority
 * transition as free to fire before an immediate high-priority one).
 *
 * <p>{@link #CONFLICT} models the executor's <i>conflict-only</i> priority
 * resolution. libpetri's {@code BitmapNetExecutor} fires ready transitions in
 * strictly-descending priority order within a scheduling pass, so when a
 * higher-priority transition consumes a token a conflicting lower-priority one
 * competes for, the lower-priority transition does not fire. {@code CONFLICT}
 * prunes exactly those firings from the graph: a transition {@code L} is not
 * expanded from a class when another enabled transition {@code H} in the same
 * class
 * <ul>
 *   <li>has strictly higher priority ({@code H.priority() > L.priority()}),</li>
 *   <li>shares at least one <b>consumed</b> input place with {@code L} under
 *       <b>real competition</b> — the shared place cannot satisfy both demands at
 *       once ({@code count(p) < demand_H(p) + demand_L(p)}); read and inhibitor
 *       arcs do not count, and</li>
 *   <li>becomes ready no later than {@code L} by the <b>DBM residual-earliest</b>
 *       predicate ({@code readyEarliest[H] <= readyEarliest[L] + EPS}), comparing
 *       the class-relative earliest-ready times captured on the base state class
 *       (the DBM lower bounds, before {@code letTimePass}) rather than the static
 *       {@code H.timing().earliest() <= L.timing().earliest()} — which is unsound
 *       on the zone off-diagonal where enabling epochs differ; this predicate
 *       subsumes the immediate-H case ({@code readyEarliest[H] == 0}).</li>
 * </ul>
 *
 * <p><b>Soundness.</b> The pruning is sound with respect to libpetri's eager,
 * priority-ordered executor: it removes only interleavings in which a
 * lower-priority transition fires ahead of a ready, conflicting, strictly-higher
 * priority one — behavior the executor never produces. {@code L} is not lost: from
 * any class reachable after {@code H} fires, {@code L} is re-examined and expands
 * once the conflict is gone. The timing side-condition keeps the reverse case
 * (an immediate low-priority transition vs. a delayed high-priority one) unpruned.
 * The canonical use is the timed dead-letter-drain idiom: an immediate,
 * higher-priority matched consumer (e.g. a &nu;-join) vs. a delayed, lower-priority
 * orphan drain over the same place — where the priority/timing-blind default
 * reports a spurious stall (the drain stealing a live token) that the executor
 * cannot exhibit.
 */
public enum PrioritySemantics {
    /** Ignore priority; expand every base-enabled transition (default, unchanged). */
    NONE,
    /** Prune a lower-priority transition in a consumed-input conflict with a
     *  no-later-ready, strictly-higher-priority enabled transition. */
    CONFLICT
}
