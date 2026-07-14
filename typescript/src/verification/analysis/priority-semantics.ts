/**
 * Priority semantics for the ν-aware Route B name-partition state-class graph
 * ({@link NameStateClassGraph}) — NU-052.
 *
 * The name-aware state-class graph is otherwise priority- and timing-blind: it
 * expands every base-enabled transition. On the timed dead-letter-drain idiom —
 * an immediate, higher-priority matched consumer (a ν-join) competing for a
 * coloured token with a delayed, lower-priority orphan drain — that blindness
 * reports a spurious stall (the drain stealing a live token) that the eager,
 * priority-ordered executor can never produce.
 *
 * - `none` (default) reproduces the shipped behaviour byte-for-byte: every
 *   base-enabled transition is expanded, so the analysis is a sound
 *   over-approximation that ignores priority (and treats a delayed low-priority
 *   transition as free to fire before an immediate high-priority one).
 * - `conflict` models the executor's *conflict-only* priority resolution.
 *   libpetri's `BitmapNetExecutor` fires ready transitions in strictly-descending
 *   priority order within a scheduling pass, so when a higher-priority transition
 *   consumes a token that a conflicting lower-priority one competes for, the
 *   lower-priority transition does not fire. `conflict` prunes exactly those
 *   firings: a transition `L` is not expanded from a class when another enabled
 *   transition `H` in the same class
 *   - has strictly higher priority (`H.priority > L.priority`),
 *   - shares at least one **consumed** input place with `L` under **real
 *     competition** — the shared place cannot satisfy both demands at once
 *     (`count(p) < demand_H(p) + demand_L(p)`); read and inhibitor arcs do not
 *     count,
 *   - becomes ready no later than `L` by the **DBM residual-earliest** predicate
 *     (`readyEarliest[H] <= readyEarliest[L] + EPS`), comparing the class-relative
 *     earliest-ready times captured on the base state class (the DBM lower bounds,
 *     before `letTimePass`) rather than the static
 *     `earliest(H.timing) <= earliest(L.timing)` — which is unsound on the zone
 *     off-diagonal where enabling epochs differ; this predicate subsumes the
 *     immediate-H case (`readyEarliest[H] === 0`), and
 *   - actually fires in this class (a name-disabled join produces no
 *     name-successor, so it must not pre-empt a conflicting drain).
 *
 * The pruning is sound with respect to the eager, priority-ordered executor: it
 * removes only interleavings in which a lower-priority transition fires ahead of
 * a ready, conflicting, strictly-higher-priority one — behaviour the executor
 * never produces. `L` is not lost: in any class reachable after `H` fires, `L` is
 * re-examined and expands once the conflict is gone.
 */
export type PrioritySemantics = 'none' | 'conflict';
