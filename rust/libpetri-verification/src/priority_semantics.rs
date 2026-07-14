//! Priority semantics for the ν-aware Route B name-partition state-class graph
//! ([`NameStateClassGraph`](crate::name_state_class_graph)) — [NU-052].

/// Controls how the ν-aware Route B analyzer treats transition **priority** when
/// it expands a class.
///
/// The name-aware state-class graph is otherwise priority- and timing-blind: it
/// expands every base-enabled transition. On the timed dead-letter-drain idiom —
/// an immediate, higher-priority matched consumer (a ν-join) competing for a
/// coloured token with a delayed, lower-priority orphan drain — that blindness
/// reports a spurious stall (the drain stealing a live token) that the eager,
/// priority-ordered executor can never produce.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PrioritySemantics {
    /// The shipped behaviour, byte-for-byte: every base-enabled transition is
    /// expanded, so the analysis is a sound over-approximation that ignores
    /// priority (and treats a delayed low-priority transition as free to fire
    /// before an immediate high-priority one).
    #[default]
    None,
    /// Models the executor's *conflict-only* priority resolution. libpetri's
    /// `BitmapNetExecutor` fires ready transitions in strictly-descending
    /// priority order within a scheduling pass, so when a higher-priority
    /// transition consumes a token that a conflicting lower-priority one competes
    /// for, the lower-priority transition does not fire. `Conflict` prunes
    /// exactly those firings: a transition `L` is not expanded from a class when
    /// another enabled transition `H` in the same class
    ///
    /// - has strictly higher priority (`H.priority() > L.priority()`),
    /// - shares at least one **consumed** input place with `L` under **real
    ///   competition** — the shared place cannot satisfy both demands at once
    ///   (`count(p) < demand_H(p) + demand_L(p)`); read and inhibitor arcs do
    ///   not count,
    /// - becomes ready no later than `L` by the **DBM residual-earliest**
    ///   predicate (`ready_earliest[H] <= ready_earliest[L] + EPS`), comparing
    ///   the class-relative earliest-ready times captured on the base state
    ///   class (the DBM lower bounds, before `let_time_pass`) rather than the
    ///   static `H.timing().earliest() <= L.timing().earliest()` — which is
    ///   unsound on the zone off-diagonal where enabling epochs differ, and
    ///   this predicate subsumes the immediate-H case (`ready_earliest[H] == 0`),
    ///   and
    /// - actually fires in this class (a name-disabled join produces no
    ///   name-successor, so it must not pre-empt a conflicting drain).
    ///
    /// # Soundness
    ///
    /// The pruning is sound with respect to libpetri's eager, priority-ordered
    /// executor: it removes only interleavings in which a lower-priority
    /// transition fires ahead of a ready, conflicting, strictly-higher-priority
    /// one — behaviour the executor never produces. `L` is not lost: in any class
    /// reachable after `H` fires, `L` is re-examined and expands once the
    /// conflict is gone. The timing side-condition keeps the reverse case (an
    /// immediate low-priority transition vs. a delayed high-priority one)
    /// unpruned.
    Conflict,
}
