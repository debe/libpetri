/// Safety properties for SMT verification.
#[derive(Debug, Clone)]
pub enum SmtProperty {
    /// No reachable quiescent state strands a token ([VER-002]).
    ///
    /// Violated when a reachable marking is quiescent and holds a token in a
    /// place that is not a declared sink. The empty marking strands nothing and
    /// never violates. This is workflow-net proper completion; for the weaker
    /// "did the net reach a terminal at all", see
    /// [`SmtProperty::TerminatesAtSink`], which inverts on the empty marking.
    DeadlockFree,
    /// Every reachable quiescent state has at least one declared sink marked
    /// ([VER-002]).
    ///
    /// Violated when a reachable marking is quiescent and no declared sink holds
    /// a token. Says nothing about tokens left elsewhere. Meaningful only with at
    /// least one sink declared; with none, every quiescent marking violates
    /// vacuously.
    TerminatesAtSink,
    /// At most one token across the given places in any reachable state.
    MutualExclusion { places: Vec<String> },
    /// A place has at most `bound` tokens in any reachable state.
    PlaceBound { place: String, bound: usize },
    /// The given set of places cannot all be simultaneously marked.
    Unreachable { places: Vec<String> },
    /// A ν-net budget / fork-branch place has at most `bound` tokens in any
    /// reachable state — the [NU-040] bounded-budget decidability lever.
    ///
    /// Encodes identically to [`SmtProperty::PlaceBound`] (a linear-integer count
    /// bound), but names the ν-net intent: the live correlation pool is bounded,
    /// keeping the WSTS finite. The matched-transition over-approximation is sound
    /// for this safety bound — a `Proven` verdict holds for the real net, which
    /// fires strictly fewer joins than the over-approximation.
    BranchPlaceBound { place: String, bound: usize },
    /// Every forked name is eventually joined or dead-lettered: no reachable
    /// *quiescent* (deadlocked) state still holds a token in `pending` ([NU-040]).
    ///
    /// Violated when a reachable marking is both quiescent and has `pending >= 1`
    /// — a stranded correlation group. Encoded as quiescence conjoined with
    /// `pending` non-emptiness, with NO sink clause: a declared sink holding a
    /// token must not excuse a stranded group ([NU-040] AC4).
    JoinedOrDeadLettered { pending: String },
    /// A token count at quiescence ([VER-002]): every reachable quiescent marking holds
    /// between `min` and `max` tokens across `places` (a place named twice counts once).
    ///
    /// Violated by a quiescent marking below `min` while every `waived_by` place is
    /// empty, or above `max` whatever the waivers hold: a halted run ([VER-014]) need not
    /// refund its budget, but never holds more than there is. `max: None` is unbounded
    /// and adds no upper clause. Build it with [`SmtProperty::quiescent_count`], which
    /// rejects `max < min`.
    QuiescentCount {
        places: Vec<String>,
        min: usize,
        max: Option<usize>,
        waived_by: Vec<String>,
    },
}

impl SmtProperty {
    pub fn deadlock_free() -> Self {
        Self::DeadlockFree
    }

    /// Quiescence reaches a declared sink (VER-002). See
    /// [`SmtProperty::TerminatesAtSink`].
    pub fn terminates_at_sink() -> Self {
        Self::TerminatesAtSink
    }

    pub fn mutual_exclusion(places: Vec<String>) -> Self {
        Self::MutualExclusion { places }
    }

    pub fn place_bound(place: impl Into<String>, bound: usize) -> Self {
        Self::PlaceBound {
            place: place.into(),
            bound,
        }
    }

    pub fn unreachable(places: Vec<String>) -> Self {
        Self::Unreachable { places }
    }

    /// Bounded-budget / fork-branch place bound (NU-040). See
    /// [`SmtProperty::BranchPlaceBound`].
    pub fn branch_place_bound(place: impl Into<String>, bound: usize) -> Self {
        Self::BranchPlaceBound {
            place: place.into(),
            bound,
        }
    }

    /// Every forked name is joined or dead-lettered at quiescence (NU-040). See
    /// [`SmtProperty::JoinedOrDeadLettered`].
    pub fn joined_or_dead_lettered(pending: impl Into<String>) -> Self {
        Self::JoinedOrDeadLettered {
            pending: pending.into(),
        }
    }

    /// A token count at quiescence ([VER-002]). See [`SmtProperty::QuiescentCount`].
    ///
    /// ```
    /// use libpetri_verification::property::SmtProperty;
    /// // The budget is back at 2 whenever the net comes to rest, unless it halted.
    /// let refunded = SmtProperty::quiescent_count(vec!["budget".into()], 2, Some(2), vec!["halt".into()]);
    /// assert_eq!(
    ///     refunded.description(),
    ///     "Quiescent count: exactly 2 across {budget}; lower bound waived while {halt} is marked"
    /// );
    /// ```
    ///
    /// # Panics
    /// If `max < min`: a caller's error, reported where the property is built rather
    /// than as a `Violated` verdict about the net ([VER-002] AC9).
    pub fn quiescent_count(
        places: Vec<String>,
        min: usize,
        max: Option<usize>,
        waived_by: Vec<String>,
    ) -> Self {
        if let Some(max) = max {
            assert!(
                max >= min,
                "quiescent_count needs whole bounds with 0 <= min <= max, got {min}..{max}"
            );
        }
        Self::QuiescentCount {
            places,
            min,
            max,
            waived_by,
        }
    }

    pub fn description(&self) -> String {
        match self {
            Self::DeadlockFree => "Deadlock-freedom".into(),
            Self::TerminatesAtSink => "Terminates at a declared sink".into(),
            // The reference names exactly two places; more are listed the same way.
            Self::MutualExclusion { places } => match places.split_last() {
                Some((last, rest)) if !rest.is_empty() => {
                    format!("Mutual exclusion of {} and {last}", rest.join(", "))
                }
                _ => format!("Mutual exclusion of {}", places.join(", ")),
            },
            Self::PlaceBound { place, bound } => format!("Place {place} bounded by {bound}"),
            // In the order given, each place once: the reference takes a set.
            Self::Unreachable { places } => {
                let mut named: Vec<&str> = Vec::with_capacity(places.len());
                for p in places {
                    if !named.contains(&p.as_str()) {
                        named.push(p);
                    }
                }
                format!("Unreachability of marking with tokens in {{{}}}", named.join(", "))
            }
            Self::BranchPlaceBound { place, bound } => {
                format!("Branch place bound (ν-budget): {place} <= {bound}")
            }
            Self::JoinedOrDeadLettered { pending } => {
                format!("Joined-or-dead-lettered: {pending} = 0 at quiescence")
            }
            Self::QuiescentCount {
                places,
                min,
                max,
                waived_by,
            } => {
                let count = format!("Quiescent count: {}", count_across(*min, *max, places));
                if waived_by.is_empty() {
                    count
                } else {
                    format!(
                        "{count}; lower bound waived while {{{}}} is marked",
                        waived_by.join(", ")
                    )
                }
            }
        }
    }
}

/// `exactly 1`, `at most 1`, `at least 2`, `between 1 and 3`, `any number`: a count's
/// bounds (`max: None` unbounded) as every implementation's report words them.
pub(crate) fn count_phrase(min: usize, max: Option<usize>) -> String {
    match max {
        Some(max) if max == min => format!("exactly {min}"),
        None if min == 0 => "any number".to_string(),
        None => format!("at least {min}"),
        Some(max) if min == 0 => format!("at most {max}"),
        Some(max) => format!("between {min} and {max}"),
    }
}

/// `exactly 1 across {a, b}`, places in the order given: the one phrasing of a count
/// clause, for the property description and the [VER-022] contract report.
pub(crate) fn count_across(min: usize, max: Option<usize>, places: &[String]) -> String {
    format!("{} across {{{}}}", count_phrase(min, max), places.join(", "))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every description is byte-identical to the TypeScript reference's
    /// `propertyDescription` for the same property.
    #[test]
    fn property_descriptions() {
        assert_eq!(
            SmtProperty::deadlock_free().description(),
            "Deadlock-freedom"
        );
        assert_eq!(
            SmtProperty::terminates_at_sink().description(),
            "Terminates at a declared sink"
        );
        assert_eq!(
            SmtProperty::mutual_exclusion(vec!["p1".into(), "p2".into()]).description(),
            "Mutual exclusion of p1 and p2"
        );
        assert_eq!(
            SmtProperty::place_bound("p1", 3).description(),
            "Place p1 bounded by 3"
        );
        // Declared order, not sorted; a repeated place is named once.
        assert_eq!(
            SmtProperty::unreachable(vec!["p2".into(), "p1".into(), "p2".into()]).description(),
            "Unreachability of marking with tokens in {p2, p1}"
        );
        assert_eq!(
            SmtProperty::branch_place_bound("budget", 2).description(),
            "Branch place bound (ν-budget): budget <= 2"
        );
        assert_eq!(
            SmtProperty::joined_or_dead_lettered("pending").description(),
            "Joined-or-dead-lettered: pending = 0 at quiescence"
        );
    }

    fn s(v: &[&str]) -> Vec<String> {
        v.iter().map(|x| x.to_string()).collect()
    }

    /// [VER-002] QuiescentCount: the description the TypeScript port pins, and
    /// every wording of a count's bounds.
    #[test]
    fn quiescent_count_describes_itself() {
        assert_eq!(
            SmtProperty::quiescent_count(s(&["budget"]), 2, Some(2), s(&["halt"])).description(),
            "Quiescent count: exactly 2 across {budget}; lower bound waived while {halt} is marked"
        );
        assert_eq!(
            SmtProperty::quiescent_count(s(&["budget", "done"]), 1, None, Vec::new()).description(),
            "Quiescent count: at least 1 across {budget, done}"
        );
        assert_eq!(
            SmtProperty::quiescent_count(s(&["a"]), 0, Some(3), s(&["h", "k"])).description(),
            "Quiescent count: at most 3 across {a}; lower bound waived while {h, k} is marked"
        );
        assert_eq!(count_phrase(1, Some(3)), "between 1 and 3");
        assert_eq!(count_phrase(0, None), "any number");
        assert_eq!(count_phrase(0, Some(0)), "exactly 0");
        assert_eq!(count_across(1, Some(1), &s(&["a", "b"])), "exactly 1 across {a, b}");
    }

    /// [VER-002] AC9: a `max` below `min` is rejected where it is built.
    #[test]
    #[should_panic(expected = "0 <= min <= max, got 2..1")]
    fn quiescent_count_rejects_max_below_min() {
        SmtProperty::quiescent_count(s(&["budget"]), 2, Some(1), Vec::new());
    }

    /// An unbounded `max` never conflicts with `min`, however large.
    #[test]
    fn quiescent_count_accepts_an_unbounded_max() {
        let prop = SmtProperty::quiescent_count(s(&["budget"]), usize::MAX, None, Vec::new());
        assert!(matches!(prop, SmtProperty::QuiescentCount { max: None, .. }));
    }
}
