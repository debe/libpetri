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
    /// No two of the listed places are marked at once, in any reachable state
    /// ([VER-002]): violated iff some two entries of the list, at different
    /// positions, both hold a token. Two places is the spec's
    /// `MutualExclusion(p1, p2)`; a longer list is the pairwise conjunction of
    /// those, the same on every route. A place listed twice pairs with itself, so
    /// any token there violates, as `MutualExclusion(p, p)` does; a list of fewer
    /// than two entries is never violated.
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
    /// Name alignment ([NU-055]): in every reachable marking, the places of `places`
    /// together hold at most one distinct name. An empty place imposes nothing, but a
    /// place holding two names violates it whatever the others hold, so the singleton
    /// `name_aligned(["p"])` says that `p` never holds two names. `#[non_exhaustive]`:
    /// build it outside this crate with [`SmtProperty::name_aligned`], which keeps each
    /// place once, at its first occurrence in the caller's order, and rejects an empty
    /// list; the order changes no verdict, only the description and which place a reason
    /// names.
    ///
    /// Every place must be a coloured place of the fragment Route B classifies for the
    /// call (a match key, a declared carrier or a relay target): an uncoloured place
    /// carries no name, so the verdict on one is `Unknown`, never `Proven`. Decided only
    /// by Route B, the name-partition state-class graph ([NU-050]); every other route
    /// gives it no verdict.
    #[non_exhaustive]
    NameAligned { places: Vec<String> },
    /// Quiescent name alignment ([NU-055]): the predicate of
    /// [`SmtProperty::NameAligned`], read only in the reachable quiescent markings (the
    /// reap-aware quiescence of [VER-002]). Like [`SmtProperty::JoinedOrDeadLettered`]
    /// it carries no sink clause. `#[non_exhaustive]` for the same reason: build it
    /// outside this crate with [`SmtProperty::quiescent_name_aligned`].
    #[non_exhaustive]
    QuiescentNameAligned { places: Vec<String> },
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

    /// Pairwise mutual exclusion over `places` ([VER-002]). See
    /// [`SmtProperty::MutualExclusion`].
    pub fn mutual_exclusion(places: Vec<String>) -> Self {
        Self::MutualExclusion { places }
    }

    /// The parts a linear route proves one by one: a [`SmtProperty::MutualExclusion`]
    /// over three or more entries is violated iff one of its pairs is, so it splits
    /// into one two-place property per pair (positions `i < j`, in list order); every
    /// other property is its own single part. A linear demand ([VER-015]) is a
    /// conjunction, and the pairwise property is a disjunction of them.
    pub fn linear_parts(&self) -> Vec<SmtProperty> {
        match self {
            Self::MutualExclusion { places } if places.len() > 2 => mutex_pairs(places.len())
                .map(|(i, j)| Self::MutualExclusion {
                    places: vec![places[i].clone(), places[j].clone()],
                })
                .collect(),
            other => vec![other.clone()],
        }
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

    /// Name alignment of `places` in every reachable marking ([NU-055]). See
    /// [`SmtProperty::NameAligned`].
    ///
    /// ```
    /// use libpetri_verification::property::SmtProperty;
    /// // box and list never hold two different names between them; a repeat counts once.
    /// let aligned = SmtProperty::name_aligned(["box", "list", "box"]);
    /// assert_eq!(aligned.description(), "Name alignment of box and list");
    /// // reply never holds two names.
    /// assert_eq!(SmtProperty::name_aligned(["reply"]).description(), "Name alignment of reply");
    /// ```
    ///
    /// # Panics
    /// If `places` is empty: a caller's error, reported where the property is built
    /// rather than as a verdict ([NU-055]).
    pub fn name_aligned(places: impl IntoIterator<Item = impl Into<String>>) -> Self {
        Self::NameAligned {
            places: alignment_places("name_aligned", places),
        }
    }

    /// Name alignment of `places` at quiescence ([NU-055]). See
    /// [`SmtProperty::QuiescentNameAligned`].
    ///
    /// # Panics
    /// If `places` is empty, as [`SmtProperty::name_aligned`].
    pub fn quiescent_name_aligned(places: impl IntoIterator<Item = impl Into<String>>) -> Self {
        Self::QuiescentNameAligned {
            places: alignment_places("quiescent_name_aligned", places),
        }
    }

    /// Whether this is [`SmtProperty::NameAligned`] or
    /// [`SmtProperty::QuiescentNameAligned`] ([NU-055]): the two properties only Route B
    /// decides.
    pub(crate) fn is_name_alignment(&self) -> bool {
        matches!(self, Self::NameAligned { .. } | Self::QuiescentNameAligned { .. })
    }

    /// Why a route other than Route B gives this name-alignment property no verdict
    /// ([NU-055] AC4): the name-blind routes do not see names. Also the closing clause
    /// of a Route B decline, after which nothing else decides it.
    pub(crate) fn route_b_only_reason(&self) -> String {
        format!(
            "{} is decided only by the name-partition state-class graph (NU-055, Route B)",
            self.description()
        )
    }

    pub fn description(&self) -> String {
        match self {
            Self::DeadlockFree => "Deadlock-freedom".into(),
            Self::TerminatesAtSink => "Terminates at a declared sink".into(),
            // The reference names exactly two places; more are listed the same way.
            Self::MutualExclusion { places } => format!("Mutual exclusion of {}", and_list(places)),
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
            Self::NameAligned { places } => format!("Name alignment of {}", and_list(places)),
            Self::QuiescentNameAligned { places } => {
                format!("Quiescent name alignment of {}", and_list(places))
            }
        }
    }
}

/// The list `S` of a name-alignment property ([NU-055]): `places` with each name kept
/// once, at its first occurrence. An empty list is the caller's error, not a verdict.
fn alignment_places(constructor: &str, places: impl IntoIterator<Item = impl Into<String>>) -> Vec<String> {
    let mut kept: Vec<String> = Vec::new();
    for p in places {
        let p = p.into();
        if !kept.contains(&p) {
            kept.push(p);
        }
    }
    assert!(!kept.is_empty(), "{constructor} needs at least one place");
    kept
}

/// `a`, `a and b`, `a, b and c`: the places of a description in the order given, `, `
/// between them and ` and ` before the last.
fn and_list(places: &[String]) -> String {
    match places.split_last() {
        Some((last, rest)) if !rest.is_empty() => format!("{} and {last}", rest.join(", ")),
        _ => places.join(", "),
    }
}

/// The position pairs `(i, j)`, `i < j < n`, in lexicographic order: the pairs of a
/// [`SmtProperty::MutualExclusion`] list, one of which must be marked on both sides for
/// a violation ([VER-002]). Empty for `n < 2`.
pub(crate) fn mutex_pairs(n: usize) -> impl Iterator<Item = (usize, usize)> {
    (0..n).flat_map(move |i| (i + 1..n).map(move |j| (i, j)))
}

/// Whether some pair of `marked` (one flag per listed entry) is marked on both sides:
/// the pairwise [`SmtProperty::MutualExclusion`] violation, as every route reads it.
pub(crate) fn two_marked(marked: impl IntoIterator<Item = bool>) -> bool {
    marked.into_iter().filter(|&m| m).nth(1).is_some()
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

    /// [NU-055]: the two name-alignment descriptions for one, two and three places, byte
    /// for byte those of every other implementation, and the reason the name-blind routes
    /// give.
    #[test]
    fn nu055_name_alignment_describes_itself() {
        assert_eq!(SmtProperty::name_aligned(["box"]).description(), "Name alignment of box");
        assert_eq!(
            SmtProperty::name_aligned(["box", "list"]).description(),
            "Name alignment of box and list"
        );
        assert_eq!(
            SmtProperty::name_aligned(["box", "staged", "list"]).description(),
            "Name alignment of box, staged and list"
        );
        assert_eq!(
            SmtProperty::quiescent_name_aligned(["box"]).description(),
            "Quiescent name alignment of box"
        );
        assert_eq!(
            SmtProperty::quiescent_name_aligned(["box", "list"]).description(),
            "Quiescent name alignment of box and list"
        );
        assert_eq!(
            SmtProperty::quiescent_name_aligned(["box", "staged", "list"]).description(),
            "Quiescent name alignment of box, staged and list"
        );
        assert!(SmtProperty::name_aligned(["box"]).is_name_alignment());
        assert!(SmtProperty::quiescent_name_aligned(["box", "list"]).is_name_alignment());
        assert!(!SmtProperty::joined_or_dead_lettered("box").is_name_alignment());
        assert_eq!(
            SmtProperty::name_aligned(["box", "list"]).route_b_only_reason(),
            "Name alignment of box and list is decided only by the name-partition state-class \
             graph (NU-055, Route B)"
        );
    }

    /// [NU-055] AC7: a repeated place counts once, at its first occurrence, in both
    /// properties, whether the names come as `&str` or `String`.
    #[test]
    fn nu055_a_repeated_place_counts_once_at_its_first_occurrence() {
        let owned = s(&["box", "list", "box", "list"]);
        for prop in [SmtProperty::name_aligned(&owned), SmtProperty::quiescent_name_aligned(owned.clone())] {
            let (SmtProperty::NameAligned { places } | SmtProperty::QuiescentNameAligned { places }) = &prop else {
                panic!("{prop:?}");
            };
            assert_eq!(places, &s(&["box", "list"]));
        }
        assert_eq!(
            SmtProperty::name_aligned(["list", "box", "list"]).description(),
            "Name alignment of list and box"
        );
        assert_eq!(SmtProperty::name_aligned(["box", "box"]).description(), "Name alignment of box");
    }

    /// [NU-055] AC7: an empty `S` is rejected where it is built.
    #[test]
    #[should_panic(expected = "name_aligned needs at least one place")]
    fn nu055_name_aligned_rejects_an_empty_list() {
        SmtProperty::name_aligned(Vec::<String>::new());
    }

    /// [NU-055] AC7: the quiescent form rejects an empty `S` too.
    #[test]
    #[should_panic(expected = "quiescent_name_aligned needs at least one place")]
    fn nu055_quiescent_name_aligned_rejects_an_empty_list() {
        SmtProperty::quiescent_name_aligned(std::iter::empty::<&str>());
    }

    /// An unbounded `max` never conflicts with `min`, however large.
    #[test]
    fn quiescent_count_accepts_an_unbounded_max() {
        let prop = SmtProperty::quiescent_count(s(&["budget"]), usize::MAX, None, Vec::new());
        assert!(matches!(prop, SmtProperty::QuiescentCount { max: None, .. }));
    }
}
