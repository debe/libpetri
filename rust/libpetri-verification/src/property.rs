/// Safety properties for SMT verification.
#[derive(Debug, Clone)]
pub enum SmtProperty {
    /// No reachable deadlock state (every reachable state has an enabled transition).
    DeadlockFree,
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
    /// — a stranded correlation group. Encoded as the deadlock predicate
    /// conjoined with `pending` non-emptiness.
    JoinedOrDeadLettered { pending: String },
}

impl SmtProperty {
    pub fn deadlock_free() -> Self {
        Self::DeadlockFree
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

    pub fn description(&self) -> String {
        match self {
            Self::DeadlockFree => "Deadlock freedom".into(),
            Self::MutualExclusion { places } => {
                format!("Mutual exclusion: {}", places.join(", "))
            }
            Self::PlaceBound { place, bound } => format!("Place bound: {place} <= {bound}"),
            Self::Unreachable { places } => {
                format!("Unreachable: {}", places.join(" & "))
            }
            Self::BranchPlaceBound { place, bound } => {
                format!("Branch place bound (ν-budget): {place} <= {bound}")
            }
            Self::JoinedOrDeadLettered { pending } => {
                format!("Joined-or-dead-lettered: {pending} = 0 at quiescence")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn property_descriptions() {
        assert_eq!(
            SmtProperty::deadlock_free().description(),
            "Deadlock freedom"
        );
        assert_eq!(
            SmtProperty::mutual_exclusion(vec!["p1".into(), "p2".into()]).description(),
            "Mutual exclusion: p1, p2"
        );
        assert_eq!(
            SmtProperty::place_bound("p1", 3).description(),
            "Place bound: p1 <= 3"
        );
        assert_eq!(
            SmtProperty::unreachable(vec!["p1".into(), "p2".into()]).description(),
            "Unreachable: p1 & p2"
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
}
