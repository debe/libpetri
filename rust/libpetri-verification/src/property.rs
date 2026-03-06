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
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn property_descriptions() {
        assert_eq!(SmtProperty::deadlock_free().description(), "Deadlock freedom");
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
    }
}
