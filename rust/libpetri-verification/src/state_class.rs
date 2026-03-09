use crate::dbm::Dbm;
use crate::marking_state::MarkingState;

/// A state class: pair of (M: marking, D: firing domain DBM).
///
/// Provides a finite abstraction of the infinite Time Petri Net state space.
#[derive(Debug, Clone)]
pub struct StateClass {
    pub marking: MarkingState,
    pub dbm: Dbm,
    pub enabled_transitions: Vec<String>,
}

impl StateClass {
    pub fn new(marking: MarkingState, dbm: Dbm, enabled_transitions: Vec<String>) -> Self {
        Self {
            marking,
            dbm,
            enabled_transitions,
        }
    }

    /// Returns true if the firing domain is empty.
    pub fn is_empty(&self) -> bool {
        self.dbm.is_empty()
    }

    /// Returns whether transition at the given clock index can fire.
    pub fn can_fire(&self, clock_idx: usize) -> bool {
        self.dbm.can_fire(clock_idx)
    }

    /// Looks up a transition clock index by name.
    pub fn transition_index(&self, name: &str) -> Option<usize> {
        self.enabled_transitions.iter().position(|n| n == name)
    }

    /// Generates a canonical key for deduplication.
    pub fn canonical_key(&self) -> String {
        format!(
            "{}|{}",
            self.marking.canonical_key(),
            self.dbm.canonical_string()
        )
    }
}

impl PartialEq for StateClass {
    fn eq(&self, other: &Self) -> bool {
        self.marking == other.marking && self.dbm == other.dbm
    }
}

impl Eq for StateClass {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;

    #[test]
    fn state_class_basic() {
        let marking = MarkingStateBuilder::new().tokens("p1", 1).build();
        let dbm = Dbm::create(vec!["t1".to_string()], &[0.0], &[f64::INFINITY]);
        let sc = StateClass::new(marking, dbm, vec!["t1".to_string()]);

        assert!(!sc.is_empty());
        assert_eq!(sc.transition_index("t1"), Some(0));
        assert_eq!(sc.transition_index("nonexistent"), None);
    }

    #[test]
    fn state_class_canonical_key() {
        let marking = MarkingStateBuilder::new().tokens("p1", 1).build();
        let dbm = Dbm::create(vec!["t1".to_string()], &[0.0], &[10.0]);
        let sc = StateClass::new(marking, dbm, vec!["t1".to_string()]);

        let key = sc.canonical_key();
        assert!(!key.is_empty());
    }

    #[test]
    fn state_class_equality() {
        let m1 = MarkingStateBuilder::new().tokens("p1", 1).build();
        let m2 = MarkingStateBuilder::new().tokens("p1", 1).build();
        let d1 = Dbm::create(vec!["t1".to_string()], &[0.0], &[10.0]);
        let d2 = Dbm::create(vec!["t1".to_string()], &[0.0], &[10.0]);

        let sc1 = StateClass::new(m1, d1, vec!["t1".to_string()]);
        let sc2 = StateClass::new(m2, d2, vec!["t1".to_string()]);

        assert_eq!(sc1, sc2);
    }
}
