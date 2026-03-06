use std::collections::HashMap;

/// Immutable snapshot of a Petri net marking for state space analysis.
///
/// Maps places by name to integer token counts. Only stores places with count > 0.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MarkingState {
    tokens: HashMap<String, usize>,
}

impl MarkingState {
    pub fn new() -> Self {
        Self {
            tokens: HashMap::new(),
        }
    }

    pub fn from_map(tokens: HashMap<String, usize>) -> Self {
        let tokens = tokens.into_iter().filter(|(_, c)| *c > 0).collect();
        Self { tokens }
    }

    /// Returns the token count for a place.
    pub fn count(&self, place: &str) -> usize {
        self.tokens.get(place).copied().unwrap_or(0)
    }

    /// Returns all places with non-zero counts.
    pub fn places(&self) -> impl Iterator<Item = (&str, usize)> {
        self.tokens.iter().map(|(k, v)| (k.as_str(), *v))
    }

    /// Returns true if the marking is empty (no tokens anywhere).
    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    /// Returns the total number of tokens across all places.
    pub fn total_tokens(&self) -> usize {
        self.tokens.values().sum()
    }

    /// Returns true if this marking has tokens in any of the named places.
    pub fn has_tokens_in_any(&self, place_names: &[&str]) -> bool {
        place_names.iter().any(|name| self.count(name) > 0)
    }

    /// Generates a canonical key for deduplication.
    pub fn canonical_key(&self) -> String {
        let mut entries: Vec<_> = self.tokens.iter().collect();
        entries.sort_by_key(|(k, _)| k.as_str());
        entries
            .iter()
            .map(|(k, v)| format!("{k}:{v}"))
            .collect::<Vec<_>>()
            .join(",")
    }
}

impl Default for MarkingState {
    fn default() -> Self {
        Self::new()
    }
}

/// Builder for constructing MarkingState instances.
pub struct MarkingStateBuilder {
    tokens: HashMap<String, usize>,
}

impl MarkingStateBuilder {
    pub fn new() -> Self {
        Self {
            tokens: HashMap::new(),
        }
    }

    pub fn tokens(mut self, place: impl Into<String>, count: usize) -> Self {
        let key = place.into();
        if count > 0 {
            self.tokens.insert(key, count);
        } else {
            self.tokens.remove(&key);
        }
        self
    }

    pub fn add_tokens(mut self, place: impl Into<String>, count: usize) -> Self {
        let entry = self.tokens.entry(place.into()).or_insert(0);
        *entry += count;
        self
    }

    pub fn build(self) -> MarkingState {
        MarkingState::from_map(self.tokens)
    }
}

impl Default for MarkingStateBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn marking_state_basics() {
        let ms = MarkingStateBuilder::new()
            .tokens("p1", 2)
            .tokens("p2", 1)
            .build();

        assert_eq!(ms.count("p1"), 2);
        assert_eq!(ms.count("p2"), 1);
        assert_eq!(ms.count("p3"), 0);
        assert_eq!(ms.total_tokens(), 3);
        assert!(!ms.is_empty());
    }

    #[test]
    fn canonical_key_deterministic() {
        let ms1 = MarkingStateBuilder::new()
            .tokens("b", 1)
            .tokens("a", 2)
            .build();
        let ms2 = MarkingStateBuilder::new()
            .tokens("a", 2)
            .tokens("b", 1)
            .build();
        assert_eq!(ms1.canonical_key(), ms2.canonical_key());
    }

    #[test]
    fn empty_marking() {
        let ms = MarkingState::new();
        assert!(ms.is_empty());
        assert_eq!(ms.total_tokens(), 0);
        assert_eq!(ms.canonical_key(), "");
    }

    #[test]
    fn zero_count_filtered() {
        let ms = MarkingStateBuilder::new()
            .tokens("p1", 0)
            .tokens("p2", 1)
            .build();
        assert_eq!(ms.count("p1"), 0);
        assert_eq!(ms.count("p2"), 1);
        assert_eq!(ms.total_tokens(), 1);
    }

    #[test]
    fn add_tokens_accumulates() {
        let ms = MarkingStateBuilder::new()
            .add_tokens("p1", 2)
            .add_tokens("p1", 3)
            .build();
        assert_eq!(ms.count("p1"), 5);
    }

    #[test]
    fn equality() {
        let ms1 = MarkingStateBuilder::new().tokens("p", 2).build();
        let ms2 = MarkingStateBuilder::new().tokens("p", 2).build();
        assert_eq!(ms1, ms2);
    }

    #[test]
    fn inequality_different_count() {
        let ms1 = MarkingStateBuilder::new().tokens("p", 1).build();
        let ms2 = MarkingStateBuilder::new().tokens("p", 2).build();
        assert_ne!(ms1, ms2);
    }
}
