use std::collections::HashMap;
use std::fmt::{self, Write as _};
use std::sync::Arc;

/// Immutable snapshot of a Petri net marking for state space analysis: token counts by
/// place name, non-zero counts only.
///
/// [`MarkingState::places`] lists a [`MarkingStateBuilder`] marking in the builder's
/// first-mention order, as the reference's `Map`-backed marking does (the order an
/// open-net port trace names places in, [VER-022]), and any other marking in code-point
/// order. The order is not part of identity: equal counts make equal markings with the
/// same [`MarkingState::canonical_key`].
///
/// # Representation
///
/// A name-sorted vector whose `Arc<str>` names are shared with every marking derived from
/// this one. The state-class graph clones a marking per successor and keys every class by
/// it, so those operations are the cheap ones:
///
/// | operation            | cost (k places, names of length L)                        |
/// |----------------------|-----------------------------------------------------------|
/// | `count`              | O(L log k), binary search                                 |
/// | set (crate-internal) | O(L log k + k), one shift; one allocation for a new name  |
/// | `places`             | O(k)                                                      |
/// | `clone`              | O(k), one allocation, no string copied                    |
/// | `canonical_key`      | O(k L), already in key order, no sort                     |
#[derive(Clone)]
pub struct MarkingState {
    /// Places with a non-zero count, sorted by name (code-point order).
    entries: Vec<(Arc<str>, usize)>,
    /// The builder's first-mention order as indices into `entries`, or `None` when that
    /// order is code-point order or the marking has none.
    order: Option<Arc<[u32]>>,
}

impl MarkingState {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            order: None,
        }
    }

    /// A marking from a map of counts, zero counts dropped. A `HashMap` has no order, so
    /// the places are listed in code-point order.
    pub fn from_map(tokens: HashMap<String, usize>) -> Self {
        let mut entries: Vec<(Arc<str>, usize)> = tokens
            .into_iter()
            .filter(|(_, c)| *c > 0)
            .map(|(p, c)| (Arc::from(p), c))
            .collect();
        entries.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        Self {
            entries,
            order: None,
        }
    }

    /// A marking whose places are listed in the order given; `first_seen` holds distinct
    /// names with non-zero counts.
    fn from_first_seen(first_seen: Vec<(String, usize)>) -> Self {
        let named: Vec<(Arc<str>, usize)> =
            first_seen.into_iter().map(|(p, c)| (Arc::from(p), c)).collect();
        let mut ranked: Vec<u32> = (0..named.len() as u32).collect();
        ranked.sort_unstable_by(|&a, &b| named[a as usize].0.cmp(&named[b as usize].0));
        if ranked.iter().enumerate().all(|(at, &i)| at as u32 == i) {
            return Self {
                entries: named,
                order: None,
            };
        }
        let mut order = vec![0u32; named.len()];
        for (at, &i) in ranked.iter().enumerate() {
            order[i as usize] = at as u32;
        }
        Self {
            entries: ranked.iter().map(|&i| named[i as usize].clone()).collect(),
            order: Some(Arc::from(order)),
        }
    }

    /// A copy for a firing to edit with [`MarkingState::set`]. A derived marking has no
    /// builder order, and room for the one place a firing typically adds.
    pub(crate) fn derived(&self) -> Self {
        let mut entries = Vec::with_capacity(self.entries.len() + 1);
        entries.extend(self.entries.iter().cloned());
        Self {
            entries,
            order: None,
        }
    }

    /// Sets the count of `place`; `0` removes it. Drops the builder order, if any.
    pub(crate) fn set(&mut self, place: &str, count: usize) {
        self.order = None;
        match self.position(place) {
            Ok(i) if count == 0 => {
                self.entries.remove(i);
            }
            Ok(i) => self.entries[i].1 = count,
            Err(_) if count == 0 => {}
            Err(i) => self.entries.insert(i, (Arc::from(place), count)),
        }
    }

    fn position(&self, place: &str) -> Result<usize, usize> {
        self.entries.binary_search_by(|(p, _)| (**p).cmp(place))
    }

    /// Returns the token count for a place.
    pub fn count(&self, place: &str) -> usize {
        self.position(place).map_or(0, |i| self.entries[i].1)
    }

    /// Returns all places with non-zero counts: in the order the builder first saw them,
    /// or in code-point order for a marking that has no builder order.
    pub fn places(&self) -> impl Iterator<Item = (&str, usize)> {
        let ordered = self.order.as_deref().map(|order| {
            order.iter().map(|&i| {
                let (p, c) = &self.entries[i as usize];
                (&**p, *c)
            })
        });
        let sorted = self
            .order
            .is_none()
            .then(|| self.entries.iter().map(|(p, c)| (&**p, *c)));
        ordered.into_iter().flatten().chain(sorted.into_iter().flatten())
    }

    /// Returns true if the marking is empty (no tokens anywhere).
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Returns the total number of tokens across all places.
    pub fn total_tokens(&self) -> usize {
        self.entries.iter().map(|(_, c)| c).sum()
    }

    /// Returns true if this marking has tokens in any of the named places.
    pub fn has_tokens_in_any(&self, place_names: &[&str]) -> bool {
        place_names.iter().any(|name| self.count(name) > 0)
    }

    /// Generates a canonical key for deduplication: `name:count` in code-point order,
    /// comma-separated.
    pub fn canonical_key(&self) -> String {
        let mut key = String::with_capacity(self.entries.iter().map(|(p, _)| p.len() + 4).sum());
        for (i, (p, c)) in self.entries.iter().enumerate() {
            if i > 0 {
                key.push(',');
            }
            let _ = write!(key, "{p}:{c}");
        }
        key
    }
}

impl Default for MarkingState {
    fn default() -> Self {
        Self::new()
    }
}

/// Equal counts on the same places; the order the places are listed in is not compared.
impl PartialEq for MarkingState {
    fn eq(&self, other: &Self) -> bool {
        self.entries == other.entries
    }
}

impl Eq for MarkingState {}

impl fmt::Debug for MarkingState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct Tokens<'a>(&'a MarkingState);
        impl fmt::Debug for Tokens<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_map().entries(self.0.places()).finish()
            }
        }
        f.debug_struct("MarkingState").field("tokens", &Tokens(self)).finish()
    }
}

/// Builder for constructing MarkingState instances.
///
/// Remembers the order places are first given a count. A place set to `0` is removed, and
/// counts from its next mention as a new place, as deleting a key from a JS `Map` does.
pub struct MarkingStateBuilder {
    /// Every place mentioned, in first-mention order; a removed place keeps a zero here.
    first_seen: Vec<(String, usize)>,
    /// The live index into `first_seen` of each place currently present.
    index: HashMap<String, usize>,
}

impl MarkingStateBuilder {
    pub fn new() -> Self {
        Self {
            first_seen: Vec::new(),
            index: HashMap::new(),
        }
    }

    pub fn tokens(mut self, place: impl Into<String>, count: usize) -> Self {
        let place = place.into();
        if count == 0 {
            if let Some(i) = self.index.remove(&place) {
                self.first_seen[i].1 = 0;
            }
        } else if let Some(&i) = self.index.get(&place) {
            self.first_seen[i].1 = count;
        } else {
            self.push(place, count);
        }
        self
    }

    pub fn add_tokens(mut self, place: impl Into<String>, count: usize) -> Self {
        let place = place.into();
        match self.index.get(&place) {
            Some(&i) => self.first_seen[i].1 += count,
            None if count > 0 => self.push(place, count),
            None => {}
        }
        self
    }

    fn push(&mut self, place: String, count: usize) {
        self.index.insert(place.clone(), self.first_seen.len());
        self.first_seen.push((place, count));
    }

    pub fn build(self) -> MarkingState {
        let mut first_seen = self.first_seen;
        first_seen.retain(|(_, c)| *c > 0);
        MarkingState::from_first_seen(first_seen)
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
    fn order(m: &MarkingState) -> Vec<(&str, usize)> {
        m.places().collect()
    }

    /// [VER-022]: the builder's first-mention order is what `places` lists, as the
    /// reference's `Map`-backed marking does.
    #[test]
    fn places_follow_the_builder_order() {
        let ms = MarkingStateBuilder::new()
            .tokens("zeta", 1)
            .add_tokens("alpha", 2)
            .tokens("mid", 3)
            .tokens("zeta", 4)
            .build();
        assert_eq!(order(&ms), vec![("zeta", 4), ("alpha", 2), ("mid", 3)]);
        assert_eq!(ms.canonical_key(), "alpha:2,mid:3,zeta:4");
    }

    /// A place set to zero is removed, and counts from its next mention as a new place.
    #[test]
    fn a_removed_place_rejoins_at_the_end() {
        let ms = MarkingStateBuilder::new()
            .tokens("b", 1)
            .tokens("a", 1)
            .tokens("b", 0)
            .add_tokens("c", 0)
            .add_tokens("b", 2)
            .build();
        assert_eq!(order(&ms), vec![("a", 1), ("b", 2)]);
    }

    #[test]
    fn equality_and_key_ignore_the_order() {
        let ba = MarkingStateBuilder::new().tokens("b", 1).tokens("a", 2).build();
        let ab = MarkingStateBuilder::new().tokens("a", 2).tokens("b", 1).build();
        assert_eq!(order(&ba), vec![("b", 1), ("a", 2)]);
        assert_eq!(ba, ab);
        let from_map = MarkingState::from_map(HashMap::from([("b".to_string(), 1), ("a".to_string(), 2)]));
        assert_eq!(from_map, ba);
        assert_eq!(order(&from_map), vec![("a", 2), ("b", 1)]);
        assert_eq!(format!("{ba:?}"), r#"MarkingState { tokens: {"b": 1, "a": 2} }"#);
    }

    /// A marking derived by firing has no builder order: its places are in code-point order.
    #[test]
    fn a_derived_marking_is_in_code_point_order() {
        let initial = MarkingStateBuilder::new().tokens("z", 1).tokens("m", 1).build();
        let mut next = initial.derived();
        assert_eq!(order(&next), vec![("m", 1), ("z", 1)]);
        next.set("z", 0);
        next.set("a", 3);
        next.set("m", 2);
        next.set("absent", 0);
        assert_eq!(order(&next), vec![("a", 3), ("m", 2)]);
        assert_eq!(next.count("a"), 3);
        assert_eq!(next.count("z"), 0);
        assert_eq!(next.total_tokens(), 5);
        assert_eq!(next.canonical_key(), "a:3,m:2");
        assert_eq!(order(&initial), vec![("z", 1), ("m", 1)]);
    }
}
