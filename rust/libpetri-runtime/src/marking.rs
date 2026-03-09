use std::any::Any;
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use libpetri_core::place::Place;
use libpetri_core::token::{ErasedToken, Token};

/// Mutable token state of a Petri net during execution.
///
/// Stores type-erased tokens in FIFO queues keyed by place name.
#[derive(Debug, Default)]
pub struct Marking {
    tokens: HashMap<Arc<str>, VecDeque<ErasedToken>>,
}

impl Marking {
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a typed token to a place.
    pub fn add<T: Send + Sync + 'static>(&mut self, place: &Place<T>, token: Token<T>) {
        let erased = ErasedToken::from_typed(&token);
        self.tokens
            .entry(Arc::clone(place.name_arc()))
            .or_default()
            .push_back(erased);
    }

    /// Adds a type-erased token to a place by name.
    pub fn add_erased(&mut self, place_name: &Arc<str>, token: ErasedToken) {
        self.tokens
            .entry(Arc::clone(place_name))
            .or_default()
            .push_back(token);
    }

    /// Returns the number of tokens in a place.
    pub fn count(&self, place_name: &str) -> usize {
        self.tokens.get(place_name).map_or(0, |q| q.len())
    }

    /// Returns true if a place has any tokens.
    pub fn has_tokens(&self, place_name: &str) -> bool {
        self.count(place_name) > 0
    }

    /// Peeks at the first token value in a place without removing it.
    pub fn peek<T: Send + Sync + 'static>(&self, place: &Place<T>) -> Option<Arc<T>> {
        self.tokens
            .get(place.name())
            .and_then(|q| q.front())
            .and_then(|t| t.downcast::<T>().map(|token| token.value_arc()))
    }

    /// Removes and returns the first token from a place (FIFO).
    pub fn remove_first(&mut self, place_name: &str) -> Option<ErasedToken> {
        self.tokens.get_mut(place_name).and_then(|q| q.pop_front())
    }

    /// Removes and returns the first token matching a guard predicate.
    pub fn remove_matching(
        &mut self,
        place_name: &str,
        guard: &dyn Fn(&dyn Any) -> bool,
    ) -> Option<ErasedToken> {
        let queue = self.tokens.get_mut(place_name)?;
        let pos = queue.iter().position(|t| guard(t.value.as_ref()))?;
        queue.remove(pos)
    }

    /// Removes and returns all tokens from a place.
    pub fn remove_all(&mut self, place_name: &str) -> Vec<ErasedToken> {
        self.tokens
            .get_mut(place_name)
            .map_or_else(Vec::new, |q| q.drain(..).collect())
    }

    /// Removes and returns all tokens matching a guard predicate.
    pub fn remove_all_matching(
        &mut self,
        place_name: &str,
        guard: &dyn Fn(&dyn Any) -> bool,
    ) -> Vec<ErasedToken> {
        let queue = match self.tokens.get_mut(place_name) {
            Some(q) => q,
            None => return Vec::new(),
        };
        let mut matched = Vec::new();
        let mut remaining = VecDeque::new();
        for token in queue.drain(..) {
            if guard(token.value.as_ref()) {
                matched.push(token);
            } else {
                remaining.push_back(token);
            }
        }
        *queue = remaining;
        matched
    }

    /// Counts tokens matching a guard predicate.
    pub fn count_matching(&self, place_name: &str, guard: &dyn Fn(&dyn Any) -> bool) -> usize {
        self.tokens
            .get(place_name)
            .map_or(0, |q| q.iter().filter(|t| guard(t.value.as_ref())).count())
    }

    /// Returns the internal token map (for snapshot/event purposes).
    pub fn token_counts(&self) -> HashMap<Arc<str>, usize> {
        self.tokens
            .iter()
            .filter(|(_, q)| !q.is_empty())
            .map(|(k, q)| (Arc::clone(k), q.len()))
            .collect()
    }

    /// Returns all place names that have tokens.
    pub fn non_empty_places(&self) -> Vec<Arc<str>> {
        self.tokens
            .iter()
            .filter(|(_, q)| !q.is_empty())
            .map(|(k, _)| Arc::clone(k))
            .collect()
    }

    /// Returns the raw queue for a place (for executor internal use).
    pub fn queue(&self, place_name: &str) -> Option<&VecDeque<ErasedToken>> {
        self.tokens.get(place_name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_and_count() {
        let p = Place::<i32>::new("p");
        let mut m = Marking::new();
        assert_eq!(m.count("p"), 0);
        assert!(!m.has_tokens("p"));

        m.add(&p, Token::new(1));
        m.add(&p, Token::new(2));
        assert_eq!(m.count("p"), 2);
        assert!(m.has_tokens("p"));
    }

    #[test]
    fn peek() {
        let p = Place::<i32>::new("p");
        let mut m = Marking::new();
        m.add(&p, Token::new(42));
        assert_eq!(*m.peek(&p).unwrap(), 42);
        assert_eq!(m.count("p"), 1); // peek doesn't consume
    }

    #[test]
    fn remove_first_fifo() {
        let p = Place::<i32>::new("p");
        let mut m = Marking::new();
        m.add(&p, Token::at(1, 100));
        m.add(&p, Token::at(2, 200));

        let t = m.remove_first("p").unwrap();
        let recovered = t.downcast::<i32>().unwrap();
        assert_eq!(*recovered.value(), 1);
        assert_eq!(m.count("p"), 1);
    }

    #[test]
    fn remove_all() {
        let p = Place::<i32>::new("p");
        let mut m = Marking::new();
        m.add(&p, Token::new(1));
        m.add(&p, Token::new(2));
        m.add(&p, Token::new(3));

        let tokens = m.remove_all("p");
        assert_eq!(tokens.len(), 3);
        assert_eq!(m.count("p"), 0);
    }

    #[test]
    fn remove_matching() {
        let p = Place::<i32>::new("p");
        let mut m = Marking::new();
        m.add(&p, Token::new(1));
        m.add(&p, Token::new(2));
        m.add(&p, Token::new(3));

        let guard = |v: &dyn Any| v.downcast_ref::<i32>().is_some_and(|n| *n > 1);
        let t = m.remove_matching("p", &guard).unwrap();
        let recovered = t.downcast::<i32>().unwrap();
        assert_eq!(*recovered.value(), 2); // first matching
        assert_eq!(m.count("p"), 2);
    }

    #[test]
    fn token_counts() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<String>::new("p2");
        let mut m = Marking::new();
        m.add(&p1, Token::new(1));
        m.add(&p1, Token::new(2));
        m.add(&p2, Token::new("hello".to_string()));

        let counts = m.token_counts();
        assert_eq!(counts.len(), 2);
        assert_eq!(counts[&Arc::from("p1")], 2);
        assert_eq!(counts[&Arc::from("p2")], 1);
    }
}
