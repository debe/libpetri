use std::any::Any;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::sync::Arc;

use libpetri_core::place::Place;
use libpetri_core::token::{ErasedToken, Token};

/// \[CORE-073\] The normative snapshot form: place **name** → the place's
/// tokens in **FIFO order** (\[CORE-013\]).
///
/// Keyed by name rather than by [`Place`] deliberately: \[CORE-073\] AC#7
/// requires a snapshot to retain a place the receiving net does not declare,
/// and there is no `Place` to construct for a name the net has never heard
/// of. `Marking` has always been keyed this way, so retention is structural
/// rather than something to remember.
///
/// A `BTreeMap` rather than a `HashMap` so the place order is **deterministic
/// across runs**. The form is a mapping and only the per-place sequence is
/// ordered, so hash order would not violate the requirement — but the moment
/// a host serializes a snapshot and diffs, hashes or content-addresses it,
/// unstable key order bites, and ordering it costs nothing here.
///
/// The entry is [`ErasedToken`], which already *is* `(value, created_at)` —
/// no parallel "snapshot entry" type, matching Java and TypeScript, which
/// reuse their `Token` for the same reason. Note it carries one extra field,
/// `value_type_name`, which is engine metadata outside the normative form
/// and does not survive a round-trip through a binding.
///
/// **Structural, not serialized.** No codec is imposed and token values need
/// not be serializable: the value stays an `Arc<dyn Any + Send + Sync>`, so
/// a closure, a native handle or a host object round-trips in-process
/// untouched (\[CORE-073\] AC#8).
pub type MarkingSnapshot = BTreeMap<Arc<str>, Vec<ErasedToken>>;

/// \[ENV-014\] AC5/AC6 — what a mid-execution snapshot returns.
///
/// The marking **and** whether an action was in flight when it was taken,
/// as one value. Deliberately not a separately-queryable flag: that would be
/// read at a different instant than the marking, which is the race AC5
/// exists to close.
///
/// # Why the flag matters
///
/// Nothing suspends the run to serve a snapshot. An action may be **in
/// flight** — having already consumed its inputs (\[EXEC-031\]) and not yet
/// produced its outputs — so those tokens are in *neither* place at the
/// instant you observe them. The marking is a perfectly valid
/// **observation**; it is not a valid **restore point**, because restoring
/// it loses that work silently.
///
/// # External events
///
/// The flag's cross-language meaning is *work in flight: an action, or an
/// accepted but un-injected external event*. In this implementation the
/// second half is never true: an inject and a snapshot request travel the
/// same FIFO signal channel, and the executor applies an inject to the
/// marking the moment it receives it. Every event accepted before the
/// snapshot was requested is therefore already **in** the marking, and the
/// flag reduces to "an action was in flight".
///
/// `action_in_flight` is singular and boolean on purpose. A count would
/// invite the reader to treat it as a live gauge of how many are running
/// now, which is exactly the racy reading AC5 forbids. This is a fact about
/// the instant the snapshot was taken, not a measurement you can re-check.
#[derive(Debug, Clone)]
pub struct SnapshotResult {
    /// The captured marking, in the \[CORE-073\] normative form.
    pub marking: MarkingSnapshot,
    /// Work in flight: an action, or an accepted but un-injected external
    /// event (the latter cannot occur here — see *External events* above).
    /// True makes the marking an observation rather than a restore point.
    pub action_in_flight: bool,
}

impl SnapshotResult {
    /// True when nothing was in flight, so the marking is safe to restore
    /// from. Sugar for `!action_in_flight`, named for the question a caller
    /// is actually asking.
    pub fn is_restore_point(&self) -> bool {
        !self.action_in_flight
    }
}

/// Mutable token state of a Petri net during execution.
///
/// Stores type-erased tokens in FIFO queues keyed by place name. `Clone` is
/// supported so an executor can hand out an owned copy through a oneshot
/// channel (used by [`ExecutorHandle::snapshot`](crate::ExecutorHandle::snapshot));
/// each cloned token clones its underlying `Arc<dyn Any + Send + Sync>`, so
/// shared payloads are not deep-copied.
///
/// `Clone` is an **in-process copy, not the snapshot form** — see
/// [`snapshot`](Self::snapshot) / [`from_snapshot`](Self::from_snapshot) for
/// \[CORE-073\]. The two coexist; neither replaces the other.
#[derive(Debug, Default, Clone)]
pub struct Marking {
    tokens: HashMap<Arc<str>, VecDeque<ErasedToken>>,
}

impl Marking {
    pub fn new() -> Self {
        Self::default()
    }

    /// \[CORE-073\] Captures this marking in the normative snapshot form.
    ///
    /// Every token's `value` and `created_at` are preserved, and each
    /// place's sequence is its FIFO order, so a restore reproduces which
    /// token the next firing consumes (\[CORE-013\], AC#6).
    ///
    /// Empty places are omitted. \[CORE-073\] permits either, and requires
    /// only that omitted and present-but-empty restore identically —
    /// [`from_snapshot`](Self::from_snapshot) accepts both.
    ///
    /// Restoring does **not** resume a partially elapsed firing interval: a
    /// restored marking seeds a new execution whose timing clocks all start
    /// fresh (\[TIME-010\] / \[TIME-011\]). That is safe for `delayed` /
    /// `exact` lower bounds and **unsafe for `deadline` / `window` upper
    /// bounds**, which receive a fresh full budget — and restoring more often
    /// than a `Delayed(d)` interval means that transition never fires at all.
    /// Restore is sound as an *occasional* operation, not as a scheduler's
    /// routine park-and-resume.
    pub fn snapshot(&self) -> MarkingSnapshot {
        self.tokens
            .iter()
            .filter(|(_, queue)| !queue.is_empty())
            .map(|(place, queue)| (Arc::clone(place), queue.iter().cloned().collect()))
            .collect()
    }

    /// \[CORE-073\] Rebuilds a marking from the normative snapshot form.
    ///
    /// FIFO order within each place is preserved, `created_at` is carried
    /// through **unchanged** — the engine never re-stamps a restored token,
    /// including under an injected epoch clock (\[TIME-015\], AC#9) — and a
    /// place the receiving net does not declare is retained rather than
    /// dropped, exactly as \[CORE-072\] requires of any initial marking
    /// (AC#7).
    ///
    /// An explicitly-empty sequence is accepted and yields the same marking
    /// as omitting the place entirely (AC#7). That half is worth testing
    /// directly: a snapshot-then-restore round-trip can never exercise it,
    /// because [`snapshot`](Self::snapshot) never emits one.
    pub fn from_snapshot(snapshot: &MarkingSnapshot) -> Self {
        let mut marking = Self::new();
        for (place, entries) in snapshot {
            if entries.is_empty() {
                continue;
            }
            marking
                .tokens
                .entry(Arc::clone(place))
                .or_default()
                .extend(entries.iter().cloned());
        }
        marking
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

    /// Removes and returns the first token whose value satisfies `predicate`.
    ///
    /// Used by the ν-net join path (NU-020/NU-021) to take the tokens whose
    /// projected correlation name equals the chosen binding. This is *not* an
    /// input guard (IO-006, removed) — input specifications are purely
    /// structural; the predicate here is always derived from name correlation.
    pub fn remove_matching(
        &mut self,
        place_name: &str,
        predicate: &dyn Fn(&dyn Any) -> bool,
    ) -> Option<ErasedToken> {
        let queue = self.tokens.get_mut(place_name)?;
        let pos = queue.iter().position(|t| predicate(t.value.as_ref()))?;
        queue.remove(pos)
    }

    /// Removes and returns all tokens from a place.
    pub fn remove_all(&mut self, place_name: &str) -> Vec<ErasedToken> {
        self.tokens
            .get_mut(place_name)
            .map_or_else(Vec::new, |q| q.drain(..).collect())
    }

    /// Removes and returns all tokens whose values satisfy `predicate`.
    pub fn remove_all_matching(
        &mut self,
        place_name: &str,
        predicate: &dyn Fn(&dyn Any) -> bool,
    ) -> Vec<ErasedToken> {
        let queue = match self.tokens.get_mut(place_name) {
            Some(q) => q,
            None => return Vec::new(),
        };
        let mut matched = Vec::new();
        let mut remaining = VecDeque::new();
        for token in queue.drain(..) {
            if predicate(token.value.as_ref()) {
                matched.push(token);
            } else {
                remaining.push_back(token);
            }
        }
        *queue = remaining;
        matched
    }

    /// Counts tokens whose values satisfy `predicate`, over the whole queue.
    ///
    /// Public API with no in-crate caller: the ν-net join path (NU-020) used to
    /// size a correlated `all`/`at-least` consume with this, but a same-pass
    /// deposit must stay out of that count ([EXEC-003] AC5), so the backends now
    /// count a bounded prefix inline instead.
    pub fn count_matching(&self, place_name: &str, predicate: &dyn Fn(&dyn Any) -> bool) -> usize {
        self.tokens.get(place_name).map_or(0, |q| {
            q.iter().filter(|t| predicate(t.value.as_ref())).count()
        })
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

        let predicate = |v: &dyn Any| v.downcast_ref::<i32>().is_some_and(|n| *n > 1);
        let t = m.remove_matching("p", &predicate).unwrap();
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
