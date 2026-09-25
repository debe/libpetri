//! Reusing the enumeration route's state space across queries ([VER-017]).
//!
//! The state-class graph the enumeration route builds depends only on the net and
//! its initial marking; the property, the sinks and the conditional sinks only
//! *read* it. A caller that asks many questions of one net would otherwise rebuild
//! the same graph for every question, and when the graph exceeds the budget every
//! question pays the full attempt before it falls through to the SMT pipeline.
//! Measured on a 47-place agent net whose graph exceeds the default budget: 3–4.6 s
//! per query with the route, 17–24 ms without it.
//!
//! A [`StateSpaceCache`] is created by the caller, handed to each verification
//! (`SmtVerifier::state_space_cache`, under the `z3` feature),
//! and owned by the caller: it holds its graphs until it is dropped or
//! [cleared](StateSpaceCache::clear), and nothing is cached without one.
//!
//! ## The key
//!
//! A [`PetriNet`] has no stable identity to key on — it is `Clone` without `Eq`,
//! and the Python binding deep-clones it on every call — so an entry is keyed on a
//! **structural fingerprint** of the net as the caller passed it, plus the initial
//! marking. The fingerprint is the `Debug` rendering of everything the graph reads:
//! the set of places (sorted by name: a net's listing of its places depends on
//! `HashSet` order, so two builds of one net may list them differently, and the
//! graph never reads that order), the terminal places, and per transition, in net
//! order, its name, input specs (kind and cardinality), output spec, inhibitor,
//! read and reset arcs, timing, priority and whether it has a match spec. `In`,
//! `Out`, the arc types and `Timing` derive `Debug` over their structural fields
//! only, and `Debug` quotes and escapes every name, so the rendering is injective:
//! two nets with the same fingerprint build the same graph. The fingerprint is kept whole as the key,
//! not hashed, so no collision can make two different nets share an entry.
//!
//! Actions and transition ids are left out. The graph reads neither, so two nets
//! that differ only there share an entry, which is a correct hit — and a clone of a
//! net, whose transitions keep their ids anyway, always hits.
//!
//! The terminal rewrite of [EXEC-042] is a deterministic function of the net, so the
//! key is the caller's net while the graph is built from the rewritten one.
//!
//! The marking is keyed by its counts in code-point order of place names, so the
//! same marking listed in another order hits. The one place a marking's listing
//! order is observable — the first state of a witness trace — is taken from the
//! caller's own marking, not the cached graph's
//! ([`decide_over_state_space`](crate::scg_verifier::decide_over_state_space)).

// The cache's only reader, `SmtVerifier`, exists under the `z3` feature. The type
// itself does not, so a binding can hold one whatever the feature set.
#![cfg_attr(not(feature = "z3"), allow(dead_code))]

use std::collections::HashMap;
use std::fmt::Write;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};

use libpetri_core::petri_net::PetriNet;

use crate::marking_state::MarkingState;
use crate::state_class_graph::StateClassGraph;

/// A caller-owned cache of state-class graphs for the enumeration route
/// ([VER-017]), shared across verifications of one net.
///
/// Cheap to clone: clones share one cache. `Send + Sync`, so verifications on
/// several threads can share it; concurrent queries on one net and initial marking
/// build its graph once, the others waiting for it.
///
/// - A **closed** graph of `C` classes is reused for any budget greater than `C`.
///   A budget of `C` or less would have truncated, and is answered as truncated.
/// - A **truncated** attempt at budget `B` is remembered: a later budget of `B` or
///   less declines at once, without building; a larger budget builds again and
///   replaces the entry.
///
/// ```ignore
/// let cache = StateSpaceCache::new();
/// for property in properties {
///     let result = SmtVerifier::for_net(&net)
///         .initial_marking(m0.clone())
///         .property(property)
///         .state_space_cache(&cache)
///         .verify();
/// }
/// ```
#[derive(Clone, Default)]
pub struct StateSpaceCache {
    inner: Arc<Inner>,
}

#[derive(Default)]
struct Inner {
    slots: Mutex<HashMap<StateSpaceKey, Arc<Slot>>>,
    builds: AtomicUsize,
}

/// One key's entry. The state is guarded separately from the map, so a build holds
/// neither lock and queries on other keys never wait for it.
#[derive(Default)]
struct Slot {
    state: Mutex<SlotState>,
    ready: Condvar,
}

#[derive(Default)]
enum SlotState {
    /// Nothing known: never built, or the build that owned the slot failed.
    #[default]
    Empty,
    /// A query is building this entry; the others wait on [`Slot::ready`]. A
    /// truncation already known for the entry stays known while it builds at a
    /// larger budget, so a query that it declines need not wait.
    Building { truncated_at: Option<usize> },
    /// The graph closed.
    Closed(Arc<StateClassGraph>),
    /// The graph hit this budget.
    Truncated(usize),
}

/// The key of an entry: the net's structural fingerprint and the initial marking.
/// See the module header for why it is complete.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct StateSpaceKey {
    net: String,
    marking: String,
}

impl StateSpaceKey {
    pub(crate) fn new(net: &PetriNet, initial: &MarkingState) -> Self {
        Self {
            net: net_fingerprint(net),
            marking: marking_fingerprint(initial),
        }
    }
}

/// How a query at some budget was answered.
pub(crate) enum StateSpaceLookup {
    /// Nothing usable was cached, so the graph was built at this budget, closed or
    /// not. The caller reads it exactly as it would without a cache.
    Built(Arc<StateClassGraph>),
    /// A closed graph was cached and the budget exceeds its class count.
    Reused(Arc<StateClassGraph>),
    /// The cache already knows this budget truncates: a truncation at this budget
    /// or a larger one, or a closed graph too large for it. Nothing was built.
    Declined,
}

impl StateSpaceCache {
    /// An empty cache.
    pub fn new() -> Self {
        Self::default()
    }

    /// Drops every entry. A build in progress completes, but into no entry.
    pub fn clear(&self) {
        lock(&self.inner.slots).clear();
    }

    /// The number of entries: closed graphs and remembered truncations.
    pub fn len(&self) -> usize {
        let slots: Vec<Arc<Slot>> = lock(&self.inner.slots).values().cloned().collect();
        slots
            .iter()
            .filter(|slot| {
                matches!(
                    *lock(&slot.state),
                    SlotState::Closed(_)
                        | SlotState::Truncated(_)
                        | SlotState::Building { truncated_at: Some(_) }
                )
            })
            .count()
    }

    /// Whether the cache holds no entry.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// How many state-class graphs this cache has built, over its lifetime. A
    /// query answered from the cache builds none; [`clear`](Self::clear) does not
    /// reset the count.
    pub fn build_count(&self) -> usize {
        self.inner.builds.load(Ordering::SeqCst)
    }

    /// Answers one enumeration query at `budget`, calling `build` only when nothing
    /// usable is cached. A concurrent query on the same key waits for the build
    /// rather than start its own, unless a truncation the entry already holds
    /// declines it. If `build` panics the slot is restored to what it held
    /// before, the waiters retry, and the panic propagates.
    pub(crate) fn lookup(
        &self,
        key: StateSpaceKey,
        budget: usize,
        build: impl FnOnce() -> StateClassGraph,
    ) -> StateSpaceLookup {
        let slot = lock(&self.inner.slots).entry(key).or_default().clone();
        let mut state = lock(&slot.state);
        loop {
            match &*state {
                SlotState::Closed(graph) => {
                    return if budget > graph.class_count() {
                        StateSpaceLookup::Reused(Arc::clone(graph))
                    } else {
                        StateSpaceLookup::Declined
                    };
                }
                SlotState::Truncated(cached)
                | SlotState::Building {
                    truncated_at: Some(cached),
                } if budget <= *cached => {
                    return StateSpaceLookup::Declined;
                }
                SlotState::Building { .. } => {
                    state = slot.ready.wait(state).unwrap_or_else(PoisonError::into_inner);
                }
                SlotState::Empty | SlotState::Truncated(_) => break,
            }
        }
        let truncated_at = match *state {
            SlotState::Truncated(cached) => Some(cached),
            _ => None,
        };
        *state = SlotState::Building { truncated_at };
        drop(state);

        let mut pending = PendingBuild {
            slot: &slot,
            truncated_at,
            done: false,
        };
        self.inner.builds.fetch_add(1, Ordering::SeqCst);
        let graph = Arc::new(build());
        let entry = if graph.is_complete() {
            SlotState::Closed(Arc::clone(&graph))
        } else {
            SlotState::Truncated(budget)
        };
        pending.finish(entry);
        StateSpaceLookup::Built(graph)
    }
}

/// The build a query owns. Publishes its entry and wakes the waiters; if the build
/// unwinds instead, restores what the slot knew before, so a waiter builds in its
/// place.
struct PendingBuild<'s> {
    slot: &'s Slot,
    /// The truncation the slot held when this build took it, if any.
    truncated_at: Option<usize>,
    done: bool,
}

impl PendingBuild<'_> {
    fn finish(&mut self, entry: SlotState) {
        *lock(&self.slot.state) = entry;
        self.done = true;
        self.slot.ready.notify_all();
    }
}

impl Drop for PendingBuild<'_> {
    fn drop(&mut self) {
        if !self.done {
            *lock(&self.slot.state) = match self.truncated_at {
                Some(cached) => SlotState::Truncated(cached),
                None => SlotState::Empty,
            };
            self.slot.ready.notify_all();
        }
    }
}

/// No lock here is held across user code that can panic, so a poisoned lock
/// still guards a consistent value.
fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Everything the state-class graph reads of `net`, rendered with `Debug`. See the
/// module header.
fn net_fingerprint(net: &PetriNet) -> String {
    // The set, not the listing: `PetriNetBuilder` lists a transition's output places
    // in `HashSet` order, which differs between two builds of one net, and the graph
    // never reads the order.
    let mut places: Vec<&str> = net.places().iter().map(|p| p.name()).collect();
    places.sort_unstable();
    let terminals: Vec<&str> = net.terminals().iter().map(|p| p.name()).collect();
    let mut out = format!("places={places:?};terminals={terminals:?}");
    for t in net.transitions() {
        let _ = write!(
            out,
            ";transition({:?}, in={:?}, out={:?}, inhibitors={:?}, reads={:?}, resets={:?}, \
             timing={:?}, priority={}, match={})",
            t.name(),
            t.input_specs(),
            t.output_spec(),
            t.inhibitors(),
            t.reads(),
            t.resets(),
            t.timing(),
            t.priority(),
            t.match_spec().is_some()
        );
    }
    out
}

/// The marking's non-zero counts in code-point order of place names, whatever order
/// the caller listed them in.
fn marking_fingerprint(marking: &MarkingState) -> String {
    let mut entries: Vec<(&str, usize)> = marking.places().collect();
    entries.sort_unstable();
    format!("{entries:?}")
}

#[cfg(test)]
mod tests {
    use std::thread;

    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use libpetri_core::action::fork;
    use libpetri_core::input::{In, exactly, one};
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    fn chain(input: In) -> PetriNet {
        let b = Place::<()>::new("b");
        PetriNet::builder("n")
            .transition(
                Transition::builder("t")
                    .input(input)
                    .output(out_place(&b))
                    .action(fork())
                    .build(),
            )
            .build()
    }

    #[test]
    fn the_cache_is_send_and_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<StateSpaceCache>();
    }

    /// Every arc kind and output shape the graph reads gives a distinct key.
    #[test]
    fn the_fingerprint_separates_every_arc_kind_and_output_shape() {
        use libpetri_core::arc::{inhibitor, read, reset};
        use libpetri_core::input::{all, at_least};
        use libpetri_core::output::{and_places, forward_input, timeout_place, xor_places};

        let (a, b, c) = (Place::<()>::new("a"), Place::<()>::new("b"), Place::<()>::new("c"));
        let (br, cr) = (b.as_ref(), c.as_ref());
        let net = |t: libpetri_core::transition::TransitionBuilder| {
            PetriNet::builder("n").transition(t.action(fork()).build()).build()
        };
        let base = || Transition::builder("t").input(one(&a));
        let nets = [
            net(base().output(out_place(&b))),
            net(Transition::builder("t").input(all(&a)).output(out_place(&b))),
            net(Transition::builder("t").input(at_least(1, &a)).output(out_place(&b))),
            net(Transition::builder("t").input(exactly(1, &a)).output(out_place(&b))),
            net(base().output(and_places(&[&br, &cr]))),
            net(base().output(xor_places(&[&b, &c]))),
            net(base().output(timeout_place(5, &b))),
            net(base().output(forward_input(&a, &b))),
            net(base().output(out_place(&b)).read(read(&c))),
            net(base().output(out_place(&b)).inhibitor(inhibitor(&c))),
            net(base().output(out_place(&b)).reset(reset(&c))),
        ];
        let m0 = MarkingStateBuilder::new().tokens("a", 1).build();
        let keys: std::collections::HashSet<_> =
            nets.iter().map(|n| StateSpaceKey::new(n, &m0)).collect();
        assert_eq!(keys.len(), nets.len());
    }

    #[test]
    fn the_fingerprint_covers_cardinality_and_ignores_listing_order() {
        let a = Place::<()>::new("a");
        let m0 = MarkingStateBuilder::new().tokens("a", 2).build();
        assert!(
            StateSpaceKey::new(&chain(one(&a)), &m0) != StateSpaceKey::new(&chain(exactly(2, &a)), &m0)
        );
        let net = chain(one(&a));
        let xy = MarkingStateBuilder::new().tokens("x", 1).tokens("a", 2).build();
        let yx = MarkingStateBuilder::new().tokens("a", 2).tokens("x", 1).build();
        assert!(StateSpaceKey::new(&net, &xy) == StateSpaceKey::new(&net, &yx));
    }

    /// A truncation at 2 is known while a build at a larger budget runs: a query at
    /// budget 2 or less declines at once, rather than wait for that build.
    #[test]
    fn a_known_truncation_declines_during_a_larger_build() {
        use std::sync::mpsc;
        use std::time::Duration;

        let a = Place::<()>::new("a");
        let net = chain(one(&a));
        let m0 = MarkingStateBuilder::new().tokens("a", 1).build();
        let cache = StateSpaceCache::new();
        let key = StateSpaceKey::new(&net, &m0);
        let truncated = StateClassGraph::build(&net, &m0, 1);
        assert!(!truncated.is_complete());
        cache.lookup(key.clone(), 1, || truncated);

        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel::<()>();
        let (answer_tx, answer_rx) = mpsc::channel();
        let (cache_ref, net_ref, m0_ref, key_ref) = (&cache, &net, &m0, &key);
        thread::scope(|scope| {
            scope.spawn(move || {
                cache_ref.lookup(key_ref.clone(), 100, || {
                    started_tx.send(()).unwrap();
                    release_rx.recv().unwrap();
                    StateClassGraph::build(net_ref, m0_ref, 100)
                })
            });
            started_rx.recv().unwrap();
            scope.spawn(move || {
                let declined = matches!(
                    cache_ref.lookup(key_ref.clone(), 1, || unreachable!()),
                    StateSpaceLookup::Declined
                );
                answer_tx.send(declined).unwrap();
            });
            let answer = answer_rx.recv_timeout(Duration::from_secs(2));
            release_tx.send(()).unwrap();
            assert_eq!(answer, Ok(true), "a known truncation waited for the larger build");
        });
        assert_eq!(cache.build_count(), 2);
    }

    /// The build panics on its own thread, which dies of it: nothing here catches
    /// the unwind, which this crate never does. The thread's guard must still leave
    /// the slot clear for the next query.
    #[test]
    fn a_failed_build_clears_the_slot() {
        let a = Place::<()>::new("a");
        let net = chain(one(&a));
        let m0 = MarkingStateBuilder::new().tokens("a", 1).build();
        let cache = StateSpaceCache::new();
        let key = StateSpaceKey::new(&net, &m0);
        let failed = thread::scope(|scope| {
            scope
                .spawn(|| cache.lookup(key.clone(), 100, || panic!("build failed")))
                .join()
        });
        assert!(failed.is_err());
        assert!(cache.is_empty());
        let slot = lock(&cache.inner.slots).get(&key).cloned().expect("slot");
        assert!(matches!(*lock(&slot.state), SlotState::Empty), "a waiter would wait forever");
        let answer = cache.lookup(key, 100, || StateClassGraph::build(&net, &m0, 100));
        assert!(matches!(answer, StateSpaceLookup::Built(_)));
        assert_eq!(cache.len(), 1);
    }

    /// A failed build at a larger budget leaves the truncation it started from.
    #[test]
    fn a_failed_larger_build_keeps_the_known_truncation() {
        let a = Place::<()>::new("a");
        let net = chain(one(&a));
        let m0 = MarkingStateBuilder::new().tokens("a", 1).build();
        let cache = StateSpaceCache::new();
        let key = StateSpaceKey::new(&net, &m0);
        cache.lookup(key.clone(), 1, || StateClassGraph::build(&net, &m0, 1));
        let failed = thread::scope(|scope| {
            scope
                .spawn(|| cache.lookup(key.clone(), 100, || panic!("build failed")))
                .join()
        });
        assert!(failed.is_err());
        assert_eq!(cache.len(), 1);
        let answer = cache.lookup(key, 1, || unreachable!());
        assert!(matches!(answer, StateSpaceLookup::Declined));
    }
}
