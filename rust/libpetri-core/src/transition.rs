use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::action::{BoxedAction, passthrough};
use crate::arc::{Inhibitor, Read, Reset};
use crate::input::In;
use crate::match_spec::MatchSpec;
use crate::output::{Out, all_places, duplicate_in_branch, find_forward_inputs, find_timeout};
use crate::place::PlaceRef;
use crate::timing::{Timing, deadline, delayed, exact, immediate, window};

/// Unique identifier for a transition instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TransitionId(u64);

static NEXT_ID: AtomicU64 = AtomicU64::new(0);

impl TransitionId {
    fn next() -> Self {
        Self(NEXT_ID.fetch_add(1, Ordering::Relaxed))
    }
}

/// A transition in the Time Petri Net that transforms tokens.
///
/// Transitions use identity-based equality (TransitionId) — each instance is unique
/// regardless of name. The name is purely a label for display/debugging/export.
#[derive(Clone)]
pub struct Transition {
    id: TransitionId,
    name: Arc<str>,
    input_specs: Vec<In>,
    output_spec: Option<Out>,
    inhibitors: Vec<Inhibitor>,
    reads: Vec<Read>,
    resets: Vec<Reset>,
    /// Optional ν-net join correlation: a subset of `input_specs` that must be
    /// correlated by name equality on firing. `None` for ordinary transitions.
    match_spec: Option<MatchSpec>,
    timing: Timing,
    action_timeout: Option<u64>,
    action: BoxedAction,
    priority: i32,
    input_places: HashSet<PlaceRef>,
    read_places: HashSet<PlaceRef>,
    output_places: HashSet<PlaceRef>,
    /// Optional mapping from **author-original** place names (as the
    /// action source code wrote them) to the **post-compose** place
    /// names that the runtime actually exposes through
    /// [`crate::context::TransitionContext`].
    ///
    /// Populated by [`crate::rewriter::substitute_places`] when a
    /// `SubnetDef` is composed into a host net: arc rewriting swaps
    /// every place reference for the host-bound (or prefixed) name, but
    /// the action's hard-coded `ctx.input("local_name")` calls still
    /// reach for the **local** name. Bindings (Python, etc.) use this
    /// map to fall back from a local-name lookup to the corresponding
    /// host name.
    ///
    /// `None` for transitions that have not been substituted (the
    /// common case — author-built transitions added directly to a net).
    local_name_map: Option<Arc<HashMap<Arc<str>, Arc<str>>>>,
}

impl Transition {
    /// Returns the unique transition ID.
    pub fn id(&self) -> TransitionId {
        self.id
    }

    /// Returns the transition name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the name as Arc<str>.
    pub fn name_arc(&self) -> &Arc<str> {
        &self.name
    }

    /// Returns the input specifications.
    pub fn input_specs(&self) -> &[In] {
        &self.input_specs
    }

    /// Returns the output specification, if any.
    pub fn output_spec(&self) -> Option<&Out> {
        self.output_spec.as_ref()
    }

    /// Returns the inhibitor arcs.
    pub fn inhibitors(&self) -> &[Inhibitor] {
        &self.inhibitors
    }

    /// Returns the read arcs.
    pub fn reads(&self) -> &[Read] {
        &self.reads
    }

    /// Returns the reset arcs.
    pub fn resets(&self) -> &[Reset] {
        &self.resets
    }

    /// Returns the ν-net join correlation spec, if any (spec NU-020).
    pub fn match_spec(&self) -> Option<&MatchSpec> {
        self.match_spec.as_ref()
    }

    /// Returns the timing specification.
    pub fn timing(&self) -> &Timing {
        &self.timing
    }

    /// Returns the action timeout in ms, if any.
    pub fn action_timeout(&self) -> Option<u64> {
        self.action_timeout
    }

    /// Returns true if this transition has an action timeout.
    pub fn has_action_timeout(&self) -> bool {
        self.action_timeout.is_some()
    }

    /// Returns the transition action.
    pub fn action(&self) -> &BoxedAction {
        &self.action
    }

    /// Returns the priority (higher fires first).
    pub fn priority(&self) -> i32 {
        self.priority
    }

    /// Returns set of input place refs (consumed tokens).
    pub fn input_places(&self) -> &HashSet<PlaceRef> {
        &self.input_places
    }

    /// Returns set of read place refs (context tokens, not consumed).
    pub fn read_places(&self) -> &HashSet<PlaceRef> {
        &self.read_places
    }

    /// Returns set of output place refs (where tokens are produced).
    pub fn output_places(&self) -> &HashSet<PlaceRef> {
        &self.output_places
    }

    /// Returns the local-name → post-compose-name map populated by the
    /// rewriter when this transition was composed into a host net. See
    /// the `local_name_map` field doc for details.
    pub fn local_name_map(&self) -> Option<&Arc<HashMap<Arc<str>, Arc<str>>>> {
        self.local_name_map.as_ref()
    }

    /// Returns a clone of the local-name map (cheap — `Arc` bump).
    /// Used by binding-side action contexts that need to keep the map
    /// alive past the transition's lifetime.
    pub fn local_name_map_cloned(&self) -> Option<Arc<HashMap<Arc<str>, Arc<str>>>> {
        self.local_name_map.as_ref().map(Arc::clone)
    }

    /// Creates a new TransitionBuilder.
    pub fn builder(name: impl Into<Arc<str>>) -> TransitionBuilder {
        TransitionBuilder::new(name)
    }
}

impl std::fmt::Debug for Transition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Transition")
            .field("id", &self.id)
            .field("name", &self.name)
            .field("timing", &self.timing)
            .field("priority", &self.priority)
            .finish()
    }
}

impl PartialEq for Transition {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Transition {}

impl std::hash::Hash for Transition {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl std::fmt::Display for Transition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Transition[{}]", self.name)
    }
}

/// Builder for constructing Transition instances.
pub struct TransitionBuilder {
    name: Arc<str>,
    input_specs: Vec<In>,
    output_spec: Option<Out>,
    inhibitors: Vec<Inhibitor>,
    reads: Vec<Read>,
    resets: Vec<Reset>,
    match_spec: Option<MatchSpec>,
    timing: Timing,
    action: BoxedAction,
    priority: i32,
    local_name_map: Option<Arc<HashMap<Arc<str>, Arc<str>>>>,
}

/// The [CORE-030] duplicate-input rejection, shared by [`TransitionBuilder::build`]
/// and the runtime's compile-time backstop so the two cannot drift; the same text
/// as Java's `ArcDiagnostics.duplicateInputMessage` and TypeScript's
/// `duplicateInputArcMessage`, with Rust's `at_least` spelling.
pub fn duplicate_input_message(transition: &str, place: &str) -> String {
    format!(
        "Transition '{transition}' declares two input arcs on place '{place}'. Duplicate input \
         places have no coherent consumption semantics and are rejected (CORE-030). Use a \
         single arc with exactly(n) / at_least(n) instead."
    )
}

impl TransitionBuilder {
    pub fn new(name: impl Into<Arc<str>>) -> Self {
        Self {
            name: name.into(),
            input_specs: Vec::new(),
            output_spec: None,
            inhibitors: Vec::new(),
            reads: Vec::new(),
            resets: Vec::new(),
            match_spec: None,
            timing: immediate(),
            action: passthrough(),
            priority: 0,
            local_name_map: None,
        }
    }

    /// Attaches a local-name → composed-name map. Used by the
    /// rewriter when substituting place references at compose time so
    /// the action's hard-coded local names still resolve.
    pub fn local_name_map(mut self, map: Arc<HashMap<Arc<str>, Arc<str>>>) -> Self {
        self.local_name_map = Some(map);
        self
    }

    /// Add a single input specification.
    pub fn input(mut self, spec: In) -> Self {
        self.input_specs.push(spec);
        self
    }

    /// Add multiple input specifications.
    pub fn inputs(mut self, specs: Vec<In>) -> Self {
        self.input_specs.extend(specs);
        self
    }

    /// Set the output specification.
    pub fn output(mut self, spec: Out) -> Self {
        self.output_spec = Some(spec);
        self
    }

    /// Add an inhibitor arc.
    pub fn inhibitor(mut self, inh: Inhibitor) -> Self {
        self.inhibitors.push(inh);
        self
    }

    /// Add multiple inhibitor arcs.
    pub fn inhibitors(mut self, inhs: Vec<Inhibitor>) -> Self {
        self.inhibitors.extend(inhs);
        self
    }

    /// Add a read arc.
    pub fn read(mut self, r: Read) -> Self {
        self.reads.push(r);
        self
    }

    /// Add multiple read arcs.
    pub fn reads(mut self, rs: Vec<Read>) -> Self {
        self.reads.extend(rs);
        self
    }

    /// Add a reset arc.
    pub fn reset(mut self, r: Reset) -> Self {
        self.resets.push(r);
        self
    }

    /// Add multiple reset arcs.
    pub fn resets(mut self, rs: Vec<Reset>) -> Self {
        self.resets.extend(rs);
        self
    }

    /// Sets the ν-net join correlation spec: the named input places must be
    /// correlated by name equality on firing (spec NU-020). Every place
    /// referenced by the spec must also be declared as an input.
    pub fn match_spec(mut self, spec: MatchSpec) -> Self {
        self.match_spec = Some(spec);
        self
    }

    /// Set timing specification. A `Timing` variant written out directly is checked
    /// in [`build`](Self::build), with the factories' rules ([TIME-001] AC5).
    pub fn timing(mut self, timing: Timing) -> Self {
        self.timing = timing;
        self
    }

    /// Set the transition action.
    pub fn action(mut self, action: BoxedAction) -> Self {
        self.action = action;
        self
    }

    /// Set priority (higher fires first).
    pub fn priority(mut self, priority: i32) -> Self {
        self.priority = priority;
        self
    }

    /// Build the transition.
    ///
    /// # Panics
    /// - Panics if two input arcs name the same place (**CORE-030** AC3): there is
    ///   no coherent consumption semantics for them. Use one arc with
    ///   `exactly(n)` / `at_least(n)`. The runtime's compile-time check stays
    ///   as a backstop, but after this one no analysis ever sees such a
    ///   transition.
    /// - Panics if one output branch names a place twice (**IO-011**): outputs are
    ///   sets of places, so `and(P, P)` is not two tokens into `P`.
    /// - Panics if an input requires no token (`In::Exactly { count: 0 }`,
    ///   `In::AtLeast { minimum: 0 }`; **IO-002**, **IO-004**).
    /// - Panics if the match specification keys one place twice (**NU-020**).
    /// - Panics if ForwardInput references a non-input place.
    pub fn build(self) -> Transition {
        // [CORE-030] AC3: duplicate input places are rejected where the
        // transition is made, so every consumer — executors, the state-class
        // graphs and the verifier's flattener — sees at most one input arc per
        // place. Place identity is the name, as everywhere in Rust.
        let mut seen_inputs: HashSet<&str> = HashSet::with_capacity(self.input_specs.len());
        for spec in &self.input_specs {
            if !seen_inputs.insert(spec.place_name()) {
                panic!("{}", duplicate_input_message(&self.name, spec.place_name()));
            }
            // [IO-002] AC1 / [IO-004] AC1: `exactly()` and `at_least()` reject a count
            // below 1, but the `In` variants are public, so a spec written out directly
            // is checked here. The executors would still wait for a token that the
            // analyses do not require.
            let required = crate::input::required_count(spec);
            if required == 0 {
                panic!(
                    "input '{}' of transition '{}' requires 0 tokens; exactly(n) and \
                     at_least(n) need n >= 1 (IO-002, IO-004)",
                    spec.place_name(),
                    self.name
                );
            }
        }

        // [TIME-001] AC5: the `Timing` variants are public, so a timing written out
        // directly skips the factories' asserts. Run them again here, as for `In`
        // above: past `MAX_DURATION_MS` a state-class graph reads a transition that can
        // fire as one that never can, and `reaping::relax_late` would panic inside the
        // verifier when it rebuilds a window as `delayed(earliest)`.
        match self.timing {
            Timing::Immediate => {}
            Timing::Deadline { by_ms } => {
                deadline(by_ms);
            }
            Timing::Delayed { after_ms } => {
                delayed(after_ms);
            }
            Timing::Window {
                earliest_ms,
                latest_ms,
            } => {
                window(earliest_ms, latest_ms);
            }
            Timing::Exact { at_ms } => {
                exact(at_ms);
            }
        }

        // [IO-011]: outputs are sets (IO-015), so one AND branch naming a place
        // twice is not a weighted output — it would silently collapse. Rejected
        // here, where every construction path (builders, composition, channel
        // merge, fusion) passes.
        if let Some(dup) = self.output_spec.as_ref().and_then(duplicate_in_branch) {
            panic!(
                "output spec of transition '{}' names place '{}' twice in one AND branch; \
                 outputs are sets (IO-015) — a weighted output is not supported, add a second \
                 place or a follow-up transition",
                self.name,
                dup.name()
            );
        }

        // Validate ForwardInput references
        if let Some(ref out) = self.output_spec {
            let input_place_names: HashSet<_> =
                self.input_specs.iter().map(|s| s.place_name()).collect();
            for (from, _) in find_forward_inputs(out) {
                assert!(
                    input_place_names.contains(from.name()),
                    "Transition '{}': ForwardInput references non-input place '{}'",
                    self.name,
                    from.name()
                );
            }
        }

        // Validate MatchSpec correlates only declared input places, each once (NU-020).
        // `MatchSpec::from_keys` (the FFI path) does not go through the builder.
        if let Some(ref ms) = self.match_spec {
            if let Some(place) = crate::match_spec::duplicate_key(ms.keys()) {
                panic!(
                    "Transition '{}': {}",
                    self.name,
                    crate::match_spec::duplicate_key_message(place)
                );
            }
            let input_place_names: HashSet<_> =
                self.input_specs.iter().map(|s| s.place_name()).collect();
            for key in ms.keys() {
                assert!(
                    input_place_names.contains(key.place_name()),
                    "Transition '{}': MatchSpec correlates non-input place '{}'",
                    self.name,
                    key.place_name()
                );
            }
            // NU-054 AC1: a relay target is an output of the transition (in at
            // least one branch), declared once.
            if !ms.relays().is_empty() {
                let output_names: HashSet<String> = self
                    .output_spec
                    .as_ref()
                    .map(|o| all_places(o).iter().map(|p| p.name().to_string()).collect())
                    .unwrap_or_default();
                let mut seen: HashSet<&str> = HashSet::new();
                for relay in ms.relays() {
                    assert!(
                        seen.insert(relay.place_name()),
                        "Transition '{}': relay target '{}' is declared twice (NU-054)",
                        self.name,
                        relay.place_name()
                    );
                    assert!(
                        output_names.contains(relay.place_name()),
                        "Transition '{}': relay target '{}' is not an output of the transition (NU-054)",
                        self.name,
                        relay.place_name()
                    );
                }
            }
        }

        let action_timeout = self
            .output_spec
            .as_ref()
            .and_then(|o| find_timeout(o).map(|(ms, _)| ms));

        // Precompute place sets
        let input_places: HashSet<PlaceRef> =
            self.input_specs.iter().map(|s| s.place().clone()).collect();

        let read_places: HashSet<PlaceRef> = self.reads.iter().map(|r| r.place.clone()).collect();

        let output_places: HashSet<PlaceRef> = self
            .output_spec
            .as_ref()
            .map(all_places)
            .unwrap_or_default();

        Transition {
            id: TransitionId::next(),
            name: self.name,
            input_specs: self.input_specs,
            output_spec: self.output_spec,
            inhibitors: self.inhibitors,
            reads: self.reads,
            resets: self.resets,
            match_spec: self.match_spec,
            timing: self.timing,
            action_timeout,
            action: self.action,
            priority: self.priority,
            input_places,
            read_places,
            output_places,
            local_name_map: self.local_name_map,
        }
    }
}

impl Transition {
    /// Returns a copy of this transition with `extra` appended to its inhibitor
    /// arcs, skipping any place it already inhibits. Name, timing, priority,
    /// action and every other arc carry through unchanged. Used by the
    /// verifier's terminal-place encoding ([EXEC-042]).
    pub fn with_added_inhibitors(&self, extra: impl IntoIterator<Item = Inhibitor>) -> Transition {
        let mut inhibitors = self.inhibitors.clone();
        for inh in extra {
            if !inhibitors.contains(&inh) {
                inhibitors.push(inh);
            }
        }
        rebuild(self, Arc::clone(&self.action), inhibitors)
    }
}

/// Creates a new transition with a different action while preserving all arc specs.
pub(crate) fn rebuild_with_action(t: &Transition, action: BoxedAction) -> Transition {
    rebuild(t, action, t.inhibitors.clone())
}

fn rebuild(t: &Transition, action: BoxedAction, inhibitors: Vec<Inhibitor>) -> Transition {
    let mut builder = Transition::builder(Arc::clone(&t.name))
        .timing(t.timing)
        .priority(t.priority)
        .action(action)
        .inputs(t.input_specs.clone())
        .inhibitors(inhibitors)
        .reads(t.reads.clone())
        .resets(t.resets.clone());

    if let Some(ref out) = t.output_spec {
        builder = builder.output(out.clone());
    }

    if let Some(ref ms) = t.match_spec {
        builder = builder.match_spec(ms.clone());
    }

    // MOD-031: carry the declared→actual place correspondence forward so an action
    // bound after instantiate/compose ([CORE-042]) still resolves its hardcoded
    // author-local places. `None` for hand-written / directly-composed transitions.
    if let Some(map) = t.local_name_map_cloned() {
        builder = builder.local_name_map(map);
    }

    builder.build()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::one;
    use crate::output::out_place;
    use crate::place::Place;

    // ---- NU-054 AC1: relay declaration ----

    fn relay_join(relays: &[&str], out: Out) -> Transition {
        use crate::match_spec::MatchSpec;
        use crate::name::NameId;
        let a = Place::<String>::new("A");
        let b = Place::<String>::new("B");
        let key = |s: &String| NameId::new(s.clone());
        let mut ms = MatchSpec::builder().key(&a, key).key(&b, key);
        for r in relays {
            ms = ms.relay_to(&Place::<String>::new(*r), key);
        }
        Transition::builder("j")
            .input(one(&a))
            .input(one(&b))
            .output(out)
            .match_spec(ms.build())
            .build()
    }

    #[test]
    fn relay_targets_are_kept_apart_from_the_keys() {
        let t = relay_join(&["C"], out_place(&Place::<String>::new("C")));
        let ms = t.match_spec().unwrap();
        let keys: Vec<&str> = ms.keys().iter().map(|k| k.place_name()).collect();
        let relays: Vec<&str> = ms.relays().iter().map(|k| k.place_name()).collect();
        assert_eq!(keys, vec!["A", "B"]);
        assert_eq!(relays, vec!["C"]);
        assert!(!ms.correlates("C"));
        assert!(ms.relay_for("C").is_some() && ms.relay_for("A").is_none());
    }

    #[test]
    #[should_panic(expected = "MatchSpec must correlate at least 2 input places, got 1")]
    fn a_relay_target_does_not_count_towards_the_two_correlated_inputs() {
        use crate::match_spec::MatchSpec;
        use crate::name::NameId;
        let key = |s: &String| NameId::new(s.clone());
        let _ = MatchSpec::builder()
            .key(&Place::<String>::new("A"), key)
            .relay_to(&Place::<String>::new("C"), key)
            .build();
    }

    #[test]
    #[should_panic(
        expected = "Transition 'j': relay target 'other' is not an output of the transition (NU-054)"
    )]
    fn rejects_a_relay_target_that_is_not_an_output() {
        relay_join(&["other"], out_place(&Place::<String>::new("C")));
    }

    #[test]
    #[should_panic(expected = "Transition 'j': relay target 'C' is declared twice (NU-054)")]
    fn rejects_a_relay_target_declared_twice() {
        relay_join(&["C", "C"], out_place(&Place::<String>::new("C")));
    }

    #[test]
    fn accepts_a_target_on_one_xor_branch_and_a_self_loop_target() {
        use crate::output::{and, xor};
        let c = Place::<String>::new("C");
        let other = Place::<String>::new("other");
        relay_join(&["C"], xor(vec![out_place(&c), out_place(&other)]));
        // A relay target that is also one of the join's keys (correlated self-loop).
        relay_join(
            &["A"],
            and(vec![out_place(&Place::<String>::new("A")), out_place(&c)]),
        );
    }

    #[test]
    fn transition_builder_basic() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("test")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .build();

        assert_eq!(t.name(), "test");
        assert_eq!(t.input_specs().len(), 1);
        assert!(t.output_spec().is_some());
        assert_eq!(t.timing(), &Timing::Immediate);
        assert_eq!(t.priority(), 0);
    }

    #[test]
    fn transition_identity() {
        let t1 = Transition::builder("test").build();
        let t2 = Transition::builder("test").build();
        assert_ne!(t1, t2); // different IDs
    }

    #[test]
    fn transition_places_computed() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<i32>::new("out");
        let p_read = Place::<String>::new("ctx");

        let t = Transition::builder("test")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .read(crate::arc::read(&p_read))
            .build();

        assert!(t.input_places().contains(&PlaceRef::new("in")));
        assert!(t.output_places().contains(&PlaceRef::new("out")));
        assert!(t.read_places().contains(&PlaceRef::new("ctx")));
    }

    #[test]
    #[should_panic(expected = "ForwardInput references non-input place")]
    fn forward_input_validation() {
        let from = Place::<i32>::new("not-an-input");
        let to = Place::<i32>::new("to");

        Transition::builder("test")
            .output(crate::output::forward_input(&from, &to))
            .build();
    }

    /// CORE-030 AC3: the rejection happens at transition build, whatever the
    /// cardinality of either arc.
    #[test]
    #[should_panic(expected = "declares two input arcs on place 'p'")]
    fn duplicate_input_places_rejected_at_build() {
        let p = Place::<i32>::new("p");
        Transition::builder("t")
            .input(one(&p))
            .input(crate::input::exactly(2, &p))
            .build();
    }

    /// TIME-001 AC5: the `Timing` variants are public, so a timing written out
    /// directly skips the factories' checks. `build` runs them again, with the
    /// factories' messages.
    fn with_timing(timing: crate::timing::Timing) -> Transition {
        Transition::builder("t").timing(timing).build()
    }

    #[test]
    #[should_panic(
        expected = "Delay must be at most MAX_DURATION_MS"
    )]
    fn a_delayed_timing_written_out_past_the_maximum_is_rejected_at_build() {
        use crate::timing::{MAX_DURATION_MS, Timing};
        with_timing(Timing::Delayed {
            after_ms: MAX_DURATION_MS + 1,
        });
    }

    #[test]
    #[should_panic(
        expected = "Earliest must be at most MAX_DURATION_MS"
    )]
    fn a_window_written_out_past_the_maximum_is_rejected_at_build() {
        use crate::timing::{MAX_DURATION_MS, Timing};
        with_timing(Timing::Window {
            earliest_ms: MAX_DURATION_MS + 1,
            latest_ms: MAX_DURATION_MS + 2,
        });
    }

    #[test]
    #[should_panic(expected = "Latest (3) must be >= earliest (5)")]
    fn an_inverted_window_written_out_is_rejected_at_build() {
        use crate::timing::Timing;
        with_timing(Timing::Window {
            earliest_ms: 5,
            latest_ms: 3,
        });
    }

    #[test]
    #[should_panic(
        expected = "Exact time must be at most MAX_DURATION_MS"
    )]
    fn an_exact_timing_written_out_past_the_maximum_is_rejected_at_build() {
        use crate::timing::{MAX_DURATION_MS, Timing};
        with_timing(Timing::Exact {
            at_ms: MAX_DURATION_MS + 1,
        });
    }

    #[test]
    #[should_panic(expected = "Deadline must be positive: 0")]
    fn a_zero_deadline_written_out_is_rejected_at_build() {
        use crate::timing::Timing;
        with_timing(Timing::Deadline { by_ms: 0 });
    }

    #[test]
    fn a_valid_timing_written_out_builds() {
        use crate::timing::{MAX_DURATION_MS, Timing};
        for timing in [
            Timing::Immediate,
            Timing::Deadline { by_ms: 1 },
            Timing::Delayed {
                after_ms: MAX_DURATION_MS,
            },
            Timing::Window {
                earliest_ms: MAX_DURATION_MS,
                latest_ms: MAX_DURATION_MS,
            },
            Timing::Exact {
                at_ms: MAX_DURATION_MS,
            },
        ] {
            assert_eq!(*with_timing(timing).timing(), timing);
        }
    }

    /// IO-011 AC4: `And(P, P)`, `And(P, And(Q, P))` and `Xor(A, And(P, P))` are
    /// rejected naming the transition and `P`; `Xor(And(P, A), And(P, B))` builds.
    #[test]
    fn a_place_named_twice_in_one_and_branch_is_rejected() {
        use crate::output::{and, xor};
        let (p, q, a, b) = (
            Place::<i32>::new("P"),
            Place::<i32>::new("Q"),
            Place::<i32>::new("A"),
            Place::<i32>::new("B"),
        );
        let message = "output spec of transition 't' names place 'P' twice in one AND branch; \
                       outputs are sets (IO-015) — a weighted output is not supported, add a \
                       second place or a follow-up transition";
        for spec in [
            and(vec![out_place(&p), out_place(&p)]),
            and(vec![out_place(&p), and(vec![out_place(&q), out_place(&p)])]),
            xor(vec![out_place(&a), and(vec![out_place(&p), out_place(&p)])]),
        ] {
            let err = std::panic::catch_unwind(|| Transition::builder("t").output(spec).build())
                .expect_err("a duplicate in one AND branch must be rejected");
            assert_eq!(err.downcast_ref::<String>().map(String::as_str), Some(message));
        }
        let ok = Transition::builder("t")
            .output(xor(vec![
                and(vec![out_place(&p), out_place(&a)]),
                and(vec![out_place(&p), out_place(&b)]),
            ]))
            .build();
        assert_eq!(ok.output_places().len(), 3);
    }

    /// IO-011: the place reported is the one Java's `ArcDiagnostics.duplicateInBranch`
    /// and TypeScript's `duplicateInBranch` report — the spec walked child by child,
    /// a duplicate inside a child before one across siblings — not the first
    /// enumerated branch's (`[A, Q, Q]` here, which would name `Q`).
    #[test]
    fn the_reported_duplicate_is_the_one_the_other_implementations_report() {
        use crate::output::{and, xor};
        let place = |n: &str| out_place(&Place::<i32>::new(n));
        let spec = and(vec![
            xor(vec![place("A"), and(vec![place("P"), place("P")])]),
            place("Q"),
            place("Q"),
        ]);
        let err = std::panic::catch_unwind(|| Transition::builder("t").output(spec).build())
            .expect_err("a duplicate in one AND branch must be rejected");
        let message = err.downcast_ref::<String>().cloned().unwrap_or_default();
        assert!(message.contains("names place 'P' twice"), "{message}");
    }

    /// IO-011: the duplicate check is linear in the spec. An AND of 64 two-way XORs
    /// has 2^64 branches; enumerating them would never return.
    #[test]
    fn the_duplicate_check_does_not_enumerate_branches() {
        use crate::output::{and, xor};
        let place = |n: String| out_place(&Place::<i32>::new(n));
        let wide = || {
            and((0..64)
                .map(|i| xor(vec![place(format!("a{i}")), place(format!("b{i}"))]))
                .collect())
        };
        Transition::builder("t").output(wide()).build();
        let mut children = vec![wide()];
        children.push(place("b63".into()));
        let err = std::panic::catch_unwind(|| {
            Transition::builder("t").output(and(children)).build()
        })
        .expect_err("b63 is named twice in some branch");
        let message = err.downcast_ref::<String>().cloned().unwrap_or_default();
        assert!(message.contains("names place 'b63' twice"), "{message}");
    }

    #[test]
    fn action_timeout_detected() {
        let p = Place::<i32>::new("timeout");
        let t = Transition::builder("test")
            .output(crate::output::timeout_place(5000, &p))
            .build();
        assert_eq!(t.action_timeout(), Some(5000));
    }

    #[test]
    fn no_action_timeout() {
        let p = Place::<i32>::new("out");
        let t = Transition::builder("test").output(out_place(&p)).build();
        assert_eq!(t.action_timeout(), None);
    }

    // ---- IO-002 / IO-004 / NU-020: arcs the builders reject, written out directly ----

    fn join_with(b_input: In, ms: crate::match_spec::MatchSpec) -> Transition {
        Transition::builder("join")
            .input(one(&Place::<String>::new("A")))
            .input(b_input)
            .output(out_place(&Place::<String>::new("merged")))
            .match_spec(ms)
            .build()
    }

    fn key_ab() -> crate::match_spec::MatchSpec {
        use crate::match_spec::MatchSpec;
        use crate::name::NameId;
        let key = |s: &String| NameId::new(s.clone());
        MatchSpec::builder()
            .key(&Place::<String>::new("A"), key)
            .key(&Place::<String>::new("B"), key)
            .build()
    }

    /// `In::Exactly { count: 0 }` is a public variant, so `exactly()`'s check does not
    /// cover it. Route B read such a join key as always satisfied and proved
    /// `DeadlockFree` for a join the executor never fires.
    #[test]
    #[should_panic(expected = "input 'B' of transition 'join' requires 0 tokens")]
    fn an_exactly_zero_input_panics() {
        use crate::place::PlaceRef;
        join_with(In::Exactly { place: PlaceRef::new("B"), count: 0 }, key_ab());
    }

    #[test]
    #[should_panic(expected = "input 'B' of transition 'join' requires 0 tokens")]
    fn an_at_least_zero_input_panics() {
        use crate::place::PlaceRef;
        join_with(In::AtLeast { place: PlaceRef::new("B"), minimum: 0 }, key_ab());
    }

    /// `MatchSpec::from_keys` (the FFI path) skips the builder, so the transition
    /// checks the keys too ([NU-020]).
    #[test]
    #[should_panic(expected = "MatchSpec correlates input place 'A' twice")]
    fn a_place_keyed_twice_through_from_keys_panics() {
        use crate::match_spec::MatchSpec;
        let keys = key_ab().keys().to_vec();
        let ms = MatchSpec::from_keys(vec![keys[0].clone(), keys[0].clone()]);
        join_with(one(&Place::<String>::new("B")), ms);
    }
}
