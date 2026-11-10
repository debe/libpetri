use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::action::{BoxedAction, passthrough};
use crate::arc::{Inhibitor, Read, Reset};
use crate::input::In;
use crate::match_spec::MatchSpec;
use crate::output::{
    Out, all_places, ambiguous_branches, duplicate_in_branch, find_forward_inputs, find_timeout,
    forward_outside_timeout, timeout_count, xor_inside_timeout,
};
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

/// The [EXEC-012] input-and-read rejection: a read of a place the same firing
/// consumes from has no coherent semantics. The spec fixes the text, byte for
/// byte, for every implementation.
pub fn input_and_read_message(transition: &str, place: &str) -> String {
    format!(
        "Transition '{transition}' declares an input arc and a read arc on place '{place}'. A \
         read of a place the same firing consumes from has no coherent semantics and is \
         rejected (EXEC-012). Remove the read arc: the input arc already hands the consumed \
         tokens to the action."
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
    /// - Panics if a read arc names an input place (**EXEC-012**): the read would
    ///   peek the place after the firing's own consumption. Remove the read arc;
    ///   the input arc already hands the consumed tokens to the action. Checked
    ///   after the input checks and before the timing and output-spec checks; the
    ///   first such read arc in declaration order is named.
    /// - Panics if one output branch names a place twice (**IO-011**): outputs are
    ///   sets of places, so `and(P, P)` is not two tokens into `P`.
    /// - Panics if an input requires no token (`In::Exactly { count: 0 }`,
    ///   `In::AtLeast { minimum: 0 }`; **IO-002**, **IO-004**).
    /// - Panics if the match specification keys one place twice (**NU-020**).
    /// - Panics if the output spec holds more than one `Timeout` node, nested or
    ///   not (**IO-013**).
    /// - Panics if the child of the `Timeout` node holds an `Xor` node at any
    ///   depth (**IO-013**): the timeout outcome deposits one fixed set of places.
    /// - Panics if a `ForwardInput` is not inside the child of a `Timeout`
    ///   (**IO-014**).
    /// - Panics if ForwardInput references a non-input place (**IO-014** AC3).
    /// - Panics if two output branches claim the same set of places (**IO-012**):
    ///   no write could tell them apart.
    ///
    /// The output-spec checks run in that order, IO-011 first, and the first
    /// failing one reports, with the message every implementation uses.
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

        // [EXEC-012]: a read arc on an input place would peek the place after this
        // firing's own consumption, which can leave it empty although the transition
        // was enabled. Runs after every input check (CORE-030 first, so two inputs
        // plus a read on one place report CORE-030) and names the place of the first
        // read arc, in declaration order, that is also an input place.
        if let Some(r) = self.reads.iter().find(|r| seen_inputs.contains(r.place.name())) {
            panic!("{}", input_and_read_message(&self.name, r.place.name()));
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

        if let Some(ref out) = self.output_spec {
            // [IO-013]: one budget per action, so at most one Timeout node, nested or not.
            let timeouts = timeout_count(out);
            if timeouts >= 2 {
                panic!(
                    "output spec of transition '{}' has {} Timeout nodes; an output spec has \
                     at most one, nested or not (IO-013)",
                    self.name, timeouts
                );
            }

            // [IO-013]: the executor makes the timeout deposit, so nothing chooses
            // among alternatives inside the Timeout child.
            if xor_inside_timeout(out) {
                panic!(
                    "output spec of transition '{}' has a Xor node inside the child of its \
                     Timeout node; the timeout outcome deposits one fixed set of places (IO-013)",
                    self.name
                );
            }

            // [IO-014]: a forward deposits only on the timeout outcome.
            if let Some((from, to)) = forward_outside_timeout(out) {
                panic!(
                    "output spec of transition '{}' uses ForwardInput('{}', '{}') outside the \
                     child of a Timeout node; a forward deposits only on the timeout outcome \
                     (IO-014)",
                    self.name,
                    from.name(),
                    to.name()
                );
            }

            // [IO-014] AC3: a forward names an input place.
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

            // [IO-012]: two distinct assignments claiming one set of places leave no
            // write that tells them apart. Runs after IO-011, which it relies on.
            if let Some(amb) = ambiguous_branches(out) {
                let places: Vec<&str> = amb.places.iter().map(|p| p.name()).collect();
                panic!(
                    "output spec of transition '{}' is ambiguous: output branches {} and {} \
                     both claim {{{}}}; no write can tell them apart (IO-012)",
                    self.name,
                    amb.first,
                    amb.second,
                    places.join(", ")
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
            .output(crate::output::timeout(10, crate::output::forward_input(&from, &to)))
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

    fn build_panic_message(build: impl FnOnce() -> Transition + std::panic::UnwindSafe) -> String {
        let err = std::panic::catch_unwind(build).expect_err("the transition must be rejected");
        err.downcast_ref::<String>()
            .cloned()
            .or_else(|| err.downcast_ref::<&str>().map(|s| s.to_string()))
            .expect("a string panic payload")
    }

    /// EXEC-012 AC2 (D15): an input arc and a read arc on one place are rejected
    /// at build with the spec's message, byte for byte, whatever the input
    /// cardinality.
    #[test]
    fn exec012_input_and_read_on_one_place_rejected_at_build() {
        use crate::arc::read;
        use crate::input::{all, at_least, exactly};
        let expected = "Transition 't' declares an input arc and a read arc on place 'p'. A read \
                        of a place the same firing consumes from has no coherent semantics and \
                        is rejected (EXEC-012). Remove the read arc: the input arc already hands \
                        the consumed tokens to the action.";
        let p = Place::<i32>::new("p");
        for input in [one(&p), all(&p), exactly(2, &p), at_least(1, &p)] {
            let msg = build_panic_message(|| {
                Transition::builder("t").input(input).read(read(&p)).build()
            });
            assert_eq!(msg, expected);
            assert_eq!(msg, input_and_read_message("t", "p"));
        }
    }

    /// EXEC-012 AC3 (D15): the first read arc in declaration order whose place is
    /// an input place is named; two inputs plus a read on one place report
    /// CORE-030, which runs first.
    #[test]
    fn exec012_names_first_offending_read_and_core030_reports_first() {
        use crate::arc::read;
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let msg = build_panic_message(|| {
            Transition::builder("t")
                .input(one(&a))
                .input(one(&b))
                .read(read(&b))
                .read(read(&a))
                .build()
        });
        assert_eq!(msg, input_and_read_message("t", "b"));

        let p = Place::<i32>::new("p");
        let msg = build_panic_message(|| {
            Transition::builder("t")
                .input(one(&p))
                .input(crate::input::exactly(2, &p))
                .read(read(&p))
                .build()
        });
        assert_eq!(msg, duplicate_input_message("t", "p"));
    }

    /// EXEC-012 AC4 (D15): an input and a read on different places, and a read
    /// plus a reset on one place, still build.
    #[test]
    fn exec012_input_and_read_on_different_places_and_read_with_reset_build() {
        use crate::arc::{read, reset};
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let t = Transition::builder("t").input(one(&a)).read(read(&b)).build();
        assert_eq!(t.reads().len(), 1);
        let t = Transition::builder("t").read(read(&a)).reset(reset(&a)).build();
        assert_eq!(t.reads().len(), 1);
        assert_eq!(t.resets().len(), 1);
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

    /// [TIME-001] AC4, [TIME-003]: a deadline written out past the maximum duration is
    /// rejected at build with the factory's message.
    #[test]
    #[should_panic(
        expected = "Deadline must be at most MAX_DURATION_MS (3153600000000): 3153600000001"
    )]
    fn a_deadline_written_out_past_the_maximum_is_rejected_at_build() {
        use crate::timing::{MAX_DURATION_MS, Timing};
        with_timing(Timing::Deadline {
            by_ms: MAX_DURATION_MS + 1,
        });
    }

    /// [TIME-001] AC4, [TIME-005]: a window written out with its latest bound past the
    /// maximum duration is rejected at build with the factory's message.
    #[test]
    #[should_panic(
        expected = "Latest must be at most MAX_DURATION_MS (3153600000000): 3153600000001"
    )]
    fn a_window_latest_written_out_past_the_maximum_is_rejected_at_build() {
        use crate::timing::{MAX_DURATION_MS, Timing};
        with_timing(Timing::Window {
            earliest_ms: MAX_DURATION_MS,
            latest_ms: MAX_DURATION_MS + 1,
        });
    }

    #[test]
    fn a_valid_timing_written_out_builds() {
        use crate::timing::{MAX_DURATION_MS, Timing};
        for timing in [
            Timing::Immediate,
            Timing::Deadline { by_ms: 1 },
            Timing::Deadline {
                by_ms: MAX_DURATION_MS,
            },
            Timing::Delayed {
                after_ms: MAX_DURATION_MS,
            },
            Timing::Window {
                earliest_ms: MAX_DURATION_MS,
                latest_ms: MAX_DURATION_MS,
            },
            Timing::Window {
                earliest_ms: 0,
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

    /// IO-011 AC5: `And(Xor(A, B), Xor(B, A))` names `B`, the place the walk reports
    /// first (the second child's pooled `B` is already named by the first child), not
    /// `A`, the repeat of the first repeating branch in enumeration order.
    #[test]
    fn io_011_ac5_the_walk_names_b_in_and_of_two_xors() {
        use crate::output::{and, xor};
        let place = |n: &str| out_place(&Place::<i32>::new(n));
        let spec = and(vec![
            xor(vec![place("A"), place("B")]),
            xor(vec![place("B"), place("A")]),
        ]);
        let err = std::panic::catch_unwind(|| Transition::builder("t").output(spec).build())
            .expect_err("And(Xor(A, B), Xor(B, A)) names a place twice in some branch");
        let message = "output spec of transition 't' names place 'B' twice in one AND branch; \
                       outputs are sets (IO-015) — a weighted output is not supported, add a \
                       second place or a follow-up transition";
        assert_eq!(err.downcast_ref::<String>().map(String::as_str), Some(message));
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

    // ---- IO-012 / IO-013 / IO-014: output specs rejected at build ----

    fn leaf(n: &str) -> Out {
        out_place(&Place::<i32>::new(n))
    }

    fn fwd(from: &str, to: &str) -> Out {
        crate::output::forward_input(&Place::<i32>::new(from), &Place::<i32>::new(to))
    }

    /// Builds `t` with input `a` (so a forward from `a` is legal) and `spec`, and
    /// returns the panic message, or `None` when it builds.
    fn build_error(spec: Out) -> Option<String> {
        let built = std::panic::catch_unwind(|| {
            Transition::builder("t")
                .input(one(&Place::<i32>::new("a")))
                .output(spec)
                .build()
        });
        built.err().map(|e| {
            e.downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default()
        })
    }

    fn ambiguity(i: u32, j: u32, places: &str) -> String {
        format!(
            "output spec of transition 't' is ambiguous: output branches {i} and {j} both \
             claim {{{places}}}; no write can tell them apart (IO-012)"
        )
    }

    /// IO-012 AC5: two distinct assignments claiming one set of places are rejected
    /// at build, naming the first pair in branch order and the places of the first.
    #[test]
    fn io_012_ac5_ambiguous_output_specs_are_rejected() {
        use crate::output::{and, timeout, xor};
        let cases = [
            (xor(vec![leaf("P"), leaf("P")]), ambiguity(0, 1, "P")),
            (
                xor(vec![and(vec![leaf("A"), leaf("B")]), and(vec![leaf("B"), leaf("A")])]),
                ambiguity(0, 1, "A, B"),
            ),
            (xor(vec![leaf("A"), xor(vec![leaf("A"), leaf("B")])]), ambiguity(0, 1, "A")),
            (and(vec![leaf("Q"), xor(vec![leaf("P"), leaf("P")])]), ambiguity(0, 1, "Q, P")),
            (
                xor(vec![
                    and(vec![leaf("A"), xor(vec![leaf("B"), leaf("C")])]),
                    and(vec![leaf("A"), leaf("B")]),
                ]),
                ambiguity(0, 2, "A, B"),
            ),
            (xor(vec![leaf("P"), timeout(10, leaf("P"))]), ambiguity(0, 1, "P")),
            (xor(vec![leaf("B"), timeout(10, fwd("a", "B"))]), ambiguity(0, 1, "B")),
        ];
        for (spec, message) in cases {
            let shown = format!("{spec:?}");
            assert_eq!(build_error(spec), Some(message), "{shown}");
        }
    }

    /// IO-012 AC5: overlapping but distinct alternatives build.
    #[test]
    fn io_012_ac5_distinct_alternatives_build() {
        use crate::output::{and, timeout, xor};
        for spec in [
            xor(vec![
                and(vec![leaf("A"), leaf("B"), leaf("C")]),
                and(vec![leaf("A"), leaf("B")]),
            ]),
            xor(vec![and(vec![leaf("P"), leaf("A")]), and(vec![leaf("P"), leaf("B")])]),
            xor(vec![leaf("A"), timeout(10, leaf("B"))]),
        ] {
            let shown = format!("{spec:?}");
            assert_eq!(build_error(spec), None, "{shown}");
        }
    }

    /// IO-012: the reported pair is the first in branch order, with indices in the
    /// global numbering of nested `And`s (first child slowest) and `Xor`s.
    #[test]
    fn io_012_the_first_pair_in_branch_order_is_reported() {
        use crate::output::{and, xor};
        // Branches: [X,A] [X,B] [X,A'] [Y,A] [Y,B] [Y,A'] with A' = A: (0, 2) first.
        let spec = and(vec![
            xor(vec![leaf("X"), leaf("Y")]),
            xor(vec![leaf("A"), leaf("B"), leaf("A")]),
        ]);
        assert_eq!(build_error(spec), Some(ambiguity(0, 2, "X, A")));
        // A repeat in the first child shows at stride 3: (0, 3).
        let spec = and(vec![
            xor(vec![leaf("X"), leaf("X")]),
            xor(vec![leaf("A"), leaf("B"), leaf("C")]),
        ]);
        assert_eq!(build_error(spec), Some(ambiguity(0, 3, "X, A")));
        // A later alternative that repeats a deep branch of an earlier one.
        let spec = xor(vec![
            and(vec![xor(vec![leaf("A"), leaf("B")]), xor(vec![leaf("C"), leaf("D")])]),
            leaf("E"),
            and(vec![leaf("D"), leaf("B")]),
        ]);
        assert_eq!(build_error(spec), Some(ambiguity(3, 5, "B, D")));
    }

    /// IO-012: the ambiguity check is linear on an `And` of many `Xor`s, as IO-011's is.
    #[test]
    fn io_012_the_ambiguity_check_does_not_enumerate_and_branches() {
        use crate::output::{and, xor};
        let wide = |extra: Vec<Out>| {
            let mut children: Vec<Out> = (0..64)
                .map(|i| xor(vec![leaf(&format!("a{i}")), leaf(&format!("b{i}"))]))
                .collect();
            children.extend(extra);
            and(children)
        };
        assert_eq!(build_error(wide(vec![])), None);
        // A repeat in the last child: branches 0 and 1 of 2^65.
        let message = build_error(wide(vec![xor(vec![leaf("z"), leaf("z")])])).unwrap();
        assert!(message.contains("output branches 0 and 1 both claim {a0, "), "{message}");
        // Two alternatives of 2^40 branches that share one place: only the branches
        // inside the other alternative's places are candidates, and there are none.
        let side = |x: &str, y: &str| {
            let mut children = vec![leaf("S")];
            children.extend(
                (0..40).map(|i| xor(vec![leaf(&format!("{x}{i}")), leaf(&format!("{y}{i}"))])),
            );
            and(children)
        };
        let started = std::time::Instant::now();
        assert_eq!(build_error(xor(vec![side("x", "y"), side("u", "v")])), None);
        assert!(started.elapsed() < std::time::Duration::from_secs(5), "{:?}", started.elapsed());
        // An empty And claims no place: two of them are the same set.
        let message = build_error(xor(vec![Out::And(vec![]), Out::And(vec![])])).unwrap();
        assert!(message.contains("output branches 0 and 1 both claim {}"), "{message}");
    }

    /// IO-013 AC7: more than one Timeout node, nested or not, is rejected at build.
    #[test]
    fn io_013_ac7_more_than_one_timeout_is_rejected() {
        use crate::output::{and, timeout, xor};
        let message = "output spec of transition 't' has 2 Timeout nodes; an output spec has at \
                       most one, nested or not (IO-013)";
        for spec in [
            timeout(10, timeout(20, leaf("P"))),
            xor(vec![timeout(10, leaf("A")), timeout(20, leaf("B"))]),
            and(vec![timeout(10, leaf("A")), xor(vec![leaf("B"), timeout(20, leaf("C"))])]),
        ] {
            let shown = format!("{spec:?}");
            assert_eq!(build_error(spec).as_deref(), Some(message), "{shown}");
        }
        let three = xor(vec![
            timeout(10, leaf("A")),
            timeout(20, leaf("B")),
            timeout(30, leaf("C")),
        ]);
        assert!(build_error(three).unwrap().contains("has 3 Timeout nodes"));
        for spec in [
            xor(vec![leaf("A"), timeout(10, leaf("B"))]),
            timeout(10, and(vec![leaf("A"), leaf("B")])),
        ] {
            let shown = format!("{spec:?}");
            assert_eq!(build_error(spec), None, "{shown}");
        }
    }

    /// IO-013 AC8: an `Xor` at any depth of the `Timeout` child is rejected at build;
    /// an `Xor` outside the `Timeout` builds.
    #[test]
    fn io_013_ac8_a_xor_inside_the_timeout_child_is_rejected() {
        use crate::output::{and, timeout, xor};
        let message = "output spec of transition 't' has a Xor node inside the child of its \
                       Timeout node; the timeout outcome deposits one fixed set of places \
                       (IO-013)";
        for spec in [
            timeout(10, xor(vec![leaf("A"), leaf("B")])),
            xor(vec![
                leaf("C"),
                timeout(10, and(vec![leaf("A"), xor(vec![leaf("B"), leaf("D")])])),
            ]),
        ] {
            let shown = format!("{spec:?}");
            assert_eq!(build_error(spec).as_deref(), Some(message), "{shown}");
        }
        for spec in [
            xor(vec![leaf("A"), timeout(10, leaf("B"))]),
            timeout(10, and(vec![leaf("A"), fwd("a", "B")])),
        ] {
            let shown = format!("{spec:?}");
            assert_eq!(build_error(spec), None, "{shown}");
        }
    }

    /// IO-014 AC7: a ForwardInput outside the child of a Timeout is rejected at build,
    /// the first in pre-order named.
    #[test]
    fn io_014_ac7_a_forward_outside_a_timeout_child_is_rejected() {
        use crate::output::{and, timeout, xor};
        let message = "output spec of transition 't' uses ForwardInput('a', 'b') outside the \
                       child of a Timeout node; a forward deposits only on the timeout outcome \
                       (IO-014)";
        for spec in [
            fwd("a", "b"),
            xor(vec![leaf("c"), fwd("a", "b")]),
            and(vec![leaf("c"), xor(vec![leaf("e"), fwd("a", "b")])]),
            xor(vec![timeout(10, fwd("a", "x")), fwd("a", "b"), fwd("a", "y")]),
        ] {
            let shown = format!("{spec:?}");
            assert_eq!(build_error(spec).as_deref(), Some(message), "{shown}");
        }
        for spec in [
            timeout(10, fwd("a", "b")),
            xor(vec![leaf("c"), timeout(10, and(vec![leaf("e"), fwd("a", "b")]))]),
        ] {
            let shown = format!("{spec:?}");
            assert_eq!(build_error(spec), None, "{shown}");
        }
    }

    /// The output-spec checks run in one order in every implementation, the first
    /// failing one reporting: IO-011, IO-013 (Timeout count, then Xor in the Timeout
    /// child), IO-014 placement, IO-014 AC3, IO-012.
    #[test]
    fn output_spec_checks_report_in_order() {
        use crate::output::{and, timeout, xor};
        // IO-011 before IO-014 placement.
        let e = build_error(and(vec![leaf("R"), fwd("a", "R")])).unwrap();
        assert!(e.contains("names place 'R' twice in one AND branch"), "{e}");
        // IO-013 before IO-014 placement.
        let e = build_error(and(vec![
            fwd("a", "b"),
            timeout(10, leaf("c")),
            timeout(20, leaf("d")),
        ]))
        .unwrap();
        assert!(e.contains("has 2 Timeout nodes"), "{e}");
        // IO-013 Timeout count before IO-013 Xor in the Timeout child.
        let e = build_error(and(vec![
            timeout(10, xor(vec![leaf("c"), leaf("d")])),
            timeout(20, leaf("e")),
        ]))
        .unwrap();
        assert!(e.contains("has 2 Timeout nodes"), "{e}");
        // IO-011 before IO-013 Xor in the Timeout child.
        let e = build_error(timeout(10, and(vec![leaf("c"), xor(vec![leaf("c"), leaf("d")])])))
            .unwrap();
        assert!(e.contains("names place 'c' twice in one AND branch"), "{e}");
        // IO-013 Xor in the Timeout child before IO-014 placement and AC3.
        let e = build_error(and(vec![
            fwd("not-an-input", "b"),
            timeout(10, xor(vec![leaf("c"), leaf("d")])),
        ]))
        .unwrap();
        assert!(e.contains("has a Xor node inside the child of its Timeout node"), "{e}");
        // IO-014 placement before the non-input check.
        let e = build_error(fwd("not-an-input", "b")).unwrap();
        assert!(e.contains("uses ForwardInput('not-an-input', 'b') outside"), "{e}");
        // The non-input check before IO-012.
        let e = build_error(xor(vec![leaf("b"), timeout(10, fwd("other", "b"))])).unwrap();
        assert_eq!(e, "Transition 't': ForwardInput references non-input place 'other'");
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
