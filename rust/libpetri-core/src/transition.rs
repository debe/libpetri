use std::collections::HashSet;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::action::{BoxedAction, passthrough};
use crate::arc::{Inhibitor, Read, Reset};
use crate::input::In;
use crate::output::{Out, all_places, find_forward_inputs, find_timeout};
use crate::place::PlaceRef;
use crate::timing::{Timing, immediate};

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
    timing: Timing,
    action_timeout: Option<u64>,
    action: BoxedAction,
    priority: i32,
    input_places: HashSet<PlaceRef>,
    read_places: HashSet<PlaceRef>,
    output_places: HashSet<PlaceRef>,
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
    timing: Timing,
    action: BoxedAction,
    priority: i32,
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
            timing: immediate(),
            action: passthrough(),
            priority: 0,
        }
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

    /// Set timing specification.
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
    /// Panics if ForwardInput references a non-input place.
    pub fn build(self) -> Transition {
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
            timing: self.timing,
            action_timeout,
            action: self.action,
            priority: self.priority,
            input_places,
            read_places,
            output_places,
        }
    }
}

/// Creates a new transition with a different action while preserving all arc specs.
pub(crate) fn rebuild_with_action(t: &Transition, action: BoxedAction) -> Transition {
    let mut builder = Transition::builder(Arc::clone(&t.name))
        .timing(t.timing)
        .priority(t.priority)
        .action(action)
        .inputs(t.input_specs.clone())
        .inhibitors(t.inhibitors.clone())
        .reads(t.reads.clone())
        .resets(t.resets.clone());

    if let Some(ref out) = t.output_spec {
        builder = builder.output(out.clone());
    }

    builder.build()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::one;
    use crate::output::out_place;
    use crate::place::Place;

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
}
