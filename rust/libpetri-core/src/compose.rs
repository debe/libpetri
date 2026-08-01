//! Typed binding builder for [`crate::petri_net::PetriNetBuilder::compose_with`],
//! per `spec/11-modular-composition.md` requirements **MOD-020** (composition
//! operation), **MOD-022** (type compatibility), and **MOD-023** (composition
//! produces a flat net).
//!
//! ## Error-handling contract
//!
//! Composition uses **panic-on-user-error**, not `Result`. Duplicate port or
//! channel bindings, unknown port names, type mismatches between caller place
//! and declared interface, and duplicate fusion keys all panic with a
//! descriptive message. The entry points where panics may originate are
//! [`crate::petri_net::PetriNetBuilder::compose`] and
//! [`crate::petri_net::PetriNetBuilder::compose_with`].
//!
//! This is a **deliberate** design choice, not an oversight — please do not
//! "refactor to `Result`" as a drive-by cleanup. The rationale is:
//!
//! - **Cross-language API parity.** The Java implementation throws
//!   `IllegalArgumentException` and the TypeScript implementation throws
//!   `Error` for the same conditions; mirroring that here keeps the three
//!   surfaces uniform.
//! - **Programmer bugs, not runtime conditions.** A duplicate binding or
//!   unknown port is a build-time wiring mistake catchable in dev/CI by the
//!   test suite, not a recoverable runtime fault.
//!
//! ## Status
//!
//! Port composition is fully implemented (this task). Channel composition is
//! deferred to task #21: recording channel bindings here is permitted, but
//! [`crate::petri_net::PetriNetBuilder::compose_with`] panics when any channel
//! binding is present until task #21 lands the merge primitive.
//!
//! ## Identity
//!
//! [`ComposeBindingsBuilder`] is a write-only collector: callers register
//! port and channel bindings against an instance's interface, and the host
//! builder consumes the recorded mappings as it merges the instance into the
//! enclosing net. The builder is constructed by
//! [`crate::petri_net::PetriNetBuilder::compose_with`] and supplied to the
//! caller's closure; direct construction is not part of the public API.

use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::Arc;

use crate::place::{Place, PlaceRef};
use crate::transition::Transition;

/// Typed binding collector for
/// [`crate::petri_net::PetriNetBuilder::compose_with`], per **MOD-020** and
/// **MOD-022**.
///
/// Callers register port bindings via [`Self::bind_port`] and channel
/// bindings via [`Self::bind_channel`]. The host builder drains the recorded
/// mappings inside `compose_with` to build the place-substitution map and (in
/// task #21) the channel-merge work list.
///
/// ## Lifetime parameter
///
/// The `'a` lifetime ties the builder to the enclosing
/// [`crate::petri_net::PetriNetBuilder::compose_with`] callback frame so the
/// builder cannot escape the closure. The `PhantomData<&'a ()>` field is the
/// only carrier of `'a`; it costs nothing at runtime.
pub struct ComposeBindingsBuilder<'a> {
    port_bindings: HashMap<Arc<str>, PlaceRef>,
    /// channel name -> caller-side transition (cloned by reference; cheap
    /// because [`Transition`] holds its arcs by value but actions are `Arc`s).
    channel_bindings: HashMap<Arc<str>, Transition>,
    _marker: PhantomData<&'a ()>,
}

impl<'a> ComposeBindingsBuilder<'a> {
    /// Crate-internal constructor — instances are produced exclusively by
    /// [`crate::petri_net::PetriNetBuilder::compose_with`].
    pub(crate) fn new() -> Self {
        Self {
            port_bindings: HashMap::new(),
            channel_bindings: HashMap::new(),
            _marker: PhantomData,
        }
    }

    /// Binds the named interface port to the supplied caller place per
    /// **MOD-020**.
    ///
    /// The port name is the **original** (pre-prefix) name as declared in the
    /// subnet's [`crate::interface::Interface`]. The typed `<T>` parameter
    /// gives the caller an ergonomic compile-time shape — the actual
    /// token-type compatibility check (per **MOD-022**) happens at compose
    /// time inside [`crate::petri_net::PetriNetBuilder::compose_with`], where
    /// the [`crate::instance::Instance::port`] machinery has access to the
    /// declared `TypeId`.
    ///
    /// # Panics
    /// Panics if the port name was already bound on this builder. (Mirrors the
    /// Java `IllegalArgumentException` and TypeScript `Error` idioms.)
    pub fn bind_port<T: 'static>(
        &mut self,
        port_name: impl Into<Arc<str>>,
        caller_place: &Place<T>,
    ) -> &mut Self {
        let name: Arc<str> = port_name.into();
        if self.port_bindings.contains_key(&name) {
            panic!("Port '{}' is already bound", name);
        }
        self.port_bindings.insert(name, caller_place.as_ref());
        self
    }

    /// Records a synchronous channel binding per **MOD-021**: at compose time
    /// (task #21), the instance-side renamed channel transition is merged
    /// with `caller_transition` into a single transition in the resulting
    /// flat net.
    ///
    /// **Status**: channel composition is implemented in task #21. Recording
    /// a channel binding here is permitted, but
    /// [`crate::petri_net::PetriNetBuilder::compose_with`] currently panics
    /// when any channel binding is present.
    ///
    /// # Panics
    /// Panics if the channel name was already bound on this builder.
    pub fn bind_channel(
        &mut self,
        channel_name: impl Into<Arc<str>>,
        caller_transition: &Transition,
    ) -> &mut Self {
        let name: Arc<str> = channel_name.into();
        if self.channel_bindings.contains_key(&name) {
            panic!("Channel '{}' is already bound", name);
        }
        self.channel_bindings.insert(name, caller_transition.clone());
        self
    }

    /// Returns a reference to the recorded port bindings (test-only — the
    /// production path uses [`Self::into_parts`] to move the maps).
    #[cfg(test)]
    pub(crate) fn port_bindings(&self) -> &HashMap<Arc<str>, PlaceRef> {
        &self.port_bindings
    }

    /// Returns a reference to the recorded channel bindings (test-only — the
    /// production path uses [`Self::into_parts`] to move the maps).
    #[cfg(test)]
    pub(crate) fn channel_bindings(&self) -> &HashMap<Arc<str>, Transition> {
        &self.channel_bindings
    }

    /// Consumes the builder and returns the recorded `(port_bindings,
    /// channel_bindings)` maps by value — used by
    /// [`crate::petri_net::PetriNetBuilder::compose_with`] to move the maps
    /// into `compose_internal` without an intermediate clone.
    pub(crate) fn into_parts(
        self,
    ) -> (
        HashMap<Arc<str>, PlaceRef>,
        HashMap<Arc<str>, Transition>,
    ) {
        (self.port_bindings, self.channel_bindings)
    }
}

#[cfg(test)]
mod tests {
    //! Inline unit tests for [`ComposeBindingsBuilder`] and end-to-end
    //! port-composition behaviour on [`crate::petri_net::PetriNetBuilder`].
    //!
    //! Runtime-driven (executor) integration tests live in the umbrella
    //! `libpetri` crate's `tests/` directory — `libpetri-core` does not depend
    //! on `libpetri-runtime` (and adding such a dev-dep would create a cycle).

    use super::*;

    use std::collections::HashSet;

    use crate::input::one;
    use crate::output::{and_places, out_place};
    use crate::petri_net::PetriNet;
    use crate::subnet_def::SubnetDef;
    use crate::transition::Transition;

    // ============================================================
    //  Fixture builders mirroring TS/Java SubnetFixtures.
    //  Local to libpetri-core's compose tests; duplicated under libpetri's
    //  integration tests for executor-driven coverage.
    // ============================================================

    fn producer() -> SubnetDef<()> {
        let next_item = Place::<String>::new("nextItem");
        let output = Place::<String>::new("output");

        let produce = Transition::builder("produce")
            .input(one(&next_item))
            .output(out_place(&output))
            .build();

        SubnetDef::<()>::builder("Producer")
            .place(&next_item)
            .transition(produce)
            .output_port("output", &output)
            .build()
    }

    fn bounded_buffer(capacity: usize) -> SubnetDef<()> {
        assert!(capacity >= 1, "capacity must be >= 1, got: {capacity}");

        let put = Place::<String>::new("put");
        let get = Place::<String>::new("get");
        let items = Place::<String>::new("items");
        let slots = Place::<String>::new("slots");

        let enqueue = Transition::builder("enqueue")
            .input(one(&put))
            .input(one(&slots))
            .output(out_place(&items))
            .build();

        let dequeue = Transition::builder("dequeue")
            .input(one(&items))
            .output(and_places(&[&get.as_ref(), &slots.as_ref()]))
            .build();

        SubnetDef::<()>::builder(format!("BoundedBuffer-{capacity}"))
            .place(&items)
            .place(&slots)
            .transition(enqueue)
            .transition(dequeue)
            .input_port("put", &put)
            .output_port("get", &get)
            .build()
    }

    fn consumer() -> SubnetDef<()> {
        let input = Place::<String>::new("input");
        let consumed = Place::<String>::new("consumed");

        let consume = Transition::builder("consume")
            .input(one(&input))
            .output(out_place(&consumed))
            .build();

        SubnetDef::<()>::builder("Consumer")
            .place(&consumed)
            .transition(consume)
            .input_port("input", &input)
            .build()
    }

    fn retry_policy() -> SubnetDef<()> {
        let attempt_count = Place::<String>::new("attemptCount");
        let attempt = Transition::builder("attempt")
            .output(out_place(&attempt_count))
            .build();

        SubnetDef::<()>::builder("RetryPolicy")
            .place(&attempt_count)
            .transition(attempt.clone())
            .channel("attempt", &attempt)
            .build()
    }

    // ============================================================
    //  Builder bookkeeping
    // ============================================================

    #[test]
    fn bind_port_records_the_binding() {
        let p = Place::<String>::new("caller_place");
        let mut b = ComposeBindingsBuilder::new();
        b.bind_port::<String>("port_name", &p);
        assert_eq!(b.port_bindings().len(), 1);
        assert_eq!(
            b.port_bindings().get("port_name").unwrap().name(),
            "caller_place"
        );
    }

    #[test]
    fn bind_port_typed_returns_chainable_reference() {
        let p1 = Place::<String>::new("a");
        let p2 = Place::<i32>::new("b");
        let mut b = ComposeBindingsBuilder::new();
        b.bind_port::<String>("p1", &p1).bind_port::<i32>("p2", &p2);
        assert_eq!(b.port_bindings().len(), 2);
    }

    #[test]
    #[should_panic(expected = "Port 'p' is already bound")]
    fn bind_port_rejects_duplicate_port_name() {
        let p1 = Place::<String>::new("a");
        let p2 = Place::<String>::new("b");
        let mut b = ComposeBindingsBuilder::new();
        b.bind_port::<String>("p", &p1);
        b.bind_port::<String>("p", &p2);
    }

    #[test]
    fn bind_channel_records_the_binding() {
        let t = Transition::builder("caller_t").build();
        let mut b = ComposeBindingsBuilder::new();
        b.bind_channel("ch", &t);
        assert_eq!(b.channel_bindings().len(), 1);
        assert_eq!(b.channel_bindings().get("ch").unwrap().name(), "caller_t");
    }

    #[test]
    #[should_panic(expected = "Channel 'c' is already bound")]
    fn bind_channel_rejects_duplicate_channel_name() {
        let t1 = Transition::builder("t1").build();
        let t2 = Transition::builder("t2").build();
        let mut b = ComposeBindingsBuilder::new();
        b.bind_channel("c", &t1);
        b.bind_channel("c", &t2);
    }

    // ============================================================
    //  PetriNetBuilder::compose — port composition
    // ============================================================

    #[test]
    fn compose_single_port_merges_place() {
        let def = producer();
        let inst = def.instantiate("p1", ());

        let buffer = Place::<String>::new("buffer");
        let mut mappings: HashMap<Arc<str>, PlaceRef> = HashMap::new();
        mappings.insert(Arc::<str>::from("output"), buffer.as_ref());

        let built = PetriNet::builder("host").compose(&inst, mappings).build();

        // The rewritten 'p1/produce' transition must reference 'buffer'
        // (the caller's place) by name on its output arc.
        let produce = built
            .transitions()
            .iter()
            .find(|t| t.name() == "p1/produce")
            .expect("'p1/produce' missing from composed net");
        // Output arc is Out::Place(buffer)
        match produce.output_spec().expect("produce has output spec") {
            crate::output::Out::Place(pr) => assert_eq!(pr.name(), "buffer"),
            other => panic!("expected Out::Place(buffer), got {other:?}"),
        }

        // The renamed instance-side port place 'p1/output' must be gone
        // from the host net — the only arc that referenced it has been
        // rewritten to point at 'buffer'.
        let names: HashSet<&str> = built.places().iter().map(|p| p.name()).collect();
        assert!(!names.contains("p1/output"), "p1/output should be gone");
        assert!(names.contains("buffer"), "caller place must be present");
        // Internal place flows through unchanged.
        assert!(names.contains("p1/nextItem"), "p1/nextItem must be present");
    }

    #[test]
    #[should_panic(expected = "no port named 'nonexistent'")]
    fn compose_unknown_port_panics() {
        let def = producer();
        let inst = def.instantiate("p1", ());
        let some_place = Place::<String>::new("some_place");

        let mut mappings: HashMap<Arc<str>, PlaceRef> = HashMap::new();
        mappings.insert(Arc::<str>::from("nonexistent"), some_place.as_ref());

        let _ = PetriNet::builder("host").compose(&inst, mappings).build();
    }

    #[test]
    fn compose_unknown_port_message_lists_known_ports_and_subnet_name() {
        let def = producer();
        let inst = def.instantiate("p1", ());
        let some_place = Place::<String>::new("some_place");

        let mut mappings: HashMap<Arc<str>, PlaceRef> = HashMap::new();
        mappings.insert(Arc::<str>::from("nonexistent"), some_place.as_ref());

        // catch_unwind requires UnwindSafe captures; Instance/PetriNetBuilder
        // are structurally fine for unwind, so AssertUnwindSafe is OK here.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = PetriNet::builder("host").compose(&inst, mappings);
        }));
        let err = result.expect_err("compose should panic on unknown port");
        let msg: String = err
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| err.downcast_ref::<&'static str>().map(|s| s.to_string()))
            .unwrap_or_default();
        assert!(
            msg.contains("Producer"),
            "panic message must name the subnet: {msg}"
        );
        assert!(
            msg.contains("output"),
            "panic message must list known ports: {msg}"
        );
    }

    #[test]
    fn compose_internal_places_get_their_own_slot() {
        let def = producer();
        let a = def.instantiate("a", ());
        let b = def.instantiate("b", ());

        let buffer = Place::<String>::new("buffer");

        let mut mappings_a: HashMap<Arc<str>, PlaceRef> = HashMap::new();
        mappings_a.insert(Arc::<str>::from("output"), buffer.as_ref());
        let mut mappings_b: HashMap<Arc<str>, PlaceRef> = HashMap::new();
        mappings_b.insert(Arc::<str>::from("output"), buffer.as_ref());

        let built = PetriNet::builder("host")
            .compose(&a, mappings_a)
            .compose(&b, mappings_b)
            .build();

        let names: HashSet<&str> = built.places().iter().map(|p| p.name()).collect();
        // Both internal places get distinct prefixed slots.
        assert!(names.contains("a/nextItem"), "a/nextItem missing");
        assert!(names.contains("b/nextItem"), "b/nextItem missing");
        // The shared port maps to one caller place.
        assert!(names.contains("buffer"), "caller place missing");
        // Renamed port places are gone.
        assert!(!names.contains("a/output"), "a/output should be gone");
        assert!(!names.contains("b/output"), "b/output should be gone");

        // Both 'a/produce' and 'b/produce' transitions exist and are distinct.
        let t_names: HashSet<&str> =
            built.transitions().iter().map(|t| t.name()).collect();
        assert!(t_names.contains("a/produce"));
        assert!(t_names.contains("b/produce"));
    }

    #[test]
    fn compose_channel_binding_replaces_renamed_with_merged() {
        // Per MOD-021: a bound channel fuses the caller-side transition with
        // the renamed instance-side transition into a single merged
        // transition under the caller's name. The renamed name is gone;
        // the caller's name is present.
        let def = retry_policy();
        let inst = def.instantiate("rp1", ());

        let caller_t = Transition::builder("callerSide").build();

        let built = PetriNet::builder("host")
            .compose_with(&inst, |b| {
                b.bind_channel("attempt", &caller_t);
            })
            .build();

        let t_names: HashSet<&str> = built.transitions().iter().map(|t| t.name()).collect();
        assert!(
            t_names.contains("callerSide"),
            "merged transition must carry the caller's name (caller-wins identity)"
        );
        assert!(
            !t_names.contains("rp1/attempt"),
            "renamed instance-side transition must be gone after channel merge"
        );
    }

    #[test]
    #[should_panic(expected = "no channel named 'nonexistent'")]
    fn compose_unknown_channel_panics() {
        let def = retry_policy();
        let inst = def.instantiate("rp1", ());
        let caller_t = Transition::builder("callerSide").build();

        let _ = PetriNet::builder("host")
            .compose_with(&inst, |b| {
                b.bind_channel("nonexistent", &caller_t);
            })
            .build();
    }

    #[test]
    fn compose_unknown_channel_message_lists_known_channels_and_subnet_name() {
        let def = retry_policy();
        let inst = def.instantiate("rp1", ());
        let caller_t = Transition::builder("callerSide").build();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = PetriNet::builder("host").compose_with(&inst, |b| {
                b.bind_channel("nonexistent", &caller_t);
            });
        }));
        let err = result.expect_err("compose_with must panic on unknown channel");
        let msg: String = err
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| err.downcast_ref::<&'static str>().map(|s| s.to_string()))
            .unwrap_or_default();
        assert!(
            msg.contains("RetryPolicy"),
            "panic message must name the subnet: {msg}"
        );
        assert!(
            msg.contains("attempt"),
            "panic message must list known channels: {msg}"
        );
    }

    #[test]
    fn compose_typed_bindings_form() {
        // A subnet with one typed port; ensure it binds through the typed
        // bind_port::<String> API and the rewrite still happens.
        let def = producer();
        let inst = def.instantiate("p1", ());
        let buffer = Place::<String>::new("caller_buffer");

        let built = PetriNet::builder("host")
            .compose_with(&inst, |b| {
                b.bind_port::<String>("output", &buffer);
            })
            .build();

        let produce = built
            .transitions()
            .iter()
            .find(|t| t.name() == "p1/produce")
            .expect("'p1/produce' must exist");
        match produce.output_spec().expect("produce has output spec") {
            crate::output::Out::Place(pr) => assert_eq!(pr.name(), "caller_buffer"),
            other => panic!("expected Out::Place(caller_buffer), got {other:?}"),
        }
    }

    #[test]
    fn compose_typed_multiple_typed_bindings_form() {
        // A subnet with two typed ports of different types; ensure both
        // typed signatures bind through cleanly.
        let in_p = Place::<String>::new("in");
        let out_p = Place::<i32>::new("out");
        let t = Transition::builder("forward")
            .input(one(&in_p))
            .output(out_place(&out_p))
            .build();
        let def = SubnetDef::<()>::builder("TwoPort")
            .transition(t)
            .input_port("in", &in_p)
            .output_port("out", &out_p)
            .build();
        let inst = def.instantiate("tp1", ());

        let caller_in = Place::<String>::new("caller_in");
        let caller_out = Place::<i32>::new("caller_out");

        let built = PetriNet::builder("host")
            .compose_with(&inst, |b| {
                b.bind_port::<String>("in", &caller_in)
                    .bind_port::<i32>("out", &caller_out);
            })
            .build();

        let forward = built
            .transitions()
            .iter()
            .find(|t| t.name() == "tp1/forward")
            .expect("'tp1/forward' must exist");
        match &forward.input_specs()[0] {
            crate::input::In::One { place, .. } => assert_eq!(place.name(), "caller_in"),
            other => panic!("expected In::One, got {other:?}"),
        }
        match forward.output_spec().expect("forward has output spec") {
            crate::output::Out::Place(pr) => assert_eq!(pr.name(), "caller_out"),
            other => panic!("expected Out::Place(caller_out), got {other:?}"),
        }
    }

    #[test]
    fn compose_unbound_channel_flows_through_as_renamed_transition() {
        // Channels declared in iface but not bound flow through as ordinary
        // renamed transitions per MOD-021 (channel 'attempt' -> 'rp1/attempt').
        let def = retry_policy();
        let inst = def.instantiate("rp1", ());

        // No channel binding recorded — compose succeeds.
        let built = PetriNet::builder("host").compose_with(&inst, |_| {}).build();

        let t_names: HashSet<&str> =
            built.transitions().iter().map(|t| t.name()).collect();
        assert!(
            t_names.contains("rp1/attempt"),
            "unbound channel transition must flow through with prefix"
        );
    }

    #[test]
    fn compose_producer_buffer_consumer_structurally_wires_pipeline() {
        // Structural-only end-to-end test: build the producer -> buffer ->
        // consumer pipeline via three compose calls, then verify the rewritten
        // arc places land on the caller-side wiring places. Executor-driven
        // coverage of the same pipeline lives in libpetri/tests/compose_e2e.rs
        // (the runtime crate is not a dev-dep of libpetri-core).
        let prod_def = producer();
        let buf_def = bounded_buffer(2);
        let cons_def = consumer();

        let prod = prod_def.instantiate("prod", ());
        let buf = buf_def.instantiate("buf", ());
        let cons = cons_def.instantiate("cons", ());

        let producer_to_buffer = Place::<String>::new("producerToBuffer");
        let buffer_to_consumer = Place::<String>::new("bufferToConsumer");

        let net = PetriNet::builder("pipeline")
            .compose_with(&prod, |b| {
                b.bind_port::<String>("output", &producer_to_buffer);
            })
            .compose_with(&buf, |b| {
                b.bind_port::<String>("put", &producer_to_buffer)
                    .bind_port::<String>("get", &buffer_to_consumer);
            })
            .compose_with(&cons, |b| {
                b.bind_port::<String>("input", &buffer_to_consumer);
            })
            .build();

        // All three subnets contributed transitions.
        let t_names: HashSet<&str> =
            net.transitions().iter().map(|t| t.name()).collect();
        assert!(t_names.contains("prod/produce"));
        assert!(t_names.contains("buf/enqueue"));
        assert!(t_names.contains("buf/dequeue"));
        assert!(t_names.contains("cons/consume"));

        // Wiring places are present; renamed port places are gone.
        let p_names: HashSet<&str> = net.places().iter().map(|p| p.name()).collect();
        assert!(p_names.contains("producerToBuffer"));
        assert!(p_names.contains("bufferToConsumer"));
        assert!(!p_names.contains("prod/output"));
        assert!(!p_names.contains("buf/put"));
        assert!(!p_names.contains("buf/get"));
        assert!(!p_names.contains("cons/input"));

        // Internal per-instance places stay distinct.
        assert!(p_names.contains("prod/nextItem"));
        assert!(p_names.contains("buf/items"));
        assert!(p_names.contains("buf/slots"));
        assert!(p_names.contains("cons/consumed"));
    }

    #[test]
    fn compose_two_producer_instances_per_instance_state_structural() {
        // Two instances of the same producer subnet feeding the same buffer:
        // assert every per-instance place is distinct and both producers'
        // transitions reach the shared wiring place 'producerToBuffer'.
        let prod_def = producer();
        let buf_def = bounded_buffer(2);
        let cons_def = consumer();

        let p1 = prod_def.instantiate("p1", ());
        let p2 = prod_def.instantiate("p2", ());
        let buf = buf_def.instantiate("buf", ());
        let cons = cons_def.instantiate("cons", ());

        let producer_to_buffer = Place::<String>::new("producerToBuffer");
        let buffer_to_consumer = Place::<String>::new("bufferToConsumer");

        let net = PetriNet::builder("pipeline")
            .compose_with(&p1, |b| {
                b.bind_port::<String>("output", &producer_to_buffer);
            })
            .compose_with(&p2, |b| {
                b.bind_port::<String>("output", &producer_to_buffer);
            })
            .compose_with(&buf, |b| {
                b.bind_port::<String>("put", &producer_to_buffer)
                    .bind_port::<String>("get", &buffer_to_consumer);
            })
            .compose_with(&cons, |b| {
                b.bind_port::<String>("input", &buffer_to_consumer);
            })
            .build();

        let p_names: HashSet<&str> = net.places().iter().map(|p| p.name()).collect();
        // Per-instance state isolated.
        assert!(p_names.contains("p1/nextItem"));
        assert!(p_names.contains("p2/nextItem"));
        // Renamed port places are gone — both producers' outputs map to the
        // shared wiring place.
        assert!(!p_names.contains("p1/output"));
        assert!(!p_names.contains("p2/output"));
        assert!(p_names.contains("producerToBuffer"));

        // Both 'p1/produce' and 'p2/produce' point their output arc at the
        // shared 'producerToBuffer' caller place.
        for prefix in ["p1", "p2"] {
            let t_name = format!("{prefix}/produce");
            let t = net
                .transitions()
                .iter()
                .find(|t| t.name() == t_name.as_str())
                .unwrap_or_else(|| panic!("'{t_name}' not found"));
            match t.output_spec().expect("produce has output spec") {
                crate::output::Out::Place(pr) => {
                    assert_eq!(pr.name(), "producerToBuffer");
                }
                other => panic!("expected Out::Place, got {other:?}"),
            }
        }
    }
}
