//! `PrecompiledNetExecutor` — the public type alias surface for the
//! precompiled (production hot path) executor.
//!
//! The 5-phase loop lives in
//! [`Executor`](crate::executor_core::executor::Executor); the
//! precompiled state lives in
//! [`PrecompiledBackend`](crate::precompiled_backend::PrecompiledBackend).
//! This module only wires them together via a type alias + a builder +
//! a few convenience constructors.

use std::collections::HashSet;
use std::sync::Arc;

use libpetri_event::event_store::EventStore;

use crate::executor_core::executor::Executor;
use crate::marking::Marking;
use crate::precompiled_backend::PrecompiledBackend;
use crate::precompiled_net::PrecompiledNet;

/// High-performance executor over a borrowed [`PrecompiledNet`].
///
/// Type alias over the shared
/// [`Executor`](crate::executor_core::executor::Executor) parameterised
/// by [`PrecompiledBackend`]. The 5-phase loop, event emission, and
/// action execution live in `Executor`; the ring buffer token pool,
/// presence / enablement / dirty bitmaps, priority-partitioned ready
/// queues, opcode-based consume dispatch, and reset-clock detection
/// live in the backend.
pub type PrecompiledNetExecutor<'a, E> = Executor<PrecompiledBackend<'a>, E>;

/// Builder for [`PrecompiledNetExecutor`].
///
/// `skip_output_validation` is preserved for API compatibility; output
/// validation isn't wired through either backend today (no path checks
/// XOR/AND output spec at runtime), so the flag is currently a no-op.
pub struct PrecompiledExecutorBuilder<'a, E: EventStore> {
    program: &'a PrecompiledNet,
    initial_marking: Marking,
    event_store: Option<E>,
    environment_places: HashSet<Arc<str>>,
    #[allow(dead_code)]
    skip_output_validation: bool,
}

impl<'a, E: EventStore> PrecompiledExecutorBuilder<'a, E> {
    /// Sets the event store.
    pub fn event_store(mut self, store: E) -> Self {
        self.event_store = Some(store);
        self
    }

    /// Sets the environment places.
    pub fn environment_places(mut self, places: HashSet<Arc<str>>) -> Self {
        self.environment_places = places;
        self
    }

    /// Skips output validation for trusted transition actions.
    /// Currently a no-op — neither backend validates outputs at
    /// runtime today; preserved for API compatibility.
    pub fn skip_output_validation(mut self, skip: bool) -> Self {
        self.skip_output_validation = skip;
        self
    }

    /// Builds the executor.
    pub fn build(self) -> PrecompiledNetExecutor<'a, E> {
        let backend = PrecompiledBackend::new(self.program, self.initial_marking);
        let has_environment_places = !self.environment_places.is_empty();
        Executor::from_parts(
            backend,
            self.event_store.unwrap_or_default(),
            has_environment_places,
        )
    }
}

impl<'a, E: EventStore> Executor<PrecompiledBackend<'a>, E> {
    /// Creates a builder for a `PrecompiledNetExecutor`.
    pub fn builder(
        program: &'a PrecompiledNet,
        initial_marking: Marking,
    ) -> PrecompiledExecutorBuilder<'a, E> {
        PrecompiledExecutorBuilder {
            program,
            initial_marking,
            event_store: None,
            environment_places: HashSet::new(),
            skip_output_validation: false,
        }
    }

    /// Creates a new executor with default options.
    pub fn new(program: &'a PrecompiledNet, initial_marking: Marking) -> Self {
        let backend = PrecompiledBackend::new(program, initial_marking);
        Executor::from_parts(backend, E::default(), false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiled_net::CompiledNet;
    use libpetri_core::action::{fork, passthrough, sync_action};
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::token::Token;
    use libpetri_core::transition::Transition;
    use libpetri_event::event_store::{InMemoryEventStore, NoopEventStore};
    use libpetri_event::net_event::NetEvent;

    fn simple_chain() -> (PetriNet, Place<i32>, Place<i32>, Place<i32>) {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(passthrough())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p3))
            .action(passthrough())
            .build();

        let net = PetriNet::builder("chain").transitions([t1, t2]).build();
        (net, p1, p2, p3)
    }

    #[test]
    fn sync_passthrough_chain() {
        let (net, p1, _p2, _p3) = simple_chain();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(42, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("p1"), 0);
    }

    #[test]
    fn sync_fork_chain() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(libpetri_core::output::and(vec![
                out_place(&p2),
                out_place(&p3),
            ]))
            .action(fork())
            .build();

        let net = PetriNet::builder("fork").transition(t1).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(42, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("p1"), 0);
        assert_eq!(result.count("p2"), 1);
        assert_eq!(result.count("p3"), 1);
    }

    #[test]
    fn sync_linear_chain_5() {
        let places: Vec<Place<i32>> = (0..6).map(|i| Place::new(format!("p{i}"))).collect();
        let transitions: Vec<Transition> = (0..5)
            .map(|i| {
                Transition::builder(format!("t{i}"))
                    .input(one(&places[i]))
                    .output(out_place(&places[i + 1]))
                    .action(fork())
                    .build()
            })
            .collect();

        let net = PetriNet::builder("chain5").transitions(transitions).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&places[0], Token::at(1, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("p0"), 0);
        assert_eq!(result.count("p5"), 1);
    }

    #[test]
    fn sync_no_initial_tokens() {
        let (net, _, _, _) = simple_chain();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);
        let marking = Marking::new();
        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();
        assert_eq!(result.count("p1"), 0);
        assert_eq!(result.count("p2"), 0);
        assert_eq!(result.count("p3"), 0);
    }

    #[test]
    fn sync_priority_ordering() {
        let p = Place::<()>::new("p");
        let out_a = Place::<()>::new("a");
        let out_b = Place::<()>::new("b");

        let t_high = Transition::builder("t_high")
            .input(one(&p))
            .output(out_place(&out_a))
            .action(passthrough())
            .priority(10)
            .build();
        let t_low = Transition::builder("t_low")
            .input(one(&p))
            .output(out_place(&out_b))
            .action(passthrough())
            .priority(1)
            .build();

        let net = PetriNet::builder("priority")
            .transitions([t_high, t_low])
            .build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p, Token::at((), 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("p"), 0);
    }

    #[test]
    fn sync_inhibitor_blocks() {
        let p1 = Place::<()>::new("p1");
        let p2 = Place::<()>::new("p2");
        let p_inh = Place::<()>::new("inh");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .inhibitor(libpetri_core::arc::inhibitor(&p_inh))
            .action(passthrough())
            .build();

        let net = PetriNet::builder("inhibitor").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p1, Token::at((), 0));
        marking.add(&p_inh, Token::at((), 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("p1"), 1);
    }

    #[test]
    fn read_arc_does_not_consume() {
        let p_in = Place::<i32>::new("in");
        let p_ctx = Place::<i32>::new("ctx");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .read(libpetri_core::arc::read(&p_ctx))
            .output(out_place(&p_out))
            .action(sync_action(|ctx| {
                let v = ctx.input::<i32>("in")?;
                let r = ctx.read::<i32>("ctx")?;
                ctx.output("out", *v + *r)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(10, 0));
        marking.add(&p_ctx, Token::at(5, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("in"), 0);
        assert_eq!(result.count("ctx"), 1);
        assert_eq!(result.count("out"), 1);
    }

    #[test]
    fn reset_arc_removes_all_tokens() {
        let p_in = Place::<()>::new("in");
        let p_reset = Place::<i32>::new("reset");
        let p_out = Place::<()>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .reset(libpetri_core::arc::reset(&p_reset))
            .output(out_place(&p_out))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at((), 0));
        marking.add(&p_reset, Token::at(1, 0));
        marking.add(&p_reset, Token::at(2, 0));
        marking.add(&p_reset, Token::at(3, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("reset"), 0);
        assert_eq!(result.count("out"), 1);
    }

    #[test]
    fn exactly_cardinality_consumes_n() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::exactly(3, &p))
            .output(out_place(&p_out))
            .action(sync_action(|ctx| {
                let vals = ctx.inputs::<i32>("p")?;
                for v in vals {
                    ctx.output("out", *v)?;
                }
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        for i in 0..5 {
            marking.add(&p, Token::at(i, 0));
        }

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("p"), 2);
        assert_eq!(result.count("out"), 3);
    }

    #[test]
    fn all_cardinality_consumes_everything() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<()>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::all(&p))
            .output(out_place(&p_out))
            .action(sync_action(|ctx| {
                let vals = ctx.inputs::<i32>("p")?;
                ctx.output("out", vals.len() as i32)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        for i in 0..5 {
            marking.add(&p, Token::at(i, 0));
        }

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("p"), 0);
    }

    #[test]
    fn at_least_blocks_insufficient() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<()>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::at_least(3, &p))
            .output(out_place(&p_out))
            .action(passthrough())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p, Token::at(1, 0));
        marking.add(&p, Token::at(2, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("p"), 2);
    }

    #[test]
    fn at_least_fires_with_enough() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<()>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::at_least(3, &p))
            .output(out_place(&p_out))
            .action(passthrough())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        for i in 0..5 {
            marking.add(&p, Token::at(i, 0));
        }

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("p"), 0);
    }

    #[test]
    fn guarded_input_only_consumes_matching() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::one_guarded(&p, |v| *v > 5))
            .output(out_place(&p_out))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p, Token::at(3, 0));
        marking.add(&p, Token::at(10, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("p"), 1);
        assert_eq!(result.count("out"), 1);
    }

    #[test]
    fn guarded_input_blocks_when_no_match() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::one_guarded(&p, |v| *v > 100))
            .output(out_place(&p_out))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p, Token::at(3, 0));
        marking.add(&p, Token::at(10, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("p"), 2);
        assert_eq!(result.count("out"), 0);
    }

    #[test]
    fn event_store_records_lifecycle() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor = PrecompiledNetExecutor::<InMemoryEventStore>::new(&prog, marking);
        let _result = executor.run_sync();

        let events = executor.event_store().events();
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::ExecutionStarted { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionEnabled { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionStarted { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionCompleted { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TokenRemoved { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TokenAdded { .. }))
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::ExecutionCompleted { .. }))
        );
    }

    #[test]
    fn action_error_does_not_crash() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .action(sync_action(|_ctx| {
                Err(libpetri_core::action::ActionError::new(
                    "intentional failure",
                ))
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(42, 0));

        let mut executor = PrecompiledNetExecutor::<InMemoryEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("in"), 0);
        assert_eq!(result.count("out"), 0);

        let events = executor.event_store().events();
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionFailed { .. }))
        );
    }

    #[test]
    fn multiple_input_arcs_require_all() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .input(one(&p2))
            .output(out_place(&p3))
            .action(sync_action(|ctx| {
                ctx.output("p3", 99i32)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        // Only p1 has token — should not fire
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));
        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();
        assert_eq!(result.count("p1"), 1);
        assert_eq!(result.count("p3"), 0);

        // Both p1 and p2 — should fire
        let compiled2 = CompiledNet::compile(&net);
        let prog2 = PrecompiledNet::from_compiled(compiled2);
        let mut marking2 = Marking::new();
        marking2.add(&p1, Token::at(1, 0));
        marking2.add(&p2, Token::at(2, 0));
        let mut executor2 = PrecompiledNetExecutor::<NoopEventStore>::new(&prog2, marking2);
        let result2 = executor2.run_sync();
        assert_eq!(result2.count("p1"), 0);
        assert_eq!(result2.count("p2"), 0);
        assert_eq!(result2.count("p3"), 1);
    }

    #[test]
    fn sync_action_custom_logic() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<String>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .action(sync_action(|ctx| {
                let v = ctx.input::<i32>("in")?;
                ctx.output("out", format!("value={v}"))?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(42, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("out"), 1);
    }

    #[test]
    fn transform_action_outputs_to_all_places() {
        let p_in = Place::<i32>::new("in");
        let p_a = Place::<i32>::new("a");
        let p_b = Place::<i32>::new("b");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .output(libpetri_core::output::and(vec![
                out_place(&p_a),
                out_place(&p_b),
            ]))
            .action(libpetri_core::action::transform(|ctx| {
                let v = ctx.input::<i32>("in").unwrap();
                Arc::new(*v * 2) as Arc<dyn std::any::Any + Send + Sync>
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(5, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        assert_eq!(result.count("a"), 1);
        assert_eq!(result.count("b"), 1);
    }

    #[test]
    fn complex_workflow() {
        use libpetri_core::output::{and, xor};

        let input = Place::<i32>::new("v_input");
        let guard_in = Place::<i32>::new("v_guardIn");
        let intent_in = Place::<i32>::new("v_intentIn");
        let search_in = Place::<i32>::new("v_searchIn");
        let output_guard_in = Place::<i32>::new("v_outputGuardIn");
        let guard_safe = Place::<i32>::new("v_guardSafe");
        let guard_violation = Place::<i32>::new("v_guardViolation");
        let _violated = Place::<i32>::new("v_violated");
        let intent_ready = Place::<i32>::new("v_intentReady");
        let topic_ready = Place::<i32>::new("v_topicReady");
        let search_ready = Place::<i32>::new("v_searchReady");
        let _output_guard_done = Place::<i32>::new("v_outputGuardDone");
        let response = Place::<i32>::new("v_response");

        let fork_trans = Transition::builder("Fork")
            .input(one(&input))
            .output(and(vec![
                out_place(&guard_in),
                out_place(&intent_in),
                out_place(&search_in),
                out_place(&output_guard_in),
            ]))
            .action(fork())
            .build();

        let guard_trans = Transition::builder("Guard")
            .input(one(&guard_in))
            .output(xor(vec![
                out_place(&guard_safe),
                out_place(&guard_violation),
            ]))
            .action(fork())
            .build();

        let handle_violation = Transition::builder("HandleViolation")
            .input(one(&guard_violation))
            .output(out_place(&_violated))
            .inhibitor(libpetri_core::arc::inhibitor(&guard_safe))
            .action(fork())
            .build();

        let intent_trans = Transition::builder("Intent")
            .input(one(&intent_in))
            .output(out_place(&intent_ready))
            .action(fork())
            .build();

        let topic_trans = Transition::builder("TopicKnowledge")
            .input(one(&intent_ready))
            .output(out_place(&topic_ready))
            .action(fork())
            .build();

        let search_trans = Transition::builder("Search")
            .input(one(&search_in))
            .output(out_place(&search_ready))
            .read(libpetri_core::arc::read(&intent_ready))
            .inhibitor(libpetri_core::arc::inhibitor(&guard_violation))
            .priority(-5)
            .action(fork())
            .build();

        let output_guard_trans = Transition::builder("OutputGuard")
            .input(one(&output_guard_in))
            .output(out_place(&_output_guard_done))
            .read(libpetri_core::arc::read(&guard_safe))
            .action(fork())
            .build();

        let compose_trans = Transition::builder("Compose")
            .input(one(&guard_safe))
            .input(one(&search_ready))
            .input(one(&topic_ready))
            .output(out_place(&response))
            .priority(10)
            .action(fork())
            .build();

        let net = PetriNet::builder("ComplexWorkflow")
            .transition(fork_trans)
            .transition(guard_trans)
            .transition(handle_violation)
            .transition(intent_trans)
            .transition(topic_trans)
            .transition(search_trans)
            .transition(output_guard_trans)
            .transition(compose_trans)
            .build();

        let compiled = CompiledNet::compile(&net);
        let prog = PrecompiledNet::from_compiled(compiled);

        let mut marking = Marking::new();
        marking.add(&input, Token::at(1, 0));

        let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
        let result = executor.run_sync();

        // fork() produces to ALL output places, including both XOR branches.
        // This means guard_safe AND guard_violation both get tokens.
        // Search is inhibited by guard_violation, so it deadlocks.
        // The important thing is the executor doesn't crash and terminates.
        assert_eq!(result.count("v_input"), 0); // consumed by Fork
    }

    #[cfg(feature = "tokio")]
    mod async_tests {
        use super::*;
        use crate::environment::{ExecutorSignal, ExternalEvent};
        use libpetri_core::action::async_action;
        use libpetri_core::petri_net::PetriNet;
        use libpetri_core::token::ErasedToken;

        #[tokio::test]
        async fn async_linear_chain() {
            let places: Vec<Place<i32>> = (0..6).map(|i| Place::new(format!("p{i}"))).collect();
            let transitions: Vec<Transition> = (0..5)
                .map(|i| {
                    Transition::builder(format!("t{i}"))
                        .input(one(&places[i]))
                        .output(out_place(&places[i + 1]))
                        .action(fork())
                        .build()
                })
                .collect();

            let net = PetriNet::builder("chain5").transitions(transitions).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let mut marking = Marking::new();
            marking.add(&places[0], Token::at(1, 0));

            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
            let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            let result = executor.run_async(rx).await;

            assert_eq!(result.count("p0"), 0);
            assert_eq!(result.count("p5"), 1);
        }

        #[tokio::test]
        async fn async_action_execution() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(async_action(|ctx| async { Ok(ctx) }))
                .build();

            let net = PetriNet::builder("async_test").transition(t).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let mut marking = Marking::new();
            marking.add(&p1, Token::at(42, 0));

            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
            let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
            let result = executor.run_async(rx).await;

            assert_eq!(result.count("p1"), 0);
        }

        // ==================== Drain/Close lifecycle tests ====================

        #[tokio::test]
        async fn async_drain_terminates_at_quiescence() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Event(ExternalEvent {
                    place_name: Arc::from("p1"),
                    token: ErasedToken::from_typed(&Token::at(42, 0)),
                }))
                .unwrap();
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Drain).unwrap();
            });

            let result = executor.run_async(rx).await;
            assert_eq!(result.count("p2"), 1);
        }

        #[tokio::test]
        async fn async_drain_rejects_post_drain_events() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Drain).unwrap();
                tx.send(ExecutorSignal::Event(ExternalEvent {
                    place_name: Arc::from("p1"),
                    token: ErasedToken::from_typed(&Token::at(99, 0)),
                }))
                .unwrap();
            });

            let result = executor.run_async(rx).await;
            assert_eq!(result.count("p2"), 0);
        }

        #[tokio::test]
        async fn async_close_discards_queued_events() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&Token::at(1, 0)),
            }))
            .unwrap();
            tx.send(ExecutorSignal::Close).unwrap();
            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&Token::at(2, 0)),
            }))
            .unwrap();
            drop(tx);

            let result = executor.run_async(rx).await;
            assert!(result.count("p2") <= 1);
        }

        #[tokio::test]
        async fn async_close_after_drain_escalates() {
            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                tx.send(ExecutorSignal::Drain).unwrap();
                tx.send(ExecutorSignal::Close).unwrap();
            });

            let _result = executor.run_async(rx).await;
            // Test passes if run_async returns — close escalated from drain
        }

        #[tokio::test]
        async fn async_handle_raii_drain_on_drop() {
            use crate::executor_handle::ExecutorHandle;

            let p1 = Place::<i32>::new("p1");
            let p2 = Place::<i32>::new("p2");

            let t1 = Transition::builder("t1")
                .input(one(&p1))
                .output(out_place(&p2))
                .action(fork())
                .build();

            let net = PetriNet::builder("test").transition(t1).build();
            let compiled = CompiledNet::compile(&net);
            let prog = PrecompiledNet::from_compiled(compiled);

            let marking = Marking::new();
            let mut executor = PrecompiledNetExecutor::<NoopEventStore>::builder(&prog, marking)
                .environment_places(["p1"].iter().map(|s| Arc::from(*s)).collect())
                .build();

            let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

            tokio::spawn(async move {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                let mut handle = ExecutorHandle::new(tx);
                handle.inject(
                    Arc::from("p1"),
                    ErasedToken::from_typed(&Token::at(7, 0)),
                );
                // handle dropped here — RAII sends Drain automatically
            });

            let result = executor.run_async(rx).await;
            assert_eq!(result.count("p2"), 1);
        }
    }
}
