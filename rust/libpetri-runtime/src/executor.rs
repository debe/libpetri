//! `BitmapNetExecutor` — the public type alias surface for the
//! bitmap-storage executor.
//!
//! The 5-phase loop lives in
//! [`Executor`](crate::executor_core::executor::Executor); the bitmap
//! state lives in
//! [`BitmapBackend`](crate::bitmap_backend::BitmapBackend). This module
//! only wires the two together via a type alias + an inherent
//! constructor + the [`ExecutorOptions`] builder type.

use std::collections::HashSet;
use std::sync::Arc;

use libpetri_core::petri_net::PetriNet;
use libpetri_event::event_store::EventStore;

use crate::bitmap_backend::BitmapBackend;
use crate::executor_core::executor::Executor;
use crate::marking::Marking;

/// Construction-time options for a [`BitmapNetExecutor`].
#[derive(Default)]
pub struct ExecutorOptions {
    /// Names of places that receive externally-injected tokens (via
    /// `ExecutorSignal::Event` on the async path). Empty by default;
    /// when empty, the sync loop terminates at quiescence.
    pub environment_places: HashSet<Arc<str>>,
}

/// Bitmap-based executor for Coloured Time Petri Nets.
///
/// Generic over `E: EventStore` for zero-cost noop event recording. The
/// sync path (`run_sync`) executes inline without any async runtime;
/// the async path (`run_async`, behind the `tokio` feature) drives
/// concurrent async actions and external event injection.
///
/// This is a type alias over the shared
/// [`Executor`](crate::executor_core::executor::Executor) parameterised
/// by [`BitmapBackend`]. The 5-phase loop, event emission, and action
/// execution live in `Executor`; the bitmap storage, presence/dirty
/// bitmaps, and per-transition enablement flags live in the backend.
pub type BitmapNetExecutor<E> = Executor<BitmapBackend, E>;

impl<E: EventStore> Executor<BitmapBackend, E> {
    /// Compile `net`, load `initial_tokens` into the backend, and wrap
    /// it with a fresh default-constructed event store.
    pub fn new(net: &PetriNet, initial_tokens: Marking, options: ExecutorOptions) -> Self {
        let backend = BitmapBackend::new(net, initial_tokens);
        let has_environment_places = !options.environment_places.is_empty();
        Executor::from_parts(backend, E::default(), has_environment_places)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::action::passthrough;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
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

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        let result = executor.run_sync();

        // Token should flow p1 -> p2 -> p3
        // passthrough produces no outputs, so token stays consumed
        // Actually passthrough produces nothing, so p2 and p3 will be empty
        assert_eq!(result.count("p1"), 0);
    }

    #[test]
    fn sync_with_event_store() {
        let (net, p1, _, _) = simple_chain();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<InMemoryEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        let store = executor.event_store();
        assert!(!store.is_empty());
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
            .action(libpetri_core::action::fork())
            .build();

        let net = PetriNet::builder("fork").transition(t1).build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        let result = executor.run_sync();

        // Fork copies input to all outputs
        assert_eq!(result.count("p1"), 0);
        assert_eq!(result.count("p2"), 1);
        assert_eq!(result.count("p3"), 1);
    }

    #[test]
    fn sync_no_initial_tokens() {
        let (net, _, _, _) = simple_chain();
        let marking = Marking::new();
        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
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

        // t_high has priority 10, t_low has priority 1
        // Both consume from p, but t_high should fire first
        let t_high = Transition::builder("t_high")
            .input(one(&p))
            .output(out_place(&out_a))
            .action(libpetri_core::action::passthrough())
            .priority(10)
            .build();
        let t_low = Transition::builder("t_low")
            .input(one(&p))
            .output(out_place(&out_b))
            .action(libpetri_core::action::passthrough())
            .priority(1)
            .build();

        let net = PetriNet::builder("priority")
            .transitions([t_high, t_low])
            .build();

        let mut marking = Marking::new();
        marking.add(&p, Token::at((), 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        // Only one token, high priority should have consumed it
        // Since passthrough doesn't produce output, both outputs empty
        // but p should be empty (consumed by the higher priority transition)
        assert_eq!(executor.marking().count("p"), 0);
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
            .action(libpetri_core::action::passthrough())
            .build();

        let net = PetriNet::builder("inhibitor").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at((), 0));
        marking.add(&p_inh, Token::at((), 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        // Inhibitor should block — token remains in p1
        assert_eq!(executor.marking().count("p1"), 1);
    }

    #[test]
    fn sync_linear_chain_5() {
        // Build a chain: p0 -> t0 -> p1 -> t1 -> ... -> p5
        let places: Vec<Place<i32>> = (0..6).map(|i| Place::new(format!("p{i}"))).collect();
        let transitions: Vec<Transition> = (0..5)
            .map(|i| {
                Transition::builder(format!("t{i}"))
                    .input(one(&places[i]))
                    .output(out_place(&places[i + 1]))
                    .action(libpetri_core::action::fork())
                    .build()
            })
            .collect();

        let net = PetriNet::builder("chain5").transitions(transitions).build();

        let mut marking = Marking::new();
        marking.add(&places[0], Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        let result = executor.run_sync();

        // Token should flow through all 5 transitions to p5
        assert_eq!(result.count("p0"), 0);
        assert_eq!(result.count("p5"), 1);
    }

    #[test]
    fn input_arc_requires_token_to_enable() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(libpetri_core::action::fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        // No tokens — transition should not fire
        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            Marking::new(),
            ExecutorOptions::default(),
        );
        executor.run_sync();
        assert_eq!(executor.marking().count("p1"), 0);
        assert_eq!(executor.marking().count("p2"), 0);
    }

    #[test]
    fn multiple_input_arcs_require_all_tokens() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .input(one(&p2))
            .output(out_place(&p3))
            .action(libpetri_core::action::sync_action(|ctx| {
                ctx.output("p3", 99i32)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        // Only p1 has a token — should not fire
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));
        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();
        assert_eq!(executor.marking().count("p1"), 1);
        assert_eq!(executor.marking().count("p3"), 0);

        // Both p1 and p2 have tokens — should fire
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));
        marking.add(&p2, Token::at(2, 0));
        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();
        assert_eq!(executor.marking().count("p1"), 0);
        assert_eq!(executor.marking().count("p2"), 0);
        assert_eq!(executor.marking().count("p3"), 1);
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
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("in")?;
                let r = ctx.read::<i32>("ctx")?;
                ctx.output("out", *v + *r)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(10, 0));
        marking.add(&p_ctx, Token::at(5, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("in"), 0); // consumed
        assert_eq!(executor.marking().count("ctx"), 1); // NOT consumed (read arc)
        assert_eq!(executor.marking().count("out"), 1);
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
            .action(libpetri_core::action::fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at((), 0));
        marking.add(&p_reset, Token::at(1, 0));
        marking.add(&p_reset, Token::at(2, 0));
        marking.add(&p_reset, Token::at(3, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("reset"), 0); // all cleared
        assert_eq!(executor.marking().count("out"), 1);
    }

    #[test]
    fn exactly_cardinality_consumes_n() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::exactly(3, &p))
            .output(out_place(&p_out))
            .action(libpetri_core::action::sync_action(|ctx| {
                let vals = ctx.inputs::<i32>("p")?;
                for v in vals {
                    ctx.output("out", *v)?;
                }
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        for i in 0..5 {
            marking.add(&p, Token::at(i, 0));
        }

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        // Consumed 3 of 5, produced 3
        assert_eq!(executor.marking().count("p"), 2);
        assert_eq!(executor.marking().count("out"), 3);
    }

    #[test]
    fn all_cardinality_consumes_everything() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<()>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::all(&p))
            .output(out_place(&p_out))
            .action(libpetri_core::action::sync_action(|ctx| {
                let vals = ctx.inputs::<i32>("p")?;
                ctx.output("out", vals.len() as i32)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        for i in 0..5 {
            marking.add(&p, Token::at(i, 0));
        }

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("p"), 0);
    }

    #[test]
    fn at_least_blocks_insufficient() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<()>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::at_least(3, &p))
            .output(out_place(&p_out))
            .action(libpetri_core::action::passthrough())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        // Only 2 tokens, need 3+
        let mut marking = Marking::new();
        marking.add(&p, Token::at(1, 0));
        marking.add(&p, Token::at(2, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("p"), 2); // not consumed
    }

    #[test]
    fn at_least_fires_with_enough_and_consumes_all() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<()>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::at_least(3, &p))
            .output(out_place(&p_out))
            .action(libpetri_core::action::passthrough())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        for i in 0..5 {
            marking.add(&p, Token::at(i, 0));
        }

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("p"), 0); // all consumed
    }

    #[test]
    fn guarded_input_only_consumes_matching() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::one_guarded(&p, |v| *v > 5))
            .output(out_place(&p_out))
            .action(libpetri_core::action::fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p, Token::at(3, 0)); // doesn't match guard
        marking.add(&p, Token::at(10, 0)); // matches

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("p"), 1); // 3 remains
        assert_eq!(executor.marking().count("out"), 1); // 10 forwarded
        let peeked = executor.marking().peek(&p_out).unwrap();
        assert_eq!(*peeked, 10);
    }

    #[test]
    fn guarded_input_blocks_when_no_match() {
        let p = Place::<i32>::new("p");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(libpetri_core::input::one_guarded(&p, |v| *v > 100))
            .output(out_place(&p_out))
            .action(libpetri_core::action::fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p, Token::at(3, 0));
        marking.add(&p, Token::at(10, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        // Nothing matches guard, transition does not fire
        assert_eq!(executor.marking().count("p"), 2);
        assert_eq!(executor.marking().count("out"), 0);
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

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(5, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("a"), 1);
        assert_eq!(executor.marking().count("b"), 1);
        assert_eq!(*executor.marking().peek(&p_a).unwrap(), 10);
        assert_eq!(*executor.marking().peek(&p_b).unwrap(), 10);
    }

    #[test]
    fn sync_action_custom_logic() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<String>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("in")?;
                ctx.output("out", format!("value={v}"))?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("out"), 1);
        let peeked = executor.marking().peek(&p_out).unwrap();
        assert_eq!(*peeked, "value=42");
    }

    #[test]
    fn action_error_does_not_crash() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .action(libpetri_core::action::sync_action(|_ctx| {
                Err(libpetri_core::action::ActionError::new(
                    "intentional failure",
                ))
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<InMemoryEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        // Token consumed even though action failed
        assert_eq!(executor.marking().count("in"), 0);
        assert_eq!(executor.marking().count("out"), 0);

        // Failure event should be recorded
        let events = executor.event_store().events();
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionFailed { .. }))
        );
    }

    #[test]
    fn event_store_records_lifecycle() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(libpetri_core::action::fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<InMemoryEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        let events = executor.event_store().events();

        // Should have: ExecutionStarted, TransitionEnabled, TokenRemoved, TransitionStarted,
        // TokenAdded, TransitionCompleted, ExecutionCompleted
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
    fn noop_event_store_has_no_events() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(libpetri_core::action::fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert!(executor.event_store().is_empty());
    }

    #[test]
    fn empty_net_completes() {
        let net = PetriNet::builder("empty").build();
        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            Marking::new(),
            ExecutorOptions::default(),
        );
        executor.run_sync();
        assert!(executor.is_quiescent());
    }

    #[test]
    fn single_transition_fires_once() {
        let p = Place::<i32>::new("p");
        let out = Place::<i32>::new("out");
        let t = Transition::builder("t1")
            .input(one(&p))
            .output(out_place(&out))
            .action(libpetri_core::action::fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("p"), 0);
        assert_eq!(executor.marking().count("out"), 1);
    }

    #[test]
    fn many_tokens_all_processed() {
        let p = Place::<i32>::new("p");
        let out = Place::<i32>::new("out");
        let t = Transition::builder("t1")
            .input(one(&p))
            .output(out_place(&out))
            .action(libpetri_core::action::fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        for i in 0..100 {
            marking.add(&p, Token::at(i, 0));
        }

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("p"), 0);
        assert_eq!(executor.marking().count("out"), 100);
    }

    #[test]
    fn input_fifo_ordering() {
        let p = Place::<i32>::new("p");
        let out = Place::<i32>::new("out");
        let t = Transition::builder("t1")
            .input(one(&p))
            .output(out_place(&out))
            .action(libpetri_core::action::fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p, Token::at(1, 0));
        marking.add(&p, Token::at(2, 0));
        marking.add(&p, Token::at(3, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        // All processed, first one should have been consumed first
        assert_eq!(executor.marking().count("out"), 3);
    }

    #[test]
    fn inhibitor_unblocked_when_token_removed() {
        // p1 has token, p_inh has token (blocks t1)
        // t_clear removes from p_inh, then t1 can fire
        let p1 = Place::<()>::new("p1");
        let p_inh = Place::<()>::new("inh");
        let p_out = Place::<()>::new("out");
        let p_trigger = Place::<()>::new("trigger");

        // t_clear: consumes from inh, outputs to trigger
        let t_clear = Transition::builder("t_clear")
            .input(one(&p_inh))
            .output(out_place(&p_trigger))
            .action(libpetri_core::action::fork())
            .priority(10) // higher priority fires first
            .build();

        // t1: consumes from p1, inhibited by inh
        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .inhibitor(libpetri_core::arc::inhibitor(&p_inh))
            .output(out_place(&p_out))
            .action(libpetri_core::action::fork())
            .priority(1)
            .build();

        let net = PetriNet::builder("test").transitions([t_clear, t1]).build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at((), 0));
        marking.add(&p_inh, Token::at((), 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        // t_clear fires first (priority 10), removes inh token
        // then t1 fires (no longer inhibited)
        assert_eq!(executor.marking().count("inh"), 0);
        assert_eq!(executor.marking().count("p1"), 0);
        assert_eq!(executor.marking().count("out"), 1);
    }

    #[test]
    fn combined_input_read_reset() {
        let p_in = Place::<i32>::new("in");
        let p_ctx = Place::<String>::new("ctx");
        let p_clear = Place::<i32>::new("clear");
        let p_out = Place::<String>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .read(libpetri_core::arc::read(&p_ctx))
            .reset(libpetri_core::arc::reset(&p_clear))
            .output(out_place(&p_out))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("in")?;
                let r = ctx.read::<String>("ctx")?;
                ctx.output("out", format!("{v}-{r}"))?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at(42, 0));
        marking.add(&p_ctx, Token::at("hello".to_string(), 0));
        marking.add(&p_clear, Token::at(1, 0));
        marking.add(&p_clear, Token::at(2, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("in"), 0); // consumed
        assert_eq!(executor.marking().count("ctx"), 1); // read, not consumed
        assert_eq!(executor.marking().count("clear"), 0); // reset
        assert_eq!(executor.marking().count("out"), 1);
        let peeked = executor.marking().peek(&p_out).unwrap();
        assert_eq!(*peeked, "42-hello");
    }

    #[test]
    fn workflow_sequential_chain() {
        // p1 -> t1 -> p2 -> t2 -> p3 -> t3 -> p4
        // Each transition doubles the value
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");
        let p4 = Place::<i32>::new("p4");

        let make_doubler = |name: &str, inp: &Place<i32>, outp: &Place<i32>| {
            let out_name: Arc<str> = Arc::from(outp.name());
            Transition::builder(name)
                .input(one(inp))
                .output(out_place(outp))
                .action(libpetri_core::action::sync_action(move |ctx| {
                    let v = ctx
                        .input::<i32>("p1")
                        .or_else(|_| ctx.input::<i32>("p2"))
                        .or_else(|_| ctx.input::<i32>("p3"))
                        .unwrap();
                    ctx.output(&out_name, *v * 2)?;
                    Ok(())
                }))
                .build()
        };

        let t1 = make_doubler("t1", &p1, &p2);
        let t2 = make_doubler("t2", &p2, &p3);
        let t3 = make_doubler("t3", &p3, &p4);

        let net = PetriNet::builder("chain").transitions([t1, t2, t3]).build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("p4"), 1);
        assert_eq!(*executor.marking().peek(&p4).unwrap(), 8); // 1 * 2 * 2 * 2
    }

    #[test]
    fn workflow_fork_join() {
        // p_start -> t_fork -> p_a, p_b -> t_join -> p_end
        let p_start = Place::<i32>::new("start");
        let p_a = Place::<i32>::new("a");
        let p_b = Place::<i32>::new("b");
        let p_end = Place::<i32>::new("end");

        let t_fork = Transition::builder("fork")
            .input(one(&p_start))
            .output(libpetri_core::output::and(vec![
                out_place(&p_a),
                out_place(&p_b),
            ]))
            .action(libpetri_core::action::fork())
            .build();

        let t_join = Transition::builder("join")
            .input(one(&p_a))
            .input(one(&p_b))
            .output(out_place(&p_end))
            .action(libpetri_core::action::sync_action(|ctx| {
                let a = ctx.input::<i32>("a")?;
                let b = ctx.input::<i32>("b")?;
                ctx.output("end", *a + *b)?;
                Ok(())
            }))
            .build();

        let net = PetriNet::builder("fork-join")
            .transitions([t_fork, t_join])
            .build();

        let mut marking = Marking::new();
        marking.add(&p_start, Token::at(5, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("start"), 0);
        assert_eq!(executor.marking().count("a"), 0);
        assert_eq!(executor.marking().count("b"), 0);
        assert_eq!(executor.marking().count("end"), 1);
        assert_eq!(*executor.marking().peek(&p_end).unwrap(), 10); // 5 + 5
    }

    #[test]
    fn workflow_mutual_exclusion() {
        // Two workers compete for a mutex token
        let p_mutex = Place::<()>::new("mutex");
        let p_w1 = Place::<()>::new("w1");
        let p_w2 = Place::<()>::new("w2");
        let p_done1 = Place::<()>::new("done1");
        let p_done2 = Place::<()>::new("done2");

        let t_w1 = Transition::builder("work1")
            .input(one(&p_w1))
            .input(one(&p_mutex))
            .output(libpetri_core::output::and(vec![
                out_place(&p_done1),
                out_place(&p_mutex), // return mutex
            ]))
            .action(libpetri_core::action::sync_action(|ctx| {
                ctx.output("done1", ())?;
                ctx.output("mutex", ())?;
                Ok(())
            }))
            .build();

        let t_w2 = Transition::builder("work2")
            .input(one(&p_w2))
            .input(one(&p_mutex))
            .output(libpetri_core::output::and(vec![
                out_place(&p_done2),
                out_place(&p_mutex), // return mutex
            ]))
            .action(libpetri_core::action::sync_action(|ctx| {
                ctx.output("done2", ())?;
                ctx.output("mutex", ())?;
                Ok(())
            }))
            .build();

        let net = PetriNet::builder("mutex").transitions([t_w1, t_w2]).build();

        let mut marking = Marking::new();
        marking.add(&p_mutex, Token::at((), 0));
        marking.add(&p_w1, Token::at((), 0));
        marking.add(&p_w2, Token::at((), 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        // Both should complete, mutex should be returned
        assert_eq!(executor.marking().count("done1"), 1);
        assert_eq!(executor.marking().count("done2"), 1);
        assert_eq!(executor.marking().count("mutex"), 1); // returned
    }

    #[test]
    fn produce_action() {
        let p_in = Place::<()>::new("in");
        let p_out = Place::<String>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .action(libpetri_core::action::produce(
                Arc::from("out"),
                "produced_value".to_string(),
            ))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p_in, Token::at((), 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("out"), 1);
    }

    #[test]
    fn xor_output_fires_one_branch() {
        let p = Place::<i32>::new("p");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");

        let t = Transition::builder("t1")
            .input(one(&p))
            .output(libpetri_core::output::xor(vec![
                out_place(&a),
                out_place(&b),
            ]))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("p")?;
                // Output to first branch place
                ctx.output("a", *v)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        // XOR: token goes to one branch
        let total = executor.marking().count("a") + executor.marking().count("b");
        assert!(total >= 1);
    }

    #[test]
    fn and_output_fires_to_all() {
        let p = Place::<i32>::new("p");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let c = Place::<i32>::new("c");

        let t = Transition::builder("t1")
            .input(one(&p))
            .output(libpetri_core::output::and(vec![
                out_place(&a),
                out_place(&b),
                out_place(&c),
            ]))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("p")?;
                ctx.output("a", *v)?;
                ctx.output("b", *v * 10)?;
                ctx.output("c", *v * 100)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("a"), 1);
        assert_eq!(executor.marking().count("b"), 1);
        assert_eq!(executor.marking().count("c"), 1);
        assert_eq!(*executor.marking().peek(&a).unwrap(), 1);
        assert_eq!(*executor.marking().peek(&b).unwrap(), 10);
        assert_eq!(*executor.marking().peek(&c).unwrap(), 100);
    }

    #[test]
    fn transition_with_no_output_consumes_only() {
        let p = Place::<i32>::new("p");

        let t = Transition::builder("t1")
            .input(one(&p))
            .action(libpetri_core::action::sync_action(|ctx| {
                let _ = ctx.input::<i32>("p")?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("p"), 0);
    }

    #[test]
    fn multiple_transitions_same_input_compete() {
        // Two transitions both need p1 — only one should fire per token
        let p1 = Place::<()>::new("p1");
        let out_a = Place::<()>::new("a");
        let out_b = Place::<()>::new("b");

        let t_a = Transition::builder("ta")
            .input(one(&p1))
            .output(out_place(&out_a))
            .action(libpetri_core::action::fork())
            .build();
        let t_b = Transition::builder("tb")
            .input(one(&p1))
            .output(out_place(&out_b))
            .action(libpetri_core::action::fork())
            .build();

        let net = PetriNet::builder("test").transitions([t_a, t_b]).build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at((), 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        // One token, two competing transitions — exactly one fires
        let total = executor.marking().count("a") + executor.marking().count("b");
        assert_eq!(total, 1);
        assert_eq!(executor.marking().count("p1"), 0);
    }

    #[test]
    fn priority_higher_fires_first() {
        let p = Place::<()>::new("p");
        let out_hi = Place::<()>::new("hi");
        let out_lo = Place::<()>::new("lo");

        let t_hi = Transition::builder("hi")
            .input(one(&p))
            .output(out_place(&out_hi))
            .action(libpetri_core::action::fork())
            .priority(10)
            .build();
        let t_lo = Transition::builder("lo")
            .input(one(&p))
            .output(out_place(&out_lo))
            .action(libpetri_core::action::fork())
            .priority(1)
            .build();

        let net = PetriNet::builder("test").transitions([t_hi, t_lo]).build();

        let mut marking = Marking::new();
        marking.add(&p, Token::at((), 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        // Higher priority should win
        assert_eq!(executor.marking().count("hi"), 1);
        assert_eq!(executor.marking().count("lo"), 0);
    }

    #[test]
    fn quiescent_when_no_enabled_transitions() {
        let p = Place::<i32>::new("p");
        let out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p))
            .output(out_place(&out))
            .action(libpetri_core::action::fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert!(executor.is_quiescent());
    }

    #[test]
    fn event_store_transition_enabled_disabled() {
        let p1 = Place::<()>::new("p1");
        let p2 = Place::<()>::new("p2");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(libpetri_core::action::fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at((), 0));

        let mut executor =
            BitmapNetExecutor::<InMemoryEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        let events = executor.event_store().events();
        // Should have at least: ExecutionStarted, TransitionEnabled, TransitionStarted,
        // TokenAdded, TransitionCompleted, ExecutionCompleted
        assert!(events.len() >= 4);

        // Check for TransitionEnabled event
        let has_enabled = events.iter().any(|e| {
            matches!(e, NetEvent::TransitionEnabled { transition_name, .. } if transition_name.as_ref() == "t1")
        });
        assert!(has_enabled);
    }

    #[test]
    fn diamond_pattern() {
        // p1 -> t1 -> p2, p3 -> t2 -> p4 (from p2), t3 -> p4 (from p3)
        let p1 = Place::<()>::new("p1");
        let p2 = Place::<()>::new("p2");
        let p3 = Place::<()>::new("p3");
        let p4 = Place::<()>::new("p4");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(libpetri_core::output::and(vec![
                out_place(&p2),
                out_place(&p3),
            ]))
            .action(libpetri_core::action::fork())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p4))
            .action(libpetri_core::action::fork())
            .build();
        let t3 = Transition::builder("t3")
            .input(one(&p3))
            .output(out_place(&p4))
            .action(libpetri_core::action::fork())
            .build();

        let net = PetriNet::builder("diamond")
            .transitions([t1, t2, t3])
            .build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at((), 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("p4"), 2); // both branches produce to p4
    }

    #[test]
    fn self_loop_with_guard_terminates() {
        // Transition that loops back, but only fires when value > 0
        // Decrements each time, terminates when 0
        let p = Place::<i32>::new("p");
        let done = Place::<i32>::new("done");

        let t = Transition::builder("dec")
            .input(libpetri_core::input::one_guarded(&p, |v: &i32| *v > 0))
            .output(out_place(&p))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("p")?;
                ctx.output("p", *v - 1)?;
                Ok(())
            }))
            .build();

        // When value hits 0, this transition moves it to done
        let t_done = Transition::builder("finish")
            .input(libpetri_core::input::one_guarded(&p, |v: &i32| *v == 0))
            .output(out_place(&done))
            .action(libpetri_core::action::fork())
            .build();

        let net = PetriNet::builder("countdown")
            .transitions([t, t_done])
            .build();

        let mut marking = Marking::new();
        marking.add(&p, Token::at(3, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(executor.marking().count("done"), 1);
        assert_eq!(*executor.marking().peek(&done).unwrap(), 0);
    }

    #[test]
    fn multiple_tokens_different_types() {
        let p_int = Place::<i32>::new("ints");
        let p_str = Place::<String>::new("strs");
        let p_out = Place::<String>::new("out");

        let t = Transition::builder("combine")
            .input(one(&p_int))
            .input(one(&p_str))
            .output(out_place(&p_out))
            .action(libpetri_core::action::sync_action(|ctx| {
                let i = ctx.input::<i32>("ints")?;
                let s = ctx.input::<String>("strs")?;
                ctx.output("out", format!("{s}-{i}"))?;
                Ok(())
            }))
            .build();

        let net = PetriNet::builder("test").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p_int, Token::at(42, 0));
        marking.add(&p_str, Token::at("hello".to_string(), 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        executor.run_sync();

        assert_eq!(*executor.marking().peek(&p_out).unwrap(), "hello-42");
    }
}

#[cfg(all(test, feature = "tokio"))]
mod async_tests {
    use super::*;
    use crate::environment::{ExecutorSignal, ExternalEvent};
    use libpetri_core::action::{ActionError, async_action, fork};
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::token::{ErasedToken, Token};
    use libpetri_core::transition::Transition;
    use libpetri_event::event_store::{InMemoryEventStore, NoopEventStore};
    use libpetri_event::net_event::NetEvent;

    #[tokio::test]
    async fn async_fork_single_transition() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 42);
    }

    #[tokio::test]
    async fn async_action_produces_output() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let action = async_action(|mut ctx| async move {
            let val: i32 = *ctx.input::<i32>("p1")?;
            ctx.output("p2", val * 10)?;
            Ok(ctx)
        });

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(action)
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(5, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 50);
    }

    #[tokio::test]
    async fn async_chain_two_transitions() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p3))
            .action(fork())
            .build();

        let net = PetriNet::builder("chain").transitions([t1, t2]).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(99, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p3"), 1);
        assert_eq!(*executor.marking().peek(&p3).unwrap(), 99);
    }

    #[tokio::test]
    async fn async_event_injection() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let marking = Marking::new(); // empty — no initial tokens

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        // Inject a token after a short delay, then close the channel
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            let token = Token::at(77, 0);
            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&token),
            }))
            .unwrap();
            // Drop tx to close the channel and let executor terminate
        });

        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 77);
    }

    #[tokio::test]
    async fn async_with_event_store_records_events() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<InMemoryEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        let events = executor.event_store().events();
        assert!(!events.is_empty());
        // Should have ExecutionStarted, TransitionStarted, TransitionCompleted, ExecutionCompleted
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::ExecutionStarted { .. }))
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
                .any(|e| matches!(e, NetEvent::ExecutionCompleted { .. }))
        );
    }

    #[tokio::test]
    async fn async_action_error_does_not_crash() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let action =
            async_action(|_ctx| async move { Err(ActionError::new("intentional failure")) });

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(action)
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<InMemoryEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        // Token consumed but no output produced
        assert_eq!(executor.marking().count("p1"), 0);
        assert_eq!(executor.marking().count("p2"), 0);

        // Failure event recorded
        let events = executor.event_store().events();
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetEvent::TransitionFailed { .. }))
        );
    }

    #[tokio::test]
    async fn async_delayed_timing() {
        use libpetri_core::timing::delayed;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .timing(delayed(100))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(10, 0));

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let start = std::time::Instant::now();
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        // Keep channel open long enough for the delayed transition to fire
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(300)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        assert!(
            start.elapsed().as_millis() >= 80,
            "delayed(100) should wait ~100ms"
        );
        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 10);
    }

    #[tokio::test]
    async fn async_exact_timing() {
        use libpetri_core::timing::exact;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .timing(exact(100))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(20, 0));

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let start = std::time::Instant::now();
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(300)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        assert!(
            start.elapsed().as_millis() >= 80,
            "exact(100) should wait ~100ms"
        );
        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 20);
    }

    #[tokio::test]
    async fn async_window_timing() {
        use libpetri_core::timing::window;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .timing(window(50, 200))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(30, 0));

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let start = std::time::Instant::now();
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(400)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        assert!(
            start.elapsed().as_millis() >= 40,
            "window(50,200) should wait >= ~50ms"
        );
        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 30);
    }

    #[tokio::test]
    async fn async_deadline_enforcement() {
        use libpetri_core::action::sync_action;
        use libpetri_core::timing::window;

        let p_slow = Place::<i32>::new("p_slow");
        let p_windowed = Place::<i32>::new("p_windowed");
        let slow_out = Place::<i32>::new("slow_out");
        let windowed_out = Place::<i32>::new("windowed_out");

        // Sync action that busy-waits for 200ms, blocking the executor thread.
        // This prevents the executor from reaching the fire phase for windowed
        // until after its deadline has passed.
        let t_slow = Transition::builder("slow")
            .input(one(&p_slow))
            .output(out_place(&slow_out))
            .priority(10)
            .action(sync_action(|ctx| {
                let v = ctx.input::<i32>("p_slow")?;
                let start = std::time::Instant::now();
                while start.elapsed().as_millis() < 200 {
                    std::hint::spin_loop();
                }
                ctx.output("slow_out", *v)?;
                Ok(())
            }))
            .build();

        // Windowed transition: enabled at start, earliest=50ms, deadline=100ms.
        // Because the slow sync action blocks the executor for 200ms, by the time
        // enforce_deadlines runs again, elapsed (~200ms) > latest (100ms) + tolerance.
        let t_windowed = Transition::builder("windowed")
            .input(one(&p_windowed))
            .output(out_place(&windowed_out))
            .timing(window(50, 100))
            .action(fork())
            .build();

        let net = PetriNet::builder("test")
            .transitions([t_slow, t_windowed])
            .build();

        let mut marking = Marking::new();
        marking.add(&p_slow, Token::at(1, 0));
        marking.add(&p_windowed, Token::at(2, 0));

        let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(500)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        // Slow fires and completes after 200ms busy-wait
        assert_eq!(executor.marking().count("slow_out"), 1);
        // Windowed should have been disabled by deadline enforcement
        assert_eq!(
            executor.marking().count("windowed_out"),
            0,
            "windowed transition should have been disabled by deadline"
        );

        let events = executor.event_store().events();
        assert!(
            events.iter().any(|e| matches!(e, NetEvent::TransitionTimedOut { transition_name, .. } if &**transition_name == "windowed")),
            "expected TransitionTimedOut event for 'windowed'"
        );
    }

    #[tokio::test]
    async fn async_multiple_injections() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            for i in 0..5 {
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                let token = Token::at(i, 0);
                tx.send(ExecutorSignal::Event(ExternalEvent {
                    place_name: Arc::from("p1"),
                    token: ErasedToken::from_typed(&token),
                }))
                .unwrap();
            }
            // Drop tx to close channel
        });

        executor.run_async(rx).await;

        assert_eq!(
            executor.marking().count("p2"),
            5,
            "all 5 injected tokens should arrive"
        );
    }

    #[tokio::test]
    async fn async_parallel_execution() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");
        let out1 = Place::<i32>::new("out1");
        let out2 = Place::<i32>::new("out2");
        let out3 = Place::<i32>::new("out3");

        let make_transition = |name: &str, inp: &Place<i32>, outp: &Place<i32>| {
            Transition::builder(name)
                .input(one(inp))
                .output(out_place(outp))
                .action(async_action(|mut ctx| async move {
                    let v: i32 =
                        *ctx.input::<i32>(ctx.transition_name().replace("t", "p").as_str())?;
                    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
                    ctx.output(&ctx.transition_name().replace("t", "out"), v)?;
                    Ok(ctx)
                }))
                .build()
        };

        let t1 = make_transition("t1", &p1, &out1);
        let t2 = make_transition("t2", &p2, &out2);
        let t3 = make_transition("t3", &p3, &out3);

        let net = PetriNet::builder("parallel")
            .transitions([t1, t2, t3])
            .build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));
        marking.add(&p2, Token::at(2, 0));
        marking.add(&p3, Token::at(3, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let start = std::time::Instant::now();
        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;
        let elapsed = start.elapsed().as_millis();

        assert_eq!(executor.marking().count("out1"), 1);
        assert_eq!(executor.marking().count("out2"), 1);
        assert_eq!(executor.marking().count("out3"), 1);
        assert!(
            elapsed < 250,
            "parallel execution should take < 250ms, took {elapsed}ms"
        );
    }

    #[tokio::test]
    async fn async_sequential_chain_order() {
        use std::sync::Mutex;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");
        let p4 = Place::<i32>::new("p4");

        let order: Arc<Mutex<Vec<i32>>> = Arc::new(Mutex::new(Vec::new()));

        let make_chain = |name: &str,
                          inp: &Place<i32>,
                          outp: &Place<i32>,
                          id: i32,
                          order: Arc<Mutex<Vec<i32>>>| {
            let inp_name: Arc<str> = Arc::from(inp.name());
            let outp_name: Arc<str> = Arc::from(outp.name());
            Transition::builder(name)
                .input(one(inp))
                .output(out_place(outp))
                .action(async_action(move |mut ctx| {
                    let order = Arc::clone(&order);
                    let inp_name = Arc::clone(&inp_name);
                    let outp_name = Arc::clone(&outp_name);
                    async move {
                        let v: i32 = *ctx.input::<i32>(&inp_name)?;
                        order.lock().unwrap().push(id);
                        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                        ctx.output(&outp_name, v)?;
                        Ok(ctx)
                    }
                }))
                .build()
        };

        let t1 = make_chain("t1", &p1, &p2, 1, Arc::clone(&order));
        let t2 = make_chain("t2", &p2, &p3, 2, Arc::clone(&order));
        let t3 = make_chain("t3", &p3, &p4, 3, Arc::clone(&order));

        let net = PetriNet::builder("chain").transitions([t1, t2, t3]).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p4"), 1);
        let recorded = order.lock().unwrap().clone();
        assert_eq!(recorded, vec![1, 2, 3], "chain should execute in order");
    }

    #[tokio::test]
    async fn async_fork_join() {
        use libpetri_core::output::and;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");
        let p4 = Place::<i32>::new("p4");

        // Fork: p1 -> (p2, p3) via AND output
        let t_fork = Transition::builder("fork")
            .input(one(&p1))
            .output(and(vec![out_place(&p2), out_place(&p3)]))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("p1")?;
                ctx.output("p2", *v)?;
                ctx.output("p3", *v)?;
                Ok(())
            }))
            .build();

        // Join: (p2, p3) -> p4
        let t_join = Transition::builder("join")
            .input(one(&p2))
            .input(one(&p3))
            .output(out_place(&p4))
            .action(libpetri_core::action::sync_action(|ctx| {
                let a = ctx.input::<i32>("p2")?;
                let b = ctx.input::<i32>("p3")?;
                ctx.output("p4", *a + *b)?;
                Ok(())
            }))
            .build();

        let net = PetriNet::builder("fork_join")
            .transitions([t_fork, t_join])
            .build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at(5, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 0);
        assert_eq!(executor.marking().count("p3"), 0);
        assert_eq!(executor.marking().count("p4"), 1);
        assert_eq!(*executor.marking().peek(&p4).unwrap(), 10);
    }

    #[tokio::test]
    async fn async_xor_output_branching() {
        use libpetri_core::output::xor;

        let p = Place::<i32>::new("p");
        let left = Place::<i32>::new("left");
        let right = Place::<i32>::new("right");

        let t = Transition::builder("xor_t")
            .input(one(&p))
            .output(xor(vec![out_place(&left), out_place(&right)]))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("p")?;
                if *v > 0 {
                    ctx.output("left", *v)?;
                } else {
                    ctx.output("right", *v)?;
                }
                Ok(())
            }))
            .build();

        let net = PetriNet::builder("xor_test").transition(t).build();

        // Test positive value goes left
        let mut marking = Marking::new();
        marking.add(&p, Token::at(42, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("left"), 1);
        assert_eq!(executor.marking().count("right"), 0);
        assert_eq!(*executor.marking().peek(&left).unwrap(), 42);
    }

    #[tokio::test]
    async fn async_loop_with_guard() {
        use libpetri_core::input::one_guarded;

        let counter = Place::<i32>::new("counter");
        let done = Place::<i32>::new("done");

        // Loop transition: counter -> counter (increment), guarded to fire when < 3
        let t_loop = Transition::builder("loop")
            .input(one_guarded(&counter, |v: &i32| *v < 3))
            .output(out_place(&counter))
            .action(libpetri_core::action::sync_action(|ctx| {
                let v = ctx.input::<i32>("counter")?;
                ctx.output("counter", *v + 1)?;
                Ok(())
            }))
            .build();

        // Exit transition: counter -> done, guarded to fire when >= 3
        let t_exit = Transition::builder("exit")
            .input(one_guarded(&counter, |v: &i32| *v >= 3))
            .output(out_place(&done))
            .action(fork())
            .build();

        let net = PetriNet::builder("loop_net")
            .transitions([t_loop, t_exit])
            .build();

        let mut marking = Marking::new();
        marking.add(&counter, Token::at(0, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("done"), 1);
        assert_eq!(*executor.marking().peek(&done).unwrap(), 3);
    }

    #[tokio::test]
    async fn async_delayed_fires_without_injection() {
        use libpetri_core::timing::delayed;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .timing(delayed(100))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(7, 0));

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        // No injections; keep channel open long enough for the delayed transition to fire
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(300)).await;
            drop(tx);
        });
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 7);
    }

    #[tokio::test]
    async fn async_timeout_produces_timeout_token() {
        use libpetri_core::output::{timeout_place, xor};

        let p1 = Place::<i32>::new("p1");
        let success = Place::<i32>::new("success");
        let timeout_out = Place::<i32>::new("timeout_out");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(xor(vec![
                out_place(&success),
                timeout_place(50, &timeout_out),
            ]))
            .action(async_action(|mut ctx| async move {
                let v: i32 = *ctx.input::<i32>("p1")?;
                tokio::time::sleep(std::time::Duration::from_millis(200)).await;
                ctx.output("success", v)?;
                Ok(ctx)
            }))
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("timeout_out"), 1);
        assert_eq!(executor.marking().count("success"), 0);
    }

    #[tokio::test]
    async fn async_timeout_normal_when_fast() {
        use libpetri_core::output::{timeout_place, xor};

        let p1 = Place::<i32>::new("p1");
        let success = Place::<i32>::new("success");
        let timeout_out = Place::<i32>::new("timeout_out");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(xor(vec![
                out_place(&success),
                timeout_place(500, &timeout_out),
            ]))
            .action(async_action(|mut ctx| async move {
                let v: i32 = *ctx.input::<i32>("p1")?;
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                ctx.output("success", v)?;
                Ok(ctx)
            }))
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let mut marking = Marking::new();
        marking.add(&p1, Token::at(1, 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("success"), 1);
        assert_eq!(executor.marking().count("timeout_out"), 0);
    }

    #[tokio::test]
    async fn async_event_store_records_token_added_for_injection() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();

        let net = PetriNet::builder("test").transition(t1).build();
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            let token = Token::at(99, 0);
            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&token),
            }))
            .unwrap();
        });

        executor.run_async(rx).await;

        let events = executor.event_store().events();
        // Should have TokenAdded for the injected token into p1
        assert!(
            events.iter().any(
                |e| matches!(e, NetEvent::TokenAdded { place_name, .. } if &**place_name == "p1")
            ),
            "expected TokenAdded event for injected token into p1"
        );
        // And also TokenAdded for the output into p2
        assert!(
            events.iter().any(
                |e| matches!(e, NetEvent::TokenAdded { place_name, .. } if &**place_name == "p2")
            ),
            "expected TokenAdded event for output token into p2"
        );
    }

    #[tokio::test]
    async fn async_inhibitor_blocks_in_async() {
        let p1 = Place::<()>::new("p1");
        let p2 = Place::<()>::new("p2");
        let p_inh = Place::<()>::new("inh");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .inhibitor(libpetri_core::arc::inhibitor(&p_inh))
            .action(fork())
            .build();

        let net = PetriNet::builder("inhibitor").transition(t).build();

        let mut marking = Marking::new();
        marking.add(&p1, Token::at((), 0));
        marking.add(&p_inh, Token::at((), 0));

        let mut executor =
            BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());

        let (_tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();
        executor.run_async(rx).await;

        // Inhibitor should block — token remains in p1, nothing in p2
        assert_eq!(executor.marking().count("p1"), 1);
        assert_eq!(executor.marking().count("p2"), 0);
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
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            // Inject a token, then drain
            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&Token::at(42, 0)),
            }))
            .unwrap();
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            tx.send(ExecutorSignal::Drain).unwrap();
        });

        executor.run_async(rx).await;

        // The injected token should have been processed
        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 42);
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
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            // Send Drain first, then an event — event should be discarded
            tx.send(ExecutorSignal::Drain).unwrap();
            tx.send(ExecutorSignal::Event(ExternalEvent {
                place_name: Arc::from("p1"),
                token: ErasedToken::from_typed(&Token::at(99, 0)),
            }))
            .unwrap();
        });

        executor.run_async(rx).await;

        // Event sent after drain should not have been processed
        assert_eq!(executor.marking().count("p2"), 0);
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
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        // Queue events then close — close should discard all pending events
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

        executor.run_async(rx).await;

        // The first event arrives before Close — it gets processed in the first
        // try_recv batch. Close then discards all remaining events.
        // So at most 1 token should be in p2 (the one before Close).
        assert!(executor.marking().count("p2") <= 1);
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
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            // Drain first, then escalate to close
            tx.send(ExecutorSignal::Drain).unwrap();
            tx.send(ExecutorSignal::Close).unwrap();
        });

        // Executor should terminate — close escalates from drain
        executor.run_async(rx).await;
        // No assertions needed — the test passes if run_async returns
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
        let marking = Marking::new();

        let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
            &net,
            marking,
            ExecutorOptions {
                environment_places: ["p1"].iter().map(|s| Arc::from(*s)).collect(),
            },
        );

        let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<ExecutorSignal>();

        tokio::spawn(async move {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            let mut handle = ExecutorHandle::new(tx);
            handle.inject(Arc::from("p1"), ErasedToken::from_typed(&Token::at(7, 0)));
            // handle dropped here — RAII sends Drain automatically
        });

        executor.run_async(rx).await;

        assert_eq!(executor.marking().count("p2"), 1);
        assert_eq!(*executor.marking().peek(&p2).unwrap(), 7);
    }
}
