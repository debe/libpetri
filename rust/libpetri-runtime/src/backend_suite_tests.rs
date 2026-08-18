//! Cross-backend CTPN semantic test suite.
//!
//! Every backend-agnostic sync test lives here exactly once, written as
//! a generic fn over [`BackendRunner`]. The [`for_each_backend!`] macro
//! at the bottom stamps out a `#[test]` entry point per backend, so each
//! semantic is verified against **both** `BitmapNetExecutor` and
//! `PrecompiledNetExecutor` from a single source.
//!
//! Before this suite the two executors carried near-duplicate sync test
//! blocks that had drifted (the bitmap file had ~20 cases the precompiled
//! file lacked, and vice-versa for `complex_workflow`). Consolidating
//! here both removes the duplication and *widens* coverage: tests that
//! used to run on one backend now run on both.
//!
//! Backend-specific tests (precompiled opcode encoding, bitmap word
//! math, the richer async timing/lifecycle suites) stay in their own
//! modules — this file is only for semantics that must hold identically
//! across backends.

#![cfg(test)]

use std::sync::Arc;

use libpetri_core::action::{
    ActionError, fork, passthrough, produce, sync_action, transform,
};
use libpetri_core::arc::{inhibitor, read, reset};
use libpetri_core::input::{all, at_least, exactly, one};
use libpetri_core::match_spec::MatchSpec;
use libpetri_core::name::NameId;
use libpetri_core::output::{and, out_place, xor};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::token::Token;
use libpetri_core::transition::Transition;
use libpetri_event::event_store::{EventStore, InMemoryEventStore, NoopEventStore};
use libpetri_event::net_event::NetEvent;

use crate::compiled_net::CompiledNet;
use crate::executor::{BitmapNetExecutor, ExecutorOptions};
use crate::marking::Marking;
use crate::precompiled_executor::PrecompiledNetExecutor;
use crate::precompiled_net::PrecompiledNet;

/// Result of running a net to sync completion: the final marking, the
/// events captured along the way, and whether the executor quiesced.
pub(crate) struct RunResult {
    pub(crate) marking: Marking,
    pub(crate) events: Vec<NetEvent>,
    pub(crate) quiescent: bool,
}

/// Abstracts "compile this net, run it to sync completion, give me the
/// outcome" across the two executor backends. Each shared test is
/// generic over this trait; [`for_each_backend!`] instantiates it for
/// both backends.
pub(crate) trait BackendRunner {
    /// Run with an [`InMemoryEventStore`] so both marking-based and
    /// event-based assertions are available from one call. The marking
    /// outcome is independent of the event store, so this also serves
    /// the marking-only tests.
    fn run(net: &PetriNet, marking: Marking) -> RunResult;
}

/// Executable twin of the Lean `token_conservation` theorem (FR2): the final
/// marking must equal the initial marking plus every `TokenAdded` minus every
/// `TokenRemoved`. `TokenAdded` is emitted by the loop independently of what
/// the backend does with the token, so a backend that silently drops or
/// duplicates a token in its storage layer breaks the balance. Runs after
/// every suite run via [`BackendRunner::run`], and after every timed
/// differential run ([`differential_prop_tests`](crate::differential_prop_tests)).
pub(crate) fn assert_token_conservation(
    initial: &std::collections::HashMap<Arc<str>, usize>,
    result: &RunResult,
) {
    let mut expected: std::collections::HashMap<Arc<str>, i64> = initial
        .iter()
        .map(|(k, &v)| (Arc::clone(k), v as i64))
        .collect();
    for event in &result.events {
        match event {
            NetEvent::TokenAdded { place_name, .. } => {
                *expected.entry(Arc::clone(place_name)).or_default() += 1;
            }
            NetEvent::TokenRemoved { place_name, .. } => {
                *expected.entry(Arc::clone(place_name)).or_default() -= 1;
            }
            _ => {}
        }
    }
    let actual = result.marking.token_counts();
    for (place, &count) in &actual {
        assert_eq!(
            expected.get(place).copied().unwrap_or(0),
            count as i64,
            "token conservation violated: place '{place}' holds {count} token(s) \
             but initial marking + events account for a different number"
        );
    }
    for (place, &count) in &expected {
        assert!(
            count >= 0,
            "token conservation violated: place '{place}' saw more TokenRemoved \
             events than tokens it ever held"
        );
        if count > 0 {
            assert_eq!(
                actual.get(place).copied().unwrap_or(0) as i64,
                count,
                "token conservation violated: {count} token(s) unaccounted for at \
                 place '{place}' (dropped by the backend?)"
            );
        }
    }
}

pub(crate) struct BitmapRunner;

impl BackendRunner for BitmapRunner {
    fn run(net: &PetriNet, marking: Marking) -> RunResult {
        let initial_counts = marking.token_counts();
        let mut executor =
            BitmapNetExecutor::<InMemoryEventStore>::new(net, marking, ExecutorOptions::default());
        let final_marking = executor.run_sync().into_owned();
        let result = RunResult {
            marking: final_marking,
            events: executor.event_store().events().to_vec(),
            quiescent: executor.is_quiescent(),
        };
        assert_token_conservation(&initial_counts, &result);
        result
    }
}

pub(crate) struct PrecompiledRunner;

impl BackendRunner for PrecompiledRunner {
    fn run(net: &PetriNet, marking: Marking) -> RunResult {
        let initial_counts = marking.token_counts();
        let prog = PrecompiledNet::from_compiled(CompiledNet::compile(net));
        let mut executor = PrecompiledNetExecutor::<InMemoryEventStore>::builder(&prog, marking)
            .event_store(InMemoryEventStore::new())
            .build();
        let final_marking = executor.run_sync().into_owned();
        let result = RunResult {
            marking: final_marking,
            events: executor.event_store().events().to_vec(),
            quiescent: executor.is_quiescent(),
        };
        assert_token_conservation(&initial_counts, &result);
        result
    }
}

fn simple_chain() -> (PetriNet, Place<i32>, Place<i32>, Place<i32>) {
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let p3 = Place::<i32>::new("p3");

    // Both transitions are sinks: passthrough produces nothing, so neither may declare an
    // output spec (CORE-043).
    let t1 = Transition::builder("t1")
        .input(one(&p1))
        .action(passthrough())
        .build();
    let t2 = Transition::builder("t2")
        .input(one(&p2))
        .action(passthrough())
        .build();

    let net = PetriNet::builder("chain")
        .place(p3.as_ref())
        .transitions([t1, t2])
        .build();
    (net, p1, p2, p3)
}

// ========================= Basic flow =========================

fn sync_passthrough_chain<R: BackendRunner>() {
    let (net, p1, _p2, _p3) = simple_chain();
    let mut marking = Marking::new();
    marking.add(&p1, Token::at(42, 0));

    // passthrough produces no outputs, so the token is consumed and not re-emitted.
    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p1"), 0);
}

fn sync_with_event_store<R: BackendRunner>() {
    let (net, p1, _, _) = simple_chain();
    let mut marking = Marking::new();
    marking.add(&p1, Token::at(42, 0));

    let result = R::run(&net, marking);
    assert!(!result.events.is_empty());
}

fn sync_fork_chain<R: BackendRunner>() {
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let p3 = Place::<i32>::new("p3");

    let t1 = Transition::builder("t1")
        .input(one(&p1))
        .output(and(vec![out_place(&p2), out_place(&p3)]))
        .action(fork())
        .build();

    let net = PetriNet::builder("fork").transition(t1).build();

    let mut marking = Marking::new();
    marking.add(&p1, Token::at(42, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p1"), 0);
    assert_eq!(result.marking.count("p2"), 1);
    assert_eq!(result.marking.count("p3"), 1);
}

fn sync_no_initial_tokens<R: BackendRunner>() {
    let (net, _, _, _) = simple_chain();
    let result = R::run(&net, Marking::new());
    assert_eq!(result.marking.count("p1"), 0);
    assert_eq!(result.marking.count("p2"), 0);
    assert_eq!(result.marking.count("p3"), 0);
}

fn sync_linear_chain_5<R: BackendRunner>() {
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

    let mut marking = Marking::new();
    marking.add(&places[0], Token::at(1, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p0"), 0);
    assert_eq!(result.marking.count("p5"), 1);
}

fn single_transition_fires_once<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let out = Place::<i32>::new("out");
    let t = Transition::builder("t1")
        .input(one(&p))
        .output(out_place(&out))
        .action(fork())
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(42, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p"), 0);
    assert_eq!(result.marking.count("out"), 1);
}

fn many_tokens_all_processed<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let out = Place::<i32>::new("out");
    let t = Transition::builder("t1")
        .input(one(&p))
        .output(out_place(&out))
        .action(fork())
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    for i in 0..100 {
        marking.add(&p, Token::at(i, 0));
    }

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p"), 0);
    assert_eq!(result.marking.count("out"), 100);
}

fn input_fifo_ordering<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let out = Place::<i32>::new("out");
    let t = Transition::builder("t1")
        .input(one(&p))
        .output(out_place(&out))
        .action(fork())
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(1, 0));
    marking.add(&p, Token::at(2, 0));
    marking.add(&p, Token::at(3, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("out"), 3);
}

fn transition_with_no_output_consumes_only<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let t = Transition::builder("t1")
        .input(one(&p))
        .action(sync_action(|ctx| {
            let _ = ctx.input::<i32>("p")?;
            Ok(())
        }))
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(42, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p"), 0);
}

// ========================= Enablement / arcs =========================

fn input_arc_requires_token_to_enable<R: BackendRunner>() {
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let t = Transition::builder("t1")
        .input(one(&p1))
        .output(out_place(&p2))
        .action(fork())
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let result = R::run(&net, Marking::new());
    assert_eq!(result.marking.count("p1"), 0);
    assert_eq!(result.marking.count("p2"), 0);
}

fn multiple_input_arcs_require_all<R: BackendRunner>() {
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let p3 = Place::<i32>::new("p3");

    let make = || {
        Transition::builder("t1")
            .input(one(&p1))
            .input(one(&p2))
            .output(out_place(&p3))
            .action(sync_action(|ctx| {
                ctx.output("p3", 99i32)?;
                Ok(())
            }))
            .build()
    };

    // Only p1 has a token — should not fire.
    let net = PetriNet::builder("test").transition(make()).build();
    let mut marking = Marking::new();
    marking.add(&p1, Token::at(1, 0));
    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p1"), 1);
    assert_eq!(result.marking.count("p3"), 0);

    // Both p1 and p2 have tokens — should fire.
    let net = PetriNet::builder("test").transition(make()).build();
    let mut marking = Marking::new();
    marking.add(&p1, Token::at(1, 0));
    marking.add(&p2, Token::at(2, 0));
    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p1"), 0);
    assert_eq!(result.marking.count("p2"), 0);
    assert_eq!(result.marking.count("p3"), 1);
}

fn read_arc_does_not_consume<R: BackendRunner>() {
    let p_in = Place::<i32>::new("in");
    let p_ctx = Place::<i32>::new("ctx");
    let p_out = Place::<i32>::new("out");

    let t = Transition::builder("t1")
        .input(one(&p_in))
        .read(read(&p_ctx))
        .output(out_place(&p_out))
        .action(sync_action(|ctx| {
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

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("in"), 0); // consumed
    assert_eq!(result.marking.count("ctx"), 1); // NOT consumed (read arc)
    assert_eq!(result.marking.count("out"), 1);
    assert_eq!(*result.marking.peek(&p_out).unwrap(), 15);
}

fn reset_arc_removes_all_tokens<R: BackendRunner>() {
    let p_in = Place::<()>::new("in");
    let p_reset = Place::<i32>::new("reset");
    let p_out = Place::<()>::new("out");

    let t = Transition::builder("t1")
        .input(one(&p_in))
        .reset(reset(&p_reset))
        .output(out_place(&p_out))
        .action(fork())
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p_in, Token::at((), 0));
    marking.add(&p_reset, Token::at(1, 0));
    marking.add(&p_reset, Token::at(2, 0));
    marking.add(&p_reset, Token::at(3, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("reset"), 0); // all cleared
    assert_eq!(result.marking.count("out"), 1);
}

fn combined_input_read_reset<R: BackendRunner>() {
    let p_in = Place::<i32>::new("in");
    let p_ctx = Place::<String>::new("ctx");
    let p_clear = Place::<i32>::new("clear");
    let p_out = Place::<String>::new("out");

    let t = Transition::builder("t1")
        .input(one(&p_in))
        .read(read(&p_ctx))
        .reset(reset(&p_clear))
        .output(out_place(&p_out))
        .action(sync_action(|ctx| {
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

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("in"), 0); // consumed
    assert_eq!(result.marking.count("ctx"), 1); // read, not consumed
    assert_eq!(result.marking.count("clear"), 0); // reset
    assert_eq!(result.marking.count("out"), 1);
    assert_eq!(*result.marking.peek(&p_out).unwrap(), "42-hello");
}

// ========================= Inhibitors =========================

fn sync_inhibitor_blocks<R: BackendRunner>() {
    let p1 = Place::<()>::new("p1");
    let p2 = Place::<()>::new("p2");
    let p_inh = Place::<()>::new("inh");

    let t = Transition::builder("t1")
        .input(one(&p1))
        .output(out_place(&p2))
        .inhibitor(inhibitor(&p_inh))
        .action(fork())
        .build();

    let net = PetriNet::builder("inhibitor").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p1, Token::at((), 0));
    marking.add(&p_inh, Token::at((), 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p1"), 1); // blocked
}

fn inhibitor_unblocked_when_token_removed<R: BackendRunner>() {
    let p1 = Place::<()>::new("p1");
    let p_inh = Place::<()>::new("inh");
    let p_out = Place::<()>::new("out");
    let p_trigger = Place::<()>::new("trigger");

    // t_clear consumes from inh (higher priority, fires first).
    let t_clear = Transition::builder("t_clear")
        .input(one(&p_inh))
        .output(out_place(&p_trigger))
        .action(fork())
        .priority(10)
        .build();

    // t1 consumes from p1, inhibited by inh.
    let t1 = Transition::builder("t1")
        .input(one(&p1))
        .inhibitor(inhibitor(&p_inh))
        .output(out_place(&p_out))
        .action(fork())
        .priority(1)
        .build();

    let net = PetriNet::builder("test").transitions([t_clear, t1]).build();

    let mut marking = Marking::new();
    marking.add(&p1, Token::at((), 0));
    marking.add(&p_inh, Token::at((), 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("inh"), 0);
    assert_eq!(result.marking.count("p1"), 0);
    assert_eq!(result.marking.count("out"), 1);
}

// ==================== Cardinality / conditional routing ====================

fn exactly_cardinality_consumes_n<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let p_out = Place::<i32>::new("out");

    let t = Transition::builder("t1")
        .input(exactly(3, &p))
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

    let mut marking = Marking::new();
    for i in 0..5 {
        marking.add(&p, Token::at(i, 0));
    }

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p"), 2);
    assert_eq!(result.marking.count("out"), 3);
}

fn all_cardinality_consumes_everything<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let p_out = Place::<()>::new("out");

    let t = Transition::builder("t1")
        .input(all(&p))
        .output(out_place(&p_out))
        .action(sync_action(|ctx| {
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

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p"), 0);
}

fn at_least_blocks_insufficient<R: BackendRunner>() {
    let p = Place::<i32>::new("p");

    // Sink: the point is the cardinality gate (CORE-043 forbids passthrough + output spec).
    let t = Transition::builder("t1")
        .input(at_least(3, &p))
        .action(passthrough())
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(1, 0));
    marking.add(&p, Token::at(2, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p"), 2); // not consumed
}

fn at_least_fires_with_enough<R: BackendRunner>() {
    let p = Place::<i32>::new("p");

    let t = Transition::builder("t1")
        .input(at_least(3, &p))
        .action(passthrough())
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    for i in 0..5 {
        marking.add(&p, Token::at(i, 0));
    }

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p"), 0); // all consumed
}

// Conditional token selection (IO-006 replacement idiom): input specifications
// are purely structural, so a data-dependent choice is modelled with a
// classifier transition whose XOR output routes each token into exactly one
// downstream place, plus conflicting transitions consuming those places.

fn xor_routing_only_forwards_matching<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let big = Place::<i32>::new("big");
    let small = Place::<i32>::new("small");
    let p_out = Place::<i32>::new("out");

    let classify = Transition::builder("classify")
        .input(one(&p))
        .output(xor(vec![out_place(&big), out_place(&small)]))
        .action(sync_action(|ctx| {
            let v = *ctx.input::<i32>("p")?;
            if v > 5 {
                ctx.output("big", v)?;
            } else {
                ctx.output("small", v)?;
            }
            Ok(())
        }))
        .build();
    let consume = Transition::builder("t1")
        .input(one(&big))
        .output(out_place(&p_out))
        .action(fork())
        .build();
    let net = PetriNet::builder("test")
        .transitions([classify, consume])
        .build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(3, 0)); // routed to `small`
    marking.add(&p, Token::at(10, 0)); // routed to `big`

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("small"), 1); // 3 lands in the other branch
    assert_eq!(result.marking.count("big"), 0);
    assert_eq!(result.marking.count("out"), 1); // 10 forwarded
    assert_eq!(*result.marking.peek(&p_out).unwrap(), 10);
}

fn xor_routing_blocks_when_nothing_routed<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let big = Place::<i32>::new("big");
    let small = Place::<i32>::new("small");
    let p_out = Place::<i32>::new("out");

    let classify = Transition::builder("classify")
        .input(one(&p))
        .output(xor(vec![out_place(&big), out_place(&small)]))
        .action(sync_action(|ctx| {
            let v = *ctx.input::<i32>("p")?;
            if v > 100 {
                ctx.output("big", v)?;
            } else {
                ctx.output("small", v)?;
            }
            Ok(())
        }))
        .build();
    let consume = Transition::builder("t1")
        .input(one(&big))
        .output(out_place(&p_out))
        .action(fork())
        .build();
    let net = PetriNet::builder("test")
        .transitions([classify, consume])
        .build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(3, 0));
    marking.add(&p, Token::at(10, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("small"), 2);
    assert_eq!(result.marking.count("big"), 0);
    assert_eq!(result.marking.count("out"), 0);
}

fn self_loop_with_xor_routing_terminates<R: BackendRunner>() {
    // Decrement until 0, then move to done. The "keep going vs. stop" choice
    // lives in the classifier's XOR output, not in an input predicate.
    let p = Place::<i32>::new("p");
    let positive = Place::<i32>::new("positive");
    let zero = Place::<i32>::new("zero");
    let done = Place::<i32>::new("done");

    let classify = Transition::builder("classify")
        .input(one(&p))
        .output(xor(vec![out_place(&positive), out_place(&zero)]))
        .action(sync_action(|ctx| {
            let v = *ctx.input::<i32>("p")?;
            if v > 0 {
                ctx.output("positive", v)?;
            } else {
                ctx.output("zero", v)?;
            }
            Ok(())
        }))
        .build();

    let t = Transition::builder("dec")
        .input(one(&positive))
        .output(out_place(&p))
        .action(sync_action(|ctx| {
            let v = ctx.input::<i32>("positive")?;
            ctx.output("p", *v - 1)?;
            Ok(())
        }))
        .build();

    let t_done = Transition::builder("finish")
        .input(one(&zero))
        .output(out_place(&done))
        .action(fork())
        .build();

    let net = PetriNet::builder("countdown")
        .transitions([classify, t, t_done])
        .build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(3, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("done"), 1);
    assert_eq!(*result.marking.peek(&done).unwrap(), 0);
}

// ========================= Actions / outputs =========================

fn transform_action_outputs_to_all_places<R: BackendRunner>() {
    let p_in = Place::<i32>::new("in");
    let p_a = Place::<i32>::new("a");
    let p_b = Place::<i32>::new("b");

    let t = Transition::builder("t1")
        .input(one(&p_in))
        .output(and(vec![out_place(&p_a), out_place(&p_b)]))
        .action(transform(|ctx| {
            let v = ctx.input::<i32>("in").unwrap();
            Arc::new(*v * 2) as Arc<dyn std::any::Any + Send + Sync>
        }))
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p_in, Token::at(5, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("a"), 1);
    assert_eq!(result.marking.count("b"), 1);
    assert_eq!(*result.marking.peek(&p_a).unwrap(), 10);
    assert_eq!(*result.marking.peek(&p_b).unwrap(), 10);
}

fn sync_action_custom_logic<R: BackendRunner>() {
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

    let mut marking = Marking::new();
    marking.add(&p_in, Token::at(42, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("out"), 1);
    assert_eq!(*result.marking.peek(&p_out).unwrap(), "value=42");
}

fn produce_action<R: BackendRunner>() {
    let p_in = Place::<()>::new("in");
    let p_out = Place::<String>::new("out");

    let t = Transition::builder("t1")
        .input(one(&p_in))
        .output(out_place(&p_out))
        .action(produce(Arc::from("out"), "produced_value".to_string()))
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p_in, Token::at((), 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("out"), 1);
}

fn xor_output_fires_one_branch<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let a = Place::<i32>::new("a");
    let b = Place::<i32>::new("b");

    let t = Transition::builder("t1")
        .input(one(&p))
        .output(xor(vec![out_place(&a), out_place(&b)]))
        .action(sync_action(|ctx| {
            let v = ctx.input::<i32>("p")?;
            ctx.output("a", *v)?;
            Ok(())
        }))
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(1, 0));

    let result = R::run(&net, marking);
    let total = result.marking.count("a") + result.marking.count("b");
    assert!(total >= 1);
}

fn and_output_fires_to_all<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let a = Place::<i32>::new("a");
    let b = Place::<i32>::new("b");
    let c = Place::<i32>::new("c");

    let t = Transition::builder("t1")
        .input(one(&p))
        .output(and(vec![out_place(&a), out_place(&b), out_place(&c)]))
        .action(sync_action(|ctx| {
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

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("a"), 1);
    assert_eq!(result.marking.count("b"), 1);
    assert_eq!(result.marking.count("c"), 1);
    assert_eq!(*result.marking.peek(&a).unwrap(), 1);
    assert_eq!(*result.marking.peek(&b).unwrap(), 10);
    assert_eq!(*result.marking.peek(&c).unwrap(), 100);
}

// ================= [IO-015] Output validation =================

/// Helper: was a `TransitionFailed` for `name` emitted, and does its
/// message mention the IO-015 violation?
fn out_violation_failed(events: &[NetEvent], name: &str) -> bool {
    events.iter().any(|e| match e {
        NetEvent::TransitionFailed {
            transition_name,
            error,
            ..
        } => &**transition_name == name && error.contains("IO-015"),
        _ => false,
    })
}

/// \[IO-015\] AC2/AC3: an `Out::Xor` declares "exactly one branch". An
/// action that writes to *both* branches violates the contract — the
/// firing fails, no tokens are deposited on either branch, and the
/// consumed input is NOT restored.
fn xor_output_both_branches_violates<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let a = Place::<i32>::new("a");
    let b = Place::<i32>::new("b");

    let t = Transition::builder("t1")
        .input(one(&p))
        .output(xor(vec![out_place(&a), out_place(&b)]))
        .action(sync_action(|ctx| {
            let v = ctx.input::<i32>("p")?;
            ctx.output("a", *v)?;
            ctx.output("b", *v)?;
            Ok(())
        }))
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(1, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("a"), 0, "XOR violation must produce nothing");
    assert_eq!(result.marking.count("b"), 0, "XOR violation must produce nothing");
    // AC3: consumed input tokens are not restored.
    assert_eq!(result.marking.count("p"), 0);
    assert!(
        out_violation_failed(&result.events, "t1"),
        "expected an IO-015 TransitionFailed event, got {:?}",
        result.events
    );
}

/// \[IO-015\] AC2: an `Out::Xor` with *no* branch produced is equally a
/// violation ("exactly 1 required").
fn xor_output_no_branch_violates<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let a = Place::<i32>::new("a");
    let b = Place::<i32>::new("b");

    let t = Transition::builder("t1")
        .input(one(&p))
        .output(xor(vec![out_place(&a), out_place(&b)]))
        .action(sync_action(|_ctx| Ok(())))
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(1, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("a"), 0);
    assert_eq!(result.marking.count("b"), 0);
    assert_eq!(result.marking.count("p"), 0);
    assert!(out_violation_failed(&result.events, "t1"));
}

/// \[IO-015\] AC2/AC3: an `Out::And` requires *all* children. Writing to
/// only one child fails the firing and deposits nothing at all — not
/// even the child that was written.
fn and_output_partial_violates<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let a = Place::<i32>::new("a");
    let b = Place::<i32>::new("b");

    let t = Transition::builder("t1")
        .input(one(&p))
        .output(and(vec![out_place(&a), out_place(&b)]))
        .action(sync_action(|ctx| {
            let v = ctx.input::<i32>("p")?;
            ctx.output("a", *v)?;
            Ok(())
        }))
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(1, 0));

    let result = R::run(&net, marking);
    assert_eq!(
        result.marking.count("a"),
        0,
        "AND violation must not deposit the partially-written branch"
    );
    assert_eq!(result.marking.count("b"), 0);
    assert_eq!(result.marking.count("p"), 0);
    assert!(out_violation_failed(&result.events, "t1"));
}

/// \[IO-015\] AC2: a plain `out_place` spec is violated when the action
/// produces nothing (the single-leaf fast path in the executor).
fn single_place_output_missing_violates<R: BackendRunner>() {
    let p_in = Place::<i32>::new("in");
    let p_out = Place::<i32>::new("out");

    let t = Transition::builder("t1")
        .input(one(&p_in))
        .output(out_place(&p_out))
        .action(sync_action(|_ctx| Ok(())))
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p_in, Token::at(7, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("out"), 0);
    assert_eq!(result.marking.count("in"), 0);
    assert!(out_violation_failed(&result.events, "t1"));
}

/// \[IO-015\] AC1: conforming output still succeeds. Guards against an
/// over-eager validator rejecting legitimate firings — covers the
/// single-place, AND, XOR and "extra place also written" shapes plus a
/// spec-less transition.
fn conforming_output_still_succeeds<R: BackendRunner>() {
    let start = Place::<i32>::new("start");
    let a = Place::<i32>::new("a");
    let b = Place::<i32>::new("b");
    let x = Place::<i32>::new("x");
    let y = Place::<i32>::new("y");
    let done = Place::<i32>::new("done");

    // AND: writes both children.
    let t_and = Transition::builder("t_and")
        .input(one(&start))
        .output(and(vec![out_place(&a), out_place(&b)]))
        .action(sync_action(|ctx| {
            let v = ctx.input::<i32>("start")?;
            ctx.output("a", *v)?;
            ctx.output("b", *v)?;
            Ok(())
        }))
        .build();

    // XOR: writes exactly one child.
    let t_xor = Transition::builder("t_xor")
        .input(one(&a))
        .output(xor(vec![out_place(&x), out_place(&y)]))
        .action(sync_action(|ctx| {
            let v = ctx.input::<i32>("a")?;
            ctx.output("x", *v)?;
            Ok(())
        }))
        .build();

    // Single place, declared spec satisfied (the fast path).
    let t_place = Transition::builder("t_place")
        .input(one(&x))
        .output(out_place(&done))
        .action(fork())
        .build();

    // No declared output spec at all — validation must be skipped
    // entirely even though the action produces nothing.
    let t_nospec = Transition::builder("t_nospec")
        .input(one(&b))
        .action(passthrough())
        .build();

    let net = PetriNet::builder("conforming")
        .transitions([t_and, t_xor, t_place, t_nospec])
        .build();

    let mut marking = Marking::new();
    marking.add(&start, Token::at(3, 0));

    let result = R::run(&net, marking);
    assert!(
        !result
            .events
            .iter()
            .any(|e| matches!(e, NetEvent::TransitionFailed { .. })),
        "conforming net must not emit any TransitionFailed, got {:?}",
        result.events
    );
    assert_eq!(result.marking.count("done"), 1);
    assert_eq!(result.marking.count("b"), 0, "t_nospec consumed its input");
    assert_eq!(result.marking.count("y"), 0);
}

/// \[IO-015\]: a satisfied XOR branch that *also* writes places belonging
/// to another branch of a nested AND is resolved by the most-specific
/// (subsuming) match, matching the Java/TypeScript tie-break.
fn xor_subsuming_branch_is_accepted<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let a = Place::<i32>::new("a");
    let b = Place::<i32>::new("b");
    let c = Place::<i32>::new("c");

    let t = Transition::builder("t1")
        .input(one(&p))
        // xor(and(a,b,c), and(a,b)) — writing a,b,c satisfies both, but
        // and(a,b,c) subsumes and(a,b), so it is the intended branch.
        .output(xor(vec![
            and(vec![out_place(&a), out_place(&b), out_place(&c)]),
            and(vec![out_place(&a), out_place(&b)]),
        ]))
        .action(sync_action(|ctx| {
            let v = ctx.input::<i32>("p")?;
            ctx.output("a", *v)?;
            ctx.output("b", *v)?;
            ctx.output("c", *v)?;
            Ok(())
        }))
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(1, 0));

    let result = R::run(&net, marking);
    assert!(
        !out_violation_failed(&result.events, "t1"),
        "subsuming XOR branch must be accepted, got {:?}",
        result.events
    );
    assert_eq!(result.marking.count("a"), 1);
    assert_eq!(result.marking.count("b"), 1);
    assert_eq!(result.marking.count("c"), 1);
}

fn action_error_does_not_crash<R: BackendRunner>() {
    let p_in = Place::<i32>::new("in");
    let p_out = Place::<i32>::new("out");

    let t = Transition::builder("t1")
        .input(one(&p_in))
        .output(out_place(&p_out))
        .action(sync_action(|_ctx| {
            Err(ActionError::new("intentional failure"))
        }))
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p_in, Token::at(42, 0));

    let result = R::run(&net, marking);
    // Token consumed even though the action failed.
    assert_eq!(result.marking.count("in"), 0);
    assert_eq!(result.marking.count("out"), 0);
    assert!(
        result
            .events
            .iter()
            .any(|e| matches!(e, NetEvent::TransitionFailed { .. }))
    );
}

fn multiple_tokens_different_types<R: BackendRunner>() {
    let p_int = Place::<i32>::new("ints");
    let p_str = Place::<String>::new("strs");
    let p_out = Place::<String>::new("out");

    let t = Transition::builder("combine")
        .input(one(&p_int))
        .input(one(&p_str))
        .output(out_place(&p_out))
        .action(sync_action(|ctx| {
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

    let result = R::run(&net, marking);
    assert_eq!(*result.marking.peek(&p_out).unwrap(), "hello-42");
}

// ========================= Scheduling =========================

fn sync_priority_ordering<R: BackendRunner>() {
    let p = Place::<()>::new("p");
    let out_a = Place::<()>::new("a");
    let out_b = Place::<()>::new("b");

    let t_high = Transition::builder("t_high")
        .input(one(&p))
        .output(out_place(&out_a))
        .action(fork())
        .priority(10)
        .build();
    let t_low = Transition::builder("t_low")
        .input(one(&p))
        .output(out_place(&out_b))
        .action(fork())
        .priority(1)
        .build();

    let net = PetriNet::builder("priority")
        .transitions([t_high, t_low])
        .build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at((), 0));

    // Single token; the higher-priority transition consumes it and forks it to "a".
    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p"), 0);
    assert_eq!(result.marking.count("a"), 1);
    assert_eq!(result.marking.count("b"), 0);
}

fn priority_higher_fires_first<R: BackendRunner>() {
    let p = Place::<()>::new("p");
    let out_hi = Place::<()>::new("hi");
    let out_lo = Place::<()>::new("lo");

    let t_hi = Transition::builder("hi")
        .input(one(&p))
        .output(out_place(&out_hi))
        .action(fork())
        .priority(10)
        .build();
    let t_lo = Transition::builder("lo")
        .input(one(&p))
        .output(out_place(&out_lo))
        .action(fork())
        .priority(1)
        .build();

    let net = PetriNet::builder("test").transitions([t_hi, t_lo]).build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at((), 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("hi"), 1);
    assert_eq!(result.marking.count("lo"), 0);
}

fn multiple_transitions_same_input_compete<R: BackendRunner>() {
    let p1 = Place::<()>::new("p1");
    let out_a = Place::<()>::new("a");
    let out_b = Place::<()>::new("b");

    let t_a = Transition::builder("ta")
        .input(one(&p1))
        .output(out_place(&out_a))
        .action(fork())
        .build();
    let t_b = Transition::builder("tb")
        .input(one(&p1))
        .output(out_place(&out_b))
        .action(fork())
        .build();

    let net = PetriNet::builder("test").transitions([t_a, t_b]).build();

    let mut marking = Marking::new();
    marking.add(&p1, Token::at((), 0));

    let result = R::run(&net, marking);
    let total = result.marking.count("a") + result.marking.count("b");
    assert_eq!(total, 1);
    assert_eq!(result.marking.count("p1"), 0);
}

// ========================= Topologies =========================

fn diamond_pattern<R: BackendRunner>() {
    let p1 = Place::<()>::new("p1");
    let p2 = Place::<()>::new("p2");
    let p3 = Place::<()>::new("p3");
    let p4 = Place::<()>::new("p4");

    let t1 = Transition::builder("t1")
        .input(one(&p1))
        .output(and(vec![out_place(&p2), out_place(&p3)]))
        .action(fork())
        .build();
    let t2 = Transition::builder("t2")
        .input(one(&p2))
        .output(out_place(&p4))
        .action(fork())
        .build();
    let t3 = Transition::builder("t3")
        .input(one(&p3))
        .output(out_place(&p4))
        .action(fork())
        .build();

    let net = PetriNet::builder("diamond")
        .transitions([t1, t2, t3])
        .build();

    let mut marking = Marking::new();
    marking.add(&p1, Token::at((), 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p4"), 2);
}

fn workflow_sequential_chain<R: BackendRunner>() {
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let p3 = Place::<i32>::new("p3");
    let p4 = Place::<i32>::new("p4");

    let make_doubler = |name: &str, inp: &Place<i32>, outp: &Place<i32>| {
        let out_name: Arc<str> = Arc::from(outp.name());
        Transition::builder(name)
            .input(one(inp))
            .output(out_place(outp))
            .action(sync_action(move |ctx| {
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

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p4"), 1);
    assert_eq!(*result.marking.peek(&p4).unwrap(), 8); // 1 * 2 * 2 * 2
}

fn workflow_fork_join<R: BackendRunner>() {
    let p_start = Place::<i32>::new("start");
    let p_a = Place::<i32>::new("a");
    let p_b = Place::<i32>::new("b");
    let p_end = Place::<i32>::new("end");

    let t_fork = Transition::builder("fork")
        .input(one(&p_start))
        .output(and(vec![out_place(&p_a), out_place(&p_b)]))
        .action(fork())
        .build();

    let t_join = Transition::builder("join")
        .input(one(&p_a))
        .input(one(&p_b))
        .output(out_place(&p_end))
        .action(sync_action(|ctx| {
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

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("start"), 0);
    assert_eq!(result.marking.count("a"), 0);
    assert_eq!(result.marking.count("b"), 0);
    assert_eq!(result.marking.count("end"), 1);
    assert_eq!(*result.marking.peek(&p_end).unwrap(), 10);
}

fn workflow_mutual_exclusion<R: BackendRunner>() {
    let p_mutex = Place::<()>::new("mutex");
    let p_w1 = Place::<()>::new("w1");
    let p_w2 = Place::<()>::new("w2");
    let p_done1 = Place::<()>::new("done1");
    let p_done2 = Place::<()>::new("done2");

    let t_w1 = Transition::builder("work1")
        .input(one(&p_w1))
        .input(one(&p_mutex))
        .output(and(vec![out_place(&p_done1), out_place(&p_mutex)]))
        .action(sync_action(|ctx| {
            ctx.output("done1", ())?;
            ctx.output("mutex", ())?;
            Ok(())
        }))
        .build();

    let t_w2 = Transition::builder("work2")
        .input(one(&p_w2))
        .input(one(&p_mutex))
        .output(and(vec![out_place(&p_done2), out_place(&p_mutex)]))
        .action(sync_action(|ctx| {
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

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("done1"), 1);
    assert_eq!(result.marking.count("done2"), 1);
    assert_eq!(result.marking.count("mutex"), 1); // returned
}

fn complex_workflow<R: BackendRunner>() {
    let input = Place::<i32>::new("v_input");
    let guard_in = Place::<i32>::new("v_guardIn");
    let intent_in = Place::<i32>::new("v_intentIn");
    let search_in = Place::<i32>::new("v_searchIn");
    let output_guard_in = Place::<i32>::new("v_outputGuardIn");
    let guard_safe = Place::<i32>::new("v_guardSafe");
    let guard_violation = Place::<i32>::new("v_guardViolation");
    let violated = Place::<i32>::new("v_violated");
    let intent_ready = Place::<i32>::new("v_intentReady");
    let topic_ready = Place::<i32>::new("v_topicReady");
    let search_ready = Place::<i32>::new("v_searchReady");
    let output_guard_done = Place::<i32>::new("v_outputGuardDone");
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
        .output(out_place(&violated))
        .inhibitor(inhibitor(&guard_safe))
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
        .read(read(&intent_ready))
        .inhibitor(inhibitor(&guard_violation))
        .priority(-5)
        .action(fork())
        .build();

    let output_guard_trans = Transition::builder("OutputGuard")
        .input(one(&output_guard_in))
        .output(out_place(&output_guard_done))
        .read(read(&guard_safe))
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

    let mut marking = Marking::new();
    marking.add(&input, Token::at(1, 0));

    // fork() produces to ALL output places, including both XOR branches,
    // so Search is inhibited and deadlocks. The contract being checked is
    // that the executor terminates without crashing and consumed the input.
    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("v_input"), 0);
}

// ========================= Lifecycle / events =========================

fn empty_net_completes<R: BackendRunner>() {
    let net = PetriNet::builder("empty").build();
    let result = R::run(&net, Marking::new());
    assert!(result.quiescent);
}

fn quiescent_when_no_enabled_transitions<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let out = Place::<i32>::new("out");

    let t = Transition::builder("t1")
        .input(one(&p))
        .output(out_place(&out))
        .action(fork())
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p, Token::at(1, 0));

    let result = R::run(&net, marking);
    assert!(result.quiescent);
}

fn event_store_records_lifecycle<R: BackendRunner>() {
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let t = Transition::builder("t1")
        .input(one(&p1))
        .output(out_place(&p2))
        .action(fork())
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p1, Token::at(1, 0));

    let result = R::run(&net, marking);
    let e = &result.events;
    assert!(e.iter().any(|x| matches!(x, NetEvent::ExecutionStarted { .. })));
    assert!(e.iter().any(|x| matches!(x, NetEvent::TransitionEnabled { .. })));
    assert!(e.iter().any(|x| matches!(x, NetEvent::TransitionStarted { .. })));
    assert!(e.iter().any(|x| matches!(x, NetEvent::TransitionCompleted { .. })));
    assert!(e.iter().any(|x| matches!(x, NetEvent::TokenRemoved { .. })));
    assert!(e.iter().any(|x| matches!(x, NetEvent::TokenAdded { .. })));
    assert!(e.iter().any(|x| matches!(x, NetEvent::ExecutionCompleted { .. })));
}

fn event_store_transition_enabled_disabled<R: BackendRunner>() {
    let p1 = Place::<()>::new("p1");
    let p2 = Place::<()>::new("p2");

    let t = Transition::builder("t1")
        .input(one(&p1))
        .output(out_place(&p2))
        .action(fork())
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p1, Token::at((), 0));

    let result = R::run(&net, marking);
    assert!(result.events.len() >= 4);
    let has_enabled = result.events.iter().any(|e| {
        matches!(e, NetEvent::TransitionEnabled { transition_name, .. } if transition_name.as_ref() == "t1")
    });
    assert!(has_enabled);
}

/// Verifies `NoopEventStore` truly records nothing — a property of the
/// store, not the executor semantics, so it runs once against each
/// backend's noop path rather than through the [`BackendRunner`]
/// (which always uses an in-memory store).
#[test]
fn noop_event_store_has_no_events() {
    let p1 = Place::<i32>::new("p1");
    let p2 = Place::<i32>::new("p2");
    let t = Transition::builder("t1")
        .input(one(&p1))
        .output(out_place(&p2))
        .action(fork())
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p1, Token::at(1, 0));
    let mut bitmap =
        BitmapNetExecutor::<NoopEventStore>::new(&net, marking, ExecutorOptions::default());
    bitmap.run_sync();
    assert!(bitmap.event_store().is_empty());

    let mut marking = Marking::new();
    marking.add(&p1, Token::at(1, 0));
    let prog = PrecompiledNet::from_compiled(CompiledNet::compile(&net));
    let mut precompiled = PrecompiledNetExecutor::<NoopEventStore>::new(&prog, marking);
    precompiled.run_sync();
    assert!(precompiled.event_store().is_empty());
}

// ========================= ν-net fork/join (NU) =========================

/// A correlated payload: an opaque correlation id plus (unused here) data.
#[derive(Clone)]
struct NuMsg {
    cid: String,
}

/// NU-020: a join with a `MatchSpec` correlates by name equality, NOT by FIFO.
/// Branch arrival order is reversed so a FIFO join would pair X with Y; the
/// name match must instead pair X-X and Y-Y.
fn nu_join_matches_by_name_not_fifo<R: BackendRunner>() {
    let a = Place::<NuMsg>::new("branchA");
    let b = Place::<NuMsg>::new("branchB");
    let merged = Place::<String>::new("merged");

    let join = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .match_spec(
            MatchSpec::builder()
                .key(&a, |m: &NuMsg| NameId::new(m.cid.clone()))
                .key(&b, |m: &NuMsg| NameId::new(m.cid.clone()))
                .build(),
        )
        .output(out_place(&merged))
        .action(sync_action(|ctx| {
            let ma = ctx.input::<NuMsg>("branchA")?;
            let mb = ctx.input::<NuMsg>("branchB")?;
            ctx.output("merged", format!("{}+{}", ma.cid, mb.cid))?;
            Ok(())
        }))
        .build();

    let net = PetriNet::builder("nu_join").transition(join).build();

    let mut marking = Marking::new();
    marking.add(&a, Token::at(NuMsg { cid: "X".into() }, 0));
    marking.add(&a, Token::at(NuMsg { cid: "Y".into() }, 1));
    marking.add(&b, Token::at(NuMsg { cid: "Y".into() }, 0));
    marking.add(&b, Token::at(NuMsg { cid: "X".into() }, 1));

    let result = R::run(&net, marking);
    assert!(result.quiescent);

    let mut merged_vals: Vec<String> = result
        .marking
        .queue("merged")
        .map(|q| {
            q.iter()
                .map(|t| t.downcast::<String>().unwrap().value().clone())
                .collect()
        })
        .unwrap_or_default();
    merged_vals.sort();
    assert_eq!(merged_vals, vec!["X+X".to_string(), "Y+Y".to_string()]);
    for v in &merged_vals {
        let (l, r) = v.split_once('+').unwrap();
        assert_eq!(l, r, "join correlated mismatched ids: {v}");
    }
}

/// NU-030 regression: binding a join's action via `bind_actions` must NOT drop
/// its `match_spec`. `rebuild_with_action` rebuilds the transition to attach the
/// action; if it dropped the match the correlated join would revert to a plain
/// FIFO AND join — pairing X+Y / Y+X across generations instead of the
/// correlated X+X / Y+Y. Verified on both executor backends.
fn nu_bound_join_matches_by_name_not_fifo<R: BackendRunner>() {
    let a = Place::<NuMsg>::new("branchA");
    let b = Place::<NuMsg>::new("branchB");
    let merged = Place::<String>::new("merged");

    // Built with a match but only a placeholder action; the real merging action
    // is attached via `bind_actions`, exercising `rebuild_with_action`.
    let join = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .match_spec(
            MatchSpec::builder()
                .key(&a, |m: &NuMsg| NameId::new(m.cid.clone()))
                .key(&b, |m: &NuMsg| NameId::new(m.cid.clone()))
                .build(),
        )
        .output(out_place(&merged))
        .action(passthrough())
        .build();

    let net = PetriNet::builder("nu_bound_join").transition(join).build();

    let mut bindings = std::collections::HashMap::new();
    bindings.insert(
        "join".to_string(),
        sync_action(|ctx| {
            let ma = ctx.input::<NuMsg>("branchA")?;
            let mb = ctx.input::<NuMsg>("branchB")?;
            ctx.output("merged", format!("{}+{}", ma.cid, mb.cid))?;
            Ok(())
        }),
    );
    let net = net.bind_actions(&bindings);

    let mut marking = Marking::new();
    marking.add(&a, Token::at(NuMsg { cid: "X".into() }, 0));
    marking.add(&a, Token::at(NuMsg { cid: "Y".into() }, 1));
    marking.add(&b, Token::at(NuMsg { cid: "Y".into() }, 0));
    marking.add(&b, Token::at(NuMsg { cid: "X".into() }, 1));

    let result = R::run(&net, marking);
    assert!(result.quiescent);

    let mut merged_vals: Vec<String> = result
        .marking
        .queue("merged")
        .map(|q| {
            q.iter()
                .map(|t| t.downcast::<String>().unwrap().value().clone())
                .collect()
        })
        .unwrap_or_default();
    merged_vals.sort();
    assert_eq!(merged_vals, vec!["X+X".to_string(), "Y+Y".to_string()]);
    for v in &merged_vals {
        let (l, r) = v.split_once('+').unwrap();
        assert_eq!(l, r, "bound join correlated mismatched ids: {v}");
    }
}

/// NU-020: with no name present in both inputs, the join is never enabled —
/// the tokens stay put and nothing is produced.
fn nu_join_blocks_without_matching_name<R: BackendRunner>() {
    let a = Place::<NuMsg>::new("branchA");
    let b = Place::<NuMsg>::new("branchB");
    let merged = Place::<String>::new("merged");

    let join = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .match_spec(
            MatchSpec::builder()
                .key(&a, |m: &NuMsg| NameId::new(m.cid.clone()))
                .key(&b, |m: &NuMsg| NameId::new(m.cid.clone()))
                .build(),
        )
        .output(out_place(&merged))
        .action(sync_action(|ctx| {
            let ma = ctx.input::<NuMsg>("branchA")?;
            let mb = ctx.input::<NuMsg>("branchB")?;
            ctx.output("merged", format!("{}+{}", ma.cid, mb.cid))?;
            Ok(())
        }))
        .build();

    let net = PetriNet::builder("nu_join_block").transition(join).build();

    let mut marking = Marking::new();
    marking.add(&a, Token::at(NuMsg { cid: "X".into() }, 0));
    marking.add(&b, Token::at(NuMsg { cid: "Y".into() }, 0));

    let result = R::run(&net, marking);
    assert!(result.quiescent);
    assert_eq!(result.marking.count("merged"), 0);
    assert_eq!(result.marking.count("branchA"), 1);
    assert_eq!(result.marking.count("branchB"), 1);
}

/// NU-020/NU-021: name correlation is the *only* per-token filter the
/// enablement check applies — input specifications are purely structural
/// (IO-006). A name held by just one side can never join, even when both
/// inputs hold enough tokens by count; a name shared by every correlated input
/// joins and consumes exactly its own tokens. Pins the cross-language firing
/// contract the TypeScript port was diverging from (nu-2).
fn nu_join_skips_unshared_name_but_joins_shared<R: BackendRunner>() {
    let a = Place::<NuMsg>::new("branchA");
    let b = Place::<NuMsg>::new("branchB");
    let merged = Place::<String>::new("merged");

    let join = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .match_spec(
            MatchSpec::builder()
                .key(&a, |m: &NuMsg| NameId::new(m.cid.clone()))
                .key(&b, |m: &NuMsg| NameId::new(m.cid.clone()))
                .build(),
        )
        .output(out_place(&merged))
        .action(sync_action(|ctx| {
            let ma = ctx.input::<NuMsg>("branchA")?;
            let mb = ctx.input::<NuMsg>("branchB")?;
            ctx.output("merged", format!("{}+{}", ma.cid, mb.cid))?;
            Ok(())
        }))
        .build();

    let net = PetriNet::builder("nu_join_unshared").transition(join).build();

    let mut marking = Marking::new();
    // Both inputs hold two tokens, but only "good" is present on both sides.
    marking.add(&a, Token::at(NuMsg { cid: "onlyA".into() }, 0));
    marking.add(&a, Token::at(NuMsg { cid: "good".into() }, 1));
    marking.add(&b, Token::at(NuMsg { cid: "onlyB".into() }, 0));
    marking.add(&b, Token::at(NuMsg { cid: "good".into() }, 1));

    let result = R::run(&net, marking);
    assert!(result.quiescent);
    // Only the shared "good" pair joins; the unshared names can never correlate.
    assert_eq!(
        result.marking.count("merged"),
        1,
        "only the shared name should join"
    );
    let merged_val = result
        .marking
        .queue("merged")
        .and_then(|q| q.iter().next().map(|t| t.downcast::<String>().unwrap().value().clone()))
        .unwrap_or_default();
    assert_eq!(merged_val, "good+good");
    // The unshared tokens are left untouched in both inputs.
    assert_eq!(result.marking.count("branchA"), 1);
    assert_eq!(result.marking.count("branchB"), 1);
}

/// NU-010 + NU-020 end to end: a fork mints a fresh correlation id per firing
/// (`ctx.fresh_name()`) and stamps both siblings; a downstream join re-merges
/// exactly the siblings that share an id. Three requests in → three correctly
/// correlated merges out, each with a distinct id.
fn nu_fork_mints_unique_ids_then_join_merges<R: BackendRunner>() {
    let source = Place::<()>::new("source");
    let a = Place::<NuMsg>::new("branchA");
    let b = Place::<NuMsg>::new("branchB");
    let merged = Place::<String>::new("merged");

    let fork = Transition::builder("fork")
        .input(one(&source))
        .output(and(vec![out_place(&a), out_place(&b)]))
        .action(sync_action(|ctx| {
            let id = ctx.fresh_name();
            ctx.output("branchA", NuMsg { cid: id.as_str().to_string() })?;
            ctx.output("branchB", NuMsg { cid: id.as_str().to_string() })?;
            Ok(())
        }))
        .build();

    let join = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .match_spec(
            MatchSpec::builder()
                .key(&a, |m: &NuMsg| NameId::new(m.cid.clone()))
                .key(&b, |m: &NuMsg| NameId::new(m.cid.clone()))
                .build(),
        )
        .output(out_place(&merged))
        .action(sync_action(|ctx| {
            let ma = ctx.input::<NuMsg>("branchA")?;
            let mb = ctx.input::<NuMsg>("branchB")?;
            if ma.cid != mb.cid {
                return Err(ActionError::new(format!(
                    "join saw mismatched ids: {} vs {}",
                    ma.cid, mb.cid
                )));
            }
            ctx.output("merged", ma.cid.clone())?;
            Ok(())
        }))
        .build();

    let net = PetriNet::builder("nu_scatter_gather")
        .transitions([fork, join])
        .build();

    let mut marking = Marking::new();
    for i in 0..3u64 {
        marking.add(&source, Token::at((), i));
    }

    let result = R::run(&net, marking);
    assert!(result.quiescent);

    let merged_vals: Vec<String> = result
        .marking
        .queue("merged")
        .map(|q| {
            q.iter()
                .map(|t| t.downcast::<String>().unwrap().value().clone())
                .collect()
        })
        .unwrap_or_default();
    assert_eq!(merged_vals.len(), 3, "all three forked requests should merge");
    let distinct: std::collections::HashSet<&String> = merged_vals.iter().collect();
    assert_eq!(
        distinct.len(),
        3,
        "fresh_name must mint a unique id per fork firing, got {merged_vals:?}"
    );
}

/// NU-040: a bounded `Budget` place caps how many fork groups can be live at
/// once (the decidability lever), while the budget token returned by each join
/// lets all work still complete — serialized at `k = 1`.
fn nu_budget_bounds_concurrency<R: BackendRunner>() {
    let source = Place::<()>::new("source");
    let budget = Place::<()>::new("budget");
    let a = Place::<NuMsg>::new("branchA");
    let b = Place::<NuMsg>::new("branchB");
    let merged = Place::<String>::new("merged");

    let fork = Transition::builder("fork")
        .input(one(&source))
        .input(one(&budget)) // minting a name costs one budget token
        .output(and(vec![out_place(&a), out_place(&b)]))
        .action(sync_action(|ctx| {
            let id = ctx.fresh_name();
            ctx.output("branchA", NuMsg { cid: id.as_str().to_string() })?;
            ctx.output("branchB", NuMsg { cid: id.as_str().to_string() })?;
            Ok(())
        }))
        .build();

    let join = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .match_spec(
            MatchSpec::builder()
                .key(&a, |m: &NuMsg| NameId::new(m.cid.clone()))
                .key(&b, |m: &NuMsg| NameId::new(m.cid.clone()))
                .build(),
        )
        .output(and(vec![out_place(&merged), out_place(&budget)])) // return the budget
        .action(sync_action(|ctx| {
            let ma = ctx.input::<NuMsg>("branchA")?;
            let mb = ctx.input::<NuMsg>("branchB")?;
            if ma.cid != mb.cid {
                return Err(ActionError::new("join saw mismatched ids"));
            }
            ctx.output("merged", ma.cid.clone())?;
            ctx.output("budget", ())?;
            Ok(())
        }))
        .build();

    let net = PetriNet::builder("nu_budget")
        .transitions([fork, join])
        .build();

    let mut marking = Marking::new();
    for i in 0..3u64 {
        marking.add(&source, Token::at((), i));
    }
    marking.add(&budget, Token::at((), 0)); // k = 1: at most one live group

    let result = R::run(&net, marking);
    assert!(result.quiescent);

    let count = |p: &str| result.marking.queue(p).map(|q| q.len()).unwrap_or(0);
    assert_eq!(count("merged"), 3, "all three requests complete despite k=1 budget");
    assert_eq!(count("budget"), 1, "the budget token is returned");
    assert_eq!(count("source"), 0);
}

// ========================= Backend divergence regressions =========================

/// Read and reset arcs on the SAME place: the read must observe the pre-reset
/// front token (EXEC-012/EXEC-013). The precompiled backend used to drain the
/// reset before peeking reads, so `ctx.read()` failed where the bitmap
/// reference delivered the token.
fn read_and_reset_same_place<R: BackendRunner>() {
    let p_in = Place::<()>::new("in");
    let p_both = Place::<i32>::new("both");
    let p_out = Place::<i32>::new("out");

    let t = Transition::builder("t1")
        .input(one(&p_in))
        .read(read(&p_both))
        .reset(reset(&p_both))
        .output(out_place(&p_out))
        .action(sync_action(|ctx| {
            let r = ctx.read::<i32>("both")?;
            ctx.output("out", *r)?;
            Ok(())
        }))
        .build();
    let net = PetriNet::builder("test").transition(t).build();

    let mut marking = Marking::new();
    marking.add(&p_in, Token::at((), 0));
    marking.add(&p_both, Token::at(7, 0));
    marking.add(&p_both, Token::at(8, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("both"), 0); // reset drained
    assert_eq!(result.marking.count("out"), 1);
    assert_eq!(*result.marking.peek(&p_out).unwrap(), 7); // read saw the pre-reset front
}

/// Two input arcs on one place have no coherent consumption semantics (the
/// bitmap reference tolerantly under-consumed, the precompiled backend
/// panicked in `ring_remove_first`) and are rejected at compile time
/// (CORE-030).
fn duplicate_input_place_rejected_at_compile<R: BackendRunner>() {
    let p = Place::<i32>::new("p");
    let t = Transition::builder("t1")
        .input(one(&p))
        .input(one(&p))
        .action(passthrough())
        .build();
    let net = PetriNet::builder("test").transition(t).build();
    let mut marking = Marking::new();
    marking.add(&p, Token::at(1, 0));

    let outcome =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| R::run(&net, marking)));
    let Err(err) = outcome else {
        panic!("duplicate input places must be rejected at compile time");
    };
    let message = err
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| err.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_default();
    assert!(
        message.contains("two input arcs"),
        "expected the duplicate-input-place rejection message, got: {message}"
    );
}

/// A place named in the initial marking but never declared to the net: both
/// backends must retain its tokens. The precompiled backend used to drop them
/// (its ring pool only stores compiled places) while the bitmap reference kept
/// its whole `Marking` — a literal lost token.
fn unknown_place_initial_tokens_retained<R: BackendRunner>() {
    let (net, p1, _, _) = simple_chain();
    let ghost = Place::<i32>::new("ghost");
    let mut marking = Marking::new();
    marking.add(&p1, Token::at(1, 0));
    marking.add(&ghost, Token::at(99, 0));

    let result = R::run(&net, marking);
    assert_eq!(result.marking.count("p1"), 0);
    assert_eq!(result.marking.count("ghost"), 1);
    assert_eq!(*result.marking.peek(&ghost).unwrap(), 99);
}

/// CORE-072 AC4: an undeclared place is flagged once per executor, not once
/// per token, and rides the existing log-message event (no new event type).
/// Retention (AC3) is independent — it holds under the no-op store too.
fn unknown_place_warns_once_per_place<R: BackendRunner>() {
    let (net, p1, _, _) = simple_chain();
    let ghost = Place::<i32>::new("ghost");
    let mut marking = Marking::new();
    marking.add(&p1, Token::at(1, 0));
    marking.add(&ghost, Token::at(7, 0));
    marking.add(&ghost, Token::at(8, 0));
    marking.add(&ghost, Token::at(9, 0));

    let result = R::run(&net, marking);
    let warnings: Vec<&NetEvent> = result
        .events
        .iter()
        .filter(|e| matches!(e, NetEvent::LogMessage { .. }))
        .collect();
    assert_eq!(warnings.len(), 1, "one diagnostic per place, not per token");
    let NetEvent::LogMessage { transition_name, level, message, .. } = warnings[0] else {
        unreachable!()
    };
    assert!(transition_name.is_empty(), "no transition fires at the initial-marking seam");
    assert_eq!(level, "WARN");
    assert!(message.contains("unknown place 'ghost'"), "unexpected message: {message}");
    assert_eq!(result.marking.count("ghost"), 3);
}

/// Divergence #5 — same-pass refill (the four from "align precompiled
/// executor with the bitmap reference" being #1–4): tokens a firing's sync
/// action deposits must be INVISIBLE to the EXEC-003 recheck of later
/// entries in the same fire pass. EXEC-001 orders the loop so outputs are
/// deposited in step 1 (process completions) while firing is step 5, and
/// EXEC-003 disables a loser when consumption leaves its inputs
/// unsatisfied — a same-pass refill is not a satisfaction. The bitmap
/// reference rechecks against `firing_snap_buffer` (refreshed
/// post-consumption, PRE-deposit); the precompiled backend used to recheck
/// the live `marking_bitmap`/`token_counts` and let the loser fire mid-pass.
///
/// Witness (the differential harness's shrunken seed, hand-reduced): t_high
/// outranks t_low, both consume from `a`; every t_high firing drains `b` by
/// reset and refills it via its own output, and t_low reads `b`. On the
/// reference t_low's recheck sees `b` empty in the snapshot every pass, so
/// t_low starves: firing order [t_high, t_high, t_high]. The pre-fix
/// precompiled backend fired [t_high, t_low, t_high].
fn same_pass_refill_invisible_to_recheck<R: BackendRunner>() {
    let a = Place::<i32>::new("a");
    let b = Place::<i32>::new("b");

    let t_low = Transition::builder("t_low")
        .input(one(&a))
        .read(read(&b))
        .action(passthrough())
        .build();
    let t_high = Transition::builder("t_high")
        .input(one(&a))
        .reset(reset(&b))
        .output(out_place(&b))
        .priority(1)
        .action(sync_action(|ctx| {
            let vals = ctx.inputs::<i32>("a")?;
            let v = vals.first().map(|t| **t).unwrap_or(0);
            ctx.output("b", v)?;
            Ok(())
        }))
        .build();

    let net = PetriNet::builder("same_pass_refill")
        .transitions([t_low, t_high])
        .build();

    let mut marking = Marking::new();
    for v in [1, 2, 3] {
        marking.add(&a, Token::at(v, 0));
    }
    marking.add(&b, Token::at(10, 0));

    let result = R::run(&net, marking);

    let firing_order: Vec<&str> = result
        .events
        .iter()
        .filter_map(|e| match e {
            NetEvent::TransitionStarted { transition_name, .. } => {
                Some(&**transition_name)
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        firing_order,
        ["t_high", "t_high", "t_high"],
        "t_low must be starved: its recheck sees the pre-deposit snapshot"
    );
    assert_eq!(result.marking.count("a"), 0);
    assert_eq!(result.marking.count("b"), 1);
    assert_eq!(*result.marking.peek(&b).unwrap(), 3); // the last refill survives
}

/// Deterministic differential tests for the general (timed / multi-priority)
/// ready path, driving the backends directly with synthetic timestamps —
/// `collect_ready_general` was never reachable from the wall-clock-free suite
/// above, which is exactly where the tid-order-vs-enablement-order divergence
/// (EXEC-002 AC3/AC4 / CONC-023 AC4) hid.
mod scheduling_order {
    use super::*;
    use crate::bitmap_backend::BitmapBackend;
    use crate::executor_core::backend::{ExecutorBackend, NoopChangeTracker};
    use crate::precompiled_backend::PrecompiledBackend;
    use libpetri_core::timing::delayed;
    use libpetri_core::token::ErasedToken;

    /// Three delayed transitions: t_late (tid 0) and t_early (tid 1) at the
    /// default priority, t_hi (tid 2) at a higher one. Tokens for t_early and
    /// t_hi's trigger are staggered so enablement times differ per cycle.
    fn staggered_net() -> (PetriNet, Marking) {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let c = Place::<i32>::new("c");

        let t_late = Transition::builder("t_late") // tid 0, enabled second
            .input(one(&a))
            .timing(delayed(10))
            .action(passthrough())
            .build();
        let t_early = Transition::builder("t_early") // tid 1, enabled first
            .input(one(&b))
            .timing(delayed(10))
            .action(passthrough())
            .build();
        let t_hi = Transition::builder("t_hi") // tid 2, higher priority
            .input(one(&c))
            .timing(delayed(10))
            .priority(5)
            .action(passthrough())
            .build();

        let net = PetriNet::builder("staggered")
            .transitions([t_late, t_early, t_hi])
            .build();

        let mut marking = Marking::new();
        marking.add(&b, Token::at(1, 0)); // t_early enabled from t=0
        (net, marking)
    }

    /// Drives one backend: t_early enabled at t=0, then tokens for t_late and
    /// t_hi arrive so both enable at t=5, then all three are ready at t=20.
    fn staggered_ready_order<B: ExecutorBackend>(mut backend: B) -> Vec<usize> {
        let mut tracker = NoopChangeTracker;
        backend.initialize();
        backend.update_enablement(0.0, &mut tracker);

        let a: Arc<str> = Arc::from("a");
        let c: Arc<str> = Arc::from("c");
        backend.produce_token(&a, ErasedToken::from_typed(&Token::at(1i32, 0)));
        backend.produce_token(&c, ErasedToken::from_typed(&Token::at(1i32, 0)));
        backend.update_enablement(5.0, &mut tracker);

        let mut out = Vec::new();
        backend.collect_ready_general(20.0, &mut out);
        out
    }

    /// Priority DESC first (t_hi), then within the shared level enablement
    /// time ASC (t_early before t_late) even though t_late has the smaller
    /// tid. The precompiled backend used to order the shared level by tid.
    #[test]
    fn ready_order_is_priority_then_enablement_time_on_both_backends() {
        let (net, marking) = staggered_net();

        let bitmap_order = staggered_ready_order(BitmapBackend::new(&net, marking.clone()));
        let prog = PrecompiledNet::from_compiled(CompiledNet::compile(&net));
        let precompiled_order = staggered_ready_order(PrecompiledBackend::new(&prog, marking));

        assert_eq!(bitmap_order, vec![2, 1, 0]);
        assert_eq!(precompiled_order, bitmap_order);
    }

    /// Transitions enabled in the SAME cycle share an enablement timestamp, so
    /// the tie-break is ascending tid — on both backends, unchanged from the
    /// pre-fix behavior for this case.
    #[test]
    fn same_cycle_enablement_ties_break_by_tid_on_both_backends() {
        let (net, _) = staggered_net();
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let mut marking = Marking::new();
        marking.add(&a, Token::at(1, 0));
        marking.add(&b, Token::at(1, 0));

        fn order<B: ExecutorBackend>(mut backend: B) -> Vec<usize> {
            let mut tracker = NoopChangeTracker;
            backend.initialize();
            backend.update_enablement(0.0, &mut tracker);
            let mut out = Vec::new();
            backend.collect_ready_general(20.0, &mut out);
            out
        }

        let bitmap_order = order(BitmapBackend::new(&net, marking.clone()));
        let prog = PrecompiledNet::from_compiled(CompiledNet::compile(&net));
        let precompiled_order = order(PrecompiledBackend::new(&prog, marking));

        assert_eq!(bitmap_order, vec![0, 1]);
        assert_eq!(precompiled_order, bitmap_order);
    }

}

/// Writes into a place the compiled program does not know (CORE-072 AC3),
/// driven straight against the backends: `TransitionContext` rejects an
/// output place the transition never declared, so `produce_token` and
/// `inject_external_token` are the only reachable seams.
mod unknown_places {
    use super::*;
    use crate::bitmap_backend::BitmapBackend;
    use crate::executor_core::backend::ExecutorBackend;
    use crate::precompiled_backend::PrecompiledBackend;
    use libpetri_core::token::ErasedToken;

    fn ghost_token(value: i32) -> ErasedToken {
        ErasedToken::from_typed(&Token::at(value, 0))
    }

    /// Retained-token count, then the flagged names after two writes and
    /// after a third — the second drain must be empty (AC4: once per place).
    fn produce_unknown(mut backend: impl ExecutorBackend) -> (usize, Vec<Arc<str>>, Vec<Arc<str>>) {
        let ghost: Arc<str> = Arc::from("ghost");
        backend.initialize();
        backend.produce_token(&ghost, ghost_token(1));
        backend.produce_token(&ghost, ghost_token(2));
        let first = backend.take_unknown_places();
        backend.produce_token(&ghost, ghost_token(3));
        let second = backend.take_unknown_places();
        (backend.snapshot_marking().count(&ghost), first, second)
    }

    /// Production into an unknown place must retain the token on both
    /// backends — the seam the precompiled ring pool cannot store.
    #[test]
    fn produce_unknown_place_retained_on_both_backends() {
        let (net, _, _, _) = simple_chain();
        let prog = PrecompiledNet::from_compiled(CompiledNet::compile(&net));

        let (bitmap_count, bitmap_first, bitmap_second) =
            produce_unknown(BitmapBackend::new(&net, Marking::new()));
        let (precompiled_count, precompiled_first, precompiled_second) =
            produce_unknown(PrecompiledBackend::new(&prog, Marking::new()));

        assert_eq!(bitmap_count, 3);
        assert_eq!(precompiled_count, bitmap_count);
        assert_eq!(bitmap_first.len(), 1);
        assert_eq!(&*bitmap_first[0], "ghost");
        assert!(bitmap_second.is_empty(), "a later write must not re-flag the place");
        assert_eq!(precompiled_first, bitmap_first);
        assert_eq!(precompiled_second, bitmap_second);
    }

    /// Injection into a place the compiled program does not know must retain
    /// the token in the observable marking on both backends (the precompiled
    /// backend used to drop it silently).
    #[test]
    fn inject_unknown_place_retained_on_both_backends() {
        let (net, _, _, _) = simple_chain();
        let ghost: Arc<str> = Arc::from("ghost");

        fn inject_and_count(mut backend: impl ExecutorBackend, place: &Arc<str>) -> usize {
            backend.initialize();
            backend.inject_external_token(place, ghost_token(9));
            backend.snapshot_marking().count(place)
        }

        let bitmap_count = inject_and_count(BitmapBackend::new(&net, Marking::new()), &ghost);
        let prog = PrecompiledNet::from_compiled(CompiledNet::compile(&net));
        let precompiled_count =
            inject_and_count(PrecompiledBackend::new(&prog, Marking::new()), &ghost);

        assert_eq!(bitmap_count, 1);
        assert_eq!(precompiled_count, 1);
    }
}

/// Generates one `#[test]` per backend for each generic test fn above,
/// so every semantic runs against both `BitmapNetExecutor` and
/// `PrecompiledNetExecutor`.
macro_rules! for_each_backend {
    ($($test:ident),+ $(,)?) => {
        mod bitmap {
            use super::*;
            $( #[test] fn $test() { super::$test::<BitmapRunner>(); } )+
        }
        mod precompiled {
            use super::*;
            $( #[test] fn $test() { super::$test::<PrecompiledRunner>(); } )+
        }
    };
}

for_each_backend!(
    sync_passthrough_chain,
    sync_with_event_store,
    sync_fork_chain,
    sync_no_initial_tokens,
    sync_linear_chain_5,
    single_transition_fires_once,
    many_tokens_all_processed,
    input_fifo_ordering,
    transition_with_no_output_consumes_only,
    input_arc_requires_token_to_enable,
    multiple_input_arcs_require_all,
    read_arc_does_not_consume,
    reset_arc_removes_all_tokens,
    combined_input_read_reset,
    sync_inhibitor_blocks,
    inhibitor_unblocked_when_token_removed,
    exactly_cardinality_consumes_n,
    all_cardinality_consumes_everything,
    at_least_blocks_insufficient,
    at_least_fires_with_enough,
    xor_routing_only_forwards_matching,
    xor_routing_blocks_when_nothing_routed,
    self_loop_with_xor_routing_terminates,
    transform_action_outputs_to_all_places,
    sync_action_custom_logic,
    produce_action,
    xor_output_fires_one_branch,
    and_output_fires_to_all,
    xor_output_both_branches_violates,
    xor_output_no_branch_violates,
    and_output_partial_violates,
    single_place_output_missing_violates,
    conforming_output_still_succeeds,
    xor_subsuming_branch_is_accepted,
    action_error_does_not_crash,
    multiple_tokens_different_types,
    sync_priority_ordering,
    priority_higher_fires_first,
    multiple_transitions_same_input_compete,
    diamond_pattern,
    workflow_sequential_chain,
    workflow_fork_join,
    workflow_mutual_exclusion,
    complex_workflow,
    empty_net_completes,
    quiescent_when_no_enabled_transitions,
    event_store_records_lifecycle,
    event_store_transition_enabled_disabled,
    nu_join_matches_by_name_not_fifo,
    nu_bound_join_matches_by_name_not_fifo,
    nu_join_blocks_without_matching_name,
    nu_join_skips_unshared_name_but_joins_shared,
    nu_fork_mints_unique_ids_then_join_merges,
    nu_budget_bounds_concurrency,
    read_and_reset_same_place,
    duplicate_input_place_rejected_at_compile,
    unknown_place_initial_tokens_retained,
    unknown_place_warns_once_per_place,
    same_pass_refill_invisible_to_recheck,
);
