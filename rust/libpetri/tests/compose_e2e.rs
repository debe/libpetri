//! End-to-end integration tests for `PetriNetBuilder::compose`/
//! `compose_with` that drive the bitmap executor across a composed
//! producer -> buffer -> consumer pipeline. Mirrors
//! `typescript/tests/core/compose.test.ts` and the analogous Java suite.
//!
//! Lives in the umbrella `libpetri` crate because `libpetri-core` does not
//! (and cannot) depend on `libpetri-runtime` — the runtime crate already
//! depends on core.

use std::sync::Arc;

use libpetri::core::action::{ActionError, BoxedAction, fork, sync_action};
use libpetri::core::context::TransitionContext;
use libpetri::core::input::one;
use libpetri::core::output::{and_places, out_place};
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::subnet_def::SubnetDef;
use libpetri::core::token::Token;
use libpetri::core::transition::Transition;
use libpetri::event::event_store::NoopEventStore;
use libpetri::runtime::executor::{BitmapNetExecutor, ExecutorOptions};
use libpetri::runtime::marking::Marking;

// ============================================================
//  Subnet fixtures (mirror typescript/tests/fixtures/subnet-fixtures.ts).
//  Duplicated locally because libpetri-core's test module is not visible
//  to integration tests in dependent crates.
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

// ============================================================
//  Action helpers — fixtures are action-less by default; tests bind
//  per-instance behaviour via `Instance::bind_actions`.
// ============================================================

/// `enqueue` consumes `(put, slots)` and emits a single `put`-valued token to
/// `items`. Used by both producer-buffer-consumer pipeline tests.
fn enqueue_action() -> BoxedAction {
    sync_action(
        |ctx: &mut TransitionContext| -> Result<(), ActionError> {
            let put_name = ctx
                .input_place_names()
                .into_iter()
                .find(|n| n.ends_with("/put") || n.as_ref() == "producerToBuffer")
                .ok_or_else(|| ActionError::new("enqueue: missing put input"))?;
            let value = ctx.input_raw(&put_name)?;
            let items_name = ctx
                .output_place_names()
                .into_iter()
                .next()
                .ok_or_else(|| ActionError::new("enqueue: missing items output"))?;
            ctx.output_raw(&items_name, value)?;
            Ok(())
        },
    )
}

fn install_pipeline_actions(
    prod: libpetri::core::instance::Instance<()>,
    buf: libpetri::core::instance::Instance<()>,
    cons: libpetri::core::instance::Instance<()>,
) -> (
    libpetri::core::instance::Instance<()>,
    libpetri::core::instance::Instance<()>,
    libpetri::core::instance::Instance<()>,
) {
    use std::collections::HashMap;
    let mut prod_actions: HashMap<Arc<str>, BoxedAction> = HashMap::new();
    prod_actions.insert(Arc::<str>::from("produce"), fork());
    let prod = prod.bind_actions(prod_actions);

    let mut buf_actions: HashMap<Arc<str>, BoxedAction> = HashMap::new();
    buf_actions.insert(Arc::<str>::from("enqueue"), enqueue_action());
    // dequeue: single input -> AND(get, slots), so fork() works.
    buf_actions.insert(Arc::<str>::from("dequeue"), fork());
    let buf = buf.bind_actions(buf_actions);

    let mut cons_actions: HashMap<Arc<str>, BoxedAction> = HashMap::new();
    cons_actions.insert(Arc::<str>::from("consume"), fork());
    let cons = cons.bind_actions(cons_actions);

    (prod, buf, cons)
}

// ============================================================
//  Tests
// ============================================================

#[test]
fn compose_producer_buffer_consumer_end_to_end() {
    let prod_def = producer();
    let buf_def = bounded_buffer(2);
    let cons_def = consumer();

    let prod = prod_def.instantiate("prod", ());
    let buf = buf_def.instantiate("buf", ());
    let cons = cons_def.instantiate("cons", ());
    let (prod, buf, cons) = install_pipeline_actions(prod, buf, cons);

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

    // Initial marking: seed producer's nextItem with one token, buffer's
    // slots with capacity tokens.
    let mut marking = Marking::new();
    let prod_next_item = Place::<String>::new("prod/nextItem");
    let buf_slots = Place::<String>::new("buf/slots");
    marking.add(&prod_next_item, Token::at("payload".to_string(), 0));
    marking.add(&buf_slots, Token::at("slot1".to_string(), 0));
    marking.add(&buf_slots, Token::at("slot2".to_string(), 0));

    let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
        &net,
        marking,
        ExecutorOptions::default(),
    );
    let final_marking = executor.run_sync();

    // The single producer token has flowed all the way to consumer's sink.
    assert_eq!(
        final_marking.count("cons/consumed"),
        1,
        "consumer's sink must hold exactly one token"
    );
    // Producer's nextItem has been drained.
    assert_eq!(
        final_marking.count("prod/nextItem"),
        0,
        "producer's nextItem must be drained"
    );
}

#[test]
fn compose_two_producer_instances_per_instance_state() {
    let prod_def = producer();
    let buf_def = bounded_buffer(2);
    let cons_def = consumer();

    let p1 = prod_def.instantiate("p1", ());
    let p2 = prod_def.instantiate("p2", ());
    let buf = buf_def.instantiate("buf", ());
    let cons = cons_def.instantiate("cons", ());

    use std::collections::HashMap;
    let mut p1_actions: HashMap<Arc<str>, BoxedAction> = HashMap::new();
    p1_actions.insert(Arc::<str>::from("produce"), fork());
    let p1 = p1.bind_actions(p1_actions);

    let mut p2_actions: HashMap<Arc<str>, BoxedAction> = HashMap::new();
    p2_actions.insert(Arc::<str>::from("produce"), fork());
    let p2 = p2.bind_actions(p2_actions);

    let mut buf_actions: HashMap<Arc<str>, BoxedAction> = HashMap::new();
    buf_actions.insert(Arc::<str>::from("enqueue"), enqueue_action());
    buf_actions.insert(Arc::<str>::from("dequeue"), fork());
    let buf = buf.bind_actions(buf_actions);

    let mut cons_actions: HashMap<Arc<str>, BoxedAction> = HashMap::new();
    cons_actions.insert(Arc::<str>::from("consume"), fork());
    let cons = cons.bind_actions(cons_actions);

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

    let mut marking = Marking::new();
    let p1_next_item = Place::<String>::new("p1/nextItem");
    let p2_next_item = Place::<String>::new("p2/nextItem");
    let buf_slots = Place::<String>::new("buf/slots");
    marking.add(&p1_next_item, Token::at("one".to_string(), 0));
    marking.add(&p2_next_item, Token::at("two".to_string(), 0));
    marking.add(&buf_slots, Token::at("slot1".to_string(), 0));
    marking.add(&buf_slots, Token::at("slot2".to_string(), 0));

    let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
        &net,
        marking,
        ExecutorOptions::default(),
    );
    let final_marking = executor.run_sync();

    // Both tokens reached the consumer.
    assert_eq!(
        final_marking.count("cons/consumed"),
        2,
        "consumer must accumulate both producer tokens"
    );
    // Both producers have drained.
    assert_eq!(
        final_marking.count("p1/nextItem"),
        0,
        "p1's nextItem must be drained"
    );
    assert_eq!(
        final_marking.count("p2/nextItem"),
        0,
        "p2's nextItem must be drained"
    );
}
