//! End-to-end integration tests for direct subnet composition per
//! **MOD-025** — [`PetriNetBuilder::compose_direct`].
//!
//! Rule: a [`SubnetDef`] composed directly is integrated *without*
//! instantiation/prefix-renaming. Body places and transitions keep their
//! original names; places merge into the host by name. Direct composition is
//! order-independent.
//!
//! Mirrors `java/src/test/java/org/libpetri/core/ComposeDirectTest.java` and
//! `typescript/tests/core/compose-direct.test.ts` (the place token-type
//! conflict scenario is Java-only — Rust `PlaceRef` identity is name-only,
//! see MOD-025).

use std::collections::HashSet;

use libpetri::core::arc::inhibitor;
use libpetri::core::input::one;
use libpetri::core::output::out_place;
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::subnet_def::SubnetDef;
use libpetri::core::transition::Transition;
use libpetri::verification::analyzer::TimePetriNetAnalyzer;
use libpetri::verification::marking_state::MarkingStateBuilder;

// ============================================================
//  Subnet fixtures — duplicated locally (libpetri-core test fixtures
//  are not visible to integration tests in dependent crates).
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

fn leaky_bucket(rate: u32) -> SubnetDef<()> {
    assert!(rate >= 1, "rate must be >= 1, got: {rate}");
    let request = Place::<String>::new("request");
    let accept = Place::<String>::new("accept");
    let reject = Place::<String>::new("reject");
    let slots = Place::<String>::new("slots");
    let accept_t = Transition::builder("accept")
        .input(one(&request))
        .input(one(&slots))
        .output(out_place(&accept))
        .build();
    let reject_t = Transition::builder("reject")
        .input(one(&request))
        .inhibitor(inhibitor(&slots))
        .output(out_place(&reject))
        .build();
    SubnetDef::<()>::builder(format!("LeakyBucket-{rate}"))
        .place(&slots)
        .transition(accept_t)
        .transition(reject_t)
        .input_port("request", &request)
        .output_port("accept", &accept)
        .output_port("reject", &reject)
        .build()
}

/// A producer whose output place is named `pipe` (wires by name).
fn pipe_producer() -> SubnetDef<()> {
    let seed = Place::<String>::new("seed");
    let pipe = Place::<String>::new("pipe");
    let emit = Transition::builder("emit")
        .input(one(&seed))
        .output(out_place(&pipe))
        .build();
    SubnetDef::<()>::builder("PipeProducer")
        .place(&seed)
        .place(&pipe)
        .transition(emit)
        .build()
}

/// A consumer whose input place is named `pipe` (wires by name).
fn pipe_consumer() -> SubnetDef<()> {
    let pipe = Place::<String>::new("pipe");
    let sink = Place::<String>::new("sink");
    let eat = Transition::builder("eat")
        .input(one(&pipe))
        .output(out_place(&sink))
        .build();
    SubnetDef::<()>::builder("PipeConsumer")
        .place(&pipe)
        .place(&sink)
        .transition(eat)
        .build()
}

// ============================================================
//  Helpers
// ============================================================

fn place_names(net: &PetriNet) -> Vec<&str> {
    let mut v: Vec<&str> = net.places().iter().map(|p| p.name()).collect();
    v.sort_unstable();
    v
}

fn transition_names(net: &PetriNet) -> Vec<&str> {
    let mut v: Vec<&str> = net.transitions().iter().map(|t| t.name()).collect();
    v.sort_unstable();
    v
}

// ============================================================
//  Tests
// ============================================================

#[test]
fn compose_direct_merges_body_places_by_name() {
    let host_output = Place::<String>::new("output");
    let prod = producer();
    let host = PetriNet::builder("Host")
        .place(host_output.as_ref())
        .compose_direct(&prod)
        .build();

    let names: Vec<&str> = host.places().iter().map(|p| p.name()).collect();
    assert_eq!(names.iter().filter(|n| **n == "output").count(), 1,
        "exactly one 'output' place after the merge. Got: {names:?}");
    assert!(names.contains(&"nextItem"), "internal place arrives un-prefixed");

    let produce = host.transitions().iter().find(|t| t.name() == "produce")
        .expect("produce must exist un-prefixed");
    let outs: Vec<&str> = produce.output_places().iter().map(|p| p.name()).collect();
    assert!(outs.contains(&"output"), "produce output arc references host place");
}

#[test]
fn compose_direct_host_has_no_pre_declared_place_arrives_unprefixed() {
    let prod = producer();
    let host = PetriNet::builder("Host").compose_direct(&prod).build();
    let names = place_names(&host);
    assert!(names.contains(&"output"));
    assert!(names.contains(&"nextItem"));
}

#[test]
fn compose_direct_introduces_no_prefix_separator() {
    let prod = producer();
    let cons = consumer();
    let host = PetriNet::builder("Host")
        .compose_direct(&prod)
        .compose_direct(&cons)
        .build();
    assert!(host.places().iter().all(|p| !p.name().contains('/')));
    assert!(host.transitions().iter().all(|t| !t.name().contains('/')));
}

#[test]
fn compose_direct_is_order_independent() {
    let prod_then_cons = {
        let p = pipe_producer();
        let c = pipe_consumer();
        PetriNet::builder("Host").compose_direct(&p).compose_direct(&c).build()
    };
    let cons_then_prod = {
        let p = pipe_producer();
        let c = pipe_consumer();
        PetriNet::builder("Host").compose_direct(&c).compose_direct(&p).build()
    };

    assert_eq!(place_names(&prod_then_cons), place_names(&cons_then_prod),
        "place sets must be equal regardless of compose order");
    assert_eq!(transition_names(&prod_then_cons), transition_names(&cons_then_prod),
        "transition sets must be equal regardless of compose order");
}

#[test]
fn compose_direct_structurally_equal_to_hand_written_flat_net() {
    let composed = {
        let p = pipe_producer();
        let c = pipe_consumer();
        PetriNet::builder("Net").compose_direct(&p).compose_direct(&c).build()
    };

    let seed = Place::<String>::new("seed");
    let pipe = Place::<String>::new("pipe");
    let sink = Place::<String>::new("sink");
    let hand_written = PetriNet::builder("Net")
        .transition(Transition::builder("emit").input(one(&seed)).output(out_place(&pipe)).build())
        .transition(Transition::builder("eat").input(one(&pipe)).output(out_place(&sink)).build())
        .build();

    assert_eq!(place_names(&composed), place_names(&hand_written));
    assert_eq!(transition_names(&composed), transition_names(&hand_written));
}

#[test]
fn compose_direct_mixed_with_instance_compose_coexist() {
    let prod = producer();
    let cons_instance = consumer().instantiate_unit("c1");
    let host = PetriNet::builder("Host")
        .compose_direct(&prod)
        .compose_auto(&cons_instance)
        .build();

    let names: HashSet<&str> = host.transitions().iter().map(|t| t.name()).collect();
    assert!(names.contains("produce"), "direct transition stays un-prefixed");
    assert!(names.contains("c1/consume"), "instance transition keeps its prefix");
}

#[test]
#[should_panic(expected = "collides with")]
fn compose_direct_transition_name_collision_panics() {
    let first = producer();
    let second = producer();
    let _ = PetriNet::builder("Host")
        .compose_direct(&first)
        .compose_direct(&second);
}

#[test]
#[should_panic(expected = "declares channels")]
fn compose_direct_subnet_with_channel_panics() {
    let retry = retry_policy();
    let _ = PetriNet::builder("Host").compose_direct(&retry);
}

#[test]
fn compose_direct_empty_subnet_is_noop() {
    let empty = SubnetDef::<()>::builder("Empty").build();
    let host = PetriNet::builder("Host").compose_direct(&empty).build();
    assert!(host.places().is_empty());
    assert!(host.transitions().is_empty());
}

#[test]
fn compose_direct_arcless_standalone_place_flows_through() {
    let standalone = Place::<String>::new("standalone");
    let subnet = SubnetDef::<()>::builder("Standalone").place(&standalone).build();
    let host = PetriNet::builder("Host").compose_direct(&subnet).build();
    assert!(place_names(&host).contains(&"standalone"),
        "an arc-less standalone body place must survive direct composition");
}

#[test]
fn compose_direct_inhibitor_arc_place_merges_by_name() {
    let host_slots = Place::<String>::new("slots");
    let bucket = leaky_bucket(2);
    let host = PetriNet::builder("Host")
        .place(host_slots.as_ref())
        .compose_direct(&bucket)
        .build();

    let reject = host.transitions().iter().find(|t| t.name() == "reject")
        .expect("reject transition must exist");
    assert!(reject.inhibitors().iter().any(|inh| inh.place.name() == "slots"),
        "the inhibitor arc place must merge with the host 'slots' place");
    assert_eq!(place_names(&host).iter().filter(|n| **n == "slots").count(), 1);
}

#[test]
fn compose_direct_then_fuse_fusion_runs_at_build() {
    let a = Place::<String>::new("a");
    let b = Place::<String>::new("b");
    let subnet = SubnetDef::<()>::builder("AB")
        .transition(Transition::builder("move").input(one(&a)).output(out_place(&b)).build())
        .build();

    let net = PetriNet::builder("Host")
        .compose_direct(&subnet)
        .fuse_with(|fb| {
            fb.member(&a).member(&b);
        })
        .build();

    let names = place_names(&net);
    assert!(names.contains(&"a"), "canonical fused place 'a' survives");
    assert!(!names.contains(&"b"), "non-canonical fused place 'b' is substituted away");
}

#[test]
fn compose_direct_producer_to_consumer_is_bounded_and_reachable() {
    // SCG-1: a direct-composed producer→pipe←consumer chain is bounded and
    // the sink is reachable — proves the name-merge wired the two subnets.
    let net = {
        let p = pipe_producer();
        let c = pipe_consumer();
        PetriNet::builder("DirectComposed").compose_direct(&p).compose_direct(&c).build()
    };

    let result = analyze_pipe_chain(&net);
    assert!(result.is_complete, "direct-composed net must be bounded");
    assert!(result.is_goal_live, "the sink token must become reachable");
}

#[test]
fn compose_direct_order_independent_under_state_class_analysis() {
    // SCG-2: formal backing for order-independence — both compose orders
    // produce nets with identical reachability and state-class structure.
    let prod_then_cons = {
        let p = pipe_producer();
        let c = pipe_consumer();
        PetriNet::builder("A").compose_direct(&p).compose_direct(&c).build()
    };
    let cons_then_prod = {
        let p = pipe_producer();
        let c = pipe_consumer();
        PetriNet::builder("B").compose_direct(&c).compose_direct(&p).build()
    };

    let a = analyze_pipe_chain(&prod_then_cons);
    let b = analyze_pipe_chain(&cons_then_prod);

    assert_eq!(a.is_goal_live, b.is_goal_live, "reachability must not depend on order");
    assert_eq!(a.is_complete, b.is_complete, "boundedness must not depend on order");
    assert_eq!(
        a.state_class_graph.class_count(),
        b.state_class_graph.class_count(),
        "state-class count must not depend on compose order",
    );
}

fn analyze_pipe_chain(net: &PetriNet) -> libpetri::verification::analyzer::LivenessResult {
    TimePetriNetAnalyzer::for_net(net)
        .initial_marking(MarkingStateBuilder::new().tokens("seed", 1).build())
        .goal_place("sink")
        .max_classes(100)
        .build()
        .analyze()
}
