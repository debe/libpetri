//! Tests for [`PetriNetBuilder::compose_auto`] — identity-default auto-
//! composition per **MOD-024**.
//!
//! Rule: every declared port whose underlying [`PlaceRef`] is equal (by
//! name, matching Rust's name-based `PartialEq`/`Hash` on `PlaceRef`) to
//! a host-builder place auto-binds to it. If the subnet declares no
//! interface ports at all, body places are matched against host places
//! directly by name.
//!
//! Mirrors `java/src/test/java/org/libpetri/core/AutoComposeTest.java`
//! and `typescript/tests/core/auto-compose.test.ts`.

use libpetri::core::input::one;
use libpetri::core::output::out_place;
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::subnet_def::SubnetDef;
use libpetri::core::transition::Transition;

// ============================================================
//  Subnet fixtures — duplicated locally because libpetri-core's
//  test fixtures are not visible to integration tests in dependent
//  crates. Mirrors the canonical producer / retry_policy fixtures
//  in rust/libpetri/tests/compose_e2e.rs and channel_composition.rs.
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
//  Tests
// ============================================================

#[test]
fn auto_compose_explicit_interface_matches_by_place_equality() {
    let prod = producer().instantiate_unit("p1");
    let host_output = Place::<String>::new("output");

    let host = PetriNet::builder("Host")
        .place(host_output.as_ref())
        .compose_auto(&prod)
        .build();

    let names: Vec<&str> = host.places().iter().map(|p| p.name()).collect();
    assert!(names.contains(&"output"), "host place must remain. Got: {names:?}");
    assert!(
        !names.contains(&"p1/output"),
        "renamed interface place 'p1/output' must not survive auto-compose. Got: {names:?}"
    );
    assert!(
        names.contains(&"p1/nextItem"),
        "internal place 'p1/nextItem' must survive. Got: {names:?}"
    );

    let produce = host
        .transitions()
        .iter()
        .find(|t| t.name() == "p1/produce")
        .expect("p1/produce must exist");
    let output_place_names: Vec<&str> =
        produce.output_places().iter().map(|p| p.name()).collect();
    assert!(
        output_place_names.contains(&"output"),
        "produce.output must merge to host place 'output'. Got: {output_place_names:?}"
    );
}

#[test]
fn auto_compose_structurally_equal_to_explicit_bind_port() {
    let host_output = Place::<String>::new("output");

    let auto_host = PetriNet::builder("Host")
        .place(host_output.as_ref())
        .compose_auto(&producer().instantiate_unit("p1"))
        .build();

    let explicit_host = PetriNet::builder("Host")
        .place(host_output.as_ref())
        .compose_with(&producer().instantiate_unit("p1"), |b| {
            b.bind_port::<String>("output", &host_output);
        })
        .build();

    let auto_place_names: Vec<&str> = auto_host.places().iter().map(|p| p.name()).collect();
    let explicit_place_names: Vec<&str> =
        explicit_host.places().iter().map(|p| p.name()).collect();
    assert_eq!(
        auto_place_names, explicit_place_names,
        "place names must match in builder insertion order"
    );

    let auto_trans: Vec<&str> =
        auto_host.transitions().iter().map(|t| t.name()).collect();
    let explicit_trans: Vec<&str> =
        explicit_host.transitions().iter().map(|t| t.name()).collect();
    assert_eq!(auto_trans, explicit_trans);

    for name in &auto_trans {
        let a = auto_host
            .transitions()
            .iter()
            .find(|t| &t.name() == name)
            .unwrap();
        let e = explicit_host
            .transitions()
            .iter()
            .find(|t| &t.name() == name)
            .unwrap();
        let a_in: Vec<&str> = a.input_specs().iter().map(|s| s.place().name()).collect();
        let e_in: Vec<&str> = e.input_specs().iter().map(|s| s.place().name()).collect();
        assert_eq!(a_in, e_in, "inputs must match for transition '{name}'");
        let mut a_out: Vec<&str> = a.output_places().iter().map(|p| p.name()).collect();
        let mut e_out: Vec<&str> = e.output_places().iter().map(|p| p.name()).collect();
        a_out.sort_unstable();
        e_out.sort_unstable();
        assert_eq!(a_out, e_out, "outputs must match for transition '{name}'");
    }
}

#[test]
fn auto_compose_host_has_no_pre_declared_place_arrives_via_arcs() {
    let prod = producer().instantiate_unit("p1");

    let host = PetriNet::builder("Host").compose_auto(&prod).build();

    let names: Vec<&str> = host.places().iter().map(|p| p.name()).collect();
    assert!(
        names.contains(&"output"),
        "interface place arrives implicitly via rewritten arcs. Got: {names:?}"
    );
    assert!(
        !names.contains(&"p1/output"),
        "renamed interface place must be merged away. Got: {names:?}"
    );
}

#[test]
fn auto_compose_no_interface_declared_infers_from_body_places() {
    let shared = Place::<String>::new("shared");
    let internal = Place::<String>::new("internal");

    let move_t = Transition::builder("move")
        .input(one(&internal))
        .output(out_place(&shared))
        .build();

    let bare_subnet = SubnetDef::<()>::builder("Bare")
        .place(&internal)
        .place(&shared)
        .transition(move_t)
        .build(); // no input_port/output_port/inout_port declarations
    let inst = bare_subnet.instantiate_unit("b1");

    let host = PetriNet::builder("Host")
        .place(shared.as_ref())
        .compose_auto(&inst)
        .build();

    let names: Vec<&str> = host.places().iter().map(|p| p.name()).collect();
    assert!(names.contains(&"shared"));
    assert!(
        !names.contains(&"b1/shared"),
        "shared place must be merged away. Got: {names:?}"
    );
    assert!(
        names.contains(&"b1/internal"),
        "internal place must survive as private. Got: {names:?}"
    );

    let renamed_move = host
        .transitions()
        .iter()
        .find(|t| t.name() == "b1/move")
        .expect("b1/move must exist");
    let out_names: Vec<&str> =
        renamed_move.output_places().iter().map(|p| p.name()).collect();
    assert!(out_names.contains(&"shared"));
}

#[test]
#[should_panic(expected = "attempt")]
fn auto_compose_subnet_with_channel_panics_naming_the_channel() {
    // AC-4: panic must name the channel ("attempt") so callers can locate the
    // offending interface element, and point at the explicit overload.
    let retry = retry_policy().instantiate_unit("r1");
    let _ = PetriNet::builder("Host").compose_auto(&retry).build();
}

#[test]
#[should_panic(expected = "compose_with")]
fn auto_compose_subnet_with_channel_panics_suggesting_compose_with() {
    let retry = retry_policy().instantiate_unit("r1");
    let _ = PetriNet::builder("Host").compose_auto(&retry).build();
}

#[test]
fn auto_compose_multiple_subnets_end_to_end() {
    let pipe = Place::<String>::new("pipe");

    let producer_def = SubnetDef::<()>::builder("ProdLocal")
        .place(&Place::<String>::new("seed"))
        .place(&pipe)
        .transition(
            Transition::builder("emit")
                .input(one(&Place::<String>::new("seed")))
                .output(out_place(&pipe))
                .build(),
        )
        .output_port("out", &pipe)
        .build();

    let consumer_def = SubnetDef::<()>::builder("ConsLocal")
        .place(&pipe)
        .place(&Place::<String>::new("sink"))
        .transition(
            Transition::builder("eat")
                .input(one(&pipe))
                .output(out_place(&Place::<String>::new("sink")))
                .build(),
        )
        .input_port("in", &pipe)
        .build();

    let host = PetriNet::builder("Host")
        .place(pipe.as_ref())
        .compose_auto(&producer_def.instantiate_unit("p"))
        .compose_auto(&consumer_def.instantiate_unit("c"))
        .build();

    let names: Vec<&str> = host.places().iter().map(|p| p.name()).collect();
    assert!(names.contains(&"pipe"));

    let emit = host
        .transitions()
        .iter()
        .find(|t| t.name() == "p/emit")
        .expect("p/emit must exist");
    let eat = host
        .transitions()
        .iter()
        .find(|t| t.name() == "c/eat")
        .expect("c/eat must exist");
    let emit_out: Vec<&str> = emit.output_places().iter().map(|p| p.name()).collect();
    assert!(emit_out.contains(&"pipe"));
    let eat_in: Vec<&str> = eat.input_specs().iter().map(|s| s.place().name()).collect();
    assert!(eat_in.contains(&"pipe"));
}

#[test]
fn auto_compose_inout_port_also_matches_by_equality() {
    let counter = Place::<i32>::new("counter");

    let subnet = SubnetDef::<()>::builder("Counter")
        .place(&counter)
        .transition(
            Transition::builder("tick")
                .input(one(&counter))
                .output(out_place(&counter))
                .build(),
        )
        .inout_port("counter", &counter)
        .build();

    let host = PetriNet::builder("Host")
        .place(counter.as_ref())
        .compose_auto(&subnet.instantiate_unit("c1"))
        .build();

    let names: Vec<&str> = host.places().iter().map(|p| p.name()).collect();
    assert!(names.contains(&"counter"));
    assert!(!names.contains(&"c1/counter"));
}

#[test]
fn auto_compose_empty_body_is_harmless() {
    let empty = SubnetDef::<()>::builder("Empty").build();
    let host = PetriNet::builder("Host")
        .compose_auto(&empty.instantiate_unit("e1"))
        .build();
    assert_eq!(host.places().len(), 0);
    assert_eq!(host.transitions().len(), 0);
}

#[test]
fn auto_compose_two_instances_per_instance_state_isolation() {
    // MOD-012: two auto-composed instances of the same SubnetDef must
    // keep their internal places under disjoint prefixed names.
    let shared = Place::<String>::new("output");

    let host = PetriNet::builder("Host")
        .place(shared.as_ref())
        .compose_auto(&producer().instantiate_unit("p1"))
        .compose_auto(&producer().instantiate_unit("p2"))
        .build();

    let place_names: Vec<&str> = host.places().iter().map(|p| p.name()).collect();
    assert!(place_names.contains(&"p1/nextItem"));
    assert!(place_names.contains(&"p2/nextItem"));
    assert!(
        !place_names.contains(&"nextItem"),
        "no un-prefixed 'nextItem' should leak. Got: {place_names:?}"
    );

    let trans_names: Vec<&str> =
        host.transitions().iter().map(|t| t.name()).collect();
    assert!(trans_names.contains(&"p1/produce"));
    assert!(trans_names.contains(&"p2/produce"));
}

