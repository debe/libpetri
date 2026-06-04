//! Conformance test for **MOD-031** (Action Place Resolution under Composition),
//! per `spec/11-modular-composition.md`.
//!
//! Rust already realises MOD-031's per-transition declared→actual correspondence
//! as [`Transition::local_name_map`] (author-local place name → composed name),
//! built by the rewriter through instantiation ([MOD-010]), port binding
//! ([MOD-020]), and nested instantiation ([MOD-013]). The executor wires it into
//! the `TransitionContext` at firing time and the binding adapters (e.g.
//! `libpetri-py`) apply it so an action that references a *declared* place name
//! resolves to the *actual* composed place.
//!
//! These tests pin that the correspondence is built correctly at compose time
//! (the MOD-031 mechanism); end-to-end action firing *through* the resolution is
//! covered natively by the binding layer and by the Python pytest in
//! `rust/libpetri-py/python/tests/`.

use libpetri_core::input::one;
use libpetri_core::interface::Interface;
use libpetri_core::output::out_place;
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::subnet_def::SubnetDef;
use libpetri_core::transition::Transition;

/// Finds a transition by name in a net.
fn find_t<'n>(net: &'n PetriNet, name: &str) -> &'n Transition {
    net.transitions()
        .iter()
        .find(|t| t.name() == name)
        .unwrap_or_else(|| panic!("no transition '{name}' in net"))
}

/// The composed name a declared place resolves to via the transition's MOD-031
/// correspondence (`None` when there is no entry — identity).
fn alias_of(t: &Transition, declared: &str) -> Option<String> {
    t.local_name_map()
        .and_then(|m| m.get(declared))
        .map(|s| s.as_ref().to_string())
}

/// AC#1 + AC#5: instantiate + port-bind populates declared→host; discovery still
/// returns the actual composed places.
#[test]
fn instantiate_then_compose_resolves_declared_to_host() {
    let req = Place::<String>::new("reqDecl");
    let resp = Place::<String>::new("respDecl");
    let step = Transition::builder("call")
        .input(one(&req))
        .output(out_place(&resp))
        .build();
    let def = SubnetDef::<()>::builder("Step")
        .place(&req)
        .place(&resp)
        .transition(step)
        .input_port("in", &req)
        .output_port("out", &resp)
        .build();

    let host_req = Place::<String>::new("REQ");
    let host_resp = Place::<String>::new("RESP");
    let inst = def.instantiate_unit("probe");
    let net = PetriNet::builder("h")
        .place(host_req.as_ref())
        .place(host_resp.as_ref())
        .compose_with(&inst, |bind| {
            bind.bind_port::<String>("in", &host_req);
            bind.bind_port::<String>("out", &host_resp);
        })
        .build();

    let t = find_t(&net, "probe/call");
    assert_eq!(alias_of(t, "reqDecl").as_deref(), Some("REQ"));
    assert_eq!(alias_of(t, "respDecl").as_deref(), Some("RESP"));

    // AC#5: discovery returns the ACTUAL composed places, not the declared ones.
    let in_names: Vec<&str> = t.input_specs().iter().map(|s| s.place_name()).collect();
    assert!(in_names.contains(&"REQ"));
    assert!(!in_names.contains(&"reqDecl"));
}

/// AC#3 (MOD-013): the correspondence chains through nested instantiation so a
/// declared place resolves to the doubly-prefixed composed place.
#[test]
fn nested_instantiation_resolves_doubly_prefixed() {
    // Inner subnet: input port "in" (reqDecl) -> internal sink xDecl.
    let req = Place::<String>::new("reqDecl");
    let x = Place::<String>::new("xDecl");
    let emit = Transition::builder("emit")
        .input(one(&req))
        .output(out_place(&x))
        .build();
    let inner = SubnetDef::<()>::builder("Inner")
        .place(&req)
        .place(&x)
        .transition(emit)
        .input_port("in", &req)
        .build();

    // Compose inner (prefix "inner") into a body net, exposing sIn as the bound input.
    let s_in = Place::<String>::new("sIn");
    let inner_inst = inner.instantiate_unit("inner");
    let s_body = PetriNet::builder("Sbody")
        .place(s_in.as_ref())
        .compose_with(&inner_inst, |bind| {
            bind.bind_port::<String>("in", &s_in);
        })
        .build();

    // Retrofit the composed body as subnet S, re-exposing sIn as port "sin".
    let s_def = SubnetDef::from_net(s_body, Interface::builder().input_port("sin", &s_in).build());

    // Instantiate S as "outer" and compose into the host, binding sin -> hostReq.
    let host_req = Place::<String>::new("hostReq");
    let outer_inst = s_def.instantiate_unit("outer");
    let host = PetriNet::builder("host")
        .place(host_req.as_ref())
        .compose_with(&outer_inst, |bind| {
            bind.bind_port::<String>("sin", &host_req);
        })
        .build();

    let t = find_t(&host, "outer/inner/emit");
    // Declared xDecl resolves to the doubly-prefixed internal place (MOD-013).
    assert_eq!(alias_of(t, "xDecl").as_deref(), Some("outer/inner/xDecl"));
    // Declared reqDecl resolves all the way to the host place.
    assert_eq!(alias_of(t, "reqDecl").as_deref(), Some("hostReq"));
}

/// AC#4 (MOD-025): a hand-written transition's correspondence is identity (None).
#[test]
fn hand_written_transition_has_identity_correspondence() {
    let a = Place::<String>::new("a");
    let b = Place::<String>::new("b");
    let t = Transition::builder("t")
        .input(one(&a))
        .output(out_place(&b))
        .build();
    assert!(t.local_name_map().is_none());
}
