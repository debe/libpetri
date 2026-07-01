//! Regression: a ν-net join's match (`match_spec`) must survive modular
//! composition through the port / instantiate path
//! (spec/12-nu-nets.md **NU-030** MUST, **NU-060**).
//!
//! Before the fix the Rust rewriter dropped `match_spec` on the
//! rename/substitute rebuild, so any ν-net join inside a composed or
//! instantiated subnet silently reverted to a plain FIFO AND join. This is the
//! path Python (PyO3) reaches via `Net.compose`, so it doubles as the Rust-side
//! proof that the Python binding preserves the match.

use libpetri_core::input::one;
use libpetri_core::match_spec::MatchSpec;
use libpetri_core::name::NameId;
use libpetri_core::output::out_place;
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::subnet_def::SubnetDef;
use libpetri_core::transition::Transition;

/// A subnet whose internal transition is a ν-net join correlating its two input
/// ports by name. Both inputs are exposed as ports and bound at compose time.
fn matched_join_subnet() -> SubnetDef<()> {
    let a = Place::<String>::new("a");
    let b = Place::<String>::new("b");
    let merged = Place::<String>::new("merged");
    let join = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .match_spec(
            MatchSpec::builder()
                .key(&a, |s: &String| NameId::new(s.clone()))
                .key(&b, |s: &String| NameId::new(s.clone()))
                .build(),
        )
        .output(out_place(&merged))
        .build();
    SubnetDef::<()>::builder("MatchedJoin")
        .place(&a)
        .place(&b)
        .place(&merged)
        .transition(join)
        .input_port("a", &a)
        .input_port("b", &b)
        .build()
}

#[test]
fn port_composition_preserves_nu_match() {
    let host_a = Place::<String>::new("host_a");
    let host_b = Place::<String>::new("host_b");

    let sub = matched_join_subnet();
    let inst = sub.instantiate_unit("j");

    let host = PetriNet::builder("Host")
        .place(host_a.as_ref())
        .place(host_b.as_ref())
        .compose_with(&inst, |bind| {
            bind.bind_port::<String>("a", &host_a);
            bind.bind_port::<String>("b", &host_b);
        })
        .build();

    // The composed join must still carry its match, now correlating the
    // host-bound places (NU-030) — not reverted to a plain FIFO AND join.
    let join = host
        .transitions()
        .iter()
        .find(|t| t.name().ends_with("/join"))
        .expect("composed join transition present");
    let ms = join
        .match_spec()
        .expect("NU-030: composed join must keep its ν-net match, not drop it");
    assert!(
        ms.correlates("host_a"),
        "match must correlate the host-bound place host_a"
    );
    assert!(
        ms.correlates("host_b"),
        "match must correlate the host-bound place host_b"
    );
}
