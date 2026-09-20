//! MOD-031 AC#8: a declared place whose actual name round-trips to the
//! author's own name at an intermediate pass must still resolve after a later
//! pass renames it — asserted on the **executor run**, because the failure
//! mode is consume-then-throw, not a build error.
//!
//! The transition enables normally, the executor consumes its inputs, and only
//! then does the action fail its declared-place check against a name that no
//! longer exists in the composed net. The tokens are gone ([EXEC-031]).
//!
//! Rust realises the correspondence in the binding-hosted style MOD-031
//! permits: `TransitionContext` exposes `local_name_map()` and the adapter
//! (pyo3, or the native action below) applies it. `resolve_declared` mirrors
//! what `libpetri-py`'s `PyActionContext` does on every lookup.
//!
//! Lives in the umbrella crate because `libpetri-core` cannot depend on
//! `libpetri-runtime`.

use libpetri::core::action::{ActionError, BoxedAction, sync_action};
use libpetri::core::context::TransitionContext;
use libpetri::core::input::one;
use libpetri::core::interface::Interface;
use libpetri::core::output::out_place;
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::subnet_def::SubnetDef;
use libpetri::core::token::Token;
use libpetri::core::transition::Transition;
use libpetri::event::event_store::NoopEventStore;
use libpetri::runtime::executor::{BitmapNetExecutor, ExecutorOptions};
use libpetri::runtime::marking::Marking;

/// Resolves an author-declared place name through the transition's MOD-031
/// declared→actual correspondence, falling back to the literal name — the
/// same two-step a binding adapter performs.
fn resolve_declared(ctx: &TransitionContext, declared: &str) -> String {
    ctx.local_name_map()
        .and_then(|m| m.get(declared).map(|actual| actual.as_ref().to_string()))
        .unwrap_or_else(|| declared.to_string())
}

/// Hardcodes its declared place names, as an action authored against the
/// subnet body would.
fn joins_x_and_y() -> BoxedAction {
    sync_action(|ctx: &mut TransitionContext| -> Result<(), ActionError> {
        let x = resolve_declared(ctx, "x");
        let y = resolve_declared(ctx, "y");
        let z = resolve_declared(ctx, "z");
        let xv = ctx.input::<String>(&x)?;
        let yv = ctx.input::<String>(&y)?;
        ctx.output(&z, format!("{xv}+{yv}"))?;
        Ok(())
    })
}

/// `x` is the port place, `y` an internal input, `z` the internal sink.
fn step_def() -> SubnetDef<()> {
    let x = Place::<String>::new("x");
    let y = Place::<String>::new("y");
    let z = Place::<String>::new("z");

    let call = Transition::builder("call")
        .input(one(&x))
        .input(one(&y))
        .output(out_place(&z))
        .action(joins_x_and_y())
        .build();

    SubnetDef::<()>::builder("Step")
        .place(&x)
        .place(&y)
        .place(&z)
        .transition(call)
        .input_port("in", &x)
        .build()
}

#[test]
fn identity_roundtrip_then_rename_still_fires_and_produces() {
    let inst = step_def().instantiate_unit("inst");

    // Pass 1+2: instantiation prefixes everything, then the port binds to a
    // host place that carries the subnet's own declared name — so `x`'s
    // correspondence round-trips to `x` (identity) while `y` and `z` stay
    // prefixed. The mixed map is what makes this reachable: an all-identity
    // map is dropped whole and the next pass re-derives keys from the arcs.
    let host_x = Place::<String>::new("x");
    let host = PetriNet::builder("Host")
        .place(host_x.as_ref())
        .compose_with(&inst, |b| {
            b.bind_port::<String>("in", &host_x);
        })
        .build();

    // Precondition: the intermediate correspondence really is the *mixed*
    // case. If it were all-identity it would be dropped whole and the next
    // pass would self-heal off the arcs, so the test would pass for the
    // wrong reason.
    let mid = host
        .transitions()
        .iter()
        .find(|t| t.name() == "inst/call")
        .expect("composed transition");
    let mid_map = mid
        .local_name_map()
        .expect("intermediate pass must carry a correspondence");
    assert_eq!(mid_map.get("x").map(|s| &**s), Some("x"));
    assert_eq!(mid_map.get("y").map(|s| &**s), Some("inst/y"));

    // Pass 3: retrofit the host as a subnet and instantiate it — now `x`
    // moves too, and only a correspondence that kept the identity entry can
    // rewrite it.
    let outer_def = SubnetDef::from_net(
        host,
        Interface::builder().input_port("in", &host_x).build(),
    );
    let outer = outer_def.instantiate_unit("outer");
    let net = outer.renamed_body();

    let mut marking = Marking::new();
    marking.add(
        &Place::<String>::new("outer/x"),
        Token::at("X".to_string(), 0),
    );
    marking.add(
        &Place::<String>::new("outer/inst/y"),
        Token::at("Y".to_string(), 0),
    );

    let mut executor =
        BitmapNetExecutor::<NoopEventStore>::new(net, marking, ExecutorOptions::default());
    let final_marking = executor.run_sync();

    assert_eq!(
        final_marking.count("outer/inst/z"),
        1,
        "action must resolve both declared places and produce; a dropped \
         identity entry loses `x` and the firing throws after consuming"
    );
    assert_eq!(
        final_marking.count("outer/x"),
        0,
        "input must have been consumed"
    );
    assert_eq!(
        final_marking.count("outer/inst/y"),
        0,
        "input must have been consumed"
    );
}

/// AC#9: when *every* place round-trips to identity the correspondence may be
/// dropped wholesale — the next pass rebuilds the key set from the arcs, whose
/// names are still author-original, so resolution survives anyway.
#[test]
fn all_identity_correspondence_still_resolves_after_a_later_pass() {
    // Every place is a port, and every port binds to a host place carrying
    // the author's own name — so the whole correspondence is the identity.
    let x = Place::<String>::new("x");
    let y = Place::<String>::new("y");
    let z = Place::<String>::new("z");
    let call = Transition::builder("call")
        .input(one(&x))
        .input(one(&y))
        .output(out_place(&z))
        .action(joins_x_and_y())
        .build();
    let def = SubnetDef::<()>::builder("Step")
        .place(&x)
        .place(&y)
        .place(&z)
        .transition(call)
        .input_port("px", &x)
        .input_port("py", &y)
        .output_port("pz", &z)
        .build();

    let host_x = Place::<String>::new("x");
    let host_y = Place::<String>::new("y");
    let host_z = Place::<String>::new("z");
    let host = PetriNet::builder("Host")
        .place(host_x.as_ref())
        .place(host_y.as_ref())
        .place(host_z.as_ref())
        .compose_with(&def.instantiate_unit("inst"), |b| {
            b.bind_port::<String>("px", &host_x)
                .bind_port::<String>("py", &host_y)
                .bind_port::<String>("pz", &host_z);
        })
        .build();

    let mid = host
        .transitions()
        .iter()
        .find(|t| t.name() == "inst/call")
        .expect("composed transition");
    assert!(
        mid.local_name_map().is_none(),
        "an all-identity correspondence may be dropped whole: {:?}",
        mid.local_name_map()
    );

    // A later pass renames all three; the arc walk re-derives the keys.
    let outer_def = SubnetDef::from_net(
        host,
        Interface::builder().input_port("px", &host_x).build(),
    );
    let outer = outer_def.instantiate_unit("outer");
    let net = outer.renamed_body();

    let mut marking = Marking::new();
    marking.add(
        &Place::<String>::new("outer/x"),
        Token::at("X".to_string(), 0),
    );
    marking.add(
        &Place::<String>::new("outer/y"),
        Token::at("Y".to_string(), 0),
    );

    let mut executor =
        BitmapNetExecutor::<NoopEventStore>::new(net, marking, ExecutorOptions::default());
    let final_marking = executor.run_sync();

    assert_eq!(final_marking.count("outer/z"), 1);
}
