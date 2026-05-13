//! End-to-end integration tests for fusion-set resolution per **MOD-061**.
//! Mirrors `typescript/tests/core/fusion.test.ts` and the analogous Java
//! `FusionTest`.
//!
//! Lives in the umbrella `libpetri` crate because `libpetri-core` does not
//! (and cannot) depend on `libpetri-runtime` — the runtime crate already
//! depends on core.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use libpetri::core::action::{ActionError, BoxedAction, sync_action};
use libpetri::core::arc::{inhibitor, read};
use libpetri::core::context::TransitionContext;
use libpetri::core::fusion::FusionSet;
use libpetri::core::input::one;
use libpetri::core::instance::Instance;
use libpetri::core::output::out_place;
use libpetri::core::petri_net::PetriNet;
use libpetri::core::place::Place;
use libpetri::core::subnet_def::SubnetDef;
use libpetri::core::token::Token;
use libpetri::core::transition::Transition;
use libpetri::event::event_store::NoopEventStore;
use libpetri::runtime::executor::{BitmapNetExecutor, ExecutorOptions};
use libpetri::runtime::marking::Marking;

// ============================================================
//  leaky_bucket fixture (mirror TS leakyBucket / Java leakyBucket)
// ============================================================
//
// One transition consumes a `request` token plus a `slots` token and emits
// to `accept`; a second transition consumes a `request` token (with an
// inhibitor on `slots`) and emits to `reject`. The internal `slots` place
// models the per-bucket capacity; fusion-composition tests declare a fusion
// set across the `slots` places of multiple bucket instances to model a
// shared rate limiter.

fn leaky_bucket(rate: u32) -> SubnetDef<()> {
    assert!(rate >= 1, "rate must be >= 1, got: {rate}");
    let request = Place::<String>::new("request");
    let accept = Place::<String>::new("accept");
    let reject = Place::<String>::new("reject");
    let slots = Place::<String>::new("slots");

    // accept-path: needs a slot, consumes the request, emits accept.
    let accept_t = Transition::builder("accept")
        .input(one(&request))
        .input(one(&slots))
        .output(out_place(&accept))
        .build();

    // reject-path: no slot available (inhibitor), still consumes request,
    // emits reject.
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

// ============================================================
//  Helpers
// ============================================================

fn place_names(net: &PetriNet) -> HashSet<String> {
    net.places().iter().map(|p| p.name().to_string()).collect()
}

fn find_transition<'a>(net: &'a PetriNet, name: &str) -> &'a Transition {
    net.transitions()
        .iter()
        .find(|t| t.name() == name)
        .unwrap_or_else(|| {
            let names: Vec<&str> = net.transitions().iter().map(|t| t.name()).collect();
            panic!(
                "no transition '{name}' in '{}'. Available: {names:?}",
                net.name()
            );
        })
}

fn find_renamed_place<P: 'static>(inst: &Instance<P>, renamed_name: &str) -> Place<String> {
    for p in inst.renamed_body().places() {
        if p.name() == renamed_name {
            return Place::<String>::new(Arc::clone(p.name_arc()));
        }
    }
    let have: Vec<&str> = inst
        .renamed_body()
        .places()
        .iter()
        .map(|p| p.name())
        .collect();
    panic!(
        "no place '{renamed_name}' in instance with prefix '{}'. Places: {have:?}",
        inst.prefix()
    );
}

/// Forwarding action used by the leaky-bucket integration test: emits a
/// marker token to every declared output place. The default passthrough
/// emits no outputs, so we need explicit forwarding to observe accept/reject
/// markings.
fn forward_action() -> BoxedAction {
    sync_action(|ctx: &mut TransitionContext| -> Result<(), ActionError> {
        for op in ctx.output_place_names() {
            ctx.output(&op, "x".to_string())?;
        }
        Ok(())
    })
}

/// Returns a map keyed by transition name, valued by a set of "kind:place"
/// strings summarising every arc reference. Lets us compare two nets' arc
/// topologies regardless of transition identity.
fn arc_summary_by_transition_name(net: &PetriNet) -> HashMap<String, HashSet<String>> {
    let mut out: HashMap<String, HashSet<String>> = HashMap::new();
    for t in net.transitions() {
        let mut refs: HashSet<String> = HashSet::new();
        for spec in t.input_specs() {
            refs.insert(format!("in:{}", spec.place().name()));
        }
        for p in t.output_places() {
            refs.insert(format!("out:{}", p.name()));
        }
        for inh in t.inhibitors() {
            refs.insert(format!("inh:{}", inh.place.name()));
        }
        for r in t.reads() {
            refs.insert(format!("read:{}", r.place.name()));
        }
        for r in t.resets() {
            refs.insert(format!("reset:{}", r.place.name()));
        }
        out.insert(t.name().to_string(), refs);
    }
    out
}

// ============================================================
//  Tests
// ============================================================

#[test]
fn fuse_substitutes_non_canonical_in_arcs() {
    let a = Place::<String>::new("A"); // canonical
    let b = Place::<String>::new("B"); // non-canonical
    let sink = Place::<String>::new("sink");

    // T1 reads from B (non-canonical) → after fuse, reads from A.
    let t1 = Transition::builder("readFromB").read(read(&b)).build();
    // T2 writes to B (non-canonical) → after fuse, writes to A.
    let t2 = Transition::builder("writeToB")
        .input(one(&sink))
        .output(out_place(&b))
        .build();

    let net = PetriNet::builder("Fused")
        .transitions([t1, t2])
        .fuse([FusionSet::of("ab", &a, &[&b])])
        .build();

    let names = place_names(&net);
    assert!(names.contains("A"));
    assert!(names.contains("sink"));
    assert!(!names.contains("B"));

    let read_from_b = find_transition(&net, "readFromB");
    let read_names: HashSet<&str> = read_from_b
        .read_places()
        .iter()
        .map(|p| p.name())
        .collect();
    assert!(read_names.contains("A"));
    assert!(!read_names.contains("B"));

    let write_to_b = find_transition(&net, "writeToB");
    let out_names: HashSet<&str> = write_to_b
        .output_places()
        .iter()
        .map(|p| p.name())
        .collect();
    assert!(out_names.contains("A"));
    assert!(!out_names.contains("B"));
}

#[test]
fn fuse_unrelated_places_unchanged() {
    let a = Place::<String>::new("A");
    let b = Place::<String>::new("B");
    let c = Place::<String>::new("C"); // unrelated to {A, B}

    let t1 = Transition::builder("usesC").read(read(&c)).build();

    let net = PetriNet::builder("Mixed")
        .transition(t1)
        .place(c.as_ref())
        .fuse([FusionSet::of("ab", &a, &[&b])])
        .build();

    assert!(place_names(&net).contains("C"));
    let rewritten = find_transition(&net, "usesC");
    let read_names: HashSet<&str> = rewritten.read_places().iter().map(|p| p.name()).collect();
    assert!(read_names.contains("C"));
}

#[test]
fn fuse_overlapping_fusion_sets_panics() {
    let a = Place::<String>::new("A");
    let b = Place::<String>::new("B");
    let c = Place::<String>::new("C");

    let s1 = FusionSet::of("set1", &a, &[&b]);
    let s2 = FusionSet::of("set2", &b, &[&c]); // B is in both!

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = PetriNet::builder("Bad").fuse([s1, s2]).build();
    }));
    let err = result.expect_err("build must panic on overlapping fusion sets");
    let msg: String = err
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| err.downcast_ref::<&'static str>().map(|s| s.to_string()))
        .unwrap_or_default();
    assert!(msg.contains('B'), "must name the offending place: {msg}");
    assert!(msg.contains("set1"), "must name first set: {msg}");
    assert!(msg.contains("set2"), "must name second set: {msg}");
}

#[test]
fn fuse_chained_three_buckets_share_limiter() {
    // Three instances of leaky-bucket, each with its own internal `slots`
    // place. Compose all three; declare a fusion set across the three slots
    // places. The resulting net has a single canonical `slots`.
    let actions: HashMap<Arc<str>, BoxedAction> = {
        let mut m = HashMap::new();
        m.insert(Arc::<str>::from("accept"), forward_action());
        m.insert(Arc::<str>::from("reject"), forward_action());
        m
    };

    let bucket_def = leaky_bucket(2);
    let b1 = bucket_def.instantiate("b1", ()).bind_actions(actions.clone());
    let b2 = bucket_def.instantiate("b2", ()).bind_actions(actions.clone());
    let b3 = bucket_def.instantiate("b3", ()).bind_actions(actions);

    // Each instance gets its own external request/accept/reject places.
    let req1 = Place::<String>::new("req1");
    let acc1 = Place::<String>::new("acc1");
    let rej1 = Place::<String>::new("rej1");
    let req2 = Place::<String>::new("req2");
    let acc2 = Place::<String>::new("acc2");
    let rej2 = Place::<String>::new("rej2");
    let req3 = Place::<String>::new("req3");
    let acc3 = Place::<String>::new("acc3");
    let rej3 = Place::<String>::new("rej3");

    // Resolve the renamed slots places by name on the renamed body.
    let slots_b1 = find_renamed_place(&b1, "b1/slots");
    let slots_b2 = find_renamed_place(&b2, "b2/slots");
    let slots_b3 = find_renamed_place(&b3, "b3/slots");

    let net = PetriNet::builder("ThreeBuckets")
        .compose_with(&b1, |b| {
            b.bind_port::<String>("request", &req1)
                .bind_port::<String>("accept", &acc1)
                .bind_port::<String>("reject", &rej1);
        })
        .compose_with(&b2, |b| {
            b.bind_port::<String>("request", &req2)
                .bind_port::<String>("accept", &acc2)
                .bind_port::<String>("reject", &rej2);
        })
        .compose_with(&b3, |b| {
            b.bind_port::<String>("request", &req3)
                .bind_port::<String>("accept", &acc3)
                .bind_port::<String>("reject", &rej3);
        })
        .fuse([FusionSet::of("sharedSlots", &slots_b1, &[&slots_b2, &slots_b3])])
        .build();

    // Assertion 1: canonical slotsB1 survives; non-canonical slotsB2/B3 do not.
    let names = place_names(&net);
    assert!(names.contains("b1/slots"));
    assert!(!names.contains("b2/slots"));
    assert!(!names.contains("b3/slots"));

    // Assertion 2: every accept transition consumes from the canonical slots.
    let b1_accept = find_transition(&net, "b1/accept");
    let b1_accept_inputs: HashSet<&str> =
        b1_accept.input_places().iter().map(|p| p.name()).collect();
    assert!(b1_accept_inputs.contains("b1/slots"));

    let b2_accept = find_transition(&net, "b2/accept");
    let b2_accept_inputs: HashSet<&str> =
        b2_accept.input_places().iter().map(|p| p.name()).collect();
    assert!(b2_accept_inputs.contains("b1/slots"));
    assert!(!b2_accept_inputs.contains("b2/slots"));

    let b3_accept = find_transition(&net, "b3/accept");
    let b3_accept_inputs: HashSet<&str> =
        b3_accept.input_places().iter().map(|p| p.name()).collect();
    assert!(b3_accept_inputs.contains("b1/slots"));
    assert!(!b3_accept_inputs.contains("b3/slots"));

    // Assertion 3: dynamic behaviour — only 2 slots total available across
    // all three buckets. Send three requests; only 2 should accept.
    let mut marking = Marking::new();
    marking.add(&req1, Token::at("r1".to_string(), 0));
    marking.add(&req2, Token::at("r2".to_string(), 0));
    marking.add(&req3, Token::at("r3".to_string(), 0));
    // 2 shared slots — pick the canonical place by name in the built net.
    marking.add(&slots_b1, Token::at("s".to_string(), 0));
    marking.add(&slots_b1, Token::at("s".to_string(), 0));

    let mut executor = BitmapNetExecutor::<NoopEventStore>::new(
        &net,
        marking,
        ExecutorOptions::default(),
    );
    let final_marking = executor.run_sync();

    let total_accepts = final_marking.count("acc1")
        + final_marking.count("acc2")
        + final_marking.count("acc3");
    let total_rejects = final_marking.count("rej1")
        + final_marking.count("rej2")
        + final_marking.count("rej3");

    assert_eq!(total_accepts, 2, "exactly 2 accepts expected");
    assert_eq!(total_rejects, 1, "exactly 1 reject expected");
}

#[test]
fn fuse_runs_after_compose() {
    // Declare a fusion set BEFORE the compose call. The fusion set
    // references places that only exist after the renamed body is merged
    // into the host. Builder accumulates fuse sets and applies at build().
    let bucket_def = leaky_bucket(1);
    let b1 = bucket_def.instantiate("b1", ());
    let b2 = bucket_def.instantiate("b2", ());

    let req1 = Place::<String>::new("req1");
    let acc1 = Place::<String>::new("acc1");
    let rej1 = Place::<String>::new("rej1");
    let req2 = Place::<String>::new("req2");
    let acc2 = Place::<String>::new("acc2");
    let rej2 = Place::<String>::new("rej2");

    let slots_b1 = find_renamed_place(&b1, "b1/slots");
    let slots_b2 = find_renamed_place(&b2, "b2/slots");

    // fuse(...) called BEFORE the compose calls.
    let net = PetriNet::builder("OrderIndependent")
        .fuse([FusionSet::of("shared", &slots_b1, &[&slots_b2])])
        .compose_with(&b1, |b| {
            b.bind_port::<String>("request", &req1)
                .bind_port::<String>("accept", &acc1)
                .bind_port::<String>("reject", &rej1);
        })
        .compose_with(&b2, |b| {
            b.bind_port::<String>("request", &req2)
                .bind_port::<String>("accept", &acc2)
                .bind_port::<String>("reject", &rej2);
        })
        .build();

    let names = place_names(&net);
    assert!(names.contains("b1/slots"));
    assert!(!names.contains("b2/slots"));

    let b2_accept = find_transition(&net, "b2/accept");
    let b2_accept_inputs: HashSet<&str> =
        b2_accept.input_places().iter().map(|p| p.name()).collect();
    assert!(b2_accept_inputs.contains("b1/slots"));
}

#[test]
fn fuse_independent_of_channel_composition() {
    // Subnet with a channel `fire` and an internal place `shared`.
    let shared_def = Place::<String>::new("shared");
    let tick_def = Place::<String>::new("tick");
    let fire_t = Transition::builder("fire")
        .read(read(&tick_def))
        .output(out_place(&shared_def))
        .build();
    let def = SubnetDef::<()>::builder("HasChannelAndInternal")
        .place(&shared_def)
        .place(&tick_def)
        .transition(fire_t.clone())
        .channel("fire", &fire_t)
        .build();

    let inst = def.instantiate("i1", ());

    // Caller-side place to fuse with the renamed shared place.
    let host_shared = Place::<String>::new("hostShared");

    // Caller-side transition for the channel binding.
    let host_trigger = Place::<String>::new("hostTrigger");
    let caller_side = Transition::builder("callerFire")
        .read(read(&host_trigger))
        .build();

    let renamed_shared = find_renamed_place(&inst, "i1/shared");

    let net = PetriNet::builder("ChannelPlusFusion")
        .compose_with(&inst, |b| {
            b.bind_channel("fire", &caller_side);
        })
        .fuse([FusionSet::of("share", &host_shared, &[&renamed_shared])])
        .build();

    // Channel composition: the merged caller-side transition exists.
    let merged = find_transition(&net, "callerFire");
    // Fusion: the renamed-instance shared place is gone; hostShared is the
    // canonical and lives in the place set + on the merged transition's
    // output.
    let names = place_names(&net);
    assert!(names.contains("hostShared"));
    assert!(!names.contains("i1/shared"));

    let merged_out_names: HashSet<&str> =
        merged.output_places().iter().map(|p| p.name()).collect();
    assert!(merged_out_names.contains("hostShared"));
}

#[test]
fn fuse_and_compose_orthogonality() {
    // Two equivalent flat nets:
    //   netA: compose-then-fuse (fuse() called after compose())
    //   netB: fuse-then-compose (fuse() called before compose())
    // Both must produce structurally equivalent place + arc sets.
    let bucket_def = leaky_bucket(2);

    // ---- netA: compose-then-fuse ----
    let b1_a = bucket_def.instantiate("b1", ());
    let b2_a = bucket_def.instantiate("b2", ());
    let req1_a = Place::<String>::new("req1");
    let acc1_a = Place::<String>::new("acc1");
    let rej1_a = Place::<String>::new("rej1");
    let req2_a = Place::<String>::new("req2");
    let acc2_a = Place::<String>::new("acc2");
    let rej2_a = Place::<String>::new("rej2");
    let slots_b1_a = find_renamed_place(&b1_a, "b1/slots");
    let slots_b2_a = find_renamed_place(&b2_a, "b2/slots");

    let net_a = PetriNet::builder("ComposeThenFuse")
        .compose_with(&b1_a, |b| {
            b.bind_port::<String>("request", &req1_a)
                .bind_port::<String>("accept", &acc1_a)
                .bind_port::<String>("reject", &rej1_a);
        })
        .compose_with(&b2_a, |b| {
            b.bind_port::<String>("request", &req2_a)
                .bind_port::<String>("accept", &acc2_a)
                .bind_port::<String>("reject", &rej2_a);
        })
        .fuse([FusionSet::of("shared", &slots_b1_a, &[&slots_b2_a])])
        .build();

    // ---- netB: fuse-then-compose ----
    let b1_b = bucket_def.instantiate("b1", ());
    let b2_b = bucket_def.instantiate("b2", ());
    let req1_b = Place::<String>::new("req1");
    let acc1_b = Place::<String>::new("acc1");
    let rej1_b = Place::<String>::new("rej1");
    let req2_b = Place::<String>::new("req2");
    let acc2_b = Place::<String>::new("acc2");
    let rej2_b = Place::<String>::new("rej2");
    let slots_b1_b = find_renamed_place(&b1_b, "b1/slots");
    let slots_b2_b = find_renamed_place(&b2_b, "b2/slots");

    let net_b = PetriNet::builder("FuseThenCompose")
        .fuse([FusionSet::of("shared", &slots_b1_b, &[&slots_b2_b])])
        .compose_with(&b1_b, |b| {
            b.bind_port::<String>("request", &req1_b)
                .bind_port::<String>("accept", &acc1_b)
                .bind_port::<String>("reject", &rej1_b);
        })
        .compose_with(&b2_b, |b| {
            b.bind_port::<String>("request", &req2_b)
                .bind_port::<String>("accept", &acc2_b)
                .bind_port::<String>("reject", &rej2_b);
        })
        .build();

    // Place sets must match by name (Rust Place identity is name-based).
    let names_a: HashSet<String> = place_names(&net_a);
    let names_b: HashSet<String> = place_names(&net_b);
    let mut sorted_a: Vec<&str> = names_a.iter().map(|s| s.as_str()).collect();
    let mut sorted_b: Vec<&str> = names_b.iter().map(|s| s.as_str()).collect();
    sorted_a.sort();
    sorted_b.sort();
    assert_eq!(sorted_a, sorted_b);

    // Transition arc topologies must match by transition name.
    let summary_a = arc_summary_by_transition_name(&net_a);
    let summary_b = arc_summary_by_transition_name(&net_b);
    assert_eq!(summary_a.len(), summary_b.len());
    for (t_name, refs_a) in &summary_a {
        let refs_b = summary_b
            .get(t_name)
            .unwrap_or_else(|| panic!("transition '{t_name}' missing in netB"));
        let mut sa: Vec<&str> = refs_a.iter().map(|s| s.as_str()).collect();
        let mut sb: Vec<&str> = refs_b.iter().map(|s| s.as_str()).collect();
        sa.sort();
        sb.sort();
        assert_eq!(sa, sb, "arc topology mismatch for '{t_name}'");
    }
}

#[test]
fn fuse_with_sugar_overload_builds_and_applies() {
    let a = Place::<String>::new("A");
    let b = Place::<String>::new("B");

    let t1 = Transition::builder("readFromB").read(read(&b)).build();

    let net = PetriNet::builder("Sugar")
        .transition(t1)
        .fuse_with(|fb| {
            fb.member(&a).member(&b);
        })
        .build();

    let names = place_names(&net);
    assert!(names.contains("A"));
    assert!(!names.contains("B"));
}

#[test]
fn fuse_multiple_disjoint_sets_each_applies_independently() {
    let a = Place::<String>::new("A");
    let b = Place::<String>::new("B");
    let c = Place::<String>::new("C");
    let d = Place::<String>::new("D");

    let t1 = Transition::builder("readsBandD")
        .read(read(&b))
        .read(read(&d))
        .build();

    let net = PetriNet::builder("Multi")
        .transition(t1)
        .fuse([
            FusionSet::of("ab", &a, &[&b]),
            FusionSet::of("cd", &c, &[&d]),
        ])
        .build();

    let names = place_names(&net);
    assert!(names.contains("A"));
    assert!(names.contains("C"));
    assert!(!names.contains("B"));
    assert!(!names.contains("D"));

    let rewritten = find_transition(&net, "readsBandD");
    let read_names: HashSet<&str> = rewritten.read_places().iter().map(|p| p.name()).collect();
    assert!(read_names.contains("A"));
    assert!(read_names.contains("C"));
    assert!(!read_names.contains("B"));
    assert!(!read_names.contains("D"));
}

#[test]
fn fuse_single_member_set_is_no_op() {
    let a = Place::<String>::new("A");
    let t1 = Transition::builder("readsA").read(read(&a)).build();

    let net = PetriNet::builder("SoloFusion")
        .transition(t1)
        .fuse([FusionSet::builder("solo").member(&a).build()])
        .build();

    assert!(place_names(&net).contains("A"));
    let rewritten = find_transition(&net, "readsA");
    let read_names: HashSet<&str> = rewritten.read_places().iter().map(|p| p.name()).collect();
    assert!(read_names.contains("A"));
}

