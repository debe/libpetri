//! Randomized differential testing of the two executor backends.
//!
//! [`backend_suite_tests`](crate::backend_suite_tests) runs every
//! hand-written semantic test against both `BitmapNetExecutor` (the
//! reference) and `PrecompiledNetExecutor` (production). This module closes
//! the gap the hand-written suite cannot: it generates small well-formed
//! nets with proptest — untimed for one property, timed for its twin —
//! runs each one through both backends via
//! the suite's [`BackendRunner`]s, and asserts the outcomes are
//! observationally equal — final marking (token values per place, FIFO
//! order), quiescence, and the deterministic projection of the event
//! sequence. `assert_token_conservation` already runs inside each runner,
//! so every generated case also re-checks the Lean `token_conservation`
//! twin per backend.
//!
//! Generated fragment: 2–8 places (all `i32`), 0–6 initial tokens per place
//! (values 0–9), 1–8 transitions with 1–3 distinct input places
//! (cardinality one / exactly(2) / all / at_least(2)), 0–2 read arcs, 0–1
//! inhibitor arcs, 0–1 reset arcs, priority 0–2. Transitions outnumber
//! priority levels on purpose: passes that fire three or more transitions
//! are where intra-pass visibility bugs live (divergence #5 below), and they
//! only occur when several transitions sit ready at the same level with
//! enough tokens to satisfy all of them. The untimed property keeps
//! timing `immediate` only; the timed property additionally draws timing from
//! {immediate, delayed, window, deadline, exact} (see [`gen_timing`]) and
//! drives both backends through `run_sync` on the executor's `#[cfg(test)]`
//! virtual clock with deadline tolerance 0, so timed runs are instant and
//! bit-for-bit reproducible. ν-net features (`MatchSpec`, `ForwardInput`)
//! are an extension point deliberately left out.
//!
//! Termination by construction: the runner executes each net to sync
//! quiescence, so every generated net must be finite-firing. We enforce a
//! DAG discipline — every output place index of a transition is strictly
//! greater than every input place index of that same transition
//! (read/inhibitor/reset arcs are unconstrained). A firing consumes at
//! least one token at some index <= i_max (its highest input index) and
//! deposits at most two tokens at indices > i_max, so the potential
//! `sum over tokens of 3^(P - place_index)` strictly decreases on every
//! firing (2 * 3^(P - i - 1) < 3^(P - i)). Total firings are therefore
//! bounded and no step budget is needed.
//!
//! Timing does not weaken that argument: a timing constraint only decides
//! *when* a transition may fire, never what a firing consumes or produces.
//! An enabled timed transition whose input tokens persist re-enables after
//! every firing and can fire again — but each re-firing still consumes at
//! least one token at index <= i_max and deposits only above it, so the same
//! potential strictly decreases on every firing and total firings stay
//! bounded regardless of timing. The virtual clock guarantees the harness
//! *reaches* those firings without wall-clock waiting: a cycle that fires
//! nothing jumps time to the next `earliest`/deadline boundary, where either
//! something fires or the enabled set shrinks.

#![cfg(test)]

use std::collections::BTreeMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use libpetri_core::action::{passthrough, sync_action};
use libpetri_core::arc::{inhibitor, read, reset};
use libpetri_core::input::{all, at_least, exactly, one};
use libpetri_core::output::{and, out_place, xor};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::timing::{deadline, delayed, exact, window};
use libpetri_core::token::Token;
use libpetri_core::transition::Transition;
use libpetri_event::event_store::{EventStore, InMemoryEventStore};
use libpetri_event::net_event::NetEvent;

use proptest::prelude::*;

use crate::backend_suite_tests::{
    BackendRunner, BitmapRunner, PrecompiledRunner, RunResult, assert_token_conservation,
};
use crate::compiled_net::CompiledNet;
use crate::executor::{BitmapNetExecutor, ExecutorOptions};
use crate::marking::Marking;
use crate::precompiled_executor::PrecompiledNetExecutor;
use crate::precompiled_net::PrecompiledNet;

// ---------------------------------------------------------------------------
//  Generator model
// ---------------------------------------------------------------------------

/// Input-arc cardinality. `Exactly2`/`AtLeast2` fix n = 2 — enough to
/// exercise the CONSUME_N / CONSUME_ATLEAST opcodes without blowing up the
/// state space.
#[derive(Debug, Clone, Copy)]
enum GenCard {
    One,
    Exactly2,
    All,
    AtLeast2,
}

/// Output shape, as indices into the place vector. All variants respect the
/// DAG discipline (indices strictly above every input index); `None` is the
/// forced shape when no higher-indexed place exists.
#[derive(Debug, Clone, Copy)]
enum GenOut {
    /// Sink: no output spec, `passthrough()` action (CORE-043 pairing).
    None,
    /// Single `out_place` leaf; the echo action writes it.
    Single(usize),
    /// `and([a, b])`; the echo action writes both branches.
    And(usize, usize),
    /// `xor([a, b])`; the echo action routes by `value % 2` to one branch.
    Xor(usize, usize),
}

/// Timing constraint. Bounds are small integers (milliseconds on the virtual
/// clock) so windows overlap and interleave across transitions; `Window`
/// stores (earliest, latest) with latest strictly greater.
#[derive(Debug, Clone, Copy)]
enum GenTiming {
    Immediate,
    Delayed(u64),
    Window(u64, u64),
    Deadline(u64),
    Exact(u64),
}

#[derive(Debug, Clone)]
struct GenTrans {
    /// Distinct ascending place indices paired with a cardinality. Distinct
    /// because duplicate input arcs on one place are rejected at
    /// `CompiledNet::compile` (CORE-030).
    inputs: Vec<(usize, GenCard)>,
    output: GenOut,
    /// Distinct place indices; may overlap inputs/reset (EXEC-012/EXEC-013
    /// read-peek semantics are exactly the historically buggy overlap).
    reads: Vec<usize>,
    inhibitor: Option<usize>,
    reset: Option<usize>,
    priority: i32,
    timing: GenTiming,
}

#[derive(Debug, Clone)]
struct GenNet {
    place_count: usize,
    /// Initial token values per place, in FIFO order.
    initial: Vec<Vec<i32>>,
    transitions: Vec<GenTrans>,
}

fn gen_card() -> impl Strategy<Value = GenCard> {
    prop_oneof![
        3 => Just(GenCard::One),
        1 => Just(GenCard::Exactly2),
        1 => Just(GenCard::All),
        1 => Just(GenCard::AtLeast2),
    ]
}

fn gen_transition(place_count: usize) -> impl Strategy<Value = GenTrans> {
    let places: Vec<usize> = (0..place_count).collect();
    let max_inputs = place_count.min(3);
    (
        prop::sample::subsequence(places.clone(), 1..=max_inputs),
        prop::collection::vec(gen_card(), max_inputs),
        // Output shape selector: 0 => none, 1-3 => single, 4-5 => and,
        // 6-7 => xor (and/xor degrade to single when only one place lies
        // above the inputs).
        0u8..8,
        any::<prop::sample::Index>(),
        any::<prop::sample::Index>(),
        prop::sample::subsequence(places, 0..=2usize),
        prop::option::of(0..place_count),
        prop::option::of(0..place_count),
        // Fewer priority levels than transitions, so ready lists stack up
        // several deep at one level (see the module docs).
        0i32..=2,
    )
        .prop_map(
            move |(ins, cards, out_kind, o1, o2, reads, inhibitor, reset, priority)| {
                let inputs: Vec<(usize, GenCard)> =
                    ins.iter().copied().zip(cards).collect();
                // DAG discipline: outputs live strictly above the highest
                // input index (see module docs for the termination argument).
                let lo = ins.last().copied().unwrap() + 1;
                let avail = place_count - lo;
                let output = if avail == 0 || out_kind == 0 {
                    GenOut::None
                } else {
                    let first = lo + o1.index(avail);
                    match out_kind {
                        1..=3 => GenOut::Single(first),
                        _ if avail < 2 => GenOut::Single(first),
                        k => {
                            // Second pick: offset into the remaining
                            // avail - 1 slots, guaranteed distinct from
                            // `first`.
                            let second =
                                lo + (first - lo + 1 + o2.index(avail - 1)) % avail;
                            if k <= 5 {
                                GenOut::And(first, second)
                            } else {
                                GenOut::Xor(first, second)
                            }
                        }
                    }
                };
                GenTrans {
                    inputs,
                    output,
                    reads,
                    inhibitor,
                    reset,
                    priority,
                    // Constant, not drawn: the untimed strategy must keep its
                    // exact RNG stream so committed regression seeds replay
                    // the same nets. Timed nets go through
                    // [`gen_timed_transition`], which draws this field.
                    timing: GenTiming::Immediate,
                }
            },
        )
}

fn gen_net() -> impl Strategy<Value = GenNet> {
    (2usize..=8).prop_flat_map(|place_count| {
        (
            prop::collection::vec(prop::collection::vec(0i32..10, 0..=6), place_count),
            prop::collection::vec(gen_transition(place_count), 1..=8),
        )
            .prop_map(move |(initial, transitions)| GenNet {
                place_count,
                initial,
                transitions,
            })
    })
}

/// Timing distribution for the timed property: immediate stays the common
/// case (weight 4) so timed and untimed transitions interleave; the four
/// timed constructors get weight 1 each. Bounds are 1..=30 ms virtual
/// (windows: earliest 1..=20, latest = earliest + 1..=30, so every window is
/// non-degenerate and hard deadlines land within a couple of clock jumps).
fn gen_timing() -> impl Strategy<Value = GenTiming> {
    prop_oneof![
        4 => Just(GenTiming::Immediate),
        1 => (1u64..=30).prop_map(GenTiming::Delayed),
        1 => (1u64..=20, 1u64..=30).prop_map(|(e, d)| GenTiming::Window(e, e + d)),
        1 => (1u64..=30).prop_map(GenTiming::Deadline),
        1 => (1u64..=30).prop_map(GenTiming::Exact),
    ]
}

/// [`gen_transition`] plus a drawn timing. Layered on top rather than folded
/// in so the untimed strategy's RNG stream stays byte-identical.
fn gen_timed_transition(place_count: usize) -> impl Strategy<Value = GenTrans> {
    (gen_transition(place_count), gen_timing()).prop_map(|(mut t, timing)| {
        t.timing = timing;
        t
    })
}

/// [`gen_net`] with timed transitions. Same structural fragment; see the
/// module docs for why the DAG termination argument is timing-independent.
fn gen_timed_net() -> impl Strategy<Value = GenNet> {
    (2usize..=8).prop_flat_map(|place_count| {
        (
            prop::collection::vec(prop::collection::vec(0i32..10, 0..=6), place_count),
            prop::collection::vec(gen_timed_transition(place_count), 1..=8),
        )
            .prop_map(move |(initial, transitions)| GenNet {
                place_count,
                initial,
                transitions,
            })
    })
}

// ---------------------------------------------------------------------------
//  GenNet -> (PetriNet, Marking)
// ---------------------------------------------------------------------------

/// Builds the concrete net + initial marking. The output/action pairing is
/// DERIVED from the generated structure, never generated independently:
///
/// - no outputs        -> `passthrough()` and no output spec (CORE-043);
/// - single / AND      -> a `sync_action` echoing the derived value to every
///                        declared output place (satisfies IO-015);
/// - XOR               -> route by `value % branch_count` to exactly one
///                        branch (the suite's classifier idiom).
///
/// The echoed value is the first consumed token of the first input place
/// plus the front token of every read arc that still holds one at firing
/// time. Folding reads in makes the oracle sensitive to the EXEC-012/
/// EXEC-013 read-peek boundary (post-input, pre-reset) — the historically
/// divergent spot — while staying total: a read place drained by this very
/// firing's input consumption simply contributes nothing.
fn build_net(g: &GenNet) -> (PetriNet, Marking) {
    let places: Vec<Place<i32>> = (0..g.place_count)
        .map(|i| Place::new(format!("p{i}")))
        .collect();

    let mut builder = PetriNet::builder("differential");
    for p in &places {
        builder = builder.place(p.as_ref());
    }

    for (ti, gt) in g.transitions.iter().enumerate() {
        let mut tb = Transition::builder(format!("t{ti}"));
        for &(pi, card) in &gt.inputs {
            tb = tb.input(match card {
                GenCard::One => one(&places[pi]),
                GenCard::Exactly2 => exactly(2, &places[pi]),
                GenCard::All => all(&places[pi]),
                GenCard::AtLeast2 => at_least(2, &places[pi]),
            });
        }
        for &ri in &gt.reads {
            tb = tb.read(read(&places[ri]));
        }
        if let Some(ii) = gt.inhibitor {
            tb = tb.inhibitor(inhibitor(&places[ii]));
        }
        if let Some(ri) = gt.reset {
            tb = tb.reset(reset(&places[ri]));
        }
        tb = tb.priority(gt.priority);
        tb = match gt.timing {
            GenTiming::Immediate => tb, // builder default
            GenTiming::Delayed(ms) => tb.timing(delayed(ms)),
            GenTiming::Window(e, l) => tb.timing(window(e, l)),
            GenTiming::Deadline(ms) => tb.timing(deadline(ms)),
            GenTiming::Exact(ms) => tb.timing(exact(ms)),
        };

        tb = match gt.output {
            GenOut::None => tb.action(passthrough()),
            _ => {
                let (spec, out_indices, is_xor) = match gt.output {
                    GenOut::Single(a) => (out_place(&places[a]), vec![a], false),
                    GenOut::And(a, b) => (
                        and(vec![out_place(&places[a]), out_place(&places[b])]),
                        vec![a, b],
                        false,
                    ),
                    GenOut::Xor(a, b) => (
                        xor(vec![out_place(&places[a]), out_place(&places[b])]),
                        vec![a, b],
                        true,
                    ),
                    GenOut::None => unreachable!(),
                };
                let first_in = Arc::clone(places[gt.inputs[0].0].name_arc());
                let read_names: Vec<Arc<str>> = gt
                    .reads
                    .iter()
                    .map(|&ri| Arc::clone(places[ri].name_arc()))
                    .collect();
                let out_names: Vec<Arc<str>> = out_indices
                    .iter()
                    .map(|&oi| Arc::clone(places[oi].name_arc()))
                    .collect();
                tb.output(spec).action(sync_action(move |ctx| {
                    // `one` consumes exactly 1 token and the batched
                    // cardinalities >= 1 (enablement guarantees it), so the
                    // first consumed token always exists.
                    let vals = ctx.inputs::<i32>(&first_in)?;
                    let mut v = vals.first().map(|a| **a).unwrap_or(0);
                    for r in &read_names {
                        if let Ok(rv) = ctx.read::<i32>(r) {
                            v += *rv;
                        }
                    }
                    if is_xor {
                        let branch = v.rem_euclid(out_names.len() as i32) as usize;
                        ctx.output(&out_names[branch], v)?;
                    } else {
                        for name in &out_names {
                            ctx.output(name, v)?;
                        }
                    }
                    Ok(())
                }))
            }
        };

        builder = builder.transition(tb.build());
    }

    let mut marking = Marking::new();
    for (pi, values) in g.initial.iter().enumerate() {
        for &v in values {
            marking.add(&places[pi], Token::at(v, 0));
        }
    }

    (builder.build(), marking)
}

// ---------------------------------------------------------------------------
//  Oracle
// ---------------------------------------------------------------------------

/// Strongest deterministic marking signal: token VALUES per place in FIFO
/// order (counts are implied by the lengths). Actions are deterministic and
/// scheduling is priority-then-FIFO, so both backends must agree exactly.
fn marking_values(g: &GenNet, marking: &Marking) -> BTreeMap<String, Vec<i32>> {
    (0..g.place_count)
        .map(|i| {
            let name = format!("p{i}");
            let values = marking
                .queue(&name)
                .map(|q| {
                    q.iter()
                        .map(|t| {
                            *t.downcast::<i32>()
                                .expect("harness only mints i32 tokens")
                                .value_arc()
                        })
                        .collect()
                })
                .unwrap_or_default();
            (name, values)
        })
        .collect()
}

/// Deterministic projection of an event: kind plus place/transition name
/// fields (and error/log payloads, which are deterministic here), dropping
/// the wall-clock `timestamp` every variant carries. `TokenAdded`/
/// `TokenRemoved` payloads are `None` under `InMemoryEventStore` and are
/// dropped too.
fn project_events(events: &[NetEvent]) -> Vec<String> {
    events
        .iter()
        .map(|e| match e {
            NetEvent::ExecutionStarted { net_name, .. } => {
                format!("execution-started {net_name}")
            }
            NetEvent::ExecutionCompleted { net_name, .. } => {
                format!("execution-completed {net_name}")
            }
            NetEvent::TransitionEnabled { transition_name, .. } => {
                format!("transition-enabled {transition_name}")
            }
            NetEvent::TransitionClockRestarted { transition_name, .. } => {
                format!("transition-clock-restarted {transition_name}")
            }
            NetEvent::TransitionStarted { transition_name, .. } => {
                format!("transition-started {transition_name}")
            }
            NetEvent::TransitionCompleted { transition_name, .. } => {
                format!("transition-completed {transition_name}")
            }
            NetEvent::TransitionFailed {
                transition_name,
                error,
                ..
            } => format!("transition-failed {transition_name}: {error}"),
            NetEvent::TransitionTimedOut { transition_name, .. } => {
                format!("transition-timed-out {transition_name}")
            }
            NetEvent::ActionTimedOut {
                transition_name,
                timeout_ms,
                ..
            } => format!("action-timed-out {transition_name} {timeout_ms}"),
            NetEvent::TokenAdded { place_name, .. } => {
                format!("token-added {place_name}")
            }
            NetEvent::TokenRemoved { place_name, .. } => {
                format!("token-removed {place_name}")
            }
            NetEvent::LogMessage {
                transition_name,
                level,
                message,
                ..
            } => format!("log {transition_name} {level} {message}"),
            NetEvent::MarkingSnapshot { marking, .. } => {
                let mut entries: Vec<String> =
                    marking.iter().map(|(k, v)| format!("{k}={v}")).collect();
                entries.sort();
                format!("marking-snapshot {}", entries.join(","))
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
//  Timed runners (virtual clock, strict deadlines)
// ---------------------------------------------------------------------------

/// [`BitmapRunner`] twin for the timed property: deadline tolerance 0 (the
/// 5ms jitter grace band would blur boundary cases the generator aims at)
/// and the executor's `#[cfg(test)]` virtual clock, so `run_sync` jumps to
/// exact timed boundaries instead of busy-waiting on the real clock.
fn run_bitmap_timed(net: &PetriNet, marking: Marking) -> RunResult {
    let initial_counts = marking.token_counts();
    let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(
        net,
        marking,
        ExecutorOptions {
            deadline_tolerance_ms: Some(0.0),
            ..ExecutorOptions::default()
        },
    );
    executor.enable_virtual_clock();
    let final_marking = executor.run_sync().into_owned();
    let result = RunResult {
        marking: final_marking,
        events: executor.event_store().events().to_vec(),
        quiescent: executor.is_quiescent(),
    };
    assert_token_conservation(&initial_counts, &result);
    result
}

/// [`PrecompiledRunner`] twin for the timed property; see
/// [`run_bitmap_timed`].
fn run_precompiled_timed(net: &PetriNet, marking: Marking) -> RunResult {
    let initial_counts = marking.token_counts();
    let prog = PrecompiledNet::from_compiled(CompiledNet::compile(net));
    let mut executor = PrecompiledNetExecutor::<InMemoryEventStore>::builder(&prog, marking)
        .event_store(InMemoryEventStore::new())
        .deadline_tolerance_ms(0.0)
        .build();
    executor.enable_virtual_clock();
    let final_marking = executor.run_sync().into_owned();
    let result = RunResult {
        marking: final_marking,
        events: executor.event_store().events().to_vec(),
        quiescent: executor.is_quiescent(),
    };
    assert_token_conservation(&initial_counts, &result);
    result
}

// ---------------------------------------------------------------------------
//  TIME-013 reap-asymmetry allowlist
// ---------------------------------------------------------------------------

/// Running count of allowlisted TIME-013 reap divergences, echoed per
/// occurrence so a run's log shows how often the known divergence was hit.
static REAP_DIVERGENCES_ALLOWLISTED: AtomicUsize = AtomicUsize::new(0);

/// The ONLY tolerated timed divergence: the TIME-013 reap asymmetry,
/// CONFIRMED and formally witnessed in Lean (`lean/Libpetri/TimedCycle.lean`,
/// `deadline_reap_dirty_diverges`). After a hard-deadline reap the
/// precompiled backend marks the transition dirty, so the next enablement
/// pass re-enables it with a fresh clock and it can fire again; the bitmap
/// backend leaves it clean, so in a quiet net it never fires again. Which
/// behaviour TIME-013 should mandate is a semantics decision deliberately
/// left open (plan phase 4); until then the harness must neither paper over
/// the asymmetry (weakening the oracle) nor fail on it (blocking the suite
/// on a known, documented, formally-modelled divergence).
///
/// The signature is detected structurally, not by net shape, and it is the
/// Lean witness read literally — nothing wider:
///
/// 1. the two projections share a common prefix whose **last**
///    `transition-timed-out` names some transition `r` (the most recent reap;
///    an older, unrelated reap must not license a divergence that opens
///    hundreds of events later), and
/// 2. the first differing position is `transition-enabled r` **in the
///    precompiled stream** — `pb_update_reenables`, the one-sided re-enable
///    that is the whole asymmetry. The bitmap stream differs there by
///    construction (`bb_never_fires_after_reap`).
///
/// The reverse direction, a different event kind on `r`, a different
/// transition, or a divergence that merely happens *after* a reap is a NEW
/// finding and fails the property with the full diff. The allowlist is also
/// scoped to the event projection alone: final marking and quiescence stay
/// asserted unconditionally at the call site, so a reap-shaped event
/// divergence that also moves tokens still fails.
///
/// Expected hit rate: ~zero under the random property. The virtual clock
/// advances `run_sync` to *exact* timed boundaries and only when a full
/// cycle fired nothing, and the advance is capped by every enabled hard
/// deadline via `millis_until_next_timed_transition` — so the executor is
/// never "blocked past a deadline" the way the Lean schedule
/// `[0, 10, 12, 15]` requires (a reap needs a stalled orchestrator, e.g. a
/// blocking sync action on the real clock). The detector is therefore
/// pinned by [`is_known_reap_divergence_matches_only_the_lean_signature`] on
/// synthetic projections and by the deterministic real-clock reproduction in
/// [`time013_reap_asymmetry_witness`], not by random traffic.
fn is_known_reap_divergence(bitmap: &[String], precompiled: &[String]) -> bool {
    let prefix = bitmap
        .iter()
        .zip(precompiled.iter())
        .take_while(|(a, b)| a == b)
        .count();
    if prefix == bitmap.len() && prefix == precompiled.len() {
        return false; // no divergence at all
    }
    let Some(reaped) = bitmap[..prefix]
        .iter()
        .rev()
        .find_map(|e| e.strip_prefix("transition-timed-out "))
    else {
        return false; // divergence not preceded by any reap
    };
    let reenable = format!("transition-enabled {reaped}");
    precompiled.get(prefix) == Some(&reenable)
}

/// Unit pin for [`is_known_reap_divergence`] over synthetic projections — no
/// clock, no executor. Without it the predicate has zero executed coverage:
/// the virtual clock lands exactly on timed boundaries so the random property
/// never reaps, and [`time013_reap_asymmetry_witness`] is `#[ignore]`d, so
/// rewriting the body to `|_, _| true` would silently turn the timed property
/// into a no-op.
#[test]
fn is_known_reap_divergence_matches_only_the_lean_signature() {
    let ev = |s: &str| s.to_string();
    let prefix = || {
        vec![
            ev("execution-started n"),
            ev("transition-enabled t_w"),
            ev("transition-timed-out t_w"),
        ]
    };

    // ACCEPT — the canonical signature: precompiled re-enables the transition
    // it just reaped, bitmap goes on to something else.
    let mut bb = prefix();
    bb.push(ev("transition-started t_keep"));
    let mut pb = prefix();
    pb.push(ev("transition-enabled t_w"));
    assert!(is_known_reap_divergence(&bb, &pb), "canonical signature");

    // ACCEPT — same shape with the bitmap run already finished at the reap.
    assert!(
        is_known_reap_divergence(&prefix(), &pb),
        "bitmap stream exhausted at the divergence point"
    );

    // REJECT — no divergence at all.
    assert!(
        !is_known_reap_divergence(&prefix(), &prefix()),
        "identical streams"
    );

    // REJECT — a divergence with no reap anywhere in the shared prefix.
    let bb_noreap = vec![ev("execution-started n"), ev("transition-started a")];
    let pb_noreap = vec![ev("execution-started n"), ev("transition-enabled t_w")];
    assert!(
        !is_known_reap_divergence(&bb_noreap, &pb_noreap),
        "no reap in prefix"
    );

    // REJECT — right transition, wrong event kind (a fire, not a re-enable).
    let mut pb_started = prefix();
    pb_started.push(ev("transition-started t_w"));
    assert!(!is_known_reap_divergence(&bb, &pb_started), "wrong event kind");

    // REJECT — a re-enable, but of a transition that was never reaped.
    let mut pb_other = prefix();
    pb_other.push(ev("transition-enabled t_other"));
    assert!(!is_known_reap_divergence(&bb, &pb_other), "unreaped transition");

    // REJECT — the asymmetry is directional: a bitmap-only re-enable is a new
    // finding, not the modelled precompiled-only one.
    assert!(!is_known_reap_divergence(&pb, &bb), "reversed direction");

    // REJECT — stale reap: `t_old` was reaped, then `t_w`, and the divergence
    // re-enables `t_old`. Only the most recent reap counts.
    let stale = || {
        vec![
            ev("transition-timed-out t_old"),
            ev("transition-started t_mid"),
            ev("transition-timed-out t_w"),
        ]
    };
    let mut bb_stale = stale();
    bb_stale.push(ev("transition-started t_keep"));
    let mut pb_stale = stale();
    pb_stale.push(ev("transition-enabled t_old"));
    assert!(!is_known_reap_divergence(&bb_stale, &pb_stale), "stale reap");

    // ACCEPT — the same prefix, re-enabling the most recent reap.
    let mut pb_recent = stale();
    pb_recent.push(ev("transition-enabled t_w"));
    assert!(is_known_reap_divergence(&bb_stale, &pb_recent), "most recent reap");

    // REJECT — precompiled exhausted at the divergence point.
    assert!(!is_known_reap_divergence(&bb, &prefix()), "precompiled exhausted");
}

// ---------------------------------------------------------------------------
//  The differential property
// ---------------------------------------------------------------------------

// Divergence #5 (fixed in 25209af): same-pass recheck visibility of produced
// tokens. The seed in proptest-regressions/differential_prop_tests.txt is
// retained as a regression pin — it replays before any novel case on every
// run. It is a pin on the harness, not on the semantics: widening the
// generated fragment re-keys the RNG stream, so the seed no longer rebuilds
// the net recorded in its comment. The semantics are pinned exactly, by hand,
// in [`backend_suite_tests`](crate::backend_suite_tests):
// `same_pass_refill_invisible_to_recheck` plus the `same_pass_deposit_*`
// trio (presence across an unrelated firing, cardinality, ν-join).
//
// Mechanism: the shared loop collects the cycle's ready list once, then
// rechecks each entry before firing (`executor_core/executor.rs`,
// `recheck_can_fire`). The recheck must judge a pass-start marking narrowed
// by what earlier firings CONSUMED and never widened by what their actions
// DEPOSITED (EXEC-001 step order, EXEC-003 AC3/AC4). The precompiled backend
// used to recheck the live `marking_bitmap`/`token_counts`, which already
// include tokens deposited by earlier same-pass firings; both backends then
// re-published those deposits anyway by refreshing the whole snapshot after
// every consumption. When an earlier firing drains a place a later ready
// transition depends on and refills it via its own output, the backends
// disagreed on whether the later transition may still fire this pass — an
// EXEC-002 AC4 violation (backends MUST produce the identical ready order).
//
// Minimal hand-verified witness (public API only, no harness code):
//   a: 3 tokens, b: 1 token
//   t_low  (priority 0): input one(a), read(b), passthrough
//   t_high (priority 1): input one(a), reset(b), output -> b (echo)
// both backends fire [t_high, t_high, t_high]  (t_low starved: its recheck
//                   sees b empty in the snapshot, so it is disabled and
//                   loses the next cycle's priority sort again)
// the pre-fix precompiled backend fired [t_high, t_low, t_high]  (its live
//                   recheck saw t_high's refill of b and fired mid-pass)
// Final markings happen to agree here; with an inhibitor dependency instead
// of a read the same window can diverge markings, not just order.

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 128,
        ..ProptestConfig::default()
    })]

    /// For every generated untimed net + marking, `BitmapNetExecutor` and
    /// `PrecompiledNetExecutor` must be observationally equal: same final
    /// marking (token values per place, FIFO order), same quiescence, same
    /// event sequence modulo timestamps. Token conservation is re-checked
    /// per backend inside each runner.
    #[test]
    fn backends_agree_on_untimed_nets(g in gen_net()) {
        let (net, marking) = build_net(&g);
        let bitmap = BitmapRunner::run(&net, marking.clone());
        let precompiled = PrecompiledRunner::run(&net, marking);

        prop_assert_eq!(
            marking_values(&g, &bitmap.marking),
            marking_values(&g, &precompiled.marking),
            "final markings diverged (token values per place, FIFO order)"
        );
        prop_assert_eq!(
            bitmap.quiescent,
            precompiled.quiescent,
            "quiescence diverged"
        );
        prop_assert_eq!(
            project_events(&bitmap.events),
            project_events(&precompiled.events),
            "event-sequence projections diverged"
        );
    }

    /// Timed twin of [`backends_agree_on_untimed_nets`]: same oracle
    /// (final marking values, quiescence, timestamp-free event projection —
    /// which already covers `transition-timed-out` and
    /// `transition-clock-restarted` by name and order), timing drawn from
    /// {immediate, delayed, window, deadline, exact}, both backends driven
    /// through `run_sync` on the virtual clock with deadline tolerance 0.
    /// The single allowlisted divergence is the TIME-013 reap asymmetry
    /// ([`is_known_reap_divergence`]), and it is allowlisted for the event
    /// projection ONLY — marking and quiescence are asserted first and
    /// unconditionally. Anything else fails with the full diff.
    #[test]
    fn backends_agree_on_timed_nets(g in gen_timed_net()) {
        let (net, marking) = build_net(&g);
        let bitmap = run_bitmap_timed(&net, marking.clone());
        let precompiled = run_precompiled_timed(&net, marking);

        let bitmap_proj = project_events(&bitmap.events);
        let precompiled_proj = project_events(&precompiled.events);

        // Marking and quiescence are asserted unconditionally: the TIME-013
        // allowlist covers the event projection ONLY. A reap-shaped event
        // divergence that also moves tokens or changes quiescence is a
        // different, unmodelled thing and must fail here.
        prop_assert_eq!(
            marking_values(&g, &bitmap.marking),
            marking_values(&g, &precompiled.marking),
            "final markings diverged (token values per place, FIFO order)"
        );
        prop_assert_eq!(
            bitmap.quiescent,
            precompiled.quiescent,
            "quiescence diverged"
        );

        if bitmap_proj != precompiled_proj
            && is_known_reap_divergence(&bitmap_proj, &precompiled_proj)
        {
            let n = REAP_DIVERGENCES_ALLOWLISTED.fetch_add(1, Ordering::Relaxed) + 1;
            eprintln!(
                "[differential] allowlisted known divergence #{n}: TIME-013 reap \
                 asymmetry (lean/Libpetri/TimedCycle.lean `deadline_reap_dirty_diverges`; \
                 semantics decision pending, plan phase 4)"
            );
            return Ok(());
        }

        prop_assert_eq!(
            bitmap_proj,
            precompiled_proj,
            "event-sequence projections diverged"
        );
    }
}

// ---------------------------------------------------------------------------
//  TIME-013 reap-asymmetry witness (known divergence, real clock)
// ---------------------------------------------------------------------------

/// Deterministic executable twin of the Lean witness
/// (`lean/Libpetri/TimedCycle.lean`, `deadline_reap_dirty_diverges`) and the
/// pin for [`is_known_reap_divergence`]. `#[ignore]`d because it documents a
/// KNOWN divergence — it stays out of the suite until plan phase 4 decides
/// which behaviour TIME-013 mandates — and because it needs the real clock
/// (a `thread::sleep` inside a sync action stalls the single-threaded
/// orchestrator past the deadline; the virtual clock cannot express that,
/// which is precisely why the random property never reaps). Run it with
/// `cargo test -p libpetri-runtime time013 -- --ignored`.
///
/// Shape (the Lean schedule `[0, 10, 12, 15]` made concrete):
/// - `t_block` fires instantly and sleeps 400ms — the blocked gap;
/// - `t_w` `window(50, 120)` never opens before the stall ends, so both
///   backends reap it at ~400ms (`transition-timed-out t_w`);
/// - `t_keep` `delayed(1200)` keeps the loop alive past the reap: `run_sync`
///   exits at `enabled_count == 0` right after `enforce_deadlines`, so
///   without a still-enabled bystander BOTH backends would terminate at the
///   reap and the dirty-bit asymmetry would stay invisible. The delay is set
///   far beyond the ~450ms re-fire so a loaded CI runner cannot turn the
///   ordering into a race.
///
/// After the reap the precompiled backend re-enables `t_w` (fresh clock) and
/// fires it at ~450ms; the bitmap backend never re-examines it. Final
/// markings diverge: bitmap keeps the `p_window` token, precompiled consumes
/// it.
#[test]
#[ignore = "documents the known TIME-013 reap divergence (lean/Libpetri/TimedCycle.lean \
            `deadline_reap_dirty_diverges`; semantics decision pending, plan phase 4); \
            real clock + thread::sleep, ~2.5s. CI runs it explicitly with --ignored \
            (.github/workflows/ci.yml, rust job) — it is the only executed check on \
            the real executor that `is_known_reap_divergence` still matches."]
fn time013_reap_asymmetry_witness() {
    let pb = Place::<i32>::new("p_block");
    let pw = Place::<i32>::new("p_window");
    let pk = Place::<i32>::new("p_keep");

    let t_block = Transition::builder("t_block")
        .input(one(&pb))
        .action(sync_action(|_ctx| {
            std::thread::sleep(std::time::Duration::from_millis(400));
            Ok(())
        }))
        .build();
    let t_w = Transition::builder("t_w")
        .input(one(&pw))
        .timing(window(50, 120))
        .action(passthrough())
        .build();
    let t_keep = Transition::builder("t_keep")
        .input(one(&pk))
        .timing(delayed(1200))
        .action(passthrough())
        .build();

    let net = PetriNet::builder("reap-witness")
        .transitions([t_block, t_w, t_keep])
        .build();
    let mut marking = Marking::new();
    marking.add(&pb, Token::at(0, 0));
    marking.add(&pw, Token::at(0, 0));
    marking.add(&pk, Token::at(0, 0));

    // Real clock (no `enable_virtual_clock`), strict deadlines — the same
    // tolerance the timed property uses.
    let (bitmap_proj, bitmap_window_tokens) = {
        let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(
            &net,
            marking.clone(),
            ExecutorOptions {
                deadline_tolerance_ms: Some(0.0),
                ..ExecutorOptions::default()
            },
        );
        let final_marking = executor.run_sync().into_owned();
        (
            project_events(executor.event_store().events()),
            final_marking.count("p_window"),
        )
    };
    let (precompiled_proj, precompiled_window_tokens) = {
        let prog = PrecompiledNet::from_compiled(CompiledNet::compile(&net));
        let mut executor = PrecompiledNetExecutor::<InMemoryEventStore>::builder(&prog, marking)
            .event_store(InMemoryEventStore::new())
            .deadline_tolerance_ms(0.0)
            .build();
        let final_marking = executor.run_sync().into_owned();
        (
            project_events(executor.event_store().events()),
            final_marking.count("p_window"),
        )
    };

    let timed_out = "transition-timed-out t_w".to_string();
    assert!(bitmap_proj.contains(&timed_out), "bitmap must reap t_w");
    assert!(precompiled_proj.contains(&timed_out), "precompiled must reap t_w");
    assert!(
        !bitmap_proj.iter().any(|e| e == "transition-started t_w"),
        "bitmap never fires the reaped t_w (bb_never_fires_after_reap)"
    );
    assert!(
        precompiled_proj.iter().any(|e| e == "transition-started t_w"),
        "precompiled re-enables and fires the reaped t_w (pb_update_reenables)"
    );
    assert_eq!(bitmap_window_tokens, 1, "bitmap keeps the p_window token");
    assert_eq!(precompiled_window_tokens, 0, "precompiled consumes it");
    assert_ne!(bitmap_proj, precompiled_proj, "the projections must diverge");
    assert!(
        is_known_reap_divergence(&bitmap_proj, &precompiled_proj),
        "the allowlist detector must match the canonical reap signature"
    );
}
