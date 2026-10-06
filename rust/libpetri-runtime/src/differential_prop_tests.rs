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
//! A third pair of properties ([`backends_agree_on_word_boundary_untimed_nets`]
//! and its timed twin) runs the same oracle over WORD-BOUNDARY nets: 65-72
//! places, with input / read / inhibitor indices biased hard onto place ids 31
//! and 63 and their neighbours (30/32/62/64). The 2-8 place fragment can never
//! reach place id 31, so an entire class of word-boundary arithmetic bugs was
//! invisible to it. The escape that motivated this was in the TypeScript twin —
//! `PrecompiledNet.canEnableSparse` compared a SIGNED `snapshot[w] & m` against
//! an unsigned `m`, so every transition whose needs mask held id 31/63/95/...
//! was permanently un-enabled on the precompiled backend while the bitmap
//! backend ran the same net correctly (fixed in b3e97a9). Rust packs the
//! snapshot into `u64` words and ANDs them unsigned, so it never had that bug —
//! the mirror is kept here because the two harnesses are meant to generate the
//! same fragment, because it would catch the bug if the Rust bitmap ever
//! narrowed its word type, and because 65+ place nets exercise multi-word masks
//! and wide reverse indexes that the small fragment cannot reach at all.
//!
//! ID PIN: "place id 31" is a COMPILED id, not a generator index, so the
//! boundary generator is worthless unless the two coincide. `CompiledNet`
//! assigns ids by SORTED PLACE NAME, so [`build_net`] zero-pads every name to a
//! fixed per-net width (`p00`..`p71` at 65+ places) and lexicographic order
//! becomes numeric order. Width is 1 for the 2-8 place fragment, so those nets
//! keep exactly the names they always had. The TypeScript twin needs a
//! different device for the same guarantee — its ids follow first-reference
//! order across transitions, so it prepends a dead anchor transition instead —
//! and [`word_boundary_generator_pins_ids_and_reaches_sign_bit_transitions`]
//! asserts the pin here rather than assuming it.
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
//! bounded regardless of timing. The word-boundary generator obeys the same
//! discipline unchanged — only the place-index POOL differs. The virtual clock
//! guarantees the harness *reaches* those firings without wall-clock waiting: a
//! cycle that fires nothing jumps time to the next `earliest`/deadline
//! boundary, where either something fires or the enabled set shrinks.

#![cfg(test)]

use std::collections::BTreeMap;
use std::sync::Arc;

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
//  Word-boundary generator (32-/64-bit sign-bit coverage)
// ---------------------------------------------------------------------------

/// Place ids 31 and 63: bit 31 of marking-snapshot words 0 and 1 when the
/// snapshot is packed into 32-bit words, i.e. the exact positions where a
/// signed/unsigned mix-up in the enablement AND flips "enabled" to "never
/// enabled" (see the module docs). Rust uses `u64` words and unsigned ANDs, so
/// these are ordinary bits here — the pool mirrors the TypeScript twin.
const SIGN_BIT_INDICES: [usize; 2] = [31, 63];

/// Sign bits plus their immediate neighbours — the full boundary pool.
const BOUNDARY_INDICES: [usize; 6] = [30, 31, 32, 62, 63, 64];

fn sign_bit_pool(place_count: usize) -> Vec<usize> {
    SIGN_BIT_INDICES
        .iter()
        .copied()
        .filter(|&i| i < place_count)
        .collect()
}

fn boundary_pool(place_count: usize) -> Vec<usize> {
    BOUNDARY_INDICES
        .iter()
        .copied()
        .filter(|&i| i < place_count)
        .collect()
}

/// True iff the transition's NEEDS mask (inputs + reads) contains a sign bit.
fn touches_sign_bit(t: &GenTrans) -> bool {
    t.inputs.iter().any(|&(p, _)| SIGN_BIT_INDICES.contains(&p))
        || t.reads.iter().any(|p| SIGN_BIT_INDICES.contains(p))
}

/// Boundary twin of [`gen_transition`]. Deliberately a near-copy rather than a
/// parameterisation of the original: [`gen_transition`] must keep its exact RNG
/// stream so the committed regression seed replays (see the note above
/// [`backends_agree_on_untimed_nets`]), and folding a pool draw into it would
/// re-key that stream.
///
/// The one structural difference is that every place-index draw feeding the
/// NEEDS mask — inputs, reads, inhibitor — comes from a small biased POOL
/// instead of the full place range. Bias is the whole point: drawn uniformly
/// over 65+ places a needs mask lands on id 31 about once in 30 draws, so
/// merely making the net wide would leave the boundary about as uncovered as it
/// is at 8 places.
///
/// - `first` (the net's `t0`) always draws from the sign-bit pool `[31, 63]`,
///   so EVERY generated net structurally contains a transition whose needs mask
///   holds a sign bit — a per-case guarantee, not a lucky draw;
/// - the remaining transitions draw their pool 2:2:1 from sign bits / boundary
///   neighbours / the full range, so surrounding traffic still varies and masks
///   land both inside one word and spanning two.
///
/// Reset arcs keep drawing uniformly over all places: resets never enter the
/// needs mask, and pooling them would just drain the boundary places the
/// property is trying to keep enabled. An inhibitor landing on one of this
/// transition's own input places is dropped for the same reason — the pool is
/// small, so self-inhibiting (permanently dead) transitions would otherwise be
/// common enough to eat the coverage.
fn gen_boundary_transition(place_count: usize, first: bool) -> impl Strategy<Value = GenTrans> {
    let pool: BoxedStrategy<Vec<usize>> = if first {
        Just(sign_bit_pool(place_count)).boxed()
    } else {
        prop_oneof![
            2 => Just(sign_bit_pool(place_count)),
            2 => Just(boundary_pool(place_count)),
            1 => Just((0..place_count).collect::<Vec<usize>>()),
        ]
        .boxed()
    };
    pool.prop_flat_map(move |pool| {
        let max_inputs = pool.len().min(3);
        let max_reads = pool.len().min(2);
        (
            prop::sample::subsequence(pool.clone(), 1..=max_inputs),
            prop::collection::vec(gen_card(), max_inputs),
            // Output shape selector, as in gen_transition.
            0u8..8,
            any::<prop::sample::Index>(),
            any::<prop::sample::Index>(),
            prop::sample::subsequence(pool.clone(), 0..=max_reads),
            prop::option::of(prop::sample::select(pool)),
            prop::option::of(0..place_count),
            0i32..=2,
        )
            .prop_map(
                move |(ins, cards, out_kind, o1, o2, reads, inhibitor, reset, priority)| {
                    let inputs: Vec<(usize, GenCard)> =
                        ins.iter().copied().zip(cards).collect();
                    // DAG discipline, unchanged: outputs live strictly above
                    // the highest input index.
                    let lo = ins.last().copied().unwrap() + 1;
                    let avail = place_count - lo;
                    let output = if avail == 0 || out_kind == 0 {
                        GenOut::None
                    } else {
                        let first_out = lo + o1.index(avail);
                        match out_kind {
                            1..=3 => GenOut::Single(first_out),
                            _ if avail < 2 => GenOut::Single(first_out),
                            k => {
                                let second =
                                    lo + (first_out - lo + 1 + o2.index(avail - 1)) % avail;
                                if k <= 5 {
                                    GenOut::And(first_out, second)
                                } else {
                                    GenOut::Xor(first_out, second)
                                }
                            }
                        }
                    };
                    // Drop a self-inhibition: it would make the transition
                    // permanently dead and cost a boundary sample.
                    let inhibitor = inhibitor.filter(|i| !ins.contains(i));
                    GenTrans {
                        inputs,
                        output,
                        reads,
                        inhibitor,
                        reset,
                        priority,
                        timing: GenTiming::Immediate,
                    }
                },
            )
    })
}

/// [`gen_boundary_transition`] plus a drawn timing, layered exactly as
/// [`gen_timed_transition`] is.
fn gen_boundary_timed_transition(
    place_count: usize,
    first: bool,
) -> impl Strategy<Value = GenTrans> {
    (gen_boundary_transition(place_count, first), gen_timing()).prop_map(|(mut t, timing)| {
        t.timing = timing;
        t
    })
}

/// 65-72 places, so ids 30/31/32 and 62/63/64 all exist and the marking
/// snapshot spans two `u64` words here (three 32-bit words in the TypeScript
/// twin, where words 0 and 1 are full and therefore both carry a sign bit).
/// `t0` is the forced sign-bit transition; up to five more follow.
///
/// Initial tokens are 0-2 per place rather than the small fragment's 0-6: these
/// nets carry nine times the places, and run cost tracks the total token count.
fn gen_boundary_net() -> impl Strategy<Value = GenNet> {
    (65usize..=72).prop_flat_map(|place_count| {
        (
            prop::collection::vec(prop::collection::vec(0i32..10, 0..=2), place_count),
            gen_boundary_transition(place_count, true),
            prop::collection::vec(gen_boundary_transition(place_count, false), 0..=5),
        )
            .prop_map(move |(initial, head, rest)| {
                let mut transitions = vec![head];
                transitions.extend(rest);
                GenNet {
                    place_count,
                    initial,
                    transitions,
                }
            })
    })
}

/// [`gen_boundary_net`] with timed transitions.
fn gen_boundary_timed_net() -> impl Strategy<Value = GenNet> {
    (65usize..=72).prop_flat_map(|place_count| {
        (
            prop::collection::vec(prop::collection::vec(0i32..10, 0..=2), place_count),
            gen_boundary_timed_transition(place_count, true),
            prop::collection::vec(gen_boundary_timed_transition(place_count, false), 0..=5),
        )
            .prop_map(move |(initial, head, rest)| {
                let mut transitions = vec![head];
                transitions.extend(rest);
                GenNet {
                    place_count,
                    initial,
                    transitions,
                }
            })
    })
}

// ---------------------------------------------------------------------------
//  GenNet -> (PetriNet, Marking)
// ---------------------------------------------------------------------------

/// Number of decimal digits in the highest place index of a net.
fn name_width(place_count: usize) -> usize {
    (place_count - 1).to_string().len()
}

/// Zero-padded place name. `CompiledNet` assigns place ids by SORTED NAME, so
/// padding to a fixed per-net width makes lexicographic order numeric order and
/// pins `id(pI) == I` — the tie the word-boundary generator depends on (see the
/// module docs). Width is 1 for the 2-8 place fragment, so those nets keep
/// exactly the names they always had.
fn place_name(i: usize, width: usize) -> String {
    format!("p{i:0width$}")
}

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
    let width = name_width(g.place_count);
    let places: Vec<Place<i32>> = (0..g.place_count)
        .map(|i| Place::new(place_name(i, width)))
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
    let width = name_width(g.place_count);
    (0..g.place_count)
        .map(|i| {
            let name = place_name(i, width);
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
    /// Any divergence fails with the full diff, a TIME-013 reap included: a
    /// reaped transition stays disabled on both backends until an input
    /// place changes (see [`time013_reap_is_not_rearmed_on_either_backend`]).
    #[test]
    fn backends_agree_on_timed_nets(g in gen_timed_net()) {
        let (net, marking) = build_net(&g);
        let bitmap = run_bitmap_timed(&net, marking.clone());
        let precompiled = run_precompiled_timed(&net, marking);

        let bitmap_proj = project_events(&bitmap.events);
        let precompiled_proj = project_events(&precompiled.events);

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
            bitmap_proj,
            precompiled_proj,
            "event-sequence projections diverged"
        );
    }
}

proptest! {
    // Half the small fragment's case count: each case builds a 65-72 place net,
    // and the coverage guard below is what certifies the cases are actually
    // spent on sign-bit transitions rather than merely on wide nets.
    #![proptest_config(ProptestConfig {
        cases: 64,
        ..ProptestConfig::default()
    })]

    /// Word-boundary twin of [`backends_agree_on_untimed_nets`]: identical
    /// oracle, nets drawn from [`gen_boundary_net`] so every case carries a
    /// transition whose needs mask holds place id 31 or 63.
    #[test]
    fn backends_agree_on_word_boundary_untimed_nets(g in gen_boundary_net()) {
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

    /// Word-boundary twin of [`backends_agree_on_timed_nets`], with the same
    /// oracle.
    #[test]
    fn backends_agree_on_word_boundary_timed_nets(g in gen_boundary_timed_net()) {
        let (net, marking) = build_net(&g);
        let bitmap = run_bitmap_timed(&net, marking.clone());
        let precompiled = run_precompiled_timed(&net, marking);

        let bitmap_proj = project_events(&bitmap.events);
        let precompiled_proj = project_events(&precompiled.events);

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
            bitmap_proj,
            precompiled_proj,
            "event-sequence projections diverged"
        );
    }
}

// ---------------------------------------------------------------------------
//  Word-boundary coverage guard
// ---------------------------------------------------------------------------

/// The boundary properties are only worth their runtime while the generator
/// keeps aiming at the sign bits, and nothing in a green differential run says
/// that it does — a generator that silently drifted back to uniform draws would
/// still pass. This test measures the bias on a DETERMINISTIC runner (so the
/// thresholds cannot flake) and asserts three things:
///
/// 1. the zero-padded naming really pins compiled place id == generator index.
///    Without it "place id 31" would be whichever name sorts 32nd, and the
///    boundary pool would aim at the wrong places entirely;
/// 2. every generated net structurally holds a transition whose needs mask
///    contains id 31 or 63 — guaranteed by `t0`'s sign-bit pool;
/// 3. a healthy fraction of nets actually FIRE such a transition on the
///    reference backend, i.e. the sign-bit transitions are reachable and not
///    merely declared. The rest simply drew no initial token into the sign-bit
///    place. Measured on this deterministic runner: structural 40/40, fired
///    20/40. The floor (30%) is loose on purpose so ordinary generator tuning
///    does not trip it — over a 64-case property run a 50% per-net rate makes
///    sign-bit firing a certainty.
#[test]
fn word_boundary_generator_pins_ids_and_reaches_sign_bit_transitions() {
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;

    let mut runner = TestRunner::deterministic();
    let strategy = gen_boundary_net();
    let samples = 40usize;
    let mut structural = 0usize;
    let mut fired = 0usize;

    for _ in 0..samples {
        let g = strategy
            .new_tree(&mut runner)
            .expect("boundary strategy must produce a value")
            .current();
        let width = name_width(g.place_count);

        let sign_bit_transitions: Vec<String> = g
            .transitions
            .iter()
            .enumerate()
            .filter(|(_, t)| touches_sign_bit(t))
            .map(|(ti, _)| format!("transition-started t{ti}"))
            .collect();
        if !sign_bit_transitions.is_empty() {
            structural += 1;
        }

        let (net, marking) = build_net(&g);
        let compiled = CompiledNet::compile(&net);
        assert_eq!(compiled.place_count, g.place_count);
        for i in 0..g.place_count {
            assert_eq!(
                compiled.place_id(&place_name(i, width)),
                Some(i),
                "place id pin broke at index {i}"
            );
        }

        let run = BitmapRunner::run(&net, marking);
        let proj = project_events(&run.events);
        if proj.iter().any(|e| sign_bit_transitions.contains(e)) {
            fired += 1;
        }
    }

    assert_eq!(
        structural, samples,
        "every boundary net must hold a sign-bit transition"
    );
    assert!(
        fired * 10 >= samples * 3,
        "sign-bit transitions must actually fire: only {fired}/{samples} nets did"
    );
}

// ---------------------------------------------------------------------------
//  TIME-013 reaping: no re-arm on either backend
// ---------------------------------------------------------------------------

/// The reaping net of the Lean witness (`lean/Libpetri/TimedCycle.lean`, the
/// schedule `[0, 10, 12, 15]` made concrete):
/// - `t_block` fires at once and its sync action stalls the single-threaded
///   orchestrator for 400ms, through `stall` (a real sleep, or an advance of a
///   manual clock);
/// - `t_w` `window(50, 120)` never opens before the stall ends, so it is reaped
///   at ~400ms (`transition-timed-out t_w`);
/// - `t_keep` `delayed(1200)` keeps the loop alive past the reap: `run_sync`
///   exits at `enabled_count == 0` right after `enforce_deadlines`, so without a
///   still-enabled bystander a re-armed `t_w` would stay invisible.
fn reap_witness_net(stall: impl Fn() + Send + Sync + 'static) -> (PetriNet, Marking) {
    let pb = Place::<i32>::new("p_block");
    let pw = Place::<i32>::new("p_window");
    let pk = Place::<i32>::new("p_keep");
    let t_block = Transition::builder("t_block")
        .input(one(&pb))
        .action(sync_action(move |_ctx| {
            stall();
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
    (net, marking)
}

/// Runs the reap witness on both backends, strict deadlines, each on the clock
/// `clock` builds (`None`: the real clock), and asserts TIME-013's no-re-arm on
/// both: `t_w` is reaped, never fires afterwards, and keeps its `p_window` token,
/// and the two event projections are identical.
fn assert_reap_witness_agrees(
    net_for: impl Fn() -> (PetriNet, Marking),
    clock: impl Fn() -> Option<Arc<dyn crate::clock::ExecutorClock>>,
) {
    let (bitmap_proj, bitmap_window_tokens) = {
        let (net, marking) = net_for();
        let mut options = ExecutorOptions::default().deadline_tolerance_ms(0.0);
        if let Some(clock) = clock() {
            options = options.clock(clock);
        }
        let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(&net, marking, options);
        let final_marking = executor.run_sync().into_owned();
        (project_events(executor.event_store().events()), final_marking.count("p_window"))
    };
    let (precompiled_proj, precompiled_window_tokens) = {
        let (net, marking) = net_for();
        let prog = PrecompiledNet::from_compiled(CompiledNet::compile(&net));
        let mut builder = PrecompiledNetExecutor::<InMemoryEventStore>::builder(&prog, marking)
            .event_store(InMemoryEventStore::new())
            .deadline_tolerance_ms(0.0);
        if let Some(clock) = clock() {
            builder = builder.clock(clock);
        }
        let mut executor = builder.build();
        let final_marking = executor.run_sync().into_owned();
        (project_events(executor.event_store().events()), final_marking.count("p_window"))
    };

    let timed_out = "transition-timed-out t_w".to_string();
    for (backend, proj, window_tokens) in [
        ("bitmap", &bitmap_proj, bitmap_window_tokens),
        ("precompiled", &precompiled_proj, precompiled_window_tokens),
    ] {
        assert!(proj.contains(&timed_out), "{backend} must reap t_w: {proj:?}");
        assert!(
            !proj.iter().any(|e| e == "transition-started t_w"),
            "{backend} must not fire the reaped t_w (TIME-013, no re-arm): {proj:?}"
        );
        assert_eq!(window_tokens, 1, "{backend} keeps the p_window token");
    }
    assert_eq!(bitmap_proj, precompiled_proj, "the event projections must agree");
}

/// TIME-013, on the virtual clock: the stall is an advance of the executor's
/// manual clock from inside `t_block`'s action, so the reap is deterministic
/// and costs no real time. Before the fix the precompiled backend marked the
/// reaped `t_w` dirty, re-enabled it on a fresh clock and fired it at ~450ms.
#[test]
fn time013_reap_is_not_rearmed_on_either_backend() {
    use crate::clock::ManualClock;
    use std::sync::Mutex;
    // One manual clock per run; the action reaches the current one.
    let current: Arc<Mutex<Option<Arc<ManualClock>>>> = Arc::new(Mutex::new(None));
    let net_for = {
        let current = Arc::clone(&current);
        move || {
            let current = Arc::clone(&current);
            reap_witness_net(move || {
                let clock = current.lock().unwrap().clone().expect("a manual clock is installed");
                clock.advance_ms(400.0);
            })
        }
    };
    let clock = {
        let current = Arc::clone(&current);
        move || {
            let clock = Arc::new(ManualClock::new());
            *current.lock().unwrap() = Some(Arc::clone(&clock));
            Some(clock as Arc<dyn crate::clock::ExecutorClock>)
        }
    };
    assert_reap_witness_agrees(net_for, clock);
}

/// TIME-013, on a host-stepped clock: the stall is still an advance from
/// inside `t_block`'s action, but nothing moves time after that except a host
/// thread. It waits for the executor to park, advances 100ms, and repeats
/// until the executor is dropped, so `t_keep` fires only because the host
/// stepped to 1200. The host never advances while the executor is running,
/// so the reap at 400 sees the same marking as on the manual clock.
#[test]
fn time013_reap_is_not_rearmed_on_a_stepped_clock() {
    use crate::clock::SteppedClock;
    use std::sync::{Mutex, Weak};
    use std::time::Duration;
    // The action reaches the current run's clock. Weak, so the host thread
    // can tell when the executor holding the clock is gone.
    let current: Arc<Mutex<Weak<SteppedClock>>> = Arc::new(Mutex::new(Weak::new()));
    let net_for = {
        let current = Arc::clone(&current);
        move || {
            let current = Arc::clone(&current);
            reap_witness_net(move || {
                let clock = current.lock().unwrap().upgrade().expect("a stepped clock is installed");
                clock.advance_ms(400.0);
            })
        }
    };
    let clock = {
        let current = Arc::clone(&current);
        move || {
            let clock = Arc::new(SteppedClock::new());
            *current.lock().unwrap() = Arc::downgrade(&clock);
            let host = Arc::downgrade(&clock);
            std::thread::spawn(move || {
                let step = Some(Duration::from_millis(50));
                while let Some(clock) = host.upgrade() {
                    if clock.settle(step) {
                        clock.settle_after(|| clock.advance_ms(100.0), step);
                    }
                }
            });
            Some(clock as Arc<dyn crate::clock::ExecutorClock>)
        }
    };
    assert_reap_witness_agrees(net_for, clock);
}

/// TIME-013, on the real clock: the same witness, with a real 400ms sleep
/// stalling the orchestrator. The executed check on the real executor path
/// (about 1.3s per backend).
#[test]
fn time013_reap_witness_backends_agree() {
    let net_for = || reap_witness_net(|| std::thread::sleep(std::time::Duration::from_millis(400)));
    assert_reap_witness_agrees(net_for, || None);
}

/// TIME-013, the other half: a reaped transition is enabled again once a token on
/// one of its input places changes. `t_feed` `delayed(600)` deposits a second
/// token into `p_window` after the reap at 400ms, so `t_w` re-enables on a fresh
/// clock and fires, once per token, only after the feed, on both backends alike
/// (virtual clock).
#[test]
fn time013_reaped_transition_rearms_when_an_input_changes() {
    use crate::clock::{ExecutorClock, ManualClock};
    let pb = Place::<i32>::new("p_block");
    let pw = Place::<i32>::new("p_window");
    let pf = Place::<i32>::new("p_feed");
    let run = |precompiled: bool| {
        let clock = Arc::new(ManualClock::new());
        let stall = Arc::clone(&clock);
        let t_block = Transition::builder("t_block")
            .input(one(&pb))
            .action(sync_action(move |_ctx| {
                stall.advance_ms(400.0);
                Ok(())
            }))
            .build();
        let t_w = Transition::builder("t_w")
            .input(one(&pw))
            .timing(window(50, 120))
            .action(passthrough())
            .build();
        let t_feed = Transition::builder("t_feed")
            .input(one(&pf))
            .output(out_place(&pw))
            .timing(delayed(600))
            .action(sync_action(|ctx| {
                ctx.output("p_window", 7i32)?;
                Ok(())
            }))
            .build();
        let net = PetriNet::builder("reap-rearm").transitions([t_block, t_w, t_feed]).build();
        let mut marking = Marking::new();
        marking.add(&pb, Token::at(0, 0));
        marking.add(&pw, Token::at(0, 0));
        marking.add(&pf, Token::at(0, 0));
        let clock: Arc<dyn ExecutorClock> = clock;
        if precompiled {
            let prog = PrecompiledNet::from_compiled(CompiledNet::compile(&net));
            let mut executor = PrecompiledNetExecutor::<InMemoryEventStore>::builder(&prog, marking)
                .event_store(InMemoryEventStore::new())
                .deadline_tolerance_ms(0.0)
                .clock(clock)
                .build();
            let final_marking = executor.run_sync().into_owned();
            (project_events(executor.event_store().events()), final_marking.count("p_window"))
        } else {
            let options = ExecutorOptions::default().deadline_tolerance_ms(0.0).clock(clock);
            let mut executor = BitmapNetExecutor::<InMemoryEventStore>::new(&net, marking, options);
            let final_marking = executor.run_sync().into_owned();
            (project_events(executor.event_store().events()), final_marking.count("p_window"))
        }
    };
    let (bitmap_proj, bitmap_window) = run(false);
    let (precompiled_proj, precompiled_window) = run(true);
    for (backend, proj, window_tokens) in
        [("bitmap", &bitmap_proj, bitmap_window), ("precompiled", &precompiled_proj, precompiled_window)]
    {
        let reaped = proj.iter().position(|e| e == "transition-timed-out t_w").expect("t_w is reaped");
        let fed = proj.iter().position(|e| e == "transition-completed t_feed").expect("t_feed fires");
        let started: Vec<usize> =
            proj.iter().enumerate().filter(|(_, e)| *e == "transition-started t_w").map(|(i, _)| i).collect();
        assert_eq!(started.len(), 2, "{backend}: t_w fires once per token, after the feed: {proj:?}");
        assert!(reaped < fed && fed < started[0], "{backend}: t_w fires only after the feed: {proj:?}");
        assert_eq!(window_tokens, 0, "{backend}: both p_window tokens are consumed");
    }
    assert_eq!(bitmap_proj, precompiled_proj, "the event projections must agree");
}
