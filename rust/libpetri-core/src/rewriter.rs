//! Crate-internal structural rewrite primitive used by
//! [`crate::subnet_def::SubnetDef::instantiate`] and (in later tasks)
//! [`crate::petri_net::PetriNetBuilder`]'s `compose(...)` per
//! `spec/11-modular-composition.md` requirement **MOD-020**.
//!
//! The rewrite is purely structural: every place reference in every arc is
//! replaced according to a supplied `HashMap<Arc<str>, PlaceRef>` (the
//! "remap"), keyed by the **original** place name. The string-content keying
//! mirrors the existing place-identity convention used in
//! `compiled_net.rs` (`HashMap<Arc<str>, usize>`). Every transition is rebuilt
//! with rewritten arcs, preserving timing, priority, and action by reference
//! per **MOD-030**.
//!
//! # Design — one engine, multiple callers
//!
//! [`rename_net`] is the rename pass: it allocates fresh prefixed places,
//! records the old-to-new mapping in caller-supplied `HashMap`s (so callers
//! can build port/channel handle maps), and returns a renamed `PetriNet`. The
//! arc-rewrite helpers ([`rewrite_in`], [`rewrite_out`], [`rewrite_inhibitor`],
//! [`rewrite_read`], [`rewrite_reset`]) are factored out so the future
//! `compose(...)` caller (task #20) can substitute port-place mappings against
//! an arbitrary remap without renaming everything, via [`substitute_places`].
//!
//! # Performance
//!
//! - Actions ([`crate::action::BoxedAction`] = `Arc<dyn TransitionAction>`)
//!   carry through by `Arc::clone` — atomic refcount only, no allocation.
//! - New `Arc<str>` allocation only for renamed names (one per place + one
//!   per transition, plus the new net name).
//! - `Out::And` / `Out::Xor` children are walked with explicit
//!   `Vec::with_capacity(n)` + indexed `for` loops (no `Iterator::map`
//!   collect), mirroring the perf reasoning in the Java/TS counterparts.

use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;

use crate::action::{ActionError, BoxedAction, TransitionAction, is_passthrough};
use crate::arc::{Inhibitor, Read, Reset};
use crate::context::TransitionContext;
use crate::input::In;
use crate::match_spec::{MatchKey, MatchSpec};
use crate::output::Out;
use crate::petri_net::PetriNet;
use crate::place::PlaceRef;
use crate::timing::Timing;
use crate::transition::Transition;

// ============================================================
//  Public entry points
// ============================================================

/// Renames every place and transition of `body`, prefixing each name with
/// `prefix + "/"`.
///
/// **Side effects**: fills the two supplied maps so the caller can resolve
/// original-place / original-transition references against the rewritten
/// equivalents:
///
/// - `place_remap` — original place **name** → renamed place reference
/// - `transition_remap` — original transition **name** → renamed transition
///
/// Both maps are cleared on entry, then populated in iteration order.
///
/// The maps are keyed by `Arc<str>` name strings (not `Place`/`Transition`
/// object identity) because Rust place identity is name-based per
/// `compiled_net.rs` (`HashMap<Arc<str>, usize>`). This matches how the
/// compiled net dedupes places.
///
/// Returns a fresh [`PetriNet`] whose name is `prefix + "/" + body.name()`
/// and whose places/transitions are renamed copies.
pub(crate) fn rename_net(
    body: &PetriNet,
    prefix: &str,
    place_remap: &mut HashMap<Arc<str>, PlaceRef>,
    transition_remap: &mut HashMap<Arc<str>, Transition>,
) -> PetriNet {
    place_remap.clear();
    transition_remap.clear();

    // Pass 1: rename every place. Must precede transitions so arc rewriting
    // can resolve every place reference unambiguously.
    for orig in body.places() {
        let renamed = rename_place_ref(orig, prefix);
        place_remap.insert(Arc::clone(orig.name_arc()), renamed);
    }

    // Pass 2: rebuild every transition with arcs rewritten via place_remap.
    let mut builder = PetriNet::builder(format!("{}/{}", prefix, body.name()));

    // Add places explicitly: some may not be referenced by any transition arc,
    // but were declared on the body — preserve that membership.
    for renamed_place in place_remap.values() {
        builder = builder.place(renamed_place.clone());
    }

    for t in body.transitions() {
        let renamed = rewrite_transition(t, prefix, place_remap);
        transition_remap.insert(Arc::clone(t.name_arc()), renamed.clone());
        builder = builder.transition(renamed);
    }

    builder.build()
}

/// Returns a renamed copy of `orig`: a fresh [`PlaceRef`] whose name is
/// `prefix + "/" + orig.name()`.
pub(crate) fn rename_place_ref(orig: &PlaceRef, prefix: &str) -> PlaceRef {
    PlaceRef::new(format!("{}/{}", prefix, orig.name()))
}

/// Rebuilds `t` with name `prefix + "/" + t.name()` and every arc rewritten
/// through `place_remap`. Timing, priority, and action are carried through by
/// reference (action sharing per **MOD-030**).
///
/// If a place referenced by an arc is not present in `place_remap` (keyed by
/// original name), the arc retains the original place — partial remaps are
/// valid (used by the future `compose(...)` caller).
pub(crate) fn rewrite_transition(
    t: &Transition,
    prefix: &str,
    place_remap: &HashMap<Arc<str>, PlaceRef>,
) -> Transition {
    let new_name: Arc<str> = Arc::from(format!("{}/{}", prefix, t.name()));
    rebuild_with_name(t, new_name, place_remap)
}

/// Rebuilds `t` with the **same** name, substituting every arc place
/// reference through `remap`. Timing, priority, and action are carried
/// through by reference (action sharing per **MOD-030**).
///
/// This is the rewrite primitive used by `PetriNetBuilder::compose(...)`
/// (task #20) when merging an instance's renamed body into an enclosing net:
/// the transition's prefixed name is already unique within the host (per
/// **MOD-010**), so no further renaming is needed — only port-place
/// references are substituted with the caller's places.
///
/// If a place referenced by an arc is not present in `remap`, the arc
/// retains the original place — partial remaps are valid.
///
pub(crate) fn substitute_places(
    t: &Transition,
    remap: &HashMap<Arc<str>, PlaceRef>,
) -> Transition {
    rebuild_with_name(t, Arc::clone(t.name_arc()), remap)
}

// ============================================================
//  Shared transition-rebuild implementation
// ============================================================

/// Shared implementation: rebuilds `t` with the supplied `name` and arc
/// places rewritten through `remap`. Used by both [`rewrite_transition`]
/// (which prefixes the name) and [`substitute_places`] (which keeps the name
/// unchanged).
fn rebuild_with_name(
    t: &Transition,
    name: Arc<str>,
    remap: &HashMap<Arc<str>, PlaceRef>,
) -> Transition {
    let mut builder = Transition::builder(name)
        .timing(*t.timing())
        .priority(t.priority())
        .action(Arc::clone(t.action()));

    // Build the local-name → composed-name map. Each arc's original
    // place name maps to the renamed place's name (or the original if
    // not remapped). Compose any pre-existing local map (from an
    // earlier substitute pass) so subnet-of-subnet wiring chains
    // through correctly: local → first-pass → final.
    if let Some(local_map) = build_local_name_map(t, remap) {
        builder = builder.local_name_map(Arc::new(local_map));
    }

    if !t.input_specs().is_empty() {
        // Pre-size for V8/JIT-friendly hot-path allocation parity with the
        // Java/TS implementations.
        let src = t.input_specs();
        let mut rewritten_inputs: Vec<In> = Vec::with_capacity(src.len());
        for spec in src {
            rewritten_inputs.push(rewrite_in(spec, remap));
        }
        builder = builder.inputs(rewritten_inputs);
    }

    if let Some(out) = t.output_spec() {
        builder = builder.output(rewrite_out(out, remap));
    }

    if !t.inhibitors().is_empty() {
        let src = t.inhibitors();
        let mut rewritten: Vec<Inhibitor> = Vec::with_capacity(src.len());
        for inh in src {
            rewritten.push(rewrite_inhibitor(inh, remap));
        }
        builder = builder.inhibitors(rewritten);
    }
    if !t.reads().is_empty() {
        let src = t.reads();
        let mut rewritten: Vec<Read> = Vec::with_capacity(src.len());
        for rd in src {
            rewritten.push(rewrite_read(rd, remap));
        }
        builder = builder.reads(rewritten);
    }
    if !t.resets().is_empty() {
        let src = t.resets();
        let mut rewritten: Vec<Reset> = Vec::with_capacity(src.len());
        for rs in src {
            rewritten.push(rewrite_reset(rs, remap));
        }
        builder = builder.resets(rewritten);
    }

    // Carry the ν-net join correlation forward, following place renames so a
    // composed join still correlates the renamed inputs (NU-030 MUST / NU-020).
    if let Some(ms) = t.match_spec() {
        let keys: Vec<MatchKey> = ms
            .keys()
            .iter()
            .map(|k| MatchKey::from_erased(resolve(k.place(), remap), Arc::clone(k.key())))
            .collect();
        builder = builder.match_spec(MatchSpec::from_keys(keys));
    }

    builder.build()
}

// ============================================================
//  Local-name map construction
// ============================================================

/// Builds the `local_name -> composed_name` map for a transition that is
/// being rewritten through `remap`. The "local" side is whatever the
/// transition's arcs currently reference (which is either the
/// author-original names, for first-pass substitute, or the result of an
/// earlier substitute, which may have already chained through an
/// existing `local_name_map`).
///
/// Returns `None` if no name actually changes — keeps the field
/// `None`-valued for the common no-op case and avoids spurious Arc
/// allocation.
fn build_local_name_map(
    t: &Transition,
    remap: &HashMap<Arc<str>, PlaceRef>,
) -> Option<HashMap<Arc<str>, Arc<str>>> {
    if remap.is_empty() && t.local_name_map().is_none() {
        return None;
    }

    let mut map: HashMap<Arc<str>, Arc<str>> = HashMap::new();

    // Chained-compose path: the transition was already rewritten in a
    // prior pass and carries an author-local → intermediate-name map.
    // Chain through it (local → resolve(intermediate, remap)) and stop.
    //
    // We do NOT also walk the arcs here. Their names are the
    // intermediate-pass names, not author-original — recording them
    // would leak intermediate names as additional lookup keys
    // (`intermediate → final`), which the user never typed.
    // `substitute_places` only rewrites existing arcs; it never adds
    // new ones, so the author-original set is exactly the prev map's
    // keys.
    if let Some(prev) = t.local_name_map() {
        for (local, prev_name) in prev.as_ref().iter() {
            let final_name = match remap.get(prev_name) {
                Some(replaced) => Arc::clone(replaced.name_arc()),
                None => Arc::clone(prev_name),
            };
            if final_name != *local {
                map.insert(Arc::clone(local), final_name);
            }
        }
        return if map.is_empty() { None } else { Some(map) };
    }

    // First-substitute path: walk arcs to capture author-original
    // names. Original place names come straight off each arc; the
    // post-remap name is computed via the same `resolve` used during
    // the rewrite.
    let mut record = |orig: &PlaceRef| {
        let local = Arc::clone(orig.name_arc());
        if map.contains_key(&local) {
            return;
        }
        let post = match remap.get(&local) {
            Some(replaced) => Arc::clone(replaced.name_arc()),
            None => Arc::clone(&local),
        };
        if post != local {
            map.insert(local, post);
        }
    };

    for spec in t.input_specs() {
        record(spec.place());
    }
    for rd in t.reads() {
        record(&rd.place);
    }
    for inh in t.inhibitors() {
        record(&inh.place);
    }
    for rs in t.resets() {
        record(&rs.place);
    }
    if let Some(out) = t.output_spec() {
        collect_out_places(out, &mut record);
    }

    if map.is_empty() { None } else { Some(map) }
}

fn collect_out_places(out: &Out, f: &mut impl FnMut(&PlaceRef)) {
    match out {
        Out::Place(p) => f(p),
        Out::ForwardInput { from, to } => {
            f(from);
            f(to);
        }
        Out::And(children) | Out::Xor(children) => {
            for c in children {
                collect_out_places(c, f);
            }
        }
        Out::Timeout { child, .. } => collect_out_places(child, f),
    }
}

// ============================================================
//  Arc rewrite helpers (exhaustive matches — no wildcard arm)
// ============================================================

/// Rewrites an [`In`] via the place remap. Exhaustive `match` over the
/// `One`, `Exactly`, `All`, `AtLeast` variants.
pub(crate) fn rewrite_in(spec: &In, remap: &HashMap<Arc<str>, PlaceRef>) -> In {
    match spec {
        In::One { place } => In::One {
            place: resolve(place, remap),
        },
        In::Exactly { place, count } => In::Exactly {
            place: resolve(place, remap),
            count: *count,
        },
        In::All { place } => In::All {
            place: resolve(place, remap),
        },
        In::AtLeast { place, minimum } => In::AtLeast {
            place: resolve(place, remap),
            minimum: *minimum,
        },
    }
}

/// Rewrites an [`Out`] via the place remap. Exhaustive recursive `match`
/// over the `Place`, `ForwardInput`, `And`, `Xor`, `Timeout` variants.
/// `And`/`Xor` traversal uses pre-sized `Vec::with_capacity(n)` + indexed
/// `for` loops on the build-time hot path.
pub(crate) fn rewrite_out(out: &Out, remap: &HashMap<Arc<str>, PlaceRef>) -> Out {
    match out {
        Out::Place(p) => Out::Place(resolve(p, remap)),

        Out::ForwardInput { from, to } => Out::ForwardInput {
            from: resolve(from, remap),
            to: resolve(to, remap),
        },

        Out::And(children) => {
            let mut rewritten: Vec<Out> = Vec::with_capacity(children.len());
            for child in children {
                rewritten.push(rewrite_out(child, remap));
            }
            Out::And(rewritten)
        }

        Out::Xor(children) => {
            let mut rewritten: Vec<Out> = Vec::with_capacity(children.len());
            for child in children {
                rewritten.push(rewrite_out(child, remap));
            }
            Out::Xor(rewritten)
        }

        Out::Timeout { after_ms, child } => Out::Timeout {
            after_ms: *after_ms,
            child: Box::new(rewrite_out(child, remap)),
        },
    }
}

/// Rewrites an [`Inhibitor`] arc via the place remap.
pub(crate) fn rewrite_inhibitor(
    inh: &Inhibitor,
    remap: &HashMap<Arc<str>, PlaceRef>,
) -> Inhibitor {
    Inhibitor {
        place: resolve(&inh.place, remap),
    }
}

/// Rewrites a [`Read`] arc via the place remap.
pub(crate) fn rewrite_read(rd: &Read, remap: &HashMap<Arc<str>, PlaceRef>) -> Read {
    Read {
        place: resolve(&rd.place, remap),
    }
}

/// Rewrites a [`Reset`] arc via the place remap.
pub(crate) fn rewrite_reset(rs: &Reset, remap: &HashMap<Arc<str>, PlaceRef>) -> Reset {
    Reset {
        place: resolve(&rs.place, remap),
    }
}

// ============================================================
//  Resolution helper
// ============================================================

/// Looks up `p` in `remap` by `p.name()`; returns a clone of the original if
/// absent (partial-remap semantics for the future `compose` caller).
///
/// Cloning the original [`PlaceRef`] is `Arc::clone` (refcount-only); cloning
/// the remap value is also `Arc::clone`.
fn resolve(p: &PlaceRef, remap: &HashMap<Arc<str>, PlaceRef>) -> PlaceRef {
    match remap.get(p.name_arc()) {
        Some(replaced) => replaced.clone(),
        None => p.clone(),
    }
}

// ============================================================
//  Fusion: bulk place substitution across a transition set (MOD-061)
// ============================================================

/// Applies a fusion remap to every transition in `transitions`, substituting
/// non-canonical → canonical place references in each transition's arcs.
/// Returns a fresh `Vec<Transition>` in iteration order; the input collection
/// is not mutated.
///
/// This is the loop wrapper around [`substitute_places`]; it exists so
/// callers — notably [`crate::petri_net::PetriNetBuilder::build`] during
/// fusion resolution per **MOD-061** — do not duplicate the per-transition
/// dispatch. Transitions whose arcs do not reference any key of `fusion_map`
/// pass through unchanged in shape but are still rebuilt by
/// [`substitute_places`] (a fresh [`Transition`] instance); callers that care
/// about identity preservation for un-affected transitions should instead
/// skip the rewrite entirely when `fusion_map.is_empty()`.
///
/// The remap is keyed by **non-canonical place name** (`Arc<str>`) →
/// **canonical place** ([`PlaceRef`]) — matching the convention used
/// throughout this module.
pub(crate) fn apply_fusion(
    transitions: impl IntoIterator<Item = Transition>,
    fusion_map: &HashMap<Arc<str>, PlaceRef>,
) -> Vec<Transition> {
    let iter = transitions.into_iter();
    let (lower, upper) = iter.size_hint();
    let cap = upper.unwrap_or(lower);
    let mut rewritten: Vec<Transition> = Vec::with_capacity(cap);
    for t in iter {
        rewritten.push(substitute_places(&t, fusion_map));
    }
    rewritten
}

// ============================================================
//  Channel composition: transition merge (MOD-021)
// ============================================================

/// Merges a caller-side transition with an instance-side (renamed) channel
/// transition into a single [`Transition`] per **MOD-021**.
///
/// # Merge semantics
///
/// - **Identity / name** — caller wins. The merged transition's name is
///   `merged_name` (typically `caller.name()`), so the merged transition
///   remains discoverable from caller-side code paths.
/// - **Arcs** — input/inhibitor/read/reset arcs are unioned: caller-side
///   first, then instance-side. Duplicates (by structural key — same arc
///   kind + place name + cardinality where applicable) are deduped so
///   identical arcs to a shared place collapse.
/// - **Output spec** — if both sides carry an output spec, they are wrapped
///   under a single new outer `Out::And(vec![caller, instance])` so both
///   sides' outputs fire on a successful merged firing. If only one side
///   has an output spec, that one wins. If neither side has one, the merged
///   transition has none. `Out::And` permits heterogeneous children
///   (recursive trees), so wrapping a possibly-`And` child under a new
///   outer `And` is structurally legal.
/// - **Timing** — see [`merge_timings`]. Caller wins when one side is
///   [`Timing::Immediate`]; equal non-`Immediate` timings collapse;
///   conflicting non-`Immediate` timings panic.
/// - **Priority** — see [`pick_priority`]. Caller wins (policy, not a bug).
/// - **Action** — see [`compose_actions`]. Sequential composition: the
///   caller-side action runs first, then on its completion the instance-side
///   action runs against the same [`TransitionContext`]. The runtime sees
///   one transition firing per [CORE-021] / [EXEC-001].
///
/// # Panics
/// - Panics if `merged_name` is empty.
/// - Panics on conflicting non-`Immediate` timings (per **MOD-021**); the
///   message names the channel and both timings.
pub(crate) fn merge_transitions(
    caller: &Transition,
    instance: &Transition,
    merged_name: Arc<str>,
) -> Transition {
    assert!(
        !merged_name.is_empty(),
        "merge_transitions: merged_name must be non-empty"
    );

    // Resolve timing / match / alias first so any conflict short-circuits
    // before building — and so `merged_name` is still borrowable before the
    // builder takes ownership of it below.
    let merged_timing = merge_timings(caller.timing(), instance.timing(), &merged_name);
    let merged_priority = pick_priority(caller.priority(), instance.priority());
    let merged_action = compose_actions(caller.action(), instance.action());
    let merged_match = merge_match_specs(caller.match_spec(), instance.match_spec(), &merged_name);
    let merged_local =
        merge_local_name_maps(caller.local_name_map(), instance.local_name_map(), &merged_name);

    let mut builder = Transition::builder(merged_name)
        .timing(merged_timing)
        .priority(merged_priority);
    if let Some(action) = merged_action {
        builder = builder.action(action);
    }

    // Inputs: union caller-first, then instance, dedup by (kind, place name,
    // count/minimum where applicable) — matching Java's record-equality dedupe.
    let unioned_inputs = union_arcs(caller.input_specs(), instance.input_specs(), key_of_in);
    if !unioned_inputs.is_empty() {
        builder = builder.inputs(unioned_inputs);
    }

    // Outputs: wrap both sides under Out::And; one-sided wins; none -> none.
    if let Some(merged_output) = merge_outputs(caller.output_spec(), instance.output_spec()) {
        builder = builder.output(merged_output);
    }

    // Inhibitors / reads / resets: arc-record union (caller first, then instance).
    let unioned_inh = union_arcs(caller.inhibitors(), instance.inhibitors(), key_of_inhibitor);
    if !unioned_inh.is_empty() {
        builder = builder.inhibitors(unioned_inh);
    }
    let unioned_reads = union_arcs(caller.reads(), instance.reads(), key_of_read);
    if !unioned_reads.is_empty() {
        builder = builder.reads(unioned_reads);
    }
    let unioned_resets = union_arcs(caller.resets(), instance.resets(), key_of_reset);
    if !unioned_resets.is_empty() {
        builder = builder.resets(unioned_resets);
    }

    // Carry the ν-net join correlation forward (NU-060: a merge MUST NOT
    // silently drop a match). Both sides already reference final host places at
    // merge time (upstream substitute_places remapped them, match included), so
    // the surviving match is cloned as-is — no further remap.
    if let Some(ms) = merged_match {
        builder = builder.match_spec(ms);
    }

    // Carry the MOD-031 declared→actual (local-name) map forward: the merged
    // action runs both sides' actions sequentially and each resolves its
    // declared place constants through this map (MOD-030 / MOD-031).
    if let Some(map) = merged_local {
        builder = builder.local_name_map(map);
    }

    builder.build()
}

/// Carries the ν-net join correlation ([`MatchSpec`]) through a channel merge
/// per **NU-060**. One-sided → that side's match survives; both-`None` → `None`;
/// both `Some` → the merge is rejected with a panic, because two independent
/// name correlations cannot be silently fused into one transition and NU-060
/// forbids dropping a match. The surviving match is cloned as-is: both
/// transitions already reference final host places at merge time, so no place
/// remap is applied here (unlike [`rebuild_with_name`]).
fn merge_match_specs(
    caller: Option<&MatchSpec>,
    instance: Option<&MatchSpec>,
    channel_name: &str,
) -> Option<MatchSpec> {
    match (caller, instance) {
        (None, None) => None,
        (Some(ms), None) | (None, Some(ms)) => Some(ms.clone()),
        (Some(_), Some(_)) => panic!(
            "Channel composition '{}': both the caller-side and instance-side \
             transition carry a ν-net match — refusing to fuse two independent \
             correlations into one transition (NU-060). Resolve explicitly by \
             keeping the match on a single side.",
            channel_name
        ),
    }
}

/// Unions the two sides' MOD-031 declared→actual (local-name) maps for a channel
/// merge. Both actions run within the single merged firing, so each side's
/// declared-place resolution must survive. Disjoint keys union; an entry present
/// on both sides with the same actual collapses; a genuine conflict (same
/// declared name bound to two different actual names) is rejected with a panic
/// naming the declared place.
fn merge_local_name_maps(
    caller: Option<&Arc<HashMap<Arc<str>, Arc<str>>>>,
    instance: Option<&Arc<HashMap<Arc<str>, Arc<str>>>>,
    channel_name: &str,
) -> Option<Arc<HashMap<Arc<str>, Arc<str>>>> {
    match (caller, instance) {
        (None, None) => None,
        (Some(m), None) | (None, Some(m)) => Some(Arc::clone(m)),
        (Some(c), Some(i)) => {
            let mut merged: HashMap<Arc<str>, Arc<str>> = (**c).clone();
            for (declared, actual) in i.iter() {
                if let Some(existing) = merged.get(declared) {
                    if existing != actual {
                        panic!(
                            "Channel composition '{}': conflicting declared→actual place \
                             alias for declared place '{}' — caller-side maps to '{}', \
                             instance-side to '{}' (MOD-031). Resolve explicitly.",
                            channel_name, declared, existing, actual
                        );
                    }
                }
                merged.insert(Arc::clone(declared), Arc::clone(actual));
            }
            Some(Arc::new(merged))
        }
    }
}

/// Merges two timings per **MOD-021**:
///
/// - Both [`Timing::Immediate`] -> `Immediate`.
/// - One `Immediate` -> the other side wins.
/// - Both non-`Immediate` and equal -> collapse.
/// - Otherwise the conflict is rejected with a panic naming the channel and
///   both timings — the user must resolve it explicitly.
pub(crate) fn merge_timings(caller: &Timing, instance: &Timing, channel_name: &str) -> Timing {
    match (caller, instance) {
        (Timing::Immediate, Timing::Immediate) => Timing::Immediate,
        (Timing::Immediate, _) => *instance,
        (_, Timing::Immediate) => *caller,
        _ if caller == instance => *caller,
        _ => panic!(
            "Channel composition '{}': conflicting non-Immediate timings — \
             caller-side {:?} vs instance-side {:?}. \
             Resolve explicitly by aligning the timings on either side (MOD-021).",
            channel_name, caller, instance
        ),
    }
}

/// Caller-side priority wins per **MOD-021**. Documented as policy: the
/// instance-side priority is ignored, not blended.
pub(crate) fn pick_priority(caller_priority: i32, _instance_priority: i32) -> i32 {
    caller_priority
}

/// Composes two transition actions sequentially: the caller-side action runs
/// first, then on its completion the instance-side action runs against the
/// same [`TransitionContext`]. The combined action surfaces a single
/// [`std::future::Future`] so the executor sees one transition firing per
/// [CORE-021] / [EXEC-001].
///
/// Passthrough handling:
/// - If both sides are the singleton [`crate::action::passthrough`] action,
///   returns `None` so [`merge_transitions`] leaves the builder's default
///   passthrough in place.
/// - If exactly one side is passthrough, the other side is returned by
///   reference (no extra wrapping).
/// - Otherwise returns a fresh [`SequentialAction`] composing both
///   sequentially.
pub(crate) fn compose_actions(caller: &BoxedAction, instance: &BoxedAction) -> Option<BoxedAction> {
    let caller_pass = is_passthrough(caller);
    let instance_pass = is_passthrough(instance);

    if caller_pass && instance_pass {
        return None;
    }
    if caller_pass {
        return Some(Arc::clone(instance));
    }
    if instance_pass {
        return Some(Arc::clone(caller));
    }
    Some(Arc::new(SequentialAction {
        first: Arc::clone(caller),
        second: Arc::clone(instance),
    }))
}

/// Combines two output specs per the merge contract: if both are present,
/// wrap them under a single `Out::And`; otherwise return the non-`None` side
/// (or `None` if both are missing).
pub(crate) fn merge_outputs(caller: Option<&Out>, instance: Option<&Out>) -> Option<Out> {
    match (caller, instance) {
        (None, None) => None,
        (Some(c), None) => Some(c.clone()),
        (None, Some(i)) => Some(i.clone()),
        (Some(c), Some(i)) => Some(Out::And(vec![c.clone(), i.clone()])),
    }
}

/// Returns the union of two arc lists, caller-first then instance, with
/// duplicates removed by structural key. Order is preserved within each
/// source list. Used for input, inhibitor, read, and reset arcs.
///
/// Implementation note: a `Vec` + a `HashSet<String>` of seen keys preserves
/// insertion order while deduping by the supplied key function. The Rust arc
/// types are not hashable in a way that captures cardinality, so the caller
/// supplies a `keyOf*` function mirroring the TS approach.
pub(crate) fn union_arcs<A: Clone>(
    caller: &[A],
    instance: &[A],
    key_of: fn(&A) -> String,
) -> Vec<A> {
    if caller.is_empty() && instance.is_empty() {
        return Vec::new();
    }
    let cap = caller.len() + instance.len();
    let mut result: Vec<A> = Vec::with_capacity(cap);
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::with_capacity(cap);
    for arc in caller {
        let k = key_of(arc);
        if seen.insert(k) {
            result.push(arc.clone());
        }
    }
    for arc in instance {
        let k = key_of(arc);
        if seen.insert(k) {
            result.push(arc.clone());
        }
    }
    result
}

// ---------- Sequential action composition (caller-then-instance) ----------

/// A composed action that runs `first` to completion, then runs `second`
/// against the same [`TransitionContext`]. Used by [`compose_actions`] for
/// channel composition (MOD-021). Each underlying action is shared by
/// reference (`Arc::clone`).
struct SequentialAction {
    first: BoxedAction,
    second: BoxedAction,
}

impl TransitionAction for SequentialAction {
    fn is_sync(&self) -> bool {
        // Sync only if both sides are sync. The runtime treats this as a
        // single transition firing per [EXEC-001].
        self.first.is_sync() && self.second.is_sync()
    }

    fn run_sync(&self, ctx: &mut TransitionContext) -> Result<(), ActionError> {
        self.first.run_sync(ctx)?;
        self.second.run_sync(ctx)?;
        Ok(())
    }

    fn run_async<'a>(
        &'a self,
        ctx: TransitionContext,
    ) -> Pin<Box<dyn Future<Output = Result<TransitionContext, ActionError>> + Send + 'a>> {
        Box::pin(async move {
            let ctx = self.first.run_async(ctx).await?;
            let ctx = self.second.run_async(ctx).await?;
            Ok(ctx)
        })
    }
}

// ---------- Structural arc keys (mirror TS keyOf*) ----------

/// Structural key for an [`In`] arc. Encodes the discriminant + place name +
/// cardinality (where applicable). Input specifications are purely structural
/// (IO-006), so this key is total.
fn key_of_in(arc: &In) -> String {
    match arc {
        In::One { place } => format!("one|{}", place.name()),
        In::Exactly { place, count } => format!("exactly|{}|{}", place.name(), count),
        In::All { place } => format!("all|{}", place.name()),
        In::AtLeast { place, minimum } => format!("atLeast|{}|{}", place.name(), minimum),
    }
}

fn key_of_inhibitor(arc: &Inhibitor) -> String {
    format!("inh|{}", arc.place.name())
}

fn key_of_read(arc: &Read) -> String {
    format!("read|{}", arc.place.name())
}

fn key_of_reset(arc: &Reset) -> String {
    format!("reset|{}", arc.place.name())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arc::{inhibitor, read, reset};
    use crate::input::{all, at_least, exactly, one};
    use crate::name::NameId;
    use crate::output::{and, forward_input, out_place, timeout, xor};
    use crate::place::Place;
    use crate::timing::{deadline, delayed, immediate};

    // ============================================================
    //  rename_net
    // ============================================================

    #[test]
    fn rename_net_prefixes_all_place_and_transition_names() {
        let p_in = Place::<i32>::new("in");
        let p_out = Place::<i32>::new("out");
        let t = Transition::builder("move")
            .input(one(&p_in))
            .output(out_place(&p_out))
            .build();
        let body = PetriNet::builder("Body").transition(t).build();

        let mut place_remap = HashMap::new();
        let mut transition_remap = HashMap::new();
        let renamed = rename_net(&body, "p1", &mut place_remap, &mut transition_remap);

        assert_eq!(renamed.name(), "p1/Body");
        for place in renamed.places() {
            assert!(
                place.name().starts_with("p1/"),
                "place '{}' missing p1/ prefix",
                place.name()
            );
        }
        for t in renamed.transitions() {
            assert!(
                t.name().starts_with("p1/"),
                "transition '{}' missing p1/ prefix",
                t.name()
            );
        }
        assert_eq!(place_remap.len(), 2);
        assert_eq!(transition_remap.len(), 1);
        assert_eq!(place_remap.get("in").unwrap().name(), "p1/in");
        assert_eq!(place_remap.get("out").unwrap().name(), "p1/out");
        assert_eq!(transition_remap.get("move").unwrap().name(), "p1/move");
    }

    #[test]
    fn rename_net_clears_input_maps() {
        let p = Place::<i32>::new("p");
        let t = Transition::builder("t").input(one(&p)).build();
        let body = PetriNet::builder("B").transition(t).build();

        let mut place_remap = HashMap::new();
        place_remap.insert(Arc::<str>::from("stale"), PlaceRef::new("stale_value"));
        let mut transition_remap = HashMap::new();
        transition_remap.insert(
            Arc::<str>::from("stale_t"),
            Transition::builder("stale_t").build(),
        );

        let _ = rename_net(&body, "x", &mut place_remap, &mut transition_remap);

        assert!(!place_remap.contains_key("stale"));
        assert!(!transition_remap.contains_key("stale_t"));
    }

    #[test]
    fn rename_net_preserves_orphan_places() {
        let orphan = Place::<i32>::new("orphan");
        let body = PetriNet::builder("B").place(orphan.as_ref()).build();

        let mut place_remap = HashMap::new();
        let mut transition_remap = HashMap::new();
        let renamed = rename_net(&body, "i1", &mut place_remap, &mut transition_remap);

        assert_eq!(renamed.places().len(), 1);
        assert!(
            renamed.places().contains(&PlaceRef::new("i1/orphan")),
            "renamed body must contain prefixed orphan place"
        );
    }

    #[test]
    fn rename_net_preserves_timing_priority_and_action_by_reference() {
        let p = Place::<i32>::new("p");
        let action = crate::action::passthrough();
        let t = Transition::builder("t")
            .input(one(&p))
            .timing(delayed(50))
            .priority(7)
            .action(Arc::clone(&action))
            .build();
        let body = PetriNet::builder("B").transition(t).build();

        let mut place_remap = HashMap::new();
        let mut transition_remap = HashMap::new();
        let renamed = rename_net(&body, "i1", &mut place_remap, &mut transition_remap);

        let renamed_t = &renamed.transitions()[0];
        assert_eq!(*renamed_t.timing(), delayed(50));
        assert_eq!(renamed_t.priority(), 7);
        // Action carried through by reference (Arc::clone of the same
        // underlying TransitionAction).
        assert!(Arc::ptr_eq(renamed_t.action(), &action));
    }

    // ============================================================
    //  rewrite_in — exhaustive variant coverage
    // ============================================================

    #[test]
    fn rewrite_in_one_substitutes_place() {
        let p = Place::<i32>::new("p");
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("p"), PlaceRef::new("renamed/p"));

        let rewritten = rewrite_in(&one(&p), &remap);
        match rewritten {
            In::One { place, .. } => assert_eq!(place.name(), "renamed/p"),
            other => panic!("expected In::One, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_in_exactly_preserves_count() {
        let p = Place::<i32>::new("p");
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("p"), PlaceRef::new("r/p"));

        let rewritten = rewrite_in(&exactly(3, &p), &remap);
        match rewritten {
            In::Exactly { place, count, .. } => {
                assert_eq!(place.name(), "r/p");
                assert_eq!(count, 3);
            }
            other => panic!("expected In::Exactly, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_in_all_substitutes_place() {
        let p = Place::<i32>::new("p");
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("p"), PlaceRef::new("r/p"));

        let rewritten = rewrite_in(&all(&p), &remap);
        match rewritten {
            In::All { place, .. } => assert_eq!(place.name(), "r/p"),
            other => panic!("expected In::All, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_in_at_least_preserves_minimum() {
        let p = Place::<i32>::new("p");
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("p"), PlaceRef::new("r/p"));

        let rewritten = rewrite_in(&at_least(5, &p), &remap);
        match rewritten {
            In::AtLeast {
                place, minimum, ..
            } => {
                assert_eq!(place.name(), "r/p");
                assert_eq!(minimum, 5);
            }
            other => panic!("expected In::AtLeast, got {other:?}"),
        }
    }

    // ============================================================
    //  rewrite_out — exhaustive variant coverage including recursion
    // ============================================================

    #[test]
    fn rewrite_out_place_substitutes() {
        let p = Place::<i32>::new("p");
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("p"), PlaceRef::new("r/p"));

        let rewritten = rewrite_out(&out_place(&p), &remap);
        match rewritten {
            Out::Place(pr) => assert_eq!(pr.name(), "r/p"),
            other => panic!("expected Out::Place, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_out_forward_input_substitutes_both() {
        let from = Place::<i32>::new("from");
        let to = Place::<i32>::new("to");
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("from"), PlaceRef::new("r/from"));
        remap.insert(Arc::<str>::from("to"), PlaceRef::new("r/to"));

        let rewritten = rewrite_out(&forward_input(&from, &to), &remap);
        match rewritten {
            Out::ForwardInput { from, to } => {
                assert_eq!(from.name(), "r/from");
                assert_eq!(to.name(), "r/to");
            }
            other => panic!("expected Out::ForwardInput, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_out_recursive_and_xor_timeout_walks_tree() {
        // Build: And( Xor(a, Timeout(100, b)), c )
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let c = Place::<i32>::new("c");
        let nested = and(vec![
            xor(vec![out_place(&a), timeout(100, out_place(&b))]),
            out_place(&c),
        ]);
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("a"), PlaceRef::new("r/a"));
        remap.insert(Arc::<str>::from("b"), PlaceRef::new("r/b"));
        remap.insert(Arc::<str>::from("c"), PlaceRef::new("r/c"));

        let rewritten = rewrite_out(&nested, &remap);
        let Out::And(top_children) = rewritten else {
            panic!("expected Out::And at root");
        };
        assert_eq!(top_children.len(), 2);
        let Out::Xor(xor_children) = &top_children[0] else {
            panic!("expected Out::Xor as first And-child");
        };
        assert_eq!(xor_children.len(), 2);
        match &xor_children[0] {
            Out::Place(pr) => assert_eq!(pr.name(), "r/a"),
            other => panic!("expected Out::Place(r/a), got {other:?}"),
        }
        match &xor_children[1] {
            Out::Timeout { after_ms, child } => {
                assert_eq!(*after_ms, 100);
                match child.as_ref() {
                    Out::Place(pr) => assert_eq!(pr.name(), "r/b"),
                    other => panic!("expected Out::Place(r/b) inside Timeout, got {other:?}"),
                }
            }
            other => panic!("expected Out::Timeout, got {other:?}"),
        }
        match &top_children[1] {
            Out::Place(pr) => assert_eq!(pr.name(), "r/c"),
            other => panic!("expected Out::Place(r/c), got {other:?}"),
        }
    }

    // ============================================================
    //  Inhibitor / Read / Reset
    // ============================================================

    #[test]
    fn rewrite_inhibitor_substitutes_place() {
        let p = Place::<i32>::new("p");
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("p"), PlaceRef::new("r/p"));
        let rewritten = rewrite_inhibitor(&inhibitor(&p), &remap);
        assert_eq!(rewritten.place.name(), "r/p");
    }

    #[test]
    fn rewrite_read_substitutes_place() {
        let p = Place::<i32>::new("p");
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("p"), PlaceRef::new("r/p"));
        let rewritten = rewrite_read(&read(&p), &remap);
        assert_eq!(rewritten.place.name(), "r/p");
    }

    #[test]
    fn rewrite_reset_substitutes_place() {
        let p = Place::<i32>::new("p");
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("p"), PlaceRef::new("r/p"));
        let rewritten = rewrite_reset(&reset(&p), &remap);
        assert_eq!(rewritten.place.name(), "r/p");
    }

    // ============================================================
    //  Identity passthrough on places not in remap
    // ============================================================

    #[test]
    fn rewrite_in_returns_original_place_when_not_in_remap() {
        let p = Place::<i32>::new("p");
        let remap: HashMap<Arc<str>, PlaceRef> = HashMap::new();
        let rewritten = rewrite_in(&one(&p), &remap);
        match rewritten {
            In::One { place, .. } => assert_eq!(place.name(), "p"),
            other => panic!("expected In::One with original name, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_out_returns_original_place_when_not_in_remap() {
        let p = Place::<i32>::new("p");
        let remap: HashMap<Arc<str>, PlaceRef> = HashMap::new();
        let rewritten = rewrite_out(&out_place(&p), &remap);
        match rewritten {
            Out::Place(pr) => assert_eq!(pr.name(), "p"),
            other => panic!("expected Out::Place with original name, got {other:?}"),
        }
    }

    #[test]
    fn rewrite_inhibitor_returns_original_place_when_not_in_remap() {
        let p = Place::<i32>::new("p");
        let remap: HashMap<Arc<str>, PlaceRef> = HashMap::new();
        let rewritten = rewrite_inhibitor(&inhibitor(&p), &remap);
        assert_eq!(rewritten.place.name(), "p");
    }

    // ============================================================
    //  substitute_places — keeps name, swaps places
    // ============================================================

    #[test]
    fn substitute_places_keeps_transition_name_unchanged() {
        let p = Place::<i32>::new("port");
        let t = Transition::builder("inst1/move")
            .input(one(&p))
            .timing(immediate())
            .build();

        let caller_place = PlaceRef::new("caller/port");
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("port"), caller_place.clone());

        let substituted = substitute_places(&t, &remap);
        assert_eq!(
            substituted.name(),
            "inst1/move",
            "substitute_places must NOT rename the transition"
        );
        match &substituted.input_specs()[0] {
            In::One { place, .. } => assert_eq!(place.name(), "caller/port"),
            other => panic!("expected In::One, got {other:?}"),
        }
    }

    #[test]
    fn substitute_places_partial_remap_passes_through_unmapped_places() {
        let in_p = Place::<i32>::new("in");
        let out_p = Place::<i32>::new("out");
        let t = Transition::builder("t")
            .input(one(&in_p))
            .output(out_place(&out_p))
            .build();

        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("in"), PlaceRef::new("caller/in"));

        let substituted = substitute_places(&t, &remap);
        match &substituted.input_specs()[0] {
            In::One { place, .. } => assert_eq!(place.name(), "caller/in"),
            other => panic!("expected In::One, got {other:?}"),
        }
        match substituted.output_spec().unwrap() {
            Out::Place(pr) => assert_eq!(pr.name(), "out", "unmapped place must pass through"),
            other => panic!("expected Out::Place, got {other:?}"),
        }
    }

    // ============================================================
    //  rename_place_ref
    // ============================================================

    #[test]
    fn rename_place_ref_prefixes_name() {
        let p = PlaceRef::new("foo");
        let renamed = rename_place_ref(&p, "ins");
        assert_eq!(renamed.name(), "ins/foo");
    }

    // ============================================================
    //  merge_transitions — channel composition (MOD-021)
    // ============================================================

    #[test]
    fn channel_merge_unions_arcs_from_both_sides() {
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");

        let caller = Transition::builder("merged").read(read(&a)).build();
        let instance = Transition::builder("instanceSide").read(read(&b)).build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        assert_eq!(merged.name(), "merged");
        assert_eq!(merged.reads().len(), 2);
        let read_names: std::collections::HashSet<&str> =
            merged.reads().iter().map(|r| r.place.name()).collect();
        assert!(read_names.contains("a"));
        assert!(read_names.contains("b"));
    }

    #[test]
    fn channel_merge_unions_input_arcs() {
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");

        let caller = Transition::builder("merged").input(one(&a)).build();
        let instance = Transition::builder("instanceSide").input(one(&b)).build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        assert_eq!(merged.input_specs().len(), 2);
        let names: std::collections::HashSet<&str> =
            merged.input_specs().iter().map(|s| s.place_name()).collect();
        assert!(names.contains("a"));
        assert!(names.contains("b"));
    }

    #[test]
    fn channel_merge_unions_inhibitor_read_reset_arcs() {
        let inh1 = Place::<String>::new("inh1");
        let inh2 = Place::<String>::new("inh2");
        let rd1 = Place::<String>::new("rd1");
        let rd2 = Place::<String>::new("rd2");
        let rs1 = Place::<String>::new("rs1");
        let rs2 = Place::<String>::new("rs2");

        let caller = Transition::builder("merged")
            .inhibitor(inhibitor(&inh1))
            .read(read(&rd1))
            .reset(reset(&rs1))
            .build();
        let instance = Transition::builder("instanceSide")
            .inhibitor(inhibitor(&inh2))
            .read(read(&rd2))
            .reset(reset(&rs2))
            .build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        assert_eq!(merged.inhibitors().len(), 2);
        assert_eq!(merged.reads().len(), 2);
        assert_eq!(merged.resets().len(), 2);
    }

    #[test]
    fn channel_merge_dedupes_identical_arcs() {
        let shared = Place::<String>::new("shared");

        let caller = Transition::builder("merged").read(read(&shared)).build();
        let instance = Transition::builder("instanceSide").read(read(&shared)).build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        assert_eq!(merged.reads().len(), 1);
        assert_eq!(merged.reads()[0].place.name(), "shared");
    }

    #[test]
    fn channel_merge_unions_output_specs_into_and() {
        let q_caller = Place::<String>::new("qCaller");
        let q_instance = Place::<String>::new("qInstance");

        let caller = Transition::builder("merged")
            .output(out_place(&q_caller))
            .build();
        let instance = Transition::builder("instanceSide")
            .output(out_place(&q_instance))
            .build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        let out = merged.output_spec().expect("merged has output spec");
        match out {
            Out::And(children) => {
                assert_eq!(children.len(), 2);
                let names: std::collections::HashSet<&str> = merged
                    .output_places()
                    .iter()
                    .map(|p| p.name())
                    .collect();
                assert!(names.contains("qCaller"));
                assert!(names.contains("qInstance"));
            }
            other => panic!("expected Out::And, got {other:?}"),
        }
    }

    #[test]
    fn channel_merge_output_spec_only_one_side_that_side_wins() {
        let q_caller = Place::<String>::new("qCaller");

        let caller = Transition::builder("merged")
            .output(out_place(&q_caller))
            .build();
        let instance = Transition::builder("instanceSide").build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        let out = merged.output_spec().expect("merged has output spec");
        match out {
            Out::Place(pr) => assert_eq!(pr.name(), "qCaller"),
            other => panic!("expected Out::Place (single-sided), got {other:?}"),
        }
    }

    #[test]
    fn channel_merge_caller_priority_wins() {
        let caller = Transition::builder("merged").priority(5).build();
        let instance = Transition::builder("instanceSide").priority(10).build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        assert_eq!(merged.priority(), 5);
    }

    #[test]
    fn channel_merge_caller_timing_wins_when_instance_immediate() {
        let caller = Transition::builder("merged").timing(delayed(50)).build();
        let instance = Transition::builder("instanceSide").timing(immediate()).build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        assert_eq!(*merged.timing(), delayed(50));
    }

    #[test]
    fn channel_merge_instance_timing_wins_when_caller_immediate() {
        let caller = Transition::builder("merged").timing(immediate()).build();
        let instance = Transition::builder("instanceSide").timing(delayed(75)).build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        assert_eq!(*merged.timing(), delayed(75));
    }

    #[test]
    fn channel_merge_both_immediate_result_immediate() {
        let caller = Transition::builder("merged").timing(immediate()).build();
        let instance = Transition::builder("instanceSide").timing(immediate()).build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        assert_eq!(*merged.timing(), immediate());
    }

    #[test]
    fn channel_merge_equal_non_immediate_timings_collapse() {
        let caller = Transition::builder("merged").timing(delayed(50)).build();
        let instance = Transition::builder("instanceSide").timing(delayed(50)).build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        assert_eq!(*merged.timing(), delayed(50));
    }

    #[test]
    fn channel_merge_conflicting_timings_panics() {
        let caller = Transition::builder("merged").timing(delayed(50)).build();
        let instance = Transition::builder("instanceSide").timing(deadline(100)).build();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            merge_transitions(&caller, &instance, Arc::<str>::from("attempt"))
        }));
        let err = result.expect_err("merge_transitions must panic on conflicting timings");
        let msg: String = err
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| err.downcast_ref::<&'static str>().map(|s| s.to_string()))
            .unwrap_or_default();
        assert!(msg.contains("attempt"), "must name the channel: {msg}");
        assert!(msg.contains("Delayed"), "must name caller timing: {msg}");
        assert!(msg.contains("Deadline"), "must name instance timing: {msg}");
    }

    #[test]
    fn channel_merge_actions_run_sequentially() {
        use std::sync::Mutex;

        let calls: Arc<Mutex<Vec<&'static str>>> = Arc::new(Mutex::new(Vec::new()));

        let calls_caller = Arc::clone(&calls);
        let caller_action = crate::action::sync_action(move |_ctx: &mut TransitionContext| {
            calls_caller.lock().unwrap().push("caller");
            Ok(())
        });
        let calls_instance = Arc::clone(&calls);
        let instance_action = crate::action::sync_action(move |_ctx: &mut TransitionContext| {
            calls_instance.lock().unwrap().push("instance");
            Ok(())
        });

        let caller = Transition::builder("merged").action(caller_action).build();
        let instance = Transition::builder("instanceSide")
            .action(instance_action)
            .build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        // Drive the merged action with a minimal context.
        let mut ctx = TransitionContext::new(
            Arc::<str>::from("merged"),
            std::collections::HashMap::new(),
            std::collections::HashMap::new(),
            std::collections::HashSet::new(),
            None,
        );
        merged.action().run_sync(&mut ctx).unwrap();

        let observed = calls.lock().unwrap().clone();
        assert_eq!(observed, vec!["caller", "instance"]);
    }

    #[test]
    fn channel_merge_single_passthrough_no_panic() {
        // composeActions: when one side is the singleton passthrough action,
        // the other is returned by reference (no extra wrapping).
        let calls: Arc<std::sync::Mutex<i32>> = Arc::new(std::sync::Mutex::new(0));
        let calls_inner = Arc::clone(&calls);
        let instance_action = crate::action::sync_action(move |_ctx: &mut TransitionContext| {
            *calls_inner.lock().unwrap() += 1;
            Ok(())
        });

        let composed =
            compose_actions(&crate::action::passthrough(), &instance_action).expect("Some");
        assert!(
            Arc::ptr_eq(&composed, &instance_action),
            "single-passthrough must return the other side by reference"
        );

        let mut ctx = TransitionContext::new(
            Arc::<str>::from("t"),
            std::collections::HashMap::new(),
            std::collections::HashMap::new(),
            std::collections::HashSet::new(),
            None,
        );
        composed.run_sync(&mut ctx).unwrap();
        assert_eq!(*calls.lock().unwrap(), 1);
    }

    #[test]
    fn channel_merge_both_passthrough() {
        // composeActions: when both sides are the singleton passthrough,
        // returns None — mergeTransitions then leaves the builder default
        // (which is itself the passthrough singleton) in place.
        let composed = compose_actions(&crate::action::passthrough(), &crate::action::passthrough());
        assert!(
            composed.is_none(),
            "both-passthrough must collapse to None so the builder default takes over"
        );

        // End-to-end: merging two default-action transitions yields a merged
        // transition whose action is the singleton passthrough.
        let caller = Transition::builder("merged").build();
        let instance = Transition::builder("instanceSide").build();
        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));
        assert!(
            Arc::ptr_eq(merged.action(), &crate::action::passthrough()),
            "merged action must be the singleton passthrough when both sides default"
        );

        // Must be safely callable end-to-end without erroring.
        let mut ctx = TransitionContext::new(
            Arc::<str>::from("merged"),
            std::collections::HashMap::new(),
            std::collections::HashMap::new(),
            std::collections::HashSet::new(),
            None,
        );
        merged.action().run_sync(&mut ctx).unwrap();
    }

    #[test]
    fn channel_merge_caller_name_wins() {
        let caller = Transition::builder("callerName").build();
        let instance = Transition::builder("instanceName").build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("callerName"));

        assert_eq!(merged.name(), "callerName");
    }

    // ============================================================
    //  ν-net match + local-name-map carry (NU-030 / NU-060 / MOD-031)
    // ============================================================

    fn cid_match(a: &Place<String>, b: &Place<String>) -> MatchSpec {
        MatchSpec::builder()
            .key(a, |s: &String| NameId::new(s.clone()))
            .key(b, |s: &String| NameId::new(s.clone()))
            .build()
    }

    /// NU-030 (MUST): a match carried through the rename/substitute path must
    /// have its correlated places remapped by the same rewrite the arcs follow.
    /// This is the broader Rust/Python bug — port-composition and instantiation
    /// both go through `substitute_places` → `rebuild_with_name`.
    #[test]
    fn substitute_places_carries_and_remaps_match_spec() {
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let t = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(cid_match(&a, &b))
            .build();

        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("a"), PlaceRef::new("host/a"));
        remap.insert(Arc::<str>::from("b"), PlaceRef::new("host/b"));

        let rewritten = substitute_places(&t, &remap);
        let ms = rewritten
            .match_spec()
            .expect("NU-030: substitute must carry the match_spec, not drop it");
        assert!(ms.correlates("host/a"), "match place must be remapped to host/a");
        assert!(ms.correlates("host/b"), "match place must be remapped to host/b");
        assert!(!ms.correlates("a"), "original (unremapped) place must be gone");
    }

    /// NU-060 criterion #1: a one-sided (caller) match survives the channel merge.
    #[test]
    fn channel_merge_carries_caller_match_spec() {
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let caller = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(cid_match(&a, &b))
            .build();
        let instance = Transition::builder("instanceSide").build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("join"));

        let ms = merged
            .match_spec()
            .expect("NU-060: caller-side match must survive the merge");
        assert!(ms.correlates("a"));
        assert!(ms.correlates("b"));
    }

    /// NU-060 criterion #1: a one-sided (instance) match also survives.
    #[test]
    fn channel_merge_carries_instance_match_spec() {
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let caller = Transition::builder("join").build();
        let instance = Transition::builder("instanceSide")
            .input(one(&a))
            .input(one(&b))
            .match_spec(cid_match(&a, &b))
            .build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("join"));

        let ms = merged
            .match_spec()
            .expect("NU-060: instance-side match must survive the merge");
        assert!(ms.correlates("a"));
        assert!(ms.correlates("b"));
    }

    /// NU-060: two independent correlations cannot be silently fused — the merge
    /// is rejected with a panic naming the channel.
    #[test]
    fn channel_merge_both_sides_carry_match_panics() {
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let c = Place::<String>::new("c");
        let d = Place::<String>::new("d");
        let caller = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(cid_match(&a, &b))
            .build();
        let instance = Transition::builder("instanceSide")
            .input(one(&c))
            .input(one(&d))
            .match_spec(cid_match(&c, &d))
            .build();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            merge_transitions(&caller, &instance, Arc::<str>::from("attempt"))
        }));
        let err = result.expect_err("merge must panic when both sides carry a match");
        let msg: String = err
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| err.downcast_ref::<&'static str>().map(|s| s.to_string()))
            .unwrap_or_default();
        assert!(msg.contains("attempt"), "must name the channel: {msg}");
        assert!(msg.contains("NU-060"), "must cite NU-060: {msg}");
    }

    /// MOD-031: the declared→actual (local-name) map is unioned across sides so
    /// each composed action resolves its declared place constants.
    #[test]
    fn channel_merge_unions_local_name_map() {
        let caller = Transition::builder("merged")
            .local_name_map(Arc::new(HashMap::from([(
                Arc::<str>::from("declaredA"),
                Arc::<str>::from("host/actualA"),
            )])))
            .build();
        let instance = Transition::builder("instanceSide")
            .local_name_map(Arc::new(HashMap::from([(
                Arc::<str>::from("declaredB"),
                Arc::<str>::from("host/actualB"),
            )])))
            .build();

        let merged = merge_transitions(&caller, &instance, Arc::<str>::from("merged"));

        let map = merged
            .local_name_map()
            .expect("MOD-031: local_name_map must survive the merge");
        assert_eq!(map.get("declaredA").map(|s| &**s), Some("host/actualA"));
        assert_eq!(map.get("declaredB").map(|s| &**s), Some("host/actualB"));
    }

    /// MOD-031: the same declared name bound to two different actual names
    /// across the fused sides is an ambiguous correspondence, rejected.
    #[test]
    fn channel_merge_conflicting_local_name_map_panics() {
        let caller = Transition::builder("merged")
            .local_name_map(Arc::new(HashMap::from([(
                Arc::<str>::from("declaredX"),
                Arc::<str>::from("host/a"),
            )])))
            .build();
        let instance = Transition::builder("instanceSide")
            .local_name_map(Arc::new(HashMap::from([(
                Arc::<str>::from("declaredX"),
                Arc::<str>::from("host/b"),
            )])))
            .build();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            merge_transitions(&caller, &instance, Arc::<str>::from("attempt"))
        }));
        let err = result.expect_err("merge must panic on conflicting local_name_map");
        let msg: String = err
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| err.downcast_ref::<&'static str>().map(|s| s.to_string()))
            .unwrap_or_default();
        assert!(msg.contains("attempt"), "must name the channel: {msg}");
        assert!(msg.contains("MOD-031"), "must cite MOD-031: {msg}");
    }

    // ============================================================
    //  build_local_name_map — author-local → composed lookup map
    //  used by binding-side action contexts for ctx.output("X")
    //  fallback after the rewriter renames "X" to a composed name.
    // ============================================================

    #[test]
    fn build_local_name_map_empty_remap_no_prev_returns_none() {
        let p = Place::<i32>::new("in");
        let t = Transition::builder("t").input(one(&p)).build();
        let remap: HashMap<Arc<str>, PlaceRef> = HashMap::new();
        let substituted = substitute_places(&t, &remap);
        assert!(
            substituted.local_name_map().is_none(),
            "no-op rewrite must not allocate a local_name_map"
        );
    }

    #[test]
    fn build_local_name_map_first_pass_captures_author_local_names() {
        let in_p = Place::<i32>::new("in");
        let out_p = Place::<i32>::new("out");
        let t = Transition::builder("t")
            .input(one(&in_p))
            .output(out_place(&out_p))
            .build();

        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("in"), PlaceRef::new("host/in"));
        remap.insert(Arc::<str>::from("out"), PlaceRef::new("host/out"));

        let substituted = substitute_places(&t, &remap);
        let map = substituted
            .local_name_map()
            .expect("rewrite must populate local_name_map");
        assert_eq!(map.len(), 2);
        assert_eq!(&**map.get("in").unwrap(), "host/in");
        assert_eq!(&**map.get("out").unwrap(), "host/out");
    }

    #[test]
    fn build_local_name_map_skips_identity_passthroughs() {
        let stays = Place::<i32>::new("stays");
        let renamed = Place::<i32>::new("renamed");
        let t = Transition::builder("t")
            .input(one(&stays))
            .input(one(&renamed))
            .build();

        // Only `renamed` is in remap. `stays` must not appear in the map.
        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("renamed"), PlaceRef::new("host/renamed"));

        let substituted = substitute_places(&t, &remap);
        let map = substituted
            .local_name_map()
            .expect("renamed entry must populate map");
        assert_eq!(map.len(), 1, "identity passthrough must not be recorded");
        assert!(
            !map.contains_key("stays"),
            "identity-passthrough name leaked into map: {map:?}"
        );
        assert_eq!(&**map.get("renamed").unwrap(), "host/renamed");
    }

    #[test]
    fn build_local_name_map_chained_compose_keeps_only_author_local_keys() {
        // Regression: a second substitute_places pass used to leak the
        // first-pass composed name (the arc's then-current name) into
        // the map as an additional key, so a chained compose ended up
        // with both `author_local → final` AND `intermediate → final`
        // entries. Only the author-original key may appear.
        let p = Place::<i32>::new("X");
        let t = Transition::builder("t").input(one(&p)).build();

        let mut remap1 = HashMap::new();
        remap1.insert(Arc::<str>::from("X"), PlaceRef::new("inst/X"));
        let pass1 = substitute_places(&t, &remap1);
        let pass1_map = pass1.local_name_map().expect("pass-1 map");
        assert_eq!(pass1_map.len(), 1);
        assert_eq!(&**pass1_map.get("X").unwrap(), "inst/X");

        let mut remap2 = HashMap::new();
        remap2.insert(Arc::<str>::from("inst/X"), PlaceRef::new("host/X"));
        let pass2 = substitute_places(&pass1, &remap2);
        let pass2_map = pass2.local_name_map().expect("pass-2 map");
        assert_eq!(
            pass2_map.len(),
            1,
            "chained compose must not leak intermediate names: {pass2_map:?}"
        );
        assert_eq!(
            &**pass2_map.get("X").unwrap(),
            "host/X",
            "author-local must chain through to final composed name"
        );
        assert!(
            !pass2_map.contains_key("inst/X"),
            "intermediate-pass name must not appear as a key: {pass2_map:?}"
        );
    }

    #[test]
    fn build_local_name_map_chained_compose_drops_entry_when_final_equals_local() {
        // If a prior pass mapped X → host/X and a second remap rewrites
        // host/X back to X, the chained entry would be X → X (a no-op).
        // It is dropped so the map stays minimal.
        let p = Place::<i32>::new("X");
        let t = Transition::builder("t").input(one(&p)).build();

        let mut remap1 = HashMap::new();
        remap1.insert(Arc::<str>::from("X"), PlaceRef::new("inst/X"));
        let pass1 = substitute_places(&t, &remap1);

        let mut remap2 = HashMap::new();
        remap2.insert(Arc::<str>::from("inst/X"), PlaceRef::new("X"));
        let pass2 = substitute_places(&pass1, &remap2);
        assert!(
            pass2.local_name_map().is_none(),
            "X → X identity must collapse the map to None"
        );
    }

    #[test]
    fn build_local_name_map_walks_output_tree_and_xor_and_timeout() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let c = Place::<i32>::new("c");
        let nested = and(vec![
            xor(vec![out_place(&a), timeout(50, out_place(&b))]),
            out_place(&c),
        ]);
        let t = Transition::builder("t").output(nested).build();

        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("a"), PlaceRef::new("h/a"));
        remap.insert(Arc::<str>::from("b"), PlaceRef::new("h/b"));
        remap.insert(Arc::<str>::from("c"), PlaceRef::new("h/c"));

        let substituted = substitute_places(&t, &remap);
        let map = substituted
            .local_name_map()
            .expect("output-tree walk must populate map");
        assert_eq!(map.len(), 3);
        assert_eq!(&**map.get("a").unwrap(), "h/a");
        assert_eq!(&**map.get("b").unwrap(), "h/b");
        assert_eq!(&**map.get("c").unwrap(), "h/c");
    }

    #[test]
    fn build_local_name_map_covers_inhibitor_read_reset_arcs() {
        let inh = Place::<i32>::new("inh");
        let rd = Place::<i32>::new("rd");
        let rs = Place::<i32>::new("rs");
        let t = Transition::builder("t")
            .inhibitor(inhibitor(&inh))
            .read(read(&rd))
            .reset(reset(&rs))
            .build();

        let mut remap = HashMap::new();
        remap.insert(Arc::<str>::from("inh"), PlaceRef::new("h/inh"));
        remap.insert(Arc::<str>::from("rd"), PlaceRef::new("h/rd"));
        remap.insert(Arc::<str>::from("rs"), PlaceRef::new("h/rs"));

        let substituted = substitute_places(&t, &remap);
        let map = substituted
            .local_name_map()
            .expect("all arc kinds must contribute");
        assert_eq!(map.len(), 3);
        assert_eq!(&**map.get("inh").unwrap(), "h/inh");
        assert_eq!(&**map.get("rd").unwrap(), "h/rd");
        assert_eq!(&**map.get("rs").unwrap(), "h/rs");
    }

    #[test]
    fn channel_merge_passthrough_singleton_identity() {
        // The passthrough() function returns the singleton; this is the
        // mechanism compose_actions uses to detect "no-op default" — verify
        // the singleton invariant explicitly.
        let a = crate::action::passthrough();
        let b = crate::action::passthrough();
        assert!(
            Arc::ptr_eq(&a, &b),
            "passthrough() must return the singleton — Arc::ptr_eq should hold"
        );
    }
}
