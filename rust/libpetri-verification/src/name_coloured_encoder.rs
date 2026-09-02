//! Bounded **name-coloured** CHC encoding for ν-net join correlation
//! ([NU-050] #1, Route A — the EUF-style carve-out).
//!
//! The flat [`crate::smt_encoder`] is a pure *counting* abstraction: a place is
//! one integer, and a matched (ν-join) transition is encoded name-blind — it
//! fires whenever the input *counts* allow, regardless of whether the consumed
//! tokens actually share a correlation name. That over-approximation is sound
//! for `Proven` on reachability-safety bounds but can report a **spurious**
//! `Violated` whose counterexample silently equates two *distinct* names.
//!
//! This module removes that imprecision for the bounded fragment. The decidability
//! lever ([NU-040]) is a bounded live-name count: a budget place gates minting, and a
//! non-negative **P-semiflow** weighting every coloured place bounds the
//! simultaneously-live names to a finite `k` (`Σ_{coloured} M ≤ y·M0`; see
//! [`build_plan`] / `colour_slot_bound`). So names are modelled as a **finite set of
//! `k` colours**. Each coloured
//! place becomes `k` per-colour integer counts; a mint introduces a *globally
//! fresh* colour (one currently empty everywhere); a matched join consumes the
//! **same colour** from every correlated input. Within the budget bound the
//! encoding is *exact* — sound and complete — so no different-name counterexample
//! survives.
//!
//! ## Supported fragment
//!
//! [`build_plan`] returns `None` (and the verifier falls back to the sound
//! over-approximation) unless the net is in the budget-bounded coloured fragment:
//! - coloured places = the correlated inputs of every matched transition, plus (in
//!   EXTENDED mode, [NU-051]) the declared carrier places;
//! - each coloured place is *produced only by* minting forks (count 1, no coloured
//!   input, costs ≥1 budget token) or EXTENDED relays, and *consumed only by*
//!   matched joins or EXTENDED coloured consumers — a relay threads one colour on, a
//!   drain drops it, each consuming exactly one coloured input at count 1;
//! - the coloured place set is structurally token-bounded: some non-negative
//!   P-semiflow weights every coloured place, so the simultaneously-live colour count
//!   is bounded by that semiflow's initial value `k` (`Σ_{coloured} M ≤ y·M0`). A net
//!   with no covering non-negative semiflow (an unbounded colour leak) falls back;
//! - coloured places start empty; no inhibitor/read/reset/consume-all arc touches a
//!   coloured place.
//!
//! XOR output branches are supported ([NU-053], Part 3): each branch is a separate
//! flat row classified by its own incidence, with `match_spec` read from its source.
//!
//! ## Properties
//!
//! Reachability-safety properties compare aggregate coloured place counts.
//! Quiescence properties (`DeadlockFree`, `JoinedOrDeadLettered`) use a colour-aware
//! deadlock predicate ([NU-053], Part 2): every transition is disabled for every
//! colour (a mint has no globally-fresh colour, a join no shared colour, a consumer
//! no resident colour) and the marking is not a sink state — mirroring the flat
//! [`crate::smt_encoder`] deadlock with the same env-injection relaxation.

use std::collections::HashSet;

use libpetri_core::output;
use libpetri_core::petri_net::PetriNet;
use libpetri_core::transition::Transition;

use crate::marking_state::MarkingState;
use crate::name_fragment::FragmentMode;
use crate::net_flattener::{FlatNet, FlatTransition};
use crate::p_invariant::PInvariant;
use crate::property::SmtProperty;
use crate::smt_encoder::SmtEncoding;

/// How a transition relates to the coloured (correlation-carrying) places.
enum Class {
    /// Minting fork: produces a freshly-coloured token into each listed place.
    Mint { coloured_out: Vec<usize> },
    /// Matched join: consumes one same-coloured token from each listed place.
    Join { coloured_in: Vec<usize> },
    /// EXTENDED coloured consumer ([NU-051]): a non-match transition that consumes
    /// one same-coloured token from `input_col` (count 1) and threads it into each
    /// `coloured_out` (relay) or into none (drain — `coloured_out` empty).
    Consume {
        input_col: usize,
        coloured_out: Vec<usize>,
    },
    /// Touches no coloured place — a pure counting transition.
    Untouched,
}

/// A validated plan for the name-coloured encoding of a budget-bounded ν-net.
pub struct ColouredPlan {
    /// Flat indices of the coloured places (sorted ascending).
    pub coloured: Vec<usize>,
    /// Per flat place: whether it is coloured.
    is_coloured: Vec<bool>,
    /// Colour bound — the number of simultaneously-live names (= initial budget).
    pub k: usize,
    /// Classification, one entry per flat transition (XOR branches included).
    classes: Vec<Class>,
}

/// Detects whether `net` is in the supported budget-bounded coloured fragment
/// (mint→matched-join, plus the EXTENDED coloured consumers and carrier places of
/// [NU-051], with XOR-expanded output branches) and, if so, returns the plan for
/// [`encode_coloured`]. Returns `None` otherwise — the verifier then uses the sound
/// over-approximation.
/// Sound colour-slot bound `k`: a colour is live iff some coloured place holds it, so
/// `#live colours ≤ Σ_{coloured} M(p) ≤ y·M0` for any non-negative P-semiflow `y`
/// (`y·C = 0`, `y ≥ 0`) that weights every coloured place `≥ 1`. Returns the tightest
/// such `y·M0` (each `PInvariant.constant` is `y·M0`), or `None` when no covering
/// non-negative semiflow exists — the coloured set is then not structurally
/// token-bounded (a genuine unbounded colour leak) and the caller must fall back.
///
/// `0` is a bound like any other ([NU-053] AC6): with the covering law's initial sum
/// at zero no coloured token can ever exist, every mint / join / consumer is dead on
/// the reachable set, and the zero-slot plan is exact (`Semiflow.lean`,
/// `vacuous_colour_layer`). A validated semi-positive law's `y·M0` is never negative.
fn colour_slot_bound(coloured: &[usize], invariants: &[PInvariant]) -> Option<usize> {
    let w = |inv: &PInvariant, pid: usize| inv.weights.get(pid).copied().unwrap_or(0);
    let is_semiflow = |inv: &PInvariant| inv.weights.iter().all(|&x| x >= 0);

    // Tightest bound: a single non-negative P-semiflow weighting every coloured place.
    let single = invariants
        .iter()
        .filter(|inv| {
            is_semiflow(inv) && coloured.iter().all(|&pid| w(inv, pid) >= 1)
        })
        .map(|inv| inv.constant)
        .min();
    if let Some(c) = single {
        return Some(c as usize);
    }

    // Otherwise sum non-negative semiflows that touch a coloured place — the sum is
    // itself a valid non-negative P-semiflow, so `Σ y·M0` over any covering set is a
    // sound (looser) bound. Zero-constant semiflows cover their places for free, so
    // they go in first; a semiflow with a positive constant is added only if it
    // touches a coloured place the free ones left uncovered (decided against that
    // snapshot, so the result does not depend on enumeration order). If some
    // coloured place stays at weight 0 across all of them, no non-negative semiflow
    // covers it, so the coloured set is not structurally token-bounded → None
    // (sound over-approximation).
    let semiflows: Vec<&PInvariant> = invariants.iter().filter(|inv| is_semiflow(inv)).collect();
    let mut covered = vec![false; coloured.len()];
    for inv in semiflows.iter().filter(|inv| inv.constant == 0) {
        for (i, &pid) in coloured.iter().enumerate() {
            if w(inv, pid) >= 1 {
                covered[i] = true;
            }
        }
    }
    let free = covered.clone();
    let mut sum_const = 0i64;
    for inv in semiflows.iter().filter(|inv| inv.constant != 0) {
        let touches_uncovered = coloured
            .iter()
            .enumerate()
            .any(|(i, &pid)| !free[i] && w(inv, pid) >= 1);
        if !touches_uncovered {
            continue;
        }
        for (i, &pid) in coloured.iter().enumerate() {
            if w(inv, pid) >= 1 {
                covered[i] = true;
            }
        }
        sum_const += inv.constant;
    }
    if covered.iter().all(|&c| c) {
        Some(sum_const as usize)
    } else {
        None
    }
}

pub fn build_plan(
    net: &PetriNet,
    flat: &FlatNet,
    initial: &MarkingState,
    budget_places: &HashSet<String>,
    fragment_mode: FragmentMode,
    carrier_places: &HashSet<String>,
    invariants: &[PInvariant],
) -> Option<ColouredPlan> {
    let p = flat.place_count;

    // Map each flat row back to its source net transition. An XOR transition expands
    // to one flat row per output branch (no 1:1 net↔flat assumption), so we read
    // `match_spec` from the source while classifying by the flat row's own incidence.
    let mut source: Vec<&Transition> = Vec::with_capacity(flat.transitions.len());
    for t in net.transitions() {
        let rows = match t.output_spec() {
            Some(out) => output::enumerate_branches(out).len().max(1),
            None => 1,
        };
        for _ in 0..rows {
            source.push(t);
        }
    }
    if source.len() != flat.transitions.len() {
        // Flattener and branch enumeration disagree — fall back defensively.
        return None;
    }

    // 1. Coloured places = every matched transition's correlated inputs, plus (in
    //    EXTENDED mode) the declared carrier places that thread a fork-minted name
    //    through intermediate places to a ν-join input ([NU-051]).
    let mut is_coloured = vec![false; p];
    for t in net.transitions() {
        if let Some(ms) = t.match_spec() {
            for key in ms.keys() {
                let &pid = flat.place_index.get(key.place_name())?;
                is_coloured[pid] = true;
            }
        }
    }
    if fragment_mode == FragmentMode::Extended {
        for c in carrier_places {
            if let Some(&pid) = flat.place_index.get(c) {
                is_coloured[pid] = true;
            }
        }
    }
    let coloured: Vec<usize> = (0..p).filter(|&i| is_coloured[i]).collect();
    if coloured.is_empty() {
        return None;
    }

    // Coloured places must start empty — we do not model an initial colour
    // assignment for pre-seeded tokens.
    for &pid in &coloured {
        if initial.count(&flat.places[pid]) != 0 {
            return None;
        }
    }

    // Colour-slot bound k: a colour is live iff some coloured place holds it, so
    // `#live colours ≤ Σ_{coloured} M(p) ≤ y·M0` for any non-negative P-semiflow `y`
    // weighting every coloured place `≥ 1`. `k` is the tightest such `y·M0` (each
    // `PInvariant.constant` is `y·M0`); any `k ≥ #live` is sound — a larger k only
    // costs O(k) columns, never under-approximates, since a mint may take any free
    // slot behind the freshness guard. If no covering non-negative semiflow exists the
    // coloured set is not structurally token-bounded (a genuine unbounded colour leak),
    // so fall back to the sound over-approximation. This replaces the old budget-count
    // `k` and both structural discipline checks (atomic-rejoin + budget-Φ) below.
    let Some(k) = colour_slot_bound(&coloured, invariants) else {
        return None;
    };
    // [NU-053] AC6: `k = 0` is an exact plan — no coloured token can ever exist, so
    // every mint / join / consumer is dead and the zero-slot encoding emits no rule
    // for them (`Semiflow.lean`, `vacuous_colour_layer`). The one shape it cannot
    // encode is a net with no uncoloured place at all: `Reachable` would be nullary
    // and every rule's `forall` binder list empty. Such a net holds no token at
    // `M0` (coloured places start empty), so fall back to the flat encoding.
    if k == 0 && coloured.len() == p {
        return None;
    }

    // Budget places gate minting: a mint must consume ≥1 budget token — that is what
    // makes it a fresh-name fork rather than an arbitrary coloured producer.
    let budget_idx: HashSet<usize> = budget_places
        .iter()
        .filter_map(|n| flat.place_index.get(n).copied())
        .collect();

    // No inhibitor/read/reset/consume-all arc may touch a coloured place.
    for ft in &flat.transitions {
        let touches_coloured = ft
            .inhibitor_places
            .iter()
            .chain(&ft.read_places)
            .chain(&ft.reset_places)
            .chain(&ft.consume_all)
            .any(|&pid| is_coloured[pid]);
        if touches_coloured {
            return None;
        }
    }

    // 2. Classify each flat row from its own incidence (match_spec from its source).
    let mut classes = Vec::with_capacity(flat.transitions.len());
    for (&t, ft) in source.iter().zip(&flat.transitions) {
        let coloured_in: Vec<usize> = coloured
            .iter()
            .copied()
            .filter(|&pid| ft.pre[pid] > 0)
            .collect();
        let coloured_out: Vec<usize> = coloured
            .iter()
            .copied()
            .filter(|&pid| ft.post[pid] > 0)
            .collect();

        let class = if t.match_spec().is_some() {
            // Matched join: consumes coloured inputs (count 1), produces none.
            if !coloured_out.is_empty() || coloured_in.is_empty() {
                return None;
            }
            if coloured_in.iter().any(|&pid| ft.pre[pid] != 1) {
                return None;
            }
            Class::Join { coloured_in }
        } else if !coloured_in.is_empty() {
            // EXTENDED coloured consumer (relay/drain, [NU-051]): a non-match
            // transition consuming a coloured place. Admitted only in EXTENDED mode,
            // and only when it consumes EXACTLY ONE coloured input at count EXACTLY
            // ONE (higher counts would over-count the name layer against the base
            // marking's single token per place). It relays the name into its coloured
            // outputs (each at count 1) or drains it (no coloured output).
            if fragment_mode != FragmentMode::Extended {
                return None;
            }
            if coloured_in.len() != 1 || ft.pre[coloured_in[0]] != 1 {
                return None;
            }
            if coloured_out.iter().any(|&pid| ft.post[pid] != 1) {
                return None;
            }
            Class::Consume {
                input_col: coloured_in[0],
                coloured_out,
            }
        } else if !coloured_out.is_empty() {
            // Minting fork: produces coloured (count 1), consumes none, and must consume
            // ≥1 budget token — that is what makes it a fresh-name fork rather than an
            // arbitrary coloured producer. (Boundedness is decided by the colour-slot
            // bound above, not here.)
            if coloured_out.iter().any(|&pid| ft.post[pid] != 1) {
                return None;
            }
            let budget_consumed: i64 = budget_idx.iter().map(|&b| ft.pre[b]).sum();
            if budget_consumed < 1 {
                return None;
            }
            Class::Mint { coloured_out }
        } else {
            // Touches no coloured place at all.
            Class::Untouched
        };
        classes.push(class);
    }

    Some(ColouredPlan {
        coloured,
        is_coloured,
        k,
        classes,
    })
}

/// Column layout over the coloured state vector: uncoloured place → one var,
/// coloured place → `k` per-colour vars.
struct Layout {
    /// Column index of each uncoloured place (`usize::MAX` if coloured).
    col_unc: Vec<usize>,
    /// Per coloured place: its `k` column indices (empty if uncoloured).
    col_col: Vec<Vec<usize>>,
    /// Current-marking variable names, one per column.
    cur: Vec<String>,
    /// Next-marking variable names, one per column.
    nxt: Vec<String>,
}

impl Layout {
    fn build(plan: &ColouredPlan, p: usize) -> Self {
        let mut col_unc = vec![usize::MAX; p];
        let mut col_col: Vec<Vec<usize>> = vec![Vec::new(); p];
        let mut cur = Vec::new();
        let mut nxt = Vec::new();
        for i in 0..p {
            if plan.is_coloured[i] {
                let mut idxs = Vec::with_capacity(plan.k);
                for c in 0..plan.k {
                    idxs.push(cur.len());
                    cur.push(format!("m{i}_{c}"));
                    nxt.push(format!("m{i}_{c}p"));
                }
                col_col[i] = idxs;
            } else {
                col_unc[i] = cur.len();
                cur.push(format!("m{i}"));
                nxt.push(format!("m{i}p"));
            }
        }
        Layout {
            col_unc,
            col_col,
            cur,
            nxt,
        }
    }

    /// Aggregate token-count expression for a place over the given var-set
    /// (`cur` or `nxt`): the single uncoloured var, or the sum of its colours.
    fn aggregate(&self, place: usize, plan: &ColouredPlan, vars: &[String]) -> String {
        if plan.is_coloured[place] {
            let parts: Vec<&str> = self.col_col[place].iter().map(|&c| vars[c].as_str()).collect();
            match parts.len() {
                // `k = 0`: a coloured place has no slot and never holds a token.
                0 => "0".to_string(),
                1 => parts[0].to_string(),
                _ => format!("(+ {})", parts.join(" ")),
            }
        } else {
            vars[self.col_unc[place]].clone()
        }
    }
}

/// Encodes the supported ν-net as bounded name-coloured CHC for Z3 Spacer.
///
/// The HORN/Spacer convention matches [`crate::smt_encoder`]: with the query
/// `(assert (not Error))`, `sat` ⇒ property PROVEN, `unsat` ⇒ VIOLATED.
/// Returns `None` when the property names a place that does not resolve in the
/// net (see [`encode_violation`]); the verifier reports `Unknown` rather than
/// certify a vacuous `Proven`.
pub fn encode_coloured(
    plan: &ColouredPlan,
    flat: &FlatNet,
    initial: &MarkingState,
    property: &SmtProperty,
    invariants: &[PInvariant],
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
) -> Option<SmtEncoding> {
    let p = flat.place_count;
    let k = plan.k;
    let lay = Layout::build(plan, p);
    let n_cols = lay.cur.len();

    let mut lines = Vec::new();
    lines.push("(set-logic HORN)".to_string());
    lines.push(String::new());

    let int_params = (0..n_cols).map(|_| "Int").collect::<Vec<_>>().join(" ");
    lines.push(format!("(declare-fun Reachable ({int_params}) Bool)"));
    lines.push("(declare-fun Error () Bool)".to_string());
    lines.push(String::new());

    // Init: uncoloured places carry their initial count; coloured start empty.
    let init: Vec<String> = (0..p)
        .flat_map(|i| {
            if plan.is_coloured[i] {
                vec!["0".to_string(); k]
            } else {
                vec![initial.count(&flat.places[i]).to_string()]
            }
        })
        .collect();
    lines.push(format!("(assert (Reachable {}))", init.join(" ")));
    lines.push(String::new());

    // Transition rules.
    for (ti, cls) in plan.classes.iter().enumerate() {
        let ft = &flat.transitions[ti];
        match cls {
            Class::Untouched => {
                lines.push(encode_rule(plan, &lay, invariants, |enab, upd| {
                    uncoloured_incidence(&lay, plan, ft, enab, upd);
                }));
            }
            Class::Mint { coloured_out } => {
                for c in 0..k {
                    lines.push(encode_rule(plan, &lay, invariants, |enab, upd| {
                        uncoloured_incidence(&lay, plan, ft, enab, upd);
                        // Globally fresh colour: c must be empty in every coloured place.
                        for &q in &plan.coloured {
                            enab.push(format!("(= {} 0)", lay.cur[lay.col_col[q][c]]));
                        }
                        for &o in coloured_out {
                            let col = lay.col_col[o][c];
                            upd.push((col, format!("(+ {} 1)", lay.cur[col])));
                        }
                    }));
                }
            }
            Class::Join { coloured_in } => {
                for c in 0..k {
                    lines.push(encode_rule(plan, &lay, invariants, |enab, upd| {
                        uncoloured_incidence(&lay, plan, ft, enab, upd);
                        // Same colour c present in every correlated input.
                        for &ip in coloured_in {
                            let col = lay.col_col[ip][c];
                            enab.push(format!("(>= {} 1)", lay.cur[col]));
                            upd.push((col, format!("(- {} 1)", lay.cur[col])));
                        }
                    }));
                }
            }
            Class::Consume {
                input_col,
                coloured_out,
            } => {
                // One rule per colour: consume colour c from the single coloured
                // input and thread it into each coloured output (relay), or into none
                // (drain).
                for c in 0..k {
                    lines.push(encode_rule(plan, &lay, invariants, |enab, upd| {
                        uncoloured_incidence(&lay, plan, ft, enab, upd);
                        let icol = lay.col_col[*input_col][c];
                        enab.push(format!("(>= {} 1)", lay.cur[icol]));
                        upd.push((icol, format!("(- {} 1)", lay.cur[icol])));
                        for &o in coloured_out {
                            let ocol = lay.col_col[o][c];
                            upd.push((ocol, format!("(+ {} 1)", lay.cur[ocol])));
                        }
                    }));
                }
            }
        }
    }
    lines.push(String::new());

    // Error rule. `None` ⇒ the property names an unresolved place; refuse to
    // build a vacuously-provable encoding and let the verifier report Unknown.
    lines.push(encode_error(plan, &lay, flat, property, sink_places, env_inject)?);
    lines.push(String::new());
    lines.push("(assert (not Error))".to_string());
    lines.push("(check-sat)".to_string());

    Some(SmtEncoding {
        smt2: lines.join("\n"),
        place_count: p,
    })
}

/// Pushes the enablement guards and column updates contributed by a transition's
/// **uncoloured** incidence (consume/produce on non-coloured places). Coloured
/// columns are handled by the caller (mint produces, join consumes).
fn uncoloured_incidence(
    lay: &Layout,
    plan: &ColouredPlan,
    ft: &crate::net_flattener::FlatTransition,
    enab: &mut Vec<String>,
    upd: &mut Vec<(usize, String)>,
) {
    let p = ft.pre.len();
    for i in 0..p {
        if plan.is_coloured[i] {
            continue;
        }
        let col = lay.col_unc[i];
        if ft.pre[i] > 0 {
            enab.push(format!("(>= {} {})", lay.cur[col], ft.pre[i]));
        }
        if ft.reset_places.contains(&i) || ft.consume_all.contains(&i) {
            upd.push((col, ft.post[i].to_string()));
        } else {
            let delta = ft.post[i] - ft.pre[i];
            if delta > 0 {
                upd.push((col, format!("(+ {} {})", lay.cur[col], delta)));
            } else if delta < 0 {
                upd.push((col, format!("(- {} {})", lay.cur[col], -delta)));
            }
        }
    }
    // Inhibitor / read arcs (all on uncoloured places — checked in build_plan).
    for &pid in &ft.inhibitor_places {
        enab.push(format!("(= {} 0)", lay.cur[lay.col_unc[pid]]));
    }
    for &pid in &ft.read_places {
        enab.push(format!("(>= {} 1)", lay.cur[lay.col_unc[pid]]));
    }
}

/// Builds one transition CHC rule. `fill` contributes the enablement guards and
/// the changed-column updates; every other column is copied unchanged, changed
/// columns get a non-negativity guard, and the (lifted) P-invariants constrain
/// the successor.
fn encode_rule(
    plan: &ColouredPlan,
    lay: &Layout,
    invariants: &[PInvariant],
    fill: impl FnOnce(&mut Vec<String>, &mut Vec<(usize, String)>),
) -> String {
    let mut enab = Vec::new();
    let mut upd: Vec<(usize, String)> = Vec::new();
    fill(&mut enab, &mut upd);

    let all_vars: String = lay
        .cur
        .iter()
        .chain(lay.nxt.iter())
        .map(|v| format!("({v} Int)"))
        .collect::<Vec<_>>()
        .join(" ");

    let mut conditions = Vec::new();
    conditions.push(format!("(Reachable {})", lay.cur.join(" ")));
    conditions.extend(enab);

    // Index the updates by column (the columns are a small contiguous range, so a
    // Vec is cheaper and more cache-friendly than a HashMap). A changed column
    // gets its update expression + a non-negativity guard; every other column is
    // copied unchanged.
    let mut changed: Vec<Option<String>> = vec![None; lay.cur.len()];
    for (col, expr) in upd {
        changed[col] = Some(expr);
    }
    for col in 0..lay.cur.len() {
        if let Some(expr) = &changed[col] {
            conditions.push(format!("(= {} {})", lay.nxt[col], expr));
            conditions.push(format!("(>= {} 0)", lay.nxt[col]));
        } else {
            conditions.push(format!("(= {} {})", lay.nxt[col], lay.cur[col]));
        }
    }

    for inv in invariants {
        if let Some(eq) = lifted_invariant(inv, plan, lay, &lay.nxt) {
            conditions.push(eq);
        }
    }

    let body = format!("(and {})", conditions.join("\n            "));
    format!(
        "(assert (forall ({all_vars})\n  (=> {body}\n      (Reachable {}))))",
        lay.nxt.join(" ")
    )
}

/// Lifts a flat P-invariant to the coloured layout: a coloured place's variable
/// becomes the sum of its colours (= its aggregate count), so the (true) flat
/// invariant constrains the coloured successor without excluding any reachable
/// state.
fn lifted_invariant(
    inv: &PInvariant,
    plan: &ColouredPlan,
    lay: &Layout,
    vars: &[String],
) -> Option<String> {
    let terms: Vec<String> = inv
        .support
        .iter()
        .map(|&i| {
            let agg = lay.aggregate(i, plan, vars);
            if inv.weights[i] == 1 {
                agg
            } else {
                format!("(* {} {})", inv.weights[i], agg)
            }
        })
        .collect();
    if terms.is_empty() {
        return None;
    }
    let sum = if terms.len() == 1 {
        terms[0].clone()
    } else {
        format!("(+ {})", terms.join(" "))
    };
    Some(format!("(= {} {})", sum, inv.constant))
}

/// Encodes the error rule: a reachable marking that violates the property.
///
/// Returns `None` when the property names an unresolved place (see
/// [`encode_violation`]) — the caller must then report `Unknown` rather than
/// build a vacuously-satisfiable encoding.
fn encode_error(
    plan: &ColouredPlan,
    lay: &Layout,
    flat: &FlatNet,
    property: &SmtProperty,
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
) -> Option<String> {
    let all_vars: String = lay
        .cur
        .iter()
        .map(|v| format!("({v} Int)"))
        .collect::<Vec<_>>()
        .join(" ");
    let violation = encode_violation(plan, lay, flat, property, sink_places, env_inject)?;
    Some(format!(
        "(assert (forall ({all_vars})\n  (=> (and (Reachable {}) {violation})\n      Error)))",
        lay.cur.join(" ")
    ))
}

/// Encodes the property-violation condition over the coloured current marking.
/// Reachability-safety properties compare aggregate place counts; quiescence
/// properties ([NU-053]) use the colour-aware deadlock predicate.
///
/// Returns `None` when the property names a place that does not resolve in the
/// net (e.g. a typo'd bound/pending place). Emitting a `false` violation term
/// there would make the Error rule unsatisfiable and yield a **vacuous**
/// `Proven` — a mis-named place would silently certify. `None` propagates up so
/// the verifier reports `Unknown` instead of certifying nothing.
fn encode_violation(
    plan: &ColouredPlan,
    lay: &Layout,
    flat: &FlatNet,
    property: &SmtProperty,
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
) -> Option<String> {
    let any_place_present = |names: &[String]| -> String {
        let conds: Vec<String> = names
            .iter()
            .filter_map(|n| flat.place_index.get(n))
            .map(|&pid| format!("(>= {} 1)", lay.aggregate(pid, plan, &lay.cur)))
            .collect();
        if conds.is_empty() {
            "false".to_string()
        } else {
            format!("(and {})", conds.join(" "))
        }
    };

    match property {
        SmtProperty::PlaceBound { place, bound }
        | SmtProperty::BranchPlaceBound { place, bound } => match flat.place_index.get(place) {
            Some(&pid) => Some(format!("(> {} {})", lay.aggregate(pid, plan, &lay.cur), bound)),
            None => None,
        },
        SmtProperty::Unreachable { places } | SmtProperty::MutualExclusion { places } => {
            Some(any_place_present(places))
        }
        SmtProperty::DeadlockFree => {
            Some(encode_coloured_deadlock(plan, lay, flat, sink_places, env_inject))
        }
        SmtProperty::JoinedOrDeadLettered { pending } => match flat.place_index.get(pending) {
            Some(&pid) => {
                let deadlock = encode_coloured_deadlock(plan, lay, flat, sink_places, env_inject);
                Some(format!(
                    "(and {deadlock} (>= {} 1))",
                    lay.aggregate(pid, plan, &lay.cur)
                ))
            }
            None => None,
        },
    }
}

/// Env-injectable bound for a place: `Some(bound)` if the place accepts external
/// injection (`bound = None` unbounded, `Some(k)` capped at k), else `None`.
fn env_bound(pid: usize, env_inject: &[(usize, Option<usize>)]) -> Option<Option<usize>> {
    env_inject.iter().find(|&&(p, _)| p == pid).map(|&(_, b)| b)
}

/// The uncoloured disable reasons for a flat row: marking-dependent clauses (any one
/// true ⇒ the transition's uncoloured part is unmet), plus a flag that it is
/// permanently disabled (an env cap below the demand means it can never fire).
/// Coloured places are excluded — their enablement is the per-class colour term.
/// Mirrors [`crate::smt_encoder`]'s flat deadlock with the same env relaxation.
fn uncoloured_disable(
    ft: &FlatTransition,
    lay: &Layout,
    plan: &ColouredPlan,
    env_inject: &[(usize, Option<usize>)],
) -> (Vec<String>, bool) {
    let mut reasons = Vec::new();
    let mut permanently_disabled = false;
    for i in 0..ft.pre.len() {
        if plan.is_coloured[i] || ft.pre[i] == 0 {
            continue;
        }
        if let Some(bound) = env_bound(i, env_inject) {
            if matches!(bound, Some(k) if (ft.pre[i] as usize) > k) {
                permanently_disabled = true;
            }
            continue;
        }
        reasons.push(format!("(< {} {})", lay.cur[lay.col_unc[i]], ft.pre[i]));
    }
    for &inh in &ft.inhibitor_places {
        reasons.push(format!("(> {} 0)", lay.cur[lay.col_unc[inh]]));
    }
    for &rd in &ft.read_places {
        if let Some(bound) = env_bound(rd, env_inject) {
            if matches!(bound, Some(k) if k < 1) {
                permanently_disabled = true;
            }
            continue;
        }
        reasons.push(format!("(< {} 1)", lay.cur[lay.col_unc[rd]]));
    }
    (reasons, permanently_disabled)
}

/// The colour-specific "disabled for every colour" term for a class (`None` if the
/// class imposes no coloured enablement constraint). Combined by the caller with the
/// uncoloured disable reasons: the transition is disabled if EITHER holds.
fn coloured_disabled_term(cls: &Class, plan: &ColouredPlan, lay: &Layout) -> Option<String> {
    let k = plan.k;
    // `k = 0` ([NU-053] AC6): no colour can ever be present, so every coloured class
    // is disabled outright — the empty conjunctions below would otherwise render as
    // `(and )`, which is not SMT-LIB.
    if k == 0 {
        return match cls {
            Class::Untouched => None,
            _ => Some("true".to_string()),
        };
    }
    match cls {
        Class::Untouched => None,
        Class::Mint { .. } => {
            // No globally-fresh colour: for every colour c, some coloured place
            // already holds c.
            let per_colour: Vec<String> = (0..k)
                .map(|c| {
                    let present: Vec<String> = plan
                        .coloured
                        .iter()
                        .map(|&q| format!("(>= {} 1)", lay.cur[lay.col_col[q][c]]))
                        .collect();
                    format!("(or {})", present.join(" "))
                })
                .collect();
            Some(format!("(and {})", per_colour.join(" ")))
        }
        Class::Join { coloured_in } => {
            // No colour is shared by all correlated inputs: for every colour c, some
            // input lacks c.
            let per_colour: Vec<String> = (0..k)
                .map(|c| {
                    let missing: Vec<String> = coloured_in
                        .iter()
                        .map(|&i| format!("(= {} 0)", lay.cur[lay.col_col[i][c]]))
                        .collect();
                    format!("(or {})", missing.join(" "))
                })
                .collect();
            Some(format!("(and {})", per_colour.join(" ")))
        }
        Class::Consume { input_col, .. } => {
            // No colour present at the single coloured input.
            let per_colour: Vec<String> = (0..k)
                .map(|c| format!("(= {} 0)", lay.cur[lay.col_col[*input_col][c]]))
                .collect();
            Some(format!("(and {})", per_colour.join(" ")))
        }
    }
}

/// Colour-aware deadlock predicate ([NU-053]): every transition is disabled (no
/// colour enables it) and no declared sink place holds a token ([VER-002]). Mirrors
/// [`crate::smt_encoder`]'s flat `encode_deadlock` with the same env-injection
/// relaxation (VER-006), lifted to the coloured layout.
fn encode_coloured_deadlock(
    plan: &ColouredPlan,
    lay: &Layout,
    flat: &FlatNet,
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
) -> String {
    let mut disabled_conditions = Vec::new();
    for (ti, cls) in plan.classes.iter().enumerate() {
        let ft = &flat.transitions[ti];
        let (mut reasons, permanently_disabled) = uncoloured_disable(ft, lay, plan, env_inject);
        if permanently_disabled {
            // The transition can never fire — it is always "disabled".
            disabled_conditions.push("true".to_string());
            continue;
        }
        if let Some(term) = coloured_disabled_term(cls, plan, lay) {
            reasons.push(term);
        }
        if reasons.is_empty() {
            // Always enabled (possibly via injection) — no marking is a deadlock.
            return "false".to_string();
        }
        disabled_conditions.push(if reasons.len() == 1 {
            reasons.pop().unwrap()
        } else {
            format!("(or {})", reasons.join(" "))
        });
    }

    // Declared sinks ([VER-002]): quiescence is a violation only when NO declared
    // sink holds a token, so each declared sink contributes `aggregate(sink) = 0`
    // over its colour slots. Same predicate as the flat `encode_deadlock`.
    for name in sink_places {
        if let Some(&pid) = flat.place_index.get(name) {
            disabled_conditions.push(format!("(= {} 0)", lay.aggregate(pid, plan, &lay.cur)));
        }
    }

    if disabled_conditions.is_empty() {
        "true".to_string()
    } else {
        format!("(and {})", disabled_conditions.join(" "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use crate::net_flattener;
    use libpetri_core::action::fork;
    use libpetri_core::input::one;
    use libpetri_core::match_spec::MatchSpec;
    use libpetri_core::name::NameId;
    use libpetri_core::output::{and, out_place};
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    /// A budget-bounded mint→join net (same-mint scatter-gather): one mint
    /// consumes 1 budget and stamps the fresh colour into both correlated inputs;
    /// the join refunds 1 budget (conserving) or 2 (inflating, into a 2nd budget
    /// place). A MatchSpec must correlate ≥2 input places, hence two branches.
    fn mint_join_net(extra_refund: bool) -> PetriNet {
        let budget1 = Place::<()>::new("budget1");
        let budget2 = Place::<()>::new("budget2");
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");

        let mint = Transition::builder("mint")
            .input(one(&budget1))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .action(fork())
            .build();
        let join_out = if extra_refund {
            // Refund an EXTRA token to a non-minting place (budget2). The MINTING budget
            // (budget1) is still conserved, so at most one colour is ever live — the net
            // is colour-bounded and the P-semiflow bound admits it. (The old budget-Φ
            // heuristic wrongly rejected any refund exceeding the mint cost.)
            and(vec![out_place(&budget1), out_place(&budget2)])
        } else {
            out_place(&budget1)
        };
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(join_out)
            .action(fork())
            .build();
        PetriNet::builder("mint_join")
            .transitions([mint, join])
            .build()
    }

    /// A mint→join net plus an EXTENDED coloured drain: a non-match transition that
    /// consumes one correlated input `a` (count 1) into a plain sink. Rejected under
    /// BASE (a non-match consumer of a coloured place), admitted under EXTENDED.
    fn mint_join_drain_net() -> PetriNet {
        let budget1 = Place::<()>::new("budget1");
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let sink = Place::<String>::new("sink");

        let mint = Transition::builder("mint")
            .input(one(&budget1))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&budget1))
            .action(fork())
            .build();
        let drain = Transition::builder("drain")
            .input(one(&a))
            .output(out_place(&sink))
            .action(fork())
            .build();
        PetriNet::builder("mint_join_drain")
            .transitions([mint, join, drain])
            .build()
    }

    /// A mint→join net with an EXTENDED carrier relay: the fork co-mints into the
    /// carrier place `carrier` and the join input `b`; a relay threads `carrier`'s
    /// name into the other join input `a`; the join correlates `a` and `b`. `carrier`
    /// is coloured only when declared as a carrier place under EXTENDED. When
    /// `relay_refunds`, the relay also refunds budget — which must be rejected, since
    /// a relay keeps the colour live.
    fn mint_relay_join_net(relay_refunds: bool) -> PetriNet {
        let budget1 = Place::<()>::new("budget1");
        let carrier = Place::<String>::new("carrier");
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");

        let mint = Transition::builder("mint")
            .input(one(&budget1))
            .output(and(vec![out_place(&carrier), out_place(&b)]))
            .action(fork())
            .build();
        let relay_out = if relay_refunds {
            and(vec![out_place(&a), out_place(&budget1)])
        } else {
            out_place(&a)
        };
        let relay = Transition::builder("relay")
            .input(one(&carrier))
            .output(relay_out)
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&budget1))
            .action(fork())
            .build();
        PetriNet::builder("mint_relay_join")
            .transitions([mint, relay, join])
            .build()
    }

    /// A leaky fork ([NU-053] S2): the mint co-mints its colour into the join
    /// inputs `a`, `b` AND a declared carrier `c`, but the join only re-collects
    /// `a`, `b` and nothing ever consumes `c`. The colour outlives the budget the
    /// join refunds, so the real net can hold more than `k` live colours while the
    /// k-colour encoding gets stuck at the freshness guard — an under-approximation
    /// that could report a false `Proven`.
    fn mint_leaky_carrier_net() -> PetriNet {
        let budget1 = Place::<()>::new("budget1");
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let c = Place::<String>::new("c");

        let mint = Transition::builder("mint")
            .input(one(&budget1))
            .output(and(vec![out_place(&a), out_place(&b), out_place(&c)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&budget1))
            .action(fork())
            .build();
        PetriNet::builder("mint_leaky_carrier")
            .transitions([mint, join])
            .build()
    }

    fn plan_for(net: &PetriNet, mode: FragmentMode, carriers: &[&str]) -> Option<ColouredPlan> {
        plan_for_marking(
            net,
            mode,
            carriers,
            MarkingStateBuilder::new().tokens("budget1", 1).build(),
        )
    }

    fn plan_for_marking(
        net: &PetriNet,
        mode: FragmentMode,
        carriers: &[&str],
        initial: MarkingState,
    ) -> Option<ColouredPlan> {
        let flat = net_flattener::flatten(net);
        let budget: HashSet<String> =
            ["budget1".to_string(), "budget2".to_string()].into_iter().collect();
        let carrier_set: HashSet<String> = carriers.iter().map(|s| s.to_string()).collect();
        let matrix = crate::incidence_matrix::IncidenceMatrix::from_flat_net(&flat, &[]);
        // Same route the verifier takes: only exactly re-validated semiflows may
        // set the colour-slot bound (see `p_invariant::validate_invariants_exact`).
        let semiflows = crate::p_invariant::validate_invariants_exact(
            crate::p_invariant::compute_p_semiflows(&matrix, &initial, &flat.places),
            &matrix,
            &initial,
            &flat,
        )
        .valid;
        build_plan(net, &flat, &initial, &budget, mode, &carrier_set, &semiflows)
    }

    /// [NU-053] AC6: with no budget token the covering semiflow's initial sum is
    /// zero, and `k = 0` is an exact plan rather than a fallback — no coloured
    /// token can ever exist (`Semiflow.lean`, `vacuous_colour_layer`).
    #[test]
    fn zero_budget_yields_the_exact_zero_slot_plan() {
        let plan = plan_for_marking(
            &mint_join_net(false),
            FragmentMode::Base,
            &[],
            MarkingStateBuilder::new().build(),
        )
        .expect("k = 0 is a plan, not a fallback");
        assert_eq!(plan.k, 0);
    }

    #[test]
    fn budget_conserving_join_takes_exact_path() {
        // Refund (1) == mint cost (1): live names ≤ k, so the fragment is
        // accepted and the exact name-coloured encoding is used.
        assert!(plan_for(&mint_join_net(false), FragmentMode::Base, &[]).is_some());
    }

    #[test]
    fn budget_refund_to_nonminting_place_stays_bounded() {
        // [NU-053] A join that refunds an extra token to a NON-minting place keeps the
        // minting budget conserved, so at most one colour is live — the net is
        // colour-bounded and the P-semiflow bound admits it. (The old budget-Φ heuristic
        // wrongly rejected any refund exceeding the mint cost; genuine colour leaks —
        // where a co-minted place accumulates distinct colours — are covered by
        // `extended_leaky_carrier_fanout_rejected`, which still falls back.)
        assert!(plan_for(&mint_join_net(true), FragmentMode::Base, &[]).is_some());
    }

    #[test]
    fn extended_drain_rejected_under_base_admitted_under_extended() {
        // A non-match consumer of a coloured place is out-of-fragment under BASE and
        // admitted as a drain under EXTENDED.
        let net = mint_join_drain_net();
        assert!(plan_for(&net, FragmentMode::Base, &[]).is_none());
        assert!(plan_for(&net, FragmentMode::Extended, &[]).is_some());
    }

    #[test]
    fn extended_carrier_relay_admitted_only_under_extended() {
        // The carrier place is coloured only when declared under EXTENDED; then the
        // relay threading its name to the join input is an admitted Consume.
        let net = mint_relay_join_net(false);
        assert!(plan_for(&net, FragmentMode::Base, &[]).is_none());
        assert!(plan_for(&net, FragmentMode::Extended, &["carrier"]).is_some());
    }

    #[test]
    fn extended_relay_refunding_budget_rejected() {
        // A relay keeps the colour live; if it also refunded budget the freed token
        // could mint a (k+1)-th live colour. build_plan must reject it.
        let net = mint_relay_join_net(true);
        assert!(plan_for(&net, FragmentMode::Extended, &["carrier"]).is_none());
    }

    #[test]
    fn extended_leaky_carrier_fanout_rejected() {
        // [NU-053] S2: the mint fans its colour into a, b AND carrier c, but the
        // refunding join only re-collects a, b — c is never consumed, so the colour
        // outlives its refunded budget and the real net can hold more than k live
        // colours. build_plan must reject this (None → sound over-approximation)
        // rather than certify an exact plan the quiescence gate would trust for a
        // false `Proven`. Contrast extended_carrier_relay_admitted: there the fork's
        // carrier branch is relayed back into a join input (atomic re-collection).
        let net = mint_leaky_carrier_net();
        assert!(plan_for(&net, FragmentMode::Extended, &["c"]).is_none());
    }

    /// A mint→join net plus a plain XOR transition (uncoloured), which expands to two
    /// flat rows — exercising Part 3 (no 1:1 net↔flat assumption).
    fn mint_join_xor_net() -> PetriNet {
        let budget1 = Place::<()>::new("budget1");
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let s = Place::<()>::new("s");
        let x = Place::<()>::new("x");
        let y = Place::<()>::new("y");

        let mint = Transition::builder("mint")
            .input(one(&budget1))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |v: &String| NameId::new(v.clone()))
                    .key(&b, |v: &String| NameId::new(v.clone()))
                    .build(),
            )
            .output(out_place(&budget1))
            .action(fork())
            .build();
        let branch = Transition::builder("branch")
            .input(one(&s))
            .output(libpetri_core::output::xor(vec![out_place(&x), out_place(&y)]))
            .action(fork())
            .build();
        PetriNet::builder("mint_join_xor")
            .transitions([mint, join, branch])
            .build()
    }

    #[test]
    fn xor_transition_no_longer_blocks_the_coloured_plan() {
        // A plain XOR transition expands to two flat rows; Part 3 drops the old 1:1
        // net↔flat rejection so the mint→join fragment is still recognised.
        let net = mint_join_xor_net();
        assert!(plan_for(&net, FragmentMode::Base, &[]).is_some());
    }

    #[test]
    fn unresolved_property_place_yields_no_encoding() {
        // Should-fix: a property naming a place absent from the net must NOT
        // silently certify. `encode_coloured` returns None (→ the verifier reports
        // Unknown) instead of emitting a `false` violation term (a vacuous Proven).
        let net = mint_join_net(false);
        let flat = net_flattener::flatten(&net);
        let initial = MarkingStateBuilder::new().tokens("budget1", 1).build();
        let plan = plan_for(&net, FragmentMode::Base, &[]).expect("mint→join is in-fragment");

        // Typo'd pending place → no encoding.
        let bad = SmtProperty::JoinedOrDeadLettered {
            pending: "typo_pending".to_string(),
        };
        assert!(
            encode_coloured(&plan, &flat, &initial, &bad, &[], &[], &[]).is_none(),
            "unresolved pending place must not produce an encoding (would be vacuously Proven)"
        );

        // A resolvable place still encodes.
        let good = SmtProperty::JoinedOrDeadLettered {
            pending: "a".to_string(),
        };
        assert!(
            encode_coloured(&plan, &flat, &initial, &good, &[], &[], &[]).is_some(),
            "a resolvable pending place must still encode"
        );
    }
}
