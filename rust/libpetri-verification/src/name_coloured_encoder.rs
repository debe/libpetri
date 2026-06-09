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
//! This module removes that imprecision for the bounded fragment. The
//! decidability lever ([NU-040]) is the budget: with a `Budget` place pre-seeded
//! with `k` tokens gating every mint, at most `k` correlation names are live at
//! once. So names are modelled as a **finite set of `k` colours**. Each coloured
//! place becomes `k` per-colour integer counts; a mint introduces a *globally
//! fresh* colour (one currently empty everywhere); a matched join consumes the
//! **same colour** from every correlated input. Within the budget bound the
//! encoding is *exact* — sound and complete — so no different-name counterexample
//! survives.
//!
//! ## Supported fragment (tracer bullet)
//!
//! [`build_plan`] returns `None` (and the verifier falls back to the sound
//! over-approximation) unless the net is in the simple **mint → matched-join**
//! shape:
//! - coloured places = the correlated inputs of every matched transition;
//! - each coloured place is *produced only by* minting forks (count 1, no
//!   coloured input, costs ≥1 budget token) and *consumed only by* matched joins
//!   (count 1, produces no coloured token);
//! - budget places are consumed only by mints and produced only by joins (so
//!   live colours ≤ initial budget = `k`);
//! - coloured places start empty; no inhibitor/read/reset/consume-all arc touches
//!   a coloured place; no XOR output anywhere.
//!
//! A dead-letter transition is on the exact path only when it is itself a join
//! that consumes the correlated coloured inputs and returns budget; a name-blind
//! dead-letter that drains a `pending` place without consuming the coloured
//! tokens drops the net to the sound over-approximation (it produces budget while
//! not being a coloured-input join, so the budget discipline above rejects it).
//!
//! Quiescence properties are never routed here (they are not reachability-safety
//! and the budget-bounded colouring does not yet model the absence of an enabled
//! join across colours — that is the SCG name-partition route).

use std::collections::HashSet;

use libpetri_core::petri_net::PetriNet;

use crate::marking_state::MarkingState;
use crate::net_flattener::FlatNet;
use crate::p_invariant::PInvariant;
use crate::property::SmtProperty;
use crate::smt_encoder::SmtEncoding;

/// How a transition relates to the coloured (correlation-carrying) places.
enum Class {
    /// Minting fork: produces a freshly-coloured token into each listed place.
    Mint { coloured_out: Vec<usize> },
    /// Matched join: consumes one same-coloured token from each listed place.
    Join { coloured_in: Vec<usize> },
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
    /// Classification per flat transition (1:1 — the fragment forbids XOR).
    classes: Vec<Class>,
}

/// Detects whether `net` is in the supported budget-bounded mint→matched-join
/// fragment and, if so, returns the plan for [`encode_coloured`]. Returns `None`
/// otherwise — the verifier then uses the sound over-approximation.
pub fn build_plan(
    net: &PetriNet,
    flat: &FlatNet,
    initial: &MarkingState,
    budget_places: &HashSet<String>,
) -> Option<ColouredPlan> {
    let p = flat.place_count;

    // No XOR: every original transition maps 1:1 to a flat row, in order.
    if flat.transitions.len() != net.transitions().len() {
        return None;
    }

    // 1. Coloured places = union of every matched transition's correlated inputs.
    let mut is_coloured = vec![false; p];
    for t in net.transitions() {
        if let Some(ms) = t.match_spec() {
            for key in ms.keys() {
                let &pid = flat.place_index.get(key.place_name())?;
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

    // Colour bound k = total initial budget tokens (the live-name ceiling).
    let budget_idx: HashSet<usize> = budget_places
        .iter()
        .filter_map(|n| flat.place_index.get(n).copied())
        .collect();
    if budget_idx.is_empty() {
        return None;
    }
    let k: usize = budget_idx
        .iter()
        .map(|&b| initial.count(&flat.places[b]))
        .sum();
    if k == 0 {
        return None;
    }

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

    // 2. Classify each transition from its flat incidence.
    let mut classes = Vec::with_capacity(flat.transitions.len());
    for (t, ft) in net.transitions().iter().zip(&flat.transitions) {
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
        } else if !coloured_out.is_empty() {
            // Minting fork: produces coloured (count 1), consumes none, costs budget.
            if !coloured_in.is_empty() {
                return None;
            }
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
            if !coloured_in.is_empty() {
                return None;
            }
            Class::Untouched
        };
        classes.push(class);
    }

    // 3. Budget discipline: consumed only by mints, produced only by joins, so
    //    live colours ≤ initial budget = k (the soundness bound for `k` colours).
    for (cls, ft) in classes.iter().zip(&flat.transitions) {
        for &b in &budget_idx {
            if ft.pre[b] > 0 && !matches!(cls, Class::Mint { .. }) {
                return None;
            }
            if ft.post[b] > 0 && !matches!(cls, Class::Join { .. }) {
                return None;
            }
        }
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
            if parts.len() == 1 {
                parts[0].to_string()
            } else {
                format!("(+ {})", parts.join(" "))
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
pub fn encode_coloured(
    plan: &ColouredPlan,
    flat: &FlatNet,
    initial: &MarkingState,
    property: &SmtProperty,
    invariants: &[PInvariant],
) -> SmtEncoding {
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
        }
    }
    lines.push(String::new());

    // Error rule.
    lines.push(encode_error(plan, &lay, flat, property));
    lines.push(String::new());
    lines.push("(assert (not Error))".to_string());
    lines.push("(check-sat)".to_string());

    SmtEncoding {
        smt2: lines.join("\n"),
        place_count: p,
    }
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
fn encode_error(
    plan: &ColouredPlan,
    lay: &Layout,
    flat: &FlatNet,
    property: &SmtProperty,
) -> String {
    let all_vars: String = lay
        .cur
        .iter()
        .map(|v| format!("({v} Int)"))
        .collect::<Vec<_>>()
        .join(" ");
    let violation = encode_violation(plan, lay, flat, property);
    format!(
        "(assert (forall ({all_vars})\n  (=> (and (Reachable {}) {violation})\n      Error)))",
        lay.cur.join(" ")
    )
}

/// Encodes the property-violation condition over the coloured current marking.
/// Only reachability-safety properties are routed to this encoder (the verifier
/// guarantees it); quiescence properties yield `false` (no violating state).
fn encode_violation(
    plan: &ColouredPlan,
    lay: &Layout,
    flat: &FlatNet,
    property: &SmtProperty,
) -> String {
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
            Some(&pid) => format!("(> {} {})", lay.aggregate(pid, plan, &lay.cur), bound),
            None => "false".to_string(),
        },
        SmtProperty::Unreachable { places } | SmtProperty::MutualExclusion { places } => {
            any_place_present(places)
        }
        // Quiescence properties are never routed here.
        SmtProperty::DeadlockFree | SmtProperty::JoinedOrDeadLettered { .. } => "false".to_string(),
    }
}
