//! The colour-slot bound `k` of the name-coloured encoding ([NU-053]), as a linear program
//! solved in exact rational arithmetic, with no solver ([VER-013] AC1).
//!
//! `k` has to bound the number of names live at once. A name is live only while some
//! coloured place holds a token of it, so the live names never outnumber the tokens on
//! the coloured places. For any weighting `y` over the flat places with
//!
//! * `y ≥ 0`,
//! * `y_p ≥ 1` on every coloured place `p`,
//! * `y·N_r ≤ 0` for every flat row `r`, where `N_r = post_r − pre_r` is the row's column
//!   of the incidence matrix (a timeout outcome counts its deposit),
//!
//! every reachable marking has `Σ_{coloured} M ≤ y·M ≤ y·M0`. `k = ⌊opt⌋`, where `opt` is
//! the least `y·M0` over all such weightings. The optimum is unique, so every
//! implementation computes the same `k`. Equivalently (the dual), `opt` is the largest
//! coloured token count the state equation `M = M0 + N·σ ≥ 0`, `σ ≥ 0` admits over the
//! reals. The program is infeasible exactly when that count is unbounded: then nothing
//! bounds the coloured tokens structurally, and the plan is refused.
//!
//! **No H1.** A place a reset or consume-all arc clears keeps a free weight `y_p ≥ 0`. At
//! an enabled firing such a place ends at its deposit, which is at most
//! `m_p − pre_p + post_p` because enablement gives `pre_p ≤ m_p` (Lean `fireAD_le_linear`,
//! `Novel/LinearBound.lean`), and a non-negative weight keeps the inequality. The
//! [VER-015] check `linear_bound::check_linear_bound_exact` still pins such places to weight
//! zero although its proof does not need it (`linear_bound_sound_noH1`); the slot bound
//! follows the proof. The difference is deliberate. Inhibitor and read arcs do not enter
//! the column: they only restrict enablement.
//!
//! **Trust.** [`solve`] is untrusted: it is neither modelled in Lean nor pinned in
//! `lean/fidelity.toml`, so editing it needs no Lean re-verification. Its answer is a
//! weighting scaled to integers ([`ScaledCover`]). The plan uses `k` only through
//! [`checked`], which runs [`check_cover`]: an exact re-check of the weighting against
//! every flat row, which computes `k = ⌊Y·M0 / D⌋` itself. Only the checker is modelled
//! (`checkCover`, `colourSlotBoundLP` in `lean/Libpetri/Novel/RouteA/SlotBound.lean`) and
//! proved sufficient for `coloured_simulates` (`buildPlan_premisesS`, `Plan.lean`).
//!
//! **The algorithm** is normative in full, so every implementation performs the same
//! pivots and returns the same weighting:
//!
//! 1. *Presolve.* `U` is the least set of places containing the coloured ones such that a
//!    row producing into `U` (`N_r[q] > 0` for some `q ∈ U`) has every place it consumes
//!    from (`N_r[p] < 0`) in `U`. The kept rows are the rows producing into `U`, in flat
//!    order, restricted to `U`; a kept row equal to an earlier one after the restriction is
//!    dropped. `U` is ordered ascending. The presolve does not change the optimum, and a
//!    presolve bug cannot make `k` unsound because the checker sees every flat row.
//! 2. *The dual, in standard form:* maximise `c·σ` subject to `A·σ + s = b`, `σ, s ≥ 0`,
//!    with one constraint row per place `U[i]` (`A[i][j] = pre − post` of kept row `j` at
//!    `U[i]`, `b_i = M0[U[i]] ≥ 0`) and `c_j` kept row `j`'s net production into the
//!    coloured places. Columns are the kept rows `0..m'` in order, then the slacks
//!    `m'..m'+n'` in the order of `U`. The slacks are the initial basis, feasible because
//!    `M0 ≥ 0`: no Phase I, no artificial variables, no big-M.
//! 3. *Bland's rule.* Entering: the smallest column with a negative objective-row entry.
//!    Leaving: the least ratio `rhs_i / a_ie` over rows with `a_ie > 0`, ties to the row
//!    whose basic column is smallest. No negative entry: optimal. No positive entry in the
//!    entering column: the dual is unbounded, so the program is infeasible.
//! 4. *The weighting.* With `π_i` the objective-row entry of slack column `m' + i`,
//!    `y_p = π_i + [p coloured]` for `p = U[i]` and `y_p = 0` off `U`. `D` is the least
//!    common multiple of the denominators of the `y_p` in lowest terms and `Y = y·D`.
//!
//! Limits, both functions of the presolved program and the pivot sequence, so every
//! implementation refuses the same nets: [`LpAnswer::TooLarge`] past [`MAX_PLACES`] places
//! or [`MAX_ROWS`] rows after the presolve, before any pivot; [`LpAnswer::PivotLimit`] past
//! [`PIVOTS_PER_SIZE`]` · (n' + m')` pivots. The solve polls the verification's stop
//! ([VER-013]) before every pivot and answers [`LpAnswer::Stopped`]; without a stop scope
//! (as in `encode_scripts`) the poll does nothing. Each round of the loop decides in this
//! order: no entering column, optimal; no leaving row, infeasible; the limit's pivots
//! already made, pivot limit; a stop, stopped; otherwise pivot. A solve that ends without
//! needing another pivot is therefore never refused by the limit.

use std::collections::HashSet;

use crate::exact::{BigInt, Rational};
use crate::marking_state::MarkingState;
use crate::net_flattener::FlatNet;

/// The largest colour-slot bound a plan may carry: the limit of Java's `int`, applied by
/// every implementation so that all three refuse the same nets (Lean `slotCap`).
pub const SLOT_CAP: u64 = 2_147_483_647;

/// The most places the presolved program may have.
pub const MAX_PLACES: usize = 4096;

/// The most rows (transitions) the presolved program may have.
pub const MAX_ROWS: usize = 16384;

/// The pivot limit is this many pivots per presolved place and row.
pub const PIVOTS_PER_SIZE: usize = 50;

/// A weighting scaled to integers: `y_p = weights[p] / denominator`, one entry per flat
/// place.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScaledCover {
    pub weights: Vec<BigInt>,
    pub denominator: BigInt,
}

/// What [`solve`] answers. `places` and `rows` are the presolved sizes `n'` and `m'`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LpAnswer {
    /// An optimal weighting, still to be re-checked.
    Optimal { cover: ScaledCover, places: usize, rows: usize },
    /// No weighting satisfies the constraints: the coloured tokens are not structurally
    /// bounded.
    Infeasible { places: usize, rows: usize },
    /// The presolved program exceeds [`MAX_PLACES`] or [`MAX_ROWS`].
    TooLarge { places: usize, rows: usize },
    /// No optimum within `limit` pivots.
    PivotLimit { limit: usize },
    /// The verification was stopped (total budget or cancellation, [VER-013]).
    Stopped,
}

/// A weighting [`check_cover`] accepted: `k = ⌊Y·M0 / D⌋` and the value `Y·M0 / D` in
/// lowest terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedCover {
    pub k: usize,
    pub value: Rational,
}

/// The colour-slot bound as `build_plan` receives it: [`checked`] of the simplex's answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SlotBound {
    /// A re-checked weighting: the bound `k`, the weighting's value, the presolved sizes.
    Bound { k: usize, value: Rational, places: usize, rows: usize },
    Infeasible { places: usize, rows: usize },
    TooLarge { places: usize, rows: usize },
    PivotLimit { limit: usize },
    /// The simplex's weighting failed the exact re-check (a simplex bug); no bound.
    CheckFailed { reason: String },
    Stopped,
}

impl SlotBound {
    /// The bound, when there is one.
    pub fn k(&self) -> Option<usize> {
        match self {
            SlotBound::Bound { k, .. } => Some(*k),
            _ => None,
        }
    }

    /// The report line, with its two-space indent and no newline. `None` for a stop: the
    /// budget machinery reports that.
    pub fn report_line(&self) -> Option<String> {
        Some(match self {
            SlotBound::Bound { k, value, places, rows } => format!(
                "  Colour-slot bound: LP optimum {value} over {places} places and {rows} \
                 transitions, so k={k} (re-checked in exact arithmetic)"
            ),
            SlotBound::Infeasible { places, rows } => format!(
                "  Colour-slot bound: none (LP infeasible over {places} places and {rows} \
                 transitions: no weighting bounds the coloured tokens)"
            ),
            SlotBound::TooLarge { places, rows } => format!(
                "  Colour-slot bound: none (LP over {places} places and {rows} transitions \
                 exceeds the limit of {MAX_PLACES} places and {MAX_ROWS} transitions)"
            ),
            SlotBound::PivotLimit { limit } => {
                format!("  Colour-slot bound: none (no LP optimum within the pivot limit of {limit})")
            }
            SlotBound::CheckFailed { reason } => {
                format!("  Colour-slot bound: none (LP weighting failed the exact re-check: {reason})")
            }
            SlotBound::Stopped => return None,
        })
    }
}

/// The bound of whatever the simplex answered (Lean `colourSlotBoundLP`). An optimal
/// answer goes through [`check_cover`]; every other answer passes through as no bound.
/// `k` never comes from an unchecked weighting.
pub fn checked(flat: &FlatNet, initial: &MarkingState, coloured: &[usize], answer: LpAnswer) -> SlotBound {
    match answer {
        LpAnswer::Optimal { cover, places, rows } => match check_cover(flat, initial, coloured, &cover) {
            Ok(CheckedCover { k, value }) => SlotBound::Bound { k, value, places, rows },
            Err(reason) => SlotBound::CheckFailed { reason },
        },
        LpAnswer::Infeasible { places, rows } => SlotBound::Infeasible { places, rows },
        LpAnswer::TooLarge { places, rows } => SlotBound::TooLarge { places, rows },
        LpAnswer::PivotLimit { limit } => SlotBound::PivotLimit { limit },
        LpAnswer::Stopped => SlotBound::Stopped,
    }
}

/// The exact re-check of a scaled weighting (Lean `checkCover`). Accepts `(Y, D)` exactly
/// when, in unbounded integer arithmetic,
///
/// 1. `Y` has one entry per flat place;
/// 2. `D ≥ 1`;
/// 3. `Y_p ≥ 0` for every place, in index order;
/// 4. `Y_p ≥ D` for every coloured place, ascending;
/// 5. `Σ_p Y_p·(post_r[p] − pre_r[p]) ≤ 0` for every flat row `r` of `flat.transitions`,
///    in flat order: all of them, never the presolved or deduplicated ones;
/// 6. with `V = Σ_p Y_p·M0[p]` and `k = V div D`, `k ≤` [`SLOT_CAP`].
///
/// and then returns `k` and `V / D`. The first failing check names the refusal. A
/// coloured index outside the net is refused too; `build_plan` never passes one.
///
/// `pre_r[p]` is the summed required count of the inputs on `p`; [CORE-030] AC3 rejects
/// two input specs on one place, so it is the one spec's count Lean `dotIncD` reads.
pub fn check_cover(
    flat: &FlatNet,
    initial: &MarkingState,
    coloured: &[usize],
    cover: &ScaledCover,
) -> Result<CheckedCover, String> {
    let n = flat.place_count;
    let y = &cover.weights;
    let d = &cover.denominator;
    if y.len() != n {
        return Err(format!("weighting has {} entries for {n} places", y.len()));
    }
    if !d.is_positive() {
        return Err(format!("denominator {d} is not positive"));
    }
    for p in 0..n {
        if y[p].is_negative() {
            return Err(format!("place '{}' has negative weight {}", flat.places[p], y[p]));
        }
    }
    let mut ascending = coloured.to_vec();
    ascending.sort_unstable();
    for &p in &ascending {
        if p >= n {
            return Err(format!("coloured place index {p} is out of range for {n} places"));
        }
        if y[p] < *d {
            return Err(format!(
                "coloured place '{}' has weight {} below the denominator {d}",
                flat.places[p], y[p]
            ));
        }
    }
    for row in &flat.transitions {
        let mut delta = BigInt::zero();
        for p in 0..n {
            let column = &BigInt::from(row.post[p]) - &BigInt::from(row.pre[p]);
            if !column.is_zero() {
                delta = &delta + &(&y[p] * &column);
            }
        }
        if delta.is_positive() {
            return Err(format!("transition '{}' increases the weighted sum by {delta}", row.name));
        }
    }
    let mut v = BigInt::zero();
    for p in 0..n {
        let m0 = initial.count(&flat.places[p]);
        if m0 != 0 {
            v = &v + &(&y[p] * &BigInt::from(m0));
        }
    }
    let k = v.div_rem(d).0;
    if k > BigInt::from(SLOT_CAP) {
        return Err(format!("k={k} exceeds {SLOT_CAP}"));
    }
    let k = k.to_i64().expect("k is at most SLOT_CAP") as usize;
    Ok(CheckedCover { k, value: Rational::new(v, d.clone()) })
}

/// Solves the colour-slot program for the coloured places `coloured` (flat indices).
/// Untrusted: see the module documentation. Deliberately not pinned in
/// `lean/fidelity.toml`.
pub fn solve(flat: &FlatNet, initial: &MarkingState, coloured: &[usize]) -> LpAnswer {
    solve_counted(flat, initial, coloured).0
}

/// [`solve`], with the number of pivots it performed.
pub fn solve_counted(flat: &FlatNet, initial: &MarkingState, coloured: &[usize]) -> (LpAnswer, usize) {
    let n = flat.place_count;
    let mut is_coloured = vec![false; n];
    for &p in coloured {
        if p < n {
            is_coloured[p] = true;
        }
    }
    let program = presolve(flat, &is_coloured);
    let (places, rows) = (program.places.len(), program.rows.len());
    if places > MAX_PLACES || rows > MAX_ROWS {
        return (LpAnswer::TooLarge { places, rows }, 0);
    }

    // Constraint row i is place U[i]: `A[i][j] = −N_j[U[i]]` for kept row j, then its
    // slack. Kept rows are visited in order, so every sparse row stays sorted by column.
    let mut a: Vec<SparseRow> = vec![Vec::new(); places];
    for (j, row) in program.rows.iter().enumerate() {
        for &(i, v) in row {
            a[i].push((j, Rational::from_int(-BigInt::from(v))));
        }
    }
    for (i, r) in a.iter_mut().enumerate() {
        r.push((rows + i, Rational::from(1)));
    }
    let b: Vec<Rational> = program
        .places
        .iter()
        .map(|&p| Rational::from_int(BigInt::from(initial.count(&flat.places[p]))))
        .collect();
    // The objective row starts at −c_j on the structural columns.
    let obj: SparseRow = program
        .rows
        .iter()
        .enumerate()
        .filter_map(|(j, row)| {
            let c: i128 = row.iter().filter(|&&(i, _)| is_coloured[program.places[i]]).map(|&(_, v)| v).sum();
            (c != 0).then(|| (j, Rational::from_int(-BigInt::from(c))))
        })
        .collect();
    let mut tableau = Tableau {
        rows: a,
        rhs: b,
        obj,
        obj_value: Rational::zero(),
        basis: (rows..rows + places).collect(),
    };
    let limit = PIVOTS_PER_SIZE * (places + rows);
    let mut pivots = 0;
    let outcome = tableau.run(Rule::Bland, limit, &mut pivots, crate::total_budget::cut);
    let answer = match outcome {
        Outcome::Optimal => {
            let mut y = vec![Rational::zero(); n];
            for (i, &p) in program.places.iter().enumerate() {
                let pi = lookup(&tableau.obj, rows + i).cloned().unwrap_or_else(Rational::zero);
                y[p] = if is_coloured[p] { pi.add(&Rational::from(1)) } else { pi };
            }
            let mut denominator = BigInt::one();
            for v in &y {
                let g = denominator.gcd(v.denom());
                denominator = &denominator.div_rem(&g).0 * v.denom();
            }
            let weights = y
                .iter()
                .map(|v| v.numer() * &denominator.div_rem(v.denom()).0)
                .collect();
            LpAnswer::Optimal { cover: ScaledCover { weights, denominator }, places, rows }
        }
        Outcome::Unbounded => LpAnswer::Infeasible { places, rows },
        Outcome::PivotLimit => LpAnswer::PivotLimit { limit },
        Outcome::Stopped => LpAnswer::Stopped,
    };
    (answer, pivots)
}

/// The presolved program: the places of `U` ascending, and the kept rows, each a sparse
/// vector over positions in `U` of the row's column `post − pre`.
struct Presolved {
    places: Vec<usize>,
    rows: Vec<Vec<(usize, i128)>>,
}

fn presolve(flat: &FlatNet, is_coloured: &[bool]) -> Presolved {
    let n = flat.place_count;
    let columns: Vec<Vec<(usize, i128)>> = flat
        .transitions
        .iter()
        .map(|t| {
            (0..n)
                .filter_map(|p| {
                    let v = t.post[p] as i128 - t.pre[p] as i128;
                    (v != 0).then_some((p, v))
                })
                .collect()
        })
        .collect();
    let produces_into = |col: &[(usize, i128)], in_u: &[bool]| col.iter().any(|&(q, v)| v > 0 && in_u[q]);

    // The upstream cone, to a fixpoint. It is a set, so the visiting order is irrelevant.
    let mut in_u = is_coloured.to_vec();
    loop {
        let mut changed = false;
        for col in &columns {
            if produces_into(col, &in_u) {
                for &(p, v) in col {
                    if v < 0 && !in_u[p] {
                        in_u[p] = true;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    let places: Vec<usize> = (0..n).filter(|&p| in_u[p]).collect();
    let mut position = vec![usize::MAX; n];
    for (i, &p) in places.iter().enumerate() {
        position[p] = i;
    }

    let mut seen: HashSet<Vec<(usize, i128)>> = HashSet::new();
    let mut rows = Vec::new();
    for col in &columns {
        if !produces_into(col, &in_u) {
            continue;
        }
        let restricted: Vec<(usize, i128)> =
            col.iter().filter(|&&(p, _)| in_u[p]).map(|&(p, v)| (position[p], v)).collect();
        if seen.insert(restricted.clone()) {
            rows.push(restricted);
        }
    }
    Presolved { places, rows }
}

// ---- the simplex core ----

/// A sparse row: `(column, value)` sorted by column, no zero value.
type SparseRow = Vec<(usize, Rational)>;

fn lookup(row: &SparseRow, col: usize) -> Option<&Rational> {
    row.binary_search_by_key(&col, |e| e.0).ok().map(|i| &row[i].1)
}

/// `row − f·prow`, both sorted, zeros dropped.
fn sub_scaled(row: &SparseRow, f: &Rational, prow: &SparseRow) -> SparseRow {
    let mut out = Vec::with_capacity(row.len() + prow.len());
    let (mut i, mut j) = (0, 0);
    while i < row.len() || j < prow.len() {
        let ci = row.get(i).map_or(usize::MAX, |e| e.0);
        let cj = prow.get(j).map_or(usize::MAX, |e| e.0);
        if ci < cj {
            out.push(row[i].clone());
            i += 1;
        } else if cj < ci {
            out.push((cj, f.mul(&prow[j].1).neg()));
            j += 1;
        } else {
            let v = row[i].1.sub(&f.mul(&prow[j].1));
            if !v.is_zero() {
                out.push((ci, v));
            }
            i += 1;
            j += 1;
        }
    }
    out
}

/// The pivot rule. Only [`Rule::Bland`] is used outside tests.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Rule {
    /// Smallest entering column; least ratio, ties to the smallest basic column.
    Bland,
    /// The most negative objective entry (smallest column on ties); least ratio, ties to
    /// the lowest row. It can cycle, which is what the tests show.
    #[cfg(test)]
    Largest,
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Optimal,
    Unbounded,
    PivotLimit,
    Stopped,
}

/// A maximisation tableau `z + Σ obj_j·x_j = obj_value`, `rows·x = rhs`, one basic column
/// per row.
struct Tableau {
    rows: Vec<SparseRow>,
    rhs: Vec<Rational>,
    obj: SparseRow,
    obj_value: Rational,
    basis: Vec<usize>,
}

impl Tableau {
    /// The standard form `max c·x` subject to `A·x ≤ b`, `x ≥ 0`, with `b ≥ 0` and the
    /// slacks as the initial basis (columns `0..c.len()` structural, then one slack per
    /// row).
    #[cfg(test)]
    fn standard(a: &[Vec<Rational>], b: Vec<Rational>, c: &[Rational]) -> Tableau {
        let m = c.len();
        let rows = a
            .iter()
            .enumerate()
            .map(|(i, r)| {
                let mut row: SparseRow =
                    r.iter().enumerate().filter(|(_, v)| !v.is_zero()).map(|(j, v)| (j, v.clone())).collect();
                row.push((m + i, Rational::from(1)));
                row
            })
            .collect();
        let obj = c.iter().enumerate().filter(|(_, v)| !v.is_zero()).map(|(j, v)| (j, v.neg())).collect();
        Tableau { rows, rhs: b, obj, obj_value: Rational::zero(), basis: (m..m + a.len()).collect() }
    }

    fn entering(&self, rule: Rule) -> Option<usize> {
        match rule {
            Rule::Bland => self.obj.iter().find(|e| e.1.is_negative()).map(|e| e.0),
            #[cfg(test)]
            Rule::Largest => {
                let mut best: Option<&(usize, Rational)> = None;
                for e in self.obj.iter().filter(|e| e.1.is_negative()) {
                    if best.is_none_or(|b| e.1 < b.1) {
                        best = Some(e);
                    }
                }
                best.map(|e| e.0)
            }
        }
    }

    fn leaving(&self, rule: Rule, e: usize) -> Option<usize> {
        let mut best: Option<(usize, Rational)> = None;
        for (i, row) in self.rows.iter().enumerate() {
            let Some(a) = lookup(row, e).filter(|a| a.is_positive()) else {
                continue;
            };
            let ratio = self.rhs[i].div(a);
            let better = match &best {
                None => true,
                Some((bi, br)) => match ratio.cmp(br) {
                    std::cmp::Ordering::Less => true,
                    std::cmp::Ordering::Greater => false,
                    std::cmp::Ordering::Equal => match rule {
                        Rule::Bland => self.basis[i] < self.basis[*bi],
                        #[cfg(test)]
                        Rule::Largest => false,
                    },
                },
            };
            if better {
                best = Some((i, ratio));
            }
        }
        best.map(|(i, _)| i)
    }

    fn pivot(&mut self, r: usize, e: usize) {
        let a = lookup(&self.rows[r], e).expect("pivot entry").clone();
        let prow: SparseRow = self.rows[r].iter().map(|(c, v)| (*c, v.div(&a))).collect();
        let prhs = self.rhs[r].div(&a);
        for i in 0..self.rows.len() {
            if i == r {
                continue;
            }
            if let Some(f) = lookup(&self.rows[i], e).cloned() {
                self.rows[i] = sub_scaled(&self.rows[i], &f, &prow);
                self.rhs[i] = self.rhs[i].sub(&f.mul(&prhs));
            }
        }
        if let Some(f) = lookup(&self.obj, e).cloned() {
            self.obj = sub_scaled(&self.obj, &f, &prow);
            self.obj_value = self.obj_value.sub(&f.mul(&prhs));
        }
        self.rows[r] = prow;
        self.rhs[r] = prhs;
        self.basis[r] = e;
    }

    /// Pivots until optimal or unbounded, at most `limit` times, polling `stop` before
    /// every pivot.
    fn run(&mut self, rule: Rule, limit: usize, pivots: &mut usize, stop: impl Fn() -> bool) -> Outcome {
        loop {
            let Some(e) = self.entering(rule) else {
                return Outcome::Optimal;
            };
            let Some(r) = self.leaving(rule, e) else {
                return Outcome::Unbounded;
            };
            if *pivots >= limit {
                return Outcome::PivotLimit;
            }
            if stop() {
                return Outcome::Stopped;
            }
            self.pivot(r, e);
            *pivots += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use crate::net_flattener::FlatTransition;

    fn q(n: i64, d: i64) -> Rational {
        Rational::new(BigInt::from(n), BigInt::from(d))
    }

    /// Beale's example (1955) in its original rational data: maximise
    /// `3/4 x4 − 20 x5 + 1/2 x6 − 6 x7` subject to
    /// `1/4 x4 − 8 x5 − x6 + 9 x7 ≤ 0`, `1/2 x4 − 12 x5 − 1/2 x6 + 3 x7 ≤ 0`, `x6 ≤ 1`.
    fn beale() -> Tableau {
        let a = vec![
            vec![q(1, 4), q(-8, 1), q(-1, 1), q(9, 1)],
            vec![q(1, 2), q(-12, 1), q(-1, 2), q(3, 1)],
            vec![q(0, 1), q(0, 1), q(1, 1), q(0, 1)],
        ];
        let b = vec![q(0, 1), q(0, 1), q(1, 1)];
        let c = vec![q(3, 4), q(-20, 1), q(1, 2), q(-6, 1)];
        Tableau::standard(&a, b, &c)
    }

    #[test]
    fn bland_solves_beales_cycling_example() {
        let mut t = beale();
        let mut pivots = 0;
        assert_eq!(t.run(Rule::Bland, 1000, &mut pivots, || false), Outcome::Optimal);
        assert_eq!(t.obj_value, q(5, 4));
        assert_eq!(pivots, 6);
    }

    /// The largest-coefficient rule with lowest-row ties revisits a basis on the same data,
    /// so it never terminates. This is what Bland's rule is there for.
    #[test]
    fn the_largest_coefficient_rule_cycles_on_beales_example() {
        let mut t = beale();
        let mut seen: Vec<Vec<usize>> = vec![t.basis.clone()];
        let mut revisited = None;
        for step in 1..=50 {
            let e = t.entering(Rule::Largest).expect("not optimal yet");
            let r = t.leaving(Rule::Largest, e).expect("bounded");
            t.pivot(r, e);
            let mut basis = t.basis.clone();
            basis.sort_unstable();
            if seen.contains(&basis) {
                revisited = Some(step);
                break;
            }
            seen.push(basis);
        }
        assert_eq!(revisited, Some(6), "the largest-coefficient rule must cycle after 6 pivots");
        assert_eq!(t.obj_value, q(0, 1));
    }

    /// After the first pivot x0 is basic in row 1, and x1 then ties rows 0 (basic s2) and 1
    /// (basic x0) at ratio 0. Bland's rule takes row 1, so x0 leaves; the lowest row would let
    /// s2 leave and end in the basis [1, 0, 4, 5]. Java and TS hold the same tableau.
    #[test]
    fn bland_breaks_a_ratio_tie_by_the_smallest_basic_column() {
        let a = vec![
            vec![q(-1, 1), q(2, 1)],
            vec![q(2, 1), q(2, 1)],
            vec![q(-1, 1), q(0, 1)],
            vec![q(0, 1), q(2, 1)],
        ];
        let mut t = Tableau::standard(&a, vec![q(0, 1), q(0, 1), q(1, 1), q(1, 1)], &[q(1, 1), q(2, 1)]);
        let mut pivots = 0;
        assert_eq!(t.run(Rule::Bland, 100, &mut pivots, || false), Outcome::Optimal);
        assert_eq!((pivots, t.basis.clone(), t.obj_value.clone()), (2, vec![2, 1, 4, 5], q(0, 1)));
    }

    #[test]
    fn the_pivot_limit_and_the_stop_are_polled_before_a_pivot() {
        let mut t = beale();
        let mut pivots = 0;
        assert_eq!(t.run(Rule::Bland, 3, &mut pivots, || false), Outcome::PivotLimit);
        assert_eq!(pivots, 3);
        let mut t = beale();
        let mut pivots = 0;
        assert_eq!(t.run(Rule::Bland, 1000, &mut pivots, || true), Outcome::Stopped);
        assert_eq!(pivots, 0);
    }

    /// Places `names` in this (already sorted) order, rows `(name, pre, post)` as
    /// `(place, count)` lists.
    fn flat(names: &[&str], rows: &[(&str, &[(&str, i64)], &[(&str, i64)])]) -> FlatNet {
        let places: Vec<String> = names.iter().map(|s| s.to_string()).collect();
        let place_index = places.iter().enumerate().map(|(i, p)| (p.clone(), i)).collect();
        let n = places.len();
        let idx = |p: &str| names.iter().position(|q| *q == p).expect("place");
        let transitions = rows
            .iter()
            .map(|(name, pre, post)| {
                let mut pv = vec![0i64; n];
                let mut qv = vec![0i64; n];
                for (p, c) in pre.iter() {
                    pv[idx(p)] += c;
                }
                for (p, c) in post.iter() {
                    qv[idx(p)] += c;
                }
                FlatTransition::new(*name, pv, qv)
            })
            .collect();
        FlatNet { places, place_index, place_count: n, transitions }
    }

    fn marking(tokens: &[(&str, usize)]) -> MarkingState {
        tokens.iter().fold(MarkingStateBuilder::new(), |m, (p, k)| m.tokens(*p, *k)).build()
    }

    fn bound(net: &FlatNet, m0: &MarkingState, coloured: &[usize]) -> SlotBound {
        checked(net, m0, coloured, solve(net, m0, coloured))
    }

    /// An `exactly(3)` fork into the keys `a`, `b` and a join that refunds one budget token:
    /// optimum `14/3` at budget 7, `2/3` at budget 1.
    fn fractional_fork() -> FlatNet {
        flat(
            &["a", "b", "budget"],
            &[
                ("mint", &[("budget", 3)], &[("a", 1), ("b", 1)]),
                ("join", &[("a", 1), ("b", 1)], &[("budget", 1)]),
            ],
        )
    }

    #[test]
    fn a_fractional_optimum_is_floored_after_the_re_check() {
        let net = fractional_fork();
        let m0 = marking(&[("budget", 7)]);
        let answer = solve(&net, &m0, &[0, 1]);
        let LpAnswer::Optimal { cover, places, rows } = &answer else { panic!("{answer:?}") };
        assert_eq!((*places, *rows), (3, 2));
        assert_eq!(cover.denominator, BigInt::from(3i64));
        assert_eq!(cover.weights, vec![BigInt::from(3i64), BigInt::from(3i64), BigInt::from(2i64)]);
        let b = checked(&net, &m0, &[0, 1], answer);
        assert_eq!(b, SlotBound::Bound { k: 4, value: q(14, 3), places: 3, rows: 2 });
        assert_eq!(
            b.report_line().unwrap(),
            "  Colour-slot bound: LP optimum 14/3 over 3 places and 2 transitions, so k=4 \
             (re-checked in exact arithmetic)"
        );
        // One budget token: below one coloured token, so the exact zero-slot plan.
        assert_eq!(bound(&net, &marking(&[("budget", 1)]), &[0, 1]).k(), Some(0));
    }

    /// The dual maximises σ0 + 2·σ1 under σ0 + σ1 ≤ 1. Bland's rule enters σ0 first and swaps
    /// it for σ1 in a second pivot; the largest coefficient would take σ1 in one.
    #[test]
    fn bland_enters_the_smallest_column_not_the_largest_coefficient() {
        let net = flat(
            &["a", "budget"],
            &[("one", &[("budget", 1)], &[("a", 1)]), ("two", &[("budget", 1)], &[("a", 2)])],
        );
        let m0 = marking(&[("budget", 1)]);
        let (answer, pivots) = solve_counted(&net, &m0, &[0]);
        assert_eq!(pivots, 2);
        let LpAnswer::Optimal { cover, .. } = &answer else { panic!("{answer:?}") };
        assert_eq!(cover.weights, vec![BigInt::from(1i64), BigInt::from(2i64)]);
        assert_eq!(checked(&net, &m0, &[0], answer).k(), Some(2));
    }

    #[test]
    fn no_budget_token_gives_k_zero_and_an_inflating_join_is_infeasible() {
        let conserving = flat(
            &["a", "b", "budget"],
            &[
                ("mint", &[("budget", 1)], &[("a", 1), ("b", 1)]),
                ("join", &[("a", 1), ("b", 1)], &[("budget", 1)]),
            ],
        );
        assert_eq!(bound(&conserving, &marking(&[]), &[0, 1]).k(), Some(0));
        assert_eq!(bound(&conserving, &marking(&[("budget", 3)]), &[0, 1]).k(), Some(6));
        // The join refunds two tokens, one to each budget place: the colours multiply.
        let inflating = flat(
            &["a", "b", "budget1", "budget2"],
            &[
                ("mint1", &[("budget1", 1)], &[("a", 1), ("b", 1)]),
                ("mint2", &[("budget2", 1)], &[("a", 1), ("b", 1)]),
                ("join", &[("a", 1), ("b", 1)], &[("budget1", 1), ("budget2", 1)]),
            ],
        );
        let b = bound(&inflating, &marking(&[("budget1", 1)]), &[0, 1]);
        assert_eq!(b, SlotBound::Infeasible { places: 4, rows: 3 });
        assert_eq!(
            b.report_line().unwrap(),
            "  Colour-slot bound: none (LP infeasible over 4 places and 3 transitions: no \
             weighting bounds the coloured tokens)"
        );
    }

    /// The presolve keeps the upstream cone: a row producing into it with an entry outside
    /// it, a duplicate restricted row, a consume-only row and an unrelated cycle.
    #[test]
    fn the_presolve_keeps_the_upstream_cone_and_drops_duplicates() {
        let net = flat(
            &["a", "budget", "log", "x", "y"],
            &[
                ("mint", &[("budget", 1)], &[("a", 1), ("log", 1)]),
                ("mint_again", &[("budget", 1)], &[("a", 1)]),
                ("consume", &[("a", 1)], &[]),
                ("cycle", &[("x", 1)], &[("y", 1)]),
                ("back", &[("y", 1)], &[("x", 1)]),
            ],
        );
        let m0 = marking(&[("budget", 2), ("x", 1)]);
        let p = presolve(&net, &[true, false, false, false, false]);
        assert_eq!(p.places, vec![0, 1]);
        assert_eq!(p.rows, vec![vec![(0, 1), (1, -1)]]);
        assert_eq!(bound(&net, &m0, &[0]), SlotBound::Bound { k: 2, value: q(2, 1), places: 2, rows: 1 });
        // m' = 0: nothing produces into the coloured place.
        let empty = flat(&["a", "b"], &[("t", &[("a", 1)], &[("b", 1)])]);
        assert_eq!(presolve(&empty, &[true, false]).rows.len(), 0);
        assert_eq!(bound(&empty, &marking(&[("b", 4)]), &[0]).k(), Some(0));
    }

    /// Large counts keep the arithmetic exact. A mint that turns `2^61` budget tokens into
    /// `2^61 − 1` keys has the optimum `(2^61 − 1)·2^30 / 2^61`, whose numerator and the
    /// tableau products behind it are far outside an `i64`.
    #[test]
    fn big_counts_and_denominators_stay_exact() {
        let big = 1i64 << 61;
        let net = flat(
            &["a", "budget"],
            &[("mint", &[("budget", big)], &[("a", big - 1)]), ("join", &[("a", 1)], &[("budget", 1)])],
        );
        let m0 = marking(&[("budget", 1usize << 30)]);
        let answer = solve(&net, &m0, &[0]);
        let LpAnswer::Optimal { cover, .. } = &answer else { panic!("{answer:?}") };
        assert_eq!(cover.denominator, BigInt::from(big));
        assert_eq!(cover.weights, vec![BigInt::from(big), BigInt::from(big - 1)]);
        let b = checked(&net, &m0, &[0], answer);
        let expected = Rational::new(&BigInt::from(big - 1) * &BigInt::from(1i64 << 30), BigInt::from(big));
        assert_eq!(expected.to_string(), "2305843009213693951/2147483648");
        let SlotBound::Bound { value, k, .. } = &b else { panic!("{b:?}") };
        assert_eq!(*value, expected);
        assert_eq!(*k, (1usize << 30) - 1);
    }

    /// One row consuming from 4096 places into the coloured one puts all 4097 in the cone.
    #[test]
    fn the_size_limit_is_decided_before_any_pivot() {
        let n = MAX_PLACES + 1;
        let places: Vec<String> = (0..n).map(|i| format!("p{i:05}")).collect();
        let place_index = places.iter().enumerate().map(|(i, p)| (p.clone(), i)).collect();
        let mut pre = vec![1i64; n];
        pre[0] = 0;
        let mut post = vec![0i64; n];
        post[0] = 1;
        let transitions = vec![FlatTransition::new("gather", pre, post)];
        let net = FlatNet { places, place_index, place_count: n, transitions };
        let (answer, pivots) = solve_counted(&net, &MarkingState::new(), &[0]);
        assert_eq!(answer, LpAnswer::TooLarge { places: n, rows: 1 });
        assert_eq!(pivots, 0);
        assert_eq!(
            checked(&net, &MarkingState::new(), &[0], answer).report_line().unwrap(),
            "  Colour-slot bound: none (LP over 4097 places and 1 transitions exceeds the limit \
             of 4096 places and 16384 transitions)"
        );
    }

    // ---- the checker, one refusal per clause, in order ----

    fn cover(weights: &[i64], d: i64) -> ScaledCover {
        ScaledCover { weights: weights.iter().map(|&w| BigInt::from(w)).collect(), denominator: BigInt::from(d) }
    }

    #[test]
    fn the_checker_refuses_each_clause_with_its_reason() {
        let net = fractional_fork();
        let m0 = marking(&[("budget", 7)]);
        let check = |c: &ScaledCover| check_cover(&net, &m0, &[0, 1], c);
        assert_eq!(check(&cover(&[3, 3, 2], 3)), Ok(CheckedCover { k: 4, value: q(14, 3) }));
        assert_eq!(check(&cover(&[3, 3], 3)).unwrap_err(), "weighting has 2 entries for 3 places");
        assert_eq!(check(&cover(&[3, 3, 2], 0)).unwrap_err(), "denominator 0 is not positive");
        assert_eq!(check(&cover(&[-3, -3, -2], -3)).unwrap_err(), "denominator -3 is not positive");
        assert_eq!(check(&cover(&[3, 3, -2], 3)).unwrap_err(), "place 'budget' has negative weight -2");
        assert_eq!(
            check(&cover(&[3, 2, 2], 3)).unwrap_err(),
            "coloured place 'b' has weight 2 below the denominator 3"
        );
        // Keys at 1 and the budget at 0: the mint raises the weighted sum by 2.
        assert_eq!(
            check(&cover(&[1, 1, 0], 1)).unwrap_err(),
            "transition 'mint' increases the weighted sum by 2"
        );
        // Feasible and above the cap: k = 7·2^31 / 3 > 2147483647.
        let w = 1i64 << 31;
        assert_eq!(
            check(&cover(&[w * 3 / 2, w * 3 / 2, w], 3)).unwrap_err(),
            format!("k={} exceeds 2147483647", 7 * w / 3)
        );
        // A feasible weighting that is not optimal is accepted, with its larger k.
        assert_eq!(check(&cover(&[1, 1, 1], 1)).map(|c| c.k), Ok(7));
    }

    /// The checker reads every flat row, including one the presolve drops: here a row
    /// that only consumes from the cone has no positive entry in it and never reaches the
    /// simplex, but a weighting that is negative on its output must still fail.
    #[test]
    fn the_checker_sees_rows_the_presolve_dropped() {
        let net = flat(
            &["a", "budget", "z"],
            &[
                ("mint", &[("budget", 1)], &[("a", 1)]),
                ("join", &[("a", 1)], &[("budget", 1)]),
                ("spill", &[("a", 1)], &[("z", 2)]),
            ],
        );
        let m0 = marking(&[("budget", 1)]);
        assert_eq!(presolve(&net, &[true, false, false]).rows.len(), 2);
        // z = 1: spill raises the sum by 2·1 − 1 = 1.
        assert_eq!(
            check_cover(&net, &m0, &[0], &cover(&[1, 1, 1], 1)).unwrap_err(),
            "transition 'spill' increases the weighted sum by 1"
        );
        assert_eq!(bound(&net, &m0, &[0]).k(), Some(1));
    }

    #[test]
    fn every_answer_without_a_weighting_is_no_bound() {
        let net = fractional_fork();
        let m0 = marking(&[]);
        for (answer, line) in [
            (LpAnswer::PivotLimit { limit: 250 }, Some("  Colour-slot bound: none (no LP optimum within the pivot limit of 250)")),
            (LpAnswer::Stopped, None),
        ] {
            let b = checked(&net, &m0, &[0, 1], answer);
            assert_eq!(b.k(), None);
            assert_eq!(b.report_line().as_deref(), line);
        }
        let b = checked(&net, &m0, &[0, 1], LpAnswer::Optimal { cover: cover(&[1, 1], 1), places: 3, rows: 2 });
        assert_eq!(
            b.report_line().unwrap(),
            "  Colour-slot bound: none (LP weighting failed the exact re-check: weighting has 2 \
             entries for 3 places)"
        );
    }
}
