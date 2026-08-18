use crate::incidence_matrix::IncidenceMatrix;
use crate::marking_state::MarkingState;
use crate::net_flattener::FlatNet;

/// A P-invariant: a weighted sum over places that is constant across all reachable markings.
///
/// sum(weights[i] * M(places[i])) = constant
#[derive(Debug, Clone)]
pub struct PInvariant {
    pub weights: Vec<i64>,
    pub constant: i64,
    pub support: Vec<usize>,
}

/// Computes P-invariants using integer Gaussian elimination (Farkas' algorithm).
///
/// Finds the null space of C^T (transposed incidence matrix) using integer arithmetic.
pub fn compute_p_invariants(
    matrix: &IncidenceMatrix,
    initial_marking: &MarkingState,
    place_names: &[String],
) -> Vec<PInvariant> {
    let ct = matrix.transposed();
    let rows = ct.len();
    let cols = if rows > 0 { ct[0].len() } else { 0 };

    if rows == 0 || cols == 0 {
        return Vec::new();
    }

    // Augmented matrix [C^T | I_P]
    let aug_cols = cols + rows;
    let mut aug: Vec<Vec<i64>> = Vec::with_capacity(rows);
    for (i, row) in ct.iter().enumerate() {
        let mut aug_row = vec![0i64; aug_cols];
        for (j, &val) in row.iter().enumerate() {
            aug_row[j] = val;
        }
        aug_row[cols + i] = 1; // identity portion
        aug.push(aug_row);
    }

    // Gaussian elimination on the C^T portion
    let mut pivot_row = 0;
    for col in 0..cols {
        // Find pivot
        let found = (pivot_row..rows).find(|&row| aug[row][col] != 0);
        let Some(pr) = found else { continue };

        // Swap
        aug.swap(pivot_row, pr);

        // Eliminate
        let pivot_val = aug[pivot_row][col];
        for row in 0..rows {
            if row == pivot_row {
                continue;
            }
            let factor = aug[row][col];
            if factor == 0 {
                continue;
            }
            let pivot_row_copy: Vec<i64> = aug[pivot_row].clone();
            for (j, pivot_j) in pivot_row_copy.iter().enumerate() {
                aug[row][j] = aug[row][j] * pivot_val - pivot_j * factor;
            }
            // GCD normalize
            let g = gcd_row(&aug[row]);
            if g > 1 {
                for val in &mut aug[row] {
                    *val /= g;
                }
            }
        }
        pivot_row += 1;
    }

    // Extract null space vectors (rows where C^T portion is all zero)
    let mut invariants = Vec::new();
    for row in &aug {
        let all_zero = (0..cols).all(|j| row[j] == 0);
        if !all_zero {
            continue;
        }

        let weights: Vec<i64> = (cols..aug_cols).map(|j| row[j]).collect();
        if weights.iter().all(|&w| w == 0) {
            continue;
        }

        // Make weights non-negative if possible
        let all_neg = weights.iter().all(|&w| w <= 0);
        let final_weights: Vec<i64> = if all_neg {
            weights.iter().map(|&w| -w).collect()
        } else {
            weights
        };

        // Compute constant from initial marking
        let constant: i64 = final_weights
            .iter()
            .enumerate()
            .map(|(i, &w)| w * initial_marking.count(&place_names[i]) as i64)
            .sum();

        let support: Vec<usize> = final_weights
            .iter()
            .enumerate()
            .filter(|(_, w)| **w != 0)
            .map(|(i, _)| i)
            .collect();

        invariants.push(PInvariant {
            weights: final_weights,
            constant,
            support,
        });
    }

    invariants
}

/// Computes the minimal **P-semiflows** — non-negative place weightings `y` with
/// `y·C = 0` — via the Colom–Silva / Farkas method. Unlike [`compute_p_invariants`]
/// (a signed null-space basis), every returned `PInvariant.weights` is non-negative, a
/// genuine P-semiflow, with `constant = y·M0`. A non-negative conservation law soundly
/// **bounds** the token sum over its support: `Σ_{support} M(p) ≤ y·M0`. Used to bound
/// the number of simultaneously-live colours in the name-coloured encoder.
pub fn compute_p_semiflows(
    matrix: &IncidenceMatrix,
    initial_marking: &MarkingState,
    place_names: &[String],
) -> Vec<PInvariant> {
    let np = matrix.place_count;
    let nt = matrix.transition_count;
    if np == 0 {
        return Vec::new();
    }

    // Each generator row = (signature over transitions, non-negative weight over
    // places). Start with one row per place: signature = that place's column of C,
    // weight = e_p. Eliminate one transition column at a time using only non-negative
    // combinations, so the accumulated weights stay non-negative.
    let mut rows: Vec<(Vec<i64>, Vec<i64>)> = (0..np)
        .map(|p| {
            let sig: Vec<i64> = (0..nt).map(|t| matrix.incidence[t][p]).collect();
            let mut weight = vec![0i64; np];
            weight[p] = 1;
            (sig, weight)
        })
        .collect();

    for t in 0..nt {
        let mut next: Vec<(Vec<i64>, Vec<i64>)> =
            rows.iter().filter(|r| r.0[t] == 0).cloned().collect();
        let pos: Vec<&(Vec<i64>, Vec<i64>)> = rows.iter().filter(|r| r.0[t] > 0).collect();
        let neg: Vec<&(Vec<i64>, Vec<i64>)> = rows.iter().filter(|r| r.0[t] < 0).collect();
        for rp in &pos {
            for rn in &neg {
                let cp = -rn.0[t]; // > 0
                let cn = rp.0[t]; // > 0
                // Checked combination: on i64 overflow, DROP this generator rather than
                // push a wrapped (invalid, non-`y·C=0`) row. Dropping it can at worst
                // lose a covering semiflow, which makes `colour_slot_bound` fall back to
                // the sound over-approximation — never an under-approximation.
                let (Some(mut sig), Some(mut weight)) =
                    (combine_row(cp, &rp.0, cn, &rn.0), combine_row(cp, &rp.1, cn, &rn.1))
                else {
                    continue;
                };
                reduce_gcd(&mut sig, &mut weight);
                next.push((sig, weight));
            }
        }
        rows = keep_support_minimal(next);
        rows.truncate(8192); // safety backstop against a combinatorial blow-up
    }

    rows.into_iter()
        .filter(|(_, w)| w.iter().any(|&x| x != 0))
        .filter_map(|(_, weights)| {
            // Checked `constant = Σ weight·M0`; on overflow drop this semiflow (fewer
            // covering semiflows → sound fallback, never a wrong bound).
            let mut constant: i64 = 0;
            for p in 0..np {
                let term = weights[p].checked_mul(initial_marking.count(&place_names[p]) as i64)?;
                constant = constant.checked_add(term)?;
            }
            let support: Vec<usize> = (0..np).filter(|&p| weights[p] != 0).collect();
            Some(PInvariant {
                weights,
                constant,
                support,
            })
        })
        .collect()
}

/// Outcome of [`validate_invariants_exact`]: the invariants that re-verified exactly,
/// plus one report-ready reason per dropped invariant.
#[derive(Debug, Clone)]
pub struct InvariantValidation {
    pub valid: Vec<PInvariant>,
    pub dropped: Vec<String>,
}

/// Exact re-validation pass between invariant computation and SMT encoding.
///
/// The Gaussian elimination in [`compute_p_invariants`] uses unchecked `i64`
/// arithmetic, so on adversarially-sized weights a row can silently wrap and still
/// look like a null-space vector. A numerically wrong invariant is not a harmless
/// weakening: the encoders conjoin `y·M' = y·M0` into every CHC transition-rule
/// BODY, where a wrong equality removes reachable successors and can certify a
/// false `Proven`. This pass therefore recomputes, in checked `i128`, every
/// component of `y·C` (each must be exactly 0) and the constant `y·M0` (must equal
/// `constant`), and DROPS — with a reason — any invariant that fails, overflows, or
/// carries a malformed weight/support shape, before it can reach an encoder.
///
/// Dropping is always sound here: an invariant only *strengthens* the encoding, so
/// losing one can at worst cost IC3 a lemma (a possible `Unknown`), never a wrong
/// verdict.
///
/// **H1 linearity guard** (`lean/Libpetri/Strengthening.lean`,
/// `consume_all_hypothesis_is_necessary`): the incidence matrix *linearizes*
/// consumption — its column is `post − pre` with `pre = required_count`, so it says
/// nothing about consume-all or reset semantics, where the encoder's fire relation
/// emits `m'_i = post[i]` and erases however many tokens the place actually held.
/// `y·C = 0` is therefore necessary but NOT sufficient: an invariant weighting such
/// a place can pass this gate yet be false on the real net, and conjoined into the
/// CHC rule bodies it prunes genuine successors (false `Proven`). Per the Lean
/// theorem's H1 hypothesis, any invariant with a nonzero weight on a place that is,
/// for any flat transition, a consume-all input place (`In::All` **and**
/// `In::AtLeast` — `at_least(n)` waits for n but then consumes ALL available,
/// `libpetri_core::input::consumption_count`; the linear cardinalities are
/// `one`/`exactly(n)`) or a reset place is dropped here. Env-injectable places need
/// no guard of their own: their injector columns (`IncidenceMatrix::from_flat_net`)
/// already force `y = 0` there through the `y·C = 0` check — Strengthening.lean's
/// H3′ sufficiency result (`invariant_strengthening_sound_inj`).
///
/// The net arrives as one `&FlatNet` rather than as separately-passed views of
/// it: passing an empty transition list used to disable the H1 guard silently
/// while still reporting the survivors as validated.
pub fn validate_invariants_exact(
    invariants: Vec<PInvariant>,
    matrix: &IncidenceMatrix,
    initial_marking: &MarkingState,
    flat: &FlatNet,
) -> InvariantValidation {
    let place_names = &flat.places;
    // Places with non-linear consumption on some flat transition (H1's
    // reset/consume-all arms). Computed once; the matrix may carry extra injector
    // columns beyond `flat.transitions`, which are linear and need no entry here.
    let mut nonlinear = vec![false; matrix.place_count];
    for ft in &flat.transitions {
        for &p in ft.consume_all.iter().chain(&ft.reset_places) {
            if p < nonlinear.len() {
                nonlinear[p] = true;
            }
        }
    }

    let mut valid = Vec::with_capacity(invariants.len());
    let mut dropped = Vec::new();
    'each: for inv in invariants {
        let desc = describe_invariant(&inv, place_names);

        // Shape: one weight per place, and place_names aligned with the matrix.
        if inv.weights.len() != matrix.place_count || place_names.len() != matrix.place_count {
            dropped.push(format!(
                "{desc} - weight vector length {} does not match place count {}",
                inv.weights.len(),
                matrix.place_count
            ));
            continue;
        }

        // Support must be exactly the (ascending) indices of the nonzero weights:
        // the encoders emit only the support terms, so an inconsistent support
        // would encode a different sum than y·M.
        let expected_support: Vec<usize> = (0..inv.weights.len())
            .filter(|&p| inv.weights[p] != 0)
            .collect();
        if inv.support != expected_support {
            dropped.push(format!(
                "{desc} - support is inconsistent with the nonzero weights"
            ));
            continue;
        }

        // H1 linearity guard (see the doc comment): a nonzero weight on a
        // consume-all or reset place makes the linearized column a lie about the
        // real firing, so `y·C = 0` below would not certify conservation.
        if let Some(pid) = (0..inv.weights.len()).find(|&p| inv.weights[p] != 0 && nonlinear[p]) {
            dropped.push(format!(
                "{desc} - support intersects consume-all/reset place '{}' \
                 (non-linear consumption; see Strengthening.lean H1)",
                place_names.get(pid).map(String::as_str).unwrap_or("?")
            ));
            continue;
        }

        // y·C = 0, recomputed exactly per transition column in checked i128.
        for t in 0..matrix.transition_count {
            let mut component: i128 = 0;
            for p in 0..matrix.place_count {
                let term = (inv.weights[p] as i128).checked_mul(matrix.incidence[t][p] as i128);
                let Some(sum) = term.and_then(|term| component.checked_add(term)) else {
                    dropped.push(format!("{desc} - {}", weight_overflow(place_names, p)));
                    continue 'each;
                };
                component = sum;
            }
            if component != 0 {
                dropped.push(format!(
                    "{desc} - y*C is {component} (not 0) at {}",
                    column_name(flat, t)
                ));
                continue 'each;
            }
        }

        // constant = y·M0, recomputed exactly in checked i128.
        let mut recomputed: i128 = 0;
        for p in 0..matrix.place_count {
            let count = initial_marking.count(&place_names[p]) as i128;
            let term = (inv.weights[p] as i128).checked_mul(count);
            let Some(sum) = term.and_then(|term| recomputed.checked_add(term)) else {
                dropped.push(format!("{desc} - {}", weight_overflow(place_names, p)));
                continue 'each;
            };
            recomputed = sum;
        }
        if recomputed != inv.constant as i128 {
            dropped.push(format!(
                "{desc} - constant {} does not match exact y*M0 = {recomputed}",
                inv.constant
            ));
            continue;
        }

        valid.push(inv);
    }
    InvariantValidation { valid, dropped }
}

/// Names an incidence-matrix column: a flat transition, or one of the
/// env-injector columns `IncidenceMatrix::from_flat_net` appends after them.
/// Shared wording with the Java/TypeScript validators.
fn column_name(flat: &FlatNet, t: usize) -> String {
    match flat.transitions.get(t) {
        Some(ft) => format!("transition '{}'", ft.name),
        None => format!("env-injector column {}", t - flat.transitions.len()),
    }
}

/// The exact-arithmetic overflow drop reason, naming the place whose term
/// could not be recomputed. Shared wording with the Java/TypeScript validators.
fn weight_overflow(place_names: &[String], place: usize) -> String {
    format!(
        "weight overflow at place '{}' (exact value outside this implementation's \
         integer extraction range)",
        place_names.get(place).map(String::as_str).unwrap_or("?")
    )
}

/// Formats an invariant like the Phase-3 report lines (`2*p1 + p2 = 5`), tolerating
/// malformed shapes (out-of-range support indices render as `?`). The rendering is
/// canonical across the four implementations — ASCII `*`, weight 1 elided, empty
/// support as `0` — because it is embedded in the byte-diffed drop lines.
fn describe_invariant(inv: &PInvariant, place_names: &[String]) -> String {
    let terms: Vec<String> = inv
        .support
        .iter()
        .map(|&pid| {
            let name = place_names.get(pid).map(String::as_str).unwrap_or("?");
            match inv.weights.get(pid) {
                Some(1) => name.to_string(),
                Some(w) => format!("{w}*{name}"),
                None => format!("?*{name}"),
            }
        })
        .collect();
    if terms.is_empty() {
        format!("0 = {}", inv.constant)
    } else {
        format!("{} = {}", terms.join(" + "), inv.constant)
    }
}

/// `cp*a + cn*b` componentwise, or `None` on i64 overflow — so the caller drops the
/// generator and the colour bound falls back soundly rather than using wrapped values.
fn combine_row(cp: i64, a: &[i64], cn: i64, b: &[i64]) -> Option<Vec<i64>> {
    a.iter()
        .zip(b)
        .map(|(&x, &y)| {
            let p1 = cp.checked_mul(x)?;
            let p2 = cn.checked_mul(y)?;
            p1.checked_add(p2)
        })
        .collect()
}

/// Divides a (signature, weight) pair by the gcd of all its entries to keep the
/// integers small during elimination.
fn reduce_gcd(sig: &mut [i64], weight: &mut [i64]) {
    let mut g = 0u64;
    for &v in sig.iter().chain(weight.iter()) {
        g = gcd(g, v.unsigned_abs());
    }
    if g > 1 {
        let g = g as i64;
        for v in sig.iter_mut() {
            *v /= g;
        }
        for v in weight.iter_mut() {
            *v /= g;
        }
    }
}

/// Drops any row whose weight-support is a strict superset of another's — a non-minimal
/// combination that only inflates the set (and can cause combinatorial blow-up).
fn keep_support_minimal(rows: Vec<(Vec<i64>, Vec<i64>)>) -> Vec<(Vec<i64>, Vec<i64>)> {
    let supports: Vec<Vec<usize>> = rows
        .iter()
        .map(|(_, w)| (0..w.len()).filter(|&i| w[i] != 0).collect())
        .collect();
    let mut keep = vec![true; rows.len()];
    for i in 0..rows.len() {
        if !keep[i] {
            continue;
        }
        for j in 0..rows.len() {
            if i == j || !keep[j] {
                continue;
            }
            if supports[j].len() < supports[i].len()
                && supports[j].iter().all(|p| supports[i].contains(p))
            {
                keep[i] = false;
                break;
            }
        }
    }
    rows.into_iter()
        .zip(keep)
        .filter_map(|(r, k)| if k { Some(r) } else { None })
        .collect()
}

/// Checks if all places are covered by at least one P-invariant.
pub fn is_covered_by_invariants(invariants: &[PInvariant], place_count: usize) -> bool {
    let mut covered = vec![false; place_count];
    for inv in invariants {
        for &pid in &inv.support {
            if pid < place_count {
                covered[pid] = true;
            }
        }
    }
    covered.iter().all(|&c| c)
}

fn gcd_row(row: &[i64]) -> i64 {
    let mut g = 0u64;
    for v in row {
        g = gcd(g, v.unsigned_abs());
    }
    if g == 0 { 1 } else { g as i64 }
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

#[cfg(test)]
mod tests {

    /// A `FlatNet` for the synthetic-matrix tests: named places, named
    /// transitions with empty pre/post (the matrix under test supplies the
    /// numbers), and therefore no non-linear places.
    fn synthetic_flat(places: &[String], transitions: &[&str]) -> FlatNet {
        let place_index = places
            .iter()
            .enumerate()
            .map(|(i, n)| (n.clone(), i))
            .collect();
        FlatNet {
            place_count: places.len(),
            places: places.to_vec(),
            place_index,
            transitions: transitions
                .iter()
                .map(|name| crate::net_flattener::FlatTransition {
                    name: (*name).to_string(),
                    pre: vec![0; places.len()],
                    post: vec![0; places.len()],
                    inhibitor_places: Vec::new(),
                    read_places: Vec::new(),
                    reset_places: Vec::new(),
                    consume_all: Vec::new(),
                })
                .collect(),
        }
    }
    use super::*;
    use crate::incidence_matrix::IncidenceMatrix;
    use crate::net_flattener::flatten;
    use libpetri_core::action::fork;
    use libpetri_core::arc::reset;
    use libpetri_core::input::{all, at_least, exactly, one};
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    #[test]
    fn simple_chain_invariant() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);

        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p1", 1)
            .build();

        let invariants = compute_p_invariants(&matrix, &initial, &flat.places);
        assert!(!invariants.is_empty());
        // p1 + p2 = 1 (conservation law)
        let inv = &invariants[0];
        assert_eq!(inv.constant, 1);
    }

    #[test]
    fn cycle_invariant() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p1))
            .action(fork())
            .build();
        let net = PetriNet::builder("cycle").transitions([t1, t2]).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);

        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p1", 3)
            .build();

        let invariants = compute_p_invariants(&matrix, &initial, &flat.places);
        assert!(!invariants.is_empty());
        // p1 + p2 = 3
        let inv = &invariants[0];
        assert_eq!(inv.constant, 3);
    }

    #[test]
    fn is_covered() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);

        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p1", 1)
            .build();

        let invariants = compute_p_invariants(&matrix, &initial, &flat.places);
        assert!(is_covered_by_invariants(&invariants, flat.place_count));
    }

    #[test]
    fn validate_drops_fabricated_invariant_with_nonzero_y_c() {
        // p1 -> t1 -> p2: C column for t1 is (-1, +1). A weighting of p1 alone is
        // NOT an invariant (y·C = -1) even though its constant matches y·M0.
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);
        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p1", 1)
            .build();

        let p1_idx = flat.place_index["p1"];
        let mut weights = vec![0i64; flat.place_count];
        weights[p1_idx] = 1;
        let poisoned = PInvariant {
            weights,
            constant: 1, // y·M0 does match — only the y·C = 0 check catches this
            support: vec![p1_idx],
        };

        let genuine = compute_p_invariants(&matrix, &initial, &flat.places);
        assert!(!genuine.is_empty());
        let mut all = genuine.clone();
        all.push(poisoned);

        let validation = validate_invariants_exact(all, &matrix, &initial, &flat);
        assert_eq!(validation.valid.len(), genuine.len());
        assert_eq!(validation.dropped.len(), 1);
        assert!(
            validation.dropped[0].contains("y*C is") && validation.dropped[0].contains("(not 0) at transition '"),
            "reason must name the failing check: {}",
            validation.dropped[0]
        );
        assert!(
            validation.dropped[0].contains("p1"),
            "reason must identify the invariant: {}",
            validation.dropped[0]
        );
    }

    #[test]
    fn validate_drops_on_i128_overflow_in_component_recompute() {
        // Three i64::MAX weights against three i64::MAX incidence entries: each
        // product is ~2^126, and the third checked_add exceeds i128::MAX. The
        // invariant must be dropped for overflow — never kept on a wrapped value.
        let matrix = IncidenceMatrix {
            pre: vec![vec![0; 3]],
            post: vec![vec![i64::MAX; 3]],
            incidence: vec![vec![i64::MAX; 3]],
            place_count: 3,
            transition_count: 1,
        };
        let names = vec!["p0".to_string(), "p1".to_string(), "p2".to_string()];
        let initial = crate::marking_state::MarkingStateBuilder::new().build();
        let inv = PInvariant {
            weights: vec![i64::MAX; 3],
            constant: 0,
            support: vec![0, 1, 2],
        };

        let validation = validate_invariants_exact(
            vec![inv],
            &matrix,
            &initial,
            &synthetic_flat(&names, &["t0"]),
        );
        assert!(validation.valid.is_empty());
        assert_eq!(validation.dropped.len(), 1);
        assert!(
            validation.dropped[0].contains("weight overflow at place 'p2'"),
            "reason must name the overflow and the place: {}",
            validation.dropped[0]
        );
    }

    #[test]
    fn validate_drops_on_i128_overflow_in_constant_recompute() {
        // Zero transitions, so y·C holds trivially; the constant recompute
        // Σ i64::MAX · i64::MAX over three places overflows i128 on the third add.
        let matrix = IncidenceMatrix {
            pre: Vec::new(),
            post: Vec::new(),
            incidence: Vec::new(),
            place_count: 3,
            transition_count: 0,
        };
        let names = vec!["p0".to_string(), "p1".to_string(), "p2".to_string()];
        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p0", i64::MAX as usize)
            .tokens("p1", i64::MAX as usize)
            .tokens("p2", i64::MAX as usize)
            .build();
        let inv = PInvariant {
            weights: vec![i64::MAX; 3],
            constant: 0,
            support: vec![0, 1, 2],
        };

        let validation = validate_invariants_exact(vec![inv], &matrix, &initial, &synthetic_flat(&names, &[]));
        assert!(validation.valid.is_empty());
        assert_eq!(validation.dropped.len(), 1);
        assert!(
            validation.dropped[0].ends_with(
                "weight overflow at place 'p2' (exact value outside this implementation's \
                 integer extraction range)"
            ),
            "the C2 overflow reason, verbatim: {}",
            validation.dropped[0]
        );
    }

    #[test]
    fn validate_drops_on_constant_mismatch() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p1))
            .action(fork())
            .build();
        let net = PetriNet::builder("cycle").transitions([t1, t2]).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);
        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p1", 3)
            .build();

        // y = (1, 1) IS a null-space vector, but the claimed constant is wrong.
        let inv = PInvariant {
            weights: vec![1, 1],
            constant: 999,
            support: vec![0, 1],
        };
        let validation = validate_invariants_exact(vec![inv], &matrix, &initial, &flat);
        assert!(validation.valid.is_empty());
        assert_eq!(validation.dropped.len(), 1);
        assert!(
            validation.dropped[0].contains("constant 999 does not match exact y*M0 = 3"),
            "reason must show the recomputed constant: {}",
            validation.dropped[0]
        );
    }

    #[test]
    fn validate_drops_on_inconsistent_support() {
        // Support omits a nonzero weight: the encoders emit only the support
        // terms, so the encoded sum would differ from y·M.
        let matrix = IncidenceMatrix {
            pre: Vec::new(),
            post: Vec::new(),
            incidence: Vec::new(),
            place_count: 2,
            transition_count: 0,
        };
        let names = vec!["p0".to_string(), "p1".to_string()];
        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p0", 1)
            .tokens("p1", 1)
            .build();
        let inv = PInvariant {
            weights: vec![1, 1],
            constant: 2,
            support: vec![0], // missing index 1
        };

        let validation = validate_invariants_exact(vec![inv], &matrix, &initial, &synthetic_flat(&names, &[]));
        assert!(validation.valid.is_empty());
        assert_eq!(validation.dropped.len(), 1);
        assert!(
            validation.dropped[0].contains("support is inconsistent"),
            "reason must name the failing check: {}",
            validation.dropped[0]
        );
    }

    #[test]
    fn validate_passes_computed_invariants_unchanged() {
        // Existing cycle fixture: everything the Farkas elimination produces on a
        // well-behaved net must re-verify exactly and pass through untouched.
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p1))
            .action(fork())
            .build();
        let net = PetriNet::builder("cycle").transitions([t1, t2]).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);
        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p1", 3)
            .build();

        let computed = compute_p_invariants(&matrix, &initial, &flat.places);
        assert!(!computed.is_empty());
        let validation =
            validate_invariants_exact(computed.clone(), &matrix, &initial, &flat);
        assert!(validation.dropped.is_empty(), "{:?}", validation.dropped);
        assert_eq!(validation.valid.len(), computed.len());
        for (v, c) in validation.valid.iter().zip(&computed) {
            assert_eq!(v.weights, c.weights);
            assert_eq!(v.constant, c.constant);
            assert_eq!(v.support, c.support);
        }

        // The semiflow path feeds the coloured encoder's slot bound — it must
        // survive the same validation unchanged too.
        let semiflows = compute_p_semiflows(&matrix, &initial, &flat.places);
        assert!(!semiflows.is_empty());
        let sf_validation =
            validate_invariants_exact(semiflows.clone(), &matrix, &initial, &flat);
        assert!(sf_validation.dropped.is_empty(), "{:?}", sf_validation.dropped);
        assert_eq!(sf_validation.valid.len(), semiflows.len());
    }

    /// The H1 witness from `Strengthening.lean` (`consume_all_hypothesis_is_necessary`):
    /// `t: all(p0) → p1`, M0 = (2, 0). The linearized column is (−1, +1), so Farkas
    /// finds y = (1, 1) with constant 2, and the y·C = 0 gate alone would accept it —
    /// but the real firing drains BOTH tokens (y·M drops 2 → 1), so the invariant is
    /// false on the net and the linearity guard must drop it. The semiflow path feeds
    /// the coloured encoder's slot bound through the same validator, so it must drop
    /// its (1, 1) row too.
    #[test]
    fn h1_guard_drops_invariant_on_consume_all_place() {
        let p0 = Place::<i32>::new("p0");
        let p1 = Place::<i32>::new("p1");
        let t = Transition::builder("t")
            .input(all(&p0))
            .output(out_place(&p1))
            .action(fork())
            .build();
        let net = PetriNet::builder("h1_witness").transition(t).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);
        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p0", 2)
            .build();

        let invariants = compute_p_invariants(&matrix, &initial, &flat.places);
        assert!(
            !invariants.is_empty(),
            "Farkas must find y = (1, 1) on the linearized (−1, +1) column"
        );

        let validation =
            validate_invariants_exact(invariants, &matrix, &initial, &flat);
        assert!(
            validation.valid.is_empty(),
            "no invariant of the witness net may survive H1: {:?}",
            validation.valid
        );
        assert!(!validation.dropped.is_empty());
        assert!(
            validation.dropped[0].contains("non-linear consumption")
                && validation.dropped[0].contains("Strengthening.lean H1")
                && validation.dropped[0].contains("'p0'"),
            "reason must name the guard and the place: {}",
            validation.dropped[0]
        );

        // Semiflow symmetry: the same validator guards the coloured-plan bound path.
        let semiflows = compute_p_semiflows(&matrix, &initial, &flat.places);
        assert!(!semiflows.is_empty());
        let sf_validation =
            validate_invariants_exact(semiflows, &matrix, &initial, &flat);
        assert!(sf_validation.valid.is_empty(), "{:?}", sf_validation.valid);
        assert!(sf_validation.dropped[0].contains("Strengthening.lean H1"));
    }

    /// Reset analogue of the witness: `t: one(p0) → p1` with a reset arc on p0.
    /// Reset places never enter pre/post at all, so the column is (−1, +1) and
    /// Farkas again finds y = (1, 1) — false on the net because the firing clears
    /// p0 entirely. The guard's reset arm must drop it.
    #[test]
    fn h1_guard_drops_invariant_on_reset_place() {
        let p0 = Place::<i32>::new("p0");
        let p1 = Place::<i32>::new("p1");
        let t = Transition::builder("t")
            .input(one(&p0))
            .reset(reset(&p0))
            .output(out_place(&p1))
            .action(fork())
            .build();
        let net = PetriNet::builder("h1_reset").transition(t).build();

        let flat = flatten(&net);
        assert_eq!(flat.transitions[0].reset_places, vec![flat.place_index["p0"]]);
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);
        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p0", 2)
            .build();

        let invariants = compute_p_invariants(&matrix, &initial, &flat.places);
        assert!(!invariants.is_empty());

        let validation =
            validate_invariants_exact(invariants, &matrix, &initial, &flat);
        assert!(validation.valid.is_empty(), "{:?}", validation.valid);
        assert!(
            validation.dropped[0].contains("consume-all/reset place 'p0'")
                && validation.dropped[0].contains("Strengthening.lean H1"),
            "reason must name the guard and the place: {}",
            validation.dropped[0]
        );
    }

    /// `at_least(n)` is NOT linear in this codebase: it waits for n tokens but then
    /// consumes ALL available (`libpetri_core::input::consumption_count` returns
    /// `available` for `In::AtLeast`), which is exactly why the flattener lists it in
    /// `consume_all` alongside `In::All` and why Lean's `Card.consumesAll` models
    /// both. Invariants weighting an at-least place must be dropped too — with
    /// `at_least(1)` ≡ `all`, keeping them would reopen the witness's false Proven.
    #[test]
    fn h1_guard_drops_invariant_on_at_least_place() {
        let p0 = Place::<i32>::new("p0");
        let p1 = Place::<i32>::new("p1");
        let t = Transition::builder("t")
            .input(at_least(2, &p0))
            .output(out_place(&p1))
            .action(fork())
            .build();
        let net = PetriNet::builder("h1_at_least").transition(t).build();

        let flat = flatten(&net);
        assert_eq!(flat.transitions[0].consume_all, vec![flat.place_index["p0"]]);
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);
        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p0", 2)
            .build();

        let invariants = compute_p_invariants(&matrix, &initial, &flat.places);
        assert!(!invariants.is_empty());

        let validation =
            validate_invariants_exact(invariants, &matrix, &initial, &flat);
        assert!(validation.valid.is_empty(), "{:?}", validation.valid);
        assert!(
            validation.dropped[0].contains("consume-all/reset place 'p0'"),
            "{}",
            validation.dropped[0]
        );
    }

    /// `exactly(n)` consumes exactly n tokens — genuinely linear — so the guard must
    /// NOT fire: the y = (1, 2) law of `t: exactly(2, p0) → p1` is a real invariant
    /// and passes through untouched.
    #[test]
    fn h1_guard_keeps_exactly_input() {
        let p0 = Place::<i32>::new("p0");
        let p1 = Place::<i32>::new("p1");
        let t = Transition::builder("t")
            .input(exactly(2, &p0))
            .output(out_place(&p1))
            .action(fork())
            .build();
        let net = PetriNet::builder("h1_exactly").transition(t).build();

        let flat = flatten(&net);
        assert!(flat.transitions[0].consume_all.is_empty());
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);
        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p0", 2)
            .build();

        let invariants = compute_p_invariants(&matrix, &initial, &flat.places);
        assert!(!invariants.is_empty());

        let validation = validate_invariants_exact(
            invariants.clone(),
            &matrix,
            &initial,
            &flat,
        );
        assert!(validation.dropped.is_empty(), "{:?}", validation.dropped);
        assert_eq!(validation.valid.len(), invariants.len());
    }

    /// The guard is support-local, not net-global: on a net mixing a linear cycle
    /// with a consume-all drain, the cycle's invariant survives while any invariant
    /// weighting the drained place is dropped.
    #[test]
    fn h1_guard_is_support_local() {
        let pa = Place::<i32>::new("pA");
        let pb = Place::<i32>::new("pB");
        let px = Place::<i32>::new("pX");
        let py = Place::<i32>::new("pY");
        let t1 = Transition::builder("t1")
            .input(one(&pa))
            .output(out_place(&pb))
            .action(fork())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&pb))
            .output(out_place(&pa))
            .action(fork())
            .build();
        let t_all = Transition::builder("t_all")
            .input(all(&px))
            .output(out_place(&py))
            .action(fork())
            .build();
        let net = PetriNet::builder("mixed").transitions([t1, t2, t_all]).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);
        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("pA", 3)
            .tokens("pX", 2)
            .build();

        let invariants = compute_p_invariants(&matrix, &initial, &flat.places);
        let validation =
            validate_invariants_exact(invariants, &matrix, &initial, &flat);

        let pa_idx = flat.place_index["pA"];
        let px_idx = flat.place_index["pX"];
        assert!(
            validation.valid.iter().any(|inv| inv.weights[pa_idx] != 0),
            "the linear pA⇄pB conservation law must survive: {:?}",
            validation.valid
        );
        assert!(
            validation.valid.iter().all(|inv| inv.weights[px_idx] == 0),
            "nothing weighting the consume-all place may survive: {:?}",
            validation.valid
        );
        assert!(
            validation.dropped.iter().any(|r| r.contains("'pX'")),
            "{:?}",
            validation.dropped
        );
    }

    #[test]
    fn no_output_transition_no_invariant() {
        let p1 = Place::<i32>::new("p1");
        let t = Transition::builder("t1").input(one(&p1)).build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat, &[]);

        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p1", 1)
            .build();

        let invariants = compute_p_invariants(&matrix, &initial, &flat.places);
        // A transition with no output is a sink — it violates conservation
        // so no positive invariant covering p1 alone
        assert!(invariants.is_empty() || !is_covered_by_invariants(&invariants, flat.place_count));
    }
}
