use crate::incidence_matrix::IncidenceMatrix;
use crate::marking_state::MarkingState;

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
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::incidence_matrix::IncidenceMatrix;
    use crate::net_flattener::flatten;
    use libpetri_core::input::one;
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
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat);

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
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p1))
            .build();
        let net = PetriNet::builder("cycle").transitions([t1, t2]).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat);

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
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat);

        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p1", 1)
            .build();

        let invariants = compute_p_invariants(&matrix, &initial, &flat.places);
        assert!(is_covered_by_invariants(&invariants, flat.place_count));
    }

    #[test]
    fn no_output_transition_no_invariant() {
        let p1 = Place::<i32>::new("p1");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        let matrix = IncidenceMatrix::from_flat_net(&flat);

        let initial = crate::marking_state::MarkingStateBuilder::new()
            .tokens("p1", 1)
            .build();

        let invariants = compute_p_invariants(&matrix, &initial, &flat.places);
        // A transition with no output is a sink — it violates conservation
        // so no positive invariant covering p1 alone
        assert!(invariants.is_empty() || !is_covered_by_invariants(&invariants, flat.place_count));
    }
}
