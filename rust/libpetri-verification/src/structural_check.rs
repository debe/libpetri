use crate::net_flattener::FlatNet;

/// Result of structural deadlock pre-check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StructuralCheckResult {
    /// No potential deadlock based on siphon/trap analysis.
    NoPotentialDeadlock,
    /// Potential deadlock detected.
    PotentialDeadlock,
    /// Structural analysis is inconclusive.
    Inconclusive,
}

/// Structural deadlock pre-check using Commoner's theorem (siphon/trap analysis).
///
/// For nets with <= 50 places, finds minimal siphons and checks if each contains a trap.
pub fn structural_check(flat: &FlatNet) -> StructuralCheckResult {
    if flat.place_count > 50 {
        return StructuralCheckResult::Inconclusive;
    }

    let siphons = find_minimal_siphons(flat);
    for siphon in &siphons {
        let trap = find_maximal_trap_in(flat, siphon);
        if trap.is_empty() {
            return StructuralCheckResult::PotentialDeadlock;
        }
    }

    StructuralCheckResult::NoPotentialDeadlock
}

/// Finds minimal siphons using fixed-point expansion.
fn find_minimal_siphons(flat: &FlatNet) -> Vec<Vec<usize>> {
    let mut siphons = Vec::new();

    // For each place, try to build a minimal siphon containing it
    for start_pid in 0..flat.place_count {
        let mut siphon = vec![false; flat.place_count];
        siphon[start_pid] = true;

        // Fixed-point expansion: add all places needed to close the siphon
        let mut changed = true;
        while changed {
            changed = false;
            for ft in &flat.transitions {
                // Check if this transition outputs to any siphon place
                let outputs_to_siphon = ft
                    .post
                    .iter()
                    .enumerate()
                    .any(|(pid, &count)| count > 0 && siphon[pid]);

                if outputs_to_siphon {
                    // All input places must be in the siphon
                    for (pid, &count) in ft.pre.iter().enumerate() {
                        if count > 0 && !siphon[pid] {
                            siphon[pid] = true;
                            changed = true;
                        }
                    }
                }
            }
        }

        let siphon_places: Vec<usize> = siphon
            .iter()
            .enumerate()
            .filter(|(_, in_s)| **in_s)
            .map(|(i, _)| i)
            .collect();

        // Check if it's truly minimal (not a superset of existing siphon)
        let is_superset = siphons
            .iter()
            .any(|existing: &Vec<usize>| existing.iter().all(|p| siphon_places.contains(p)));

        if !is_superset {
            siphons.push(siphon_places);
        }
    }

    siphons
}

/// Finds the maximal trap contained within a siphon using fixed-point contraction.
fn find_maximal_trap_in(flat: &FlatNet, siphon: &[usize]) -> Vec<usize> {
    let mut trap = vec![false; flat.place_count];
    for &pid in siphon {
        trap[pid] = true;
    }

    // Fixed-point contraction: remove places that don't satisfy trap property
    let mut changed = true;
    while changed {
        changed = false;
        for &pid in siphon {
            if !trap[pid] {
                continue;
            }

            // For a trap: every transition that consumes from pid must also produce into the trap
            let mut satisfies = true;
            for ft in &flat.transitions {
                if ft.pre[pid] > 0 {
                    // This transition consumes from pid
                    let produces_to_trap = ft
                        .post
                        .iter()
                        .enumerate()
                        .any(|(p, &count)| count > 0 && trap[p]);

                    if !produces_to_trap {
                        satisfies = false;
                        break;
                    }
                }
            }

            if !satisfies {
                trap[pid] = false;
                changed = true;
            }
        }
    }

    trap.iter()
        .enumerate()
        .filter(|(_, in_t)| **in_t)
        .map(|(i, _)| i)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net_flattener::flatten;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    #[test]
    fn simple_chain_potential_deadlock() {
        // A simple chain p1->t1->p2 IS a potential deadlock
        // because p2 is a terminal siphon with no trap
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        let result = structural_check(&flat);
        assert_eq!(result, StructuralCheckResult::PotentialDeadlock);
    }

    #[test]
    fn cycle_no_deadlock() {
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
        let result = structural_check(&flat);
        // Cycle forms a siphon that contains its own trap
        assert_eq!(result, StructuralCheckResult::NoPotentialDeadlock);
    }

    #[test]
    fn potential_deadlock_detected() {
        // Two transitions competing for shared resource without cycle
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let shared = Place::<i32>::new("shared");
        let out1 = Place::<i32>::new("out1");
        let out2 = Place::<i32>::new("out2");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .input(one(&shared))
            .output(out_place(&out1))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .input(one(&shared))
            .output(out_place(&out2))
            .build();

        let net = PetriNet::builder("deadlock").transitions([t1, t2]).build();

        let flat = flatten(&net);
        let result = structural_check(&flat);
        // The shared place is a siphon without a trap (no transition produces back into it)
        assert_eq!(result, StructuralCheckResult::PotentialDeadlock);
    }
}
