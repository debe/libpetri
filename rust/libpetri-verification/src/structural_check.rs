use crate::marking_state::MarkingState;
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

/// Search budget for [`find_minimal_siphons`], in search nodes. Deciding
/// Commoner's condition is co-NP-complete, so the search is exponential in the
/// worst case; past this budget the check answers `Inconclusive` and the SMT
/// pipeline decides. Identical in every implementation.
const SIPHON_SEARCH_BUDGET: usize = 10_000;

/// Structural deadlock pre-check using Commoner's theorem (siphon/trap analysis).
///
/// An ordinary net is deadlock-free if every siphon contains a trap that is
/// marked under the initial marking. Checking every *minimal* siphon suffices,
/// since a trap inside a minimal siphon lies inside every siphon containing it.
/// So `NoPotentialDeadlock` needs two things: the search found **every**
/// minimal siphon, and each one's maximal trap holds a token in `initial`.
/// Answers `Inconclusive` for nets with more than 50 places, or when the siphon
/// search exceeds its 10 000-node budget.
pub fn structural_check(flat: &FlatNet, initial: &MarkingState) -> StructuralCheckResult {
    if flat.place_count > 50 {
        return StructuralCheckResult::Inconclusive;
    }

    let Some(siphons) = find_minimal_siphons(flat, SIPHON_SEARCH_BUDGET) else {
        return StructuralCheckResult::Inconclusive;
    };
    for siphon in &siphons {
        let trap = find_maximal_trap_in(flat, siphon);
        let marked = trap
            .iter()
            .any(|&pid| initial.count(&flat.places[pid]) > 0);
        if !marked {
            return StructuralCheckResult::PotentialDeadlock;
        }
    }

    StructuralCheckResult::NoPotentialDeadlock
}

/// Finds **all** minimal siphons, or `None` when the search exceeds `budget` nodes.
///
/// A siphon is a place set `S` such that every transition with an output in `S`
/// has at least one input in `S`. The search grows `S` from each start place;
/// where a producer into `S` has no input in `S`, it branches on each of that
/// producer's inputs. Every minimal siphon containing the start place is reached
/// by the branch that always picks an input inside it, so the search is complete.
/// Committing to one input instead (the first, or all of them at once) is not:
/// it can miss exactly the unmarked siphon that makes the net dead.
fn find_minimal_siphons(flat: &FlatNet, budget: usize) -> Option<Vec<Vec<usize>>> {
    let mut found: Vec<Vec<bool>> = Vec::new();
    let mut nodes = 0usize;
    for start_pid in 0..flat.place_count {
        let mut siphon = vec![false; flat.place_count];
        siphon[start_pid] = true;
        if !grow_siphon(flat, siphon, &mut found, &mut nodes, budget) {
            return None;
        }
    }

    // Keep only the minimal ones.
    let minimal: Vec<Vec<usize>> = found
        .iter()
        .enumerate()
        .filter(|(i, s)| {
            !found
                .iter()
                .enumerate()
                .any(|(j, other)| j != *i && is_subset(other, s))
        })
        .map(|(_, s)| (0..flat.place_count).filter(|&p| s[p]).collect())
        .collect();
    Some(minimal)
}

/// One node of the siphon search. Returns `false` when the budget is exhausted.
fn grow_siphon(
    flat: &FlatNet,
    siphon: Vec<bool>,
    found: &mut Vec<Vec<bool>>,
    nodes: &mut usize,
    budget: usize,
) -> bool {
    *nodes += 1;
    if *nodes > budget {
        return false;
    }
    // A superset of a siphon already found cannot lead to a new minimal one.
    if found.iter().any(|f| is_subset(f, &siphon)) {
        return true;
    }

    let violating = flat.transitions.iter().find(|ft| {
        let outputs_to_siphon = ft
            .post
            .iter()
            .enumerate()
            .any(|(pid, &count)| count > 0 && siphon[pid]);
        let has_input_in_siphon = ft
            .pre
            .iter()
            .enumerate()
            .any(|(pid, &count)| count > 0 && siphon[pid]);
        outputs_to_siphon && !has_input_in_siphon
    });

    let Some(ft) = violating else {
        found.push(siphon);
        return true;
    };
    // A producer with no inputs keeps any set holding its output marked: no siphon
    // on this branch. Otherwise branch on each input.
    for (pid, &count) in ft.pre.iter().enumerate() {
        if count > 0 {
            let mut next = siphon.clone();
            next[pid] = true;
            if !grow_siphon(flat, next, found, nodes, budget) {
                return false;
            }
        }
    }
    true
}

fn is_subset(a: &[bool], b: &[bool]) -> bool {
    a.iter().zip(b).all(|(&x, &y)| !x || y)
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
    use crate::marking_state::MarkingStateBuilder;
    use libpetri_core::action::fork;
    use libpetri_core::input::one;
    use libpetri_core::output::{and, out_place};
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
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let flat = flatten(&net);
        let result = structural_check(&flat, &MarkingState::new());
        assert_eq!(result, StructuralCheckResult::PotentialDeadlock);
    }

    #[test]
    fn cycle_no_deadlock() {
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
        let result = structural_check(&flat, &MarkingStateBuilder::new().tokens("p1", 1).build());
        // Cycle forms a siphon that contains its own trap, marked by p1
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
            .action(fork())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .input(one(&shared))
            .output(out_place(&out2))
            .action(fork())
            .build();

        let net = PetriNet::builder("deadlock").transitions([t1, t2]).build();

        let flat = flatten(&net);
        let result = structural_check(&flat, &MarkingState::new());
        // The shared place is a siphon without a trap (no transition produces back into it)
        assert_eq!(result, StructuralCheckResult::PotentialDeadlock);
    }

    fn ring(guarded: bool) -> PetriNet {
        // x -> y -> x; when guarded, each step also consumes and returns its own
        // guard place (g for t1, h for t2).
        let (g, h) = (Place::<i32>::new("g"), Place::<i32>::new("h"));
        let (x, y) = (Place::<i32>::new("x"), Place::<i32>::new("y"));
        let mut t1 = Transition::builder("t1").input(one(&x));
        let mut t2 = Transition::builder("t2").input(one(&y));
        if guarded {
            t1 = t1.input(one(&g)).output(and(vec![out_place(&y), out_place(&g)]));
            t2 = t2.input(one(&h)).output(and(vec![out_place(&x), out_place(&h)]));
        } else {
            t1 = t1.output(out_place(&y));
            t2 = t2.output(out_place(&x));
        }
        PetriNet::builder("ring")
            .transitions([t1.action(fork()).build(), t2.action(fork()).build()])
            .build()
    }

    /// The trap inside a siphon must be marked under the INITIAL marking: an
    /// unmarked ring has a trap and no token to keep it alive.
    #[test]
    fn an_unmarked_trap_does_not_count() {
        let flat = flatten(&ring(false));
        assert_eq!(
            structural_check(&flat, &MarkingState::new()),
            StructuralCheckResult::PotentialDeadlock
        );
    }

    /// Every minimal siphon, not one per start place. Growing a siphon by the
    /// FIRST input of each producer reaches only {g} and {h} here and misses the
    /// empty {x,y}; the net is dead at M0 with tokens stranded in g and h.
    #[test]
    fn a_siphon_behind_a_second_input_is_found() {
        let flat = flatten(&ring(true));
        let siphons = find_minimal_siphons(&flat, SIPHON_SEARCH_BUDGET).unwrap();
        let names: Vec<Vec<&str>> = siphons
            .iter()
            .map(|s| s.iter().map(|&p| flat.places[p].as_str()).collect())
            .collect();
        assert!(names.iter().any(|s| *s == ["x", "y"]), "{names:?}");
        let m0 = MarkingStateBuilder::new().tokens("g", 1).tokens("h", 1).build();
        assert_eq!(structural_check(&flat, &m0), StructuralCheckResult::PotentialDeadlock);

        let live = MarkingStateBuilder::new().tokens("g", 1).tokens("h", 1).tokens("x", 1).build();
        assert_eq!(structural_check(&flat, &live), StructuralCheckResult::NoPotentialDeadlock);
    }

    /// Adding EVERY input of a producer overshoots: `t1: a + c -> b + c`,
    /// `t2: b -> a` only yields {a,b,c}, whose trap is marked through c, and
    /// misses the minimal siphon {a,b}, empty at `{c:1}`.
    #[test]
    fn a_siphon_is_not_padded_with_every_input() {
        let (a, b, c) = (Place::<i32>::new("a"), Place::<i32>::new("b"), Place::<i32>::new("c"));
        let t1 = Transition::builder("t1")
            .input(one(&a))
            .input(one(&c))
            .output(and(vec![out_place(&b), out_place(&c)]))
            .action(fork())
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&b))
            .output(out_place(&a))
            .action(fork())
            .build();
        let flat = flatten(&PetriNet::builder("stranded").transitions([t1, t2]).build());
        let m0 = MarkingStateBuilder::new().tokens("c", 1).build();
        assert_eq!(structural_check(&flat, &m0), StructuralCheckResult::PotentialDeadlock);
    }

    /// An exhausted search is inconclusive, never a verdict.
    #[test]
    fn an_exhausted_search_is_inconclusive() {
        let flat = flatten(&ring(true));
        assert!(find_minimal_siphons(&flat, 1).is_none());
    }
}
