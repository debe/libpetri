//! Trap refinement for the state-equation phase ([VER-018]), after Esparza,
//! Ledesma-Garza, Majumdar, Meyer and Niksic, "An SMT-based approach to coverability
//! analysis" (CAV 2014).
//!
//! A **trap** is a set of places `Q` such that every transition that removes a token
//! from `Q` also puts one into `Q`. A trap marked at `M0` stays marked in every
//! reachable marking, so a candidate that leaves an initially marked trap empty is not
//! reachable, and `Σ_{q∈Q} m_q ≥ 1` refutes it.
//!
//! "Removes a token" is generalised to the arcs the ordinary definition does not know:
//! a consume-all input or a reset arc on a place of `Q` removes tokens from `Q` whatever
//! its weight, so that transition must also put one into `Q`. Read and inhibitor arcs
//! remove nothing, and environment injection only adds tokens. No solver is involved.

use std::collections::BTreeSet;

use crate::net_flattener::{FlatNet, FlatTransition};
use crate::state_equation_query::{InequalityOrigin, MarkingInequality};

/// An initially marked trap the candidate leaves empty, as the inequality
/// `Σ_{q∈Q} m_q ≥ 1`, or `None` when there is none. The trap is shrunk to a locally
/// minimal one: a smaller trap is a stronger constraint on the next candidate.
pub fn refuting_trap(
    flat: &FlatNet,
    initial: &[i64],
    candidate: &[i64],
) -> Option<MarkingInequality> {
    let drains: Vec<Vec<usize>> = flat.transitions.iter().map(drained_places).collect();
    let feeds: Vec<Vec<usize>> = flat.transitions.iter().map(fed_places).collect();
    let mut empty: BTreeSet<usize> = BTreeSet::new();
    for (p, &count) in candidate.iter().enumerate() {
        if count == 0 {
            empty.insert(p);
        }
    }
    let mut trap = maximal_trap(&empty, &drains, &feeds);
    if !marked_in(&trap, initial) {
        return None;
    }
    // A snapshot of the trap we started from, while `trap` shrinks underneath: a place an
    // earlier round already dropped is no longer a candidate for dropping.
    let candidates: Vec<usize> = trap.iter().copied().collect();
    for p in candidates {
        if !trap.contains(&p) {
            continue;
        }
        let mut without = trap.clone();
        without.remove(&p);
        let smaller = maximal_trap(&without, &drains, &feeds);
        if marked_in(&smaller, initial) {
            trap = smaller;
        }
    }
    let mut weights = vec![0i128; flat.place_count];
    for &p in &trap {
        weights[p] = -1;
    }
    Some(MarkingInequality {
        weights,
        constant: -1,
        origin: InequalityOrigin::Trap,
    })
}

/// The largest trap inside `within` (possibly empty): repeatedly drop the places a
/// transition drains when it feeds nothing back into what is left. Traps are closed
/// under union, so the result contains every trap inside `within`.
fn maximal_trap(
    within: &BTreeSet<usize>,
    drains: &[Vec<usize>],
    feeds: &[Vec<usize>],
) -> BTreeSet<usize> {
    let mut trap = within.clone();
    let mut changed = true;
    while changed {
        changed = false;
        for t in 0..drains.len() {
            if !drains[t].iter().any(|p| trap.contains(p)) {
                continue;
            }
            if feeds[t].iter().any(|p| trap.contains(p)) {
                continue;
            }
            for p in &drains[t] {
                if trap.remove(p) {
                    changed = true;
                }
            }
        }
    }
    trap
}

/// The places a firing of `ft` can take tokens from: its inputs, consume-all places and
/// reset places.
fn drained_places(ft: &FlatTransition) -> Vec<usize> {
    let mut out: BTreeSet<usize> = ft.reset_places.iter().copied().collect();
    out.extend(ft.consume_all.iter().copied());
    for (p, &pre) in ft.pre.iter().enumerate() {
        if pre > 0 {
            out.insert(p);
        }
    }
    out.into_iter().collect()
}

/// The places a firing of `ft` puts at least one token into.
fn fed_places(ft: &FlatTransition) -> Vec<usize> {
    ft.post
        .iter()
        .enumerate()
        .filter_map(|(p, &post)| if post > 0 { Some(p) } else { None })
        .collect()
}

fn marked_in(places: &BTreeSet<usize>, marking: &[i64]) -> bool {
    places
        .iter()
        .any(|&p| marking.get(p).copied().unwrap_or(0) > 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net_flattener::flatten;
    use crate::state_equation_query::format_inequality;
    use libpetri_core::action::fork;
    use libpetri_core::input::{all, one};
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    fn marking_of(flat: &FlatNet, tokens: &[(&str, i64)]) -> Vec<i64> {
        let mut m = vec![0i64; flat.place_count];
        for (name, count) in tokens {
            m[flat.place_index[*name]] = *count;
        }
        m
    }

    /// `{a, b}` is a trap: `ab` moves a token a → b, `ba` moves it back. The same
    /// assertions the TypeScript port makes ([VER-018] test derivation).
    #[test]
    fn finds_an_initially_marked_trap_the_candidate_empties() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let loop_net = PetriNet::builder("loop")
            .transition(
                Transition::builder("ab")
                    .input(one(&a))
                    .output(out_place(&b))
                    .action(fork())
                    .build(),
            )
            .transition(
                Transition::builder("ba")
                    .input(one(&b))
                    .output(out_place(&a))
                    .action(fork())
                    .build(),
            )
            .build();
        let flat = flatten(&loop_net);
        let trap = refuting_trap(
            &flat,
            &marking_of(&flat, &[("a", 1)]),
            &marking_of(&flat, &[]),
        );
        let trap = trap.expect("an initially marked trap the empty candidate leaves empty");
        assert_eq!(format_inequality(&flat, &trap), "a + b >= 1");
    }

    /// A consume-all arc counts as a removal, so a drain out of `{a, b}` breaks the trap.
    #[test]
    fn a_consume_all_drain_is_not_a_trap() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let c = Place::<i32>::new("c");
        let drained = PetriNet::builder("drained")
            .transition(
                Transition::builder("ab")
                    .input(one(&a))
                    .output(out_place(&b))
                    .action(fork())
                    .build(),
            )
            .transition(
                Transition::builder("ba")
                    .input(one(&b))
                    .output(out_place(&a))
                    .action(fork())
                    .build(),
            )
            .transition(
                Transition::builder("drain")
                    .input(all(&b))
                    .output(out_place(&c))
                    .action(fork())
                    .build(),
            )
            .build();
        let flat = flatten(&drained);
        assert!(
            refuting_trap(
                &flat,
                &marking_of(&flat, &[("a", 1)]),
                &marking_of(&flat, &[("c", 1)])
            )
            .is_none()
        );
    }
}
