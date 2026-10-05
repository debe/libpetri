//! The colour-slot bound before the linear program ([NU-053]): the least `y·M0` over the
//! enumerated non-negative P-semiflows that weight every coloured place, else a summed
//! fallback. `colour_slot_bound` is a verbatim copy of the function `build_plan` called
//! until the LP replaced it (Lean `colourSlotBound`, `Plan.lean`, kept there as history).
//! The differential tests use it to show the LP bound is never above it. Test-only code,
//! shared through `#[path]`.

#![allow(dead_code)]

use libpetri_verification::incidence_matrix::IncidenceMatrix;
use libpetri_verification::marking_state::MarkingState;
use libpetri_verification::net_flattener::FlatNet;
use libpetri_verification::p_invariant::{self, PInvariant};

/// The gate-validated semiflows the old bound read, computed as the verifier did.
pub fn validated_semiflows(flat: &FlatNet, initial: &MarkingState) -> Vec<PInvariant> {
    let matrix = IncidenceMatrix::from_flat_net(flat, &[]);
    p_invariant::validate_invariants_exact(
        p_invariant::compute_p_semiflows(&matrix, initial, &flat.places),
        &matrix,
        initial,
        flat,
    )
    .valid
}

/// Verbatim copy of the old `name_coloured_encoder::colour_slot_bound`.
pub fn colour_slot_bound(coloured: &[usize], invariants: &[PInvariant]) -> Option<usize> {
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

/// The weighting behind [`colour_slot_bound`]: the covering semiflow it picked (the first
/// of least constant), or the sum of the semiflows its fallback added. `y·M0` of it is the
/// old bound.
pub fn colour_slot_weighting(n: usize, coloured: &[usize], invariants: &[PInvariant]) -> Option<Vec<i64>> {
    let w = |inv: &PInvariant, pid: usize| inv.weights.get(pid).copied().unwrap_or(0);
    let semiflows: Vec<&PInvariant> = invariants.iter().filter(|inv| inv.weights.iter().all(|&x| x >= 0)).collect();
    if let Some(best) = semiflows
        .iter()
        .filter(|inv| coloured.iter().all(|&pid| w(inv, pid) >= 1))
        .min_by_key(|inv| inv.constant)
    {
        return Some((0..n).map(|p| w(best, p)).collect());
    }
    let free: Vec<bool> = coloured
        .iter()
        .map(|&pid| semiflows.iter().any(|inv| inv.constant == 0 && w(inv, pid) >= 1))
        .collect();
    let mut sum = vec![0i64; n];
    let mut covered = free.clone();
    for inv in &semiflows {
        let take = if inv.constant == 0 {
            coloured.iter().any(|&pid| w(inv, pid) >= 1)
        } else {
            coloured.iter().enumerate().any(|(i, &pid)| !free[i] && w(inv, pid) >= 1)
        };
        if !take {
            continue;
        }
        for (i, &pid) in coloured.iter().enumerate() {
            if w(inv, pid) >= 1 {
                covered[i] = true;
            }
        }
        for (p, s) in sum.iter_mut().enumerate() {
            *s += w(inv, p);
        }
    }
    covered.iter().all(|&c| c).then_some(sum)
}
