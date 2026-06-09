//! ν-net binding selection — the canonical name-correlation algorithm shared
//! by both executor backends (spec NU-020).
//!
//! A transition carrying a [`MatchSpec`](libpetri_core::match_spec::MatchSpec)
//! is enabled only when there is a single name present in every correlated
//! input with its required token count. The two backends differ only in how
//! they read tokens (ring buffer vs FIFO `Marking`); the *selection* — which
//! name satisfies the join, and the deterministic tie-break — lives here so it
//! is provably identical across backends (and is the reference the other
//! language ports mirror verbatim).

use std::collections::HashMap;

use libpetri_core::name::NameId;

/// Per-correlated-input name index: `name -> (count, min_created_at)`.
///
/// `count` is the number of (guard-passing) tokens carrying that name in the
/// input; `min_created_at` is the oldest such token's timestamp, used for the
/// tie-break.
pub(crate) type NameIndex = HashMap<NameId, (usize, u64)>;

/// Selects the satisfying correlation name across all correlated inputs, or
/// `None` when no single name is present in every input with at least its
/// required count.
///
/// Determinism (spec NU-020): among satisfying names, pick the one whose
/// oldest matched token (minimum `created_at` across the correlated inputs) is
/// earliest; break remaining ties by [`NameId`] order. This must be
/// byte-identical across backends and language ports.
pub(crate) fn select_match_name(per_place: &[NameIndex], requireds: &[usize]) -> Option<NameId> {
    if per_place.is_empty() {
        return None;
    }
    // Seed candidate names from the smallest index to minimise work; the
    // result is independent of which index seeds it.
    let seed = (0..per_place.len()).min_by_key(|&i| per_place[i].len())?;

    let mut best: Option<(NameId, u64)> = None;
    for (name, &(count, _)) in &per_place[seed] {
        if count < requireds[seed] {
            continue;
        }
        // The candidate must appear in every correlated input with enough
        // tokens; track the oldest matched token across inputs.
        let mut rep_ts = u64::MAX;
        let mut satisfied = true;
        for (j, index) in per_place.iter().enumerate() {
            match index.get(name) {
                Some(&(c, ts)) if c >= requireds[j] => rep_ts = rep_ts.min(ts),
                _ => {
                    satisfied = false;
                    break;
                }
            }
        }
        if !satisfied {
            continue;
        }
        let take = match &best {
            None => true,
            Some((best_name, best_ts)) => {
                rep_ts < *best_ts || (rep_ts == *best_ts && name < best_name)
            }
        };
        if take {
            best = Some((name.clone(), rep_ts));
        }
    }
    best.map(|(name, _)| name)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn idx(entries: &[(&str, usize, u64)]) -> NameIndex {
        entries
            .iter()
            .map(|&(n, c, ts)| (NameId::new(n), (c, ts)))
            .collect()
    }

    #[test]
    fn picks_common_name() {
        let a = idx(&[("X", 1, 5), ("Y", 1, 1)]);
        let b = idx(&[("Y", 1, 9)]);
        // Only Y is in both.
        assert_eq!(select_match_name(&[a, b], &[1, 1]), Some(NameId::new("Y")));
    }

    #[test]
    fn none_when_no_common_name() {
        let a = idx(&[("X", 1, 0)]);
        let b = idx(&[("Y", 1, 0)]);
        assert_eq!(select_match_name(&[a, b], &[1, 1]), None);
    }

    #[test]
    fn respects_required_count() {
        let a = idx(&[("X", 1, 0)]);
        let b = idx(&[("X", 1, 0)]);
        // Needs 2 of X in the second input but only 1 present.
        assert_eq!(select_match_name(&[a, b], &[1, 2]), None);
    }

    #[test]
    fn tie_break_oldest_then_name() {
        // X oldest token = min(0, 9) = 0 ; Y oldest = min(0, 9) = 0 → tie → "X" < "Y".
        let a = idx(&[("X", 1, 0), ("Y", 1, 9)]);
        let b = idx(&[("X", 1, 9), ("Y", 1, 0)]);
        assert_eq!(select_match_name(&[a, b], &[1, 1]), Some(NameId::new("X")));
    }

    #[test]
    fn tie_break_prefers_strictly_older() {
        let a = idx(&[("X", 1, 3), ("Y", 1, 1)]);
        let b = idx(&[("X", 1, 3), ("Y", 1, 8)]);
        // X oldest = 3, Y oldest = 1 → Y is strictly older.
        assert_eq!(select_match_name(&[a, b], &[1, 1]), Some(NameId::new("Y")));
    }
}
