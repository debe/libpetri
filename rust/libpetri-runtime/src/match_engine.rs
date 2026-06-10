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

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

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

/// FIFO queue of `u64` timestamps with O(1)-amortised min-query (two-stack
/// method). Mirrors the ring's **FIFO-within-name** removal (`pop_front` removes
/// the earliest-inserted token, exactly as `ring_remove_matching` does) while
/// answering "oldest remaining timestamp" for the tie-break. A plain min-heap
/// would diverge from the ring whenever a name's tokens are inserted out of
/// timestamp order.
#[derive(Default)]
struct MinQueue {
    // each entry carries the running min from that element to the back of its
    // stack, so the queue min is min(in_stack.top.min, out_stack.top.min).
    in_stack: Vec<(u64, u64)>,
    out_stack: Vec<(u64, u64)>,
}

impl MinQueue {
    fn len(&self) -> usize {
        self.in_stack.len() + self.out_stack.len()
    }

    fn is_empty(&self) -> bool {
        self.in_stack.is_empty() && self.out_stack.is_empty()
    }

    fn push_back(&mut self, v: u64) {
        let m = self.in_stack.last().map_or(v, |&(_, mn)| mn.min(v));
        self.in_stack.push((v, m));
    }

    fn pop_front(&mut self) {
        if self.out_stack.is_empty() {
            while let Some((v, _)) = self.in_stack.pop() {
                let m = self.out_stack.last().map_or(v, |&(_, mn)| mn.min(v));
                self.out_stack.push((v, m));
            }
        }
        self.out_stack.pop();
    }

    fn min(&self) -> u64 {
        match (self.in_stack.last(), self.out_stack.last()) {
            (Some(&(_, a)), Some(&(_, b))) => a.min(b),
            (Some(&(_, a)), None) => a,
            (None, Some(&(_, b))) => b,
            (None, None) => u64::MAX,
        }
    }
}

/// Incremental equivalent of [`select_match_name`] for the common case where
/// every correlated input is `One`/`Exactly(n)` (fixed consume count).
///
/// `select_match_name` re-builds a full `name -> {count, oldest}` index over
/// every token on each call, so draining N ready correlation groups costs
/// O(N²). This maintains, per correlated input, a [`MinQueue`] of token
/// timestamps per name (FIFO-within-name removal, NU-020) plus a lazy-deletion
/// min-heap of ready names keyed by the same `(oldest_token, name)` order. Each
/// `add`/`consume` is O(log n) and [`best`](Self::best) is an O(1) read, so a
/// drain is O(N log N).
///
/// **Contract:** for any sequence of adds/consumes, `best()` returns exactly the
/// name `select_match_name` would for the equivalent marking — verified
/// byte-for-byte by `incremental_matches_select_byte_for_byte` (which uses
/// non-monotonic timestamps to exercise the FIFO-vs-oldest distinction). Callers
/// that have an `AtLeast`/`All` correlated input (variable consume count) must
/// fall back to [`select_match_name`]; build this only when every correlated
/// input is `One`/`Exactly`.
pub(crate) struct IncrementalMatcher {
    requireds: Vec<usize>,
    /// per input: name -> FIFO min-queue of its (guard-passing) token timestamps.
    ts: Vec<HashMap<NameId, MinQueue>>,
    /// candidate ready names by `(rep_ts, name)`; may hold stale entries.
    heap: BinaryHeap<Reverse<(u64, NameId)>>,
    /// name -> its current `rep_ts` while ready (the staleness oracle).
    ready: HashMap<NameId, u64>,
}

impl IncrementalMatcher {
    pub(crate) fn new(requireds: Vec<usize>) -> Self {
        let k = requireds.len();
        IncrementalMatcher {
            requireds,
            ts: (0..k).map(|_| HashMap::new()).collect(),
            heap: BinaryHeap::new(),
            ready: HashMap::new(),
        }
    }

    /// Add one (already guard-passing) token carrying `name` at `created_at` to
    /// correlated input `i`.
    pub(crate) fn add(&mut self, i: usize, name: NameId, created_at: u64) {
        self.ts[i].entry(name.clone()).or_default().push_back(created_at);
        self.refresh(name);
        self.clean_top();
    }

    /// Remove the `required` earliest-inserted tokens of `name` from every
    /// correlated input — exactly what the matched join firing consumes
    /// (FIFO-within-name per NU-020).
    pub(crate) fn consume(&mut self, name: &NameId) {
        for i in 0..self.requireds.len() {
            if let Some(q) = self.ts[i].get_mut(name) {
                for _ in 0..self.requireds[i] {
                    q.pop_front();
                }
                if q.is_empty() {
                    self.ts[i].remove(name);
                }
            }
        }
        self.refresh(name.clone());
        self.clean_top();
    }

    /// The name `select_match_name` would pick, or `None`. O(1) read; relies on
    /// `clean_top` having run after the last mutation (it always does).
    pub(crate) fn best(&self) -> Option<&NameId> {
        self.heap.peek().map(|r| &r.0.1)
    }

    /// `rep_ts(name)` = the oldest remaining token of `name` across the inputs,
    /// or `None` if some input lacks its required count — identical to the value
    /// `select_match_name` derives.
    fn rep_ts(&self, name: &NameId) -> Option<u64> {
        let mut rep = u64::MAX;
        for i in 0..self.requireds.len() {
            let q = self.ts[i].get(name)?;
            if q.len() < self.requireds[i] {
                return None;
            }
            rep = rep.min(q.min());
        }
        Some(rep)
    }

    fn refresh(&mut self, name: NameId) {
        match self.rep_ts(&name) {
            Some(rep) => {
                if self.ready.get(&name) != Some(&rep) {
                    self.ready.insert(name.clone(), rep);
                    self.heap.push(Reverse((rep, name)));
                }
            }
            None => {
                self.ready.remove(&name);
            }
        }
    }

    /// Pop stale entries so `heap.peek()` is a valid ready name (or empty).
    fn clean_top(&mut self) {
        loop {
            let stale = match self.heap.peek() {
                Some(Reverse((rep, name))) => self.ready.get(name) != Some(rep),
                None => false,
            };
            if stale {
                self.heap.pop();
            } else {
                break;
            }
        }
    }
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

    /// Reference pick: build the per-input index from the ground-truth tokens and
    /// defer to `select_match_name` (the contract the incremental matcher mirrors).
    fn reference_select(truth: &[Vec<(NameId, u64)>], requireds: &[usize]) -> Option<NameId> {
        let per_place: Vec<NameIndex> = truth
            .iter()
            .map(|toks| {
                let mut index = NameIndex::new();
                for (n, ts) in toks {
                    let e = index.entry(n.clone()).or_insert((0, u64::MAX));
                    e.0 += 1;
                    e.1 = e.1.min(*ts);
                }
                index
            })
            .collect();
        select_match_name(&per_place, requireds)
    }

    /// Tiny deterministic PRNG (no external rng crate; argless `Date::now` etc.
    /// are unavailable anyway).
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 16
        }
    }

    /// Differential test: for random add/consume sequences (2–3 inputs, required
    /// 1–2, multiple tokens per name → partial consume + rep_ts advance + ties),
    /// `IncrementalMatcher::best()` must equal `select_match_name` at every step.
    ///
    /// Timestamps are **random and non-monotonic** (not insertion-ordered), and
    /// the ground truth removes in **insertion order** (FIFO-within-name, like
    /// the ring) — so this exercises the FIFO-vs-oldest distinction a plain
    /// min-heap would get wrong.
    #[test]
    fn incremental_matches_select_byte_for_byte() {
        let names = [
            NameId::new("A"),
            NameId::new("B"),
            NameId::new("C"),
            NameId::new("D"),
        ];
        for seed in 0..400u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xDEAD_BEEF);
            let k = 2 + (rng.next() % 2) as usize; // 2 or 3 inputs
            let requireds: Vec<usize> = (0..k).map(|_| 1 + (rng.next() % 2) as usize).collect();
            let mut m = IncrementalMatcher::new(requireds.clone());
            // ground truth: per input, tokens in INSERTION order (= ring order).
            let mut truth: Vec<Vec<(NameId, u64)>> = vec![Vec::new(); k];

            for _ in 0..80 {
                if rng.next() % 3 < 2 {
                    // add a token (random, non-monotonic ts) to a random input
                    let i = (rng.next() % k as u64) as usize;
                    let name = names[(rng.next() % names.len() as u64) as usize].clone();
                    let ts = rng.next() % 40; // collisions + out-of-order on purpose
                    m.add(i, name.clone(), ts);
                    truth[i].push((name, ts));
                } else if let Some(pick) = reference_select(&truth, &requireds) {
                    // consume the agreed pick from both matcher and ground truth
                    assert_eq!(m.best(), Some(&pick), "best() diverged before consume (seed={seed})");
                    m.consume(&pick);
                    // remove the first `required` occurrences of pick in INSERTION
                    // order — exactly the ring's FIFO-within-name removal.
                    for (i, req) in requireds.iter().enumerate() {
                        let mut removed = 0;
                        truth[i].retain(|(n, _)| {
                            if removed < *req && *n == pick {
                                removed += 1;
                                false
                            } else {
                                true
                            }
                        });
                    }
                }
                assert_eq!(
                    m.best().cloned(),
                    reference_select(&truth, &requireds),
                    "best() diverged after op (seed={seed})"
                );
            }
        }
    }
}
