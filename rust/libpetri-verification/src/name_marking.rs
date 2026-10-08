//! The abstract **name-partition** layer for the ν-aware state class graph
//! ([NU-050], Route B).
//!
//! The plain [`crate::state_class_graph`] is name-blind: a marking is a
//! per-place token *count*, so a ν-join fires whenever the counts allow,
//! ignoring whether the consumed tokens actually share a correlation name. This
//! module adds, beside the count marking, an abstract partition of the
//! correlation tokens into **name-symbols**.
//!
//! A [`Sym`] is an opaque identity only — the analyzer never evaluates the
//! runtime name projection ([`libpetri_core::match_spec`]'s `KeyFn`), so a symbol
//! carries no value; only *distinctness* from other live symbols matters
//! ([NU-001]). Names are interchangeable, so two markings that differ only by a
//! permutation of symbols denote the same state. [`NameMarking::canonical_key`]
//! quotients them — the raw symbol ids never appear in a dedup key, which is what
//! keeps the graph finite when the number of simultaneously-live names is
//! structurally bounded (the lever that replaces Route A's budget `k`).

use std::collections::{BTreeMap, BTreeSet};

/// An abstract correlation-name symbol — opaque identity, no value ([NU-001]).
pub(crate) type Sym = u32;

/// The name-partition carried alongside a [`crate::state_class::StateClass`]:
/// for each *coloured* place, the multiset of live name-symbols holding tokens
/// there. Only coloured places appear; a place's total here equals its count in
/// the base count-marking (a debug invariant).
#[derive(Debug, Clone, Default)]
pub(crate) struct NameMarking {
    per_place: BTreeMap<String, BTreeMap<Sym, usize>>,
}

impl NameMarking {
    pub(crate) fn new() -> Self {
        Self {
            per_place: BTreeMap::new(),
        }
    }

    /// Adds `count` tokens of symbol `s` to a coloured place.
    pub(crate) fn add(&mut self, place: &str, s: Sym, count: usize) {
        if count == 0 {
            return;
        }
        *self
            .per_place
            .entry(place.to_string())
            .or_default()
            .entry(s)
            .or_insert(0) += count;
    }

    /// Removes `count` tokens of symbol `s` from a coloured place. Returns `false`
    /// (leaving the marking unchanged) when fewer than `count` are present — the
    /// caller must establish enablement first.
    pub(crate) fn remove(&mut self, place: &str, s: Sym, count: usize) -> bool {
        let Some(syms) = self.per_place.get_mut(place) else {
            return false;
        };
        let Some(have) = syms.get_mut(&s) else {
            return false;
        };
        if *have < count {
            return false;
        }
        *have -= count;
        if *have == 0 {
            syms.remove(&s);
        }
        if syms.is_empty() {
            self.per_place.remove(place);
        }
        true
    }

    /// Token count of symbol `s` in `place`.
    pub(crate) fn count_of(&self, place: &str, s: Sym) -> usize {
        self.per_place
            .get(place)
            .and_then(|m| m.get(&s))
            .copied()
            .unwrap_or(0)
    }

    /// Symbols holding at least one token in `place`.
    pub(crate) fn symbols_in(&self, place: &str) -> Vec<Sym> {
        self.per_place
            .get(place)
            .map(|m| m.keys().copied().collect())
            .unwrap_or_default()
    }

    /// The name-alignment predicate of [NU-055]: the places of `places` together hold at
    /// most one distinct symbol, so an empty place imposes nothing and a singleton list
    /// says that its place holds at most one. It compares symbols only for equality, so
    /// it is invariant under any permutation of them and a function of the canonical key
    /// (Lean `Aligned.alignedAll_key_inv`), and only membership in `places` counts. It
    /// walks the resident symbols in place, keeping the first one seen and stopping at
    /// the first other, which decides Lean `Aligned.alignedAll` (every pair of places,
    /// self pairs included) without building the set of names. Route B tests it on
    /// every class it stores.
    pub(crate) fn aligned(&self, places: &[impl AsRef<str>]) -> bool {
        let mut first: Option<Sym> = None;
        for syms in places.iter().filter_map(|p| self.per_place.get(p.as_ref())) {
            for &s in syms.keys() {
                match first {
                    None => first = Some(s),
                    Some(f) if f != s => return false,
                    Some(_) => {}
                }
            }
        }
        true
    }

    /// All live symbols across every coloured place.
    fn live_symbols(&self) -> BTreeSet<Sym> {
        self.per_place
            .values()
            .flat_map(|m| m.keys().copied())
            .collect()
    }

    /// Symmetry-canonical key over the coloured places (the finiteness
    /// mechanism). Two markings that differ only by a permutation of symbols
    /// produce an identical key ([NU-001]); the raw symbol ids are renumbered
    /// away. `coloured_order` must be the fixed ascending coloured-place ordering.
    ///
    /// Each symbol's *signature* is its token-count vector over `coloured_order`;
    /// symbols with equal signatures are interchangeable. Symbols are ranked by
    /// `(signature, raw id)` and the canonical ranks are emitted per place as a
    /// rank-multiset. The result is a complete invariant of the symbol-permutation
    /// orbit (the multiset of signatures), so dedup is sound *and* complete.
    pub(crate) fn canonical_key(&self, coloured_order: &[String]) -> String {
        let signature = |s: Sym| -> Vec<usize> {
            coloured_order.iter().map(|p| self.count_of(p, s)).collect()
        };

        let mut ranked: Vec<(Vec<usize>, Sym)> = self
            .live_symbols()
            .into_iter()
            .map(|s| (signature(s), s))
            .collect();
        ranked.sort();

        let mut rank_of: BTreeMap<Sym, usize> = BTreeMap::new();
        for (rank, (_, s)) in ranked.iter().enumerate() {
            rank_of.insert(*s, rank);
        }

        let parts: Vec<String> = coloured_order
            .iter()
            .map(|p| {
                let mut entries: Vec<(usize, usize)> = self
                    .per_place
                    .get(p)
                    .map(|m| m.iter().map(|(s, c)| (rank_of[s], *c)).collect())
                    .unwrap_or_default();
                entries.sort();
                let inner: Vec<String> =
                    entries.iter().map(|(r, c)| format!("{r}x{c}")).collect();
                format!("{p}:{{{}}}", inner.join(","))
            })
            .collect();
        parts.join("#")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn order() -> Vec<String> {
        vec!["branchA".to_string(), "branchB".to_string()]
    }

    #[test]
    fn permutation_invariant() {
        // {branchA:{X}, branchB:{Y}} vs the same with X and Y swapped → equal keys.
        let mut a = NameMarking::new();
        a.add("branchA", 0, 1);
        a.add("branchB", 1, 1);

        let mut b = NameMarking::new();
        b.add("branchA", 7, 1); // different raw symbol ids
        b.add("branchB", 3, 1);

        assert_eq!(a.canonical_key(&order()), b.canonical_key(&order()));
    }

    #[test]
    fn same_name_in_both_differs_from_split() {
        // One symbol in BOTH branches (same mint) ≠ two distinct symbols split.
        let mut same = NameMarking::new();
        same.add("branchA", 0, 1);
        same.add("branchB", 0, 1);

        let mut split = NameMarking::new();
        split.add("branchA", 0, 1);
        split.add("branchB", 1, 1);

        assert_ne!(same.canonical_key(&order()), split.canonical_key(&order()));
    }

    #[test]
    fn multiplicity_distinguished() {
        // Same symbol twice in a place ≠ two distinct symbols once each.
        let mut twice = NameMarking::new();
        twice.add("branchA", 0, 2);

        let mut two = NameMarking::new();
        two.add("branchA", 0, 1);
        two.add("branchA", 1, 1);

        assert_ne!(twice.canonical_key(&order()), two.canonical_key(&order()));
    }

    /// [NU-055]: empty places are aligned, one shared symbol is, two symbols in one
    /// place or different symbols across the places are not.
    #[test]
    fn nu055_aligned_reads_symbol_equality() {
        let mut nm = NameMarking::new();
        assert!(nm.aligned(&["box", "list"]), "both empty");
        nm.add("box", 4, 1);
        assert!(nm.aligned(&["box", "list"]), "list empty");
        assert!(nm.aligned(&["box"]), "one symbol in box");
        nm.add("list", 4, 2);
        assert!(nm.aligned(&["box", "list"]), "the same symbol, any count");
        nm.add("list", 9, 1);
        assert!(!nm.aligned(&["box", "list"]), "a second symbol in list");
        assert!(!nm.aligned(&["list"]), "list holds two names");
        assert!(nm.aligned(&["box", "ready"]), "a place without a row is empty");
        nm.remove("list", 9, 1);
        assert!(nm.aligned(&["box", "list"]), "a removed symbol leaves no trace");
    }

    /// [NU-055] AC7: one name across all. A place holding two names violates `S` whatever
    /// the others hold, which the pairwise reading of two places (every name in `p` equals
    /// every name in `q`) accepts when the other is empty; and places each holding one
    /// name violate it when the names differ.
    #[test]
    fn nu055_aligned_is_one_name_across_all_the_places() {
        let mut nm = NameMarking::new();
        nm.add("box", 0, 1);
        nm.add("box", 1, 1);
        assert!(!nm.aligned(&["box", "list"]));
        assert!(nm.aligned(&["list"]));
        let mut split = NameMarking::new();
        split.add("box", 0, 1);
        split.add("staged", 0, 1);
        split.add("list", 1, 1);
        assert!(split.aligned(&["box", "staged"]));
        assert!(!split.aligned(&["box", "staged", "list"]));
        assert!(!split.aligned(&["list", "box"]));
    }

    /// [NU-055] AC5: the predicate is invariant under name permutation. Every
    /// renaming of the symbols of a layer gives the same answer, and so does every
    /// layer with the same canonical key. Only membership in `S` counts: `S` reversed,
    /// or with a place repeated, reads the same.
    #[test]
    fn nu055_aligned_is_invariant_under_permutation() {
        let coloured = vec!["box".to_string(), "list".to_string(), "reply".to_string()];
        let layer = |rename: &dyn Fn(Sym) -> Sym| {
            let mut nm = NameMarking::new();
            nm.add("box", rename(0), 1);
            nm.add("reply", rename(0), 1);
            nm.add("reply", rename(1), 1);
            nm.add("list", rename(1), 1);
            nm
        };
        let renamings: [&dyn Fn(Sym) -> Sym; 3] = [&|s| s, &|s| 1 - s, &|s| 10 + 7 * s];
        let base = layer(renamings[0]);
        for rename in renamings {
            let renamed = layer(rename);
            assert_eq!(renamed.canonical_key(&coloured), base.canonical_key(&coloured));
            let singles = coloured.iter().map(|p| vec![p.clone()]);
            let pairs = coloured
                .iter()
                .flat_map(|p| coloured.iter().filter(move |q| *q != p).map(move |q| vec![p.clone(), q.clone()]));
            for list in singles.chain(pairs).chain([coloured.clone()]) {
                assert_eq!(renamed.aligned(&list), base.aligned(&list), "{list:?}");
                let reversed: Vec<String> = list.iter().rev().cloned().collect();
                assert_eq!(base.aligned(&reversed), base.aligned(&list), "{list:?} reversed");
                let repeated: Vec<String> = list.iter().chain(&list[..1]).cloned().collect();
                assert_eq!(base.aligned(&repeated), base.aligned(&list), "{list:?} repeated");
            }
        }
        assert!(!base.aligned(&["box", "list"]));
        assert!(!base.aligned(&["box", "reply"]));
        assert!(!base.aligned(&["reply"]));
        assert!(base.aligned(&["list"]));
        assert!(base.aligned(&["box"]));
    }

    #[test]
    fn remove_underflow_is_rejected() {
        let mut nm = NameMarking::new();
        nm.add("branchA", 0, 1);
        assert!(!nm.remove("branchA", 0, 2));
        assert!(nm.remove("branchA", 0, 1));
        assert_eq!(nm.count_of("branchA", 0), 0);
        assert!(nm.symbols_in("branchA").is_empty());
    }
}
