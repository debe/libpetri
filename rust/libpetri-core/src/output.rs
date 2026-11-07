use std::collections::{BTreeSet, HashMap, HashSet};

use crate::place::{Place, PlaceRef};

/// Output specification with explicit split semantics.
///
/// Supports composite structures (XOR of ANDs, AND of XORs, etc.)
///
/// A spec names **places, not counts**. Validation (\[IO-015\]) compares the
/// SET of places an action wrote against the branches' claims, so an action
/// that deposits several tokens into one named place is accepted — and every
/// analysis that enumerates branches ([`enumerate_branches`]: the state-class
/// graph, the SMT encoding, the ν fragment check) models exactly one token per
/// named place. Such a firing therefore does more than the analyses explore,
/// in the direction that can make a `proven` false. The executors report it
/// once per transition as a `WARN` log-message (\[IO-016\] AC4); a net meant
/// to be verified should produce one token per named place and express
/// multiplicity in its topology.
#[derive(Debug, Clone)]
pub enum Out {
    /// Leaf node: single output place.
    Place(PlaceRef),
    /// AND-split: ALL children must receive tokens.
    And(Vec<Out>),
    /// XOR-split: EXACTLY ONE child receives token.
    Xor(Vec<Out>),
    /// Timeout branch that activates if action exceeds duration. A spec holds
    /// at most one, nested or not (\[IO-013\]).
    Timeout { after_ms: u64, child: Box<Out> },
    /// Forward consumed input to output on timeout. Only inside the child of
    /// a `Timeout` (\[IO-014\]).
    ForwardInput { from: PlaceRef, to: PlaceRef },
}

// ==================== Factory Functions ====================

/// Leaf output spec for a single place.
pub fn out_place<T: 'static>(p: &Place<T>) -> Out {
    Out::Place(p.as_ref())
}

/// AND-split: all children must receive tokens.
///
/// # Panics
/// Panics if children is empty.
pub fn and(children: Vec<Out>) -> Out {
    assert!(!children.is_empty(), "AND requires at least 1 child");
    Out::And(children)
}

/// AND-split from places: all places must receive tokens.
pub fn and_places(places: &[&PlaceRef]) -> Out {
    and(places.iter().map(|p| Out::Place((*p).clone())).collect())
}

/// XOR-split: exactly one child receives token.
///
/// # Panics
/// Panics if fewer than 2 children.
pub fn xor(children: Vec<Out>) -> Out {
    assert!(children.len() >= 2, "XOR requires at least 2 children");
    Out::Xor(children)
}

/// XOR-split from places: exactly one place receives token.
pub fn xor_places<T: 'static>(places: &[&Place<T>]) -> Out {
    xor(places.iter().map(|p| out_place(*p)).collect())
}

/// Timeout output: activates if action exceeds duration.
///
/// # Panics
/// Panics if `after_ms` is 0.
pub fn timeout(after_ms: u64, child: Out) -> Out {
    assert!(after_ms > 0, "Timeout must be positive: {after_ms}");
    Out::Timeout {
        after_ms,
        child: Box::new(child),
    }
}

/// Timeout output pointing to a single place.
pub fn timeout_place<T: 'static>(after_ms: u64, p: &Place<T>) -> Out {
    timeout(after_ms, out_place(p))
}

/// Forward consumed input value to output place on timeout.
///
/// The transition build rejects it outside the child of a [`timeout`]
/// (\[IO-014\]).
pub fn forward_input<I: 'static, O: 'static>(from: &Place<I>, to: &Place<O>) -> Out {
    Out::ForwardInput {
        from: from.as_ref(),
        to: to.as_ref(),
    }
}

// ==================== Helper Functions ====================

/// Collects all leaf place names from this output spec (flattened).
pub fn all_places(out: &Out) -> HashSet<PlaceRef> {
    let mut result = HashSet::new();
    collect_places(out, &mut result);
    result
}

fn collect_places(out: &Out, result: &mut HashSet<PlaceRef>) {
    match out {
        Out::Place(p) => {
            result.insert(p.clone());
        }
        Out::ForwardInput { to, .. } => {
            result.insert(to.clone());
        }
        Out::And(children) | Out::Xor(children) => {
            for child in children {
                collect_places(child, result);
            }
        }
        Out::Timeout { child, .. } => {
            collect_places(child, result);
        }
    }
}

/// Enumerates all possible output branches for structural analysis.
///
/// - AND = single branch containing all child places (Cartesian product)
/// - XOR = one branch per alternative child
/// - Nested = Cartesian product for AND, union for XOR
///
/// A branch is a **set** of places: it says which places receive a token when
/// the branch is taken, not how many tokens each receives. Every analysis built
/// on this enumeration deposits one token per place of the chosen branch
/// (\[IO-016\]); an action that writes more is reported by the executor, not
/// modelled here. The branches are what an *action* writes: the analyses append
/// the timeout outcome — the `Timeout` child's places only, a `ForwardInput`
/// depositing one token per consumed token (\[IO-013\], \[IO-014\]) — after
/// them (`libpetri_verification::branch_outcomes`).
pub fn enumerate_branches(out: &Out) -> Vec<HashSet<PlaceRef>> {
    match out {
        Out::Place(p) => {
            let mut set = HashSet::new();
            set.insert(p.clone());
            vec![set]
        }
        Out::ForwardInput { to, .. } => {
            let mut set = HashSet::new();
            set.insert(to.clone());
            vec![set]
        }
        Out::And(children) => {
            let mut result = vec![HashSet::new()];
            for child in children {
                result = cross_product(&result, &enumerate_branches(child));
            }
            result
        }
        Out::Xor(children) => {
            let mut result = Vec::new();
            for child in children {
                result.extend(enumerate_branches(child));
            }
            result
        }
        Out::Timeout { child, .. } => enumerate_branches(child),
    }
}

/// Two leaves of one output branch that stand for the same place
/// ([`duplicate_in_branch_by`]).
#[derive(Debug, Clone, Copy)]
pub struct BranchDuplicate<'o> {
    /// The first leaf naming the place, as the spec names it.
    pub first: &'o PlaceRef,
    /// The second leaf, as the spec names it.
    pub second: &'o PlaceRef,
}

/// The place the walk of [IO-011] ("Which place the message names") reports: a
/// place some output branch of `out` names twice, or `None` when no branch does.
/// A `Timeout` is read as its child and the `to` of a `ForwardInput` is a leaf.
/// `And(Xor(A, B), Xor(B, A))` reports `B`; `Xor(And(P, A), And(P, B))` has no
/// duplicate: the two `P`s are in different alternatives.
pub fn duplicate_in_branch(out: &Out) -> Option<&PlaceRef> {
    duplicate_in_branch_by(out, |p| p.name()).map(|d| d.second)
}

/// [`duplicate_in_branch`] with `name_of` mapping each leaf to the place it
/// stands for: the identity for a spec as written, the port-to-host binding for
/// composition ([MOD-020]).
///
/// Linear in the spec, never enumerating branches: an `And`'s children combine
/// by cross product, so a place one child names in any of its branches and a
/// sibling names in any of its branches is named twice by some branch; a
/// `Xor`'s alternatives only pool their leaves. The walk is child by child, a
/// duplicate inside a child before one across siblings — the same place Java's
/// `ArcDiagnostics.duplicateInBranch` and TypeScript's `duplicateInBranch`
/// report.
pub fn duplicate_in_branch_by<'o, 'n>(
    out: &'o Out,
    name_of: impl Fn(&'o PlaceRef) -> &'n str + Copy,
) -> Option<BranchDuplicate<'o>> {
    scan_branches(out, name_of, &mut Leaves::default())
}

/// The leaves of a subtree in first-seen order, one per mapped name.
#[derive(Default)]
struct Leaves<'o, 'n> {
    order: Vec<(&'n str, &'o PlaceRef)>,
    seen: HashSet<&'n str>,
}

impl<'o, 'n> Leaves<'o, 'n> {
    fn pool(&mut self, name: &'n str, p: &'o PlaceRef) {
        if self.seen.insert(name) {
            self.order.push((name, p));
        }
    }
}

/// Adds the leaves of `out` to `leaves`, pooling across `Xor` alternatives, and
/// returns the first duplicate inside one `And` branch.
fn scan_branches<'o, 'n>(
    out: &'o Out,
    name_of: impl Fn(&'o PlaceRef) -> &'n str + Copy,
    leaves: &mut Leaves<'o, 'n>,
) -> Option<BranchDuplicate<'o>> {
    match out {
        Out::Place(p) => leaves.pool(name_of(p), p),
        Out::ForwardInput { to, .. } => leaves.pool(name_of(to), to),
        Out::Timeout { child, .. } => return scan_branches(child, name_of, leaves),
        Out::Xor(children) => {
            for child in children {
                if let Some(found) = scan_branches(child, name_of, leaves) {
                    return Some(found);
                }
            }
        }
        Out::And(children) => {
            let mut own: HashMap<&'n str, &'o PlaceRef> = HashMap::new();
            let mut own_order: Vec<(&'n str, &'o PlaceRef)> = Vec::new();
            for child in children {
                let mut child_leaves = Leaves::default();
                if let Some(found) = scan_branches(child, name_of, &mut child_leaves) {
                    return Some(found);
                }
                for (name, p) in child_leaves.order {
                    if let Some(&first) = own.get(name) {
                        return Some(BranchDuplicate { first, second: p });
                    }
                    own.insert(name, p);
                    own_order.push((name, p));
                }
            }
            for (name, p) in own_order {
                leaves.pool(name, p);
            }
        }
    }
    None
}

/// The number of `Timeout` nodes in `out`, nested and sibling ones alike.
/// A spec with more than one is rejected when the transition is built
/// (\[IO-013\]).
pub(crate) fn timeout_count(out: &Out) -> usize {
    match out {
        Out::Place(_) | Out::ForwardInput { .. } => 0,
        Out::And(children) | Out::Xor(children) => children.iter().map(timeout_count).sum(),
        Out::Timeout { child, .. } => 1 + timeout_count(child),
    }
}

/// Whether the child of a `Timeout` node of `out` holds an `Xor` node at any
/// depth. The executor makes the timeout deposit, so nothing chooses among
/// alternatives there: the transition build rejects such a spec (\[IO-013\]).
/// The build runs this after the `Timeout` count check, so at most one
/// `Timeout` node is searched.
pub(crate) fn xor_inside_timeout(out: &Out) -> bool {
    fn has_xor(out: &Out) -> bool {
        match out {
            Out::Xor(_) => true,
            Out::And(children) => children.iter().any(has_xor),
            Out::Timeout { child, .. } => has_xor(child),
            Out::Place(_) | Out::ForwardInput { .. } => false,
        }
    }
    match out {
        Out::Timeout { child, .. } => has_xor(child),
        Out::And(children) | Out::Xor(children) => children.iter().any(xor_inside_timeout),
        Out::Place(_) | Out::ForwardInput { .. } => false,
    }
}

/// The first `ForwardInput` of `out`, in pre-order with children left to
/// right, that is not inside the child of a `Timeout` node, as `(from, to)`.
/// A forward deposits only on the timeout outcome, so the transition build
/// rejects such a node (\[IO-014\]). A `Timeout`'s subtree is not searched.
pub(crate) fn forward_outside_timeout(out: &Out) -> Option<(&PlaceRef, &PlaceRef)> {
    match out {
        Out::ForwardInput { from, to } => Some((from, to)),
        Out::And(children) | Out::Xor(children) => {
            children.iter().find_map(forward_outside_timeout)
        }
        Out::Place(_) | Out::Timeout { .. } => None,
    }
}

/// Two output branches of one spec that claim the same set of places
/// ([`ambiguous_branches`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AmbiguousBranches<'o> {
    /// The smaller index, in [`enumerate_branches`] order (the `<t>_b<i>`
    /// numbering of \[VER-001\]).
    pub first: u128,
    /// The first index whose set equals the set of an earlier branch.
    pub second: u128,
    /// The places of branch `first`, in the order the spec names them
    /// (leaves left to right).
    pub places: Vec<&'o PlaceRef>,
}

/// The first pair of output branches of `out` that claim the same set of
/// places (\[IO-012\]), or `None`.
///
/// The branches are numbered as [`enumerate_branches`] lists them, one per
/// assignment (a choice of child at each `Xor` reached), a `ForwardInput`
/// claiming `to` and a `Timeout` its child's claim. The reported pair is the
/// first index `second` whose set equals an earlier branch's, and the smallest
/// such earlier index `first`: the result every implementation reports.
///
/// Place identity is the name, as everywhere in Rust. The spec must hold no
/// place twice in one branch (\[IO-011\], [`duplicate_in_branch`]), which the
/// transition build checks first.
///
/// Branches are not enumerated where the structure decides: under that
/// precondition an `And`'s children write disjoint sets of places, so two of
/// its branches are equal exactly when they are equal child by child. An `And`
/// of `Xor`s is therefore checked in time linear in the spec. Two alternatives
/// of one `Xor` that can name a common place are compared branch by branch,
/// but only over the branches that lie inside the other alternative's places,
/// walking the side with fewer such branches. That search is exponential only
/// when both alternatives have exponentially many branches inside each other's
/// places without ever claiming the same set.
///
/// Indices are exact up to `u128::MAX`; a spec with more branches than that
/// saturates them.
pub(crate) fn ambiguous_branches(out: &Out) -> Option<AmbiguousBranches<'_>> {
    let root = BranchNode::new(out);
    let (first, second) = root.first_ambiguity()?;
    Some(AmbiguousBranches {
        first,
        second,
        places: root.entry(first),
    })
}

/// An output spec annotated with its branch count and the names its branches
/// can write. A `Timeout` is read as its child.
struct BranchNode<'o> {
    kind: BranchKind<'o>,
    /// Number of branches, saturating.
    count: u128,
    /// Every place name some branch writes.
    pool: HashSet<&'o str>,
    /// Some branch claims no place (an `And` with no children).
    has_empty: bool,
}

enum BranchKind<'o> {
    Leaf(&'o PlaceRef),
    And(Vec<BranchNode<'o>>),
    Xor(Vec<BranchNode<'o>>),
}

impl<'o> BranchNode<'o> {
    fn new(out: &'o Out) -> Self {
        match out {
            Out::Place(p) | Out::ForwardInput { to: p, .. } => BranchNode {
                kind: BranchKind::Leaf(p),
                count: 1,
                pool: HashSet::from([p.name()]),
                has_empty: false,
            },
            Out::Timeout { child, .. } => BranchNode::new(child),
            Out::And(children) => {
                let children: Vec<_> = children.iter().map(BranchNode::new).collect();
                let count = children.iter().fold(1u128, |n, c| n.saturating_mul(c.count));
                let pool = children.iter().flat_map(|c| c.pool.iter().copied()).collect();
                let has_empty = children.iter().all(|c| c.has_empty);
                BranchNode { kind: BranchKind::And(children), count, pool, has_empty }
            }
            Out::Xor(children) => {
                let children: Vec<_> = children.iter().map(BranchNode::new).collect();
                let count = children.iter().fold(0u128, |n, c| n.saturating_add(c.count));
                let pool = children.iter().flat_map(|c| c.pool.iter().copied()).collect();
                let has_empty = children.iter().any(|c| c.has_empty);
                BranchNode { kind: BranchKind::Xor(children), count, pool, has_empty }
            }
        }
    }

    /// The places of branch `idx`, leaves left to right.
    fn entry(&self, mut idx: u128) -> Vec<&'o PlaceRef> {
        match &self.kind {
            BranchKind::Leaf(p) => vec![*p],
            BranchKind::And(children) => {
                // The first child varies slowest: its digit is the most significant.
                let mut digits = vec![0u128; children.len()];
                for (c, child) in children.iter().enumerate().rev() {
                    digits[c] = idx % child.count;
                    idx /= child.count;
                }
                children.iter().zip(digits).flat_map(|(c, d)| c.entry(d)).collect()
            }
            BranchKind::Xor(children) => {
                for child in children {
                    if idx < child.count {
                        return child.entry(idx);
                    }
                    idx -= child.count;
                }
                unreachable!("branch index out of range")
            }
        }
    }

    fn entry_set(&self, idx: u128) -> BTreeSet<&'o str> {
        self.entry(idx).into_iter().map(|p| p.name()).collect()
    }

    /// The number of branches whose places all lie in `pool`, saturating.
    fn count_within(&self, pool: &HashSet<&'o str>) -> u128 {
        match &self.kind {
            BranchKind::Leaf(p) => u128::from(pool.contains(p.name())),
            BranchKind::And(children) => children
                .iter()
                .fold(1u128, |n, c| n.saturating_mul(c.count_within(pool))),
            BranchKind::Xor(children) => children
                .iter()
                .fold(0u128, |n, c| n.saturating_add(c.count_within(pool))),
        }
    }

    /// Calls `f` with the index and set of every branch whose places all lie in
    /// `pool`, in index order, until `f` returns `true`. Returns whether it did.
    fn walk_within(
        &self,
        pool: &HashSet<&'o str>,
        f: &mut dyn FnMut(u128, &BTreeSet<&'o str>) -> bool,
    ) -> bool {
        match &self.kind {
            BranchKind::Leaf(p) => {
                pool.contains(p.name()) && f(0, &BTreeSet::from([p.name()]))
            }
            BranchKind::Xor(children) => {
                let mut offset = 0u128;
                for child in children {
                    if child.walk_within(pool, &mut |i, set| f(offset.saturating_add(i), set)) {
                        return true;
                    }
                    offset = offset.saturating_add(child.count);
                }
                false
            }
            BranchKind::And(children) => {
                walk_and_within(children, pool, 0, &BTreeSet::new(), f)
            }
        }
    }

    /// The smallest index of a branch whose set is `set`.
    fn first_index(&self, set: &BTreeSet<&'o str>) -> Option<u128> {
        if !set.iter().all(|n| self.pool.contains(n)) {
            return None;
        }
        match &self.kind {
            // `set` is inside the pool, which is the leaf's one place.
            BranchKind::Leaf(_) => (set.len() == 1).then_some(0),
            BranchKind::And(children) => {
                // The children's pools are disjoint (IO-011), so `set` splits by pool
                // and the smallest index takes the smallest digit in every child.
                let mut idx = 0u128;
                for child in children {
                    let part: BTreeSet<&str> =
                        set.iter().copied().filter(|n| child.pool.contains(n)).collect();
                    let digit = child.first_index(&part)?;
                    idx = idx.saturating_mul(child.count).saturating_add(digit);
                }
                Some(idx)
            }
            BranchKind::Xor(children) => {
                let mut offset = 0u128;
                for child in children {
                    if let Some(i) = child.first_index(set) {
                        return Some(offset.saturating_add(i));
                    }
                    offset = offset.saturating_add(child.count);
                }
                None
            }
        }
    }

    /// The first `(i, j)`, `i < j`, with equal branch sets, `j` smallest and
    /// then `i` smallest.
    fn first_ambiguity(&self) -> Option<(u128, u128)> {
        match &self.kind {
            BranchKind::Leaf(_) => None,
            BranchKind::And(children) => {
                // Branch sets are equal exactly when they are equal child by child. A
                // repeat in child `c` first shows with every other digit 0, at
                // `j_c * stride_c`; the last child with a repeat has the smallest.
                let mut stride = 1u128;
                for child in children.iter().rev() {
                    if let Some((i, j)) = child.first_ambiguity() {
                        return Some((i.saturating_mul(stride), j.saturating_mul(stride)));
                    }
                    stride = stride.saturating_mul(child.count);
                }
                None
            }
            BranchKind::Xor(children) => {
                let mut offset = 0u128;
                for (k, child) in children.iter().enumerate() {
                    let within = child.first_ambiguity();
                    let cross = children[..k]
                        .iter()
                        .filter_map(|earlier| first_shared(earlier, child))
                        .min();
                    match (within, cross) {
                        (Some((i, j)), c) if c.is_none_or(|c| j < c) => {
                            return Some((offset.saturating_add(i), offset.saturating_add(j)));
                        }
                        (_, Some(c)) => {
                            let set = child.entry_set(c);
                            let mut earlier_offset = 0u128;
                            for earlier in &children[..k] {
                                if let Some(i) = earlier.first_index(&set) {
                                    return Some((
                                        earlier_offset.saturating_add(i),
                                        offset.saturating_add(c),
                                    ));
                                }
                                earlier_offset = earlier_offset.saturating_add(earlier.count);
                            }
                            unreachable!("a shared set has an earlier index")
                        }
                        _ => {}
                    }
                    offset = offset.saturating_add(child.count);
                }
                None
            }
        }
    }
}

/// The `And` part of [`BranchNode::walk_within`]: the product of `children`,
/// the first child varying slowest, with `idx` and `set` the index and places
/// chosen so far.
fn walk_and_within<'o>(
    children: &[BranchNode<'o>],
    pool: &HashSet<&'o str>,
    idx: u128,
    set: &BTreeSet<&'o str>,
    f: &mut dyn FnMut(u128, &BTreeSet<&'o str>) -> bool,
) -> bool {
    let Some((child, rest)) = children.split_first() else {
        return f(idx, set);
    };
    child.walk_within(pool, &mut |i, part| {
        let mut joined = set.clone();
        joined.extend(part.iter().copied());
        walk_and_within(rest, pool, idx.saturating_mul(child.count).saturating_add(i), &joined, f)
    })
}

/// The smallest index in `later` of a branch whose set is also a branch of
/// `earlier`. A shared set lies inside both alternatives' places, so only the
/// branches of each side inside the other's places are candidates; the search
/// walks the side with fewer of them.
fn first_shared<'o>(earlier: &BranchNode<'o>, later: &BranchNode<'o>) -> Option<u128> {
    if earlier.pool.is_disjoint(&later.pool) && !(earlier.has_empty && later.has_empty) {
        return None;
    }
    let earlier_n = earlier.count_within(&later.pool);
    let later_n = later.count_within(&earlier.pool);
    if earlier_n == 0 || later_n == 0 {
        return None;
    }
    let mut found = None;
    if earlier_n <= later_n {
        earlier.walk_within(&later.pool, &mut |_, set| {
            if let Some(j) = later.first_index(set) {
                found = Some(found.map_or(j, |f: u128| f.min(j)));
            }
            false
        });
    } else {
        // Index order: the first hit is the smallest.
        later.walk_within(&earlier.pool, &mut |j, set| {
            let hit = earlier.first_index(set).is_some();
            if hit {
                found = Some(j);
            }
            hit
        });
    }
    found
}

fn cross_product(a: &[HashSet<PlaceRef>], b: &[HashSet<PlaceRef>]) -> Vec<HashSet<PlaceRef>> {
    let mut result = Vec::new();
    for set_a in a {
        for set_b in b {
            let mut merged = set_a.clone();
            merged.extend(set_b.iter().cloned());
            result.push(merged);
        }
    }
    result
}

/// Recursively searches the output spec for a Timeout node.
pub fn find_timeout(out: &Out) -> Option<(u64, &Out)> {
    match out {
        Out::Timeout { after_ms, child } => Some((*after_ms, child)),
        Out::And(children) | Out::Xor(children) => {
            for child in children {
                if let Some(found) = find_timeout(child) {
                    return Some(found);
                }
            }
            None
        }
        Out::Place(_) | Out::ForwardInput { .. } => None,
    }
}

/// Recursively finds all ForwardInput nodes in the output spec.
pub fn find_forward_inputs(out: &Out) -> Vec<(PlaceRef, PlaceRef)> {
    match out {
        Out::ForwardInput { from, to } => vec![(from.clone(), to.clone())],
        Out::And(children) | Out::Xor(children) => {
            children.iter().flat_map(find_forward_inputs).collect()
        }
        Out::Timeout { child, .. } => find_forward_inputs(child),
        Out::Place(_) => vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::place::Place;

    #[test]
    fn out_place_creates_leaf() {
        let p = Place::<i32>::new("test");
        let out = out_place(&p);
        assert!(matches!(out, Out::Place(ref r) if r.name() == "test"));
    }

    #[test]
    fn all_places_from_and() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let out = and(vec![out_place(&a), out_place(&b)]);
        let places = all_places(&out);
        assert_eq!(places.len(), 2);
    }

    #[test]
    fn all_places_from_xor() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let out = xor(vec![out_place(&a), out_place(&b)]);
        let places = all_places(&out);
        assert_eq!(places.len(), 2);
    }

    #[test]
    fn enumerate_branches_place() {
        let a = Place::<i32>::new("a");
        let branches = enumerate_branches(&out_place(&a));
        assert_eq!(branches.len(), 1);
        assert_eq!(branches[0].len(), 1);
    }

    #[test]
    fn enumerate_branches_and() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let out = and(vec![out_place(&a), out_place(&b)]);
        let branches = enumerate_branches(&out);
        assert_eq!(branches.len(), 1);
        assert_eq!(branches[0].len(), 2);
    }

    #[test]
    fn enumerate_branches_xor() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let out = xor(vec![out_place(&a), out_place(&b)]);
        let branches = enumerate_branches(&out);
        assert_eq!(branches.len(), 2);
    }

    #[test]
    fn enumerate_branches_and_of_xors() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let c = Place::<i32>::new("c");
        let d = Place::<i32>::new("d");
        let out = and(vec![
            xor(vec![out_place(&a), out_place(&b)]),
            xor(vec![out_place(&c), out_place(&d)]),
        ]);
        let branches = enumerate_branches(&out);
        assert_eq!(branches.len(), 4); // 2x2 Cartesian product
    }

    #[test]
    fn find_timeout_present() {
        let p = Place::<i32>::new("timeout");
        let out = timeout_place(5000, &p);
        assert!(find_timeout(&out).is_some());
    }

    #[test]
    fn find_timeout_absent() {
        let p = Place::<i32>::new("a");
        assert!(find_timeout(&out_place(&p)).is_none());
    }

    #[test]
    #[should_panic(expected = "AND requires at least 1 child")]
    fn and_empty_panics() {
        and(vec![]);
    }

    #[test]
    #[should_panic(expected = "XOR requires at least 2 children")]
    fn xor_one_panics() {
        let p = Place::<i32>::new("a");
        xor(vec![out_place(&p)]);
    }

    /// [`ambiguous_branches`] reports what the naive algorithm of IO-012 reports:
    /// enumerate in [`enumerate_branches`] order, first `j` with an earlier equal
    /// set, smallest such `i`, places of `i` in leaf order.
    #[test]
    fn ambiguous_branches_agrees_with_enumeration() {
        fn leaves(o: &Out) -> Vec<Vec<String>> {
            match o {
                Out::Place(p) | Out::ForwardInput { to: p, .. } => vec![vec![p.name().into()]],
                Out::Timeout { child, .. } => leaves(child),
                Out::Xor(cs) => cs.iter().flat_map(leaves).collect(),
                Out::And(cs) => cs.iter().fold(vec![vec![]], |acc, c| {
                    let lc = leaves(c);
                    acc.iter()
                        .flat_map(|a| lc.iter().map(move |b| [a.clone(), b.clone()].concat()))
                        .collect()
                }),
            }
        }
        fn naive(o: &Out) -> Option<(u128, u128, Vec<String>)> {
            let ls = leaves(o);
            let sets: Vec<BTreeSet<&String>> = ls.iter().map(|l| l.iter().collect()).collect();
            for j in 0..sets.len() {
                if let Some(i) = (0..j).find(|&i| sets[i] == sets[j]) {
                    return Some((i as u128, j as u128, ls[i].clone()));
                }
            }
            None
        }
        let mut seed: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut next = move |n: u64| {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (seed >> 33) % n
        };
        fn random_spec(next: &mut impl FnMut(u64) -> u64, depth: u32) -> Out {
            let name = |next: &mut dyn FnMut(u64) -> u64| format!("p{}", next(5));
            match if depth == 0 { 0 } else { next(4) } {
                // An empty `And` claims no place: two of them in one `Xor` clash.
                0 if next(10) == 0 => Out::And(vec![]),
                0 => Out::Place(PlaceRef::new(name(next))),
                1 => Out::And((0..1 + next(3)).map(|_| random_spec(next, depth - 1)).collect()),
                _ => Out::Xor((0..2 + next(2)).map(|_| random_spec(next, depth - 1)).collect()),
            }
        }
        let mut checked = 0;
        for _ in 0..4000 {
            let o = random_spec(&mut next, 3);
            if duplicate_in_branch(&o).is_some() {
                continue;
            }
            checked += 1;
            let got = ambiguous_branches(&o).map(|a| {
                (a.first, a.second, a.places.iter().map(|p| p.name().to_string()).collect())
            });
            assert_eq!(got, naive(&o), "{o:?}");
        }
        assert!(checked > 500, "{checked}");
    }

    #[test]
    fn forward_input_spec() {
        let from = Place::<i32>::new("from");
        let to = Place::<i32>::new("to");
        let out = forward_input(&from, &to);
        let fis = find_forward_inputs(&out);
        assert_eq!(fis.len(), 1);
        assert_eq!(fis[0].0.name(), "from");
        assert_eq!(fis[0].1.name(), "to");
    }
}
