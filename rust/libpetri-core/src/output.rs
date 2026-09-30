use std::collections::{HashMap, HashSet};

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
    /// Timeout branch that activates if action exceeds duration.
    Timeout { after_ms: u64, child: Box<Out> },
    /// Forward consumed input to output on timeout.
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

/// The first place a single output branch of `out` names twice ([IO-011]) —
/// one choice at every `Xor`, nested `And`s flattened, a `Timeout` read as its
/// child, the `to` of a `ForwardInput` a leaf — or `None`. `Xor(And(P, A),
/// And(P, B))` has no duplicate: the two `P`s are in different alternatives.
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
