use std::collections::{HashMap, HashSet};

use crate::place::{Place, PlaceRef};

/// Output specification with explicit split semantics.
///
/// Supports composite structures (XOR of ANDs, AND of XORs, etc.)
#[derive(Debug, Clone)]
pub enum Out {
    /// Leaf node: produce 1 token to a single output place. Mirrors `In::One`.
    One(PlaceRef),
    /// Leaf node: produce exactly N tokens to a single output place (N >= 1).
    /// Mirrors `In::Exactly`. Multiplicity is verification-only metadata; the
    /// runtime validator treats `Exactly` identically to `One`.
    Exactly { place: PlaceRef, count: usize },
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

/// Leaf output spec — produce 1 token to a single place. Mirrors `In::one`.
/// Prefixed with `out_` to disambiguate from `input::one` at call sites.
pub fn out_one<T: 'static>(p: &Place<T>) -> Out {
    Out::One(p.as_ref())
}

/// Leaf output spec — produce exactly N tokens to a single place. Mirrors `In::exactly`.
///
/// Multiplicity is verification-only metadata: the runtime validator treats
/// `Exactly(p, n)` identically to `One(p)`. The count is honoured by formal
/// analyzers (`StateClassGraph`, SMT `NetFlattener`).
///
/// # Panics
/// Panics if `count` is 0.
pub fn out_exactly<T: 'static>(count: usize, p: &Place<T>) -> Out {
    assert!(count >= 1, "count must be >= 1, got: {count}");
    Out::Exactly {
        place: p.as_ref(),
        count,
    }
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
    and(places.iter().map(|p| Out::One((*p).clone())).collect())
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
    xor(places.iter().map(|p| out_one(*p)).collect())
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
    timeout(after_ms, out_one(p))
}

/// Forward consumed input value to output place on timeout.
pub fn forward_input<I: 'static, O: 'static>(from: &Place<I>, to: &Place<O>) -> Out {
    Out::ForwardInput {
        from: from.as_ref(),
        to: to.as_ref(),
    }
}

// ==================== Helper Functions ====================

/// Collects all leaf place names from this output spec (flattened, no multiplicity).
pub fn all_places(out: &Out) -> HashSet<PlaceRef> {
    let mut result = HashSet::new();
    collect_places(out, &mut result);
    result
}

fn collect_places(out: &Out, result: &mut HashSet<PlaceRef>) {
    match out {
        Out::One(p) => {
            result.insert(p.clone());
        }
        Out::Exactly { place, .. } => {
            result.insert(place.clone());
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
/// Each branch is a multiset (place → integer count):
/// - `One(P)` contributes `{P → 1}`
/// - `Exactly(P, N)` contributes `{P → N}`
/// - `ForwardInput(_, to)` contributes `{to → 1}`
/// - `And` = Cartesian product of children's branches; on key collision, counts SUM
/// - `Xor` = list-concatenation of children's branches (one per alternative)
/// - `Timeout` = delegates to child
pub fn enumerate_branches(out: &Out) -> Vec<HashMap<PlaceRef, usize>> {
    match out {
        Out::One(p) => {
            let mut map = HashMap::new();
            map.insert(p.clone(), 1);
            vec![map]
        }
        Out::Exactly { place, count } => {
            let mut map = HashMap::new();
            map.insert(place.clone(), *count);
            vec![map]
        }
        Out::ForwardInput { to, .. } => {
            let mut map = HashMap::new();
            map.insert(to.clone(), 1);
            vec![map]
        }
        Out::And(children) => {
            let mut result: Vec<HashMap<PlaceRef, usize>> = vec![HashMap::new()];
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

fn cross_product(
    a: &[HashMap<PlaceRef, usize>],
    b: &[HashMap<PlaceRef, usize>],
) -> Vec<HashMap<PlaceRef, usize>> {
    let mut result = Vec::new();
    for map_a in a {
        for map_b in b {
            let mut merged = map_a.clone();
            for (place, count) in map_b {
                *merged.entry(place.clone()).or_insert(0) += *count;
            }
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
        Out::One(_) | Out::Exactly { .. } | Out::ForwardInput { .. } => None,
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
        Out::One(_) | Out::Exactly { .. } => vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::place::Place;

    #[test]
    fn one_creates_leaf() {
        let p = Place::<i32>::new("test");
        let out = out_one(&p);
        assert!(matches!(out, Out::One(ref r) if r.name() == "test"));
    }

    #[test]
    fn exactly_creates_leaf_with_count() {
        let p = Place::<i32>::new("test");
        let out = out_exactly(3, &p);
        assert!(matches!(&out, Out::Exactly { place, count } if place.name() == "test" && *count == 3));
    }

    #[test]
    #[should_panic(expected = "count must be >= 1")]
    fn exactly_zero_panics() {
        let p = Place::<i32>::new("test");
        out_exactly(0, &p);
    }

    #[test]
    fn all_places_from_and() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let out = and(vec![out_one(&a), out_one(&b)]);
        let places = all_places(&out);
        assert_eq!(places.len(), 2);
    }

    #[test]
    fn all_places_from_xor() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let out = xor(vec![out_one(&a), out_one(&b)]);
        let places = all_places(&out);
        assert_eq!(places.len(), 2);
    }

    #[test]
    fn all_places_includes_exactly() {
        let a = Place::<i32>::new("a");
        let places = all_places(&out_exactly(5, &a));
        assert_eq!(places.len(), 1);
    }

    #[test]
    fn enumerate_branches_one() {
        let a = Place::<i32>::new("a");
        let branches = enumerate_branches(&out_one(&a));
        assert_eq!(branches.len(), 1);
        assert_eq!(branches[0].get(&a.as_ref()), Some(&1));
    }

    #[test]
    fn enumerate_branches_exactly() {
        let a = Place::<i32>::new("a");
        let branches = enumerate_branches(&out_exactly(3, &a));
        assert_eq!(branches.len(), 1);
        assert_eq!(branches[0].get(&a.as_ref()), Some(&3));
    }

    #[test]
    fn enumerate_branches_and_repeated_place_sums() {
        let a = Place::<i32>::new("a");
        let out = and(vec![out_one(&a), out_one(&a), out_one(&a)]);
        let branches = enumerate_branches(&out);
        assert_eq!(branches.len(), 1);
        assert_eq!(branches[0].get(&a.as_ref()), Some(&3));
    }

    #[test]
    fn enumerate_branches_and_exactly_and_one_sum() {
        let a = Place::<i32>::new("a");
        let out = and(vec![out_exactly(2, &a), out_one(&a)]);
        let branches = enumerate_branches(&out);
        assert_eq!(branches.len(), 1);
        assert_eq!(branches[0].get(&a.as_ref()), Some(&3));
    }

    #[test]
    fn enumerate_branches_and_two_exactly_sum() {
        let a = Place::<i32>::new("a");
        let out = and(vec![out_exactly(2, &a), out_exactly(3, &a)]);
        let branches = enumerate_branches(&out);
        assert_eq!(branches.len(), 1);
        assert_eq!(branches[0].get(&a.as_ref()), Some(&5));
    }

    #[test]
    fn enumerate_branches_xor_same_place_different_counts() {
        let a = Place::<i32>::new("a");
        let out = xor(vec![out_one(&a), out_exactly(3, &a)]);
        let branches = enumerate_branches(&out);
        assert_eq!(branches.len(), 2);
        assert_eq!(branches[0].get(&a.as_ref()), Some(&1));
        assert_eq!(branches[1].get(&a.as_ref()), Some(&3));
    }

    #[test]
    fn enumerate_branches_and() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let out = and(vec![out_one(&a), out_one(&b)]);
        let branches = enumerate_branches(&out);
        assert_eq!(branches.len(), 1);
        assert_eq!(branches[0].len(), 2);
    }

    #[test]
    fn enumerate_branches_xor() {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let out = xor(vec![out_one(&a), out_one(&b)]);
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
            xor(vec![out_one(&a), out_one(&b)]),
            xor(vec![out_one(&c), out_one(&d)]),
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
        assert!(find_timeout(&out_one(&p)).is_none());
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
        xor(vec![out_one(&p)]);
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
