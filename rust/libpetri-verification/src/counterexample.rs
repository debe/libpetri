//! Decoding z3's refutation output into replayable counterexample material.
//!
//! There is exactly one decoder: [`decode_state_set`], which collects the
//! ground `Reachable` facts of a `:produce-proofs` refutation into a SET. The
//! ordered trace a caller sees is reconstructed from that set by the abstract
//! replay ([`crate::abstract_replay`]) — the proof printer's traversal order is
//! not a firing order and was never safe to read as one.

use crate::marking_state::MarkingState;
#[allow(unused_imports)]
use crate::net_flattener::FlatNet;

/// A counterexample trace: markings and the step labels between them.
#[derive(Debug, Clone)]
pub struct DecodedTrace {
    pub trace: Vec<MarkingState>,
    pub transitions: Vec<String>,
}

impl DecodedTrace {
    pub fn empty() -> Self {
        Self {
            trace: Vec::new(),
            transitions: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.trace.is_empty()
    }
}

/// Collects the ground `Reachable(...)` applications from a z3 refutation
/// proof into a state SET (C3).
///
/// When the HORN script is run with `:produce-proofs` and `(get-proof)`, the
/// unsat (VIOLATED) answer contains a hyper-resolution proof whose
/// conclusions are ground `Reachable` facts — e.g. `(Reachable 2 0)` — one
/// per state Spacer stepped through (verified empirically on z3 4.13). This
/// decoder deliberately returns a SET: proof traversal order is an artifact
/// of the proof printer and is NOT trusted as a trace — the abstract replay
/// ([`crate::abstract_replay`]) reconstructs the order by search.
///
/// Applications with non-ground arguments (rule bodies quantify `Reachable`
/// over variables) or the wrong arity are skipped; a malformed proof simply
/// yields a smaller (possibly empty) set, never an error.
#[cfg(feature = "z3")]
pub fn decode_state_set(
    answer_str: &str,
    flat: &FlatNet,
) -> std::collections::BTreeSet<Vec<i64>> {
    use crate::smt_verifier::sexpr_end;

    let mut set = std::collections::BTreeSet::new();
    for head in ["(Reachable", "(|Reachable|"] {
        let mut from = 0;
        while let Some(pos) = answer_str[from..].find(head) {
            let start = from + pos;
            from = start + head.len();
            // Word boundary: "(Reachable" must not match "(ReachableFoo …".
            if head == "(Reachable"
                && !answer_str[from..]
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_whitespace() || c == ')')
            {
                continue;
            }
            let Some(end) = sexpr_end(answer_str, start) else {
                break;
            };
            // Interior between the head symbol and the closing paren.
            let inner = &answer_str[start + head.len()..end - 1];
            if let Some(args) = parse_ground_int_args(inner) {
                if args.len() == flat.place_count {
                    set.insert(args);
                }
            }
        }
    }
    set
}

/// Parses an application's argument text into integers, accepting only GROUND
/// arguments: bare integer literals (`3`, `-1`) and the SMT-LIB negation form
/// `(- 3)`. Any other token — a bound variable (`A`, `m0`), a nested
/// expression — makes the application non-ground: returns `None`.
#[cfg(feature = "z3")]
fn parse_ground_int_args(inner: &str) -> Option<Vec<i64>> {
    let mut args = Vec::new();
    let mut rest = inner.trim_start();
    while !rest.is_empty() {
        if let Some(stripped) = rest.strip_prefix('(') {
            // Only the `(- N)` form is ground.
            let close = stripped.find(')')?;
            let body = &stripped[..close];
            if body.contains('(') {
                return None;
            }
            let negated = body.trim().strip_prefix('-')?.trim();
            let n: i64 = negated.parse().ok()?;
            args.push(-n);
            rest = stripped[close + 1..].trim_start();
        } else {
            let token_end = rest
                .find(|c: char| c.is_whitespace() || c == '(' || c == ')')
                .unwrap_or(rest.len());
            let token = &rest[..token_end];
            args.push(token.parse().ok()?);
            rest = rest[token_end..].trim_start();
        }
    }
    Some(args)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_trace() {
        let trace = DecodedTrace::empty();
        assert!(trace.is_empty());
        assert!(trace.transitions.is_empty());
    }

    #[cfg(feature = "z3")]
    #[test]
    fn decode_state_set_from_proof_text() {
        use std::collections::HashMap;

        let flat = FlatNet {
            places: vec!["p0".into(), "p1".into()],
            place_index: HashMap::from([("p0".into(), 0), ("p1".into(), 1)]),
            place_count: 2,
            transitions: Vec::new(),
        };

        // Shaped like a real z3 4.13 HORN refutation: ground applications
        // inline in hyper-res steps, variable-argument applications in rule
        // bodies, duplicates, and a |quoted| head.
        let proof = r#"unsat
((set-logic HORN)
(declare-fun query!0 () Bool)
(proof
(let (($x143 (forall ((A Int) (B Int) )(let (($x41 (Reachable A B)))
 (=> (and (Reachable A B) (>= A 1)) $x41)))))
 (let ((@x723 ((_ hyper-res 0 0 0 1) (asserted $x143) ((_ hyper-res 0 0) (asserted (Reachable 2 0)) (Reachable 2 0)) (Reachable 1 1))))
 (let ((@x9 (|Reachable| 0 2)))
 (mp @x723 (asserted (Reachable (- 1) 3)) false))))))
"#;
        let set = decode_state_set(proof, &flat);
        let expect: std::collections::BTreeSet<Vec<i64>> = [
            vec![2, 0],
            vec![1, 1],
            vec![0, 2],
            vec![-1, 3],
        ]
        .into_iter()
        .collect();
        assert_eq!(set, expect, "ground applications only, deduped as a set");
    }

    #[cfg(feature = "z3")]
    #[test]
    fn decode_state_set_skips_wrong_arity_and_non_ground() {
        use std::collections::HashMap;

        let flat = FlatNet {
            places: vec!["p0".into(), "p1".into()],
            place_index: HashMap::from([("p0".into(), 0), ("p1".into(), 1)]),
            place_count: 2,
            transitions: Vec::new(),
        };
        // Wrong arity, variable args, nested exprs, and a different symbol
        // sharing the prefix: all skipped.
        let text = "(Reachable 1) (Reachable 1 2 3) (Reachable A B)                     (Reachable (+ 1 2) 0) (ReachableX 1 2) (Reachable 4 5)";
        let set = decode_state_set(text, &flat);
        let expect: std::collections::BTreeSet<Vec<i64>> = [vec![4, 5]].into_iter().collect();
        assert_eq!(set, expect);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn parse_ground_int_args_forms() {
        assert_eq!(parse_ground_int_args(" 2 0 "), Some(vec![2, 0]));
        assert_eq!(parse_ground_int_args("(- 3) 1"), Some(vec![-3, 1]));
        assert_eq!(parse_ground_int_args(""), Some(vec![]));
        assert_eq!(parse_ground_int_args("A 1"), None);
        assert_eq!(parse_ground_int_args("(+ 1 2)"), None);
    }
}
