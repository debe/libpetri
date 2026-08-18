use crate::marking_state::MarkingState;
#[allow(unused_imports)]
use crate::marking_state::MarkingStateBuilder;
#[allow(unused_imports)]
use crate::net_flattener::FlatNet;

/// A decoded counterexample trace from Z3.
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

/// Decodes a Z3 proof answer into a counterexample trace.
///
/// Extracts marking states from `Reachable(m0, m1, ..., mP-1)` applications
/// and transition names from rule applications prefixed with `t_`.
///
/// This is a best-effort decoder that gracefully degrades if the Z3 answer
/// format varies — returns an empty trace rather than failing.
#[cfg(feature = "z3")]
pub fn decode(answer_str: &str, flat: &FlatNet) -> DecodedTrace {
    let mut trace = Vec::new();
    let mut transitions = Vec::new();

    // Parse the answer string looking for Reachable applications and transition names.
    // Z3 Spacer returns the answer as an S-expression tree.
    // We look for patterns like (Reachable 0 1 0 ...) and (t_name ...)
    for line in answer_str.lines() {
        let trimmed = line.trim();

        // Look for transition names (prefixed with t_)
        if let Some(name) = extract_transition_name(trimmed) {
            if let Some(original) = flat.transitions.iter().find(|ft| ft.name == name) {
                transitions.push(original.name.clone());
            } else {
                transitions.push(name);
            }
        }

        // Look for Reachable applications with integer arguments
        if let Some(marking) = extract_marking(trimmed, flat) {
            trace.push(marking);
        }
    }

    DecodedTrace { trace, transitions }
}

/// Extracts a transition name from a Z3 S-expression fragment.
#[allow(dead_code)]
fn extract_transition_name(s: &str) -> Option<String> {
    // Look for patterns like (t_name or |t_name|
    let s = s.trim_start_matches('(').trim();
    if s.starts_with("t_") || s.starts_with("|t_") {
        let name = s
            .trim_start_matches('|')
            .split_whitespace()
            .next()?
            .trim_end_matches('|')
            .trim_end_matches(')');
        Some(name.to_string())
    } else {
        None
    }
}

/// Extracts a MarkingState from a Reachable application in S-expression format.
#[allow(dead_code)]
fn extract_marking(s: &str, flat: &FlatNet) -> Option<MarkingState> {
    // Pattern: (Reachable 0 1 0 ...) or (|Reachable| 0 1 0 ...)
    let content = s.trim_start_matches('(').trim();
    let prefix = if content.starts_with("|Reachable|") {
        "|Reachable|"
    } else if content.starts_with("Reachable") {
        "Reachable"
    } else {
        return None;
    };

    let args = content[prefix.len()..].trim().trim_end_matches(')');
    let values: Vec<i64> = args
        .split_whitespace()
        .filter_map(|tok| {
            tok.trim_matches(|c: char| !c.is_ascii_digit() && c != '-')
                .parse()
                .ok()
        })
        .collect();

    if values.len() != flat.place_count {
        return None;
    }

    let mut builder = MarkingStateBuilder::new();
    for (i, &count) in values.iter().enumerate() {
        if count > 0 {
            builder = builder.tokens(&flat.places[i], count as usize);
        }
    }
    Some(builder.build())
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
    fn extract_transition_name_basic() {
        assert_eq!(
            extract_transition_name("(t_fire_a 1 2 3)"),
            Some("t_fire_a".into())
        );
        assert_eq!(
            extract_transition_name("(|t_fire_b| 1 2)"),
            Some("t_fire_b".into())
        );
        assert_eq!(extract_transition_name("(Reachable 1 2)"), None);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn extract_marking_basic() {
        use std::collections::HashMap;

        let flat = FlatNet {
            places: vec!["p1".into(), "p2".into()],
            place_index: HashMap::from([("p1".into(), 0), ("p2".into(), 1)]),
            place_count: 2,
            transitions: Vec::new(),
        };

        let m = extract_marking("(Reachable 1 0)", &flat);
        assert!(m.is_some());
        let marking = m.unwrap();
        assert_eq!(marking.count("p1"), 1);
        assert_eq!(marking.count("p2"), 0);
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
