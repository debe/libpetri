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
}
