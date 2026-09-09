//! Where a token may come to rest without being stranded ([VER-002], [VER-014]).
//!
//! `DeadlockFree` is violated by a quiescent marking that holds a token outside
//! the places where resting is permitted. The permitted set has two layers:
//!
//! - the **declared sinks** (`SmtVerifier::sink_places`), where a token may
//!   always rest;
//! - the **conditional sinks** (`SmtVerifier::sink_places_when(marker, …)`),
//!   where a token may rest only while `marker` holds a token. A marked marker
//!   is a *designed terminal* — a halted or paused run — and the marker itself
//!   is at rest whenever it is marked.
//!
//! Declarations union: a token in `p` is excused when `p` is a declared sink,
//! when `p` is a marker, or when some conditional set naming `p` has its marker
//! marked. Every route that decides `DeadlockFree` — the flat and name-coloured
//! CHC encoders, the abstract counterexample replay and the Route B
//! name-partition graph — reads this one module, so the predicate cannot drift
//! between them ([VER-002] AC7).
//!
//! `TerminatesAtSink` is untouched by conditional declarations: it asks whether
//! a declared sink was reached and reads only the unconditional set.

use crate::marking_state::MarkingState;
use crate::net_flattener::FlatNet;

/// Places where a token may rest while `marker` holds a token ([VER-014]).
/// `places` keeps declaration order (the report renders it) and holds no
/// duplicates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionalSinks {
    pub marker: String,
    pub places: Vec<String>,
}

/// Per flat place, how a token resting there is excused: `None` when it never
/// counts as stranded (a declared sink, or a marker), otherwise the ascending
/// flat indices of the markers whose presence excuses it — empty when nothing
/// does, so a token there is stranded whenever the marking is quiescent.
///
/// Places and markers that do not resolve in the flat net contribute nothing,
/// as an unresolved sink does: a mistyped marker makes the property stricter,
/// never laxer.
pub fn stranding_excuses(
    flat: &FlatNet,
    sink_places: &[String],
    conditional: &[ConditionalSinks],
) -> Vec<Option<Vec<usize>>> {
    let mut excuses: Vec<Option<Vec<usize>>> = vec![Some(Vec::new()); flat.place_count];
    for sink in sink_places {
        if let Some(&pid) = flat.place_index.get(sink) {
            excuses[pid] = None;
        }
    }
    for entry in conditional {
        let Some(&mid) = flat.place_index.get(&entry.marker) else {
            continue;
        };
        excuses[mid] = None;
        for place in &entry.places {
            let Some(&pid) = flat.place_index.get(place) else {
                continue;
            };
            if let Some(list) = &mut excuses[pid] {
                if !list.contains(&mid) {
                    list.push(mid);
                }
            }
        }
    }
    for list in excuses.iter_mut().flatten() {
        list.sort_unstable();
    }
    excuses
}

/// Whether `m` holds a token that is stranded — outside every place where
/// resting is permitted in `m`. The graph-route form of [`stranding_excuses`].
pub fn strands_token(
    m: &MarkingState,
    sink_places: &[String],
    conditional: &[ConditionalSinks],
) -> bool {
    let mut resting: Vec<&str> = sink_places.iter().map(String::as_str).collect();
    for entry in conditional {
        resting.push(entry.marker.as_str());
        if m.count(&entry.marker) > 0 {
            resting.extend(entry.places.iter().map(String::as_str));
        }
    }
    m.places().any(|(p, _)| !resting.contains(&p))
}

/// The declarations as the report prints them after the property description:
/// `sinks: a, b; when h: c, d; when p`, or `None` when nothing is declared.
/// Declaration order throughout (a sink named twice is printed once), so the
/// four implementations render the same text.
pub fn describe_sinks(sink_places: &[String], conditional: &[ConditionalSinks]) -> Option<String> {
    let mut parts: Vec<String> = Vec::new();
    let mut sinks: Vec<&str> = Vec::new();
    for s in sink_places {
        if !sinks.contains(&s.as_str()) {
            sinks.push(s);
        }
    }
    if !sinks.is_empty() {
        parts.push(format!("sinks: {}", sinks.join(", ")));
    }
    for entry in conditional {
        if entry.places.is_empty() {
            parts.push(format!("when {}", entry.marker));
        } else {
            parts.push(format!("when {}: {}", entry.marker, entry.places.join(", ")));
        }
    }
    if parts.is_empty() {
        None
    } else {
        Some(parts.join("; "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use crate::net_flattener::flatten;
    use libpetri_core::action::fork;
    use libpetri_core::arc::inhibitor;
    use libpetri_core::input::one;
    use libpetri_core::output::{and, out_place, xor};
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    fn s(v: &[&str]) -> Vec<String> {
        v.iter().map(|x| x.to_string()).collect()
    }

    fn when(marker: &str, places: &[&str]) -> ConditionalSinks {
        ConditionalSinks {
            marker: marker.to_string(),
            places: s(places),
        }
    }

    /// p0(1) → t → AND(a, b); a → ta → XOR(done | halt); b → tb → done unless
    /// `halt` is marked. Flat place order: a, b, done, halt, p0.
    fn halt_net() -> FlatNet {
        let p0 = Place::<i32>::new("p0");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let done = Place::<i32>::new("done");
        let halt = Place::<i32>::new("halt");
        let t = Transition::builder("t")
            .input(one(&p0))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .action(fork())
            .build();
        let ta = Transition::builder("ta")
            .input(one(&a))
            .output(xor(vec![out_place(&done), out_place(&halt)]))
            .action(fork())
            .build();
        let tb = Transition::builder("tb")
            .input(one(&b))
            .inhibitor(inhibitor(&halt))
            .output(out_place(&done))
            .action(fork())
            .build();
        flatten(&PetriNet::builder("haltNet").transitions([t, ta, tb]).build())
    }

    #[test]
    fn excuses_sinks_and_markers_never_strand_and_conditional_places_name_their_markers() {
        let flat = halt_net();
        let idx = |n: &str| flat.place_index[n];
        let ex = stranding_excuses(&flat, &s(&["done"]), &[when("halt", &["b"])]);
        assert_eq!(ex[idx("done")], None);
        assert_eq!(ex[idx("halt")], None);
        assert_eq!(ex[idx("b")], Some(vec![idx("halt")]));
        assert_eq!(ex[idx("a")], Some(vec![]));
        assert_eq!(ex[idx("p0")], Some(vec![]));
    }

    #[test]
    fn excuses_two_markers_are_listed_in_place_index_order_once_each() {
        let flat = halt_net();
        let idx = |n: &str| flat.place_index[n];
        let ex = stranding_excuses(
            &flat,
            &[],
            &[when("halt", &["b"]), when("done", &["b"]), when("halt", &["b"])],
        );
        let mut expected = vec![idx("done"), idx("halt")];
        expected.sort_unstable();
        assert_eq!(ex[idx("b")], Some(expected));
    }

    #[test]
    fn excuses_unresolved_marker_or_place_contributes_nothing() {
        let flat = halt_net();
        let ex = stranding_excuses(&flat, &s(&["ghost"]), &[when("ghost", &["b", "ghost"])]);
        assert_eq!(ex[flat.place_index["b"]], Some(vec![]));
    }

    #[test]
    fn strands_token_marker_excuses_its_places_only_while_marked() {
        let cond = [when("halt", &["b"])];
        let sinks = s(&["done"]);
        let m = |pairs: &[(&str, usize)]| {
            let mut b = MarkingStateBuilder::new();
            for (p, n) in pairs {
                b = b.tokens(*p, *n);
            }
            b.build()
        };
        assert!(!strands_token(&m(&[("halt", 1), ("b", 1)]), &sinks, &cond));
        assert!(strands_token(&m(&[("b", 1)]), &sinks, &cond));
        assert!(strands_token(&m(&[("halt", 1), ("a", 1)]), &sinks, &cond));
        assert!(!strands_token(&m(&[("halt", 1)]), &sinks, &cond));
        assert!(!strands_token(&m(&[("done", 2)]), &sinks, &cond));
        assert!(!strands_token(&MarkingState::new(), &sinks, &cond));
    }

    #[test]
    fn describe_sinks_renders_declarations_in_order() {
        assert_eq!(describe_sinks(&[], &[]), None);
        assert_eq!(describe_sinks(&s(&["a", "b"]), &[]).as_deref(), Some("sinks: a, b"));
        assert_eq!(
            describe_sinks(&s(&["a"]), &[when("h", &["b"]), when("p", &[])]).as_deref(),
            Some("sinks: a; when h: b; when p")
        );
        assert_eq!(
            describe_sinks(&[], &[when("h", &["a", "b"])]).as_deref(),
            Some("when h: a, b")
        );
        // A sink declared twice is printed once (TypeScript's Set semantics).
        assert_eq!(describe_sinks(&s(&["a", "a"]), &[]).as_deref(), Some("sinks: a"));
    }
}
