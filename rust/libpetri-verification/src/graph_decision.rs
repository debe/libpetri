//! The property predicate both state-class-graph routes decide, in one place.
//!
//! Two routes enumerate a finite graph of classes and read a verdict off it: the
//! ν name-partition quotient of [VER-012] ([`crate::nu_scg_verifier`]) and the
//! plain bounded enumeration of [VER-017] ([`crate::scg_verifier`]). They explore
//! different graphs, but the question they ask of a class is identical, and
//! [VER-002] AC7 requires every route to decide the *same* predicate. Stating it
//! once is what keeps that true: when the sink clause last lived in two copies,
//! one of them drifted ([NU-040] AC4).

use std::collections::HashSet;

use crate::marking_state::MarkingState;
use crate::property::SmtProperty;
use crate::rest_set::{ConditionalSinks, strands_token};

/// A finite graph of classes, indexed `0 .. count() - 1`, class 0 the initial one.
pub trait ClassView {
    /// How many classes the graph holds.
    fn count(&self) -> usize;
    /// The marking of class `i`.
    fn marking_of(&self, i: usize) -> &MarkingState;
    /// Whether class `i` has no successor — the graph's quiescence.
    fn is_quiescent(&self, i: usize) -> bool;
}

/// The index of the first class witnessing a violation, or `None` when the
/// property holds across the whole graph.
///
/// Quiescence-based properties read [`ClassView::is_quiescent`];
/// reachability-safety properties read the marking alone.
/// [`SmtProperty::DeadlockFree`] uses the shared rest set of [VER-014], so a
/// conditional sink excuses a token exactly as it does in the encoders.
pub fn decide_over_classes(
    view: &dyn ClassView,
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
) -> Option<usize> {
    let first_where = |pred: &dyn Fn(usize) -> bool| -> Option<usize> {
        (0..view.count()).find(|&i| pred(i))
    };

    match property {
        SmtProperty::PlaceBound { place, bound }
        | SmtProperty::BranchPlaceBound { place, bound } => {
            first_where(&|i| view.marking_of(i).count(place) > *bound)
        }
        SmtProperty::Unreachable { places } => first_where(&|i| {
            let m = view.marking_of(i);
            places.iter().all(|p| m.count(p) >= 1)
        }),
        SmtProperty::MutualExclusion { places } => first_where(&|i| {
            let m = view.marking_of(i);
            places.iter().filter(|p| m.count(p) >= 1).count() >= 2
        }),
        // DeadlockFree ([VER-002]): a quiescent class that strands a token — some
        // marked place is not where resting is permitted, the conditional sinks
        // of [VER-014] included. The empty marking strands nothing (AC4).
        SmtProperty::DeadlockFree => first_where(&|i| {
            view.is_quiescent(i)
                && strands_token(view.marking_of(i), sink_places, conditional_sinks)
        }),
        // TerminatesAtSink ([VER-002]): a quiescent class that marks NO declared
        // sink. Inverts with DeadlockFree on the empty marking, by design.
        SmtProperty::TerminatesAtSink => {
            let sinks: HashSet<&str> = sink_places.iter().map(String::as_str).collect();
            first_where(&|i| {
                view.is_quiescent(i) && !any_sink_marked(view.marking_of(i), &sinks)
            })
        }
        // JoinedOrDeadLettered ([NU-040] AC4): a quiescent class still holding a
        // pending token. No sink clause.
        SmtProperty::JoinedOrDeadLettered { pending } => {
            first_where(&|i| view.is_quiescent(i) && view.marking_of(i).count(pending) >= 1)
        }
    }
}

/// Whether any declared sink place holds a token in `m` ([VER-002]).
fn any_sink_marked(m: &MarkingState, sinks: &HashSet<&str>) -> bool {
    m.places().any(|(p, _)| sinks.contains(p))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;

    /// A hand-built graph: the predicate under test is pure, so the route that
    /// produced the classes is irrelevant to what it decides.
    struct Classes {
        markings: Vec<MarkingState>,
        quiescent: Vec<bool>,
    }

    impl ClassView for Classes {
        fn count(&self) -> usize {
            self.markings.len()
        }
        fn marking_of(&self, i: usize) -> &MarkingState {
            &self.markings[i]
        }
        fn is_quiescent(&self, i: usize) -> bool {
            self.quiescent[i]
        }
    }

    fn marking(pairs: &[(&str, usize)]) -> MarkingState {
        let mut b = MarkingStateBuilder::new();
        for (p, n) in pairs {
            b = b.tokens(*p, *n);
        }
        b.build()
    }

    #[test]
    fn deadlock_free_reads_the_shared_rest_set() {
        let view = Classes {
            markings: vec![marking(&[("p0", 1)]), marking(&[("done", 1), ("stuck", 1)])],
            quiescent: vec![false, true],
        };
        // `stuck` is not a sink: stranded.
        assert_eq!(
            decide_over_classes(&view, &SmtProperty::DeadlockFree, &["done".into()], &[]),
            Some(1)
        );
        // ... unless `done` excuses it ([VER-014]).
        let conditional = [ConditionalSinks {
            marker: "done".into(),
            places: vec!["stuck".into()],
        }];
        assert_eq!(
            decide_over_classes(
                &view,
                &SmtProperty::DeadlockFree,
                &["done".into()],
                &conditional
            ),
            None
        );
    }

    #[test]
    fn terminates_at_sink_inverts_on_the_empty_marking() {
        let view = Classes {
            markings: vec![marking(&[])],
            quiescent: vec![true],
        };
        assert_eq!(
            decide_over_classes(&view, &SmtProperty::DeadlockFree, &["done".into()], &[]),
            None
        );
        assert_eq!(
            decide_over_classes(&view, &SmtProperty::TerminatesAtSink, &["done".into()], &[]),
            Some(0)
        );
    }

    #[test]
    fn reachability_safety_reads_the_marking_alone() {
        let view = Classes {
            markings: vec![marking(&[("a", 1)]), marking(&[("a", 1), ("b", 2)])],
            quiescent: vec![false, false],
        };
        assert_eq!(
            decide_over_classes(&view, &SmtProperty::place_bound("b", 1), &[], &[]),
            Some(1)
        );
        assert_eq!(
            decide_over_classes(&view, &SmtProperty::place_bound("b", 2), &[], &[]),
            None
        );
        assert_eq!(
            decide_over_classes(
                &view,
                &SmtProperty::unreachable(vec!["a".into(), "b".into()]),
                &[],
                &[]
            ),
            Some(1)
        );
        assert_eq!(
            decide_over_classes(
                &view,
                &SmtProperty::mutual_exclusion(vec!["a".into(), "b".into()]),
                &[],
                &[]
            ),
            Some(1)
        );
    }
}
