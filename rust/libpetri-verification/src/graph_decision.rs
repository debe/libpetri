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
use crate::property::{SmtProperty, two_marked};
use crate::rest_set::{ConditionalSinks, strands_token};

/// A finite graph of classes, indexed `0 .. count() - 1`, class 0 the initial one.
pub trait ClassView {
    /// How many classes the graph holds.
    fn count(&self) -> usize;
    /// The marking of class `i`.
    fn marking_of(&self, i: usize) -> &MarkingState;
    /// Whether class `i` has no successor — the graph's quiescence.
    fn is_quiescent(&self, i: usize) -> bool;
    /// Whether the name layer of class `i` aligns `p` and `q` ([NU-055]): every name
    /// resident in `p` equals every name resident in `q`. Only the ν name-partition
    /// graph ([NU-050]) has a name layer; `None` (the default) on a graph without one,
    /// which cannot decide a name-alignment property.
    fn name_aligned(&self, _i: usize, _p: &str, _q: &str) -> Option<bool> {
        None
    }
}

/// The index of the first class witnessing a violation, or `None` when the
/// property holds across the whole graph.
///
/// Quiescence-based properties read [`ClassView::is_quiescent`];
/// reachability-safety properties read the class alone. The name-alignment
/// properties of [NU-055] read [`ClassView::name_aligned`].
/// [`SmtProperty::DeadlockFree`] uses the shared rest set of [VER-014], so a
/// conditional sink excuses a token exactly as it does in the encoders.
///
/// # Panics
/// On a name-alignment property and a view without a name layer: only the ν
/// name-partition graph decides it ([NU-055] AC4), and a graph without names would
/// read every class as aligned.
pub fn decide_over_classes(
    view: &dyn ClassView,
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
) -> Option<usize> {
    let first_where = |pred: &dyn Fn(usize) -> bool| -> Option<usize> {
        (0..view.count()).find(|&i| pred(i))
    };
    let aligned = |i: usize, p: &str, q: &str| -> bool {
        view.name_aligned(i, p, q)
            .unwrap_or_else(|| panic!("{}", property.route_b_only_reason()))
    };
    // [NU-055]: a view without a name layer would read every class as aligned, so
    // refuse before reading any, whether or not a class is quiescent.
    if let SmtProperty::NameAligned { p, q } | SmtProperty::QuiescentNameAligned { p, q } = property {
        if view.count() == 0 || view.name_aligned(0, p, q).is_none() {
            panic!("{}", property.route_b_only_reason());
        }
    }

    match property {
        SmtProperty::PlaceBound { .. }
        | SmtProperty::BranchPlaceBound { .. }
        | SmtProperty::Unreachable { .. }
        | SmtProperty::MutualExclusion { .. } => {
            first_where(&|i| marking_violates(property, view.marking_of(i)))
        }
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
        // QuiescentCount ([VER-002]): a quiescent class whose count across the
        // places is below the lower bound with no waiver marked, or above the upper
        // bound.
        SmtProperty::QuiescentCount {
            places,
            min,
            max,
            waived_by,
        } => first_where(&|i| {
            view.is_quiescent(i)
                && count_violation(view.marking_of(i), places, *min, *max, waived_by).is_some()
        }),
        // NameAligned ([NU-055]): a class whose name layer holds a name in `p` other
        // than a name in `q`.
        SmtProperty::NameAligned { p, q } => first_where(&|i| !aligned(i, p, q)),
        // QuiescentNameAligned ([NU-055]): the same, at a quiescent class. No sink
        // clause.
        SmtProperty::QuiescentNameAligned { p, q } => {
            first_where(&|i| view.is_quiescent(i) && !aligned(i, p, q))
        }
    }
}

/// Whether `m` alone violates a reachability-safety property: the predicate
/// [`decide_over_classes`] applies to each class for [`SmtProperty::PlaceBound`],
/// [`SmtProperty::BranchPlaceBound`], [`SmtProperty::Unreachable`] and
/// [`SmtProperty::MutualExclusion`]. Route B ([VER-012]) runs it on each class as
/// the class is discovered, to stop at the first violating one. `false` for the
/// quiescence-based properties and the name-alignment properties of [NU-055], which
/// no marking decides alone.
pub(crate) fn marking_violates(property: &SmtProperty, m: &MarkingState) -> bool {
    match property {
        SmtProperty::PlaceBound { place, bound }
        | SmtProperty::BranchPlaceBound { place, bound } => m.count(place) > *bound,
        SmtProperty::Unreachable { places } => places.iter().all(|p| m.count(p) >= 1),
        // Pairwise ([VER-002]): two entries of the list marked at once.
        SmtProperty::MutualExclusion { places } => two_marked(places.iter().map(|p| m.count(p) >= 1)),
        SmtProperty::DeadlockFree
        | SmtProperty::TerminatesAtSink
        | SmtProperty::JoinedOrDeadLettered { .. }
        | SmtProperty::QuiescentCount { .. } => false,
        // [NU-055]: these read the name layer, which a count marking does not carry.
        SmtProperty::NameAligned { .. } | SmtProperty::QuiescentNameAligned { .. } => false,
    }
}

/// Which bound of a count a marking breaks ([`count_violation`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CountBound {
    /// Fewer than `min`, with no waiver marked.
    Lower,
    /// More than `max`. Never waived.
    Upper,
}

/// The tokens `m` holds across `places`, a place named twice counted once, as the
/// encoders read it.
pub(crate) fn tokens_across(m: &MarkingState, places: &[String]) -> usize {
    let mut seen: HashSet<&str> = HashSet::with_capacity(places.len());
    places
        .iter()
        .filter(|p| seen.insert(p.as_str()))
        .map(|p| m.count(p))
        .sum()
}

/// Which bound of a count `m` breaks: [`CountBound::Upper`] above `max` (`None` is
/// unbounded) whatever the waivers hold, checked first; [`CountBound::Lower`] below `min`
/// while no `waived_by` place is marked; else `None`. The one reading of a count clause,
/// shared by [VER-002]'s [`SmtProperty::QuiescentCount`] on the graph routes and the
/// [VER-022] open-net contract.
pub(crate) fn count_violation(
    m: &MarkingState,
    places: &[String],
    min: usize,
    max: Option<usize>,
    waived_by: &[String],
) -> Option<CountBound> {
    let count = tokens_across(m, places);
    if max.is_some_and(|max| count > max) {
        return Some(CountBound::Upper);
    }
    if count < min && !waived_by.iter().any(|w| m.count(w) > 0) {
        return Some(CountBound::Lower);
    }
    None
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

    fn s(v: &[&str]) -> Vec<String> {
        v.iter().map(|x| x.to_string()).collect()
    }

    #[test]
    fn tokens_across_counts_each_place_once() {
        let m = marking(&[("a", 2), ("b", 3)]);
        assert_eq!(tokens_across(&m, &s(&["a", "b", "a"])), 5);
        assert_eq!(tokens_across(&m, &s(&["c"])), 0);
        assert_eq!(tokens_across(&m, &[]), 0);
    }

    #[test]
    fn count_violation_waives_only_the_lower_bound() {
        let budget = s(&["budget"]);
        let halt = s(&["halt"]);
        let at = |pairs: &[(&str, usize)], min, max| {
            count_violation(&marking(pairs), &budget, min, max, &halt)
        };
        assert_eq!(at(&[("budget", 1)], 2, Some(2)), Some(CountBound::Lower));
        assert_eq!(at(&[("budget", 1), ("halt", 1)], 2, Some(2)), None);
        assert_eq!(at(&[("budget", 3)], 2, Some(2)), Some(CountBound::Upper));
        assert_eq!(at(&[("budget", 3), ("halt", 1)], 2, Some(2)), Some(CountBound::Upper));
        assert_eq!(at(&[("budget", 2)], 2, Some(2)), None);
        assert_eq!(at(&[("budget", 99)], 0, None), None);
        assert_eq!(at(&[], 1, None), Some(CountBound::Lower));
    }

    #[test]
    fn quiescent_count_reads_quiescent_classes_only() {
        let view = Classes {
            markings: vec![marking(&[("budget", 1)]), marking(&[("budget", 1), ("halt", 1)]), marking(&[])],
            quiescent: vec![false, true, true],
        };
        let waived = SmtProperty::quiescent_count(s(&["budget"]), 2, Some(2), s(&["halt"]));
        // Class 0 is below but not quiescent, class 1 is waived: the empty class 2 witnesses.
        assert_eq!(decide_over_classes(&view, &waived, &[], &[]), Some(2));
        let at_most_one = SmtProperty::quiescent_count(s(&["budget"]), 0, Some(1), s(&["halt"]));
        assert_eq!(decide_over_classes(&view, &at_most_one, &[], &[]), None);
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

    /// A graph with a name layer: `aligned[i]` answers [`ClassView::name_aligned`] for
    /// class `i`, whatever the places.
    struct Named {
        marking: MarkingState,
        aligned: Vec<bool>,
        quiescent: Vec<bool>,
    }

    impl ClassView for Named {
        fn count(&self) -> usize {
            self.aligned.len()
        }
        fn marking_of(&self, _i: usize) -> &MarkingState {
            &self.marking
        }
        fn is_quiescent(&self, i: usize) -> bool {
            self.quiescent[i]
        }
        fn name_aligned(&self, i: usize, _p: &str, _q: &str) -> Option<bool> {
            Some(self.aligned[i])
        }
    }

    /// [NU-055]: `NameAligned` reads the name layer of every class, its quiescent form only
    /// that of the quiescent ones, and no sink excuses either.
    #[test]
    fn nu055_name_alignment_reads_the_name_layer() {
        let view = Named {
            marking: marking(&[]),
            aligned: vec![true, false, true, false],
            quiescent: vec![false, false, true, true],
        };
        let sinks = ["box".to_string(), "list".to_string()];
        assert_eq!(decide_over_classes(&view, &SmtProperty::name_aligned("box", "list"), &sinks, &[]), Some(1));
        assert_eq!(
            decide_over_classes(&view, &SmtProperty::quiescent_name_aligned("box", "list"), &sinks, &[]),
            Some(3)
        );
        // A marking alone never decides it: the early stop reads the name layer instead.
        assert!(!marking_violates(&SmtProperty::name_aligned("box", "list"), &marking(&[("box", 2)])));
    }

    /// [NU-055] AC4: a view without a name layer refuses a name-alignment property: no
    /// class may be read as aligned for want of names.
    #[test]
    #[should_panic(expected = "decided only by the name-partition state-class graph (NU-055, Route B)")]
    fn nu055_a_view_without_a_name_layer_refuses_name_alignment() {
        let view = Classes {
            markings: vec![marking(&[("box", 1), ("list", 1)])],
            quiescent: vec![true],
        };
        decide_over_classes(&view, &SmtProperty::name_aligned("box", "list"), &[], &[]);
    }

    /// [NU-055] AC4: the quiescent form is refused too, on a graph with no resting class,
    /// where it would read no class at all and prove.
    #[test]
    #[should_panic(expected = "decided only by the name-partition state-class graph (NU-055, Route B)")]
    fn nu055_a_view_without_a_name_layer_refuses_quiescent_name_alignment() {
        let view = Classes {
            markings: vec![marking(&[("box", 1), ("list", 1)])],
            quiescent: vec![false],
        };
        decide_over_classes(&view, &SmtProperty::quiescent_name_aligned("box", "list"), &[], &[]);
    }
}
