//! Dead-arc detection per **CORE-037**: a read, inhibitor or reset arc on a
//! place nothing ever fills.
//!
//! A read, inhibitor or reset arc only means something when its place can hold
//! a token. When no transition consumes from or produces into the place, it is
//! not an environment place, and the initial marking leaves it empty, the place
//! stays empty forever: a read arc disables its transition for good, an
//! inhibitor never blocks, a reset clears nothing. Such an arc is almost always
//! a wiring mistake — typically an arc naming a place that composition replaced
//! ([MOD-027] rejects the port case outright) — but it is also a legitimate way
//! to leave a hook for a caller who seeds the place, so it is only ever a
//! warning, never an error.
//!
//! One analysis, shared by both executors (a one-shot `LogMessage` at
//! construction, the [CORE-072] AC4 channel) and the verifier's report.

use std::collections::HashSet;
use std::sync::Arc;

use crate::petri_net::PetriNet;

/// The kind of a test or clear arc ([CORE-037]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum DeadArcKind {
    Read,
    Inhibitor,
    Reset,
}

impl DeadArcKind {
    fn label(self) -> &'static str {
        match self {
            DeadArcKind::Read => "read",
            DeadArcKind::Inhibitor => "inhibitor",
            DeadArcKind::Reset => "reset",
        }
    }
}

/// One read, inhibitor or reset arc that can have no effect ([CORE-037]).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct DeadArc {
    /// The arc's kind.
    pub kind: DeadArcKind,
    /// The transition that declares the arc.
    pub transition: Arc<str>,
    /// The place nothing fills.
    pub place: Arc<str>,
}

impl DeadArc {
    /// The diagnostic sentence of [CORE-037], without a level prefix:
    /// `reset arc of 'hub_kill' on 'answer/IN': no transition produces into or
    /// consumes from it and it starts empty; the arc has no effect.`
    /// The verifier's report prefixes it with `WARNING: `; the executors emit it
    /// as a `WARN` log message naming [`transition`](Self::transition).
    pub fn message(&self) -> String {
        let effect = match self.kind {
            DeadArcKind::Read => "the transition can never be enabled",
            DeadArcKind::Inhibitor => "the arc never blocks",
            DeadArcKind::Reset => "the arc has no effect",
        };
        format!(
            "{} arc of '{}' on '{}': no transition produces into or consumes from it and it \
             starts empty; {effect}.",
            self.kind.label(),
            self.transition,
            self.place
        )
    }
}

/// Every read, inhibitor or reset arc of `net` on a place that no transition
/// consumes from, no transition's output spec contains (any branch, timeout
/// and forward targets included), `is_environment` does not name, and
/// `initially_marked` does not report as holding a token ([CORE-037]). One
/// entry per arc — two dead arcs on one place are two entries — in transition
/// order and, within a transition, read, inhibitor, then reset. Empty for
/// every net without such arcs, which is the common case and costs one pass.
pub fn dead_arcs(
    net: &PetriNet,
    is_environment: impl Fn(&str) -> bool,
    initially_marked: impl Fn(&str) -> bool,
) -> Vec<DeadArc> {
    let transitions = net.transitions();
    if transitions
        .iter()
        .all(|t| t.reads().is_empty() && t.inhibitors().is_empty() && t.resets().is_empty())
    {
        return Vec::new();
    }
    // Every place some transition consumes from or produces into, once: one pass
    // over the arcs rather than one per test arc.
    let filled: HashSet<&str> = transitions
        .iter()
        .flat_map(|t| {
            t.input_specs()
                .iter()
                .map(|s| s.place_name())
                .chain(t.output_places().iter().map(|p| p.name()))
        })
        .collect();
    let dead = |place: &str| {
        !filled.contains(place) && !is_environment(place) && !initially_marked(place)
    };
    let mut found = Vec::new();
    for t in transitions {
        let arcs = t
            .reads()
            .iter()
            .map(|r| (DeadArcKind::Read, &r.place))
            .chain(t.inhibitors().iter().map(|i| (DeadArcKind::Inhibitor, &i.place)))
            .chain(t.resets().iter().map(|r| (DeadArcKind::Reset, &r.place)));
        for (kind, place) in arcs {
            if dead(place.name()) {
                found.push(DeadArc {
                    kind,
                    transition: Arc::clone(t.name_arc()),
                    place: Arc::clone(place.name_arc()),
                });
            }
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arc::{inhibitor, read, reset};
    use crate::input::one;
    use crate::output::out_place;
    use crate::place::Place;
    use crate::transition::Transition;

    fn net() -> PetriNet {
        let a = Place::<()>::new("A");
        let b = Place::<()>::new("B");
        let ghost = Place::<()>::new("ghost");
        let fed = Place::<()>::new("fed");
        let t = Transition::builder("t")
            .input(one(&a))
            .output(out_place(&b))
            .reset(reset(&ghost))
            .inhibitor(inhibitor(&fed))
            .build();
        let feeder = Transition::builder("feeder").output(out_place(&fed)).build();
        let reader = Transition::builder("reader").read(read(&ghost)).build();
        PetriNet::builder("n").transition(t).transition(feeder).transition(reader).build()
    }

    #[test]
    fn every_dead_arc_is_reported_once_in_transition_then_kind_order() {
        let found = dead_arcs(&net(), |_| false, |_| false);
        let messages: Vec<String> = found.iter().map(DeadArc::message).collect();
        assert_eq!(
            messages,
            [
                "reset arc of 't' on 'ghost': no transition produces into or consumes from it \
                 and it starts empty; the arc has no effect.",
                "read arc of 'reader' on 'ghost': no transition produces into or consumes from \
                 it and it starts empty; the transition can never be enabled.",
            ]
        );
        assert_eq!(found[1].transition.as_ref(), "reader");
    }

    #[test]
    fn a_seeded_or_environment_place_is_not_dead() {
        assert!(dead_arcs(&net(), |_| false, |p| p == "ghost").is_empty());
        assert!(dead_arcs(&net(), |p| p == "ghost", |_| false).is_empty());
    }

    #[test]
    fn one_transition_reports_read_then_inhibitor_then_reset() {
        let g = Place::<()>::new("g");
        let h = Place::<()>::new("h");
        let t = Transition::builder("w")
            .reset(reset(&g))
            .inhibitor(inhibitor(&h))
            .read(read(&g))
            .build();
        let n = PetriNet::builder("n").transition(t).build();
        let kinds: Vec<(DeadArcKind, String)> = dead_arcs(&n, |_| false, |_| false)
            .into_iter()
            .map(|d| (d.kind, d.place.to_string()))
            .collect();
        assert_eq!(
            kinds,
            [
                (DeadArcKind::Read, "g".to_string()),
                (DeadArcKind::Inhibitor, "h".to_string()),
                (DeadArcKind::Reset, "g".to_string()),
            ]
        );
        assert!(dead_arcs(&n, |_| false, |_| false)[1].message().ends_with("the arc never blocks."));
    }
}
