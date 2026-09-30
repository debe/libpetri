//! Deadline reaping and late firing in the verifier ([VER-002], [VER-004], [TIME-006],
//! [TIME-013]).
//!
//! A `deadline` / `window` transition that is still enabled past `latest` plus the
//! executor's tolerance is **reaped**: the executor clears its enabled bit, emits
//! `TransitionTimedOut` and leaves its input tokens where they are ([TIME-013]). It is
//! not re-enabled until a token on one of its input places changes, so an executor
//! that fell behind (a blocked thread, a clock that jumped, [TIME-015]) can come to
//! rest at a marking the untimed net still enables. Lean:
//! `Libpetri/Novel/ReapingVsUntimed.lean`, `reaping_refutes_ver004_ac3` (the witness
//! `p0 → t → p1`, `t = window(3, 5)`, which rests at `{p0}`), and
//! `TimedCycle.bb_never_fires_after_reap`.
//!
//! Reaping never changes the marking, so the markings a timed run visits are still
//! untimed-reachable and the marking properties keep their untimed verdicts on the
//! untimed routes. What it changes is where a run can **rest**. A transition is
//! **reapable** iff its timing is `Deadline` or `Window` (a bounded latest that is
//! enforced destructively; `Exact` is enforced softly, [TIME-006]). A marking is
//! **reap-quiescent** iff every transition it enables is reapable — plain quiescence
//! (none enabled) is the special case. Every quiescence property reads
//! reap-quiescence on every route.
//!
//! A late executor also fires late: it reaps a `deadline` / `window` transition, and
//! it fires an `exact` one after its bound. So a timed graph that can return `Proven`
//! (Route B) is built on [`relax_late`]'s net, in which no transition has a latest
//! bound (Lean: `TimedScg/Late.relax`, `late_run_sound`), for every property.
//!
//! The caller opts out of both with `assume_no_reaping`, which assumes an **on-time
//! executor**: no transition is reaped and none fires after its latest bound. The
//! strict quiescence and the strong-semantics graph return, and the report says the
//! verdict rests on that assumption.
//!
//! A net timed only with `immediate` and `delayed` has no latest bound at all, so
//! nothing changes for it: same scripts, same graphs, same verdicts, same reports.

use std::collections::BTreeSet;

use libpetri_core::petri_net::PetriNet;
use libpetri_core::timing::{Timing, delayed, immediate};
use libpetri_core::transition::Transition;

/// Whether a transition with this timing can be reaped ([TIME-013]): `Deadline` and
/// `Window`, the two timings with a destructively enforced latest bound.
pub fn is_reapable(timing: &Timing) -> bool {
    matches!(timing, Timing::Deadline { .. } | Timing::Window { .. })
}

/// The names of the net's reapable transitions, in code-point order.
pub fn reapable_transitions(net: &PetriNet) -> BTreeSet<String> {
    net.transitions()
        .iter()
        .filter(|t| is_reapable(t.timing()))
        .map(|t| t.name().to_string())
        .collect()
}

/// Whether this timing has a finite latest bound ([TIME-006], [TIME-013]): `Deadline`,
/// `Window` and `Exact`. A late executor reaps the first two and fires the third late.
pub fn has_latest_bound(timing: &Timing) -> bool {
    timing.has_deadline()
}

/// The names of the net's transitions with a finite latest bound, in code-point order.
pub fn late_transitions(net: &PetriNet) -> BTreeSet<String> {
    net.transitions()
        .iter()
        .filter(|t| has_latest_bound(t.timing()))
        .map(|t| t.name().to_string())
        .collect()
}

/// `net` with the latest bound of every transition in `late` dropped, the earliest
/// kept: `deadline(by)` becomes `immediate()`, `window(e, l)` becomes `delayed(e)` and
/// `exact(a)` becomes `delayed(a)` (`immediate()` when the earliest is 0). `None` when
/// no transition changes. Lean: `TimedScg/Late.relax` (`lft := ∞`, `eft` kept).
///
/// A timed graph explores the executor's runs under **strong** semantics: an enabled
/// transition must fire by its latest bound, so no other firing can happen after that
/// bound while it stays enabled. The executor does not guarantee that: when it runs
/// late it reaps a `deadline` / `window` transition, or fires an `exact` one after its
/// bound, and the others fire meanwhile. Dropping the bound lets the graph reach those
/// markings too; a reaped transition that still fires in the graph only adds runs, so
/// the graph over-approximates the late executor (Lean: `late_run_sound`).
pub fn relax_late(net: &PetriNet, late: &BTreeSet<String>) -> Option<PetriNet> {
    if !net.transitions().iter().any(|t| late.contains(t.name()) && has_latest_bound(t.timing())) {
        return None;
    }
    let transitions = net.transitions().iter().map(|t| {
        if !late.contains(t.name()) || !has_latest_bound(t.timing()) {
            return t.clone();
        }
        match t.timing().earliest() {
            0 => with_timing(t, immediate()),
            earliest => with_timing(t, delayed(earliest)),
        }
    });
    Some(
        PetriNet::builder(net.name())
            .places(net.places().iter().cloned())
            .transitions(transitions)
            .terminals(net.terminals().iter().cloned())
            .build(),
    )
}

/// `t` with `timing`, every arc, the priority, the action and the name map kept.
fn with_timing(t: &Transition, timing: Timing) -> Transition {
    let mut b = Transition::builder(t.name_arc().clone())
        .timing(timing)
        .priority(t.priority())
        .action(t.action().clone())
        .inputs(t.input_specs().to_vec())
        .inhibitors(t.inhibitors().to_vec())
        .reads(t.reads().to_vec())
        .resets(t.resets().to_vec());
    if let Some(out) = t.output_spec() {
        b = b.output(out.clone());
    }
    if let Some(ms) = t.match_spec() {
        b = b.match_spec(ms.clone());
    }
    if let Some(map) = t.local_name_map_cloned() {
        b = b.local_name_map(map);
    }
    b.build()
}

/// The report line of a quiescence verdict on a net with reapable transitions, read
/// reap-aware (the default).
pub fn reap_aware_note(reapable: &BTreeSet<String>) -> String {
    format!(
        "Reaping (TIME-013): {} can be reaped, so a marking where only {} enabled counts as \
         quiescent (VER-002); the assume-no-reaping option reads it strictly.\n",
        join(reapable),
        if reapable.len() == 1 { "it is" } else { "they are" }
    )
}

/// The report line of a verdict reached under `assume_no_reaping` on a net with a
/// transition a late executor treats differently: the on-time executor the verdict
/// rests on. `late` names the reapable transitions and those with a latest bound.
pub fn no_reaping_assumption_note(late: &BTreeSet<String>) -> String {
    format!(
        "ASSUMPTION: no transition is reaped (the assume-no-reaping option) and none fires after \
         its latest bound, i.e. an on-time executor. A late executor can reap or fire late {} \
         (TIME-006, TIME-013); this verdict holds only for runs in which it does neither.\n",
        join(late)
    )
}

/// [`no_reaping_assumption_note`] for a verdict Route B reached ([NU-050]). Route B is
/// the one route that keeps timing, and with the latest bounds kept its graph reads each
/// firing as one instant step: an action that runs while a bound passes lets other
/// transitions fire before its outputs land, which the graph does not hold ([VER-004]).
pub fn no_reaping_route_b_note(late: &BTreeSet<String>) -> String {
    format!(
        "ASSUMPTION: no transition is reaped (the assume-no-reaping option), none fires after its \
         latest bound, and an action takes no time, i.e. an on-time executor with atomic firings. \
         Route B keeps the latest bound of {} and reads each firing as one instant step: a late \
         executor can reap or fire late (TIME-006, TIME-013), and an action that runs while a \
         bound passes lets other transitions fire before its outputs land (VER-004); this verdict \
         holds only for runs in which none of this happens.\n",
        join(late)
    )
}

fn join(names: &BTreeSet<String>) -> String {
    names.iter().map(String::as_str).collect::<Vec<_>>().join(", ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::action::fork;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::timing::{deadline, exact, window};

    fn net_with(timings: &[(&str, Timing)]) -> PetriNet {
        let p0 = Place::<()>::new("p0");
        let p1 = Place::<()>::new("p1");
        let mut b = PetriNet::builder("reap");
        for (name, timing) in timings {
            b = b.transition(
                Transition::builder(*name)
                    .input(one(&p0))
                    .output(out_place(&p1))
                    .timing(*timing)
                    .action(fork())
                    .build(),
            );
        }
        b.build()
    }

    #[test]
    fn deadline_and_window_are_reapable_and_nothing_else_is() {
        assert!(is_reapable(&deadline(5)));
        assert!(is_reapable(&window(3, 5)));
        assert!(!is_reapable(&exact(5)));
        assert!(!is_reapable(&delayed(5)));
        assert!(!is_reapable(&immediate()));
    }

    #[test]
    fn relaxing_drops_every_latest_bound_and_keeps_the_earliest() {
        let net = net_with(&[
            ("d", deadline(5)),
            ("w", window(3, 5)),
            ("w0", window(0, 5)),
            ("x", exact(4)),
            ("x0", exact(0)),
            ("y", delayed(2)),
            ("i", immediate()),
        ]);
        let reapable = reapable_transitions(&net);
        assert_eq!(reapable.iter().map(String::as_str).collect::<Vec<_>>(), ["d", "w", "w0"]);
        let late = late_transitions(&net);
        assert_eq!(late.iter().map(String::as_str).collect::<Vec<_>>(), ["d", "w", "w0", "x", "x0"]);
        let relaxed = relax_late(&net, &late).expect("five transitions change");
        let timing = |name: &str| {
            *relaxed.transitions().iter().find(|t| t.name() == name).unwrap().timing()
        };
        assert_eq!(timing("d"), immediate());
        assert_eq!(timing("w"), delayed(3));
        assert_eq!(timing("w0"), immediate());
        assert_eq!(timing("x"), delayed(4));
        assert_eq!(timing("x0"), immediate());
        assert_eq!(timing("y"), delayed(2));
        assert_eq!(timing("i"), immediate());
        assert!(relax_late(&net, &BTreeSet::new()).is_none());
    }

    #[test]
    fn a_net_without_latest_bounds_is_not_relaxed() {
        let net = net_with(&[("y", delayed(2)), ("i", immediate())]);
        assert!(late_transitions(&net).is_empty());
        let all: BTreeSet<String> = ["y".to_string(), "i".to_string()].into();
        assert!(relax_late(&net, &all).is_none());
    }
}
