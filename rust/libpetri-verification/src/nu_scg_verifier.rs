//! ν-net exact verification via the name-aware state-class-graph name-partition
//! quotient ([NU-050], Route B).
//!
//! Builds the [`NameStateClassGraph`] (the symmetry-reduced, name-aware SCG) and
//! decides the requested [`SmtProperty`] directly over its reachable classes — no
//! Z3. Because the graph carries the DBM zone, the verdict is exact over *time*
//! too (name×time); because joins are name-aware, *quiescence* is exact. The
//! analysis is **sound**, and **complete (exact)** when the symbolic graph closes
//! within `max_classes`. When it truncates, a violation among the explored classes
//! still stands (every stored class is reachable; only an expanded class can be
//! quiescent), and without one the verdict is `Unknown` (ν-PN reachability is
//! undecidable — undecidability surfaces as truncation, never an unsound verdict;
//! this generalises [NU-050] #2). A truncated graph never proves anything
//! ([VER-012] AC3). A reachability-safety property is checked on each class as
//! it is discovered, and the build stops at the first violating one ([VER-012]):
//! the verdict and witness of the full build, without filling the class cap.
//!
//! This route is invoked by [`crate::smt_verifier`] to *fill the gaps* the
//! SMT / Route A path cannot answer exactly: quiescence properties on a ν-net and
//! unbudgeted reachability-safety. It returns `None` when the net is not in the
//! supported mint→matched-join fragment, and the caller falls back. The
//! name-alignment properties of [NU-055] are its alone: no other route decides them.

use std::collections::{BTreeSet, HashSet, VecDeque};

use libpetri_core::petri_net::PetriNet;

use crate::environment::EnvironmentAnalysisMode;
use crate::graph_decision::{ClassView, decide_over_classes, marking_violates};
use crate::marking_state::MarkingState;
use crate::name_fragment::{self, FragmentMode};
use crate::name_marking::NameMarking;
use crate::name_state_class_graph::NameStateClassGraph;
use crate::priority_semantics::PrioritySemantics;
use crate::property::SmtProperty;
use crate::reaping;
use crate::rest_set::ConditionalSinks;
use crate::result::Verdict;

/// Outcome of the name-aware ν-partition analysis.
pub struct NuScgOutcome {
    pub verdict: Verdict,
    pub trace: Vec<MarkingState>,
    pub transitions: Vec<String>,
    /// Report note (empty for the truncation `Unknown`, whose reason is on the
    /// verdict).
    pub note: String,
    pub class_count: usize,
}

impl NuScgOutcome {
    /// An `Unknown` with `reason` on the verdict, after `class_count` classes.
    fn unknown(reason: String, class_count: usize) -> Self {
        Self {
            verdict: Verdict::Unknown { reason },
            trace: Vec::new(),
            transitions: Vec::new(),
            note: String::new(),
            class_count,
        }
    }
}

const NOTE_EXACT: &str = "Note: ν-join correlation decided exactly via the state-class-graph \
name-partition quotient — the symbolic graph closed, so the verdict is sound AND complete \
(no spurious different-name counterexample; quiescence is name-aware), beyond the \
bounded-budget fragment (NU-050, Route B).\n";

/// [`NOTE_EXACT`] for a graph built on a net in which a transition keeps its latest
/// bound (the on-time executor of `assume_no_reaping`, or a direct call of
/// [`verify_via_name_scg`] on a timed net). The strong-semantics graph fires every
/// transition by its latest bound and reads each firing as one instant step, so its
/// verdict is exact for that executor alone ([VER-004], [TIME-013]).
const NOTE_ON_TIME: &str = "Note: ν-join correlation decided via the state-class-graph \
name-partition quotient: the symbolic graph closed, and a transition keeps its latest bound in \
it, so the verdict is exact only for an on-time executor whose actions take no time (quiescence \
is name-aware; NU-050, Route B).\n";

/// The note of a closed graph built on `net` ([`NOTE_EXACT`] or [`NOTE_ON_TIME`]).
fn closed_note(net: &PetriNet) -> &'static str {
    if net.transitions().iter().any(|t| reaping::has_latest_bound(t.timing())) {
        NOTE_ON_TIME
    } else {
        NOTE_EXACT
    }
}

/// Tries to decide `property` exactly via the name-aware SCG. Returns `None` when
/// `net` is not in the supported fragment or marks a coloured place initially (the
/// caller falls back to the SMT / Route A path). A name-alignment property ([NU-055])
/// has no fallback: an uncoloured property place or a marked coloured place is
/// `Some` `Unknown` naming the place, and `None` means only that `net` is outside the
/// fragment, which the caller answers `Unknown` too.
///
/// `mint_transitions` names the transitions declared to mint ([NU-010]; the
/// verifier passes [`name_fragment::declared_mints`]). A transition that writes a
/// coloured place without consuming one and is not named there puts the net outside
/// the fragment.
///
/// This is the graph of `net` as given, for an on-time executor. It applies neither the
/// in-flight split of [VER-004] ([`crate::in_flight::split_in_flight`]) nor the late
/// executor of [TIME-013] ([`verify_via_name_scg_reaping`]): every firing is one atomic,
/// instant step, a transition fires by its latest bound, and a marking rests only when
/// nothing fires. Its note says the verdict is exact only for such an executor when a
/// transition keeps a latest bound, and says nothing of the split. `SmtVerifier::verify`
/// applies both, and splits every conflict pruner under
/// [`PrioritySemantics::Conflict`]; a direct caller that wants them does the same.
#[allow(clippy::too_many_arguments)]
pub fn verify_via_name_scg(
    net: &PetriNet,
    initial: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    env_places: &[&str],
    env_mode: &EnvironmentAnalysisMode,
    max_classes: usize,
    fragment_mode: FragmentMode,
    carrier_places: &BTreeSet<String>,
    mint_transitions: &BTreeSet<String>,
    priority_semantics: PrioritySemantics,
    conditional_sinks: &[ConditionalSinks],
) -> Option<NuScgOutcome> {
    verify_via_name_scg_reaping(
        net,
        initial,
        property,
        sink_places,
        env_places,
        env_mode,
        max_classes,
        fragment_mode,
        carrier_places,
        mint_transitions,
        priority_semantics,
        conditional_sinks,
        &BTreeSet::new(),
        &BTreeSet::new(),
    )
}

/// [`verify_via_name_scg`] for a late executor ([VER-002], [VER-004], [TIME-006],
/// [TIME-013]).
///
/// - The graph is built on [`reaping::relax_late`]'s net, in which no transition named
///   in `late` has a latest bound, for **every** property. A late executor reaps a
///   `deadline` / `window` transition or fires an `exact` one after its bound, and
///   fires the others meanwhile; the strong-semantics zone would forbid those runs, and
///   a `Proven` of any property, marking properties included, could miss them (Lean:
///   `TimedScg/Retrodict.reaping_escapes_timed_graph`, `TimedScg/Late.late_run_sound`).
/// - An expanded class rests when every firing out of it is of a transition in
///   `reapable` (none is the plain rule): the executor reaps those and stops. Only a
///   quiescence property reads it.
/// - [`PrioritySemantics::Conflict`] falls back to [`PrioritySemantics::None`] when a
///   transition in `reapable` exists: a reapable transition that pre-empts a
///   conflicting one on time is reaped by a late executor, which then fires the other,
///   so no firing can be pruned for it.
///
/// Empty `reapable` and `late` (the on-time executor of `assume_no_reaping`, or a net
/// timed only with `immediate` and `delayed`) is [`verify_via_name_scg`] exactly.
#[allow(clippy::too_many_arguments)]
pub fn verify_via_name_scg_reaping(
    net: &PetriNet,
    initial: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    env_places: &[&str],
    env_mode: &EnvironmentAnalysisMode,
    max_classes: usize,
    fragment_mode: FragmentMode,
    carrier_places: &BTreeSet<String>,
    mint_transitions: &BTreeSet<String>,
    priority_semantics: PrioritySemantics,
    conditional_sinks: &[ConditionalSinks],
    reapable: &BTreeSet<String>,
    late: &BTreeSet<String>,
) -> Option<NuScgOutcome> {
    let in_net = |names: &BTreeSet<String>| -> BTreeSet<String> {
        net.transitions()
            .iter()
            .filter(|t| names.contains(t.name()))
            .map(|t| t.name().to_string())
            .collect()
    };
    let reapable = in_net(reapable);
    let lifted: BTreeSet<String> = in_net(late)
        .into_iter()
        .filter(|name| {
            net.transitions()
                .iter()
                .any(|t| t.name() == name && reaping::has_latest_bound(t.timing()))
        })
        .collect();
    let relaxed = reaping::relax_late(net, &lifted);
    let net = relaxed.as_ref().unwrap_or(net);
    let pruning_off = !reapable.is_empty() && priority_semantics == PrioritySemantics::Conflict;
    let priority_semantics = if reapable.is_empty() {
        priority_semantics
    } else {
        PrioritySemantics::None
    };
    let late_note = if lifted.is_empty() {
        String::new()
    } else {
        lateness_note(&lifted, pruning_off)
    };
    // The marking properties read no rest ([VER-004]).
    let rests_on: BTreeSet<String> =
        if is_reachability_safety(property) { BTreeSet::new() } else { reapable };
    let mut outcome = verify_name_scg(
        net,
        initial,
        property,
        sink_places,
        env_places,
        env_mode,
        max_classes,
        fragment_mode,
        carrier_places,
        mint_transitions,
        priority_semantics,
        conditional_sinks,
        &rests_on,
    )?;
    if !outcome.note.is_empty() {
        outcome.note.push_str(&late_note);
    }
    Some(outcome)
}

/// Whether `property` reads one class alone (no quiescence clause): the marking, or
/// for `NameAligned` the name layer ([NU-055]).
fn is_reachability_safety(property: &SmtProperty) -> bool {
    match property {
        SmtProperty::PlaceBound { .. }
        | SmtProperty::BranchPlaceBound { .. }
        | SmtProperty::Unreachable { .. }
        | SmtProperty::MutualExclusion { .. }
        | SmtProperty::NameAligned { .. } => true,
        SmtProperty::DeadlockFree
        | SmtProperty::TerminatesAtSink
        | SmtProperty::JoinedOrDeadLettered { .. }
        | SmtProperty::QuiescentCount { .. }
        | SmtProperty::QuiescentNameAligned { .. } => false,
    }
}

/// The note Route B adds when it lifted latest bounds.
fn lateness_note(lifted: &BTreeSet<String>, pruning_off: bool) -> String {
    let names: Vec<&str> = lifted.iter().map(String::as_str).collect();
    format!(
        "Note: the latest bound of {} was lifted{}, so the graph holds the runs of a late \
         executor, which reaps a deadline or window transition and fires an exact one after its \
         bound (TIME-006, TIME-013).\n",
        names.join(", "),
        if pruning_off { " and priority pruning is off" } else { "" }
    )
}

#[allow(clippy::too_many_arguments)]
fn verify_name_scg(
    net: &PetriNet,
    initial: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    env_places: &[&str],
    env_mode: &EnvironmentAnalysisMode,
    max_classes: usize,
    fragment_mode: FragmentMode,
    carrier_places: &BTreeSet<String>,
    mint_transitions: &BTreeSet<String>,
    priority_semantics: PrioritySemantics,
    conditional_sinks: &[ConditionalSinks],
    reapable: &BTreeSet<String>,
) -> Option<NuScgOutcome> {
    // CORE-043: this is a public entry that reaches the ν-SCG without going through
    // `StateClassGraph::build_with_env`, where the check otherwise sits.
    libpetri_core::petri_net::require_output_producing_actions(net);

    // Carrier validation (EXTENDED, [NU-051]): a mistyped carrier name would make
    // two fork branches mint INDEPENDENT names, so the join never becomes
    // name-enabled and the verifier would report a confident false deadlock. Fail
    // loudly as `Unknown` naming the offending place — never silently proceed.
    if fragment_mode == FragmentMode::Extended {
        let known: HashSet<&str> = net.places().iter().map(|p| p.name()).collect();
        for c in carrier_places {
            if !known.contains(c.as_str()) {
                return Some(NuScgOutcome::unknown(format!("declared carrier place '{c}' not in the net"), 0));
            }
        }
    }

    let fragment = name_fragment::classify(
        net,
        fragment_mode,
        carrier_places,
        mint_transitions,
        property.is_name_alignment(),
    )?;
    // [NU-055]: nothing but this graph decides a name-alignment property, so where it
    // cannot, the verdict is Unknown naming the place rather than a decline the caller
    // would route elsewhere.
    if let Some(reason) = name_alignment_refusal(property, &fragment, fragment_mode, initial) {
        return Some(NuScgOutcome::unknown(reason, 0));
    }
    // We model no initial colour assignment, so coloured places must start empty.
    for p in &fragment.coloured_order {
        if initial.count(p) != 0 {
            return None;
        }
    }

    // [VER-012]: a reachability-safety property is checked on each class as it is
    // discovered, with the predicate `decide` applies, and the build stops at the
    // first violating class — the lowest-index one, so verdict and witness are
    // those of the full build. Quiescence needs expanded classes: no early stop.
    // `NameAligned` ([NU-055]) reads the name layer, as `NameClasses` does.
    let violates = |m: &MarkingState, names: &NameMarking| {
        marking_violates(property, m)
            || matches!(property, SmtProperty::NameAligned { places } if !names.aligned(places))
    };
    let stop_at = is_reachability_safety(property)
        .then_some(&violates as &dyn Fn(&MarkingState, &NameMarking) -> bool);
    let scg = NameStateClassGraph::build_until(
        net,
        initial,
        &fragment,
        max_classes,
        env_places,
        env_mode,
        priority_semantics,
        stop_at,
    );

    // [VER-013]: a build the total budget or a cancellation stopped says nothing,
    // not even about its prefix; the caller reports the stop.
    if scg.is_stopped() {
        return Some(NuScgOutcome::unknown(
            format!("ν name-aware state-class graph stopped after {} classes (VER-013)", scg.class_count()),
            scg.class_count(),
        ));
    }

    // On truncation the same predicate runs over the explored prefix ([VER-012]
    // AC3, [VER-017]): every stored class is a real reachable class, and only an
    // expanded class counts as quiescent.
    let complete = scg.is_complete();
    let (verdict, violating) = decide(&scg, property, sink_places, conditional_sinks, reapable);
    if let Some(idx) = violating {
        let (trace, transitions) = counterexample_path(&scg, idx);
        return Some(NuScgOutcome {
            verdict,
            trace,
            transitions,
            note: if complete {
                closed_note(net).to_string()
            } else if scg.stopped_at_violation() {
                early_stop_note(scg.class_count())
            } else {
                crate::scg_verifier::prefix_note("ν name-aware state-class graph", max_classes)
            },
            class_count: scg.class_count(),
        });
    }

    if !complete {
        return Some(NuScgOutcome::unknown(
            format!(
                "ν name-aware state-class graph truncated at {max_classes} classes — the \
                 live correlation pool is not structurally bounded; reachability over \
                 unbounded fresh names is undecidable (NU-050, Route B). Declare a budget \
                 place to bound the live pool, or raise nu_max_classes."
            ),
            scg.class_count(),
        ));
    }

    Some(NuScgOutcome {
        verdict,
        trace: Vec::new(),
        transitions: Vec::new(),
        note: closed_note(net).to_string(),
        class_count: scg.class_count(),
    })
}

/// Why Route B cannot decide the name-alignment `property` on `fragment` ([NU-055]), or
/// `None` (always for any other property): a property place that is not coloured,
/// whose predicate would hold vacuously (AC2, AC3; Lean `Aligned.alignedAll_uncoloured`),
/// or a coloured place the initial marking marks (AC6), since the graph models no
/// initial names. Checked in that order, the last two steps of the [NU-055] refusal
/// order: the first uncoloured place of `S` in the order of `S`, then the first marked
/// coloured place in code-point order.
fn name_alignment_refusal(
    property: &SmtProperty,
    fragment: &name_fragment::NameFragment,
    fragment_mode: FragmentMode,
    initial: &MarkingState,
) -> Option<String> {
    let (SmtProperty::NameAligned { places } | SmtProperty::QuiescentNameAligned { places }) = property else {
        return None;
    };
    if let Some(place) = places.iter().find(|place| !fragment.is_coloured(place)) {
        let base = if fragment_mode == FragmentMode::Base {
            "; under BASE only the match keys are coloured, carrier places and relay targets \
             only under the EXTENDED fragment (fragment_mode(FragmentMode::Extended), NU-051, \
             NU-054)"
        } else {
            ""
        };
        return Some(format!(
            "place '{place}' is not a coloured place of the ν fragment (a match key, declared \
             carrier or relay target), so it carries no name and name alignment on it would \
             hold vacuously (NU-055){base}"
        ));
    }
    let marked = fragment.coloured_order.iter().find(|c| initial.count(c) != 0)?;
    Some(format!(
        "coloured place '{marked}' holds a token in the initial marking; the name-partition \
         graph models no initial names, so the coloured places must start empty (NU-055)"
    ))
}

/// The report note of a violation found by stopping the build at its first
/// violating class ([VER-012]). The graph was never finished, so it says nothing
/// about closure.
pub(crate) fn early_stop_note(class_count: usize) -> String {
    format!(
        "Note: Route B stopped at the first violating class after {class_count} classes (VER-012). \
         Every explored class is reachable and classes are discovered breadth-first, so the \
         counterexample is a real firing sequence and a shortest one to any violation.\n"
    )
}

/// Decides the property over the name-aware SCG — the whole of it, or the
/// explored prefix of a truncated one. Returns the verdict and, for a violation,
/// the index of a witnessing class. The `Proven` is the caller's to discard when
/// the graph did not close.
///
/// The predicate itself lives in [`decide_over_classes`], shared with the plain
/// enumeration route of [VER-017] so the two cannot drift ([VER-002] AC7).
fn decide(
    scg: &NameStateClassGraph,
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
    reapable: &BTreeSet<String>,
) -> (Verdict, Option<usize>) {
    match decide_over_classes(&NameClasses::new(scg, reapable), property, sink_places, conditional_sinks) {
        Some(idx) => (Verdict::Violated, Some(idx)),
        None => (
            Verdict::Proven {
                method: "ν name-partition SCG (NU-050, Route B)".into(),
                inductive_invariant: None,
            },
            None,
        ),
    }
}

/// The name-partition graph's classes as the shared predicate reads them.
///
/// `fires_unreapable[i]` is whether some firing out of class `i` is of a transition
/// that cannot be reaped; `None` when nothing is reapable, where "no firing at all"
/// is the rule ([VER-002] reap-quiescence, [TIME-013]).
struct NameClasses<'g> {
    scg: &'g NameStateClassGraph,
    fires_unreapable: Option<Vec<bool>>,
}

impl<'g> NameClasses<'g> {
    fn new(scg: &'g NameStateClassGraph, reapable: &BTreeSet<String>) -> Self {
        let fires_unreapable = (!reapable.is_empty()).then(|| {
            let mut out = vec![false; scg.class_count()];
            for e in &scg.edges {
                if !reapable.contains(&e.transition_name) {
                    out[e.from] = true;
                }
            }
            out
        });
        NameClasses { scg, fires_unreapable }
    }
}

impl ClassView for NameClasses<'_> {
    fn count(&self) -> usize {
        self.scg.class_count()
    }
    fn marking_of(&self, i: usize) -> &MarkingState {
        &self.scg.classes[i].base.marking
    }
    /// A frontier class of a truncated graph was never expanded: no successors
    /// recorded, but not dead ([VER-017]). An expanded class rests when nothing fires
    /// out of it, or only reapable transitions do.
    fn is_quiescent(&self, i: usize) -> bool {
        i < self.scg.expanded_count()
            && match &self.fires_unreapable {
                None => self.scg.successors(i).is_empty(),
                Some(fires) => !fires[i],
            }
    }
    fn name_aligned(&self, i: usize, places: &[String]) -> Option<bool> {
        Some(self.scg.classes[i].names.aligned(places))
    }
}

/// Shortest firing sequence from the initial class (0) to `target` for the
/// counterexample trace: BFS over each class's labelled out-edges, O(V + E).
///
/// The edge list is grouped by source in one pass first. Scanning the whole edge
/// list per dequeued class instead was O(V·E), on graphs of up to `nu_max_classes`
/// (100 000 by default) classes. Grouping keeps edge-list order within a source,
/// so the BFS tree — and the reported path — is the one the scan found.
fn counterexample_path(scg: &NameStateClassGraph, target: usize) -> (Vec<MarkingState>, Vec<String>) {
    let n = scg.class_count();
    let mut out_edges: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (idx, e) in scg.edges.iter().enumerate() {
        out_edges[e.from].push(idx);
    }
    let mut parent: Vec<Option<usize>> = vec![None; n];
    let mut via: Vec<String> = vec![String::new(); n];
    let mut visited = vec![false; n];
    visited[0] = true;
    let mut queue = VecDeque::new();
    queue.push_back(0usize);
    while let Some(u) = queue.pop_front() {
        if u == target {
            break;
        }
        for &idx in &out_edges[u] {
            let e = &scg.edges[idx];
            if !visited[e.to] {
                visited[e.to] = true;
                parent[e.to] = Some(u);
                via[e.to] = e.transition_name.clone();
                queue.push_back(e.to);
            }
        }
    }
    if target != 0 && parent[target].is_none() {
        return (Vec::new(), Vec::new());
    }
    let mut chain = vec![target];
    let mut cur = target;
    while let Some(p) = parent[cur] {
        chain.push(p);
        cur = p;
    }
    chain.reverse();
    let markings = chain
        .iter()
        .map(|&i| scg.classes[i].base.marking.clone())
        .collect();
    let transitions = chain.iter().skip(1).map(|&i| via[i].clone()).collect();
    (markings, transitions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use libpetri_core::action::fork;
    use libpetri_core::input::one;
    use libpetri_core::match_spec::MatchSpec;
    use libpetri_core::name::NameId;
    use libpetri_core::output::{and, out_place};
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    const MAX: usize = 10_000;

    fn verify(net: &PetriNet, initial: &MarkingState, property: SmtProperty) -> NuScgOutcome {
        verify_via_name_scg(
            net,
            initial,
            &property,
            &[],
            &[],
            &EnvironmentAnalysisMode::Ignore,
            MAX,
            FragmentMode::Base,
            &BTreeSet::new(),
            &crate::name_fragment::all_mints(&net),
            PrioritySemantics::None,
            &[],
        )
        .expect("net should be in the ν name-fragment")
    }

    /// Two independent mints feed one join: their fresh names can never be equal,
    /// so `merged` is unreachable — WITH NO BUDGET PLACE (the beyond-bounded win
    /// Route A cannot do; it would return Unknown without a declared budget).
    fn distinct_mints_no_budget() -> PetriNet {
        let source_a = Place::<()>::new("sourceA");
        let source_b = Place::<()>::new("sourceB");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");

        let fork_a = Transition::builder("forkA")
            .input(one(&source_a))
            .output(out_place(&a))
            .action(fork())
            .build();
        let fork_b = Transition::builder("forkB")
            .input(one(&source_b))
            .output(out_place(&b))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();

        PetriNet::builder("distinct_mints_no_budget")
            .transitions([fork_a, fork_b, join])
            .build()
    }

    /// One mint stamps both branches with the same name, so the join can fire.
    fn same_mint() -> PetriNet {
        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();

        PetriNet::builder("same_mint")
            .transitions([t_fork, join])
            .build()
    }

    /// [VER-012] early stop: the build that stops at the first violating class
    /// stores the unstopped build's classes up to it, and the witness — the
    /// lowest-index violating class and its shortest path — is the full build's.
    #[test]
    fn early_stop_witness_is_the_full_builds() {
        use crate::name_state_class_graph::tests::fig11b;

        let (fig, fig_m0) = fig11b();
        let mint = same_mint();
        let mint_m0 = MarkingStateBuilder::new().tokens("source", 2).build();
        let cases: Vec<(&str, &PetriNet, &MarkingState, SmtProperty)> = vec![
            ("11(b) placeBound(order_clerk, 2)", &fig, &fig_m0, SmtProperty::place_bound("order_clerk", 2)),
            ("11(b) placeBound(send_done, 1)", &fig, &fig_m0, SmtProperty::place_bound("send_done", 1)),
            ("11(b) unreachable(send_done)", &fig, &fig_m0, SmtProperty::unreachable(vec!["send_done".into()])),
            (
                "11(b) mutualExclusion(order, send_done)",
                &fig,
                &fig_m0,
                SmtProperty::mutual_exclusion(vec!["order".into(), "send_done".into()]),
            ),
            ("same mint unreachable(merged)", &mint, &mint_m0, SmtProperty::unreachable(vec!["merged".into()])),
            (
                "same mint placeBound(branchA, 1)",
                &mint,
                &mint_m0,
                SmtProperty::place_bound("branchA", 1),
            ),
        ];
        for (name, net, m0, property) in cases {
            let fragment = name_fragment::classify(net, FragmentMode::Base, &BTreeSet::new(), &crate::name_fragment::all_mints(&net), false)
                .expect("in the base fragment");
            let build = |stop_at: Option<&dyn Fn(&MarkingState, &NameMarking) -> bool>| {
                NameStateClassGraph::build_until(
                    net,
                    m0,
                    &fragment,
                    300,
                    &[],
                    &EnvironmentAnalysisMode::Ignore,
                    PrioritySemantics::None,
                    stop_at,
                )
            };
            let full = build(None);
            let violates = |m: &MarkingState, _: &NameMarking| marking_violates(&property, m);
            let stopped = build(Some(&violates));
            let (full_verdict, full_idx) = decide(&full, &property, &[], &[], &BTreeSet::new());
            let (stop_verdict, stop_idx) = decide(&stopped, &property, &[], &[], &BTreeSet::new());
            assert!(full_verdict.is_violated(), "{name}");
            assert!(stop_verdict.is_violated(), "{name}");
            assert!(stopped.stopped_at_violation(), "{name}");
            assert!(!stopped.is_complete(), "{name}: an early-stopped graph is not closed");
            assert_eq!(stop_idx, Some(stopped.class_count() - 1), "{name}: the stop class is the last");
            assert_eq!(stop_idx, full_idx, "{name}");
            let idx = stop_idx.unwrap();
            for i in 0..=idx {
                assert_eq!(stopped.classes[i].base.marking, full.classes[i].base.marking, "{name}: class {i}");
            }
            let (full_trace, full_path) = counterexample_path(&full, idx);
            let (stop_trace, stop_path) = counterexample_path(&stopped, idx);
            assert_eq!(stop_path, full_path, "{name}");
            assert_eq!(stop_trace, full_trace, "{name}");
            assert!(stopped.class_count() <= full.class_count(), "{name}");
        }
    }

    #[test]
    fn distinct_mints_merged_unreachable_proven_no_budget() {
        let net = distinct_mints_no_budget();
        let initial = MarkingStateBuilder::new()
            .tokens("sourceA", 1)
            .tokens("sourceB", 1)
            .build();
        let out = verify(&net, &initial, SmtProperty::unreachable(vec!["merged".into()]));
        assert!(
            out.verdict.is_proven(),
            "distinct-mint names can never correlate → merged unreachable (no budget needed): {:?}",
            out.verdict
        );
        assert!(out.note.contains("name-partition quotient"));
        assert!(out.note.contains("Route B"));
    }

    #[test]
    fn same_mint_merged_reachable_violated_with_trace() {
        let net = same_mint();
        let initial = MarkingStateBuilder::new().tokens("source", 1).build();
        let out = verify(&net, &initial, SmtProperty::unreachable(vec!["merged".into()]));
        assert!(out.verdict.is_violated(), "same-mint siblings join → merged reachable");
        assert!(
            out.transitions.iter().any(|t| t == "join"),
            "counterexample trace should fire the join: {:?}",
            out.transitions
        );
    }

    #[test]
    fn joined_or_dead_lettered_violated_when_distinct_strands_pending() {
        // forkA mints into branchA AND pending; forkB mints into branchB. Their
        // names differ, so the join is name-disabled and `pending` is stranded at
        // quiescence → JoinedOrDeadLettered VIOLATED (the SMT path returns Unknown).
        let source_a = Place::<()>::new("sourceA");
        let source_b = Place::<()>::new("sourceB");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let pending = Place::<()>::new("pending");
        let merged = Place::<String>::new("merged");

        let fork_a = Transition::builder("forkA")
            .input(one(&source_a))
            .output(and(vec![out_place(&a), out_place(&pending)]))
            .action(fork())
            .build();
        let fork_b = Transition::builder("forkB")
            .input(one(&source_b))
            .output(out_place(&b))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .input(one(&pending))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();
        let net = PetriNet::builder("strand")
            .transitions([fork_a, fork_b, join])
            .build();

        let initial = MarkingStateBuilder::new()
            .tokens("sourceA", 1)
            .tokens("sourceB", 1)
            .build();
        let out = verify(&net, &initial, SmtProperty::joined_or_dead_lettered("pending"));
        assert!(
            out.verdict.is_violated(),
            "distinct-name siblings cannot join → pending stranded at quiescence: {:?}",
            out.verdict
        );
    }

    #[test]
    fn joined_or_dead_lettered_proven_when_same_mint_always_joins() {
        // Same-mint scatter-gather: every group's pending is joinable, so no
        // quiescent state holds a pending token → PROVEN.
        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let pending = Place::<()>::new("pending");
        let merged = Place::<String>::new("merged");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&a), out_place(&b), out_place(&pending)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .input(one(&pending))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();
        let net = PetriNet::builder("joinable")
            .transitions([t_fork, join])
            .build();

        let initial = MarkingStateBuilder::new().tokens("source", 2).build();
        let out = verify(&net, &initial, SmtProperty::joined_or_dead_lettered("pending"));
        assert!(out.verdict.is_proven(), "every group joins → no stranded pending: {:?}", out.verdict);
    }

    #[test]
    fn name_times_time_same_mint_join_reachable_under_delay() {
        // A timed same-mint join: the name layer must compose with the reused DBM
        // step. With a delay the join still fires → merged reachable.
        use libpetri_core::timing;

        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .timing(timing::delayed(100))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .timing(timing::window(50, 200))
            .action(fork())
            .build();
        let net = PetriNet::builder("timed_same_mint")
            .transitions([t_fork, join])
            .build();

        let initial = MarkingStateBuilder::new().tokens("source", 1).build();
        let out = verify(&net, &initial, SmtProperty::unreachable(vec!["merged".into()]));
        assert!(out.verdict.is_violated(), "timed same-mint join still reaches merged: {:?}", out.verdict);
    }

    /// [TIME-013] on Route B: the same-mint join with a `window(50, 200)` join. On time
    /// the join fires and the run rests at `{merged}`; a late executor reaps it and rests
    /// with both branches marked. Read reap-aware, the class after the fork rests.
    #[test]
    fn route_b_reads_a_reaped_join_as_resting() {
        use libpetri_core::timing;

        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");
        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .timing(timing::window(50, 200))
            .action(fork())
            .build();
        let net = PetriNet::builder("reaped_join").transitions([t_fork, join]).build();
        let initial = MarkingStateBuilder::new().tokens("source", 1).build();
        let run = |reapable: &BTreeSet<String>| {
            verify_via_name_scg_reaping(
                &net,
                &initial,
                &SmtProperty::DeadlockFree,
                &["merged".to_string()],
                &[],
                &EnvironmentAnalysisMode::Ignore,
                1_000,
                FragmentMode::Base,
                &BTreeSet::new(),
                &crate::name_fragment::all_mints(&net),
                PrioritySemantics::Conflict,
                &[],
                reapable,
                reapable,
            )
            .expect("in the fragment")
        };
        let strict = run(&BTreeSet::new());
        assert!(strict.verdict.is_proven(), "on time the join always fires: {:?}", strict.verdict);
        let reaping = run(&BTreeSet::from(["join".to_string()]));
        assert!(reaping.verdict.is_violated(), "a reaped join strands both branches: {:?}", reaping.verdict);
        assert_eq!(reaping.transitions, vec!["fork".to_string()]);
        assert!(reaping.note.contains("latest bound of join was lifted"), "{}", reaping.note);
    }

    #[test]
    fn unbounded_mint_truncates_to_unknown() {
        // A self-refilling fork mints a fresh name every firing with no join able
        // to consume it (branchB is never produced) → the symbolic graph grows
        // without bound → truncation → Unknown (NU-050 #2 generalised).
        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&source), out_place(&a)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();
        let net = PetriNet::builder("unbounded_mint")
            .transitions([t_fork, join])
            .build();

        let initial = MarkingStateBuilder::new().tokens("source", 1).build();
        let out = verify_via_name_scg(
            &net,
            &initial,
            &SmtProperty::unreachable(vec!["merged".into()]),
            &[],
            &[],
            &EnvironmentAnalysisMode::Ignore,
            40,
            FragmentMode::Base,
            &BTreeSet::new(),
            &crate::name_fragment::all_mints(&net),
            PrioritySemantics::None,
            &[],
        )
        .expect("in fragment");
        match &out.verdict {
            Verdict::Unknown { reason } => {
                assert!(reason.contains("truncated"), "reason: {reason}");
            }
            other => panic!("expected Unknown on truncation, got {other:?}"),
        }
    }

    #[test]
    fn non_nu_net_is_not_in_fragment() {
        // No match transition → not a ν-net → None (caller falls back).
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("plain").transition(t).build();
        let initial = MarkingStateBuilder::new().tokens("p1", 1).build();
        assert!(verify_via_name_scg(
            &net,
            &initial,
            &SmtProperty::unreachable(vec!["p2".into()]),
            &[],
            &[],
            &EnvironmentAnalysisMode::Ignore,
            MAX,
            FragmentMode::Base,
            &BTreeSet::new(),
            &crate::name_fragment::all_mints(&net),
            PrioritySemantics::None,
            &[],
        )
        .is_none());
    }

    /// `join1` matches on `a`/`b` and also consumes `c`, a key of `join2`, as a
    /// non-correlated input: at runtime it takes `c`'s oldest token, whatever its
    /// name. With `mintB` first that token is `join2`'s, so `join2` never fires and
    /// `pending` strands. The name layer would drop nothing from `c` and prove the
    /// net stranding-free, so the net must be out of fragment ([NU-051] AC7).
    #[test]
    fn join_consuming_a_coloured_place_off_key_is_not_in_fragment() {
        let src_a = Place::<()>::new("srcA");
        let src_b = Place::<()>::new("srcB");
        let a = Place::<String>::new("a");
        let b = Place::<String>::new("b");
        let c = Place::<String>::new("c");
        let d = Place::<String>::new("d");
        let pending = Place::<()>::new("pending");
        let out = Place::<()>::new("out");
        let key = |s: &String| NameId::new(s.clone());

        let mint_a = Transition::builder("mintA")
            .input(one(&src_a))
            .output(and(vec![out_place(&a), out_place(&b), out_place(&c)]))
            .action(fork())
            .build();
        let mint_b = Transition::builder("mintB")
            .input(one(&src_b))
            .output(and(vec![out_place(&c), out_place(&d), out_place(&pending)]))
            .action(fork())
            .build();
        let join1 = Transition::builder("join1")
            .input(one(&a))
            .input(one(&b))
            .input(one(&c))
            .match_spec(MatchSpec::builder().key(&a, key).key(&b, key).build())
            .output(out_place(&out))
            .action(fork())
            .build();
        let join2 = Transition::builder("join2")
            .input(one(&c))
            .input(one(&d))
            .input(one(&pending))
            .match_spec(MatchSpec::builder().key(&c, key).key(&d, key).build())
            .output(out_place(&out))
            .action(fork())
            .build();
        let net = PetriNet::builder("off_key_coloured")
            .transitions([mint_a, mint_b, join1, join2])
            .build();
        let initial = MarkingStateBuilder::new().tokens("srcA", 1).tokens("srcB", 1).build();

        for mode in [FragmentMode::Base, FragmentMode::Extended] {
            let out = verify_via_name_scg(
                &net,
                &initial,
                &SmtProperty::joined_or_dead_lettered("pending"),
                &[],
                &[],
                &EnvironmentAnalysisMode::Ignore,
                MAX,
                mode,
                &BTreeSet::new(),
                &crate::name_fragment::all_mints(&net),
                PrioritySemantics::None,
                &[],
            );
            assert!(
                out.is_none(),
                "{mode:?}: off-key coloured input must fall back, got {:?}",
                out.map(|o| o.verdict)
            );
        }
    }

    // === EXTENDED coloured-consumer fragment ([NU-051]) ===

    /// A fork co-mints one fresh name into `branchA`, `branchB`, and the declared
    /// carrier `stray`; the join consumes `branchA`/`branchB` (leaving `stray`);
    /// a `drain` (when present) dead-letters the leftover `stray`. Without the
    /// drain, `stray` is stranded at quiescence.
    fn comint_carrier_drain_net(with_drain: bool) -> PetriNet {
        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let stray = Place::<String>::new("stray");
        let merged = Place::<String>::new("merged");
        let dl = Place::<()>::new("deadletter");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&a), out_place(&b), out_place(&stray)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();

        let mut builder = PetriNet::builder("comint_carrier_drain").transitions([t_fork, join]);
        if with_drain {
            let drain = Transition::builder("drain")
                .input(one(&stray))
                .output(out_place(&dl))
                .action(fork())
                .build();
            builder = builder.transition(drain);
        }
        builder.build()
    }

    /// EXTENDED admits the carrier-co-mint + drain net (`stray` is a declared
    /// carrier); the drain relays/dead-letters it via [`Role::Consume`].
    #[test]
    fn extended_carrier_comint_drain_in_fragment() {
        let net = comint_carrier_drain_net(true);
        let carriers: BTreeSet<String> = ["stray".to_string()].into_iter().collect();
        let out = verify_via_name_scg(
            &net,
            &MarkingStateBuilder::new().tokens("source", 2).build(),
            &SmtProperty::unreachable(vec!["merged".into()]),
            &[],
            &[],
            &EnvironmentAnalysisMode::Ignore,
            MAX,
            FragmentMode::Extended,
            &carriers,
            &crate::name_fragment::all_mints(&net),
            PrioritySemantics::None,
            &[],
        );
        assert!(out.is_some(), "EXTENDED must admit the carrier-co-mint + drain net");
    }

    /// (f) An unknown carrier name surfaces as `Unknown` naming the offending
    /// place — never a silent fall-back, never a false verdict.
    #[test]
    fn unknown_carrier_place_is_unknown_with_reason() {
        let net = comint_carrier_drain_net(true);
        let carriers: BTreeSet<String> = ["typoStray".to_string()].into_iter().collect();
        let out = verify_via_name_scg(
            &net,
            &MarkingStateBuilder::new().tokens("source", 1).build(),
            &SmtProperty::DeadlockFree,
            &[],
            &[],
            &EnvironmentAnalysisMode::Ignore,
            MAX,
            FragmentMode::Extended,
            &carriers,
            &crate::name_fragment::all_mints(&net),
            PrioritySemantics::None,
            &[],
        )
        .expect("carrier validation must surface an outcome, not fall back");
        match &out.verdict {
            Verdict::Unknown { reason } => assert!(
                reason.contains("typoStray"),
                "reason must name the offending carrier: {reason}"
            ),
            other => panic!("expected Unknown for an unknown carrier, got {other:?}"),
        }
    }

    // === NU-052: conflict-only priority ([PrioritySemantics::Conflict]) ===

    /// The Marvin guard-join vs. timed dead-letter-drain conflict, minimal.
    /// `MINT` co-mints one fresh name into `COL_A` (and `COL_B` when `co_mint_both`);
    /// an immediate, default-priority ν-`JOIN` matches them into `OUT`; a delayed,
    /// lower-priority `DRAIN_A` dead-letters `COL_A` into `DEADLETTER`. `DRAIN_A` and
    /// `JOIN` conflict on `COL_A`.
    fn priority_fixture(co_mint_both: bool, with_drain: bool) -> PetriNet {
        use libpetri_core::timing;

        let seed = Place::<()>::new("SEED");
        let a = Place::<String>::new("COL_A");
        let b = Place::<String>::new("COL_B");
        let out = Place::<String>::new("OUT");
        let dl = Place::<String>::new("DEADLETTER");

        let mint = Transition::builder("MINT")
            .input(one(&seed))
            .output(if co_mint_both {
                and(vec![out_place(&a), out_place(&b)])
            } else {
                out_place(&a)
            })
            .action(fork())
            .build();
        let join = Transition::builder("JOIN") // immediate, priority 0
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&out))
            .action(fork())
            .build();

        let mut builder = PetriNet::builder("priorityFixture").transitions([mint, join]);
        if with_drain {
            let drain = Transition::builder("DRAIN_A") // delayed, lower priority, conflicts on COL_A
                .input(one(&a))
                .timing(timing::delayed(5_000))
                .priority(-10)
                .output(out_place(&dl))
                .action(fork())
                .build();
            builder = builder.transition(drain);
        }
        builder.build()
    }

    /// Runs Route B on the priority fixture as EXTENDED `DeadlockFree`, with `OUT`
    /// and `DEADLETTER` as sinks.
    fn verify_priority(net: &PetriNet, ps: PrioritySemantics) -> NuScgOutcome {
        let sinks = vec!["OUT".to_string(), "DEADLETTER".to_string()];
        verify_via_name_scg(
            net,
            &MarkingStateBuilder::new().tokens("SEED", 1).build(),
            &SmtProperty::DeadlockFree,
            &sinks,
            &[],
            &EnvironmentAnalysisMode::Ignore,
            MAX,
            FragmentMode::Extended,
            &BTreeSet::new(),
            &crate::name_fragment::all_mints(&net),
            ps,
            &[],
        )
        .expect("EXTENDED must admit the priority fixture")
    }

    #[test]
    fn priority_blind_none_reports_spurious_stall() {
        // NONE (default, priority/timing-blind): the graph explores DRAIN_A stealing
        // the matched COL_A and stranding COL_B — a spurious stall.
        let out = verify_priority(&priority_fixture(true, true), PrioritySemantics::None);
        assert!(
            out.verdict.is_violated(),
            "priority-blind NONE must report the spurious stall: {:?}",
            out.verdict
        );
    }

    #[test]
    fn conflict_priority_proves_no_stall() {
        // CONFLICT: the immediate, higher-priority join pre-empts the delayed drain,
        // so COL_A is never stolen from a live join.
        let out = verify_priority(&priority_fixture(true, true), PrioritySemantics::Conflict);
        assert!(
            out.verdict.is_proven(),
            "CONFLICT must prove no-stall: {:?}",
            out.verdict
        );
    }

    #[test]
    fn conflict_priority_still_finds_genuine_stall() {
        // A real orphan (COL_A with no matching COL_B) and no drain: the join can
        // never fire and COL_A strands. CONFLICT must NOT hide this — the join is
        // not enabled, so nothing is pruned.
        let out = verify_priority(&priority_fixture(false, false), PrioritySemantics::Conflict);
        assert!(
            out.verdict.is_violated(),
            "CONFLICT must still find the genuine stall: {:?}",
            out.verdict
        );
    }

    #[test]
    fn conflict_priority_lets_drain_clear_a_real_orphan() {
        // A real orphan WITH the drain: CONFLICT does not prune the drain (the join
        // is not enabled), so the orphan is dead-lettered and the net is
        // deadlock-free.
        let out = verify_priority(&priority_fixture(false, true), PrioritySemantics::Conflict);
        assert!(
            out.verdict.is_proven(),
            "CONFLICT must let the drain clear a genuine orphan: {:?}",
            out.verdict
        );
    }

    // ---- [NU-020] / [TIME-012]: a join's clock follows its name-enabledness ----

    /// `forkA` and `forkB` mint one name each into `branchA` and `branchB`
    /// (`deadline(1)`), `forkC` co-mints one name into both at `exact(5)` when
    /// `with_co_mint`, and `join` matches the two on the name with `join_timing`. The
    /// watchdog `W -> BAD` fires with `watchdog_timing`.
    fn clocked_join_net(
        join_timing: libpetri_core::timing::Timing,
        watchdog_timing: libpetri_core::timing::Timing,
        with_co_mint: bool,
    ) -> PetriNet {
        use libpetri_core::timing;
        let p = |n: &str| Place::<String>::new(n);
        let key = |s: &String| NameId::new(s.clone());
        let mint = |name: &str, from: &str, to: Vec<&str>, timing| {
            Transition::builder(name)
                .input(one(&p(from)))
                .output(and(to.into_iter().map(|t| out_place(&p(t))).collect()))
                .timing(timing)
                .action(fork())
                .build()
        };
        let mut ts = vec![
            mint("forkA", "sourceA", vec!["branchA"], timing::deadline(1)),
            mint("forkB", "sourceB", vec!["branchB"], timing::deadline(1)),
            Transition::builder("join")
                .input(one(&p("branchA")))
                .input(one(&p("branchB")))
                .match_spec(MatchSpec::builder().key(&p("branchA"), key).key(&p("branchB"), key).build())
                .output(out_place(&p("merged")))
                .timing(join_timing)
                .action(fork())
                .build(),
            Transition::builder("watchdog")
                .input(one(&p("W")))
                .output(out_place(&p("BAD")))
                .timing(watchdog_timing)
                .action(fork())
                .build(),
        ];
        if with_co_mint {
            ts.push(mint("forkC", "sourceC", vec!["branchA", "branchB"], timing::exact(5)));
        }
        PetriNet::builder("clocked_join").transitions(ts).build()
    }

    /// R6: the two names never match, so the executor never enables `join` and the
    /// watchdog fires at 10 ms. A graph that clocked the count-enabled join would let
    /// its `window(0, 5)` deadline forbid the watchdog and prove `BAD` unreachable.
    /// Checked on time (no reaping), where the join keeps its latest bound.
    #[test]
    fn a_name_disabled_join_has_no_clock() {
        use libpetri_core::timing;
        let net = clocked_join_net(timing::window(0, 5), timing::delayed(10), false);
        let initial = MarkingStateBuilder::new()
            .tokens("sourceA", 1)
            .tokens("sourceB", 1)
            .tokens("W", 1)
            .build();
        let out = verify(&net, &initial, SmtProperty::unreachable(vec!["BAD".into()]));
        assert!(out.verdict.is_violated(), "the watchdog fires at 10 ms: {:?}", out.verdict);
        assert!(!out.transitions.iter().any(|t| t == "join"), "{:?}", out.transitions);
    }

    /// The join is count-enabled from 1 ms but name-enabled only when `forkC` co-mints
    /// at 5 ms, so its `delayed(10)` clock starts at 5 ms and it fires at 15 ms at the
    /// earliest, after the watchdog's `exact(12)`: `merged` and `W` are never marked
    /// together. Clocking the join from its count enabling lets it fire at 10 ms.
    #[test]
    fn a_join_clock_starts_when_its_binding_appears() {
        use libpetri_core::timing;
        let net = clocked_join_net(timing::delayed(10), timing::exact(12), true);
        let initial = MarkingStateBuilder::new()
            .tokens("sourceA", 1)
            .tokens("sourceB", 1)
            .tokens("sourceC", 1)
            .tokens("W", 1)
            .build();
        let out = verify(
            &net,
            &initial,
            SmtProperty::mutual_exclusion(vec!["merged".into(), "W".into()]),
        );
        assert!(out.verdict.is_proven(), "the join fires at 15 ms at the earliest: {:?}", out.verdict);
    }

    /// [NU-055], [VER-012] AC5: on the search-as-you-type net, `NameAligned(box, list)`
    /// stops at its first misaligned class with the full build's verdict and witness, and
    /// the quiescent form holds on the closed graph. The quiescent form on the buggy
    /// variant, a net without a matched transition, is violated with 12 firings.
    #[test]
    fn nu055_route_b_decides_name_alignment_on_the_search_as_you_type_net() {
        use crate::relay_nets::{pnid_net, search_as_you_type};
        let m0 = MarkingStateBuilder::new()
            .tokens("typed", 2)
            .tokens("idle", 1)
            .tokens("listEmpty", 1)
            .tokens("slot", 1)
            .build();
        let mints: BTreeSet<String> = ["sendA", "sendB"].map(String::from).into();
        let run = |bug: bool, carriers: &[&str], property: SmtProperty| {
            let net = pnid_net(if bug { "searchAsYouTypeBug" } else { "searchAsYouType" }, &search_as_you_type(bug));
            let carriers: BTreeSet<String> = carriers.iter().map(|c| c.to_string()).collect();
            verify_via_name_scg(
                &net,
                &m0,
                &property,
                &[],
                &[],
                &EnvironmentAnalysisMode::Ignore,
                MAX,
                FragmentMode::Extended,
                &carriers,
                &mints,
                PrioritySemantics::None,
                &[],
            )
            .expect("in the EXTENDED fragment")
        };
        let fixed = ["inflightA", "inflightB", "list"];
        let transient = run(false, &fixed, SmtProperty::name_aligned(["box", "list"]));
        assert!(transient.verdict.is_violated(), "{:?}", transient.verdict);
        assert_eq!(transient.transitions.len(), 8, "{:?}", transient.transitions);
        assert!(transient.note.contains("stopped at the first violating class"), "{}", transient.note);
        let at_rest = run(false, &fixed, SmtProperty::quiescent_name_aligned(["box", "list"]));
        assert!(at_rest.verdict.is_proven(), "{:?}", at_rest.verdict);
        let bug = ["box", "inflightA", "inflightB", "reply", "staged", "list"];
        let stale = run(true, &bug, SmtProperty::quiescent_name_aligned(["box", "list"]));
        assert!(stale.verdict.is_violated(), "{:?}", stale.verdict);
        assert_eq!(stale.transitions.len(), 12, "{:?}", stale.transitions);
        // [NU-055] AC2: an uncoloured place is refused by name, never proven.
        let ready = run(false, &fixed, SmtProperty::quiescent_name_aligned(["box", "ready"]));
        assert!(
            matches!(&ready.verdict, Verdict::Unknown { reason } if reason.contains("place 'ready' is not a coloured place")),
            "{:?}",
            ready.verdict
        );
    }

    /// [NU-055]: the refusal reads only the name-alignment properties.
    #[test]
    fn nu055_the_refusal_is_for_name_alignment_only() {
        use crate::relay_nets::{pnid_net, search_as_you_type};
        let net = pnid_net("searchAsYouType", &search_as_you_type(false));
        let carriers: BTreeSet<String> = ["inflightA", "inflightB", "list"].map(String::from).into();
        let fragment = name_fragment::classify(&net, FragmentMode::Extended, &carriers, &crate::name_fragment::all_mints(&net), false)
            .expect("in the fragment");
        let marked = MarkingStateBuilder::new().tokens("box", 1).build();
        assert_eq!(
            name_alignment_refusal(&SmtProperty::place_bound("ready", 0), &fragment, FragmentMode::Extended, &marked),
            None
        );
        assert_eq!(
            name_alignment_refusal(
                &SmtProperty::name_aligned(["box", "list"]),
                &fragment,
                FragmentMode::Extended,
                &MarkingStateBuilder::new().build()
            ),
            None
        );
        let refused =
            name_alignment_refusal(&SmtProperty::name_aligned(["box", "list"]), &fragment, FragmentMode::Extended, &marked);
        assert!(refused.is_some_and(|r| r.starts_with("coloured place 'box' holds a token in the initial marking")));
    }
}
