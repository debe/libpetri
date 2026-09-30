//! In-flight actions in verification ([VER-004], [EXEC-001], [EXEC-003]).
//!
//! Every route reads a firing as one atomic step. The executor does not fire
//! that way: it consumes a firing's inputs when the action starts and deposits
//! its outputs when the action completes, and other transitions fire in
//! between. An asynchronous action leaves that gap open for as long as it runs;
//! a synchronous one leaves it open until the end of its firing pass, because a
//! drain later in the same pass does not see the deposit ([EXEC-003] AC5).
//!
//! For most nets the gap changes nothing. A run with `t` in flight can be
//! reordered so that `t`'s deposit comes right after its start, as long as no
//! step in between tests one of `t`'s output places non-monotonically: the
//! steps in between see more tokens there, and a transition that only needs
//! tokens is still enabled and does the same. An **inhibitor** arc, a **reset**
//! arc and a **draining** input (`all`, `at_least`) are the non-monotone tests:
//! more tokens can disable an inhibited transition, and a drain or reset takes
//! a different number of tokens. A terminal place ([EXEC-042]) counts as one,
//! since it inhibits every transition.
//!
//! So a transition `t` needs the executor's two-step firing exactly when some
//! transition tests one of `t`'s output places that way. [`split_in_flight`]
//! splits each such `t` into
//!
//! - `t` itself, with every input, read, inhibitor and reset arc, its timing,
//!   priority and match spec, whose only output is the fresh place
//!   `inflight:<t>`, and
//! - `complete:<t>`, immediate, consuming `inflight:<t>` and depositing `t`'s
//!   output spec (every branch, the `Timeout` branch included).
//!
//! Every other transition stays atomic, so a net without such a transition is
//! not rewritten and verifies, and scripts, exactly as before. A marked
//! `inflight:<t>` never rests: `complete:<t>` is enabled, immediate and not
//! reapable. Lean mechanises the reordering argument in
//! `Libpetri/Novel/InFlight.lean`: `commute_add` is the one-step reordering,
//! `atomic_covers_executor` covers a net this module leaves atomic, and
//! `split_covers_executor` with `split_rest_sound` covers the split net, its
//! rests included.
//!
//! Two more readings test a place without an arc, and the verifier adds them to the
//! tested places ([`SplitDemand`]):
//!
//! - A **terminal place** stops the net without waiting for an action in flight
//!   ([EXEC-042]): the action is abandoned, its inputs consumed and its outputs never
//!   deposited. Removing tokens is harmless to every quiescence property but one: a
//!   `QuiescentCount` with a lower bound, when some terminal does not waive it. For it
//!   the places the count reads and its waiver places are tested too
//!   ([`quiescent_count_demand`]), so every transition depositing there is split and
//!   the terminal, which inhibits `complete:<t>` as it inhibits every transition,
//!   models the abandonment.
//! - **Conflict priority** on Route B ([NU-052]) fires `L` only when no conflicting,
//!   higher-priority `H` is enabled, a test of `H`'s input and read places that more
//!   tokens can fail. Those places are tested too, and every such `H` is split as well:
//!   while `inflight:<H>` is marked, `H` pre-empts nothing, since the Java and
//!   TypeScript executors do not start `H` again while its action runs
//!   ([`conflict_demand`]).
//!
//! The split deposits a transition's outputs together, when its completion step fires.
//! An action that calls `ctx.flush()` publishes some of them while it still runs, and
//! a transition testing an output non-monotonically can see that partial deposit. The
//! split does not model it, and a split verdict says so ([`FLUSH_NOTE`]).
//!
//! Three cases are refused rather than split ([`InFlight::Refused`]): a
//! transition to split that is a ν-join or a writer into a coloured place (its
//! halves would lose the name the output carries, [NU-010], [NU-020], [NU-054]);
//! a `Timeout` forward of more than one token
//! (`exactly(n)`, `all`, `at_least`, [IO-014]), whose count the completion step
//! cannot see; and a name the split would add that the net already uses.

use std::collections::HashSet;

use libpetri_core::input::In;
use libpetri_core::output::Out;
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::PlaceRef;
use libpetri_core::timing::immediate;
use libpetri_core::transition::Transition;

use crate::marking_state::MarkingState;
use crate::property::SmtProperty;

/// What [`split_in_flight`] did to a net.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum InFlight {
    /// No transition needs the two-step firing: verify the net as it is.
    Atomic,
    /// The rewritten net, and the names of the transitions it split, in net order.
    Split { net: PetriNet, split: Vec<String> },
    /// The net needs the two-step firing and the split cannot express it; no
    /// route may answer ([VER-004]). The reason names the transition.
    Refused { reason: String },
}

/// The in-flight place of transition `t`.
pub fn in_flight_place(t: &str) -> String {
    format!("inflight:{t}")
}

/// The completion transition of transition `t`.
pub fn completion_transition(t: &str) -> String {
    format!("complete:{t}")
}

/// Every place some transition tests non-monotonically: an inhibitor, a reset, a
/// draining input (`all`, `at_least`), and every terminal place ([EXEC-042]).
pub fn non_monotone_places(net: &PetriNet) -> HashSet<String> {
    let mut out: HashSet<String> = net.terminals().iter().map(|p| p.name().to_string()).collect();
    for t in net.transitions() {
        out.extend(t.inhibitors().iter().map(|a| a.place.name().to_string()));
        out.extend(t.resets().iter().map(|a| a.place.name().to_string()));
        for spec in t.input_specs() {
            if matches!(spec, In::All { .. } | In::AtLeast { .. }) {
                out.insert(spec.place_name().to_string());
            }
        }
    }
    out
}

/// Whether `t` is a completion step: `complete:<x>`, whose one input is
/// `one(inflight:<x>)`, with no read or reset arc. It is itself a single deposit, so
/// it is never split, which makes [`split_in_flight`] idempotent, also after the
/// terminal rewrite has given it an inhibitor ([EXEC-042]).
fn is_completion(t: &Transition) -> bool {
    let Some(x) = t.name().strip_prefix("complete:") else {
        return false;
    };
    matches!(t.input_specs(), [In::One { place }] if place.name() == in_flight_place(x))
        && t.reads().is_empty()
        && t.resets().is_empty()
}

/// The transitions of `net` that need the executor's two-step firing, in net order:
/// those with an output place some transition tests non-monotonically. `environment`
/// names the transitions that model the environment rather than an action of the net
/// (the arrivals of [VER-006], the environment of an open-net contract, [VER-022]): the
/// executor runs no action for them, and an injection deposits at once, so they stay
/// atomic. Their arcs still count as tests.
pub fn in_flight_transitions(net: &PetriNet, environment: &HashSet<String>) -> Vec<String> {
    in_flight_transitions_for(net, environment, &SplitDemand::default())
}

/// [`in_flight_transitions`] with the places and transitions `demand` adds: a transition
/// is split when an output is in [`non_monotone_places`] or in `demand.tested`, or when
/// `demand.forced` names it. Environment steps and completion steps stay atomic.
pub(crate) fn in_flight_transitions_for(
    net: &PetriNet,
    environment: &HashSet<String>,
    demand: &SplitDemand,
) -> Vec<String> {
    let mut tested = non_monotone_places(net);
    tested.extend(demand.tested.iter().cloned());
    net.transitions()
        .iter()
        .filter(|t| !is_completion(t) && !environment.contains(t.name()))
        .filter(|t| {
            demand.forced.contains(t.name()) || t.output_places().iter().any(|p| tested.contains(p.name()))
        })
        .map(|t| t.name().to_string())
        .collect()
}

/// What a verification tests beyond the arcs of its net ([`non_monotone_places`]), and
/// so adds to the split (module docs).
#[derive(Debug, Clone, Default)]
pub(crate) struct SplitDemand {
    /// Places tested non-monotonically: every transition depositing into one is split.
    pub tested: HashSet<String>,
    /// Transitions split whatever their outputs.
    pub forced: HashSet<String>,
}

impl SplitDemand {
    #[cfg_attr(not(feature = "z3"), allow(dead_code))]
    pub(crate) fn extend(&mut self, other: SplitDemand) {
        self.tested.extend(other.tested);
        self.forced.extend(other.forced);
    }
}

/// The places a terminal stop can leave short ([EXEC-042], [VER-004]): the places
/// `property` counts and its waiver places, when it is a `QuiescentCount` with a lower
/// bound above zero and `net` has a terminal place the waivers do not name. Every other
/// quiescence property holds of a marking whenever it holds of one with more tokens at
/// a terminal rest, which every terminal excuses, so an abandoned action cannot break it.
/// Empty otherwise.
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
pub(crate) fn quiescent_count_demand(net: &PetriNet, property: &SmtProperty) -> SplitDemand {
    let SmtProperty::QuiescentCount { places, min, waived_by, .. } = property else {
        return SplitDemand::default();
    };
    let unwaived_terminal = net.terminals().iter().any(|p| !waived_by.iter().any(|w| w == p.name()));
    if *min == 0 || !unwaived_terminal {
        return SplitDemand::default();
    }
    SplitDemand {
        tested: places.iter().chain(waived_by).cloned().collect(),
        forced: HashSet::new(),
    }
}

/// The transitions of `net` that can pre-empt another under conflict priority
/// ([NU-052]): each `H` with a strictly higher priority than some other transition that
/// consumes one of `H`'s input places. In net order.
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
pub(crate) fn conflict_pruners(net: &PetriNet) -> Vec<String> {
    net.transitions()
        .iter()
        .filter(|h| {
            let inputs = h.input_places();
            net.transitions().iter().any(|l| {
                l.name() != h.name()
                    && h.priority() > l.priority()
                    && l.input_places().iter().any(|p| inputs.contains(p))
            })
        })
        .map(|h| h.name().to_string())
        .collect()
}

/// What conflict priority ([NU-052]) adds to the split: every pruner of
/// [`conflict_pruners`] is forced, and its input and read places are tested, since
/// more tokens there can enable it and so disable the transition it pre-empts.
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
pub(crate) fn conflict_demand(net: &PetriNet) -> SplitDemand {
    let pruners = conflict_pruners(net);
    let mut demand = SplitDemand::default();
    for h in net.transitions().iter().filter(|t| pruners.iter().any(|p| p == t.name())) {
        demand.tested.extend(h.input_places().iter().map(|p| p.name().to_string()));
        demand.tested.extend(h.reads().iter().map(|a| a.place.name().to_string()));
        demand.forced.insert(h.name().to_string());
    }
    demand
}

/// Splits every transition of [`in_flight_transitions`] into a start and a
/// completion (module docs). `coloured` names the places whose tokens carry a ν name
/// beyond the match specs' keys and relay targets (the declared carrier places); a
/// transition to split that is a ν-join or writes a coloured place is refused. A mint
/// ([NU-010]) mints only into a coloured place, so that covers it too. `environment` is
/// as for [`in_flight_transitions`].
pub fn split_in_flight(net: &PetriNet, coloured: &HashSet<String>, environment: &HashSet<String>) -> InFlight {
    split_in_flight_for(net, coloured, environment, &SplitDemand::default())
}

/// [`split_in_flight`] of the transitions [`in_flight_transitions_for`] names under
/// `demand`.
pub(crate) fn split_in_flight_for(
    net: &PetriNet,
    coloured: &HashSet<String>,
    environment: &HashSet<String>,
    demand: &SplitDemand,
) -> InFlight {
    let split = in_flight_transitions_for(net, environment, demand);
    if split.is_empty() {
        return InFlight::Atomic;
    }
    if let Some((t, cause)) = first_unsplittable(net, coloured, &split) {
        let head = if in_flight_transitions(net, environment).contains(&t) {
            refusal_head(&t)
        } else {
            demand_refusal_head(&t)
        };
        return InFlight::Refused { reason: format!("{head} {cause}") };
    }
    let to_split: HashSet<&str> = split.iter().map(String::as_str).collect();
    let transitions = net.transitions().iter().flat_map(|t| {
        if to_split.contains(t.name()) {
            let (start, end) = halves(t);
            vec![start, end]
        } else {
            vec![t.clone()]
        }
    });
    let rewritten = PetriNet::builder(net.name())
        .places(net.places().iter().cloned())
        .transitions(transitions.collect::<Vec<_>>())
        .terminals(net.terminals().iter().cloned())
        .build();
    InFlight::Split { net: rewritten, split }
}

/// The first transition of `split`, in net order, that the split cannot express, with
/// the cause ([`refusal_cause`]). `coloured` is as for [`split_in_flight`].
pub(crate) fn first_unsplittable(
    net: &PetriNet,
    coloured: &HashSet<String>,
    split: &[String],
) -> Option<(String, String)> {
    let mut coloured: HashSet<String> = coloured.clone();
    for t in net.transitions() {
        if let Some(ms) = t.match_spec() {
            coloured.extend(ms.keys().iter().map(|k| k.place_name().to_string()));
            coloured.extend(ms.relays().iter().map(|k| k.place_name().to_string()));
        }
    }
    let names: HashSet<&str> = net
        .places()
        .iter()
        .map(|p| p.name())
        .chain(net.transitions().iter().map(|t| t.name()))
        .collect();
    let to_split: HashSet<&str> = split.iter().map(String::as_str).collect();
    net.transitions()
        .iter()
        .filter(|t| to_split.contains(t.name()))
        .find_map(|t| refusal_cause(t, &coloured, &names).map(|cause| (t.name().to_string(), cause)))
}

/// The opening of the refusal of transition `name`.
fn refusal_head(name: &str) -> String {
    format!(
        "transition '{name}' must be verified as two steps, since its action runs between \
         consuming and depositing and another transition tests one of its outputs with an \
         inhibitor, reset or drain (VER-004), but"
    )
}

/// The opening of the refusal of transition `name` when only a [`SplitDemand`] splits
/// it: a `QuiescentCount` lower bound over a place it deposits into, on a net with a
/// terminal place ([`quiescent_count_demand`]).
fn demand_refusal_head(name: &str) -> String {
    format!(
        "transition '{name}' must be verified as two steps, since a terminal place can stop \
         the net while its action runs and the property's lower bound counts a place it \
         deposits into (VER-004, EXEC-042), but"
    )
}

/// Why `t` cannot be split, if it cannot: the clause that completes [`refusal_head`].
fn refusal_cause(t: &Transition, coloured: &HashSet<String>, names: &HashSet<&str>) -> Option<String> {
    let name = t.name();
    if t.match_spec().is_some() {
        return Some("it is a ν-join, whose outputs carry the matched name (NU-020, NU-054)".to_string());
    }
    let mut outs: Vec<&str> = t.output_places().iter().map(|p| p.name()).collect();
    outs.sort_unstable();
    if let Some(p) = outs.iter().find(|p| coloured.contains(**p)) {
        return Some(format!("it writes the coloured place '{p}', whose tokens carry a ν name"));
    }
    if let Some((from, to)) = t.output_spec().and_then(|o| multi_token_forward(o, t, false)) {
        return Some(format!(
            "its timeout forwards input '{from}' to '{to}', one token per token consumed (IO-014), \
             a count its completion step cannot see"
        ));
    }
    for added in [in_flight_place(name), completion_transition(name)] {
        if names.contains(added.as_str()) {
            return Some(format!("the net already uses the name '{added}' the split would add"));
        }
    }
    None
}

/// The first `ForwardInput` under a `Timeout` whose source input is not `one`.
fn multi_token_forward(out: &Out, t: &Transition, under_timeout: bool) -> Option<(String, String)> {
    match out {
        Out::Place(_) => None,
        Out::ForwardInput { from, to } => {
            let single = matches!(
                t.input_specs().iter().find(|s| s.place_name() == from.name()),
                Some(In::One { .. }) | None
            );
            (under_timeout && !single).then(|| (from.name().to_string(), to.name().to_string()))
        }
        Out::Timeout { child, .. } => multi_token_forward(child, t, true),
        Out::And(children) | Out::Xor(children) => {
            children.iter().find_map(|c| multi_token_forward(c, t, under_timeout))
        }
    }
}

/// `t`'s output spec for its completion step: a `ForwardInput(from, to)` leaf becomes
/// the place `to`. The action path writes one token there either way ([IO-016]), and
/// [`refusal_cause`] has already turned away a timeout forward of more than one token.
fn completion_output(out: &Out) -> Out {
    match out {
        Out::Place(p) => Out::Place(p.clone()),
        Out::ForwardInput { to, .. } => Out::Place(to.clone()),
        Out::And(children) => Out::And(children.iter().map(completion_output).collect()),
        Out::Xor(children) => Out::Xor(children.iter().map(completion_output).collect()),
        Out::Timeout { after_ms, child } => Out::Timeout {
            after_ms: *after_ms,
            child: Box::new(completion_output(child)),
        },
    }
}

/// The start and the completion step of `t`.
fn halves(t: &Transition) -> (Transition, Transition) {
    let place = PlaceRef::new(in_flight_place(t.name()));
    let mut start = Transition::builder(t.name_arc().clone())
        .timing(*t.timing())
        .priority(t.priority())
        .action(t.action().clone())
        .inputs(t.input_specs().to_vec())
        .inhibitors(t.inhibitors().to_vec())
        .reads(t.reads().to_vec())
        .resets(t.resets().to_vec())
        .output(Out::Place(place.clone()));
    if let Some(ms) = t.match_spec() {
        start = start.match_spec(ms.clone());
    }
    if let Some(map) = t.local_name_map_cloned() {
        start = start.local_name_map(map);
    }
    let mut end = Transition::builder(completion_transition(t.name()))
        .timing(immediate())
        .priority(t.priority())
        .action(t.action().clone())
        .input(In::One { place });
    if let Some(out) = t.output_spec() {
        end = end.output(completion_output(out));
    }
    (start.build(), end.build())
}

/// The report line naming the split transitions.
pub fn split_note(split: &[String]) -> String {
    let names = split.join(", ");
    format!(
        "In-flight actions (VER-004): {names} {verb} verified in two steps, a start that consumes \
         and a completion step (complete:<name>) that deposits, because another transition tests \
         an output with an inhibitor, reset or drain and the executor fires other transitions \
         while an action is in flight.\n",
        verb = if split.len() == 1 { "is" } else { "are" }
    )
}

/// Why a verification splits beyond the arcs of its net ([`SplitDemand`]).
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct SplitReasons {
    /// Some transition tests an output non-monotonically ([`non_monotone_places`]).
    pub tested: bool,
    /// [`quiescent_count_demand`] added a transition.
    pub terminal: bool,
    /// Conflict priority is applied with pruners ([`conflict_demand`]).
    pub conflict: bool,
}

#[cfg_attr(not(feature = "z3"), allow(dead_code))]
impl SplitReasons {
    /// Whether the plain [`split_note`] says it all.
    pub(crate) fn plain(&self) -> bool {
        !self.terminal && !self.conflict
    }

    fn clauses(&self) -> String {
        let mut out: Vec<&str> = Vec::new();
        if self.tested {
            out.push("another transition tests an output with an inhibitor, reset or drain");
        }
        if self.terminal {
            out.push(
                "a terminal place stops the net without waiting for an action in flight (EXEC-042) \
                 and the property's lower bound counts a place one of them deposits into",
            );
        }
        if self.conflict {
            out.push(
                "conflict priority (NU-052) reads whether a pruning transition is enabled, so a \
                 transition pre-empts no other while its own action is in flight",
            );
        }
        out.join("; ")
    }
}

/// The report line naming the split transitions when the verification added some
/// ([`SplitDemand`]); [`split_note`] when it added none.
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
pub(crate) fn split_note_for(split: &[String], reasons: SplitReasons) -> String {
    if reasons.plain() {
        return split_note(split);
    }
    format!(
        "In-flight actions (VER-004): {names} {verb} verified in two steps, a start that consumes \
         and a completion step (complete:<name>) that deposits, because the executor fires other \
         transitions while an action is in flight and {clauses}.\n",
        names = split.join(", "),
        verb = if split.len() == 1 { "is" } else { "are" },
        clauses = reasons.clauses(),
    )
}

/// The report line of a split verdict in Rust: `ctx.flush()` is not modelled (module
/// docs). Python rides on this runtime and reports it too.
pub const FLUSH_NOTE: &str = "In-flight actions (VER-004): the outputs of a split transition are \
read as landing together when its action completes; an action that calls ctx.flush() publishes \
some of them earlier, which this verdict does not model.\n";

/// The report line of a verdict reached with conflict priority ([NU-052]) turned off,
/// because `transition` has to be split for the pruning to hold and cannot be (`cause`,
/// as [`first_unsplittable`] gives it).
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
pub(crate) fn conflict_off_note(transition: &str, cause: &str) -> String {
    format!(
        "Conflict priority (NU-052) is off: it holds only while no pruning transition, and no \
         transition depositing into the input or read places of one, has an action in flight, \
         which the verifier models by splitting them (VER-004), and transition '{transition}' \
         cannot be split: {cause}. Every enabled transition is explored.\n"
    )
}

/// The report line of a verdict reached under `assume_atomic_firing` on a net with a
/// transition the split would have applied to, when the verification added some
/// ([`SplitDemand`]); [`atomic_assumption_note`] when it added none.
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
pub(crate) fn atomic_assumption_note_for(split: &[String], reasons: SplitReasons) -> String {
    if reasons.plain() {
        return atomic_assumption_note(split);
    }
    format!(
        "ASSUMPTION: every firing is atomic (the assume-atomic-firing option). The executor fires \
         other transitions while an action of {names} is in flight, and {clauses} (VER-004); this \
         verdict holds only for runs in which none of those actions is in flight when that \
         matters.\n",
        names = split.join(", "),
        clauses = reasons.clauses(),
    )
}

/// The transitions a counterexample starts while an earlier firing of each is still in
/// flight ([CONC-002]): step `i` fires `transitions[i]` from `trace[i]`, and names a
/// start whose place `inflight:<name>` is marked there. First occurrence order, each
/// once. Empty when the trace is not aligned (`trace.len() != transitions.len() + 1`).
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
pub(crate) fn restarted_transitions(trace: &[MarkingState], transitions: &[String]) -> Vec<String> {
    if trace.len() != transitions.len() + 1 {
        return Vec::new();
    }
    let mut out: Vec<String> = Vec::new();
    for (t, before) in transitions.iter().zip(trace) {
        if before.count(&in_flight_place(t)) > 0 && !out.contains(t) {
            out.push(t.clone());
        }
    }
    out
}

/// The report line of a counterexample that restarts a transition in flight
/// ([CONC-002], [`restarted_transitions`]): the split lets a start fire again while its
/// completion is pending, as the Rust executor does, and the Java and TypeScript
/// executors never do. `None` when it restarts none.
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
pub(crate) fn restart_note(trace: &[MarkingState], transitions: &[String]) -> Option<String> {
    let restarted = restarted_transitions(trace, transitions);
    if restarted.is_empty() {
        return None;
    }
    let names: Vec<String> = restarted.iter().map(|t| format!("'{t}'")).collect();
    let places: Vec<String> = restarted.iter().map(|t| in_flight_place(t)).collect();
    let (its, firing, is) =
        if restarted.len() == 1 { ("its", "firing", "is") } else { ("their", "firings", "are") };
    Some(format!(
        "NOTE (CONC-002): the counterexample starts {} again while {its} earlier {firing} {is} still \
         in flight ({} marked). The Rust executor starts a transition again while its action runs; \
         the Java and TypeScript executors never do, so on them this counterexample may be a \
         false alarm.\n",
        names.join(", "),
        places.join(", "),
    ))
}

/// The name of the transition of the caller's net that `name` stands for: `t` for the
/// completion step `complete:<t>` of a split net that holds `inflight:<t>`, `name`
/// itself otherwise.
pub(crate) fn source_transition<'n>(net: &PetriNet, name: &'n str) -> &'n str {
    match net.transitions().iter().find(|t| t.name() == name) {
        Some(t) if is_completion(t) => &name["complete:".len()..],
        _ => name,
    }
}

/// The report line of a verdict reached under `assume_atomic_firing` on a net with a
/// transition the split would have applied to.
pub fn atomic_assumption_note(split: &[String]) -> String {
    format!(
        "ASSUMPTION: every firing is atomic (the assume-atomic-firing option). Another transition \
         tests an output of {} with an inhibitor, reset or drain, and the executor fires other \
         transitions while an action is in flight (VER-004); this verdict holds only for runs in \
         which no such test happens while one of those actions runs.\n",
        split.join(", ")
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::action::fork;
    use libpetri_core::arc::inhibitor;
    use libpetri_core::input::{all, one};
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;

    fn p(name: &str) -> Place<()> {
        Place::new(name)
    }

    /// `t: p → p` and `u: q + inhibitor(p) → r`.
    fn inhibitor_net() -> PetriNet {
        PetriNet::builder("n")
            .transition(Transition::builder("t").input(one(&p("p"))).output(out_place(&p("p"))).action(fork()).build())
            .transition(
                Transition::builder("u")
                    .input(one(&p("q")))
                    .inhibitor(inhibitor(&p("p")))
                    .output(out_place(&p("r")))
                    .action(fork())
                    .build(),
            )
            .build()
    }

    #[test]
    fn a_transition_whose_output_is_inhibited_is_split() {
        let net = inhibitor_net();
        assert_eq!(in_flight_transitions(&net, &HashSet::new()), vec!["t".to_string()]);
        let InFlight::Split { net: split, split: names } =
            split_in_flight(&net, &HashSet::new(), &HashSet::new())
        else {
            panic!("expected a split");
        };
        assert_eq!(names, vec!["t".to_string()]);
        let order: Vec<&str> = split.transitions().iter().map(|t| t.name()).collect();
        assert_eq!(order, ["t", "complete:t", "u"]);
        let places: Vec<&str> = split.places().iter().map(|p| p.name()).collect();
        assert_eq!(places, ["p", "q", "r", "inflight:t"]);
        // Idempotent: the completion step is never split again.
        assert!(matches!(
            split_in_flight(&split, &HashSet::new(), &HashSet::new()),
            InFlight::Atomic
        ));
        // An environment step stays atomic.
        let env: HashSet<String> = ["t".to_string()].into();
        assert!(in_flight_transitions(&net, &env).is_empty());
    }

    #[test]
    fn a_net_with_only_monotone_tests_of_outputs_is_atomic() {
        // `u` inhibited by `q`, which nothing writes: no transition is split.
        let net = PetriNet::builder("n")
            .transition(Transition::builder("t").input(one(&p("p"))).output(out_place(&p("p"))).action(fork()).build())
            .transition(Transition::builder("u").input(all(&p("a"))).inhibitor(inhibitor(&p("q"))).build())
            .build();
        assert!(in_flight_transitions(&net, &HashSet::new()).is_empty());
        assert!(matches!(
            split_in_flight(&net, &HashSet::new(), &HashSet::new()),
            InFlight::Atomic
        ));
    }

    #[test]
    fn a_producer_of_a_terminal_place_is_split() {
        let net = PetriNet::builder("n")
            .transition(Transition::builder("t").input(one(&p("a"))).output(out_place(&p("done"))).action(fork()).build())
            .terminal(&p("done"))
            .build();
        assert_eq!(in_flight_transitions(&net, &HashSet::new()), vec!["t".to_string()]);
    }

    #[test]
    fn a_writer_into_a_coloured_place_is_refused() {
        let coloured: HashSet<String> = ["p".to_string()].into();
        assert!(matches!(
            split_in_flight(&inhibitor_net(), &coloured, &HashSet::new()),
            InFlight::Refused { .. }
        ));
    }
}
