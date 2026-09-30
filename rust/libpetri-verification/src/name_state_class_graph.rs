//! The ν-aware (name-partition quotient) State Class Graph ([NU-050], Route B).
//!
//! Mirrors [`crate::state_class_graph::StateClassGraph`] — same Berthomieu-Diaz
//! BFS, same count + DBM successor step (reused verbatim via
//! [`crate::state_class_graph::compute_successor`]) — but each class additionally
//! carries the abstract [`NameMarking`] partition. The differences:
//!
//! - a **ν-join** is enabled only when one shared name is present at the required
//!   multiplicity in every correlated input (not merely when the counts allow);
//! - a **mint** introduces a globally-fresh name-symbol into its coloured outputs;
//! - dedup is by the symmetry-canonical key, so states that differ only by a
//!   permutation of names collapse — the quotient that keeps the graph finite
//!   when live names are structurally bounded.
//!
//! ν-Petri-net reachability is undecidable; if BFS closes within `max_classes`
//! the graph is the complete reachable quotient (an *exact* answer), otherwise it
//! is truncated (`complete == false`): the verifier then reads only its explored
//! prefix, where a violation still stands, and otherwise reports `Unknown`
//! ([VER-012] AC3).

use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use libpetri_core::petri_net::PetriNet;
use libpetri_core::transition::Transition;

use crate::environment::EnvironmentAnalysisMode;
use crate::marking_state::MarkingState;
use crate::name_fragment::{NameFragment, Role};
use crate::name_marking::{NameMarking, Sym};
use crate::name_state_class::NameStateClass;
use crate::priority_semantics::PrioritySemantics;
use crate::state_class::StateClass;
use crate::state_class_graph::{compute_successor_gated, expand_transition, initial_state_class};

/// Edge in the name-aware state class graph (a transition firing).
#[derive(Debug, Clone)]
pub(crate) struct NameEdge {
    pub from: usize,
    pub to: usize,
    pub transition_name: String,
}

pub(crate) struct NameStateClassGraph {
    pub classes: Vec<NameStateClass>,
    pub edges: Vec<NameEdge>,
    successors: Vec<Vec<usize>>,
    predecessors: Vec<Vec<usize>>,
    complete: bool,
    /// How many classes were expanded; FIFO, so exactly `0 .. expanded`
    /// ([VER-017] "Verdicts from a truncated graph").
    expanded: usize,
    /// Whether the total budget or a cancellation stopped the build ([VER-013]).
    stopped: bool,
    /// Whether the build stopped at the first class the `stop_at` predicate of
    /// [`NameStateClassGraph::build_until`] held for ([VER-012]): that class is the
    /// last one stored. Such a graph is not complete.
    stopped_at_violation: bool,
}

impl NameStateClassGraph {
    /// The whole graph, up to `max_classes`: [`NameStateClassGraph::build_until`]
    /// with no stop predicate. Route B goes through `build_until`; the tests build
    /// the unstopped graph here.
    #[cfg(test)]
    pub(crate) fn build(
        net: &PetriNet,
        initial_marking: &MarkingState,
        fragment: &NameFragment,
        max_classes: usize,
        env_places: &[&str],
        env_mode: &EnvironmentAnalysisMode,
        priority_semantics: PrioritySemantics,
    ) -> Self {
        Self::build_until(
            net,
            initial_marking,
            fragment,
            max_classes,
            env_places,
            env_mode,
            priority_semantics,
            None,
        )
    }

    /// Builds the graph up to `max_classes`, stopping at the first discovered class whose
    /// marking satisfies `stop_at` ([VER-012]: Route B's on-the-fly check of a
    /// reachability-safety property). Each class is tested as it is stored, so the
    /// classes stored up to the stop are exactly those of the unstopped build, in
    /// the same order, and the stop class is the lowest-index class the predicate
    /// holds for — the one the full graph's prefix check would pick. The edge that
    /// discovered it is recorded first, so its shortest path is the full graph's
    /// too. The stopped graph is not complete.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_until(
        net: &PetriNet,
        initial_marking: &MarkingState,
        fragment: &NameFragment,
        max_classes: usize,
        env_places: &[&str],
        env_mode: &EnvironmentAnalysisMode,
        priority_semantics: PrioritySemantics,
        stop_at: Option<&dyn Fn(&MarkingState) -> bool>,
    ) -> Self {
        env_mode.reject_arrivals(env_places.len(), "NameStateClassGraph::build");
        let env_set: HashSet<&str> = env_places.iter().copied().collect();
        // No join is enabled here: every correlated input consumes at least one token
        // ([NU-020], checked when the transition is built) and coloured places start
        // empty (the verifier guards this), so the count test alone gives the clocks.
        let base0 = initial_state_class(net, initial_marking, &env_set, env_mode, false);
        // Transitions by name, so each class resolves its enabled set in O(1) per
        // transition rather than by a scan of the net.
        let by_name: HashMap<&str, &Transition> =
            net.transitions().iter().map(|t| (t.name(), t)).collect();

        let mut graph = NameStateClassGraph {
            classes: Vec::new(),
            edges: Vec::new(),
            successors: Vec::new(),
            predecessors: Vec::new(),
            complete: true,
            expanded: 0,
            stopped: false,
            stopped_at_violation: false,
        };
        // Hash-consing (memory only, no semantic effect — [VER-012], `Interning.lean`):
        // the base layer is shared between classes at the same (marking, zone,
        // earliest-ready times) and the name layer between classes with the same
        // canonical key; a class is identified by the pair of intern ids, so no
        // per-class key string is retained. Without this a class costs kilobytes
        // (a map of maps plus a DBM) and a medium ν-net exhausts memory before it
        // closes.
        let mut base_intern: HashMap<String, (u32, Rc<StateClass>)> = HashMap::new();
        let mut name_intern: HashMap<String, (u32, Rc<NameMarking>)> = HashMap::new();
        let mut index_of: HashMap<(u32, u32), usize> = HashMap::new();
        // Coloured places start empty in the supported fragment (the verifier
        // guards this), so the initial name partition is empty.
        let (bid0, base0) = intern_base(&mut base_intern, base0);
        let (nid0, names0) =
            intern_names(&mut name_intern, NameMarking::new(), &fragment.coloured_order);
        graph.push_class(NameStateClass::new(base0, names0), (bid0, nid0), &mut index_of);
        let violates = |g: &NameStateClassGraph, idx: usize| {
            stop_at.is_some_and(|stop| stop(&g.classes[idx].base.marking))
        };
        if violates(&graph, 0) {
            graph.complete = false;
            graph.stopped_at_violation = true;
            return graph;
        }

        let mut next_sym: Sym = 0;
        let mut queue: VecDeque<usize> = VecDeque::new();
        queue.push_back(0);

        'bfs: while let Some(cur_idx) = queue.pop_front() {
            if graph.classes.len() >= max_classes {
                graph.complete = false;
                break;
            }
            // [VER-013]: the total budget ran out or the caller cancelled. Not a
            // truncation: nothing is read off this graph, not even its prefix.
            if crate::total_budget::cut() {
                graph.complete = false;
                graph.stopped = true;
                break;
            }
            let current = graph.classes[cur_idx].clone();

            // The enabled transitions of this class as objects — used by the
            // conflict-only priority prune below ([NU-052]).
            let enabled: Vec<&Transition> = current
                .base
                .enabled_transitions
                .iter()
                .map(|t_name| by_name[t_name.as_str()])
                .collect();

            for (clock_idx, t_name) in current.base.enabled_transitions.iter().enumerate() {
                let transition = enabled[clock_idx];
                let role = fragment.role(t_name);

                // NU-052: under CONFLICT semantics, skip a firing the eager,
                // priority-ordered executor would never produce — a conflicting,
                // no-later-ready, strictly-higher-priority transition that actually
                // fires takes the contested token first. `clock_idx` is L's index
                // in the enabled set (parallel to `ready_earliest`).
                if priority_semantics == PrioritySemantics::Conflict
                    && priority_dominated(
                        transition,
                        clock_idx,
                        &enabled,
                        &current.base.ready_earliest,
                        &current.base.marking,
                        &current.names,
                        fragment,
                    )
                {
                    continue;
                }

                for (_branch, outcome) in expand_transition(transition) {
                    // Name-layer steps for this firing (the join may yield 0). The base
                    // successor is computed per step: a ν-join holds a clock only while
                    // one name is present in every correlated input ([NU-020]), judged
                    // on the step's intermediate and new layers ([TIME-012]).
                    let steps =
                        name_successors(role, &current.names, &outcome.places, fragment, &mut next_sym);
                    for step in steps {
                        let between = step.intermediate.as_ref().unwrap_or(&current.names);
                        let base_succ = compute_successor_gated(
                            net,
                            &current.base,
                            clock_idx,
                            t_name,
                            &outcome,
                            &env_set,
                            env_mode,
                            false,
                            |t| name_enabled(t, between, fragment),
                            |t| name_enabled(t, &step.after, fragment),
                        );
                        if base_succ.is_empty() {
                            continue; // DBM zone infeasible
                        }
                        let (bid, shared_base) = intern_base(&mut base_intern, base_succ);
                        let (nid, shared_names) =
                            intern_names(&mut name_intern, step.after, &fragment.coloured_order);
                        let (to_idx, fresh) = if let Some(&i) = index_of.get(&(bid, nid)) {
                            (i, false)
                        } else {
                            let idx = graph.classes.len();
                            graph.push_class(
                                NameStateClass::new(shared_base, shared_names),
                                (bid, nid),
                                &mut index_of,
                            );
                            queue.push_back(idx);
                            (idx, true)
                        };
                        graph.add_edge(cur_idx, to_idx, t_name);
                        // The current class is left unexpanded (`expanded` is not
                        // advanced), so it never reads as quiescent.
                        if fresh && violates(&graph, to_idx) {
                            graph.complete = false;
                            graph.stopped_at_violation = true;
                            break 'bfs;
                        }
                    }
                }
            }
            graph.expanded += 1;
        }

        graph
    }

    fn push_class(
        &mut self,
        c: NameStateClass,
        ids: (u32, u32),
        index_of: &mut HashMap<(u32, u32), usize>,
    ) {
        let idx = self.classes.len();
        self.classes.push(c);
        self.successors.push(Vec::new());
        self.predecessors.push(Vec::new());
        index_of.insert(ids, idx);
    }

    fn add_edge(&mut self, from: usize, to: usize, t_name: &str) {
        self.edges.push(NameEdge {
            from,
            to,
            transition_name: t_name.to_string(),
        });
        self.successors[from].push(to);
        self.predecessors[to].push(from);
    }

    pub(crate) fn class_count(&self) -> usize {
        self.classes.len()
    }

    pub(crate) fn is_complete(&self) -> bool {
        self.complete
    }

    /// How many classes were expanded: `0 .. expanded_count()`, FIFO. The rest of
    /// an incomplete graph is frontier, whose successors nobody computed.
    pub(crate) fn expanded_count(&self) -> usize {
        self.expanded
    }

    /// Whether the total budget or a cancellation stopped the build ([VER-013]).
    pub(crate) fn is_stopped(&self) -> bool {
        self.stopped
    }

    /// Whether the build stopped at the first class its `stop_at` predicate held
    /// for ([`NameStateClassGraph::build_until`]); that class is the last stored.
    pub(crate) fn stopped_at_violation(&self) -> bool {
        self.stopped_at_violation
    }

    pub(crate) fn successors(&self, idx: usize) -> &[usize] {
        &self.successors[idx]
    }
}

/// Interns the base layer: one `Rc<StateClass>` per distinct (marking, zone,
/// earliest-ready times), returning its id and the shared object.
///
/// `StateClass` equality (`state_class.rs`) is marking + zone, which is all base
/// timed-reachability needs — but the [NU-052] prune (`priority_dominated`) also
/// reads `ready_earliest`, the class-relative lower bounds captured before
/// `let_time_pass`, and two arrivals at one zone can disagree on those (a
/// transition freshly enabled here versus one persistent through an unbounded
/// delay). Sharing a base across name layers is semantics-free only if the
/// shared object carries everything the successor step reads
/// (`Interning.lean`, `equivariance_is_necessary` is the witness), so the key
/// is all three, bit-exact on the doubles.
fn intern_base(
    intern: &mut HashMap<String, (u32, Rc<StateClass>)>,
    base: StateClass,
) -> (u32, Rc<StateClass>) {
    let mut key = base.canonical_key();
    key.push('#');
    for (i, r) in base.ready_earliest.iter().enumerate() {
        if i > 0 {
            key.push(',');
        }
        key.push_str(&r.to_bits().to_string());
    }
    let next = intern.len() as u32;
    let (id, shared) = intern.entry(key).or_insert_with(|| (next, Rc::new(base)));
    (*id, Rc::clone(shared))
}

/// Interns the name layer: one `Rc<NameMarking>` per canonical key, returning its
/// id and the shared object. Two layers with the same key are the same partition
/// up to a renaming of symbols, and every consumer of the layer —
/// `name_successors`, `will_fire`, the key itself — is invariant under renaming;
/// freshness stays sound because `next_sym` never revisits an id
/// (`Interning.lean`, `interned_keys_eq`).
fn intern_names(
    intern: &mut HashMap<String, (u32, Rc<NameMarking>)>,
    names: NameMarking,
    coloured_order: &[String],
) -> (u32, Rc<NameMarking>) {
    let key = names.canonical_key(coloured_order);
    let next = intern.len() as u32;
    let (id, shared) = intern.entry(key).or_insert_with(|| (next, Rc::new(names)));
    (*id, Rc::clone(shared))
}

/// The coloured output places of the fired branch (used by `Mint` to stamp a
/// fresh symbol and by `Consume` to relay the consumed symbol).
fn coloured_outputs<'a>(
    output_places: &'a HashSet<String>,
    fragment: &NameFragment,
) -> Vec<&'a String> {
    output_places
        .iter()
        .filter(|p| fragment.is_coloured(p))
        .collect()
}

/// One name-layer step of a firing: the layer once the firing has taken its
/// inputs (`None` when it takes no symbol, so the layer is the class's own) and
/// the layer once its outputs have landed. The first is the name half of the
/// intermediate marking of [TIME-012].
pub(crate) struct NameStep {
    pub intermediate: Option<NameMarking>,
    pub after: NameMarking,
}

/// Name-layer successors of one transition firing, as [`NameStep`]s. `Ordinary` passes the layer
/// through; `Mint` stamps one globally-fresh symbol into the coloured outputs of
/// this branch (one symbol into several = same-mint siblings); `Join` yields one
/// step per **distinct signature** among the enabling symbols (none ⇒ the
/// join is name-disabled), adding that symbol back once to each relay target of
/// the fired branch (EXTENDED, [NU-054]); `Consume` (EXTENDED, [NU-051]) yields one step per
/// distinct signature among the resident symbols of the single coloured input,
/// threading that symbol into every coloured output (relay) or dropping it
/// (drain). A `Join` or `Consume` step's intermediate layer is the class's layer
/// with the chosen symbol removed from the consumed places.
///
/// **Orbit dedup ([VER-012]).** A symbol's signature is its count vector over
/// `coloured_order`, as in [`NameMarking::canonical_key`]. Two symbols with equal
/// signatures are exchanged by a transposition that fixes `names`, so firing on
/// either gives successors that are renamings of each other, with equal canonical
/// keys: the class set and the set of (label, key) successor pairs are those of
/// one successor per symbol, and only parallel identical edges disappear. Each
/// signature is represented by its first symbol in id order, so the discovery
/// order is unchanged too. Emitting one per symbol copied and keyed every
/// successor only to collapse them into one class — quadratic in the class count
/// on a join-heavy graph. The number of distinct signatures, and the key each
/// one yields, are themselves invariant under renaming, which is what keeps the
/// step key-equivariant (`Interning.lean`, `Equivariant`). The intermediate
/// layers are renamed with the successors, and [`name_enabled`] reads only
/// whether some symbol enables a join, so the clocks they decide are invariant too.
fn name_successors(
    role: &Role,
    names: &NameMarking,
    output_places: &HashSet<String>,
    fragment: &NameFragment,
    next_sym: &mut Sym,
) -> Vec<NameStep> {
    match role {
        Role::Ordinary => vec![NameStep {
            intermediate: None,
            after: names.clone(),
        }],
        Role::Mint => {
            let coloured_out = coloured_outputs(output_places, fragment);
            let mut nm = names.clone();
            if !coloured_out.is_empty() {
                let fresh = *next_sym;
                *next_sym += 1;
                for p in coloured_out {
                    nm.add(p, fresh, 1);
                }
            }
            vec![NameStep {
                intermediate: None,
                after: nm,
            }]
        }
        Role::Join {
            coloured_in,
            relay_to,
        } => {
            // [NU-054]: the relay targets of the fired branch. Relaying adds back
            // the symbol the join removed, so the step mints nothing and stays
            // equivariant under renaming: the orbit dedup reads signatures on the
            // pre-step layer, and a transposition of two equal-signature symbols
            // fixes that layer and maps one successor onto the other — equal keys,
            // as for a drain.
            let relays: Vec<&String> = if relay_to.is_empty() {
                Vec::new()
            } else {
                output_places.iter().filter(|p| relay_to.contains(*p)).collect()
            };
            distinct_signatures(names, enabling_symbols(names, coloured_in), fragment)
                .into_iter()
                .map(|s| {
                    let mut between = names.clone();
                    for (p, req) in coloured_in {
                        between.remove(p, s, *req);
                    }
                    let mut after = between.clone();
                    for p in &relays {
                        after.add(p, s, 1);
                    }
                    NameStep {
                        intermediate: Some(between),
                        after,
                    }
                })
                .collect()
        }
        Role::Consume { input_place } => {
            let coloured_out = coloured_outputs(output_places, fragment);
            // The consumed count is fixed at 1, so EVERY resident symbol (each
            // present at count ≥ 1) enables a firing — none is dropped, so no
            // base-enabled firing vanishes (Blocker 2). Each coloured output
            // receives EXACTLY ONE symbol, matching the base marking's single
            // token per output place (Blocker 1).
            distinct_signatures(names, names.symbols_in(input_place), fragment)
                .into_iter()
                .map(|s| {
                    let mut between = names.clone();
                    between.remove(input_place, s, 1);
                    let mut after = between.clone();
                    for p in &coloured_out {
                        after.add(p, s, 1);
                    }
                    NameStep {
                        intermediate: Some(between),
                        after,
                    }
                })
                .collect()
        }
    }
}

/// Whether `t` is enabled by the name layer `names`, given that the count
/// marking enables it: a ν-join needs one symbol present at the required
/// multiplicity in every correlated input ([NU-020]); every other role is
/// enabled by counts alone (a consumer's input count is its symbol count).
fn name_enabled(t: &Transition, names: &NameMarking, fragment: &NameFragment) -> bool {
    match fragment.role(t.name()) {
        Role::Join { coloured_in, .. } => !enabling_symbols(names, coloured_in).is_empty(),
        Role::Consume { .. } | Role::Ordinary | Role::Mint => true,
    }
}

/// One representative per distinct signature among `symbols` — the first, in the
/// given (ascending id) order: the orbit dedup of [`name_successors`]. A
/// symbol's signature is its count vector over the coloured places, the vector
/// [`NameMarking::canonical_key`] ranks symbols by.
fn distinct_signatures(names: &NameMarking, symbols: Vec<Sym>, fragment: &NameFragment) -> Vec<Sym> {
    if symbols.len() < 2 {
        return symbols;
    }
    let mut seen: HashSet<Vec<usize>> = HashSet::with_capacity(symbols.len());
    symbols
        .into_iter()
        .filter(|&s| {
            seen.insert(
                fragment
                    .coloured_order
                    .iter()
                    .map(|p| names.count_of(p, s))
                    .collect(),
            )
        })
        .collect()
}

/// Symbols that enable a join: present at the required multiplicity in EVERY
/// correlated input. The exactness core of [NU-050] — a count-only check would
/// (wrongly) fire on two distinct names.
fn enabling_symbols(names: &NameMarking, coloured_in: &[(String, usize)]) -> Vec<Sym> {
    let Some(((first_place, first_req), rest)) = coloured_in.split_first() else {
        return Vec::new();
    };
    names
        .symbols_in(first_place)
        .into_iter()
        .filter(|&s| {
            names.count_of(first_place, s) >= *first_req
                && rest.iter().all(|(p, req)| names.count_of(p, s) >= *req)
        })
        .collect()
}

/// True if firing `l` is pre-empted by conflict-only priority ([NU-052]): some
/// other enabled transition `h` has strictly higher priority, shares a consumed
/// input place with `l` **under real competition**, becomes ready no later than
/// `l`, and actually fires in this class (produces a name-successor). The
/// executor fires ready transitions in descending priority order within a pass,
/// so `h` takes the contested token and `l` cannot fire — the pruned firing is
/// not runtime-reachable.
///
/// **Readiness (DBM residual-earliest).** The name-SCG carries a DBM, so a static
/// `h.earliest() <= l.earliest()` does NOT entail "H ready no later than L":
/// their class-relative enabling epochs can put H's clock behind L's. We compare
/// the *class-relative* earliest-ready times captured on the base class
/// (`ready_earliest`, the DBM lower bounds before `let_time_pass`): H pre-empts L
/// only when `ready_earliest[H] <= ready_earliest[L] + EPS`. This is fully
/// precise on the zone off-diagonal and subsumes the previously-shipped
/// `earliest() == 0` special case (an immediate H has `ready_earliest[H] = 0 <=
/// ready_earliest[L]`), so no capability is lost on the immediate-H idiom.
///
/// **Real competition (multiplicity).** Sharing a consumed place name is not
/// enough: if the place holds enough tokens to satisfy H and L at once they do
/// not compete, and pruning L would be unsound. `shares_consumed_input` therefore
/// requires some shared consumed place `p` with `count(p) < demand_H(p) +
/// demand_L(p)` in the class marking.
///
/// The `will_fire` guard is essential on a ν-net: a match (join) transition can
/// be base-enabled yet **name-disabled** (its inputs carry no shared name). Such
/// a join never consumes the contested token, so it must not pre-empt a
/// conflicting drain — otherwise a genuine straggler would strand.
///
/// **In flight ([VER-004]).** On a net the verifier split, `h` pre-empts nothing
/// while its place `inflight:<h>` is marked: its action is still running, and the
/// Java and TypeScript executors do not start `h` again then, so `l` fires. The
/// verifier splits every pruner for this ([`crate::in_flight::conflict_demand`]); on
/// a net with no such place the guard never applies.
fn priority_dominated(
    l: &Transition,
    idx_l: usize,
    enabled: &[&Transition],
    ready_earliest: &[f64],
    marking: &MarkingState,
    names: &NameMarking,
    fragment: &NameFragment,
) -> bool {
    /// Float slack for the class-relative earliest-ready comparison (matches the
    /// DBM's own `EPSILON`).
    const EPS: f64 = 1e-9;
    enabled.iter().enumerate().any(|(idx_h, &h)| {
        h.name() != l.name()
            && h.priority() > l.priority()
            && ready_earliest[idx_h] <= ready_earliest[idx_l] + EPS
            && marking.count(&crate::in_flight::in_flight_place(h.name())) == 0
            && will_fire(h, names, fragment)
            && shares_consumed_input(h, l, marking)
    })
}

/// True if base-enabled `h` actually produces a name-successor from this class —
/// a join finds a shared enabling name and a consumer finds a resident symbol.
/// `Ordinary` and `Mint` always fire; only a name-disabled join (or an
/// empty-input consumer) does not, and such a transition must not pre-empt a
/// conflicting firing.
fn will_fire(h: &Transition, names: &NameMarking, fragment: &NameFragment) -> bool {
    match fragment.role(h.name()) {
        Role::Join { coloured_in, .. } => !enabling_symbols(names, coloured_in).is_empty(),
        Role::Consume { input_place } => !names.symbols_in(input_place).is_empty(),
        // Explicit (not `_`) so a future Role variant forces a compile-time
        // decision here rather than silently defaulting to will-fire=true.
        Role::Ordinary | Role::Mint => true,
    }
}

/// True if `h` and `l` genuinely compete for a consumed token — they share a
/// consumed input place `p` whose token count in `marking` cannot satisfy both
/// demands at once (`count(p) < demand_h(p) + demand_l(p)`). Read and inhibitor
/// arcs are excluded ([`Transition::input_places`] is consumed inputs only),
/// since they do not remove a token another transition competes for.
///
/// The multiplicity clause is a soundness guard for the [NU-052] prune: if the
/// shared place holds enough tokens for both, `h` does NOT rob `l`, so pruning
/// `l` would drop a runtime-reachable firing.
fn shares_consumed_input(h: &Transition, l: &Transition, marking: &MarkingState) -> bool {
    let l_ins = l.input_places();
    h.input_places().iter().any(|p| {
        l_ins.contains(p) && {
            let name = p.name();
            marking.count(name) < consumed_demand(h, name) + consumed_demand(l, name)
        }
    })
}

/// Tokens `t` consumes from `place` on one firing (summed across its input specs
/// referencing that place — normally a single spec). Uses the enablement
/// `required_count` so `In::All`/`In::AtLeast` demand their minimum, matching the
/// base SCG's consumption model.
fn consumed_demand(t: &Transition, place: &str) -> usize {
    t.input_specs()
        .iter()
        .filter(|spec| spec.place_name() == place)
        .map(libpetri_core::input::required_count)
        .sum()
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use libpetri_core::action::fork;
    use std::collections::BTreeSet;

    /// [VER-012] interning regression fixture (`Interning.lean`,
    /// `equivariance_is_necessary`): two routes to one (marking, zone) that
    /// disagree on `ready_earliest` under different name layers. `MC` co-mints one
    /// name into `C1`, `C2` and enables `H` fresh (ready in 5 s); `M1` then `M2`
    /// mint two names and leave `H` persistent through `M2`'s unbounded delay
    /// (ready now). `H` (priority 10) and `L` (priority 0) compete for `Q`. `J` is
    /// gated on the never-marked `R` so the meeting class enables exactly `H` and
    /// `L`, both fresh at the point each route enables them, and the two zones
    /// agree constraint for constraint.
    fn interning_fixture(with_drain: bool) -> PetriNet {
        use libpetri_core::input::{exactly, one};
        use libpetri_core::match_spec::MatchSpec;
        use libpetri_core::name::NameId;
        use libpetri_core::output::{and, out_place};
        use libpetri_core::place::Place;
        use libpetri_core::timing;
        use libpetri_core::transition::Transition;

        let p = Place::<String>::new("P");
        let c1 = Place::<String>::new("C1");
        let c2 = Place::<String>::new("C2");
        let q = Place::<String>::new("Q");
        let out = Place::<String>::new("OUT");
        let out_h = Place::<String>::new("OUT_H");
        let dead = Place::<String>::new("DEAD");
        let drained = Place::<String>::new("DRAINED");
        // Never marked: keeps `J` structurally a ν-join without ever enabling it.
        let r = Place::<String>::new("R");

        let mc = Transition::builder("MC")
            .input(exactly(2, &p))
            .output(and(vec![out_place(&c1), out_place(&c2), out_place(&q)]))
            .action(fork())
            .build();
        let m1 = Transition::builder("M1")
            .input(one(&p))
            .output(and(vec![out_place(&c1), out_place(&q)]))
            .action(fork())
            .build();
        let m2 = Transition::builder("M2")
            .input(one(&p))
            .timing(timing::delayed(3_000))
            .output(out_place(&c2))
            .action(fork())
            .build();
        let h = Transition::builder("H")
            .input(one(&q))
            .timing(timing::delayed(5_000))
            .priority(10)
            .output(out_place(&out_h))
            .action(fork())
            .build();
        let l = Transition::builder("L")
            .input(one(&q))
            .output(out_place(&dead))
            .action(fork())
            .build();
        let j = Transition::builder("J")
            .input(one(&c1))
            .input(one(&c2))
            .input(one(&r))
            .match_spec(
                MatchSpec::builder()
                    .key(&c1, |s: &String| NameId::new(s.clone()))
                    .key(&c2, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&out))
            .action(fork())
            .build();
        let mut transitions = vec![mc, m1, m2, h, l, j];
        if with_drain {
            transitions.push(
                Transition::builder("D")
                    .input(one(&c1))
                    .output(out_place(&drained))
                    .action(fork())
                    .build(),
            );
        }
        PetriNet::builder("interning").transitions(transitions).build()
    }

    fn edge_target(graph: &NameStateClassGraph, from: usize, name: &str) -> usize {
        graph
            .edges
            .iter()
            .find(|e| e.from == from && e.transition_name == name)
            .map(|e| e.to)
            .unwrap_or_else(|| panic!("no edge {name} out of class {from}"))
    }

    fn has_edge(graph: &NameStateClassGraph, from: usize, name: &str) -> bool {
        graph.edges.iter().any(|e| e.from == from && e.transition_name == name)
    }

    #[test]
    fn interned_base_keeps_each_arrivals_ready_earliest() {
        use crate::marking_state::MarkingStateBuilder;
        use crate::name_fragment::{classify, FragmentMode};
        use std::collections::BTreeSet;

        let net = interning_fixture(false);
        let fragment = classify(&net, FragmentMode::Base, &BTreeSet::new(), &crate::name_fragment::all_mints(&net))
            .expect("the interning fixture is in the base fragment");
        let initial = MarkingStateBuilder::new().tokens("P", 2).build();
        let graph = NameStateClassGraph::build(
            &net,
            &initial,
            &fragment,
            10_000,
            &[],
            &EnvironmentAnalysisMode::Ignore,
            PrioritySemantics::Conflict,
        );

        let same = edge_target(&graph, 0, "MC"); // one name in C1 and C2
        let mid = edge_target(&graph, 0, "M1");
        let diff = edge_target(&graph, mid, "M2"); // two names
        assert_ne!(same, diff, "different name partitions are different classes");
        assert_eq!(
            graph.classes[same].base.marking, graph.classes[diff].base.marking,
            "same base marking"
        );
        assert!(
            has_edge(&graph, same, "L"),
            "H is freshly enabled here (ready in 5 s), so L is not pre-empted"
        );
        assert!(
            !has_edge(&graph, diff, "L"),
            "H has been enabled since M1 and may be ready now, so L is pre-empted: an interned \
             base must not hand this class the other arrival's ready_earliest"
        );
        assert!(
            !Rc::ptr_eq(&graph.classes[same].base, &graph.classes[diff].base),
            "the two arrivals disagree on ready_earliest, so they must not share a base"
        );
    }

    /// The same two arrivals, reaching one name layer: `MC` and `M1` each co-mint one
    /// name into `C1` and `C2`, and the uncoloured `B` balances the marking so both
    /// routes meet at `C1 + C2 + B + Q`. `MC` enables `H` fresh (ready in 5 s); `M1`
    /// then the 3 s `M2` leaves `H` persistent (ready now). Class identity therefore has
    /// to carry `ready_earliest` itself: sharing the base object is not enough when the
    /// name layers coincide.
    fn same_name_layer_fixture() -> PetriNet {
        use libpetri_core::input::{exactly, one};
        use libpetri_core::match_spec::MatchSpec;
        use libpetri_core::name::NameId;
        use libpetri_core::output::{and, out_place};
        use libpetri_core::place::Place;
        use libpetri_core::timing;
        use libpetri_core::transition::Transition;

        let p = Place::<String>::new("P");
        let c1 = Place::<String>::new("C1");
        let c2 = Place::<String>::new("C2");
        let b = Place::<String>::new("B");
        let q = Place::<String>::new("Q");
        let out = Place::<String>::new("OUT");
        let out_h = Place::<String>::new("OUT_H");
        let dead = Place::<String>::new("DEAD");
        let r = Place::<String>::new("R");

        let mc = Transition::builder("MC")
            .input(exactly(2, &p))
            .output(and(vec![out_place(&c1), out_place(&c2), out_place(&b), out_place(&q)]))
            .action(fork())
            .build();
        let m1 = Transition::builder("M1")
            .input(one(&p))
            .output(and(vec![out_place(&c1), out_place(&c2), out_place(&q)]))
            .action(fork())
            .build();
        let m2 = Transition::builder("M2")
            .input(one(&p))
            .timing(timing::delayed(3_000))
            .output(out_place(&b))
            .action(fork())
            .build();
        let h = Transition::builder("H")
            .input(one(&q))
            .timing(timing::delayed(5_000))
            .priority(10)
            .output(out_place(&out_h))
            .action(fork())
            .build();
        let l = Transition::builder("L")
            .input(one(&q))
            .output(out_place(&dead))
            .action(fork())
            .build();
        let j = Transition::builder("J")
            .input(one(&c1))
            .input(one(&c2))
            .input(one(&r))
            .match_spec(
                MatchSpec::builder()
                    .key(&c1, |s: &String| NameId::new(s.clone()))
                    .key(&c2, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&out))
            .action(fork())
            .build();
        PetriNet::builder("interning-same-layer")
            .transitions(vec![mc, m1, m2, h, l, j])
            .build()
    }

    #[test]
    fn class_identity_carries_ready_earliest_when_name_layers_coincide() {
        use crate::marking_state::MarkingStateBuilder;
        use crate::name_fragment::{classify, FragmentMode};
        use std::collections::BTreeSet;

        let net = same_name_layer_fixture();
        let fragment = classify(&net, FragmentMode::Base, &BTreeSet::new(), &crate::name_fragment::all_mints(&net))
            .expect("the fixture is in the base fragment");
        let initial = MarkingStateBuilder::new().tokens("P", 2).build();
        let graph = NameStateClassGraph::build(
            &net,
            &initial,
            &fragment,
            10_000,
            &[],
            &EnvironmentAnalysisMode::Ignore,
            PrioritySemantics::Conflict,
        );

        let fresh = edge_target(&graph, 0, "MC"); // H enabled here, ready in 5 s
        let mid = edge_target(&graph, 0, "M1");
        let persistent = edge_target(&graph, mid, "M2"); // H enabled since M1, may be ready now

        assert_eq!(
            graph.classes[fresh].names.canonical_key(&fragment.coloured_order),
            graph.classes[persistent].names.canonical_key(&fragment.coloured_order),
            "both routes co-mint one name into C1 and C2, so the layers are the same partition"
        );
        assert_eq!(
            graph.classes[fresh].base.marking, graph.classes[persistent].base.marking,
            "same base marking"
        );
        assert_ne!(
            fresh, persistent,
            "the arrivals disagree on ready_earliest, so they are two classes: dedup on \
             (marking, zone, name key) alone would hand one arrival the other's prune input"
        );
        assert!(
            has_edge(&graph, fresh, "L"),
            "H is freshly enabled here (ready in 5 s), so L is not pre-empted"
        );
        assert!(
            !has_edge(&graph, persistent, "L"),
            "H may be ready now, so L is pre-empted (NU-052)"
        );
    }

    fn rename(nm: &NameMarking, places: &[&str], sigma: impl Fn(Sym) -> Sym) -> NameMarking {
        let mut out = NameMarking::new();
        for p in places {
            for s in nm.symbols_in(p) {
                out.add(p, sigma(s), nm.count_of(p, s));
            }
        }
        out
    }

    fn successor_keys(
        fragment: &NameFragment,
        transition: &str,
        names: &NameMarking,
        outputs: &HashSet<String>,
        mut fresh: Sym,
    ) -> Vec<String> {
        let mut keys: Vec<String> =
            name_successors(fragment.role(transition), names, outputs, fragment, &mut fresh)
                .iter()
                .map(|step| step.after.canonical_key(&fragment.coloured_order))
                .collect();
        keys.sort();
        keys
    }

    /// The hypothesis `Interning.lean` rests on: `name_successors` is equivariant
    /// under a renaming of symbols — a renamed layer (same canonical key) has
    /// successors with the same canonical keys, for every role, given fresh
    /// counters.
    #[test]
    fn name_successors_is_key_equivariant() {
        use crate::name_fragment::{classify, FragmentMode};
        use std::collections::BTreeSet;

        let net = interning_fixture(true);
        let fragment = classify(&net, FragmentMode::Extended, &BTreeSet::new(), &crate::name_fragment::all_mints(&net))
            .expect("the drain is an EXTENDED coloured consumer");
        let mut names = NameMarking::new();
        names.add("C1", 3, 1);
        names.add("C2", 3, 1);
        names.add("C2", 7, 1);
        let renamed = rename(&names, &["C1", "C2"], |s| match s {
            3 => 11,
            7 => 2,
            s => s,
        });
        assert_eq!(
            names.canonical_key(&fragment.coloured_order),
            renamed.canonical_key(&fragment.coloured_order)
        );

        let outputs: HashSet<String> = ["C1", "C2", "Q"].iter().map(|s| s.to_string()).collect();
        for t in ["MC", "J", "H", "D"] {
            assert_eq!(
                successor_keys(&fragment, t, &names, &outputs, 8),
                successor_keys(&fragment, t, &renamed, &outputs, 12),
                "{t}"
            );
        }
    }

    #[test]
    fn enabling_requires_shared_symbol() {
        // Counts allow (one symbol in each branch) but the symbols differ → the
        // join is NOT enabled (the over-approximation bug this route fixes).
        let mut split = NameMarking::new();
        split.add("branchA", 0, 1);
        split.add("branchB", 1, 1);
        let coloured_in = vec![("branchA".to_string(), 1), ("branchB".to_string(), 1)];
        assert!(enabling_symbols(&split, &coloured_in).is_empty());

        // Same symbol in both → enabled on that symbol.
        let mut shared = NameMarking::new();
        shared.add("branchA", 5, 1);
        shared.add("branchB", 5, 1);
        assert_eq!(enabling_symbols(&shared, &coloured_in), vec![5]);
    }

    #[test]
    fn enabling_respects_multiplicity() {
        // Join needs 2 of the matched name in branchA but only 1 is present.
        let mut nm = NameMarking::new();
        nm.add("branchA", 0, 1);
        nm.add("branchB", 0, 1);
        let coloured_in = vec![("branchA".to_string(), 2), ("branchB".to_string(), 1)];
        assert!(enabling_symbols(&nm, &coloured_in).is_empty());

        nm.add("branchA", 0, 1); // now 2 of symbol 0 in branchA
        assert_eq!(enabling_symbols(&nm, &coloured_in), vec![0]);
    }

    /// [NU-052] multiplicity guard: two transitions sharing a consumed place
    /// compete only when the place cannot satisfy both demands at once.
    #[test]
    fn multiplicity_two_tokens_is_not_competition() {
        use crate::marking_state::MarkingStateBuilder;
        use libpetri_core::input::one;
        use libpetri_core::output::out_place;
        use libpetri_core::place::Place;
        use libpetri_core::transition::Transition;

        let p = Place::<i32>::new("P");
        let out_h = Place::<i32>::new("OUT_H");
        let out_l = Place::<i32>::new("OUT_L");
        let h = Transition::builder("H")
            .input(one(&p))
            .output(out_place(&out_h))
            .action(fork())
            .build();
        let l = Transition::builder("L")
            .input(one(&p))
            .output(out_place(&out_l))
            .action(fork())
            .build();

        // One shared token: H and L genuinely compete (1 < 1 + 1).
        let one_tok = MarkingStateBuilder::new().tokens("P", 1).build();
        assert!(shares_consumed_input(&h, &l, &one_tok));

        // Two shared tokens: both demands satisfiable at once → NOT competition,
        // so the [NU-052] prune must not fire.
        let two_tok = MarkingStateBuilder::new().tokens("P", 2).build();
        assert!(!shares_consumed_input(&h, &l, &two_tok));
    }

    /// [NU-052] criterion 4: a READ or INHIBITOR arc on the shared place is not a
    /// consumption conflict, so it must not drive the CONFLICT prune.
    /// `shares_consumed_input` looks only at consumed inputs
    /// ([`Transition::input_places`]), so an H that merely reads/inhibits `P`
    /// while L consumes `P` do NOT compete — even with a single token present.
    #[test]
    fn read_or_inhibitor_arc_is_not_a_consumption_conflict() {
        use crate::marking_state::MarkingStateBuilder;
        use libpetri_core::arc::{inhibitor, read};
        use libpetri_core::input::one;
        use libpetri_core::output::out_place;
        use libpetri_core::place::Place;
        use libpetri_core::transition::Transition;

        let p = Place::<i32>::new("P");
        let out_h = Place::<i32>::new("OUT_H");
        let out_l = Place::<i32>::new("OUT_L");

        // L consumes the single token in P.
        let l = Transition::builder("L")
            .input(one(&p))
            .output(out_place(&out_l))
            .action(fork())
            .build();

        // One token present — if H *consumed* P this would be a genuine conflict.
        let one_tok = MarkingStateBuilder::new().tokens("P", 1).build();

        // H merely READS P (tests presence, consumes nothing) → no conflict.
        let h_read = Transition::builder("H_READ")
            .read(read(&p))
            .output(out_place(&out_h))
            .action(fork())
            .build();
        assert!(
            !shares_consumed_input(&h_read, &l, &one_tok),
            "a read arc on the shared place is not a consumption conflict"
        );

        // H merely INHIBITS on P (blocks when present) → no conflict either.
        let h_inh = Transition::builder("H_INH")
            .inhibitor(inhibitor(&p))
            .output(out_place(&out_h))
            .action(fork())
            .build();
        assert!(
            !shares_consumed_input(&h_inh, &l, &one_tok),
            "an inhibitor arc on the shared place is not a consumption conflict"
        );

        // Sanity: a genuine consume on P with a single token IS a conflict.
        let h_consume = Transition::builder("H_CONS")
            .input(one(&p))
            .output(out_place(&out_h))
            .action(fork())
            .build();
        assert!(
            shares_consumed_input(&h_consume, &l, &one_tok),
            "a genuine consume on the shared place IS a consumption conflict"
        );
    }

    /// [NU-052] residual-earliest: a DELAYED higher-priority join (delayed 100)
    /// pre-empts a DELAYED lower-priority drain (delayed 200) they conflict with —
    /// a case the old `earliest() == 0` guard could not prune. Differential:
    /// NONE reaches DEADLETTER (drain explored), CONFLICT does not (drain pruned).
    #[test]
    fn delayed_conflict_prunes_lower_priority() {
        use crate::marking_state::MarkingStateBuilder;
        use crate::name_fragment::{FragmentMode, classify};
        use libpetri_core::input::one;
        use libpetri_core::match_spec::MatchSpec;
        use libpetri_core::name::NameId;
        use libpetri_core::output::{and, out_place};
        use libpetri_core::place::Place;
        use libpetri_core::timing;
        use libpetri_core::transition::Transition;
        use std::collections::BTreeSet;

        let seed = Place::<()>::new("SEED");
        let a = Place::<String>::new("COL_A");
        let b = Place::<String>::new("COL_B");
        let out = Place::<String>::new("OUT");
        let dl = Place::<String>::new("DEADLETTER");

        let mint = Transition::builder("MINT")
            .input(one(&seed))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .action(fork())
            .build();
        let join = Transition::builder("JOIN") // delayed 100, default priority
            .input(one(&a))
            .input(one(&b))
            .timing(timing::delayed(100))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&out))
            .action(fork())
            .build();
        let drain = Transition::builder("DRAIN_A") // delayed 200, lower priority
            .input(one(&a))
            .timing(timing::delayed(200))
            .priority(-10)
            .output(out_place(&dl))
            .action(fork())
            .build();
        let net = PetriNet::builder("delayedPriorityFixture")
            .transitions([mint, join, drain])
            .build();

        let fragment = classify(&net, FragmentMode::Extended, &BTreeSet::new(), &crate::name_fragment::all_mints(&net))
            .expect("EXTENDED must admit the delayed priority fixture");
        let initial = MarkingStateBuilder::new().tokens("SEED", 1).build();

        let reaches_deadletter = |ps: PrioritySemantics| {
            let graph = NameStateClassGraph::build(
                &net,
                &initial,
                &fragment,
                10_000,
                &[],
                &EnvironmentAnalysisMode::Ignore,
                ps,
            );
            graph
                .classes
                .iter()
                .any(|c| c.base.marking.count("DEADLETTER") > 0)
        };

        assert!(
            reaches_deadletter(PrioritySemantics::None),
            "NONE must explore the drain and reach DEADLETTER"
        );
        assert!(
            !reaches_deadletter(PrioritySemantics::Conflict),
            "CONFLICT must prune the DELAYED lower-priority drain (residual-earliest)"
        );
    }

    /// PNID Fig. 11(b) (`research/net-metrics/validation/pnid/src/nets.ts`,
    /// `res11b`): `create_order` reads a clerk and co-mints one name into `order`
    /// and `order_clerk`; `send_order` joins them by name. Minting is unbounded, so
    /// the graph never closes, and every live name has the same signature: the
    /// join-heavy shape the orbit dedup of [VER-012] exists for.
    pub(crate) fn fig11b() -> (PetriNet, crate::marking_state::MarkingState) {
        use crate::marking_state::MarkingStateBuilder;
        use libpetri_core::arc::read;
        use libpetri_core::input::one;
        use libpetri_core::match_spec::MatchSpec;
        use libpetri_core::name::NameId;
        use libpetri_core::output::{and, out_place};
        use libpetri_core::place::Place;
        use libpetri_core::transition::Transition;

        let clerk = Place::<()>::new("clerk");
        let order = Place::<String>::new("order");
        let order_clerk = Place::<String>::new("order_clerk");
        let done = Place::<String>::new("send_done");
        let create = Transition::builder("create_order")
            .read(read(&clerk))
            .output(and(vec![out_place(&order), out_place(&order_clerk)]))
            .action(fork())
            .build();
        let send = Transition::builder("send_order")
            .input(one(&order))
            .input(one(&order_clerk))
            .match_spec(
                MatchSpec::builder()
                    .key(&order, |s: &String| NameId::new(s.clone()))
                    .key(&order_clerk, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&done))
            .action(fork())
            .build();
        let net = PetriNet::builder("P-Fig11b-not-exclusive")
            .transitions(vec![create, send])
            .build();
        (net, MarkingStateBuilder::new().tokens("clerk", 2).build())
    }

    fn fig11b_graph(max_classes: usize) -> (NameStateClassGraph, NameFragment) {
        use crate::name_fragment::{FragmentMode, classify};
        use std::collections::BTreeSet;

        let (net, m0) = fig11b();
        let fragment = classify(&net, FragmentMode::Base, &BTreeSet::new(), &crate::name_fragment::all_mints(&net))
            .expect("Fig. 11(b) is in the base fragment");
        let graph = NameStateClassGraph::build(
            &net,
            &m0,
            &fragment,
            max_classes,
            &[],
            &EnvironmentAnalysisMode::Ignore,
            PrioritySemantics::None,
        );
        (graph, fragment)
    }

    /// Per-symbol emission, as `name_successors` did before the orbit dedup: one
    /// successor per enabling symbol of a join.
    fn per_symbol_join_keys(
        fragment: &NameFragment,
        transition: &str,
        names: &NameMarking,
    ) -> BTreeSet<String> {
        let Role::Join { coloured_in, .. } = fragment.role(transition) else {
            panic!("{transition} is not a join");
        };
        enabling_symbols(names, coloured_in)
            .into_iter()
            .map(|s| {
                let mut nm = names.clone();
                for (p, req) in coloured_in {
                    nm.remove(p, s, *req);
                }
                nm.canonical_key(&fragment.coloured_order)
            })
            .collect()
    }

    /// [VER-012] orbit dedup: one successor per distinct signature, whose keys are
    /// exactly the keys of the per-symbol emission — same set, fewer duplicates.
    #[test]
    fn orbit_dedup_keeps_the_successor_key_set_of_per_symbol_emission() {
        let (_, fragment) = fig11b_graph(1);
        let outputs: HashSet<String> = ["send_done"].iter().map(|s| s.to_string()).collect();
        let dedup = |names: &NameMarking| {
            let mut fresh: Sym = 100;
            name_successors(fragment.role("send_order"), names, &outputs, &fragment, &mut fresh)
                .iter()
                .map(|step| step.after.canonical_key(&fragment.coloured_order))
                .collect::<Vec<_>>()
        };

        // Three live names with one signature, plus one that does not enable.
        let mut same = NameMarking::new();
        for s in [0, 1, 2] {
            same.add("order", s, 1);
            same.add("order_clerk", s, 1);
        }
        same.add("order", 3, 1);
        let keys = dedup(&same);
        assert_eq!(keys.len(), 1, "three interchangeable names are one orbit");
        assert_eq!(
            keys.iter().cloned().collect::<BTreeSet<_>>(),
            per_symbol_join_keys(&fragment, "send_order", &same)
        );

        // Two enabling names with different signatures stay two successors.
        let mut split = NameMarking::new();
        split.add("order", 0, 2);
        split.add("order_clerk", 0, 1);
        split.add("order", 1, 1);
        split.add("order_clerk", 1, 1);
        let keys = dedup(&split);
        assert_eq!(keys.len(), 2);
        assert_eq!(
            keys.iter().cloned().collect::<BTreeSet<_>>(),
            per_symbol_join_keys(&fragment, "send_order", &split)
        );
    }

    /// The same equality over every class of an explored Fig. 11(b) graph: at each
    /// class the join's deduplicated successors have exactly the keys of the
    /// per-symbol emission, and at most one successor per key.
    #[test]
    fn orbit_dedup_agrees_with_per_symbol_emission_on_every_explored_class() {
        let (graph, fragment) = fig11b_graph(300);
        let outputs: HashSet<String> = ["send_done"].iter().map(|s| s.to_string()).collect();
        let mut joins_with_duplicates = 0;
        for class in &graph.classes {
            let reference = per_symbol_join_keys(&fragment, "send_order", &class.names);
            let mut fresh: Sym = 1_000_000;
            let keys: Vec<String> = name_successors(
                fragment.role("send_order"),
                &class.names,
                &outputs,
                &fragment,
                &mut fresh,
            )
            .iter()
            .map(|step| step.after.canonical_key(&fragment.coloured_order))
            .collect();
            let distinct: BTreeSet<String> = keys.iter().cloned().collect();
            assert_eq!(distinct.len(), keys.len(), "one successor per key");
            assert_eq!(distinct, reference);
            if enabling_symbols(&class.names, &[
                ("order".to_string(), 1),
                ("order_clerk".to_string(), 1),
            ])
            .len()
                > keys.len()
            {
                joins_with_duplicates += 1;
            }
        }
        assert!(joins_with_duplicates > 0, "the fixture exercises the dedup");
    }

    /// Class counts of Fig. 11(b) at several caps, and the edge multiset the
    /// dedup removes: the graph is the per-symbol graph with parallel identical
    /// edges collapsed. The counts were recorded with per-symbol emission.
    #[test]
    fn orbit_dedup_leaves_the_fig11b_class_counts_unchanged() {
        for (cap, classes) in FIG11B_CLASS_COUNTS {
            let (graph, _) = fig11b_graph(cap);
            assert!(!graph.is_complete());
            assert_eq!(graph.class_count(), classes, "cap {cap}");
            let mut edges: Vec<(usize, usize, &str)> = graph
                .edges
                .iter()
                .map(|e| (e.from, e.to, e.transition_name.as_str()))
                .collect();
            let n = edges.len();
            edges.sort_unstable();
            edges.dedup();
            assert_eq!(edges.len(), n, "no parallel identical edges remain (cap {cap})");
        }
    }

    /// Recorded with the per-symbol emission (before the orbit dedup).
    const FIG11B_CLASS_COUNTS: [(usize, usize); 3] = [(50, 51), (300, 300), (2_000, 2_000)];

    /// [VER-012]: an 8 000-class build of Fig. 11(b) finishes under a generous
    /// bound. Per-symbol emission is roughly quadratic in the class count here.
    #[test]
    fn fig11b_8k_class_build_is_fast() {
        let started = std::time::Instant::now();
        let (graph, _) = fig11b_graph(8_000);
        let took = started.elapsed();
        assert!(graph.class_count() >= 8_000);
        assert!(took.as_secs() < 20, "8k-class Fig. 11(b) build took {took:?}");
    }

    /// Timing of 2k / 4k / 8k-class Fig. 11(b) builds, for the record:
    /// `cargo test --release -p libpetri-verification fig11b_build_timings -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn fig11b_build_timings() {
        for cap in [2_000, 4_000, 8_000] {
            let mut runs: Vec<std::time::Duration> = (0..3)
                .map(|_| {
                    let started = std::time::Instant::now();
                    let (graph, _) = fig11b_graph(cap);
                    let took = started.elapsed();
                    assert!(graph.class_count() >= cap);
                    took
                })
                .collect();
            runs.sort();
            println!("fig11b cap={cap}: median {:?} (runs {runs:?})", runs[1]);
        }
    }

    // ---- NU-054: the relay step and the orbit dedup ----

    /// The dedup emits one successor per distinct PRE-step signature. A relay step
    /// removes `s` from the keys and adds it back to the relay targets, so a
    /// transposition of two symbols with equal pre-step signatures fixes the layer
    /// and maps one successor onto the other: equal keys. Checked on every
    /// reachable class: the keys the step emits equal the keys a per-symbol step
    /// (no dedup) produces, one successor per key.
    #[test]
    fn relay_step_dedup_covers_every_per_symbol_successor() {
        use crate::name_fragment::{FragmentMode, classify};
        use crate::relay_nets::{FIG_12C_CARRIERS, fig_12c, j, n1_corr, pnid_net, t};

        let beside_carrier = vec![
            t("m", &["S"], &["A", "B", "E"]),
            t("t", &["E"], &[]),
            j("j", &["A", "B"], &["C"], &["A", "B"], &["C"]),
            t("k", &["C"], &["done"]),
        ];
        let cases: Vec<(&str, Vec<crate::relay_nets::Row>, (&str, usize), Vec<&str>)> = vec![
            ("N1 correlated, SUPPLY 3", n1_corr(), ("SUPPLY", 3), vec![]),
            ("Fig. 12(c), R 3", fig_12c(), ("R", 3), FIG_12C_CARRIERS.to_vec()),
            // Two enabling symbols of `j` whose signatures differ off the keys (one
            // still holds `E`): they must not collapse, and the dedup must not read
            // the post-step layer.
            ("relay beside an undrained carrier, S 2", beside_carrier, ("S", 2), vec!["E"]),
        ];
        for (name, rows, (place, k), carriers) in cases {
            let net = pnid_net("orbit", &rows);
            let carrier_set: BTreeSet<String> = carriers.iter().map(|s| s.to_string()).collect();
            let fragment = classify(&net, FragmentMode::Extended, &carrier_set, &crate::name_fragment::all_mints(&net)).expect(name);
            let graph = NameStateClassGraph::build(
                &net,
                &crate::marking_state::MarkingStateBuilder::new().tokens(place, k).build(),
                &fragment,
                100_000,
                &[],
                &EnvironmentAnalysisMode::Ignore,
                PrioritySemantics::None,
            );
            assert!(graph.is_complete(), "{name}");
            let mut relay_steps = 0;
            let mut collapsed = 0;
            for class in &graph.classes {
                for tname in &class.base.enabled_transitions {
                    let Role::Join { coloured_in, relay_to } = fragment.role(tname) else {
                        continue;
                    };
                    if relay_to.is_empty() {
                        continue;
                    }
                    let tr = net.transitions().iter().find(|x| x.name() == tname).unwrap();
                    for (_, outputs) in expand_transition(tr) {
                        let mut fresh: Sym = 1_000_000;
                        let emitted: Vec<String> = name_successors(
                            fragment.role(tname),
                            &class.names,
                            &outputs.places,
                            &fragment,
                            &mut fresh,
                        )
                        .iter()
                        .map(|step| step.after.canonical_key(&fragment.coloured_order))
                        .collect();
                        // Per-symbol reference step: every enabling symbol, no dedup.
                        let enabling = enabling_symbols(&class.names, coloured_in);
                        let reference: BTreeSet<String> = enabling
                            .iter()
                            .map(|&s| {
                                let mut nm = (*class.names).clone();
                                for (p, req) in coloured_in {
                                    nm.remove(p, s, *req);
                                }
                                for p in outputs.places.iter().filter(|p| relay_to.contains(*p)) {
                                    nm.add(p, s, 1);
                                }
                                nm.canonical_key(&fragment.coloured_order)
                            })
                            .collect();
                        let distinct: BTreeSet<String> = emitted.iter().cloned().collect();
                        assert_eq!(distinct, reference, "{name}: {tname}");
                        assert_eq!(emitted.len(), reference.len(), "{name}: one successor per key");
                        relay_steps += 1;
                        if enabling.len() > reference.len() {
                            collapsed += 1;
                        }
                    }
                }
            }
            assert!(relay_steps > 0, "{name}: the fixture fires a relaying join");
            if name != "relay beside an undrained carrier, S 2" {
                assert!(collapsed > 0, "{name}: the fixture exercises the dedup");
            }
        }
    }

    /// [TIME-012] on a ν-join: a firing that takes the join's matched name out of a
    /// key place breaks the binding in the intermediate marking even when the count
    /// stays, so the join's clock restarts. `M0` mints `m` into `A`, `M1` co-mints `n`
    /// into `A` and `B`, both by 1 ms, and the relay `R` (EXTENDED, `delayed(3)`) takes
    /// one name from `A` and puts it back. Taking `n` leaves `A = {m}`, `B = {n}` in between: `J` restarts with its
    /// full 10 ms. Taking `m` leaves `J` enabled throughout: its clock continues.
    #[test]
    fn a_broken_binding_in_the_intermediate_marking_restarts_the_join_clock() {
        use crate::marking_state::MarkingStateBuilder;
        use crate::name_fragment::{FragmentMode, classify};
        use libpetri_core::input::one;
        use libpetri_core::match_spec::MatchSpec;
        use libpetri_core::name::NameId;
        use libpetri_core::output::{and, out_place};
        use libpetri_core::place::Place;
        use libpetri_core::timing;
        use std::collections::BTreeSet;

        let p = |n: &str| Place::<String>::new(n);
        let key = |s: &String| NameId::new(s.clone());
        let m0 = Transition::builder("M0")
            .input(one(&p("s0")))
            .output(out_place(&p("A")))
            .timing(timing::deadline(1))
            .action(fork())
            .build();
        let m1 = Transition::builder("M1")
            .input(one(&p("s1")))
            .output(and(vec![out_place(&p("A")), out_place(&p("B"))]))
            .timing(timing::deadline(1))
            .action(fork())
            .build();
        let j = Transition::builder("J")
            .input(one(&p("A")))
            .input(one(&p("B")))
            .match_spec(MatchSpec::builder().key(&p("A"), key).key(&p("B"), key).build())
            .output(out_place(&p("OUT")))
            .timing(timing::delayed(10))
            .action(fork())
            .build();
        let r = Transition::builder("R")
            .input(one(&p("A")))
            .input(one(&p("go")))
            .output(out_place(&p("A")))
            .timing(timing::delayed(3))
            .action(fork())
            .build();
        let net = PetriNet::builder("broken_binding").transitions([m0, m1, j, r]).build();
        let fragment = classify(&net, FragmentMode::Extended, &BTreeSet::new(), &crate::name_fragment::all_mints(&net))
            .expect("R is an EXTENDED relay");
        let initial = MarkingStateBuilder::new()
            .tokens("s0", 1)
            .tokens("s1", 1)
            .tokens("go", 1)
            .build();
        let graph = NameStateClassGraph::build(
            &net,
            &initial,
            &fragment,
            10_000,
            &[],
            &EnvironmentAnalysisMode::Ignore,
            PrioritySemantics::None,
        );
        assert!(graph.is_complete());
        let j_ready_after_r: BTreeSet<u64> = graph
            .edges
            .iter()
            .filter(|e| e.transition_name == "R")
            .filter_map(|e| {
                let base = &graph.classes[e.to].base;
                let k = base.enabled_transitions.iter().position(|t| t == "J")?;
                Some((base.ready_earliest[k] * 1000.0).round() as u64)
            })
            .collect();
        assert!(
            j_ready_after_r.contains(&10),
            "taking the matched name restarts J: ready in {j_ready_after_r:?} ms"
        );
        assert!(
            j_ready_after_r.iter().any(|&ms| ms <= 8),
            "taking the other name keeps J's clock: ready in {j_ready_after_r:?} ms"
        );
    }
}
