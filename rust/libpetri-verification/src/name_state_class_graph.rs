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
//! is truncated (`complete == false`) and the verifier reports `Unknown`.

use std::collections::{HashMap, HashSet, VecDeque};

use libpetri_core::petri_net::PetriNet;
use libpetri_core::transition::Transition;

use crate::environment::EnvironmentAnalysisMode;
use crate::marking_state::MarkingState;
use crate::name_fragment::{NameFragment, Role};
use crate::name_marking::{NameMarking, Sym};
use crate::name_state_class::NameStateClass;
use crate::priority_semantics::PrioritySemantics;
use crate::state_class_graph::{compute_successor, expand_transition, initial_state_class};

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
}

impl NameStateClassGraph {
    pub(crate) fn build(
        net: &PetriNet,
        initial_marking: &MarkingState,
        fragment: &NameFragment,
        max_classes: usize,
        env_places: &[&str],
        env_mode: &EnvironmentAnalysisMode,
        priority_semantics: PrioritySemantics,
    ) -> Self {
        let env_set: HashSet<&str> = env_places.iter().copied().collect();
        let base0 = initial_state_class(net, initial_marking, &env_set, env_mode);
        // Coloured places start empty in the supported fragment (the verifier
        // guards this), so the initial name partition is empty.
        let initial = NameStateClass::new(base0, NameMarking::new());

        let mut graph = NameStateClassGraph {
            classes: Vec::new(),
            edges: Vec::new(),
            successors: Vec::new(),
            predecessors: Vec::new(),
            complete: true,
        };
        let mut keys: HashMap<String, usize> = HashMap::new();
        let key0 = initial.canonical_key(&fragment.coloured_order);
        graph.push_class(initial, key0, &mut keys);

        let mut next_sym: Sym = 0;
        let mut queue: VecDeque<usize> = VecDeque::new();
        queue.push_back(0);

        while let Some(cur_idx) = queue.pop_front() {
            if graph.classes.len() >= max_classes {
                graph.complete = false;
                break;
            }
            let current = graph.classes[cur_idx].clone();

            // The enabled transitions of this class as objects — used by the
            // conflict-only priority prune below ([NU-052]).
            let enabled: Vec<&Transition> = current
                .base
                .enabled_transitions
                .iter()
                .map(|t_name| {
                    net.transitions()
                        .iter()
                        .find(|t| t.name() == t_name.as_str())
                        .unwrap()
                })
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

                for (_branch, output_places) in expand_transition(transition) {
                    // Base (count + DBM) successor — identical across name-orbits.
                    let base_succ = compute_successor(
                        net,
                        &current.base,
                        clock_idx,
                        t_name,
                        &output_places,
                        &env_set,
                        env_mode,
                    );
                    if base_succ.is_empty() {
                        continue; // DBM zone infeasible
                    }

                    // Name-layer successors for this firing (the join may yield 0).
                    let name_succs =
                        name_successors(role, &current.names, &output_places, fragment, &mut next_sym);

                    for names in name_succs {
                        let succ = NameStateClass::new(base_succ.clone(), names);
                        let key = succ.canonical_key(&fragment.coloured_order);
                        let to_idx = if let Some(&i) = keys.get(&key) {
                            i
                        } else {
                            let idx = graph.classes.len();
                            graph.push_class(succ, key, &mut keys);
                            queue.push_back(idx);
                            idx
                        };
                        graph.add_edge(cur_idx, to_idx, t_name);
                    }
                }
            }
        }

        graph
    }

    fn push_class(&mut self, c: NameStateClass, key: String, keys: &mut HashMap<String, usize>) {
        let idx = self.classes.len();
        self.classes.push(c);
        self.successors.push(Vec::new());
        self.predecessors.push(Vec::new());
        keys.insert(key, idx);
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

    pub(crate) fn successors(&self, idx: usize) -> &[usize] {
        &self.successors[idx]
    }
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

/// Name-layer successors of one transition firing. `Ordinary` passes the layer
/// through; `Mint` stamps one globally-fresh symbol into the coloured outputs of
/// this branch (one symbol into several = same-mint siblings); `Join` yields one
/// successor per enabling symbol (none ⇒ the join is name-disabled); `Consume`
/// (EXTENDED, [NU-051]) yields one successor per resident symbol of the single
/// coloured input, threading that symbol into every coloured output (relay) or
/// dropping it (drain).
fn name_successors(
    role: &Role,
    names: &NameMarking,
    output_places: &HashSet<String>,
    fragment: &NameFragment,
    next_sym: &mut Sym,
) -> Vec<NameMarking> {
    match role {
        Role::Ordinary => vec![names.clone()],
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
            vec![nm]
        }
        Role::Join { coloured_in } => enabling_symbols(names, coloured_in)
            .into_iter()
            .map(|s| {
                let mut nm = names.clone();
                for (p, req) in coloured_in {
                    nm.remove(p, s, *req);
                }
                nm
            })
            .collect(),
        Role::Consume { input_place } => {
            let coloured_out = coloured_outputs(output_places, fragment);
            // The consumed count is fixed at 1, so EVERY resident symbol (each
            // present at count ≥ 1) enables a firing — none is dropped, so no
            // base-enabled firing vanishes (Blocker 2). Each coloured output
            // receives EXACTLY ONE symbol, matching the base marking's single
            // token per output place (Blocker 1).
            names
                .symbols_in(input_place)
                .into_iter()
                .map(|s| {
                    let mut nm = names.clone();
                    nm.remove(input_place, s, 1);
                    for p in &coloured_out {
                        nm.add(p, s, 1);
                    }
                    nm
                })
                .collect()
        }
    }
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
        Role::Join { coloured_in } => !enabling_symbols(names, coloured_in).is_empty(),
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
mod tests {
    use super::*;
    use libpetri_core::action::fork;

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

        let fragment = classify(&net, FragmentMode::Extended, &BTreeSet::new())
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
}
