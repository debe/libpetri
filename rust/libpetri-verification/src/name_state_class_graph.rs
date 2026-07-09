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

use crate::environment::EnvironmentAnalysisMode;
use crate::marking_state::MarkingState;
use crate::name_fragment::{NameFragment, Role};
use crate::name_marking::{NameMarking, Sym};
use crate::name_state_class::NameStateClass;
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

            for (clock_idx, t_name) in current.base.enabled_transitions.iter().enumerate() {
                let transition = net
                    .transitions()
                    .iter()
                    .find(|t| t.name() == t_name.as_str())
                    .unwrap();
                let role = fragment.role(t_name);

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

#[cfg(test)]
mod tests {
    use super::*;

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
}
