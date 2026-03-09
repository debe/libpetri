use std::collections::{HashMap, HashSet, VecDeque};

use libpetri_core::input::{self, In};
use libpetri_core::output::enumerate_branches;
use libpetri_core::petri_net::PetriNet;

use crate::dbm::Dbm;
use crate::environment::EnvironmentAnalysisMode;
use crate::marking_state::{MarkingState, MarkingStateBuilder};
use crate::state_class::StateClass;

/// Edge in the state class graph representing a transition firing.
#[derive(Debug, Clone)]
pub struct StateClassEdge {
    pub from: usize,
    pub to: usize,
    pub transition_name: String,
    pub branch_index: usize,
}

/// State Class Graph implementing the Berthomieu-Diaz (1991) algorithm.
///
/// BFS exploration with deduplication by canonical key (marking + firing domain).
#[derive(Debug)]
pub struct StateClassGraph {
    classes: Vec<StateClass>,
    edges: Vec<StateClassEdge>,
    successors: HashMap<usize, Vec<usize>>,
    predecessors: HashMap<usize, Vec<usize>>,
    complete: bool,
}

impl StateClassGraph {
    pub fn new() -> Self {
        Self {
            classes: Vec::new(),
            edges: Vec::new(),
            successors: HashMap::new(),
            predecessors: HashMap::new(),
            complete: true,
        }
    }

    /// Builds the state class graph for a Time Petri Net using BFS exploration.
    pub fn build(net: &PetriNet, initial_marking: &MarkingState, max_classes: usize) -> Self {
        Self::build_with_env(
            net,
            initial_marking,
            max_classes,
            &[],
            &EnvironmentAnalysisMode::Ignore,
        )
    }

    /// Builds with environment place support.
    pub fn build_with_env(
        net: &PetriNet,
        initial_marking: &MarkingState,
        max_classes: usize,
        env_places: &[&str],
        env_mode: &EnvironmentAnalysisMode,
    ) -> Self {
        let env_set: HashSet<&str> = env_places.iter().copied().collect();
        let enabled = find_enabled_transitions(net, initial_marking, &env_set, env_mode);
        let clock_names: Vec<String> = enabled.clone();
        let lower_bounds: Vec<f64> = enabled
            .iter()
            .map(|name| {
                let t = net
                    .transitions()
                    .iter()
                    .find(|t| t.name() == name.as_str())
                    .unwrap();
                t.timing().earliest() as f64 / 1000.0
            })
            .collect();
        let upper_bounds: Vec<f64> = enabled
            .iter()
            .map(|name| {
                let t = net
                    .transitions()
                    .iter()
                    .find(|t| t.name() == name.as_str())
                    .unwrap();
                t.timing().latest() as f64 / 1000.0
            })
            .collect();

        let initial_dbm = Dbm::create(clock_names, &lower_bounds, &upper_bounds);
        let initial_dbm = initial_dbm.let_time_pass();
        let initial_class = StateClass::new(initial_marking.clone(), initial_dbm, enabled);

        let mut graph = StateClassGraph::new();
        let initial_key = initial_class.canonical_key();

        graph.classes.push(initial_class);
        let mut class_keys: HashMap<String, usize> = HashMap::new();
        class_keys.insert(initial_key, 0);
        graph.successors.insert(0, Vec::new());
        graph.predecessors.insert(0, Vec::new());

        let mut queue: VecDeque<usize> = VecDeque::new();
        queue.push_back(0);

        while let Some(current_idx) = queue.pop_front() {
            if graph.classes.len() >= max_classes {
                graph.complete = false;
                break;
            }

            let current = graph.classes[current_idx].clone();

            for (clock_idx, transition_name) in current.enabled_transitions.iter().enumerate() {
                let transition = net
                    .transitions()
                    .iter()
                    .find(|t| t.name() == transition_name.as_str())
                    .unwrap();

                // Expand XOR branches into virtual transitions
                let virtual_transitions = expand_transition(transition);

                for (branch_index, output_places) in virtual_transitions {
                    let successor = compute_successor(
                        net,
                        &current,
                        clock_idx,
                        transition_name,
                        &output_places,
                        &env_set,
                        env_mode,
                    );

                    if successor.is_empty() {
                        continue;
                    }

                    let key = successor.canonical_key();

                    let target_idx = if let Some(&existing_idx) = class_keys.get(&key) {
                        existing_idx
                    } else {
                        let idx = graph.classes.len();
                        class_keys.insert(key, idx);
                        graph.classes.push(successor);
                        graph.successors.insert(idx, Vec::new());
                        graph.predecessors.insert(idx, Vec::new());
                        queue.push_back(idx);
                        idx
                    };

                    graph.edges.push(StateClassEdge {
                        from: current_idx,
                        to: target_idx,
                        transition_name: transition_name.clone(),
                        branch_index,
                    });
                    graph
                        .successors
                        .entry(current_idx)
                        .or_default()
                        .push(target_idx);
                    graph
                        .predecessors
                        .entry(target_idx)
                        .or_default()
                        .push(current_idx);
                }
            }
        }

        graph
    }

    /// Returns the number of state classes.
    pub fn class_count(&self) -> usize {
        self.classes.len()
    }

    /// Returns the state classes.
    pub fn classes(&self) -> &[StateClass] {
        &self.classes
    }

    /// Returns all edges.
    pub fn edges(&self) -> &[StateClassEdge] {
        &self.edges
    }

    /// Returns whether the graph was fully explored (not truncated).
    pub fn is_complete(&self) -> bool {
        self.complete
    }

    /// Returns successor class indices for a given class.
    pub fn successors(&self, class_idx: usize) -> &[usize] {
        self.successors
            .get(&class_idx)
            .map_or(&[], |v| v.as_slice())
    }

    /// Returns predecessor class indices for a given class.
    pub fn predecessors(&self, class_idx: usize) -> &[usize] {
        self.predecessors
            .get(&class_idx)
            .map_or(&[], |v| v.as_slice())
    }

    /// Checks if a marking is reachable (exists in any state class).
    pub fn is_reachable(&self, marking: &MarkingState) -> bool {
        self.classes.iter().any(|sc| sc.marking == *marking)
    }

    /// Returns all unique reachable markings.
    pub fn reachable_markings(&self) -> Vec<&MarkingState> {
        let mut seen = HashSet::new();
        let mut result = Vec::new();
        for sc in &self.classes {
            let key = sc.marking.canonical_key();
            if seen.insert(key) {
                result.push(&sc.marking);
            }
        }
        result
    }

    /// Returns the edge count.
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Returns the enabled transition names for a state class.
    pub fn enabled_transitions(&self, class_idx: usize) -> &[String] {
        &self.classes[class_idx].enabled_transitions
    }

    /// Returns edges from a given class that fired a specific transition name.
    pub fn branch_edges(&self, class_idx: usize, transition_name: &str) -> Vec<&StateClassEdge> {
        self.edges
            .iter()
            .filter(|e| e.from == class_idx && e.transition_name == transition_name)
            .collect()
    }
}

impl Default for StateClassGraph {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== Internal Functions ====================

fn find_enabled_transitions(
    net: &PetriNet,
    marking: &MarkingState,
    env_places: &HashSet<&str>,
    env_mode: &EnvironmentAnalysisMode,
) -> Vec<String> {
    let mut enabled = Vec::new();
    for t in net.transitions() {
        if is_enabled(t, marking, env_places, env_mode) {
            enabled.push(t.name().to_string());
        }
    }
    enabled
}

fn is_enabled(
    transition: &libpetri_core::transition::Transition,
    marking: &MarkingState,
    env_places: &HashSet<&str>,
    env_mode: &EnvironmentAnalysisMode,
) -> bool {
    for spec in transition.input_specs() {
        let place_name = spec.place_name();
        let is_env = env_places.contains(place_name);

        if is_env {
            match env_mode {
                EnvironmentAnalysisMode::AlwaysAvailable => continue, // always satisfied
                EnvironmentAnalysisMode::Bounded { max_tokens } => {
                    // Consider up to max_tokens available
                    let required = input::required_count(spec);
                    let available = marking.count(place_name) + max_tokens;
                    if available < required {
                        return false;
                    }
                }
                EnvironmentAnalysisMode::Ignore => {
                    let required = input::required_count(spec);
                    if marking.count(place_name) < required {
                        return false;
                    }
                }
            }
        } else {
            let required = input::required_count(spec);
            if marking.count(place_name) < required {
                return false;
            }
        }
    }
    for arc in transition.reads() {
        if marking.count(arc.place.name()) < 1 {
            return false;
        }
    }
    for arc in transition.inhibitors() {
        if marking.count(arc.place.name()) > 0 {
            return false;
        }
    }
    true
}

fn expand_transition(
    transition: &libpetri_core::transition::Transition,
) -> Vec<(usize, HashSet<String>)> {
    if let Some(out_spec) = transition.output_spec() {
        let branches = enumerate_branches(out_spec);
        if branches.len() <= 1 {
            let places: HashSet<String> = branches
                .into_iter()
                .flat_map(|b| b.into_iter().map(|p| p.name().to_string()))
                .collect();
            vec![(0, places)]
        } else {
            branches
                .into_iter()
                .enumerate()
                .map(|(i, b)| {
                    let places: HashSet<String> =
                        b.into_iter().map(|p| p.name().to_string()).collect();
                    (i, places)
                })
                .collect()
        }
    } else {
        vec![(0, HashSet::new())]
    }
}

fn compute_successor(
    net: &PetriNet,
    current: &StateClass,
    fired_clock: usize,
    fired_name: &str,
    output_places: &HashSet<String>,
    env_places: &HashSet<&str>,
    env_mode: &EnvironmentAnalysisMode,
) -> StateClass {
    let transition = net
        .transitions()
        .iter()
        .find(|t| t.name() == fired_name)
        .unwrap();

    // 1. Compute new marking
    let new_marking = fire_transition_marking(
        &current.marking,
        transition,
        output_places,
        env_places,
        env_mode,
    );

    // 2. Determine persistent and newly enabled transitions
    let new_enabled_all = find_enabled_transitions(net, &new_marking, env_places, env_mode);

    let mut persistent = Vec::new();
    let mut persistent_indices = Vec::new();
    for (i, name) in current.enabled_transitions.iter().enumerate() {
        if name != fired_name && new_enabled_all.contains(name) {
            persistent.push(name.clone());
            persistent_indices.push(i);
        }
    }

    let persistent_set: HashSet<&String> = persistent.iter().collect();
    let newly_enabled: Vec<String> = new_enabled_all
        .into_iter()
        .filter(|n| !persistent_set.contains(n))
        .collect();

    // 3. Compute successor DBM
    let new_lower_bounds: Vec<f64> = newly_enabled
        .iter()
        .map(|name| {
            let t = net
                .transitions()
                .iter()
                .find(|t| t.name() == name.as_str())
                .unwrap();
            t.timing().earliest() as f64 / 1000.0
        })
        .collect();
    let new_upper_bounds: Vec<f64> = newly_enabled
        .iter()
        .map(|name| {
            let t = net
                .transitions()
                .iter()
                .find(|t| t.name() == name.as_str())
                .unwrap();
            t.timing().latest() as f64 / 1000.0
        })
        .collect();

    let new_dbm = current.dbm.fire_transition(
        fired_clock,
        &newly_enabled,
        &new_lower_bounds,
        &new_upper_bounds,
        &persistent_indices,
    );
    let new_dbm = new_dbm.let_time_pass();

    let mut all_enabled = persistent;
    all_enabled.extend(newly_enabled);

    StateClass::new(new_marking, new_dbm, all_enabled)
}

fn fire_transition_marking(
    marking: &MarkingState,
    transition: &libpetri_core::transition::Transition,
    output_places: &HashSet<String>,
    env_places: &HashSet<&str>,
    env_mode: &EnvironmentAnalysisMode,
) -> MarkingState {
    let mut builder = MarkingStateBuilder::new();

    // Copy current marking
    for (place, count) in marking.places() {
        builder = builder.tokens(place, count);
    }

    // Consume from inputs (skip env places in AlwaysAvailable/Bounded modes)
    for spec in transition.input_specs() {
        let place_name = spec.place_name();
        let is_env = env_places.contains(place_name);

        if is_env && *env_mode != EnvironmentAnalysisMode::Ignore {
            // Don't consume from environment places in AlwaysAvailable/Bounded modes
            continue;
        }

        let to_consume = input_consume_count(spec);
        let current = marking.count(place_name);
        let remaining = current.saturating_sub(to_consume);
        builder = builder.tokens(place_name, remaining);
    }

    // Reset places
    for arc in transition.resets() {
        builder = builder.tokens(arc.place.name(), 0);
    }

    let result = builder.build();

    // Produce to outputs
    let mut output_builder = MarkingStateBuilder::new();
    for (place, count) in result.places() {
        output_builder = output_builder.tokens(place, count);
    }
    for place in output_places {
        let current = result.count(place);
        output_builder = output_builder.tokens(place.as_str(), current + 1);
    }

    output_builder.build()
}

fn input_consume_count(spec: &In) -> usize {
    match spec {
        In::One { .. } => 1,
        In::Exactly { count, .. } => *count,
        In::All { .. } => 1, // Analysis: consume minimum (1 token)
        In::AtLeast { minimum, .. } => *minimum,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    #[test]
    fn build_simple_chain() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("chain").transition(t).build();

        let initial = MarkingStateBuilder::new().tokens("p1", 1).build();
        let scg = StateClassGraph::build(&net, &initial, 1000);

        assert!(scg.is_complete());
        assert!(scg.class_count() >= 2); // initial + after firing
        assert!(!scg.edges().is_empty());

        // p2 should be reachable
        let target = MarkingStateBuilder::new().tokens("p2", 1).build();
        assert!(scg.is_reachable(&target));
    }

    #[test]
    fn build_cycle() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p1))
            .build();
        let net = PetriNet::builder("cycle").transitions([t1, t2]).build();

        let initial = MarkingStateBuilder::new().tokens("p1", 1).build();
        let scg = StateClassGraph::build(&net, &initial, 1000);

        assert!(scg.is_complete());
        // Two markings: p1=1 and p2=1, cycling
        assert_eq!(scg.reachable_markings().len(), 2);
    }

    #[test]
    fn build_truncated() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p1))
            .build();
        let net = PetriNet::builder("cycle").transitions([t1, t2]).build();

        let initial = MarkingStateBuilder::new().tokens("p1", 1).build();
        let scg = StateClassGraph::build(&net, &initial, 1); // max 1 class

        assert!(!scg.is_complete());
    }

    #[test]
    fn build_no_enabled_transitions() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        // No tokens in p1 — nothing enabled
        let initial = MarkingState::new();
        let scg = StateClassGraph::build(&net, &initial, 1000);

        assert!(scg.is_complete());
        assert_eq!(scg.class_count(), 1); // just the initial class
        assert!(scg.edges().is_empty());
    }

    #[test]
    fn build_fork_net() {
        let p = Place::<i32>::new("p");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");

        let t = Transition::builder("t1")
            .input(one(&p))
            .output(libpetri_core::output::and(vec![
                out_place(&a),
                out_place(&b),
            ]))
            .build();
        let net = PetriNet::builder("fork").transition(t).build();

        let initial = MarkingStateBuilder::new().tokens("p", 1).build();
        let scg = StateClassGraph::build(&net, &initial, 1000);

        let target = MarkingStateBuilder::new()
            .tokens("a", 1)
            .tokens("b", 1)
            .build();
        assert!(scg.is_reachable(&target));
    }

    #[test]
    fn build_xor_net() {
        let p = Place::<i32>::new("p");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");

        let t = Transition::builder("t1")
            .input(one(&p))
            .output(libpetri_core::output::xor(vec![
                out_place(&a),
                out_place(&b),
            ]))
            .build();
        let net = PetriNet::builder("xor").transition(t).build();

        let initial = MarkingStateBuilder::new().tokens("p", 1).build();
        let scg = StateClassGraph::build(&net, &initial, 1000);

        // Both branches should be reachable
        let target_a = MarkingStateBuilder::new().tokens("a", 1).build();
        let target_b = MarkingStateBuilder::new().tokens("b", 1).build();
        assert!(scg.is_reachable(&target_a));
        assert!(scg.is_reachable(&target_b));
    }

    #[test]
    fn build_inhibitor_net() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p_inh = Place::<i32>::new("inh");

        let t = Transition::builder("t1")
            .input(one(&p1))
            .inhibitor(libpetri_core::arc::inhibitor(&p_inh))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        // With inhibitor present — transition disabled
        let initial_blocked = MarkingStateBuilder::new()
            .tokens("p1", 1)
            .tokens("inh", 1)
            .build();
        let scg = StateClassGraph::build(&net, &initial_blocked, 1000);
        assert_eq!(scg.class_count(), 1); // no transitions fire
        assert!(scg.edges().is_empty());

        // Without inhibitor — transition enabled
        let initial_free = MarkingStateBuilder::new().tokens("p1", 1).build();
        let scg2 = StateClassGraph::build(&net, &initial_free, 1000);
        assert!(scg2.class_count() >= 2);
        let target = MarkingStateBuilder::new().tokens("p2", 1).build();
        assert!(scg2.is_reachable(&target));
    }

    #[test]
    fn build_with_timing_constraints() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let p3 = Place::<i32>::new("p3");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .timing(libpetri_core::timing::delayed(100))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&p3))
            .timing(libpetri_core::timing::window(50, 200))
            .build();

        let net = PetriNet::builder("timed").transitions([t1, t2]).build();

        let initial = MarkingStateBuilder::new().tokens("p1", 1).build();
        let scg = StateClassGraph::build(&net, &initial, 1000);

        assert!(scg.is_complete());
        let target = MarkingStateBuilder::new().tokens("p3", 1).build();
        assert!(scg.is_reachable(&target));

        // Check that DBMs have timing information
        let initial_class = &scg.classes()[0];
        assert!(!initial_class.dbm.is_empty());
    }

    #[test]
    fn build_concurrent_transitions() {
        // Two transitions enabled concurrently with different timings
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let out_a = Place::<i32>::new("a");
        let out_b = Place::<i32>::new("b");

        let t1 = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&out_a))
            .timing(libpetri_core::timing::delayed(100))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p2))
            .output(out_place(&out_b))
            .timing(libpetri_core::timing::delayed(200))
            .build();

        let net = PetriNet::builder("concurrent")
            .transitions([t1, t2])
            .build();

        let initial = MarkingStateBuilder::new()
            .tokens("p1", 1)
            .tokens("p2", 1)
            .build();
        let scg = StateClassGraph::build(&net, &initial, 1000);

        assert!(scg.is_complete());
        // Both transitions should fire
        let target = MarkingStateBuilder::new()
            .tokens("a", 1)
            .tokens("b", 1)
            .build();
        assert!(scg.is_reachable(&target));
    }

    #[test]
    fn build_env_always_available() {
        let p_env = Place::<i32>::new("env");
        let p_ready = Place::<i32>::new("ready");
        let p_out = Place::<i32>::new("out");

        let t = Transition::builder("t1")
            .input(one(&p_env))
            .input(one(&p_ready))
            .output(out_place(&p_out))
            .build();

        let net = PetriNet::builder("env").transition(t).build();

        let initial = MarkingStateBuilder::new().tokens("ready", 1).build();

        // Without env mode — env place has no tokens, transition blocked
        let scg_no_env = StateClassGraph::build(&net, &initial, 100);
        assert_eq!(scg_no_env.class_count(), 1);

        // With always-available — transition should fire
        let scg_env = StateClassGraph::build_with_env(
            &net,
            &initial,
            100,
            &["env"],
            &EnvironmentAnalysisMode::AlwaysAvailable,
        );
        assert!(scg_env.class_count() >= 2);
        let target = MarkingStateBuilder::new().tokens("out", 1).build();
        assert!(scg_env.is_reachable(&target));
    }

    #[test]
    fn build_env_always_available_cycles() {
        // With always-available env, a cycle where env is consumed should work indefinitely
        let p_env = Place::<i32>::new("env");
        let p_ready = Place::<i32>::new("ready");
        let p_out = Place::<i32>::new("out");

        let t1 = Transition::builder("process")
            .input(one(&p_env))
            .input(one(&p_ready))
            .output(out_place(&p_out))
            .build();
        let t2 = Transition::builder("reset")
            .input(one(&p_out))
            .output(out_place(&p_ready))
            .build();

        let net = PetriNet::builder("env-cycle").transitions([t1, t2]).build();

        let initial = MarkingStateBuilder::new().tokens("ready", 1).build();

        let scg = StateClassGraph::build_with_env(
            &net,
            &initial,
            100,
            &["env"],
            &EnvironmentAnalysisMode::AlwaysAvailable,
        );

        assert!(scg.is_complete());
        // Should cycle between ready and out states
        assert!(scg.class_count() >= 2);
        let target = MarkingStateBuilder::new().tokens("out", 1).build();
        assert!(scg.is_reachable(&target));
    }

    #[test]
    fn edge_count_matches_edges() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let initial = MarkingStateBuilder::new().tokens("p1", 1).build();
        let scg = StateClassGraph::build(&net, &initial, 1000);

        assert_eq!(scg.edge_count(), scg.edges().len());
    }

    #[test]
    fn enabled_transitions_returns_names() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let initial = MarkingStateBuilder::new().tokens("p1", 1).build();
        let scg = StateClassGraph::build(&net, &initial, 1000);

        let enabled = scg.enabled_transitions(0);
        assert!(enabled.contains(&"t1".to_string()));
    }

    #[test]
    fn branch_edges_for_xor() {
        let p = Place::<i32>::new("p");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");

        let t = Transition::builder("t1")
            .input(one(&p))
            .output(libpetri_core::output::xor(vec![
                out_place(&a),
                out_place(&b),
            ]))
            .build();
        let net = PetriNet::builder("xor").transition(t).build();

        let initial = MarkingStateBuilder::new().tokens("p", 1).build();
        let scg = StateClassGraph::build(&net, &initial, 1000);

        let edges = scg.branch_edges(0, "t1");
        assert_eq!(edges.len(), 2); // two XOR branches
        let branch_indices: HashSet<usize> = edges.iter().map(|e| e.branch_index).collect();
        assert!(branch_indices.contains(&0));
        assert!(branch_indices.contains(&1));
    }

    #[test]
    fn predecessors_and_successors() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let initial = MarkingStateBuilder::new().tokens("p1", 1).build();
        let scg = StateClassGraph::build(&net, &initial, 1000);

        // Initial class (0) should have successors
        assert!(!scg.successors(0).is_empty());
        // Successor should have predecessors pointing back to 0
        let succ = scg.successors(0)[0];
        assert!(scg.predecessors(succ).contains(&0));
    }
}
