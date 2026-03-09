use std::collections::HashSet;

use libpetri_core::output::enumerate_branches;
use libpetri_core::petri_net::PetriNet;

use crate::environment::EnvironmentAnalysisMode;
use crate::marking_state::MarkingState;
use crate::scc::{compute_sccs, find_terminal_sccs};
use crate::state_class_graph::StateClassGraph;

/// Result of liveness analysis.
#[derive(Debug)]
pub struct LivenessResult {
    pub state_class_graph: StateClassGraph,
    pub all_sccs: Vec<Vec<usize>>,
    pub terminal_sccs: Vec<Vec<usize>>,
    pub goal_classes: HashSet<usize>,
    pub can_reach_goal: HashSet<usize>,
    pub is_goal_live: bool,
    pub is_l4_live: bool,
    pub is_complete: bool,
    pub report: String,
}

/// XOR branch coverage information for a single transition.
#[derive(Debug)]
pub struct XorBranchInfo {
    pub transition_name: String,
    pub total_branches: usize,
    pub taken_branches: HashSet<usize>,
    pub untaken_branches: HashSet<usize>,
}

/// Result of XOR branch analysis.
#[derive(Debug)]
pub struct XorBranchAnalysis {
    pub branches: Vec<XorBranchInfo>,
}

impl XorBranchAnalysis {
    pub fn unreachable_branches(&self) -> Vec<(&str, &HashSet<usize>)> {
        self.branches
            .iter()
            .filter(|b| !b.untaken_branches.is_empty())
            .map(|b| (b.transition_name.as_str(), &b.untaken_branches))
            .collect()
    }

    pub fn is_xor_complete(&self) -> bool {
        self.branches.iter().all(|b| b.untaken_branches.is_empty())
    }

    pub fn report(&self) -> String {
        if self.branches.is_empty() {
            return "No XOR transitions in net.".to_string();
        }

        let mut lines = Vec::new();
        lines.push("XOR Branch Coverage Analysis".to_string());
        lines.push("============================\n".to_string());

        for info in &self.branches {
            lines.push(format!("Transition: {}", info.transition_name));
            lines.push(format!("  Branches: {}", info.total_branches));
            lines.push(format!(
                "  Taken: [{:?}]",
                info.taken_branches.iter().collect::<Vec<_>>()
            ));

            if info.untaken_branches.is_empty() {
                lines.push("  All branches reachable".to_string());
            } else {
                lines.push(format!(
                    "  UNREACHABLE: [{:?}]",
                    info.untaken_branches.iter().collect::<Vec<_>>()
                ));
            }
            lines.push(String::new());
        }

        if self.is_xor_complete() {
            lines.push("RESULT: All XOR branches are reachable.".to_string());
        } else {
            lines.push("RESULT: Some XOR branches are unreachable!".to_string());
        }

        lines.join("\n")
    }
}

/// Formal analyzer for Time Petri Nets using the State Class Graph method.
pub struct TimePetriNetAnalyzer<'a> {
    net: &'a PetriNet,
    initial_marking: MarkingState,
    goal_places: Vec<String>,
    max_classes: usize,
    env_places: Vec<String>,
    env_mode: EnvironmentAnalysisMode,
}

impl<'a> TimePetriNetAnalyzer<'a> {
    pub fn for_net(net: &'a PetriNet) -> TimePetriNetAnalyzerBuilder<'a> {
        TimePetriNetAnalyzerBuilder {
            net,
            initial_marking: MarkingState::new(),
            goal_places: Vec::new(),
            max_classes: 100_000,
            env_places: Vec::new(),
            env_mode: EnvironmentAnalysisMode::Ignore,
        }
    }

    /// Performs formal liveness analysis.
    pub fn analyze(&self) -> LivenessResult {
        let mut report = Vec::new();
        report.push("=== TIME PETRI NET FORMAL ANALYSIS ===\n".to_string());
        report.push("Method: State Class Graph (Berthomieu-Diaz 1991)".to_string());
        report.push(format!("Net: {}", self.net.name()));
        report.push(format!("Places: {}", self.net.places().len()));
        report.push(format!("Transitions: {}", self.net.transitions().len()));
        report.push(format!("Goal places: [{}]\n", self.goal_places.join(", ")));

        // Phase 1: Build State Class Graph
        report.push("Phase 1: Building State Class Graph...".to_string());
        if !self.env_places.is_empty() {
            report.push(format!("  Environment places: {}", self.env_places.len()));
            report.push(format!("  Environment mode: {:?}", self.env_mode));
        }
        let env_refs: Vec<&str> = self.env_places.iter().map(|s| s.as_str()).collect();
        let scg = StateClassGraph::build_with_env(
            self.net,
            &self.initial_marking,
            self.max_classes,
            &env_refs,
            &self.env_mode,
        );
        report.push(format!("  State classes: {}", scg.class_count()));
        report.push(format!("  Edges: {}", scg.edge_count()));
        report.push(format!(
            "  Complete: {}",
            if scg.is_complete() {
                "YES"
            } else {
                "NO (truncated)"
            }
        ));

        if !scg.is_complete() {
            report.push(format!(
                "  WARNING: State class graph truncated at {} classes. Analysis may be incomplete.",
                self.max_classes
            ));
        }
        report.push(String::new());

        // Phase 2: Identify goal state classes
        report.push("Phase 2: Identifying goal state classes...".to_string());
        let goal_place_refs: Vec<&str> = self.goal_places.iter().map(|s| s.as_str()).collect();
        let mut goal_classes = HashSet::new();
        for (idx, sc) in scg.classes().iter().enumerate() {
            if sc.marking.has_tokens_in_any(&goal_place_refs) {
                goal_classes.insert(idx);
            }
        }
        report.push(format!("  Goal state classes: {}\n", goal_classes.len()));

        // Phase 3: Compute SCCs
        report.push("Phase 3: Computing Strongly Connected Components...".to_string());
        let successor_fn = |idx: usize| scg.successors(idx).to_vec();
        let all_sccs = compute_sccs(scg.class_count(), successor_fn);
        let terminal_sccs = find_terminal_sccs(scg.class_count(), successor_fn);

        report.push(format!("  Total SCCs: {}", all_sccs.len()));
        report.push(format!("  Terminal SCCs: {}\n", terminal_sccs.len()));

        // Phase 4: Check goal liveness
        report.push("Phase 4: Verifying Goal Liveness...".to_string());
        report
            .push("  Property: From every reachable state, a goal state is reachable".to_string());

        let mut terminal_without_goal = 0;
        for scc in &terminal_sccs {
            if !scc.iter().any(|idx| goal_classes.contains(idx)) {
                terminal_without_goal += 1;
            }
        }

        let can_reach_goal = compute_backward_reachability(&scg, &goal_classes);
        let states_not_reaching_goal = scg.class_count() - can_reach_goal.len();

        report.push(format!(
            "  Terminal SCCs with goal: {}",
            terminal_sccs.len() - terminal_without_goal
        ));
        report.push(format!(
            "  Terminal SCCs without goal: {}",
            terminal_without_goal
        ));
        report.push(format!(
            "  States that can reach goal: {}/{}\n",
            can_reach_goal.len(),
            scg.class_count()
        ));

        let is_goal_live = terminal_without_goal == 0 && states_not_reaching_goal == 0;

        // Phase 5: Check classical liveness (L4)
        report.push("Phase 5: Verifying Classical Liveness (L4)...".to_string());
        report
            .push("  Property: Every transition can fire from every reachable marking".to_string());

        let all_transition_names: HashSet<&str> =
            self.net.transitions().iter().map(|t| t.name()).collect();

        let mut terminal_missing_transitions = 0;
        for scc in &terminal_sccs {
            let scc_set: HashSet<usize> = scc.iter().copied().collect();
            let mut transitions_in_scc: HashSet<String> = HashSet::new();

            for &class_idx in scc {
                for t_name in scg.enabled_transitions(class_idx) {
                    let edges = scg.branch_edges(class_idx, t_name);
                    for edge in edges {
                        if scc_set.contains(&edge.to) {
                            transitions_in_scc.insert(t_name.clone());
                        }
                    }
                }
            }

            let mut missing_any = false;
            for &t_name in &all_transition_names {
                if !transitions_in_scc.contains(t_name) {
                    missing_any = true;
                    break;
                }
            }
            if missing_any {
                terminal_missing_transitions += 1;
                let missing: Vec<&str> = all_transition_names
                    .iter()
                    .filter(|&&t| !transitions_in_scc.contains(t))
                    .copied()
                    .collect();
                report.push(format!(
                    "  Terminal SCC missing transitions: [{}]",
                    missing.join(", ")
                ));
            }
        }

        let is_l4_live = terminal_missing_transitions == 0 && scg.is_complete();

        // Summary
        report.push("\n=== ANALYSIS RESULT ===\n".to_string());

        if is_goal_live && scg.is_complete() {
            report.push("GOAL LIVENESS VERIFIED".to_string());
            report.push(
                "  From every reachable state class, a goal marking is reachable.".to_string(),
            );
        } else if is_goal_live {
            report.push("GOAL LIVENESS LIKELY (incomplete proof)".to_string());
        } else {
            report.push("GOAL LIVENESS VIOLATION".to_string());
            if terminal_without_goal > 0 {
                report.push(format!(
                    "  {} terminal SCC(s) have no goal state.",
                    terminal_without_goal
                ));
            }
            if states_not_reaching_goal > 0 {
                report.push(format!(
                    "  {} state class(es) cannot reach goal.",
                    states_not_reaching_goal
                ));
            }
        }

        report.push(String::new());

        if is_l4_live {
            report.push("CLASSICAL LIVENESS (L4) VERIFIED".to_string());
        } else {
            report.push("CLASSICAL LIVENESS (L4) NOT VERIFIED".to_string());
            if terminal_missing_transitions > 0 {
                report.push("  Some terminal SCCs don't contain all transitions.".to_string());
            }
            if !scg.is_complete() {
                report.push("  (State class graph incomplete - cannot prove L4)".to_string());
            }
        }

        let is_complete = scg.is_complete();

        LivenessResult {
            state_class_graph: scg,
            all_sccs,
            terminal_sccs,
            goal_classes,
            can_reach_goal,
            is_goal_live,
            is_l4_live,
            is_complete,
            report: report.join("\n"),
        }
    }

    /// Analyzes XOR branch coverage for a built state class graph.
    pub fn analyze_xor_branches(net: &PetriNet, scg: &StateClassGraph) -> XorBranchAnalysis {
        let mut branches = Vec::new();

        for transition in net.transitions() {
            let out_spec = match transition.output_spec() {
                Some(spec) => spec,
                None => continue,
            };

            let all_branches = enumerate_branches(out_spec);
            if all_branches.len() <= 1 {
                continue;
            }

            let mut taken = HashSet::new();
            for class_idx in 0..scg.class_count() {
                for edge in scg.branch_edges(class_idx, transition.name()) {
                    taken.insert(edge.branch_index);
                }
            }

            let untaken: HashSet<usize> = (0..all_branches.len())
                .filter(|i| !taken.contains(i))
                .collect();

            branches.push(XorBranchInfo {
                transition_name: transition.name().to_string(),
                total_branches: all_branches.len(),
                taken_branches: taken,
                untaken_branches: untaken,
            });
        }

        XorBranchAnalysis { branches }
    }
}

fn compute_backward_reachability(scg: &StateClassGraph, goals: &HashSet<usize>) -> HashSet<usize> {
    let mut reachable: HashSet<usize> = goals.clone();
    let mut queue: Vec<usize> = goals.iter().copied().collect();

    while let Some(current) = queue.pop() {
        for &pred in scg.predecessors(current) {
            if reachable.insert(pred) {
                queue.push(pred);
            }
        }
    }

    reachable
}

/// Builder for TimePetriNetAnalyzer.
pub struct TimePetriNetAnalyzerBuilder<'a> {
    net: &'a PetriNet,
    initial_marking: MarkingState,
    goal_places: Vec<String>,
    max_classes: usize,
    env_places: Vec<String>,
    env_mode: EnvironmentAnalysisMode,
}

impl<'a> TimePetriNetAnalyzerBuilder<'a> {
    pub fn initial_marking(mut self, marking: MarkingState) -> Self {
        self.initial_marking = marking;
        self
    }

    pub fn goal_place(mut self, place_name: &str) -> Self {
        self.goal_places.push(place_name.to_string());
        self
    }

    pub fn goal_places(mut self, names: &[&str]) -> Self {
        for name in names {
            self.goal_places.push(name.to_string());
        }
        self
    }

    pub fn max_classes(mut self, max: usize) -> Self {
        self.max_classes = max;
        self
    }

    pub fn env_place(mut self, place_name: &str) -> Self {
        self.env_places.push(place_name.to_string());
        self
    }

    pub fn env_places(mut self, names: &[&str]) -> Self {
        for name in names {
            self.env_places.push(name.to_string());
        }
        self
    }

    pub fn env_mode(mut self, mode: EnvironmentAnalysisMode) -> Self {
        self.env_mode = mode;
        self
    }

    pub fn build(self) -> TimePetriNetAnalyzer<'a> {
        assert!(
            !self.goal_places.is_empty(),
            "At least one goal place must be specified"
        );
        TimePetriNetAnalyzer {
            net: self.net,
            initial_marking: self.initial_marking,
            goal_places: self.goal_places,
            max_classes: self.max_classes,
            env_places: self.env_places,
            env_mode: self.env_mode,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use libpetri_core::input::one;
    use libpetri_core::output::{out_place, xor};
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    #[test]
    fn goal_liveness_circular_net() {
        let p_a = Place::<i32>::new("A");
        let p_b = Place::<i32>::new("B");

        let t1 = Transition::builder("t1")
            .input(one(&p_a))
            .output(out_place(&p_b))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p_b))
            .output(out_place(&p_a))
            .build();

        let net = PetriNet::builder("circular").transitions([t1, t2]).build();

        let result = TimePetriNetAnalyzer::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("A", 1).build())
            .goal_place("B")
            .max_classes(100)
            .build()
            .analyze();

        assert!(result.is_goal_live);
        assert!(result.is_complete);
        assert!(result.state_class_graph.class_count() >= 2);
        assert!(result.report.contains("GOAL LIVENESS VERIFIED"));
    }

    #[test]
    fn goal_liveness_violation_dead_end() {
        let p_a = Place::<i32>::new("A");
        let p_b = Place::<i32>::new("B");
        let p_goal = Place::<i32>::new("Goal");

        let t1 = Transition::builder("t1")
            .input(one(&p_a))
            .output(out_place(&p_b))
            .build();

        let net = PetriNet::builder("deadend").transition(t1).build();
        let _ = &p_goal; // Goal place not connected

        let result = TimePetriNetAnalyzer::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("A", 1).build())
            .goal_place("Goal")
            .max_classes(100)
            .build()
            .analyze();

        assert!(!result.is_goal_live);
        assert!(result.report.contains("GOAL LIVENESS VIOLATION"));
    }

    #[test]
    fn l4_liveness_circular_net() {
        let p_a = Place::<i32>::new("A");
        let p_b = Place::<i32>::new("B");

        let t1 = Transition::builder("t1")
            .input(one(&p_a))
            .output(out_place(&p_b))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p_b))
            .output(out_place(&p_a))
            .build();

        let net = PetriNet::builder("circular").transitions([t1, t2]).build();

        let result = TimePetriNetAnalyzer::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("A", 1).build())
            .goal_place("A")
            .max_classes(100)
            .build()
            .analyze();

        assert!(result.is_l4_live);
        assert!(result.report.contains("CLASSICAL LIVENESS (L4) VERIFIED"));
    }

    #[test]
    fn l4_violation_dead_end() {
        let p_a = Place::<i32>::new("A");
        let p_b = Place::<i32>::new("B");

        let t1 = Transition::builder("t1")
            .input(one(&p_a))
            .output(out_place(&p_b))
            .build();

        let net = PetriNet::builder("deadend").transition(t1).build();

        let result = TimePetriNetAnalyzer::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("A", 1).build())
            .goal_place("B")
            .max_classes(100)
            .build()
            .analyze();

        assert!(!result.is_l4_live);
    }

    #[test]
    fn xor_branch_analysis() {
        let p0 = Place::<i32>::new("start");
        let p_a = Place::<i32>::new("branchA");
        let p_b = Place::<i32>::new("branchB");
        let p_end = Place::<i32>::new("end");

        let t_choice = Transition::builder("choice")
            .input(one(&p0))
            .output(xor(vec![out_place(&p_a), out_place(&p_b)]))
            .build();
        let t_a = Transition::builder("fromA")
            .input(one(&p_a))
            .output(out_place(&p_end))
            .build();
        let t_b = Transition::builder("fromB")
            .input(one(&p_b))
            .output(out_place(&p_end))
            .build();

        let net = PetriNet::builder("xor")
            .transitions([t_choice, t_a, t_b])
            .build();

        let marking = MarkingStateBuilder::new().tokens("start", 1).build();
        let scg = StateClassGraph::build(&net, &marking, 100);
        let analysis = TimePetriNetAnalyzer::analyze_xor_branches(&net, &scg);

        assert_eq!(analysis.branches.len(), 1);
        assert_eq!(analysis.branches[0].transition_name, "choice");
        assert_eq!(analysis.branches[0].total_branches, 2);
        assert_eq!(analysis.branches[0].taken_branches.len(), 2);
        assert!(analysis.branches[0].untaken_branches.is_empty());
        assert!(analysis.is_xor_complete());
        assert!(analysis.unreachable_branches().is_empty());
    }

    #[test]
    fn xor_report_generation() {
        let p0 = Place::<i32>::new("start");
        let p_a = Place::<i32>::new("branchA");
        let p_b = Place::<i32>::new("branchB");

        let t_choice = Transition::builder("choice")
            .input(one(&p0))
            .output(xor(vec![out_place(&p_a), out_place(&p_b)]))
            .build();

        let net = PetriNet::builder("xor").transition(t_choice).build();

        let marking = MarkingStateBuilder::new().tokens("start", 1).build();
        let scg = StateClassGraph::build(&net, &marking, 100);
        let analysis = TimePetriNetAnalyzer::analyze_xor_branches(&net, &scg);

        let report = analysis.report();
        assert!(report.contains("XOR Branch Coverage"));
        assert!(report.contains("choice"));
    }

    #[test]
    fn no_xor_report() {
        let p_a = Place::<i32>::new("A");
        let p_b = Place::<i32>::new("B");

        let t1 = Transition::builder("t1")
            .input(one(&p_a))
            .output(out_place(&p_b))
            .build();

        let net = PetriNet::builder("no-xor").transition(t1).build();

        let marking = MarkingStateBuilder::new().tokens("A", 1).build();
        let scg = StateClassGraph::build(&net, &marking, 100);
        let analysis = TimePetriNetAnalyzer::analyze_xor_branches(&net, &scg);

        assert_eq!(analysis.report(), "No XOR transitions in net.");
    }

    #[test]
    #[should_panic(expected = "At least one goal place")]
    fn builder_requires_goal_places() {
        let p_a = Place::<i32>::new("A");
        let t1 = Transition::builder("t1").input(one(&p_a)).build();
        let net = PetriNet::builder("test").transition(t1).build();

        TimePetriNetAnalyzer::for_net(&net)
            .initial_marking(MarkingState::new())
            .build();
    }

    #[test]
    fn always_available_env_enables_transitions() {
        let p_ready = Place::<i32>::new("ready");
        let p_env = Place::<i32>::new("input");
        let p_out = Place::<i32>::new("output");

        let t1 = Transition::builder("process")
            .input(one(&p_ready))
            .input(one(&p_env))
            .output(out_place(&p_out))
            .build();
        let t2 = Transition::builder("reset")
            .input(one(&p_out))
            .output(out_place(&p_ready))
            .build();

        let net = PetriNet::builder("env-net").transitions([t1, t2]).build();

        let result = TimePetriNetAnalyzer::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("ready", 1).build())
            .goal_place("output")
            .env_place("input")
            .env_mode(EnvironmentAnalysisMode::AlwaysAvailable)
            .max_classes(100)
            .build()
            .analyze();

        assert!(result.is_goal_live);
        assert!(result.report.contains("Environment places"));
    }

    #[test]
    fn ignore_env_treats_as_regular() {
        let p_env = Place::<i32>::new("input");
        let p_out = Place::<i32>::new("output");

        let t1 = Transition::builder("process")
            .input(one(&p_env))
            .output(out_place(&p_out))
            .build();

        let net = PetriNet::builder("env-net").transition(t1).build();

        let result = TimePetriNetAnalyzer::for_net(&net)
            .initial_marking(MarkingState::new())
            .goal_place("output")
            .env_place("input")
            .env_mode(EnvironmentAnalysisMode::Ignore)
            .max_classes(100)
            .build()
            .analyze();

        // No tokens in env place + ignore = not enabled → no goal reached
        assert!(!result.is_goal_live);
    }

    #[test]
    fn bounded_env_limits_tokens() {
        let p_ready = Place::<i32>::new("ready");
        let p_env = Place::<i32>::new("input");
        let p_out = Place::<i32>::new("output");

        let t1 = Transition::builder("process")
            .input(one(&p_ready))
            .input(one(&p_env))
            .output(out_place(&p_out))
            .build();
        let t2 = Transition::builder("reset")
            .input(one(&p_out))
            .output(out_place(&p_ready))
            .build();

        let net = PetriNet::builder("env-net").transitions([t1, t2]).build();

        let result = TimePetriNetAnalyzer::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("ready", 1).build())
            .goal_place("output")
            .env_place("input")
            .env_mode(EnvironmentAnalysisMode::Bounded { max_tokens: 1 })
            .max_classes(100)
            .build()
            .analyze();

        assert!(result.is_complete);
    }

    #[test]
    fn comprehensive_report() {
        let p_a = Place::<i32>::new("A");
        let p_b = Place::<i32>::new("B");

        let t1 = Transition::builder("t1")
            .input(one(&p_a))
            .output(out_place(&p_b))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p_b))
            .output(out_place(&p_a))
            .build();

        let net = PetriNet::builder("circular").transitions([t1, t2]).build();

        let result = TimePetriNetAnalyzer::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("A", 1).build())
            .goal_place("A")
            .max_classes(100)
            .build()
            .analyze();

        assert!(result.report.contains("TIME PETRI NET FORMAL ANALYSIS"));
        assert!(result.report.contains("Berthomieu-Diaz"));
        assert!(result.report.contains("State classes:"));
        assert!(result.report.contains("Terminal SCCs:"));
        assert!(result.report.contains("ANALYSIS RESULT"));
    }
}
