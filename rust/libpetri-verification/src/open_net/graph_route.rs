//! The contract decided on the closed net's state-class graph ([VER-022]).
//!
//! The graph is built **untimed** ([VER-004]): every clock gets the interval of
//! `immediate()`, so the graph holds exactly the markings the untimed encoders reason about,
//! and its verdict is the stronger untimed claim even for a subnet with delayed transitions.
//! Like every graph route it is priority-blind and value-blind.
//!
//! When the graph closes, the verdict is exact. Every quiescent class is judged against the
//! contract, and a cycle anywhere in the graph is a run that never comes to rest. When it
//! does not close, what was found is still real. A class with no enabled transition is
//! quiescent whether or not the build got round to expanding it, and a cycle among explored
//! classes is a real cycle. Only the absence of findings needs the graph to have closed.

use std::collections::{HashMap, HashSet};

use crate::environment::EnvironmentAnalysisMode;
use crate::marking_state::MarkingState;
use crate::state_class_graph::{StateClassGraph, StateClassGraphOptions};

use super::closure::ClosedNet;
use super::contract::OpenNetContract;
use super::predicate::{Finding, quiescence_findings, rest_declaration_of};
use super::result::{ContractViolation, ContractViolationKind, Witness, contract_violation};

/// What the graph route found.
pub(super) struct GraphRouteOutcome {
    pub complete: bool,
    pub class_count: usize,
    /// Real violations: the shallowest witness per subject, then termination.
    pub violations: Vec<ContractViolation>,
}

/// Builds the closed net's untimed graph and judges it against `contract`.
pub(super) fn decide_on_graph(
    closed: &ClosedNet,
    contract: &OpenNetContract,
    max_classes: usize,
    traced_places: &[String],
) -> GraphRouteOutcome {
    let graph = StateClassGraph::build_with_options(
        &closed.net,
        &closed.initial_marking,
        max_classes,
        &[],
        &EnvironmentAnalysisMode::Ignore,
        StateClassGraphOptions { untimed: true },
    );
    let classes = graph.classes();
    let rest = rest_declaration_of(contract, closed);
    let outgoing = outgoing_edges(&graph);
    let tree = bfs_tree(&outgoing);

    // Classes come in BFS order, so the first class to show a subject is a shallowest one.
    let mut seen: HashSet<(ContractViolationKind, String)> = HashSet::new();
    let mut first: Vec<(Finding<'_>, usize)> = Vec::new();
    for (index, sc) in classes.iter().enumerate() {
        // In an untimed exploration an enabled transition can always fire, so "nothing
        // enabled" is the graph's own quiescence, and it holds of a class the build never
        // expanded as well.
        if !sc.enabled_transitions.is_empty() {
            continue;
        }
        for finding in quiescence_findings(&sc.marking, contract, &rest) {
            let key = (kind_of(&finding), finding.subject().to_string());
            if seen.insert(key) {
                first.push((finding, index));
            }
        }
    }

    // Clauses in contract order, then stranded places in code-point order: byte order is
    // code-point order for UTF-8, so every implementation lists the same way.
    let clause_order: HashMap<&str, usize> =
        contract.clauses().iter().enumerate().map(|(i, c)| (c.name.as_str(), i)).collect();
    let rank = |f: &Finding<'_>| -> usize {
        match f {
            Finding::Clause { clause, .. } => clause_order[clause.name.as_str()],
            Finding::Stranded { .. } => contract.clauses().len(),
        }
    };
    first.sort_by(|a, b| rank(&a.0).cmp(&rank(&b.0)).then_with(|| a.0.subject().cmp(b.0.subject())));

    let mut violations: Vec<ContractViolation> = first
        .iter()
        .map(|(finding, target)| {
            let (path, transitions) = path_to(&tree, *target);
            contract_violation(
                closed,
                traced_places,
                Witness {
                    kind: kind_of(finding),
                    subject: finding.subject().to_string(),
                    detail: finding.describe(),
                    transitions,
                    markings: path.iter().map(|&c| classes[c].marking.clone()).collect(),
                    cycle_start: None,
                    confirmed: true,
                },
            )
        })
        .collect();

    if contract.requires_termination() {
        if let Some(cycle) = find_cycle(&graph, &outgoing, &tree) {
            violations.push(contract_violation(closed, traced_places, cycle));
        }
    }
    GraphRouteOutcome { complete: graph.is_complete(), class_count: classes.len(), violations }
}

fn kind_of(f: &Finding<'_>) -> ContractViolationKind {
    match f {
        Finding::Clause { .. } => ContractViolationKind::Clause,
        Finding::Stranded { .. } => ContractViolationKind::Stranded,
    }
}

/// Each class's outgoing edges as `(transition, target)`, grouped by transition in the
/// order the build fired them, branches of one transition in branch order.
///
/// The build pushes every edge of a class while expanding it, one enabled transition after
/// another, so a class's edges are contiguous and already in that order.
fn outgoing_edges(graph: &StateClassGraph) -> Vec<Vec<(&str, usize)>> {
    let mut outgoing: Vec<Vec<(&str, usize)>> = vec![Vec::new(); graph.class_count()];
    for edge in graph.edges() {
        outgoing[edge.from].push((edge.transition_name.as_str(), edge.to));
    }
    outgoing
}

/// Each explored class's BFS parent and the transition that first reached it; `None` for
/// the initial class and for classes nothing reached.
fn bfs_tree<'g>(outgoing: &[Vec<(&'g str, usize)>]) -> Vec<Option<(usize, &'g str)>> {
    let mut tree: Vec<Option<(usize, &str)>> = vec![None; outgoing.len()];
    if outgoing.is_empty() {
        return tree;
    }
    let mut seen = vec![false; outgoing.len()];
    seen[0] = true;
    let mut queue: Vec<usize> = vec![0];
    let mut head = 0;
    while head < queue.len() {
        let current = queue[head];
        head += 1;
        for &(via, target) in &outgoing[current] {
            if seen[target] {
                continue;
            }
            seen[target] = true;
            tree[target] = Some((current, via));
            queue.push(target);
        }
    }
    tree
}

/// The shortest firing sequence from the initial class to `target`: the classes along it,
/// `target` last, and the transitions between them.
fn path_to(tree: &[Option<(usize, &str)>], target: usize) -> (Vec<usize>, Vec<String>) {
    let mut classes: Vec<usize> = Vec::new();
    let mut transitions: Vec<String> = Vec::new();
    let mut current = target;
    loop {
        classes.push(current);
        match tree[current] {
            Some((parent, via)) => {
                transitions.push(via.to_string());
                current = parent;
            }
            None => break,
        }
    }
    classes.reverse();
    transitions.reverse();
    (classes, transitions)
}

struct Frame<'g> {
    node: usize,
    next: usize,
    /// The transition that entered this frame's class from the one below it.
    via: Option<&'g str>,
}

/// A reachable cycle as a lasso (the shortest stem to its entry class, then the loop), or
/// `None` when the explored graph has none. An iterative depth-first search: a graph deep
/// enough to matter would overflow a recursive one.
fn find_cycle(
    graph: &StateClassGraph,
    outgoing: &[Vec<(&str, usize)>],
    tree: &[Option<(usize, &str)>],
) -> Option<Witness> {
    if outgoing.is_empty() {
        return None;
    }
    let classes = graph.classes();
    // A class's position on the stack while it is open, `FINISHED` once it is done,
    // `UNSEEN` before it is reached.
    const UNSEEN: usize = usize::MAX;
    const FINISHED: usize = usize::MAX - 1;
    let mut position: Vec<usize> = vec![UNSEEN; outgoing.len()];
    position[0] = 0;
    let mut stack: Vec<Frame<'_>> = vec![Frame { node: 0, next: 0, via: None }];
    while let Some(top) = stack.last_mut() {
        let Some(&(via, target)) = outgoing[top.node].get(top.next) else {
            position[top.node] = FINISHED;
            stack.pop();
            continue;
        };
        top.next += 1;
        match position[target] {
            UNSEEN => {
                position[target] = stack.len();
                stack.push(Frame { node: target, next: 0, via: Some(via) });
            }
            FINISHED => {}
            at => {
                // A back edge: the stack from `target` up to the top, closed by `via`, is a
                // cycle.
                let lasso = &stack[at..];
                let (stem, stem_transitions) = path_to(tree, target);
                let mut cycle: Vec<String> =
                    lasso[1..].iter().map(|f| f.via.unwrap_or_default().to_string()).collect();
                cycle.push(via.to_string());
                let mut markings: Vec<MarkingState> =
                    stem.iter().map(|&c| classes[c].marking.clone()).collect();
                markings.extend(lasso[1..].iter().map(|f| classes[f.node].marking.clone()));
                markings.push(classes[target].marking.clone());
                let cycle_start = stem_transitions.len();
                let detail = format!("a run can repeat {} forever without coming to rest", cycle.join(" → "));
                let mut transitions = stem_transitions;
                transitions.extend(cycle);
                return Some(Witness {
                    kind: ContractViolationKind::Termination,
                    subject: "termination".to_string(),
                    detail,
                    transitions,
                    markings,
                    cycle_start: Some(cycle_start),
                    confirmed: true,
                });
            }
        }
    }
    None
}
