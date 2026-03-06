/// Computes all SCCs in a graph defined by node count and successor function.
/// Uses Tarjan's algorithm. O(V + E) time complexity.
///
/// Returns SCCs as vectors of node indices.
pub fn compute_sccs(
    node_count: usize,
    successors: impl Fn(usize) -> Vec<usize>,
) -> Vec<Vec<usize>> {
    let mut state = TarjanState {
        index_map: vec![None; node_count],
        lowlink: vec![0; node_count],
        on_stack: vec![false; node_count],
        stack: Vec::new(),
        sccs: Vec::new(),
        next_index: 0,
    };

    for node in 0..node_count {
        if state.index_map[node].is_none() {
            strong_connect(node, &successors, &mut state);
        }
    }

    state.sccs
}

/// Finds terminal (bottom) SCCs — SCCs with no outgoing edges to other SCCs.
pub fn find_terminal_sccs(
    node_count: usize,
    successors: impl Fn(usize) -> Vec<usize>,
) -> Vec<Vec<usize>> {
    let all_sccs = compute_sccs(node_count, &successors);

    // Build a lookup: node → SCC index
    let mut node_to_scc = vec![0usize; node_count];
    for (scc_idx, scc) in all_sccs.iter().enumerate() {
        for &node in scc {
            node_to_scc[node] = scc_idx;
        }
    }

    all_sccs
        .into_iter()
        .enumerate()
        .filter(|(scc_idx, scc)| {
            // Terminal if no node has a successor in a different SCC
            !scc.iter().any(|&node| {
                successors(node)
                    .iter()
                    .any(|&succ| node_to_scc[succ] != *scc_idx)
            })
        })
        .map(|(_, scc)| scc)
        .collect()
}

struct TarjanState {
    index_map: Vec<Option<usize>>,
    lowlink: Vec<usize>,
    on_stack: Vec<bool>,
    stack: Vec<usize>,
    sccs: Vec<Vec<usize>>,
    next_index: usize,
}

fn strong_connect(
    v: usize,
    successors: &impl Fn(usize) -> Vec<usize>,
    state: &mut TarjanState,
) {
    state.index_map[v] = Some(state.next_index);
    state.lowlink[v] = state.next_index;
    state.next_index += 1;
    state.stack.push(v);
    state.on_stack[v] = true;

    for w in successors(v) {
        if state.index_map[w].is_none() {
            strong_connect(w, successors, state);
            state.lowlink[v] = state.lowlink[v].min(state.lowlink[w]);
        } else if state.on_stack[w] {
            state.lowlink[v] = state.lowlink[v].min(state.index_map[w].unwrap());
        }
    }

    if state.lowlink[v] == state.index_map[v].unwrap() {
        let mut scc = Vec::new();
        loop {
            let w = state.stack.pop().unwrap();
            state.on_stack[w] = false;
            scc.push(w);
            if w == v {
                break;
            }
        }
        state.sccs.push(scc);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_cycle() {
        // A(0) -> B(1) -> C(2) -> A(0)
        let edges: Vec<Vec<usize>> = vec![vec![1], vec![2], vec![0]];
        let sccs = compute_sccs(3, |n| edges[n].clone());
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0].len(), 3);
    }

    #[test]
    fn linear_chain() {
        // A(0) -> B(1) -> C(2)
        let edges: Vec<Vec<usize>> = vec![vec![1], vec![2], vec![]];
        let sccs = compute_sccs(3, |n| edges[n].clone());
        assert_eq!(sccs.len(), 3);
        for scc in &sccs {
            assert_eq!(scc.len(), 1);
        }
    }

    #[test]
    fn multiple_sccs() {
        // Two cycles: {0,1} and {2,3}, 0 -> 2
        let edges: Vec<Vec<usize>> = vec![vec![1, 2], vec![0], vec![3], vec![2]];
        let sccs = compute_sccs(4, |n| edges[n].clone());
        assert_eq!(sccs.len(), 2);
    }

    #[test]
    fn single_node() {
        let sccs = compute_sccs(1, |_| vec![]);
        assert_eq!(sccs.len(), 1);
        assert!(sccs[0].contains(&0));
    }

    #[test]
    fn terminal_sccs() {
        // A(0) -> B(1) -> C(2) -> B(1), {B,C} is terminal
        let edges: Vec<Vec<usize>> = vec![vec![1], vec![2], vec![1]];
        let terminal = find_terminal_sccs(3, |n| edges[n].clone());
        assert_eq!(terminal.len(), 1);
        let scc = &terminal[0];
        assert!(scc.contains(&1));
        assert!(scc.contains(&2));
        assert!(!scc.contains(&0));
    }

    #[test]
    fn all_terminal_when_isolated() {
        // A(0) -> A(0), B(1) -> B(1)
        let edges: Vec<Vec<usize>> = vec![vec![0], vec![1]];
        let terminal = find_terminal_sccs(2, |n| edges[n].clone());
        assert_eq!(terminal.len(), 2);
    }

    #[test]
    fn empty_graph() {
        let sccs = compute_sccs(0, |_| vec![]);
        assert!(sccs.is_empty());

        let terminal = find_terminal_sccs(0, |_| vec![]);
        assert!(terminal.is_empty());
    }
}
