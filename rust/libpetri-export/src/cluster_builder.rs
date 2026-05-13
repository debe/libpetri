//! Builds nested `subgraph cluster_*` blocks per
//! `spec/11-modular-composition.md` **MOD-040** and `spec/09-export.md`
//! **EXP-016**.
//!
//! Mirrors `org.libpetri.export.ClusterBuilder` (Java) and
//! `typescript/src/export/cluster-builder.ts` (TypeScript) line-for-line so
//! cross-language byte-parity holds.
//!
//! Given a flat list of nodes and edges plus a `nodeId -> prefix` map
//! produced during mapping, this partitioner:
//!
//! 1. Walks every distinct prefix to produce the cluster tree (nested
//!    [`Subgraph`] entries).
//! 2. Routes each node into the deepest cluster whose prefix equals the
//!    node's prefix; nodes without a prefix stay at the top level.
//! 3. Routes each edge into the deepest cluster that contains **both**
//!    endpoints; edges crossing cluster boundaries (or with at least one
//!    top-level endpoint) stay at the top level so Graphviz routes them
//!    correctly without truncating cluster boxes.
//! 4. Applies a default cluster style (rounded, dashed, light fill).

use std::collections::HashMap;

use crate::graph::{GraphEdge, GraphNode, Subgraph};
use crate::mapper::sanitize;
use crate::subnet_prefixes::parent_of;

/// Result of partitioning nodes/edges into a clustered hierarchy.
pub struct Partition {
    pub top_level_nodes: Vec<GraphNode>,
    pub top_level_edges: Vec<GraphEdge>,
    pub top_level_subgraphs: Vec<Subgraph>,
}

/// Default cluster styling (per [EXP-016] visual contract). Returned as a
/// `Vec<(K, V)>` because the renderer iterates these in order — must match
/// the Java `LinkedHashMap` and TS object-literal insertion order
/// (`style → bgcolor → penwidth`) for byte-parity.
pub fn default_cluster_attrs() -> Vec<(String, String)> {
    vec![
        ("style".into(), "rounded,dashed".into()),
        ("bgcolor".into(), "#FAFAFA".into()),
        ("penwidth".into(), "1.5".into()),
    ]
}

/// Mutable accumulator threaded through the partition pass.
struct MutableCluster {
    nodes: Vec<GraphNode>,
    edges: Vec<GraphEdge>,
    child_prefixes: Vec<String>,
}

impl MutableCluster {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            child_prefixes: Vec::new(),
        }
    }
}

/// Partitions nodes and edges into a cluster hierarchy. Mutates neither
/// input collection.
pub fn partition(
    nodes: Vec<GraphNode>,
    edges: Vec<GraphEdge>,
    node_id_to_prefix: &HashMap<String, String>,
) -> Partition {
    // Fast path: no prefixes => no clusters. Preserves byte-equal output for
    // flat (non-composed) nets.
    if node_id_to_prefix.is_empty() {
        return Partition {
            top_level_nodes: nodes,
            top_level_edges: edges,
            top_level_subgraphs: Vec::new(),
        };
    }

    // Step 1: walk every prefix to produce the cluster tree shape. Use a
    // Vec to track insertion order (deterministic per [EXP-014]) plus a
    // HashSet for O(1) membership.
    let mut prefix_order: Vec<String> = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();

    // Insertion order: deterministically follow node iteration order. Walk
    // node ids in the order they appear in `nodes`, then look up their
    // prefix. This avoids depending on HashMap iteration order.
    for node in &nodes {
        if let Some(prefix) = node_id_to_prefix.get(&node.id) {
            register_prefix_chain(prefix, &mut prefix_order, &mut seen);
        }
    }

    // Maps prefix -> mutable cluster state. We index back into
    // `prefix_order` for deterministic iteration.
    let mut prefix_state: HashMap<String, MutableCluster> = HashMap::new();
    for prefix in &prefix_order {
        prefix_state.insert(prefix.clone(), MutableCluster::new());
    }
    // Wire parent -> child relationships in the order parents were
    // discovered.
    for prefix in &prefix_order {
        if let Some(parent) = parent_of(prefix) {
            prefix_state
                .get_mut(parent)
                .expect("parent prefix registered before child")
                .child_prefixes
                .push(prefix.clone());
        }
    }

    // Step 2: route nodes into their deepest cluster.
    let mut top_level_nodes: Vec<GraphNode> = Vec::new();
    for node in nodes {
        if let Some(prefix) = node_id_to_prefix.get(&node.id) {
            prefix_state
                .get_mut(prefix)
                .expect("node prefix registered above")
                .nodes
                .push(node);
        } else {
            top_level_nodes.push(node);
        }
    }

    // Step 3: route edges into the deepest cluster containing both
    // endpoints. Cross-cluster edges stay at the top level.
    let mut top_level_edges: Vec<GraphEdge> = Vec::new();
    for edge in edges {
        let from_prefix = node_id_to_prefix.get(&edge.from).map(String::as_str);
        let to_prefix = node_id_to_prefix.get(&edge.to).map(String::as_str);
        match deepest_common_prefix(from_prefix, to_prefix) {
            Some(common) => prefix_state
                .get_mut(common)
                .expect("common prefix registered above")
                .edges
                .push(edge),
            None => top_level_edges.push(edge),
        }
    }

    // Step 4: assemble Subgraph values bottom-up so children are built
    // before they're consumed by parents. Iterate `prefix_order` in
    // reverse — parents were inserted before children in
    // `register_prefix_chain` so reverse order is deepest-first.
    let mut built: HashMap<String, Subgraph> = HashMap::new();
    for prefix in prefix_order.iter().rev() {
        let state = prefix_state
            .remove(prefix)
            .expect("each prefix processed once");
        // Build child Subgraphs in their original insertion order. The
        // `child_prefixes` list was filled in `register_prefix_chain`
        // order (oldest -> newest), so it already matches the desired
        // visit order; no extra reverse needed.
        let mut children: Vec<Subgraph> = Vec::with_capacity(state.child_prefixes.len());
        for child_prefix in &state.child_prefixes {
            if let Some(child) = built.remove(child_prefix) {
                children.push(child);
            }
        }
        let subgraph = Subgraph {
            id: sanitize(prefix),
            label: Some(prefix.clone()),
            nodes: state.nodes,
            edges: state.edges,
            subgraphs: children,
            attrs: default_cluster_attrs(),
        };
        built.insert(prefix.clone(), subgraph);
    }

    // Top-level subgraphs are those whose prefix has no parent. Walk
    // prefix_order to preserve discovery order.
    let mut top_level_subgraphs: Vec<Subgraph> = Vec::new();
    for prefix in &prefix_order {
        if parent_of(prefix).is_none() {
            if let Some(sg) = built.remove(prefix) {
                top_level_subgraphs.push(sg);
            }
        }
    }

    Partition {
        top_level_nodes,
        top_level_edges,
        top_level_subgraphs,
    }
}

/// Walks a prefix root-to-leaf, registering every intermediate prefix in
/// `accumulator` (no-op when already present). Ensures parents are
/// inserted before children.
fn register_prefix_chain(
    prefix: &str,
    accumulator: &mut Vec<String>,
    seen: &mut std::collections::HashSet<String>,
) {
    if prefix.is_empty() {
        return;
    }
    let mut built = String::new();
    for seg in prefix.split('/') {
        if seg.is_empty() {
            continue;
        }
        if !built.is_empty() {
            built.push('/');
        }
        built.push_str(seg);
        if seen.insert(built.clone()) {
            accumulator.push(built.clone());
        }
    }
}

/// Returns the deepest prefix that is a (non-strict) ancestor of both
/// sides, or [`None`] when there is no shared cluster (top-level routing).
fn deepest_common_prefix<'a>(a: Option<&'a str>, b: Option<&'a str>) -> Option<&'a str> {
    let (a, b) = match (a, b) {
        (Some(a), Some(b)) => (a, b),
        _ => return None,
    };
    if a == b {
        return Some(a);
    }
    let a_segs: Vec<&str> = a.split('/').collect();
    let b_segs: Vec<&str> = b.split('/').collect();
    let mut matched = 0usize;
    let mut byte_len = 0usize;
    let min = a_segs.len().min(b_segs.len());
    for i in 0..min {
        if a_segs[i] != b_segs[i] {
            break;
        }
        if matched > 0 {
            byte_len += 1; // for the '/'
        }
        byte_len += a_segs[i].len();
        matched += 1;
    }
    if matched == 0 {
        None
    } else {
        Some(&a[..byte_len])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{ArrowHead, EdgeLineStyle, NodeShape};

    fn make_node(id: &str) -> GraphNode {
        GraphNode {
            id: id.into(),
            label: "".into(),
            shape: NodeShape::Circle,
            fill: Some("#FFFFFF".into()),
            stroke: Some("#333333".into()),
            penwidth: Some(1.5),
            semantic_id: None,
            style: None,
            height: None,
            width: Some(0.35),
            attrs: Vec::new(),
        }
    }

    fn make_edge(from: &str, to: &str) -> GraphEdge {
        GraphEdge {
            from: from.into(),
            to: to.into(),
            label: None,
            color: Some("#333333".into()),
            style: Some(EdgeLineStyle::Solid),
            arrowhead: Some(ArrowHead::Normal),
            penwidth: None,
            arc_type: None,
            attrs: Vec::new(),
        }
    }

    #[test]
    fn no_prefix_returns_flat() {
        let nodes = vec![make_node("p_a"), make_node("p_b")];
        let edges = vec![make_edge("p_a", "p_b")];
        let p = partition(nodes, edges, &HashMap::new());
        assert_eq!(p.top_level_nodes.len(), 2);
        assert_eq!(p.top_level_edges.len(), 1);
        assert_eq!(p.top_level_subgraphs.len(), 0);
    }

    #[test]
    fn single_prefix_groups_nodes_and_intra_edges() {
        let nodes = vec![make_node("p_inner_x"), make_node("p_inner_y")];
        let edges = vec![make_edge("p_inner_x", "p_inner_y")];
        let mut prefix = HashMap::new();
        prefix.insert("p_inner_x".to_string(), "inner".to_string());
        prefix.insert("p_inner_y".to_string(), "inner".to_string());
        let p = partition(nodes, edges, &prefix);
        assert_eq!(p.top_level_nodes.len(), 0);
        assert_eq!(p.top_level_edges.len(), 0);
        assert_eq!(p.top_level_subgraphs.len(), 1);
        assert_eq!(p.top_level_subgraphs[0].nodes.len(), 2);
        assert_eq!(p.top_level_subgraphs[0].edges.len(), 1);
    }

    #[test]
    fn cross_cluster_edge_stays_top_level() {
        let nodes = vec![make_node("p_a"), make_node("p_b")];
        let edges = vec![make_edge("p_a", "p_b")];
        let mut prefix = HashMap::new();
        prefix.insert("p_a".to_string(), "left".to_string());
        prefix.insert("p_b".to_string(), "right".to_string());
        let p = partition(nodes, edges, &prefix);
        assert_eq!(p.top_level_nodes.len(), 0);
        assert_eq!(p.top_level_edges.len(), 1);
        assert_eq!(p.top_level_subgraphs.len(), 2);
    }

    #[test]
    fn nested_prefixes_build_tree() {
        let nodes = vec![make_node("p_outer_x"), make_node("p_outer_inner_y")];
        let edges = vec![];
        let mut prefix = HashMap::new();
        prefix.insert("p_outer_x".to_string(), "outer".to_string());
        prefix.insert("p_outer_inner_y".to_string(), "outer/inner".to_string());
        let p = partition(nodes, edges, &prefix);
        assert_eq!(p.top_level_subgraphs.len(), 1);
        let outer = &p.top_level_subgraphs[0];
        assert_eq!(outer.nodes.len(), 1);
        assert_eq!(outer.subgraphs.len(), 1);
        assert_eq!(outer.subgraphs[0].nodes.len(), 1);
    }
}
