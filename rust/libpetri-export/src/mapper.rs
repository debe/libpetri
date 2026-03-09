use std::collections::HashSet;

use libpetri_core::input::In;
use libpetri_core::output::{self, Out};
use libpetri_core::petri_net::PetriNet;

use crate::graph::*;
use crate::styles;

/// Configuration for DOT export.
#[derive(Debug, Clone)]
pub struct DotConfig {
    pub direction: RankDir,
    pub show_types: bool,
    pub show_intervals: bool,
    pub show_priority: bool,
    pub environment_places: HashSet<String>,
}

impl Default for DotConfig {
    fn default() -> Self {
        Self {
            direction: RankDir::TopToBottom,
            show_types: true,
            show_intervals: true,
            show_priority: true,
            environment_places: HashSet::new(),
        }
    }
}

/// Sanitize a name for use as a DOT identifier.
pub fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Place classification for visual styling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PlaceCategory {
    Start,
    End,
    Environment,
    Regular,
}

/// Maps a PetriNet to a format-agnostic Graph.
pub fn map_to_graph(net: &PetriNet, config: &DotConfig) -> Graph {
    let mut graph = Graph::new(net.name());
    graph.rankdir = config.direction;

    // Graph attributes
    graph
        .graph_attrs
        .push(("nodesep".into(), styles::NODESEP.to_string()));
    graph
        .graph_attrs
        .push(("ranksep".into(), styles::RANKSEP.to_string()));
    graph
        .graph_attrs
        .push(("forcelabels".into(), styles::FORCE_LABELS.into()));
    graph
        .graph_attrs
        .push(("overlap".into(), styles::OVERLAP.into()));

    // Node defaults
    graph
        .node_defaults
        .push(("fontname".into(), styles::FONT_FAMILY.into()));
    graph
        .node_defaults
        .push(("fontsize".into(), styles::FONT_NODE_SIZE.to_string()));

    // Edge defaults
    graph
        .edge_defaults
        .push(("fontname".into(), styles::FONT_FAMILY.into()));
    graph
        .edge_defaults
        .push(("fontsize".into(), styles::FONT_EDGE_SIZE.to_string()));

    // Analyze places
    let (has_incoming, has_outgoing) = analyze_places(net);

    // Create place nodes
    for place_ref in net.places() {
        let name = place_ref.name();
        let id = format!("p_{}", sanitize(name));
        let category = place_category(
            name,
            has_incoming.contains(name),
            has_outgoing.contains(name),
            config.environment_places.contains(name),
        );
        let style = match category {
            PlaceCategory::Start => &styles::START_PLACE,
            PlaceCategory::End => &styles::END_PLACE,
            PlaceCategory::Environment => &styles::ENVIRONMENT_PLACE,
            PlaceCategory::Regular => &styles::PLACE,
        };

        let shape = match style.shape {
            "circle" => NodeShape::Circle,
            "doublecircle" => NodeShape::DoubleCircle,
            _ => NodeShape::Circle,
        };

        let node = GraphNode {
            id,
            label: name.to_string(),
            shape,
            fill: Some(style.fill.to_string()),
            stroke: Some(style.stroke.to_string()),
            penwidth: Some(style.penwidth),
            semantic_id: Some(name.to_string()),
            style: style.style.map(|s| s.to_string()),
            height: None,
            width: None,
            attrs: Vec::new(),
        };
        graph.nodes.push(node);
    }

    // Create transition nodes and edges
    for t in net.transitions() {
        let t_id = format!("t_{}", sanitize(t.name()));
        let label = transition_label(t, config);

        graph.nodes.push(GraphNode {
            id: t_id.clone(),
            label,
            shape: NodeShape::Box,
            fill: Some(styles::TRANSITION.fill.to_string()),
            stroke: Some(styles::TRANSITION.stroke.to_string()),
            penwidth: Some(styles::TRANSITION.penwidth),
            semantic_id: Some(t.name().to_string()),
            style: None,
            height: None,
            width: None,
            attrs: Vec::new(),
        });

        // Input edges
        for in_spec in t.input_specs() {
            let from_id = format!("p_{}", sanitize(in_spec.place_name()));
            let label = input_label(in_spec);

            graph.edges.push(GraphEdge {
                from: from_id,
                to: t_id.clone(),
                label,
                color: Some(styles::INPUT_EDGE.color.to_string()),
                style: Some(EdgeLineStyle::Solid),
                arrowhead: Some(ArrowHead::Normal),
                penwidth: Some(styles::INPUT_EDGE.penwidth),
                arc_type: Some("input".into()),
                attrs: Vec::new(),
            });
        }

        // Output edges
        if let Some(out_spec) = t.output_spec() {
            let reset_places: HashSet<&str> = t.resets().iter().map(|r| r.place.name()).collect();
            output_edges(&t_id, out_spec, &reset_places, &mut graph.edges);
        }

        // Inhibitor edges
        for inh in t.inhibitors() {
            let from_id = format!("p_{}", sanitize(inh.place.name()));
            graph.edges.push(GraphEdge {
                from: from_id,
                to: t_id.clone(),
                label: None,
                color: Some(styles::INHIBITOR_EDGE.color.to_string()),
                style: Some(EdgeLineStyle::Solid),
                arrowhead: Some(ArrowHead::Odot),
                penwidth: Some(styles::INHIBITOR_EDGE.penwidth),
                arc_type: Some("inhibitor".into()),
                attrs: Vec::new(),
            });
        }

        // Read edges
        for r in t.reads() {
            let from_id = format!("p_{}", sanitize(r.place.name()));
            graph.edges.push(GraphEdge {
                from: from_id,
                to: t_id.clone(),
                label: None,
                color: Some(styles::READ_EDGE.color.to_string()),
                style: Some(EdgeLineStyle::Dashed),
                arrowhead: Some(ArrowHead::Normal),
                penwidth: Some(styles::READ_EDGE.penwidth),
                arc_type: Some("read".into()),
                attrs: Vec::new(),
            });
        }

        // Reset edges (only those not overlapping with outputs)
        for r in t.resets() {
            if t.output_places().contains(&r.place) {
                continue; // suppress if already an output
            }
            let from_id = format!("p_{}", sanitize(r.place.name()));
            graph.edges.push(GraphEdge {
                from: t_id.clone(),
                to: from_id,
                label: None,
                color: Some(styles::RESET_EDGE.color.to_string()),
                style: Some(EdgeLineStyle::Bold),
                arrowhead: Some(ArrowHead::Normal),
                penwidth: Some(styles::RESET_EDGE.penwidth),
                arc_type: Some("reset".into()),
                attrs: Vec::new(),
            });
        }
    }

    graph
}

fn analyze_places(net: &PetriNet) -> (HashSet<String>, HashSet<String>) {
    let mut has_incoming = HashSet::new();
    let mut has_outgoing = HashSet::new();

    for t in net.transitions() {
        // Input arcs: place -> transition (place has outgoing)
        for spec in t.input_specs() {
            has_outgoing.insert(spec.place_name().to_string());
        }
        // Output arcs: transition -> place (place has incoming)
        if let Some(out) = t.output_spec() {
            for p in output::all_places(out) {
                has_incoming.insert(p.name().to_string());
            }
        }
    }

    (has_incoming, has_outgoing)
}

fn place_category(
    _name: &str,
    has_incoming: bool,
    has_outgoing: bool,
    is_environment: bool,
) -> PlaceCategory {
    if is_environment {
        PlaceCategory::Environment
    } else if !has_incoming && has_outgoing {
        PlaceCategory::Start
    } else if has_incoming && !has_outgoing {
        PlaceCategory::End
    } else {
        PlaceCategory::Regular
    }
}

fn transition_label(t: &libpetri_core::transition::Transition, config: &DotConfig) -> String {
    let mut label = t.name().to_string();

    if config.show_intervals && *t.timing() != libpetri_core::timing::Timing::Immediate {
        let earliest = t.timing().earliest();
        let latest = t.timing().latest();
        if latest < libpetri_core::timing::MAX_DURATION_MS {
            label.push_str(&format!("\n[{earliest}, {latest}]"));
        } else {
            label.push_str(&format!("\n[{earliest}, \u{221e})"));
        }
    }

    if config.show_priority && t.priority() != 0 {
        label.push_str(&format!("\nP={}", t.priority()));
    }

    label
}

fn input_label(spec: &In) -> Option<String> {
    match spec {
        In::One { .. } => None,
        In::Exactly { count, .. } => Some(count.to_string()),
        In::All { .. } => Some("*".to_string()),
        In::AtLeast { minimum, .. } => Some(format!("{minimum}+")),
    }
}

#[allow(clippy::only_used_in_recursion)]
fn output_edges(t_id: &str, out: &Out, reset_places: &HashSet<&str>, edges: &mut Vec<GraphEdge>) {
    match out {
        Out::Place(p) => {
            let to_id = format!("p_{}", sanitize(p.name()));
            edges.push(GraphEdge {
                from: t_id.to_string(),
                to: to_id,
                label: None,
                color: Some(styles::OUTPUT_EDGE.color.to_string()),
                style: Some(EdgeLineStyle::Solid),
                arrowhead: Some(ArrowHead::Normal),
                penwidth: Some(styles::OUTPUT_EDGE.penwidth),
                arc_type: Some("output".into()),
                attrs: Vec::new(),
            });
        }
        Out::And(children) => {
            for child in children {
                output_edges(t_id, child, reset_places, edges);
            }
        }
        Out::Xor(children) => {
            for (i, child) in children.iter().enumerate() {
                let branch_label = infer_branch_label(child).unwrap_or_else(|| format!("b{i}"));
                output_edges_with_label(t_id, child, Some(&branch_label), edges);
            }
        }
        Out::Timeout { after_ms: _, child } => {
            output_edges(t_id, child, reset_places, edges);
            // The timeout itself is handled by the action
        }
        Out::ForwardInput { from, to } => {
            let to_id = format!("p_{}", sanitize(to.name()));
            edges.push(GraphEdge {
                from: t_id.to_string(),
                to: to_id,
                label: Some(format!("\u{21a9} {}", from.name())),
                color: Some(styles::OUTPUT_EDGE.color.to_string()),
                style: Some(EdgeLineStyle::Dashed),
                arrowhead: Some(ArrowHead::Normal),
                penwidth: Some(styles::OUTPUT_EDGE.penwidth),
                arc_type: Some("output".into()),
                attrs: Vec::new(),
            });
        }
    }
}

fn output_edges_with_label(t_id: &str, out: &Out, label: Option<&str>, edges: &mut Vec<GraphEdge>) {
    match out {
        Out::Place(p) => {
            let to_id = format!("p_{}", sanitize(p.name()));
            edges.push(GraphEdge {
                from: t_id.to_string(),
                to: to_id,
                label: label.map(|s| s.to_string()),
                color: Some(styles::OUTPUT_EDGE.color.to_string()),
                style: Some(EdgeLineStyle::Solid),
                arrowhead: Some(ArrowHead::Normal),
                penwidth: Some(styles::OUTPUT_EDGE.penwidth),
                arc_type: Some("output".into()),
                attrs: Vec::new(),
            });
        }
        Out::And(children) => {
            for child in children {
                output_edges_with_label(t_id, child, label, edges);
            }
        }
        _ => {
            output_edges(t_id, out, &HashSet::new(), edges);
        }
    }
}

fn infer_branch_label(out: &Out) -> Option<String> {
    match out {
        Out::Place(p) => Some(p.name().to_string()),
        _ => None,
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
    fn sanitize_names() {
        assert_eq!(sanitize("hello"), "hello");
        assert_eq!(sanitize("hello world"), "hello_world");
        assert_eq!(sanitize("a-b.c"), "a_b_c");
    }

    #[test]
    fn basic_graph_mapping() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());

        // 2 place nodes + 1 transition node
        assert_eq!(graph.nodes.len(), 3);
        // 1 input edge + 1 output edge
        assert_eq!(graph.edges.len(), 2);
    }

    #[test]
    fn place_categories() {
        let p_start = Place::<i32>::new("start");
        let p_mid = Place::<i32>::new("mid");
        let p_end = Place::<i32>::new("end");

        let t1 = Transition::builder("t1")
            .input(one(&p_start))
            .output(out_place(&p_mid))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p_mid))
            .output(out_place(&p_end))
            .build();

        let net = PetriNet::builder("test").transitions([t1, t2]).build();

        let graph = map_to_graph(&net, &DotConfig::default());

        // Find start place (green)
        let start_node = graph.nodes.iter().find(|n| n.id == "p_start").unwrap();
        assert_eq!(start_node.fill.as_deref(), Some(styles::START_PLACE.fill));

        // Find end place (blue)
        let end_node = graph.nodes.iter().find(|n| n.id == "p_end").unwrap();
        assert_eq!(end_node.fill.as_deref(), Some(styles::END_PLACE.fill));
    }
}
