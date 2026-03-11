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
            label: String::new(),
            shape,
            fill: Some(style.fill.to_string()),
            stroke: Some(style.stroke.to_string()),
            penwidth: Some(style.penwidth),
            semantic_id: Some(name.to_string()),
            style: style.style.map(|s| s.to_string()),
            height: style.height,
            width: style.width,
            attrs: vec![
                ("xlabel".into(), name.to_string()),
                ("fixedsize".into(), "true".into()),
            ],
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
            height: styles::TRANSITION.height,
            width: styles::TRANSITION.width,
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
                penwidth: styles::INPUT_EDGE.penwidth,
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
                penwidth: styles::INHIBITOR_EDGE.penwidth,
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
                label: Some("read".into()),
                color: Some(styles::READ_EDGE.color.to_string()),
                style: Some(EdgeLineStyle::Dashed),
                arrowhead: Some(ArrowHead::Normal),
                penwidth: styles::READ_EDGE.penwidth,
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
                label: Some("reset".into()),
                color: Some(styles::RESET_EDGE.color.to_string()),
                style: Some(EdgeLineStyle::Bold),
                arrowhead: Some(ArrowHead::Normal),
                penwidth: styles::RESET_EDGE.penwidth,
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
    let mut parts = vec![t.name().to_string()];

    if config.show_intervals && *t.timing() != libpetri_core::timing::Timing::Immediate {
        let earliest = t.timing().earliest();
        let latest = t.timing().latest();
        if latest < libpetri_core::timing::MAX_DURATION_MS {
            parts.push(format!("[{earliest}, {latest}]ms"));
        } else {
            parts.push(format!("[{earliest}, \u{221e})ms"));
        }
    }

    if config.show_priority && t.priority() != 0 {
        parts.push(format!("prio={}", t.priority()));
    }

    parts.join(" ")
}

fn input_label(spec: &In) -> Option<String> {
    match spec {
        In::One { .. } => None,
        In::Exactly { count, .. } => Some(format!("\u{00d7}{count}")),
        In::All { .. } => Some("*".to_string()),
        In::AtLeast { minimum, .. } => Some(format!("\u{2265}{minimum}")),
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
                penwidth: styles::OUTPUT_EDGE.penwidth,
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
            for child in children {
                let branch_label = infer_branch_label(child);
                output_edges_with_label(t_id, child, branch_label.as_deref(), edges);
            }
        }
        Out::Timeout { after_ms, child } => {
            let label = format!("\u{23f1}{after_ms}ms");
            output_edges_with_label(t_id, child, Some(&label), edges);
        }
        Out::ForwardInput { from, to } => {
            let to_id = format!("p_{}", sanitize(to.name()));
            edges.push(GraphEdge {
                from: t_id.to_string(),
                to: to_id,
                label: Some(format!("\u{27f5}{}", from.name())),
                color: Some(styles::OUTPUT_EDGE.color.to_string()),
                style: Some(EdgeLineStyle::Dashed),
                arrowhead: Some(ArrowHead::Normal),
                penwidth: styles::OUTPUT_EDGE.penwidth,
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
                penwidth: styles::OUTPUT_EDGE.penwidth,
                arc_type: Some("output".into()),
                attrs: Vec::new(),
            });
        }
        Out::And(children) => {
            for child in children {
                output_edges_with_label(t_id, child, label, edges);
            }
        }
        Out::ForwardInput { from, to } => {
            let to_id = format!("p_{}", sanitize(to.name()));
            let fwd_label = match label {
                Some(l) => format!("{l} \u{27f5}{}", from.name()),
                None => format!("\u{27f5}{}", from.name()),
            };
            edges.push(GraphEdge {
                from: t_id.to_string(),
                to: to_id,
                label: Some(fwd_label),
                color: Some(styles::OUTPUT_EDGE.color.to_string()),
                style: Some(EdgeLineStyle::Dashed),
                arrowhead: Some(ArrowHead::Normal),
                penwidth: styles::OUTPUT_EDGE.penwidth,
                arc_type: Some("output".into()),
                attrs: Vec::new(),
            });
        }
        _ => {
            output_edges(t_id, out, &HashSet::new(), edges);
        }
    }
}

fn infer_branch_label(out: &Out) -> Option<String> {
    match out {
        Out::Place(p) => Some(p.name().to_string()),
        Out::Timeout { after_ms, .. } => Some(format!("\u{23f1}{after_ms}ms")),
        Out::ForwardInput { to, .. } => Some(to.name().to_string()),
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

        // Find end place (blue, doublecircle)
        let end_node = graph.nodes.iter().find(|n| n.id == "p_end").unwrap();
        assert_eq!(end_node.fill.as_deref(), Some(styles::END_PLACE.fill));
        assert_eq!(end_node.shape, NodeShape::DoubleCircle);
    }

    #[test]
    fn places_have_empty_label_and_xlabel() {
        let p1 = Place::<i32>::new("Start");
        let p2 = Place::<i32>::new("End");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());

        for node in &graph.nodes {
            if node.id.starts_with("p_") {
                assert_eq!(node.label, "", "Place label should be empty");
                let xlabel = node.attrs.iter().find(|(k, _)| k == "xlabel");
                assert!(xlabel.is_some(), "Place should have xlabel");
                let fixedsize = node.attrs.iter().find(|(k, _)| k == "fixedsize");
                assert_eq!(fixedsize.unwrap().1, "true");
            }
        }
    }

    #[test]
    fn transition_has_dimensions() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());

        let t_node = graph.nodes.iter().find(|n| n.id == "t_t1").unwrap();
        assert_eq!(t_node.height, Some(0.4));
        assert_eq!(t_node.width, Some(0.8));
    }

    #[test]
    fn input_labels_use_unicode() {
        use libpetri_core::input::{exactly, at_least};

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t = Transition::builder("t1")
            .input(exactly(3, &p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let graph = map_to_graph(&net, &DotConfig::default());
        let edge = &graph.edges[0];
        assert_eq!(edge.label.as_deref(), Some("\u{00d7}3"));

        let t2 = Transition::builder("t2")
            .input(at_least(2, &p1))
            .output(out_place(&p2))
            .build();
        let net2 = PetriNet::builder("test2").transition(t2).build();
        let graph2 = map_to_graph(&net2, &DotConfig::default());
        let edge2 = &graph2.edges[0];
        assert_eq!(edge2.label.as_deref(), Some("\u{2265}2"));
    }

    #[test]
    fn edge_penwidth_only_set_when_style_has_some() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());

        // Input/output edges should have no penwidth (styles have None)
        for edge in &graph.edges {
            assert_eq!(edge.penwidth, None, "input/output edges should have no penwidth");
        }
    }

    #[test]
    fn transition_label_space_separated() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("fire")
            .input(one(&p1))
            .output(out_place(&p2))
            .timing(libpetri_core::timing::Timing::Delayed { after_ms: 500 })
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());
        let t_node = graph.nodes.iter().find(|n| n.id == "t_fire").unwrap();
        assert_eq!(t_node.label, "fire [500, \u{221e})ms");
    }

    #[test]
    fn read_edge_has_label() {
        use libpetri_core::arc::read;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let cfg = Place::<i32>::new("cfg");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .read(read(&cfg))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());
        let read_edge = graph.edges.iter().find(|e| e.arc_type.as_deref() == Some("read")).unwrap();
        assert_eq!(read_edge.label.as_deref(), Some("read"));
    }

    #[test]
    fn reset_edge_has_label_and_penwidth() {
        use libpetri_core::arc::reset;

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let cache = Place::<i32>::new("cache");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .reset(reset(&cache))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());
        let reset_edge = graph.edges.iter().find(|e| e.arc_type.as_deref() == Some("reset")).unwrap();
        assert_eq!(reset_edge.label.as_deref(), Some("reset"));
        assert_eq!(reset_edge.penwidth, Some(2.0));
    }
}
