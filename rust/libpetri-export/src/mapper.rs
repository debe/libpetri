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
    graph
        .graph_attrs
        .push(("outputorder".into(), styles::OUTPUT_ORDER.into()));

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

        let node = GraphNode {
            id,
            label: String::new(),
            shape: shape_from_str(style.shape),
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
        let t_sanitized = sanitize(t.name());
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

        let reset_places: HashSet<String> = t
            .resets()
            .iter()
            .map(|r| r.place.name().to_string())
            .collect();
        let mut combined: HashSet<String> = HashSet::new();

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

        // Output edges + junction nodes
        if let Some(out_spec) = t.output_spec() {
            let mut ctx = EmitCtx {
                t_sanitized: &t_sanitized,
                reset_places: &reset_places,
                combined: &mut combined,
                nodes: &mut graph.nodes,
                edges: &mut graph.edges,
                counter: 0,
            };
            emit_output(out_spec, &t_id, None, &mut ctx);
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

        // Standalone reset edges (only those not already combined with an output)
        for r in t.resets() {
            if combined.contains(r.place.name()) {
                continue;
            }
            let to_id = format!("p_{}", sanitize(r.place.name()));
            graph.edges.push(GraphEdge {
                from: t_id.clone(),
                to: to_id,
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

fn shape_from_str(s: &str) -> NodeShape {
    match s {
        "circle" => NodeShape::Circle,
        "doublecircle" => NodeShape::DoubleCircle,
        "box" => NodeShape::Box,
        "diamond" => NodeShape::Diamond,
        "ellipse" => NodeShape::Ellipse,
        "point" => NodeShape::Point,
        "record" => NodeShape::Record,
        _ => NodeShape::Circle,
    }
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

/// Mutable per-transition state threaded through the recursive Out-tree walk.
///
/// `counter` starts at 0 and increments once per emitted junction (depth-first
/// pre-order). `combined` accumulates place names where a reset+output combination
/// short-circuited the standalone reset edge.
struct EmitCtx<'a> {
    t_sanitized: &'a str,
    reset_places: &'a HashSet<String>,
    combined: &'a mut HashSet<String>,
    nodes: &'a mut Vec<GraphNode>,
    edges: &'a mut Vec<GraphEdge>,
    counter: u32,
}

/// Emits output edges for an Out tree, inserting junction nodes for XOR/AND
/// groups with two or more children. Combined reset+output edges replace plain
/// output edges when a leaf place is also in `ctx.reset_places`.
fn emit_output(out: &Out, parent_id: &str, branch_label: Option<&str>, ctx: &mut EmitCtx<'_>) {
    match out {
        Out::One(p) => {
            let to_id = format!("p_{}", sanitize(p.name()));
            push_leaf_edge(parent_id, &to_id, p.name(), branch_label, ctx, false);
        }
        Out::Exactly { place, count } => {
            let to_id = format!("p_{}", sanitize(place.name()));
            let count_label = match branch_label {
                Some(l) => format!("{l} \u{00d7}{count}"),
                None => format!("\u{00d7}{count}"),
            };
            push_leaf_edge(parent_id, &to_id, place.name(), Some(&count_label), ctx, false);
        }
        Out::ForwardInput { from, to } => {
            let to_id = format!("p_{}", sanitize(to.name()));
            let fwd_label = match branch_label {
                Some(l) => format!("{l} \u{27f5}{}", from.name()),
                None => format!("\u{27f5}{}", from.name()),
            };
            push_leaf_edge(parent_id, &to_id, to.name(), Some(&fwd_label), ctx, true);
        }
        Out::And(children) => {
            emit_group("and", children, parent_id, branch_label, ctx);
        }
        Out::Xor(children) => {
            emit_group("xor", children, parent_id, branch_label, ctx);
        }
        Out::Timeout { after_ms, child } => {
            // Override any inherited branch_label: the timeout label fully
            // describes this branch (the XOR pre-inference resolves to the
            // same string).
            let timeout_label = format!("\u{23f1}{after_ms}ms");
            emit_output(child, parent_id, Some(&timeout_label), ctx);
        }
    }
}

fn emit_group(
    kind: &str,
    children: &[Out],
    parent_id: &str,
    branch_label: Option<&str>,
    ctx: &mut EmitCtx<'_>,
) {
    // Single-child groups collapse: pass through.
    if children.len() < 2 {
        if children.len() == 1 {
            emit_output(&children[0], parent_id, branch_label, ctx);
        }
        return;
    }

    // Insert junction node — diamond gateway with heavy ✕ / ✚ glyph as discriminator.
    let idx = ctx.counter;
    ctx.counter += 1;
    let junction_id = format!("j_{}__{kind}_{idx}", ctx.t_sanitized);
    let (style, label) = if kind == "xor" {
        (&styles::XOR_JUNCTION, "\u{2715}") // ✕
    } else {
        (&styles::AND_JUNCTION, "\u{271a}") // ✚
    };
    ctx.nodes.push(GraphNode {
        id: junction_id.clone(),
        label: label.to_string(),
        shape: NodeShape::Diamond,
        fill: Some(style.fill.to_string()),
        stroke: Some(style.stroke.to_string()),
        penwidth: Some(style.penwidth),
        semantic_id: Some(junction_id.clone()),
        style: style.style.map(|s| s.to_string()),
        height: style.height,
        width: style.width,
        attrs: vec![
            ("fixedsize".into(), "true".into()),
            ("fontsize".into(), "14".into()),
        ],
    });

    // Edge parent → junction (carries any inherited branch/timeout label).
    ctx.edges.push(GraphEdge {
        from: parent_id.to_string(),
        to: junction_id.clone(),
        label: branch_label.map(|s| s.to_string()),
        color: Some(styles::OUTPUT_EDGE.color.to_string()),
        style: Some(EdgeLineStyle::Solid),
        arrowhead: Some(ArrowHead::Normal),
        penwidth: styles::OUTPUT_EDGE.penwidth,
        arc_type: Some("output".into()),
        attrs: Vec::new(),
    });

    // Recurse children: XOR junction propagates per-branch labels; AND does not.
    for child in children {
        let child_label = if kind == "xor" {
            infer_branch_label(child)
        } else {
            None
        };
        emit_output(child, &junction_id, child_label.as_deref(), ctx);
    }
}

fn push_leaf_edge(
    from_id: &str,
    to_id: &str,
    place_name: &str,
    branch_label: Option<&str>,
    ctx: &mut EmitCtx<'_>,
    is_forward_input: bool,
) {
    if ctx.reset_places.contains(place_name) {
        ctx.combined.insert(place_name.to_string());
        ctx.edges.push(GraphEdge {
            from: from_id.to_string(),
            to: to_id.to_string(),
            label: Some("reset+out".into()),
            color: Some(styles::RESET_OUTPUT_EDGE.color.to_string()),
            style: Some(EdgeLineStyle::Bold),
            arrowhead: Some(ArrowHead::Normal),
            penwidth: styles::RESET_OUTPUT_EDGE.penwidth,
            arc_type: Some("reset-output".into()),
            attrs: Vec::new(),
        });
        return;
    }

    let style = if is_forward_input {
        EdgeLineStyle::Dashed
    } else {
        EdgeLineStyle::Solid
    };
    ctx.edges.push(GraphEdge {
        from: from_id.to_string(),
        to: to_id.to_string(),
        label: branch_label.map(|s| s.to_string()),
        color: Some(styles::OUTPUT_EDGE.color.to_string()),
        style: Some(style),
        arrowhead: Some(ArrowHead::Normal),
        penwidth: styles::OUTPUT_EDGE.penwidth,
        arc_type: Some("output".into()),
        attrs: Vec::new(),
    });
}

fn infer_branch_label(out: &Out) -> Option<String> {
    match out {
        Out::One(p) => Some(p.name().to_string()),
        Out::Exactly { place, count } => Some(format!("{}\u{00d7}{count}", place.name())),
        Out::Timeout { after_ms, .. } => Some(format!("\u{23f1}{after_ms}ms")),
        Out::ForwardInput { to, .. } => Some(to.name().to_string()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libpetri_core::input::one;
    use libpetri_core::output::out_one;
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
            .output(out_one(&p2))
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
            .output(out_one(&p_mid))
            .build();
        let t2 = Transition::builder("t2")
            .input(one(&p_mid))
            .output(out_one(&p_end))
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
            .output(out_one(&p2))
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
            .output(out_one(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());

        let t_node = graph.nodes.iter().find(|n| n.id == "t_t1").unwrap();
        assert_eq!(t_node.height, Some(0.4));
        assert_eq!(t_node.width, Some(0.8));
    }

    #[test]
    fn input_labels_use_unicode() {
        use libpetri_core::input::{at_least, exactly};

        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");

        let t = Transition::builder("t1")
            .input(exactly(3, &p1))
            .output(out_one(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let graph = map_to_graph(&net, &DotConfig::default());
        let edge = &graph.edges[0];
        assert_eq!(edge.label.as_deref(), Some("\u{00d7}3"));

        let t2 = Transition::builder("t2")
            .input(at_least(2, &p1))
            .output(out_one(&p2))
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
            .output(out_one(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());

        // Input/output edges should have no penwidth (styles have None)
        for edge in &graph.edges {
            assert_eq!(
                edge.penwidth, None,
                "input/output edges should have no penwidth"
            );
        }
    }

    #[test]
    fn transition_label_space_separated() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("fire")
            .input(one(&p1))
            .output(out_one(&p2))
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
            .output(out_one(&p2))
            .read(read(&cfg))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());
        let read_edge = graph
            .edges
            .iter()
            .find(|e| e.arc_type.as_deref() == Some("read"))
            .unwrap();
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
            .output(out_one(&p2))
            .reset(reset(&cache))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());
        let reset_edge = graph
            .edges
            .iter()
            .find(|e| e.arc_type.as_deref() == Some("reset"))
            .unwrap();
        assert_eq!(reset_edge.label.as_deref(), Some("reset"));
        assert_eq!(reset_edge.penwidth, Some(2.0));
    }

    #[test]
    fn xor_junction_with_branch_labels() {
        use libpetri_core::output::{out_one, xor};

        let p_in = Place::<i32>::new("In");
        let success = Place::<i32>::new("Success");
        let error = Place::<i32>::new("Error");
        let t = Transition::builder("Process")
            .input(one(&p_in))
            .output(xor(vec![out_one(&success), out_one(&error)]))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let graph = map_to_graph(&net, &DotConfig::default());

        let junction = graph
            .nodes
            .iter()
            .find(|n| n.id.starts_with("j_Process__xor_"))
            .expect("XOR junction should be emitted");
        assert_eq!(junction.shape, NodeShape::Diamond);
        assert_eq!(junction.label, "\u{2715}"); // ✕
        assert_eq!(junction.fill.as_deref(), Some("#FFFFFF"));
        assert_eq!(junction.stroke.as_deref(), Some("#333333"));
        let fontsize = junction.attrs.iter().find(|(k, _)| k == "fontsize");
        assert_eq!(fontsize.map(|(_, v)| v.as_str()), Some("14"));

        let to_success = graph.edges.iter().find(|e| e.to == "p_Success").unwrap();
        let to_error = graph.edges.iter().find(|e| e.to == "p_Error").unwrap();
        assert_eq!(to_success.from, junction.id);
        assert_eq!(to_error.from, junction.id);
        assert_eq!(to_success.label.as_deref(), Some("Success"));
        assert_eq!(to_error.label.as_deref(), Some("Error"));
    }

    #[test]
    fn and_junction_no_labels() {
        use libpetri_core::output::{and, out_one};

        let p_in = Place::<i32>::new("In");
        let a = Place::<i32>::new("A");
        let b = Place::<i32>::new("B");
        let t = Transition::builder("Fork")
            .input(one(&p_in))
            .output(and(vec![out_one(&a), out_one(&b)]))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let graph = map_to_graph(&net, &DotConfig::default());

        let junction = graph
            .nodes
            .iter()
            .find(|n| n.id.starts_with("j_Fork__and_"))
            .expect("AND junction should be emitted");
        assert_eq!(junction.shape, NodeShape::Diamond);
        assert_eq!(junction.label, "\u{271a}"); // ✚
        assert_eq!(junction.fill.as_deref(), Some("#FFFFFF"));
        assert_eq!(junction.stroke.as_deref(), Some("#333333"));
        let fontsize = junction.attrs.iter().find(|(k, _)| k == "fontsize");
        assert_eq!(fontsize.map(|(_, v)| v.as_str()), Some("14"));
        assert_eq!(junction.width, Some(0.3));

        let t_to_j: Vec<_> = graph
            .edges
            .iter()
            .filter(|e| e.from == "t_Fork" && e.to == junction.id)
            .collect();
        assert_eq!(t_to_j.len(), 1);

        let j_to_children: Vec<_> = graph
            .edges
            .iter()
            .filter(|e| e.from == junction.id && e.arc_type.as_deref() == Some("output"))
            .collect();
        assert_eq!(j_to_children.len(), 2);
        for e in j_to_children {
            assert!(e.label.is_none(), "AND junction edges should have no labels");
        }
    }

    #[test]
    fn single_child_and_collapses_no_junction() {
        use libpetri_core::output::{and, out_one};

        let p_in = Place::<i32>::new("In");
        let only = Place::<i32>::new("Only");
        let t = Transition::builder("SingleAnd")
            .input(one(&p_in))
            .output(and(vec![out_one(&only)]))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let graph = map_to_graph(&net, &DotConfig::default());

        let junctions: Vec<_> = graph.nodes.iter().filter(|n| n.id.starts_with("j_")).collect();
        assert!(junctions.is_empty(), "single-child AND should not emit a junction");

        let direct = graph.edges.iter().find(|e| e.from == "t_SingleAnd" && e.to == "p_Only");
        assert!(direct.is_some());
        assert_eq!(direct.unwrap().arc_type.as_deref(), Some("output"));
    }

    #[test]
    fn combines_reset_and_output_into_single_edge() {
        use libpetri_core::arc::reset;

        let p_in = Place::<i32>::new("In");
        let cache = Place::<i32>::new("Cache");
        let t = Transition::builder("Refresh")
            .input(one(&p_in))
            .output(out_one(&cache))
            .reset(reset(&cache))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let graph = map_to_graph(&net, &DotConfig::default());

        let edges_to_cache: Vec<_> = graph.edges.iter().filter(|e| e.to == "p_Cache").collect();
        assert_eq!(edges_to_cache.len(), 1);
        let combined = edges_to_cache[0];
        assert_eq!(combined.arc_type.as_deref(), Some("reset-output"));
        assert_eq!(combined.label.as_deref(), Some("reset+out"));
        assert_eq!(combined.color.as_deref(), Some("#fd7e14"));
        assert_eq!(combined.style, Some(EdgeLineStyle::Bold));
        assert_eq!(combined.penwidth, Some(2.0));

        let standalone = graph
            .edges
            .iter()
            .find(|e| e.arc_type.as_deref() == Some("reset") && e.to == "p_Cache");
        assert!(standalone.is_none());
    }

    #[test]
    fn combines_reset_and_output_through_xor_junction() {
        use libpetri_core::arc::reset;
        use libpetri_core::output::{out_one, xor};

        let p_in = Place::<i32>::new("In");
        let ok = Place::<i32>::new("Ok");
        let cache = Place::<i32>::new("Cache");
        let t = Transition::builder("Try")
            .input(one(&p_in))
            .output(xor(vec![out_one(&ok), out_one(&cache)]))
            .reset(reset(&cache))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let graph = map_to_graph(&net, &DotConfig::default());

        let junction = graph
            .nodes
            .iter()
            .find(|n| n.id.starts_with("j_Try__xor_"))
            .expect("XOR junction should be emitted");

        let to_cache = graph.edges.iter().find(|e| e.to == "p_Cache").unwrap();
        assert_eq!(to_cache.from, junction.id);
        assert_eq!(to_cache.arc_type.as_deref(), Some("reset-output"));
        assert_eq!(to_cache.label.as_deref(), Some("reset+out"));

        let to_ok = graph.edges.iter().find(|e| e.to == "p_Ok").unwrap();
        assert_eq!(to_ok.arc_type.as_deref(), Some("output"));
        assert_eq!(to_ok.label.as_deref(), Some("Ok"));
    }

    #[test]
    fn deterministic_junction_ids_in_depth_first_order() {
        use libpetri_core::output::{and, out_one, xor};

        let p_in = Place::<i32>::new("In");
        let a = Place::<i32>::new("A");
        let b = Place::<i32>::new("B");
        let c = Place::<i32>::new("C");
        let d = Place::<i32>::new("D");
        // AND( XOR(a, b), XOR(c, d) )
        let t = Transition::builder("Nested")
            .input(one(&p_in))
            .output(and(vec![
                xor(vec![out_one(&a), out_one(&b)]),
                xor(vec![out_one(&c), out_one(&d)]),
            ]))
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let graph = map_to_graph(&net, &DotConfig::default());

        let ids: Vec<_> = graph
            .nodes
            .iter()
            .filter(|n| n.id.starts_with("j_Nested__"))
            .map(|n| n.id.as_str())
            .collect();
        assert_eq!(
            ids,
            vec!["j_Nested__and_0", "j_Nested__xor_1", "j_Nested__xor_2"]
        );
    }

    /// EXP-014 AC#2: repeated exports of the same net produce byte-identical DOT.
    #[test]
    fn round_trip_export_is_byte_identical() {
        use crate::dot_renderer::render_dot;
        use libpetri_core::arc::reset;
        use libpetri_core::output::{and, out_one, xor};

        let p_in = Place::<i32>::new("In");
        let a = Place::<i32>::new("A");
        let b = Place::<i32>::new("B");
        let c = Place::<i32>::new("C");
        let d = Place::<i32>::new("D");
        let cache = Place::<i32>::new("Cache");

        // Nested junctions + reset+output covers the full range of EXP-012/013/014 paths.
        let nested = Transition::builder("Nested")
            .input(one(&p_in))
            .output(and(vec![
                xor(vec![out_one(&a), out_one(&b)]),
                xor(vec![out_one(&c), out_one(&d)]),
            ]))
            .build();
        let refresh = Transition::builder("RefreshCache")
            .input(one(&a))
            .output(out_one(&cache))
            .reset(reset(&cache))
            .build();
        let net = PetriNet::builder("Stable")
            .transition(nested)
            .transition(refresh)
            .build();

        let first = render_dot(&map_to_graph(&net, &DotConfig::default()));
        let second = render_dot(&map_to_graph(&net, &DotConfig::default()));
        assert_eq!(
            first, second,
            "DOT output must be byte-identical across repeated exports"
        );
    }

    #[test]
    fn graph_attrs_include_outputorder() {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_one(&p2))
            .build();
        let net = PetriNet::builder("test").transition(t).build();

        let graph = map_to_graph(&net, &DotConfig::default());
        let find = |key: &str| {
            graph
                .graph_attrs
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| v.as_str())
        };
        assert_eq!(find("outputorder"), Some("edgesfirst"));
    }
}
