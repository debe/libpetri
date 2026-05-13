//! Renders a [`Graph`] to a DOT (Graphviz) string.
//!
//! Pure function with zero Petri net knowledge — operates solely on the
//! format-agnostic [`Graph`] model.
//!
//! ## Cross-language byte-parity
//!
//! Output is byte-identical to the Java (`org.libpetri.export.DotRenderer`)
//! and TypeScript (`typescript/src/export/dot-renderer.ts`) renderers per
//! [EXP-014]. The contract is exercised by
//! `scripts/cross-lang-dot-parity.sh` which builds the canonical
//! producer/buffer/consumer pipeline in all three languages and diffs the
//! resulting DOT.
//!
//! Key conventions (must match across languages):
//! - 4-space indentation
//! - Attribute values quoted unless purely numeric (`/^-?\d+(\.\d+)?$/`)
//! - Subgraph ids prefixed with `cluster_` at render time
//! - Node attribute order: `label, shape, style, fillcolor, color,
//!   penwidth, height, width, ...extra`
//! - Edge attribute order: `color, style, arrowhead, label, penwidth,
//!   ...extra`
//! - `style="filled"` is auto-emitted whenever a `fill` is present, with
//!   any extra style appended as `style="filled,<extra>"`
//! - Numbers: integers strip the trailing `.0` (e.g. `2.0` -> `2`,
//!   `0.4` -> `0.4`)

use crate::graph::*;

const INDENT_STEP: &str = "    "; // 4 spaces per level

/// DOT keywords that must be quoted when used as identifiers.
const DOT_KEYWORDS: &[&str] = &["graph", "digraph", "subgraph", "node", "edge", "strict"];

/// Renders a [`Graph`] to a DOT format string per the cross-language
/// byte-parity contract documented at the module level.
pub fn render_dot(graph: &Graph) -> String {
    let mut lines: Vec<String> = Vec::new();

    lines.push(format!("digraph {} {{", quote_id(&graph.name)));

    // Rankdir + graph attrs.
    lines.push(format!("{INDENT_STEP}rankdir={};", graph.rankdir.as_dot()));
    for (k, v) in &graph.graph_attrs {
        lines.push(format!("{INDENT_STEP}{k}={};", quote_attr(v)));
    }

    // Node defaults.
    if !graph.node_defaults.is_empty() {
        lines.push(format!(
            "{INDENT_STEP}node [{}];",
            format_simple_attrs(&graph.node_defaults)
        ));
    }

    // Edge defaults.
    if !graph.edge_defaults.is_empty() {
        lines.push(format!(
            "{INDENT_STEP}edge [{}];",
            format_simple_attrs(&graph.edge_defaults)
        ));
    }

    lines.push(String::new());

    // Subgraphs (top level).
    for sg in &graph.subgraphs {
        render_subgraph(sg, INDENT_STEP, &mut lines);
        lines.push(String::new());
    }

    // Top-level nodes.
    for node in &graph.nodes {
        lines.push(format!("{INDENT_STEP}{}", render_node(node)));
    }

    if !graph.nodes.is_empty() {
        lines.push(String::new());
    }

    // Top-level edges.
    for edge in &graph.edges {
        lines.push(format!("{INDENT_STEP}{}", render_edge(edge)));
    }

    lines.push("}".to_string());
    lines.join("\n")
}

// ============================================================
//  Node / edge / subgraph rendering
// ============================================================

/// Renders one node line. Attribute order is fixed for byte-parity:
/// `label, shape, style, fillcolor, color, penwidth, height, width,
/// ...extra-attrs`.
fn render_node(node: &GraphNode) -> String {
    let mut attrs: Vec<(String, AttrValue)> = Vec::new();

    attrs.push(("label".into(), AttrValue::Bare(node.label.clone())));
    attrs.push(("shape".into(), AttrValue::Bare(node.shape.as_dot().into())));

    // Style: auto-emit "filled" when a fill is present, optionally compose
    // with the node's extra style attribute. This mirrors the Java/TS
    // renderer (which always emits `style="filled"` for nodes with a fill).
    let style_value = if node.fill.is_some() {
        if let Some(ref extra) = node.style {
            AttrValue::PreQuoted(format!("\"filled,{extra}\""))
        } else {
            AttrValue::Bare("filled".into())
        }
    } else if let Some(ref extra) = node.style {
        AttrValue::Bare(extra.clone())
    } else {
        // No style at all is unreachable for the mapper today (every node
        // has either a fill or a style), but the renderer is conservative:
        // skip the attribute when there is genuinely nothing to emit.
        AttrValue::Skip
    };
    push_unless_skip(&mut attrs, "style", style_value);

    if let Some(ref fill) = node.fill {
        attrs.push(("fillcolor".into(), AttrValue::Bare(fill.clone())));
    }
    if let Some(ref stroke) = node.stroke {
        attrs.push(("color".into(), AttrValue::Bare(stroke.clone())));
    }
    if let Some(pw) = node.penwidth {
        attrs.push(("penwidth".into(), AttrValue::Bare(format_number(pw))));
    }
    if let Some(h) = node.height {
        attrs.push(("height".into(), AttrValue::Bare(format_number(h))));
    }
    if let Some(w) = node.width {
        attrs.push(("width".into(), AttrValue::Bare(format_number(w))));
    }
    for (k, v) in &node.attrs {
        attrs.push((k.clone(), AttrValue::Bare(v.clone())));
    }

    format!("{} [{}];", quote_id(&node.id), format_node_attrs(&attrs))
}

/// Renders one edge line. Attribute order is fixed:
/// `color, style, arrowhead, label, penwidth, ...extra-attrs`.
fn render_edge(edge: &GraphEdge) -> String {
    let mut attrs: Vec<(String, AttrValue)> = Vec::new();

    if let Some(ref color) = edge.color {
        attrs.push(("color".into(), AttrValue::Bare(color.clone())));
    }
    if let Some(ref style) = edge.style {
        attrs.push(("style".into(), AttrValue::Bare(style.as_dot().into())));
    }
    if let Some(ref arrowhead) = edge.arrowhead {
        attrs.push(("arrowhead".into(), AttrValue::Bare(arrowhead.as_dot().into())));
    }
    if let Some(ref label) = edge.label {
        attrs.push(("label".into(), AttrValue::Bare(label.clone())));
    }
    if let Some(pw) = edge.penwidth {
        attrs.push(("penwidth".into(), AttrValue::Bare(format_number(pw))));
    }
    for (k, v) in &edge.attrs {
        attrs.push((k.clone(), AttrValue::Bare(v.clone())));
    }

    format!(
        "{} -> {} [{}];",
        quote_id(&edge.from),
        quote_id(&edge.to),
        format_node_attrs(&attrs)
    )
}

/// Renders a subgraph (cluster) and any nested children. Adds the
/// `cluster_` prefix at render time, matching Java/TS.
fn render_subgraph(sg: &Subgraph, indent: &str, lines: &mut Vec<String>) {
    let cluster_id = format!("cluster_{}", sg.id);
    lines.push(format!("{indent}subgraph {} {{", quote_id(&cluster_id)));

    let inner = format!("{indent}{INDENT_STEP}");

    if let Some(ref label) = sg.label {
        lines.push(format!("{inner}label={};", quote_attr(label)));
    }

    for (k, v) in &sg.attrs {
        lines.push(format!("{inner}{k}={};", quote_attr(v)));
    }

    for node in &sg.nodes {
        lines.push(format!("{inner}{}", render_node(node)));
    }

    // Nested clusters per [EXP-016] / [MOD-040].
    for nested in &sg.subgraphs {
        render_subgraph(nested, &inner, lines);
    }

    // Intra-cluster edges (both endpoints inside this cluster). Cross-
    // cluster edges live on the top-level Graph.edges list so Graphviz
    // routes them between cluster boxes correctly.
    for edge in &sg.edges {
        lines.push(format!("{inner}{}", render_edge(edge)));
    }

    lines.push(format!("{indent}}}"));
}

// ============================================================
//  Attribute formatting
// ============================================================

/// Internal attribute-value tag distinguishing values that need quoting via
/// [`quote_attr`] from values already in their final escaped/quoted form
/// (e.g. the auto-composed `"filled,dashed"`).
enum AttrValue {
    /// Render as `key=quote_attr(value)`.
    Bare(String),
    /// Render as `key=value` verbatim — the value already includes its
    /// surrounding quotes.
    PreQuoted(String),
    /// Skip this attribute entirely.
    Skip,
}

fn push_unless_skip(attrs: &mut Vec<(String, AttrValue)>, key: &str, v: AttrValue) {
    if !matches!(v, AttrValue::Skip) {
        attrs.push((key.into(), v));
    }
}

/// Formats node/edge attribute pairs, joining them with `, `. Pre-quoted
/// values are emitted verbatim; bare values go through [`quote_attr`].
fn format_node_attrs(attrs: &[(String, AttrValue)]) -> String {
    let mut out = String::new();
    for (i, (k, v)) in attrs.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        match v {
            AttrValue::Bare(s) => {
                out.push_str(k);
                out.push('=');
                out.push_str(&quote_attr(s));
            }
            AttrValue::PreQuoted(s) => {
                out.push_str(k);
                out.push('=');
                out.push_str(s);
            }
            AttrValue::Skip => {}
        }
    }
    out
}

/// Formats simple `key=quote_attr(value)` pairs (graph attrs, node/edge
/// defaults).
fn format_simple_attrs(attrs: &[(String, String)]) -> String {
    let mut out = String::new();
    for (i, (k, v)) in attrs.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(k);
        out.push('=');
        out.push_str(&quote_attr(v));
    }
    out
}

// ============================================================
//  Quoting & numbers
// ============================================================

/// Quotes a DOT identifier when needed (non-identifier chars or DOT
/// keyword). Pure ASCII identifier shortcut matches Java/TS regex
/// `[a-zA-Z_][a-zA-Z0-9_]*`.
fn quote_id(id: &str) -> String {
    if id.is_empty() {
        return "\"\"".to_string();
    }
    if is_dot_keyword(id) {
        return format!("\"{}\"", escape_dot(id));
    }
    let first = id.as_bytes()[0];
    if !(first.is_ascii_alphabetic() || first == b'_') {
        return format!("\"{}\"", escape_dot(id));
    }
    if !id
        .as_bytes()
        .iter()
        .all(|b| b.is_ascii_alphanumeric() || *b == b'_')
    {
        return format!("\"{}\"", escape_dot(id));
    }
    id.to_string()
}

/// Quotes a DOT attribute value. Numeric values (matching the same regex
/// Java/TS use, `^-?\d+(\.\d+)?$`) are emitted unquoted.
fn quote_attr(value: &str) -> String {
    if is_numeric_literal(value) {
        return value.to_string();
    }
    format!("\"{}\"", escape_dot(value))
}

fn escape_dot(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            other => out.push(other),
        }
    }
    out
}

fn is_dot_keyword(id: &str) -> bool {
    DOT_KEYWORDS.iter().any(|kw| kw.eq_ignore_ascii_case(id))
}

fn is_numeric_literal(s: &str) -> bool {
    // Mirrors Java regex `-?\d+(\.\d+)?` and the TS equivalent.
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return false;
    }
    let mut i = 0;
    if bytes[0] == b'-' {
        i += 1;
    }
    let int_start = i;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    if i == int_start {
        return false;
    }
    if i == bytes.len() {
        return true;
    }
    if bytes[i] != b'.' {
        return false;
    }
    i += 1;
    let frac_start = i;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    i == bytes.len() && i > frac_start
}

/// Formats a floating-point number the way Java/TS do: integers strip the
/// trailing `.0`. Mirrors Java's `formatNumber` (`value == (long) value`)
/// and TS's `String(value)` which already drops `.0` for integral floats.
pub(crate) fn format_number(value: f64) -> String {
    if value.is_finite() && value == value.trunc() && value.abs() < 1e15 {
        format!("{}", value as i64)
    } else {
        format!("{value}")
    }
}

// ============================================================
//  Tests
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_graph_uses_4_space_indent() {
        let graph = Graph::new("test");
        let dot = render_dot(&graph);
        assert!(dot.starts_with("digraph test {\n    rankdir=TB;\n"));
        assert!(dot.ends_with("}\n}") || dot.ends_with("}\n") || dot.ends_with("}"));
    }

    #[test]
    fn quotes_keywords() {
        assert_eq!(quote_id("graph"), "\"graph\"");
        assert_eq!(quote_id("node"), "\"node\"");
        assert_eq!(quote_id("my_node"), "my_node");
    }

    #[test]
    fn quote_attr_skips_quotes_for_numbers() {
        assert_eq!(quote_attr("0.5"), "0.5");
        assert_eq!(quote_attr("-3"), "-3");
        assert_eq!(quote_attr("1.5"), "1.5");
        assert_eq!(quote_attr("true"), "\"true\"");
        assert_eq!(quote_attr(""), "\"\"");
    }

    #[test]
    fn format_number_strips_trailing_zero() {
        assert_eq!(format_number(2.0), "2");
        assert_eq!(format_number(0.4), "0.4");
        assert_eq!(format_number(-1.0), "-1");
    }

    #[test]
    fn renders_node_with_filled_style_auto_emitted() {
        let mut graph = Graph::new("test");
        graph.nodes.push(GraphNode {
            id: "n1".into(),
            label: "".into(),
            shape: NodeShape::Circle,
            fill: Some("#FFFFFF".into()),
            stroke: Some("#333333".into()),
            penwidth: Some(1.5),
            semantic_id: None,
            style: None,
            height: None,
            width: Some(0.35),
            attrs: vec![("xlabel".into(), "Hello".into()), ("fixedsize".into(), "true".into())],
        });
        let dot = render_dot(&graph);
        assert!(dot.contains(
            "n1 [label=\"\", shape=\"circle\", style=\"filled\", fillcolor=\"#FFFFFF\", color=\"#333333\", penwidth=1.5, width=0.35, xlabel=\"Hello\", fixedsize=\"true\"];"
        ));
    }

    #[test]
    fn renders_node_composing_filled_with_extra_style() {
        let mut graph = Graph::new("test");
        graph.nodes.push(GraphNode {
            id: "n1".into(),
            label: "".into(),
            shape: NodeShape::Circle,
            fill: Some("#f8d7da".into()),
            stroke: Some("#721c24".into()),
            penwidth: Some(2.0),
            semantic_id: None,
            style: Some("dashed".into()),
            height: None,
            width: Some(0.35),
            attrs: Vec::new(),
        });
        let dot = render_dot(&graph);
        assert!(dot.contains("style=\"filled,dashed\""));
    }

    #[test]
    fn renders_edge_with_attribute_ordering() {
        let mut graph = Graph::new("test");
        graph.edges.push(GraphEdge {
            from: "a".into(),
            to: "b".into(),
            label: Some("hello".into()),
            color: Some("#333333".into()),
            style: Some(EdgeLineStyle::Solid),
            arrowhead: Some(ArrowHead::Normal),
            penwidth: Some(2.0),
            arc_type: None,
            attrs: Vec::new(),
        });
        let dot = render_dot(&graph);
        assert!(dot.contains(
            "a -> b [color=\"#333333\", style=\"solid\", arrowhead=\"normal\", label=\"hello\", penwidth=2];"
        ));
    }

    #[test]
    fn renders_subgraph_with_cluster_prefix_and_4_space_indent() {
        let mut graph = Graph::new("test");
        graph.subgraphs.push(Subgraph {
            id: "p1".into(),
            label: Some("p1".into()),
            nodes: vec![GraphNode {
                id: "p_p1_x".into(),
                label: "".into(),
                shape: NodeShape::Circle,
                fill: Some("#FFFFFF".into()),
                stroke: Some("#333333".into()),
                penwidth: Some(1.5),
                semantic_id: None,
                style: None,
                height: None,
                width: Some(0.35),
                attrs: vec![
                    ("xlabel".into(), "p1/x".into()),
                    ("fixedsize".into(), "true".into()),
                ],
            }],
            edges: Vec::new(),
            subgraphs: Vec::new(),
            attrs: vec![
                ("style".into(), "rounded,dashed".into()),
                ("bgcolor".into(), "#FAFAFA".into()),
                ("penwidth".into(), "1.5".into()),
            ],
        });
        let dot = render_dot(&graph);
        assert!(dot.contains("    subgraph cluster_p1 {\n"));
        assert!(dot.contains("        label=\"p1\";\n"));
        assert!(dot.contains("        style=\"rounded,dashed\";\n"));
    }
}
