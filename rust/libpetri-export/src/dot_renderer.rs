use crate::graph::*;

/// DOT keywords that must be quoted when used as identifiers.
const DOT_KEYWORDS: &[&str] = &["graph", "digraph", "subgraph", "node", "edge", "strict"];

/// Renders a Graph to a DOT format string.
pub fn render_dot(graph: &Graph) -> String {
    let mut out = String::new();
    out.push_str(&format!("digraph {} {{\n", quote_id(&graph.name)));

    // Rankdir
    out.push_str(&format!("  rankdir={};\n", graph.rankdir.as_dot()));

    // Graph attributes
    for (k, v) in &graph.graph_attrs {
        out.push_str(&format!("  {}={};\n", k, quote_attr(v)));
    }

    // Node defaults
    if !graph.node_defaults.is_empty() {
        out.push_str("  node [");
        render_attrs(&graph.node_defaults, &mut out);
        out.push_str("];\n");
    }

    // Edge defaults
    if !graph.edge_defaults.is_empty() {
        out.push_str("  edge [");
        render_attrs(&graph.edge_defaults, &mut out);
        out.push_str("];\n");
    }

    out.push('\n');

    // Subgraphs
    for sg in &graph.subgraphs {
        render_subgraph(sg, &mut out, 2);
    }

    // Nodes
    for node in &graph.nodes {
        render_node(node, &mut out, 2);
    }

    out.push('\n');

    // Edges
    for edge in &graph.edges {
        render_edge(edge, &mut out, 2);
    }

    out.push_str("}\n");
    out
}

fn render_subgraph(sg: &Subgraph, out: &mut String, indent: usize) {
    let prefix = " ".repeat(indent);
    out.push_str(&format!("{prefix}subgraph {} {{\n", quote_id(&sg.id)));

    if let Some(ref label) = sg.label {
        out.push_str(&format!("{prefix}  label={};\n", quote_attr(label)));
    }

    for (k, v) in &sg.attrs {
        out.push_str(&format!("{prefix}  {}={};\n", k, quote_attr(v)));
    }

    for node in &sg.nodes {
        render_node(node, out, indent + 2);
    }

    for edge in &sg.edges {
        render_edge(edge, out, indent + 2);
    }

    out.push_str(&format!("{prefix}}}\n"));
}

fn render_node(node: &GraphNode, out: &mut String, indent: usize) {
    let prefix = " ".repeat(indent);
    out.push_str(&format!("{prefix}{} [", quote_id(&node.id)));

    let mut attrs = Vec::new();
    attrs.push(("label".to_string(), escape_dot(&node.label)));
    attrs.push(("shape".to_string(), node.shape.as_dot().to_string()));

    if let Some(ref fill) = node.fill {
        attrs.push(("fillcolor".to_string(), fill.clone()));
        attrs.push(("style".to_string(), {
            let mut s = "filled".to_string();
            if let Some(ref extra) = node.style {
                s.push_str(&format!(",{extra}"));
            }
            s
        }));
    } else if let Some(ref style) = node.style {
        attrs.push(("style".to_string(), style.clone()));
    }

    if let Some(ref stroke) = node.stroke {
        attrs.push(("color".to_string(), stroke.clone()));
    }

    if let Some(pw) = node.penwidth {
        attrs.push(("penwidth".to_string(), format!("{pw}")));
    }

    if let Some(h) = node.height {
        attrs.push(("height".to_string(), format!("{h}")));
    }

    if let Some(w) = node.width {
        attrs.push(("width".to_string(), format!("{w}")));
    }

    for (k, v) in &node.attrs {
        attrs.push((k.clone(), v.clone()));
    }

    render_attrs_owned(&attrs, out);
    out.push_str("];\n");
}

fn render_edge(edge: &GraphEdge, out: &mut String, indent: usize) {
    let prefix = " ".repeat(indent);
    out.push_str(&format!(
        "{prefix}{} -> {} [",
        quote_id(&edge.from),
        quote_id(&edge.to)
    ));

    let mut attrs = Vec::new();

    if let Some(ref label) = edge.label {
        attrs.push(("label".to_string(), escape_dot(label)));
    }

    if let Some(ref color) = edge.color {
        attrs.push(("color".to_string(), color.clone()));
    }

    if let Some(ref style) = edge.style {
        attrs.push(("style".to_string(), style.as_dot().to_string()));
    }

    if let Some(ref arrowhead) = edge.arrowhead {
        attrs.push(("arrowhead".to_string(), arrowhead.as_dot().to_string()));
    }

    if let Some(pw) = edge.penwidth {
        attrs.push(("penwidth".to_string(), format!("{pw}")));
    }

    for (k, v) in &edge.attrs {
        attrs.push((k.clone(), v.clone()));
    }

    render_attrs_owned(&attrs, out);
    out.push_str("];\n");
}

fn render_attrs(attrs: &[(String, String)], out: &mut String) {
    for (i, (k, v)) in attrs.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(&format!("{}={}", k, quote_attr(v)));
    }
}

fn render_attrs_owned(attrs: &[(String, String)], out: &mut String) {
    for (i, (k, v)) in attrs.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(&format!("{}={}", k, quote_attr(v)));
    }
}

/// Quotes a DOT identifier if needed.
fn quote_id(id: &str) -> String {
    if needs_quoting(id) {
        format!("\"{}\"", id.replace('\"', "\\\""))
    } else {
        id.to_string()
    }
}

/// Quotes a DOT attribute value.
fn quote_attr(value: &str) -> String {
    format!("\"{}\"", value.replace('\"', "\\\""))
}

/// Escapes special characters in DOT labels.
fn escape_dot(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
}

fn needs_quoting(id: &str) -> bool {
    if id.is_empty() {
        return true;
    }
    if is_dot_keyword(id) {
        return true;
    }
    // Must start with letter or underscore
    let first = id.chars().next().unwrap();
    if !first.is_ascii_alphabetic() && first != '_' {
        return true;
    }
    // Must contain only alphanumeric or underscore
    !id.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn is_dot_keyword(id: &str) -> bool {
    DOT_KEYWORDS.iter().any(|kw| kw.eq_ignore_ascii_case(id))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_graph() {
        let graph = Graph::new("test");
        let dot = render_dot(&graph);
        assert!(dot.contains("digraph test"));
        assert!(dot.contains("rankdir=TB"));
    }

    #[test]
    fn quotes_keywords() {
        assert_eq!(quote_id("graph"), "\"graph\"");
        assert_eq!(quote_id("node"), "\"node\"");
        assert_eq!(quote_id("my_node"), "my_node");
    }

    #[test]
    fn escapes_special_chars() {
        assert_eq!(escape_dot("a\"b"), "a\\\"b");
        assert_eq!(escape_dot("line1\nline2"), "line1\\nline2");
    }

    #[test]
    fn renders_node() {
        let mut graph = Graph::new("test");
        graph.nodes.push(GraphNode {
            id: "n1".into(),
            label: "Node 1".into(),
            shape: NodeShape::Circle,
            fill: Some("#fff".into()),
            stroke: Some("#000".into()),
            penwidth: Some(1.5),
            semantic_id: None,
            style: None,
            height: None,
            width: None,
            attrs: Vec::new(),
        });
        let dot = render_dot(&graph);
        assert!(dot.contains("n1 ["));
        assert!(dot.contains("shape=\"circle\""));
        assert!(dot.contains("fillcolor=\"#fff\""));
    }

    #[test]
    fn renders_edge() {
        let mut graph = Graph::new("test");
        graph.edges.push(GraphEdge {
            from: "a".into(),
            to: "b".into(),
            label: Some("edge".into()),
            color: Some("#333".into()),
            style: Some(EdgeLineStyle::Solid),
            arrowhead: Some(ArrowHead::Normal),
            penwidth: Some(1.0),
            arc_type: None,
            attrs: Vec::new(),
        });
        let dot = render_dot(&graph);
        assert!(dot.contains("a -> b ["));
        assert!(dot.contains("label=\"edge\""));
    }
}
