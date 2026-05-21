/// Selects how DOT export groups nodes into `subgraph cluster_*` blocks
/// (per `spec/11-modular-composition.md` **MOD-040** /
/// `spec/09-export.md` **EXP-016**).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ClusterSource {
    /// Use subnet-membership metadata (per MOD-026) when the net carries
    /// any; otherwise fall back to instance-prefix name detection. Default.
    #[default]
    Auto,
    /// Strictly cluster from subnet-membership metadata (per MOD-026); a node
    /// with no metadata entry — including a prefix-named instance node — is
    /// not clustered. Use [`ClusterSource::Auto`] to also cluster
    /// prefix-named nodes.
    Metadata,
    /// Always cluster from instance-prefix name segments; ignore metadata.
    Prefix,
    /// Emit no clusters — every node renders at the top level.
    None,
}

/// Direction of graph layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RankDir {
    TopToBottom,
    LeftToRight,
    BottomToTop,
    RightToLeft,
}

impl RankDir {
    pub fn as_dot(&self) -> &'static str {
        match self {
            RankDir::TopToBottom => "TB",
            RankDir::LeftToRight => "LR",
            RankDir::BottomToTop => "BT",
            RankDir::RightToLeft => "RL",
        }
    }
}

/// Shape of a graph node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeShape {
    Circle,
    DoubleCircle,
    Box,
    Diamond,
    Ellipse,
    Point,
    Record,
}

impl NodeShape {
    pub fn as_dot(&self) -> &'static str {
        match self {
            NodeShape::Circle => "circle",
            NodeShape::DoubleCircle => "doublecircle",
            NodeShape::Box => "box",
            NodeShape::Diamond => "diamond",
            NodeShape::Ellipse => "ellipse",
            NodeShape::Point => "point",
            NodeShape::Record => "record",
        }
    }
}

/// Style of an edge line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeLineStyle {
    Solid,
    Dashed,
    Bold,
    /// Invisible edge — used for ghost cluster-to-cluster layout hints (spec EXP-017).
    Invis,
}

impl EdgeLineStyle {
    pub fn as_dot(&self) -> &'static str {
        match self {
            EdgeLineStyle::Solid => "solid",
            EdgeLineStyle::Dashed => "dashed",
            EdgeLineStyle::Bold => "bold",
            EdgeLineStyle::Invis => "invis",
        }
    }
}

/// Arrowhead type for edges.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArrowHead {
    Normal,
    None,
    Odot,
    Dot,
    Diamond,
    Vee,
}

impl ArrowHead {
    pub fn as_dot(&self) -> &'static str {
        match self {
            ArrowHead::Normal => "normal",
            ArrowHead::None => "none",
            ArrowHead::Odot => "odot",
            ArrowHead::Dot => "dot",
            ArrowHead::Diamond => "diamond",
            ArrowHead::Vee => "vee",
        }
    }
}

/// A node in the graph.
#[derive(Debug, Clone)]
pub struct GraphNode {
    pub id: String,
    pub label: String,
    pub shape: NodeShape,
    pub fill: Option<String>,
    pub stroke: Option<String>,
    pub penwidth: Option<f64>,
    pub semantic_id: Option<String>,
    pub style: Option<String>,
    pub height: Option<f64>,
    pub width: Option<f64>,
    pub attrs: Vec<(String, String)>,
}

/// An edge in the graph.
#[derive(Debug, Clone)]
pub struct GraphEdge {
    pub from: String,
    pub to: String,
    pub label: Option<String>,
    pub color: Option<String>,
    pub style: Option<EdgeLineStyle>,
    pub arrowhead: Option<ArrowHead>,
    pub penwidth: Option<f64>,
    pub arc_type: Option<String>,
    pub attrs: Vec<(String, String)>,
}

/// A subgraph (cluster) in the graph.
///
/// Subgraphs may nest arbitrarily via [`Subgraph::subgraphs`] to model
/// nested subnet instance prefixes per `spec/11-modular-composition.md`
/// **MOD-040** and `spec/09-export.md` **EXP-016**. Edges whose endpoints
/// both live inside the same cluster are placed inside that cluster via
/// [`Subgraph::edges`] so Graphviz routes them correctly. Cross-cluster
/// (or fully top-level) edges live on the parent [`Graph::edges`] list.
#[derive(Debug, Clone)]
pub struct Subgraph {
    /// Subgraph identifier — the renderer prefixes this with `cluster_`.
    pub id: String,
    /// Optional display label (typically the un-sanitized prefix string for
    /// human readability per [EXP-016]).
    pub label: Option<String>,
    /// Nodes contained directly in this subgraph (excluding nodes inside
    /// nested [`Subgraph::subgraphs`]).
    pub nodes: Vec<GraphNode>,
    /// Edges whose source and target both live inside this subgraph.
    pub edges: Vec<GraphEdge>,
    /// Nested child subgraphs.
    pub subgraphs: Vec<Subgraph>,
    /// Optional extra DOT attributes (style, bgcolor, penwidth, ...). Stored
    /// as a `Vec<(K, V)>` because cross-language byte-parity requires
    /// insertion-order preservation.
    pub attrs: Vec<(String, String)>,
}

/// A complete graph.
#[derive(Debug, Clone)]
pub struct Graph {
    pub name: String,
    pub rankdir: RankDir,
    pub nodes: Vec<GraphNode>,
    pub edges: Vec<GraphEdge>,
    pub subgraphs: Vec<Subgraph>,
    pub node_defaults: Vec<(String, String)>,
    pub edge_defaults: Vec<(String, String)>,
    pub graph_attrs: Vec<(String, String)>,
}

impl Graph {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            rankdir: RankDir::TopToBottom,
            nodes: Vec::new(),
            edges: Vec::new(),
            subgraphs: Vec::new(),
            node_defaults: Vec::new(),
            edge_defaults: Vec::new(),
            graph_attrs: Vec::new(),
        }
    }
}
