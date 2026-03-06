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
}

impl EdgeLineStyle {
    pub fn as_dot(&self) -> &'static str {
        match self {
            EdgeLineStyle::Solid => "solid",
            EdgeLineStyle::Dashed => "dashed",
            EdgeLineStyle::Bold => "bold",
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

/// A subgraph (cluster).
#[derive(Debug, Clone)]
pub struct Subgraph {
    pub id: String,
    pub label: Option<String>,
    pub nodes: Vec<GraphNode>,
    pub edges: Vec<GraphEdge>,
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
