/// Node visual style.
pub struct NodeVisual {
    pub shape: &'static str,
    pub fill: &'static str,
    pub stroke: &'static str,
    pub penwidth: f64,
    pub style: Option<&'static str>,
}

/// Edge visual style.
pub struct EdgeVisual {
    pub color: &'static str,
    pub style: &'static str,
    pub penwidth: f64,
    pub arrowhead: &'static str,
}

// Node styles (from spec/petri-net-styles.json)
pub const PLACE: NodeVisual = NodeVisual {
    shape: "circle",
    fill: "#ffffff",
    stroke: "#333333",
    penwidth: 1.5,
    style: None,
};

pub const START_PLACE: NodeVisual = NodeVisual {
    shape: "circle",
    fill: "#d4edda",
    stroke: "#28a745",
    penwidth: 2.0,
    style: None,
};

pub const END_PLACE: NodeVisual = NodeVisual {
    shape: "doublecircle",
    fill: "#cce5ff",
    stroke: "#007bff",
    penwidth: 2.0,
    style: None,
};

pub const ENVIRONMENT_PLACE: NodeVisual = NodeVisual {
    shape: "circle",
    fill: "#ffe6e6",
    stroke: "#dc3545",
    penwidth: 2.0,
    style: Some("dashed"),
};

pub const TRANSITION: NodeVisual = NodeVisual {
    shape: "box",
    fill: "#fff3cd",
    stroke: "#ffc107",
    penwidth: 1.5,
    style: None,
};

// Edge styles
pub const INPUT_EDGE: EdgeVisual = EdgeVisual {
    color: "#333333",
    style: "solid",
    penwidth: 1.0,
    arrowhead: "normal",
};

pub const OUTPUT_EDGE: EdgeVisual = EdgeVisual {
    color: "#333333",
    style: "solid",
    penwidth: 1.0,
    arrowhead: "normal",
};

pub const INHIBITOR_EDGE: EdgeVisual = EdgeVisual {
    color: "#dc3545",
    style: "solid",
    penwidth: 1.5,
    arrowhead: "odot",
};

pub const READ_EDGE: EdgeVisual = EdgeVisual {
    color: "#6c757d",
    style: "dashed",
    penwidth: 1.0,
    arrowhead: "normal",
};

pub const RESET_EDGE: EdgeVisual = EdgeVisual {
    color: "#fd7e14",
    style: "bold",
    penwidth: 2.0,
    arrowhead: "normal",
};

// Font settings
pub const FONT_FAMILY: &str = "Helvetica";
pub const FONT_NODE_SIZE: f64 = 11.0;
pub const FONT_EDGE_SIZE: f64 = 9.0;

// Graph spacing
pub const NODESEP: f64 = 0.5;
pub const RANKSEP: f64 = 0.75;
