// GENERATED from spec/petri-net-styles.json — do not edit manually.
// Regenerate with: scripts/generate-styles.sh

/// Node visual style.
pub struct NodeVisual {
    pub shape: &'static str,
    pub fill: &'static str,
    pub stroke: &'static str,
    pub penwidth: f64,
    pub style: Option<&'static str>,
    pub height: Option<f64>,
    pub width: Option<f64>,
}

/// Edge visual style.
pub struct EdgeVisual {
    pub color: &'static str,
    pub style: &'static str,
    pub penwidth: Option<f64>,
    pub arrowhead: &'static str,
}

// Node styles
pub const PLACE: NodeVisual = NodeVisual {
    shape: "circle",
    fill: "#FFFFFF",
    stroke: "#333333",
    penwidth: 1.5,
    style: None,
    height: None,
    width: Some(0.35),
};

pub const START_PLACE: NodeVisual = NodeVisual {
    shape: "circle",
    fill: "#d4edda",
    stroke: "#28a745",
    penwidth: 2.0,
    style: None,
    height: None,
    width: Some(0.35),
};

pub const END_PLACE: NodeVisual = NodeVisual {
    shape: "doublecircle",
    fill: "#cce5ff",
    stroke: "#004085",
    penwidth: 2.0,
    style: None,
    height: None,
    width: Some(0.35),
};

pub const ENVIRONMENT_PLACE: NodeVisual = NodeVisual {
    shape: "circle",
    fill: "#f8d7da",
    stroke: "#721c24",
    penwidth: 2.0,
    style: Some("dashed"),
    height: None,
    width: Some(0.35),
};

pub const TRANSITION: NodeVisual = NodeVisual {
    shape: "box",
    fill: "#fff3cd",
    stroke: "#856404",
    penwidth: 1.0,
    style: None,
    height: Some(0.4),
    width: Some(0.8),
};

// Edge styles
pub const INPUT_EDGE: EdgeVisual = EdgeVisual {
    color: "#333333",
    style: "solid",
    penwidth: None,
    arrowhead: "normal",
};

pub const OUTPUT_EDGE: EdgeVisual = EdgeVisual {
    color: "#333333",
    style: "solid",
    penwidth: None,
    arrowhead: "normal",
};

pub const INHIBITOR_EDGE: EdgeVisual = EdgeVisual {
    color: "#dc3545",
    style: "solid",
    penwidth: None,
    arrowhead: "odot",
};

pub const READ_EDGE: EdgeVisual = EdgeVisual {
    color: "#6c757d",
    style: "dashed",
    penwidth: None,
    arrowhead: "normal",
};

pub const RESET_EDGE: EdgeVisual = EdgeVisual {
    color: "#fd7e14",
    style: "bold",
    penwidth: Some(2.0),
    arrowhead: "normal",
};

// Font settings
pub const FONT_FAMILY: &str = "Helvetica,Arial,sans-serif";
pub const FONT_NODE_SIZE: f64 = 12.0;
pub const FONT_EDGE_SIZE: f64 = 10.0;

// Graph spacing
pub const NODESEP: f64 = 0.5;
pub const RANKSEP: f64 = 0.75;
pub const FORCE_LABELS: &str = "true";
pub const OVERLAP: &str = "false";
pub const OUTPUT_ORDER: &str = "edgesfirst";
pub const SPLINES: &str = "curved";
