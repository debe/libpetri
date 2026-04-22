#!/usr/bin/env bash
# Generates style constant files for all three languages from spec/petri-net-styles.json.
#
# Generated files:
#   rust/libpetri-export/src/styles.rs
#   java/src/main/java/org/libpetri/export/StyleConstants.java
#   typescript/src/export/styles.ts
#
# Usage:
#   scripts/generate-styles.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
SPEC="$ROOT_DIR/spec/petri-net-styles.json"

if ! command -v jq &>/dev/null; then
  echo "Error: jq is required but not installed." >&2
  exit 1
fi

# Helper: read a value from the spec
j() { jq -r "$1" "$SPEC"; }

# ======================== Read spec values ========================

# Node styles
read_node() {
  local key=$1
  local prefix="${2:-}"
  eval "${prefix}shape=$(j ".node.${key}.shape")"
  eval "${prefix}fill=$(j ".node.${key}.fill")"
  eval "${prefix}stroke=$(j ".node.${key}.stroke")"
  eval "${prefix}penwidth=$(j ".node.${key}.penwidth")"
  eval "${prefix}style=$(j ".node.${key}.style // empty")"
  eval "${prefix}height=$(j ".node.${key}.height // empty")"
  eval "${prefix}width=$(j ".node.${key}.width // empty")"
}

# Edge styles
read_edge() {
  local key=$1
  local prefix="${2:-}"
  eval "${prefix}color=$(j ".edge.${key}.color")"
  eval "${prefix}estyle=$(j ".edge.${key}.style")"
  eval "${prefix}arrowhead=$(j ".edge.${key}.arrowhead")"
  eval "${prefix}epenwidth=$(j ".edge.${key}.penwidth // empty")"
}

# Font/graph
FONT_FAMILY=$(j '.font.family')
FONT_NODE_SIZE=$(j '.font.nodeSize')
FONT_EDGE_SIZE=$(j '.font.edgeSize')
GRAPH_NODESEP=$(j '.graph.nodesep')
GRAPH_RANKSEP=$(j '.graph.ranksep')
GRAPH_FORCELABELS=$(j '.graph.forcelabels')
GRAPH_OVERLAP=$(j '.graph.overlap')
GRAPH_OUTPUTORDER=$(j '.graph.outputorder')
GRAPH_SPLINES=$(j '.graph.splines')

# ======================== Generate Rust ========================

RUST_FILE="$ROOT_DIR/rust/libpetri-export/src/styles.rs"

rust_node() {
  local const_name=$1 key=$2
  read_node "$key" "n_"
  local style_str="None"
  [[ -n "$n_style" ]] && style_str="Some(\"$n_style\")"
  local height_str="None"
  [[ -n "$n_height" ]] && height_str="Some($n_height)"
  local width_str="None"
  [[ -n "$n_width" ]] && width_str="Some($n_width)"
  cat <<EOF
pub const ${const_name}: NodeVisual = NodeVisual {
    shape: "$n_shape",
    fill: "$n_fill",
    stroke: "$n_stroke",
    penwidth: $n_penwidth,
    style: $style_str,
    height: $height_str,
    width: $width_str,
};
EOF
}

rust_edge() {
  local const_name=$1 key=$2
  read_edge "$key" "e_"
  local pw_str="None"
  [[ -n "$e_epenwidth" ]] && pw_str="Some($e_epenwidth)"
  cat <<EOF
pub const ${const_name}: EdgeVisual = EdgeVisual {
    color: "$e_color",
    style: "$e_estyle",
    penwidth: $pw_str,
    arrowhead: "$e_arrowhead",
};
EOF
}

cat > "$RUST_FILE" <<'HEADER'
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

HEADER

{
  echo "// Node styles"
  rust_node "PLACE" "place"
  echo
  rust_node "START_PLACE" "start"
  echo
  rust_node "END_PLACE" "end"
  echo
  rust_node "ENVIRONMENT_PLACE" "environment"
  echo
  rust_node "TRANSITION" "transition"
  echo
  echo "// Edge styles"
  rust_edge "INPUT_EDGE" "input"
  echo
  rust_edge "OUTPUT_EDGE" "output"
  echo
  rust_edge "INHIBITOR_EDGE" "inhibitor"
  echo
  rust_edge "READ_EDGE" "read"
  echo
  rust_edge "RESET_EDGE" "reset"
  echo
  cat <<EOF
// Font settings
pub const FONT_FAMILY: &str = "$FONT_FAMILY";
pub const FONT_NODE_SIZE: f64 = ${FONT_NODE_SIZE}.0;
pub const FONT_EDGE_SIZE: f64 = ${FONT_EDGE_SIZE}.0;

// Graph spacing
pub const NODESEP: f64 = $GRAPH_NODESEP;
pub const RANKSEP: f64 = $GRAPH_RANKSEP;
pub const FORCE_LABELS: &str = "$GRAPH_FORCELABELS";
pub const OVERLAP: &str = "$GRAPH_OVERLAP";
pub const OUTPUT_ORDER: &str = "$GRAPH_OUTPUTORDER";
pub const SPLINES: &str = "$GRAPH_SPLINES";
EOF
} >> "$RUST_FILE"

echo "Generated $RUST_FILE"

# ======================== Generate Java ========================

JAVA_FILE="$ROOT_DIR/java/src/main/java/org/libpetri/export/StyleConstants.java"

java_shape() {
  case "$1" in
    circle) echo "NodeShape.CIRCLE" ;;
    doublecircle) echo "NodeShape.DOUBLECIRCLE" ;;
    box) echo "NodeShape.BOX" ;;
    *) echo "NodeShape.CIRCLE" ;;
  esac
}

java_node() {
  local const_name=$1 key=$2
  read_node "$key" "n_"
  local shape_java
  shape_java=$(java_shape "$n_shape")
  local style_java="null"
  [[ -n "$n_style" ]] && style_java="\"$n_style\""
  local height_java="null"
  [[ -n "$n_height" ]] && height_java="$n_height"
  local width_java="null"
  [[ -n "$n_width" ]] && width_java="$n_width"
  printf '    public static final NodeVisual %-13s = new NodeVisual(%s,  "%s", "%s", %s, %s, %s, %s);\n' \
    "$const_name" "$shape_java" "$n_fill" "$n_stroke" "$n_penwidth" "$style_java" "$height_java" "$width_java"
}

java_edge_style() {
  case "$1" in
    solid) echo "EdgeLineStyle.SOLID" ;;
    dashed) echo "EdgeLineStyle.DASHED" ;;
    bold) echo "EdgeLineStyle.BOLD" ;;
    *) echo "EdgeLineStyle.SOLID" ;;
  esac
}

java_arrowhead() {
  case "$1" in
    normal) echo "ArrowHead.NORMAL" ;;
    odot) echo "ArrowHead.ODOT" ;;
    *) echo "ArrowHead.NORMAL" ;;
  esac
}

java_edge() {
  local const_name=$1 key=$2
  read_edge "$key" "e_"
  local style_java arrowhead_java
  style_java=$(java_edge_style "$e_estyle")
  arrowhead_java=$(java_arrowhead "$e_arrowhead")
  if [[ -n "$e_epenwidth" ]]; then
    printf '    public static final EdgeVisual %-14s = new EdgeVisual("%s", %s,  %s, %s);\n' \
      "$const_name" "$e_color" "$style_java" "$arrowhead_java" "$e_epenwidth"
  else
    printf '    public static final EdgeVisual %-14s = new EdgeVisual("%s", %s,  %s);\n' \
      "$const_name" "$e_color" "$style_java" "$arrowhead_java"
  fi
}

cat > "$JAVA_FILE" <<'JAVA_HEADER'
// GENERATED from spec/petri-net-styles.json — do not edit manually.
// Regenerate with: scripts/generate-styles.sh

package org.libpetri.export;

import org.libpetri.export.graph.*;

import java.util.Map;

/**
 * Hardcoded visual style constants from {@code spec/petri-net-styles.json}.
 *
 * <p>This avoids a runtime JSON dependency. Values must be kept in sync
 * with the shared spec file.
 */
public final class StyleConstants {

    private StyleConstants() {}

    // ======================== Node Styles ========================

JAVA_HEADER

{
  java_node "PLACE" "place"
  java_node "START" "start"
  java_node "END" "end"
  java_node "ENVIRONMENT" "environment"
  java_node "TRANSITION" "transition"
  echo
  cat <<'EOF'
    private static final Map<String, NodeVisual> NODE_STYLES = Map.of(
        "place",       PLACE,
        "start",       START,
        "end",         END,
        "environment", ENVIRONMENT,
        "transition",  TRANSITION
    );

    // ======================== Edge Styles ========================

EOF
  java_edge "INPUT_EDGE" "input"
  java_edge "OUTPUT_EDGE" "output"
  java_edge "INHIBITOR_EDGE" "inhibitor"
  java_edge "READ_EDGE" "read"
  java_edge "RESET_EDGE" "reset"
  echo
  cat <<EOF
    private static final Map<ArcType, EdgeVisual> EDGE_STYLES = Map.of(
        ArcType.INPUT,     INPUT_EDGE,
        ArcType.OUTPUT,    OUTPUT_EDGE,
        ArcType.INHIBITOR, INHIBITOR_EDGE,
        ArcType.READ,      READ_EDGE,
        ArcType.RESET,     RESET_EDGE
    );

    // ======================== Font & Graph ========================

    public static final String FONT_FAMILY = "$FONT_FAMILY";
    public static final int NODE_FONT_SIZE = $FONT_NODE_SIZE;
    public static final int EDGE_FONT_SIZE = $FONT_EDGE_SIZE;
    public static final double NODESEP = $GRAPH_NODESEP;
    public static final double RANKSEP = $GRAPH_RANKSEP;
    public static final String FORCE_LABELS = "$GRAPH_FORCELABELS";
    public static final String OVERLAP = "$GRAPH_OVERLAP";
    public static final String OUTPUT_ORDER = "$GRAPH_OUTPUTORDER";
    public static final String SPLINES = "$GRAPH_SPLINES";

    // ======================== Lookup ========================

    /** Returns the visual style for the given node category. */
    public static NodeVisual nodeStyle(String category) {
        var style = NODE_STYLES.get(category);
        if (style == null) throw new IllegalArgumentException("Unknown node category: " + category);
        return style;
    }

    /** Returns the visual style for the given arc type. */
    public static EdgeVisual edgeStyle(ArcType arcType) {
        return EDGE_STYLES.get(arcType);
    }
}
EOF
} >> "$JAVA_FILE"

echo "Generated $JAVA_FILE"

# ======================== Generate TypeScript ========================

TS_FILE="$ROOT_DIR/typescript/src/export/styles.ts"

ts_node() {
  local key=$1
  read_node "$key" "n_"
  local extras=""
  [[ -n "$n_style" ]] && extras="$extras style: '$n_style',"
  [[ -n "$n_height" ]] && extras="$extras height: $n_height,"
  [[ -n "$n_width" ]] && extras="$extras width: $n_width,"
  # Remove trailing comma
  extras="${extras%,}"
  printf "  %-13s { shape: '%s',  fill: '%s', stroke: '%s', penwidth: %s,%s },\n" \
    "${key}:" "$n_shape" "$n_fill" "$n_stroke" "$n_penwidth" "$extras"
}

ts_edge() {
  local key=$1
  read_edge "$key" "e_"
  local extras=""
  [[ -n "$e_epenwidth" ]] && extras=" penwidth: $e_epenwidth,"
  extras="${extras%,}"
  printf "  %-10s { color: '%s', style: '%s',  arrowhead: '%s'%s },\n" \
    "${key}:" "$e_color" "$e_estyle" "$e_arrowhead" "${extras:+, $extras}"
}

cat > "$TS_FILE" <<'TS_HEADER'
// GENERATED from spec/petri-net-styles.json — do not edit manually.
// Regenerate with: scripts/generate-styles.sh

/**
 * Style loader for Petri net visualization.
 *
 * Reads the shared style definition from `spec/petri-net-styles.json` and
 * exposes typed accessors for node and edge visual properties.
 *
 * @module export/styles
 */

import type { NodeShape, EdgeLineStyle, ArrowHead } from './graph.js';

// ======================== Style Types ========================

export interface NodeVisual {
  readonly shape: NodeShape;
  readonly fill: string;
  readonly stroke: string;
  readonly penwidth: number;
  readonly style?: string;
  readonly height?: number;
  readonly width?: number;
}

export interface EdgeVisual {
  readonly color: string;
  readonly style: EdgeLineStyle;
  readonly arrowhead: ArrowHead;
  readonly penwidth?: number;
}

export interface FontStyle {
  readonly family: string;
  readonly nodeSize: number;
  readonly edgeSize: number;
}

export interface GraphStyle {
  readonly nodesep: number;
  readonly ranksep: number;
  readonly forcelabels: boolean;
  readonly overlap: boolean;
  readonly outputorder: string;
  readonly splines: string;
}

// ======================== Inline Style Data ========================

// Inlined from spec/petri-net-styles.json to avoid runtime JSON import issues.
// Keep in sync with the spec file.

TS_HEADER

{
  echo "const NODE_STYLES: Record<NodeCategory, NodeVisual> = {"
  ts_node "place"
  ts_node "start"
  ts_node "end"
  ts_node "environment"
  ts_node "transition"
  echo "};"
  echo
  echo "const EDGE_STYLES: Record<EdgeCategory, EdgeVisual> = {"
  ts_edge "input"
  ts_edge "output"
  ts_edge "inhibitor"
  ts_edge "read"
  ts_edge "reset"
  echo "};"
  echo
  cat <<EOF
export const FONT: FontStyle = { family: '$FONT_FAMILY', nodeSize: $FONT_NODE_SIZE, edgeSize: $FONT_EDGE_SIZE };

export const GRAPH: GraphStyle = { nodesep: $GRAPH_NODESEP, ranksep: $GRAPH_RANKSEP, forcelabels: $GRAPH_FORCELABELS, overlap: $GRAPH_OVERLAP, outputorder: '$GRAPH_OUTPUTORDER', splines: '$GRAPH_SPLINES' };

// ======================== Public API ========================

export type NodeCategory = 'place' | 'start' | 'end' | 'environment' | 'transition';
export type EdgeCategory = 'input' | 'output' | 'inhibitor' | 'read' | 'reset';

/** Returns the visual style for the given node category. */
export function nodeStyle(category: NodeCategory): NodeVisual {
  return NODE_STYLES[category];
}

/** Returns the visual style for the given edge/arc type. */
export function edgeStyle(arcType: EdgeCategory): EdgeVisual {
  return EDGE_STYLES[arcType];
}
EOF
} >> "$TS_FILE"

echo "Generated $TS_FILE"
echo "Done. All style files regenerated from $SPEC"
