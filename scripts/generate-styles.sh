#!/usr/bin/env bash
# Generates style constant files for all three languages, and the Lean copy of the
# node and edge tables, from spec/petri-net-styles.json.
#
# Generated files:
#   rust/libpetri-export/src/styles.rs
#   java/src/main/java/org/libpetri/export/StyleConstants.java
#   typescript/src/export/styles.ts
#   lean/Libpetri/Export/Styles.lean
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
  eval "${prefix}shape=$(j ".node[\"${key}\"].shape")"
  eval "${prefix}fill=$(j ".node[\"${key}\"].fill")"
  eval "${prefix}stroke=$(j ".node[\"${key}\"].stroke")"
  eval "${prefix}penwidth=$(j ".node[\"${key}\"].penwidth")"
  eval "${prefix}style=$(j ".node[\"${key}\"].style // empty")"
  eval "${prefix}height=$(j ".node[\"${key}\"].height // empty")"
  eval "${prefix}width=$(j ".node[\"${key}\"].width // empty")"
}

# Edge styles
read_edge() {
  local key=$1
  local prefix="${2:-}"
  eval "${prefix}color=$(j ".edge[\"${key}\"].color")"
  eval "${prefix}estyle=$(j ".edge[\"${key}\"].style")"
  eval "${prefix}arrowhead=$(j ".edge[\"${key}\"].arrowhead")"
  eval "${prefix}epenwidth=$(j ".edge[\"${key}\"].penwidth // empty")"
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
  cat <<'EOF'
/// A terminal place (EXEC-042): the run ends once it is marked. Takes
/// precedence over the environment/start/end categories. Values from
/// `spec/petri-net-styles.json` "terminal".
EOF
  rust_node "TERMINAL_PLACE" "terminal"
  echo
  rust_node "TRANSITION" "transition"
  echo
  rust_node "XOR_JUNCTION" "xor-junction"
  echo
  rust_node "AND_JUNCTION" "and-junction"
  echo
  rust_node "INTERFACE_PORT" "interface-port"
  echo
  rust_node "SYNC_CHANNEL" "sync-channel"
  echo
  echo "// Edge styles"
  rust_edge "INPUT_EDGE" "input"
  echo
  cat <<'EOF'
/// ν-net correlated input edge (a join input named by a `MatchSpec`, NU-020 /
/// EXP-018). Teal to distinguish it from a plain input; carries a `⟨n⟩` label.
EOF
  rust_edge "MATCH_INPUT_EDGE" "match-input"
  echo
  rust_edge "OUTPUT_EDGE" "output"
  echo
  rust_edge "INHIBITOR_EDGE" "inhibitor"
  echo
  rust_edge "READ_EDGE" "read"
  echo
  rust_edge "RESET_EDGE" "reset"
  echo
  rust_edge "RESET_OUTPUT_EDGE" "reset-output"
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
    diamond) echo "NodeShape.DIAMOND" ;;
    ellipse) echo "NodeShape.ELLIPSE" ;;
    record) echo "NodeShape.RECORD" ;;
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
  printf '    public static final NodeVisual %-14s = new NodeVisual(%s,  "%s", "%s", %s, %s, %s, %s);\n' \
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
  java_node "TERMINAL" "terminal"
  java_node "TRANSITION" "transition"
  java_node "XOR_JUNCTION" "xor-junction"
  java_node "AND_JUNCTION" "and-junction"
  java_node "INTERFACE_PORT" "interface-port"
  java_node "SYNC_CHANNEL" "sync-channel"
  echo
  cat <<'EOF'
    private static final Map<String, NodeVisual> NODE_STYLES = Map.ofEntries(
        Map.entry("place",          PLACE),
        Map.entry("start",          START),
        Map.entry("end",            END),
        Map.entry("environment",    ENVIRONMENT),
        Map.entry("terminal",       TERMINAL),
        Map.entry("transition",     TRANSITION),
        Map.entry("xor-junction",   XOR_JUNCTION),
        Map.entry("and-junction",   AND_JUNCTION),
        Map.entry("interface-port", INTERFACE_PORT),
        Map.entry("sync-channel",   SYNC_CHANNEL)
    );

    // ======================== Edge Styles ========================

EOF
  java_edge "INPUT_EDGE" "input"
  echo "    /** ν-net correlated input edge (a join input named by a MatchSpec, NU-020 / EXP-018). */"
  java_edge "MATCH_INPUT_EDGE" "match-input"
  java_edge "OUTPUT_EDGE" "output"
  java_edge "INHIBITOR_EDGE" "inhibitor"
  java_edge "READ_EDGE" "read"
  java_edge "RESET_EDGE" "reset"
  java_edge "RESET_OUTPUT_EDGE" "reset-output"
  echo
  cat <<EOF
    private static final Map<ArcType, EdgeVisual> EDGE_STYLES = Map.of(
        ArcType.INPUT,        INPUT_EDGE,
        ArcType.OUTPUT,       OUTPUT_EDGE,
        ArcType.INHIBITOR,    INHIBITOR_EDGE,
        ArcType.READ,         READ_EDGE,
        ArcType.RESET,        RESET_EDGE,
        ArcType.RESET_OUTPUT, RESET_OUTPUT_EDGE
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
  # Quote hyphenated keys (invalid as bare property names)
  local key_out="${key}:"
  [[ "$key" == *-* ]] && key_out="'${key}':"
  printf "  %-17s{ shape: '%s',  fill: '%s', stroke: '%s', penwidth: %s,%s },\n" \
    "$key_out" "$n_shape" "$n_fill" "$n_stroke" "$n_penwidth" "$extras"
}

ts_edge() {
  local key=$1
  read_edge "$key" "e_"
  local extras=""
  [[ -n "$e_epenwidth" ]] && extras=" penwidth: $e_epenwidth,"
  extras="${extras%,}"
  local key_out="${key}:"
  [[ "$key" == *-* ]] && key_out="'${key}':"
  printf "  %-14s { color: '%s', style: '%s',  arrowhead: '%s'%s },\n" \
    "$key_out" "$e_color" "$e_estyle" "$e_arrowhead" "${extras:+, $extras}"
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
  ts_node "terminal"
  ts_node "transition"
  ts_node "xor-junction"
  ts_node "and-junction"
  ts_node "interface-port"
  ts_node "sync-channel"
  echo "};"
  echo
  echo "const EDGE_STYLES: Record<EdgeCategory, EdgeVisual> = {"
  ts_edge "input"
  ts_edge "output"
  ts_edge "inhibitor"
  ts_edge "read"
  ts_edge "reset"
  ts_edge "reset-output"
  echo "};"
  echo
  cat <<EOF
export const FONT: FontStyle = { family: '$FONT_FAMILY', nodeSize: $FONT_NODE_SIZE, edgeSize: $FONT_EDGE_SIZE };

export const GRAPH: GraphStyle = { nodesep: $GRAPH_NODESEP, ranksep: $GRAPH_RANKSEP, forcelabels: $GRAPH_FORCELABELS, overlap: $GRAPH_OVERLAP, outputorder: '$GRAPH_OUTPUTORDER' };

// ======================== Public API ========================

export type NodeCategory = 'place' | 'start' | 'end' | 'environment' | 'terminal' | 'transition' | 'xor-junction' | 'and-junction' | 'interface-port' | 'sync-channel';
export type EdgeCategory = 'input' | 'output' | 'inhibitor' | 'read' | 'reset' | 'reset-output';

/** Returns the visual style for the given node category. */
export function nodeStyle(category: NodeCategory): NodeVisual {
  return NODE_STYLES[category];
}

/** Returns the visual style for the given edge/arc type. */
export function edgeStyle(arcType: EdgeCategory): EdgeVisual {
  return EDGE_STYLES[arcType];
}
EOF
  read_edge "match-input" "m_"
  echo
  echo "/** ν-net correlated input edge (a join input named by a MatchSpec, NU-020 / EXP-018). */"
  echo "export const MATCH_INPUT_EDGE: EdgeVisual = { color: '$m_color', style: '$m_estyle', arrowhead: '$m_arrowhead' };"
} >> "$TS_FILE"

echo "Generated $TS_FILE"

# ======================== Generate Lean ========================
#
# The Lean copy of the node and edge tables (export design, policy P2): requirement
# statements name a row, never a value. Every row of `.node` and `.edge` is emitted, in the
# order of the JSON file, so a new row reaches Lean without a change here.

LEAN_FILE="$ROOT_DIR/lean/Libpetri/Export/Styles.lean"
mkdir -p "$(dirname "$LEAN_FILE")"

# kebab-case key -> lowerCamelCase constructor name, guillemets around a Lean keyword.
lean_ctor() {
  local name
  name=$(echo "$1" | awk -F- '{ out = $1; for (i = 2; i <= NF; i++) out = out toupper(substr($i, 1, 1)) substr($i, 2); print out }')
  case "$name" in
    end|in|do|then|else|if|fun|let|at|by|from|have|show|match|with|open|where|deriving|instance|structure|inductive)
      echo "«$name»" ;;
    *) echo "$name" ;;
  esac
}

# A JSON value as a Lean `Option String`.
lean_opt() { if [[ -n "$1" ]]; then echo "some \"$1\""; else echo "none"; fi; }

lean_enum() {
  local type=$1 table=$2 doc=$3
  local key ctor
  echo "/-- $doc -/"
  echo "inductive $type where"
  for key in $(jq -r ".${table} | keys_unsorted[]" "$SPEC"); do
    ctor=$(lean_ctor "$key")
    echo "  /-- The \`$key\` row. -/"
    echo "  | $ctor"
  done
  echo "  deriving DecidableEq, Repr"
  echo
  echo "/-- The row's key in \`spec/petri-net-styles.json\`. -/"
  echo "def ${type}.key : $type → String"
  for key in $(jq -r ".${table} | keys_unsorted[]" "$SPEC"); do
    echo "  | .$(lean_ctor "$key") => \"$key\""
  done
  echo
  echo "/-- Every row of the \`${table}\` table, in the order of the file. -/"
  local all=()
  for key in $(jq -r ".${table} | keys_unsorted[]" "$SPEC"); do
    all+=(".$(lean_ctor "$key")")
  done
  local joined
  joined=$(IFS=,; echo "${all[*]}")
  echo "def ${type}.all : List $type := [${joined//,/, }]"
}

{
  cat <<'LEAN_HEADER'
-- GENERATED from spec/petri-net-styles.json. Do not edit manually.
-- Regenerate with: scripts/generate-styles.sh

set_option linter.missingDocs true

/-!
# Export styles (generated)

The node and edge tables of `spec/petri-net-styles.json`, the style table every runtime mapper
draws with (the Rust `styles` module, `StyleConstants.java` and `styles.ts` are generated from
the same file).
Requirement statements name a row (a node category or an edge row), never a colour, shape or
pen width: the values are fixed definitions, read only by facts about the table itself, and
the values the runtimes draw are checked by tests, not by proofs. Values are kept as the JSON
text has them. The cluster, animation, font and graph tables are not mirrored.
-/

namespace Libpetri.Export

LEAN_HEADER
  lean_enum "NodeCat" "node" "A node category: one row of the \`node\` table."
  echo
  lean_enum "EdgeRow" "edge" "An edge row: one row of the \`edge\` table."
  cat <<'LEAN_TYPES'

/-- The attributes of a node row, as the JSON text holds them. -/
structure NodeStyle where
  /-- Graphviz shape. -/
  shape : String
  /-- Fill colour. -/
  fill : String
  /-- Stroke colour. -/
  stroke : String
  /-- Pen width. -/
  penwidth : String
  /-- Line style, when the row has one. -/
  style : Option String
  /-- Height, when the row has one. -/
  height : Option String
  /-- Width, when the row has one. -/
  width : Option String
  deriving DecidableEq, Repr

/-- The attributes of an edge row, as the JSON text holds them. -/
structure EdgeStyle where
  /-- Line colour. -/
  color : String
  /-- Line style. -/
  style : String
  /-- Arrowhead. -/
  arrowhead : String
  /-- Pen width, when the row has one. -/
  penwidth : Option String
  deriving DecidableEq, Repr

/-- The `node` table. -/
def nodeStyle : NodeCat → NodeStyle
LEAN_TYPES
  for key in $(jq -r '.node | keys_unsorted[]' "$SPEC"); do
    read_node "$key" "n_"
    # One line per row: a structure instance continued on a line left of its first field
    # does not parse.
    printf '  | .%s => { shape := "%s", fill := "%s", stroke := "%s", penwidth := "%s", style := %s, height := %s, width := %s }\n' \
      "$(lean_ctor "$key")" "$n_shape" "$n_fill" "$n_stroke" "$n_penwidth" \
      "$(lean_opt "$n_style")" "$(lean_opt "$n_height")" "$(lean_opt "$n_width")"
  done
  echo
  echo "/-- The \`edge\` table. -/"
  echo "def edgeStyle : EdgeRow → EdgeStyle"
  for key in $(jq -r '.edge | keys_unsorted[]' "$SPEC"); do
    read_edge "$key" "e_"
    printf '  | .%s => { color := "%s", style := "%s", arrowhead := "%s", penwidth := %s }\n' \
      "$(lean_ctor "$key")" "$e_color" "$e_estyle" "$e_arrowhead" "$(lean_opt "$e_epenwidth")"
  done
  echo
  echo "end Libpetri.Export"
} > "$LEAN_FILE"

echo "Generated $LEAN_FILE"
echo "Done. All style files regenerated from $SPEC"
