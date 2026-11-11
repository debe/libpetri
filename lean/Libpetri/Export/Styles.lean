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

/-- A node category: one row of the `node` table. -/
inductive NodeCat where
  /-- The `place` row. -/
  | place
  /-- The `start` row. -/
  | start
  /-- The `end` row. -/
  | «end»
  /-- The `environment` row. -/
  | environment
  /-- The `terminal` row. -/
  | terminal
  /-- The `transition` row. -/
  | transition
  /-- The `xor-junction` row. -/
  | xorJunction
  /-- The `and-junction` row. -/
  | andJunction
  /-- The `interface-port` row. -/
  | interfacePort
  /-- The `sync-channel` row. -/
  | syncChannel
  deriving DecidableEq, Repr

/-- The row's key in `spec/petri-net-styles.json`. -/
def NodeCat.key : NodeCat → String
  | .place => "place"
  | .start => "start"
  | .«end» => "end"
  | .environment => "environment"
  | .terminal => "terminal"
  | .transition => "transition"
  | .xorJunction => "xor-junction"
  | .andJunction => "and-junction"
  | .interfacePort => "interface-port"
  | .syncChannel => "sync-channel"

/-- Every row of the `node` table, in the order of the file. -/
def NodeCat.all : List NodeCat := [.place, .start, .«end», .environment, .terminal, .transition, .xorJunction, .andJunction, .interfacePort, .syncChannel]

/-- An edge row: one row of the `edge` table. -/
inductive EdgeRow where
  /-- The `input` row. -/
  | input
  /-- The `match-input` row. -/
  | matchInput
  /-- The `output` row. -/
  | output
  /-- The `inhibitor` row. -/
  | inhibitor
  /-- The `read` row. -/
  | read
  /-- The `reset` row. -/
  | reset
  /-- The `reset-output` row. -/
  | resetOutput
  deriving DecidableEq, Repr

/-- The row's key in `spec/petri-net-styles.json`. -/
def EdgeRow.key : EdgeRow → String
  | .input => "input"
  | .matchInput => "match-input"
  | .output => "output"
  | .inhibitor => "inhibitor"
  | .read => "read"
  | .reset => "reset"
  | .resetOutput => "reset-output"

/-- Every row of the `edge` table, in the order of the file. -/
def EdgeRow.all : List EdgeRow := [.input, .matchInput, .output, .inhibitor, .read, .reset, .resetOutput]

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
  | .place => { shape := "circle", fill := "#FFFFFF", stroke := "#333333", penwidth := "1.5", style := none, height := none, width := some "0.35" }
  | .start => { shape := "circle", fill := "#d4edda", stroke := "#28a745", penwidth := "2.0", style := none, height := none, width := some "0.35" }
  | .«end» => { shape := "doublecircle", fill := "#cce5ff", stroke := "#004085", penwidth := "2.0", style := none, height := none, width := some "0.35" }
  | .environment => { shape := "circle", fill := "#f8d7da", stroke := "#721c24", penwidth := "2.0", style := some "dashed", height := none, width := some "0.35" }
  | .terminal => { shape := "doublecircle", fill := "#d6d8db", stroke := "#1b1e21", penwidth := "3.0", style := none, height := none, width := some "0.35" }
  | .transition => { shape := "box", fill := "#fff3cd", stroke := "#856404", penwidth := "1.0", style := none, height := some "0.4", width := some "0.8" }
  | .xorJunction => { shape := "diamond", fill := "#FFFFFF", stroke := "#333333", penwidth := "1.0", style := none, height := some "0.3", width := some "0.3" }
  | .andJunction => { shape := "diamond", fill := "#FFFFFF", stroke := "#333333", penwidth := "1.0", style := none, height := some "0.3", width := some "0.3" }
  | .interfacePort => { shape := "circle", fill := "#e7f1ff", stroke := "#1d4ed8", penwidth := "2.0", style := some "dashed", height := none, width := some "0.35" }
  | .syncChannel => { shape := "box", fill := "#f3e8ff", stroke := "#6d28d9", penwidth := "1.5", style := none, height := some "0.4", width := some "0.8" }

/-- The `edge` table. -/
def edgeStyle : EdgeRow → EdgeStyle
  | .input => { color := "#333333", style := "solid", arrowhead := "normal", penwidth := none }
  | .matchInput => { color := "#0d9488", style := "solid", arrowhead := "normal", penwidth := none }
  | .output => { color := "#333333", style := "solid", arrowhead := "normal", penwidth := none }
  | .inhibitor => { color := "#dc3545", style := "solid", arrowhead := "odot", penwidth := none }
  | .read => { color := "#6c757d", style := "dashed", arrowhead := "normal", penwidth := none }
  | .reset => { color := "#fd7e14", style := "bold", arrowhead := "normal", penwidth := some "2.0" }
  | .resetOutput => { color := "#fd7e14", style := "bold", arrowhead := "normal", penwidth := some "2.0" }

end Libpetri.Export
