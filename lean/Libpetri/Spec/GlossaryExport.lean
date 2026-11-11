import Libpetri.Spec.Glossary
import Libpetri.Export.Styles
import Libpetri.Novel.TimedScg.Timing

set_option linter.missingDocs true

/-!
# Glossary: graph export (`spec/09-export.md`)

The vocabulary the export requirements are stated in. The exporter has no marking and no state:
it maps a net definition to a typed graph (the runtimes' `graph` module of the Rust export crate, `graph.ts`, the Java
`export/graph` layer, before DOT text), so the export model is pure functions, and a requirement
is a predicate over an abstract function, as EXEC-002 is over an ordering function.

The emitter half: the n-ary output tree as the runtimes hold it (`OutTree`), the graph's node
references and edges (`NodeRef`, `XEdge`), the per-transition output emitter (`Emitter`), the
labels of EXP-012 and the drawing rule of EXP-012 (`OutTree.junctions`, `drawOut`), and the
projections `OutTree.toOut` and its total form `OutTree.view` onto the firing model's binary
`Reference.Out`, which tie the diagram to the glossary's output arcs (`outPlaces`, `OutputArc`).

The mapper half: the export view of a net (`ExportTrans`, `ExportNet`, with the firing views
`ExportTrans.toTrans` and `ExportNet.toNet`), the configuration (`ExportCfg`), the DOT IDs
(`sanitize`, `nodeId`), the exported graph (`XNode`, `XCluster`, `XGraph`), the `Exporter` and
`TransLabeller` the blocks quantify over, the correlated input label (`corrLabel`), the output
side and junctions of one transition in a graph (`XGraph.outEdges`, `XGraph.junctionsOf`), and
the agreement predicate `ExportAgrees` that makes one exporter, emitter, labellers and place
classifier describe one mapper.

Visual constants (colours, shapes, pen widths) never appear here: an edge names a style row of
`Libpetri.Export` (generated from `spec/petri-net-styles.json`), a junction a node category.

Strings are compared through `List Char` or literal equality only: `String.isPrefixOf` and
`String.splitOn` do not reduce in the kernel on this toolchain, so a statement using them could
not be decided on an example.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## The output tree -/

/-- **Glossary: Output spec** (export view). An output spec as the runtimes hold it ([IO-010] to
[IO-014]): `And` and `Xor` groups keep their children as a list, and a `Timeout` keeps its
duration in milliseconds. The firing model's `Reference.Out` is binary and has no duration, so
`And(a, And(b, c))` and `And(a, b, c)` are one term there and two drawings here
(`OutTree.toOut`). A group may have any number of children: the runtimes' factories refuse an
`Xor` with fewer than two, but Rust's `Out::Xor` is a public variant and a TypeScript node a
plain object, and the mappers have a pass-through arm for a short group. -/
inductive OutTree where
  /-- A `Place` leaf: one token to the place. -/
  | place (p : String)
  /-- A `ForwardInput` leaf: the input token of `src`, forwarded to `dst` ([IO-014]). -/
  | forward (src dst : String)
  /-- An `And` group: every child. -/
  | and (cs : List OutTree)
  /-- An `Xor` group: one child. -/
  | xor (cs : List OutTree)
  /-- A `Timeout` node of `ms` milliseconds over its child ([IO-013]). -/
  | timeout (ms : Nat) (c : OutTree)
  deriving Repr, Inhabited

/-- The kind of a junction node: the kind of the group it is drawn for. -/
inductive JKind where
  /-- An `Xor` junction. -/
  | xor
  /-- An `And` junction. -/
  | and
  deriving DecidableEq, Repr

/-- The node category ([EXP-012], `spec/petri-net-styles.json`) a junction of kind `k` is drawn
with. -/
def JKind.cat : JKind → NodeCat
  | .xor => .xorJunction
  | .and => .andJunction

/-- The kind word of a junction in its DOT ID ([EXP-014]). -/
def JKind.tag : JKind → String
  | .xor => "xor"
  | .and => "and"

/-! ## The graph -/

/-- **Glossary: Node reference.** What a graph node stands for: a transition (by name), the
junction of kind `k` with index `idx` of transition `t`, or a place (by name). The DOT ID
of a node is a function of its reference ([EXP-014]). -/
inductive NodeRef where
  /-- The node of transition `t`. -/
  | trans (t : String)
  /-- Junction `idx` of kind `k` of transition `t`. -/
  | junction (t : String) (k : JKind) (idx : Nat)
  /-- The node of place `p`. -/
  | place (p : String)
  deriving DecidableEq, Repr

/-- The place a node stands for, if it stands for one. -/
def NodeRef.place? : NodeRef → Option String
  | .place p => some p
  | _ => none

/-- `r` with the index of a junction renamed by `ρ`; transition and place nodes unchanged. -/
def NodeRef.renJ (ρ : Nat → Nat) : NodeRef → NodeRef
  | .junction t k i => .junction t k (ρ i)
  | r => r

/-- Is `r` the node of a place in `R`? -/
def NodeRef.inPlaces (R : List String) : NodeRef → Bool
  | .place p => decide (p ∈ R)
  | _ => false

/-- The arc type of a drawn edge (the runtimes' `arcType`): one per arc kind, the combined
reset+output edge of [EXP-013], and the ghost edge of [EXP-017]. -/
inductive ArcType where
  /-- An input arc. -/
  | input
  /-- An output edge (an edge of the output spec). -/
  | output
  /-- An inhibitor arc. -/
  | inhibitor
  /-- A read arc. -/
  | read
  /-- A standalone reset edge. -/
  | reset
  /-- A combined reset+output edge ([EXP-013]). -/
  | resetOutput
  /-- A ghost edge between clusters ([EXP-017]). -/
  | ghost
  deriving DecidableEq, Repr

/-- **Glossary: Edge** (of the exported graph). From `src` to `dst`, of arc type `arc`, drawn
with style row `row`; `dashed` overrides the row's line style (a `ForwardInput` leaf edge is an
`output` edge drawn dashed, as all three mappers draw it); `label` is the edge label;
`ltail` / `lhead` name the clusters a ghost edge is clipped at. -/
structure XEdge where
  /-- Source node. -/
  src : NodeRef
  /-- Target node. -/
  dst : NodeRef
  /-- Arc type. -/
  arc : ArcType
  /-- Style row. -/
  row : EdgeRow
  /-- Drawn dashed in place of the row's line style. -/
  dashed : Bool
  /-- Edge label, if any. -/
  label : Option String
  /-- Cluster the edge's tail is clipped at, if any. -/
  ltail : Option String
  /-- Cluster the edge's head is clipped at, if any. -/
  lhead : Option String
  deriving DecidableEq, Repr

/-- The place an edge ends in, if it ends in a place. -/
def XEdge.placeTarget (e : XEdge) : Option String := e.dst.place?

/-- What one transition's output side draws: its junctions, as (kind, index), and its edges. -/
structure Emitted where
  /-- The junction nodes, as (kind, index). -/
  junctions : List (JKind × Nat) := []
  /-- The edges, in the order drawn. -/
  edges : List XEdge := []
  deriving DecidableEq, Repr

/-- **An output emitter**: given a transition's name `t`, its reset places `R` and its output
tree `o`, the junctions and edges the exporter draws for the output side of `t`. EXP-012 and
EXP-005 are predicates over an emitter; the reset places are an argument because the combined
edge of [EXP-013] replaces a leaf edge into a reset place. -/
abbrev Emitter := String → List String → OutTree → Emitted

/-! ## Labels -/

/-- The label of a `Timeout` node of `ms` milliseconds: `⏱<ms>ms`. -/
def timeoutLabel (ms : Nat) : String := "⏱" ++ toString ms ++ "ms"

/-- The label of a `ForwardInput` leaf edge from `src`: `⟵<src>`, after the label `l` the edge
would otherwise carry and a space, when there is one. -/
def forwardLabel (l : Option String) (src : String) : String :=
  (match l with | some l => l ++ " " | none => "") ++ "⟵" ++ src

/-- **Glossary: Branch label** ([EXP-012]). The label of the edge into a child of an `Xor`
junction: the place name of a `Place` child, the timeout label of a `Timeout` child, none for a
group. A `ForwardInput` child to `P` is drawn as a `Place` leaf for `P` ([EXP-012]), so its
branch label is `P`; no transition that builds has one ([IO-013], [IO-014]). -/
def branchLabel : OutTree → Option String
  | .place p => some p
  | .forward _ dst => some dst
  | .timeout ms _ => some (timeoutLabel ms)
  | .and _ => none
  | .xor _ => none

/-- Where a child of a group is drawn from: `pass l`, through a group with fewer than two
children, whose edge would carry `l`; `junction k`, below a junction of kind `k`. -/
inductive Under where
  /-- Through a short group whose edge would carry `l`. -/
  | pass (l : Option String)
  /-- Below a junction of kind `k`. -/
  | junction (k : JKind)

/-- The label the edge into child `c` inherits: the passed label through a short group, the
branch label below an `Xor` junction, none below an `And` junction. -/
def Under.label : Under → OutTree → Option String
  | .pass l, _ => l
  | .junction .xor, c => branchLabel c
  | .junction .and, _ => none

/-! ## The drawing rule of EXP-012 -/

mutual
/-- **Glossary: Junctions of an output spec** ([EXP-012]). The kinds of the groups with two or
more children, in pre-order (a group before its children, children left to right). -/
def OutTree.junctions : OutTree → List JKind
  | .place _ => []
  | .forward _ _ => []
  | .timeout _ c => OutTree.junctions c
  | .and cs => (if 2 ≤ cs.length then [JKind.and] else []) ++ OutTree.junctionsL cs
  | .xor cs => (if 2 ≤ cs.length then [JKind.xor] else []) ++ OutTree.junctionsL cs
/-- `OutTree.junctions` of a list of children, concatenated. -/
def OutTree.junctionsL : List OutTree → List JKind
  | [] => []
  | c :: cs => OutTree.junctions c ++ OutTree.junctionsL cs
end

/-- A drawn edge of the drawing rule: its ends, whether it is dashed, and its label. -/
structure DrawnEdge where
  /-- Source node. -/
  src : NodeRef
  /-- Target node. -/
  dst : NodeRef
  /-- Dashed (a `ForwardInput` leaf edge). -/
  dashed : Bool
  /-- Label, if any. -/
  label : Option String
  deriving DecidableEq, Repr

mutual
/-- **Glossary: The drawing of an output spec** ([EXP-012]). The output edges of transition `t`
for the subtree `o`, drawn from node `par` with inherited label `l`, the junctions of `o`
numbered from `n` in pre-order. One clause per sentence of EXP-012:

* a `Place` leaf for `p`: one solid edge `par → p` with the inherited label;
* a `ForwardInput` leaf from `s` to `d`: the edge of a `Place` leaf for `d`, dashed, labelled
  `forwardLabel l s` (`⟵s` after the inherited label and a space);
* a `Timeout` node of `ms`: its child, with label `⏱<ms>ms` in place of the inherited one;
* a group with two or more children: one junction `n` of the group's kind, one solid edge
  `par → junction` with the inherited label, then the children below the junction, each with
  the label `Under.label` gives it (branch label below `Xor`, none below `And`);
* a group with fewer than two children: no junction; its children drawn from `par` with the
  inherited label. -/
def drawOut (t : String) (par : NodeRef) (l : Option String) (n : Nat) :
    OutTree → List DrawnEdge
  | .place p => [⟨par, .place p, false, l⟩]
  | .forward s d => [⟨par, .place d, true, some (forwardLabel l s)⟩]
  | .timeout ms c => drawOut t par (some (timeoutLabel ms)) n c
  | .and cs =>
    if 2 ≤ cs.length then
      ⟨par, .junction t .and n, false, l⟩ ::
        drawOutL t (.junction t .and n) (.junction .and) (n + 1) cs
    else drawOutL t par (.pass l) n cs
  | .xor cs =>
    if 2 ≤ cs.length then
      ⟨par, .junction t .xor n, false, l⟩ ::
        drawOutL t (.junction t .xor n) (.junction .xor) (n + 1) cs
    else drawOutL t par (.pass l) n cs
/-- `drawOut` of a list of children below `par`, the junction numbering continued from child to
child. -/
def drawOutL (t : String) (par : NodeRef) (u : Under) (n : Nat) :
    List OutTree → List DrawnEdge
  | [] => []
  | c :: cs => drawOut t par (u.label c) n c ++ drawOutL t par u (n + (OutTree.junctions c).length) cs
end

/-- The drawing of transition `t`'s whole output spec `o`: from the transition, no inherited
label, junctions numbered from 0. -/
def Drawing (t : String) (o : OutTree) : List DrawnEdge := drawOut t (.trans t) none 0 o

/-- What EXP-012 constrains of an emitted edge, after renaming junction indices by `ρ`: its two
ends always, and its arc type, style row, dash and label unless it ends in a reset place (where
[EXP-013] decides them). -/
def XEdge.seen (R : List String) (ρ : Nat → Nat) (e : XEdge) :
    NodeRef × NodeRef × Option (ArcType × EdgeRow × Bool × Option String) :=
  (e.src.renJ ρ, e.dst.renJ ρ,
    if e.dst.inPlaces R then none else some (e.arc, e.row, e.dashed, e.label))

/-- The same view of an edge of the drawing rule: an output edge with the output row. -/
def DrawnEdge.seen (R : List String) (d : DrawnEdge) :
    NodeRef × NodeRef × Option (ArcType × EdgeRow × Bool × Option String) :=
  (d.src, d.dst, if d.dst.inPlaces R then none else some (.output, .output, d.dashed, d.label))

/-! ## The join to the firing model -/

mutual
/-- The places the leaves of an output tree name, left to right (`allPlaces` of [IO-017]; a
`ForwardInput` contributes its target). -/
def OutTree.leafPlaces : OutTree → List String
  | .place p => [p]
  | .forward _ d => [d]
  | .timeout _ c => OutTree.leafPlaces c
  | .and cs => OutTree.leafPlacesL cs
  | .xor cs => OutTree.leafPlacesL cs
/-- `OutTree.leafPlaces` of a list of children, concatenated. -/
def OutTree.leafPlacesL : List OutTree → List String
  | [] => []
  | c :: cs => OutTree.leafPlaces c ++ OutTree.leafPlacesL cs
end

/-- Fold a list of binary output specs right-nested with `mk`, as `Reference.Load.nest` does;
`none` for the empty list. -/
def nestOpt (mk : Out String → Out String → Out String) : List (Out String) → Option (Out String)
  | [] => none
  | [x] => some x
  | x :: xs => (nestOpt mk xs).map (mk x)

mutual
/-- **The firing model's view of an output tree**: the binary `Reference.Out` the firing
relation reads, groups folded right-nested and the timeout duration dropped; `none` when a
group is empty (no output spec has one: [IO-011] and [IO-012] ask for children). -/
def OutTree.toOut : OutTree → Option (Out String)
  | .place p => some (.place p)
  | .forward s d => some (.forward s d)
  | .timeout _ c => (OutTree.toOut c).map .timeout
  | .and cs => (OutTree.toOutL cs).bind (nestOpt .and)
  | .xor cs => (OutTree.toOutL cs).bind (nestOpt .xor)
/-- `OutTree.toOut` of every child, `none` if any child has none. -/
def OutTree.toOutL : List OutTree → Option (List (Out String))
  | [] => some []
  | c :: cs =>
    match OutTree.toOut c, OutTree.toOutL cs with
    | some x, some xs => some (x :: xs)
    | _, _ => none
end

mutual
/-- **The firing model's view of an output tree, total.** As `OutTree.toOut`, except that a group
with no child that has a view is dropped instead of making the whole view fail: the places a
view names are then always the leaf places (`view_places` in `Reference/Export.lean`), and on
every tree without an empty group it is `toOut` (`view_of_toOut`). No transition that builds has
an empty group ([IO-011], [IO-012]), so the two differ only on trees no net holds; the total form
lets the export view of a net (`ExportNet.toNet`) exist for every net the exporter is handed. -/
def OutTree.view : OutTree → Option (Out String)
  | .place p => some (.place p)
  | .forward s d => some (.forward s d)
  | .timeout _ c => (OutTree.view c).map .timeout
  | .and cs => nestOpt .and (OutTree.viewL cs)
  | .xor cs => nestOpt .xor (OutTree.viewL cs)
/-- `OutTree.view` of every child that has one, in order. -/
def OutTree.viewL : List OutTree → List (Out String)
  | [] => []
  | c :: cs => (OutTree.view c).toList ++ OutTree.viewL cs
end

/-! ## The export view of a net (the mapper half) -/

open Libpetri.Novel.Seam (NTransition NInSpec)
open Libpetri.Novel.TimedScg (Timing)

/-- **A transition, as the exporter reads it**: its name and its input (place and cardinality),
inhibitor, read and reset arcs (`core`, the same record the firing model fires on), its output
spec as an n-ary tree (`none`: no output spec), its timing ([TIME-001]) and priority, and the
correlated places of its ν-net match specification ([NU-020]; empty without one). -/
structure ExportTrans where
  /-- Name and input, inhibitor, read and reset arcs. -/
  core   : NTransition String
  /-- Output spec, if any. -/
  out    : Option OutTree := none
  /-- Timing. -/
  timing : Timing := .immediate
  /-- Priority. -/
  prio   : Int := 0
  /-- The places a ν-net match specification correlates ([NU-020]). -/
  corr   : List String := []

/-- The transition's name. -/
def ExportTrans.name (t : ExportTrans) : String := t.core.name

/-- The places the leaves of the output spec name, left to right (`allPlaces` of [IO-017]); empty
without an output spec. -/
def ExportTrans.outLeaves (t : ExportTrans) : List String := (t.out.map OutTree.leafPlaces).getD []

/-- Every place an arc of `t` touches: input, output (every leaf place), inhibitor, read and reset
arcs, in that order. -/
def ExportTrans.touched (t : ExportTrans) : List String :=
  t.core.inputs.map (·.place) ++ t.outLeaves ++ t.core.inhibitors ++ t.core.reads ++ t.core.resets

/-- **The firing model's view of a transition** (`toTrans`): the same arcs (`core`), the output
spec's view (`OutTree.view`), and the reapable bit of its timing, as `TransDef.toTrans` sets it.
The glossary's arc predicates (`InputArc`, `OutputArc`, `InhibitorArc`, `ReadArc`, `ResetArc`)
over `t.toTrans` are the arcs the firing relations fire on. -/
def ExportTrans.toTrans (t : ExportTrans) : Trans String :=
  ⟨t.core, t.out.bind OutTree.view, t.timing.reapable⟩

/-- **A net, as the exporter reads it**: its declared places (a built net's places, terminal
places included), its transitions in declaration order, its terminal places ([EXEC-042]) and
its subnet-membership map ([MOD-026]: the subnet a node name belongs to, if any). -/
structure ExportNet where
  /-- Declared places. -/
  places : List String := []
  /-- Transitions, in declaration order. -/
  trans  : List ExportTrans := []
  /-- Terminal places ([EXEC-042]). -/
  term   : List String := []
  /-- Subnet membership ([MOD-026]). -/
  member : String → Option String := fun _ => none

/-- The firing model's view of the net. -/
def ExportNet.toNet (X : ExportNet) : Reference.Net String := ⟨X.places, X.trans.map ExportTrans.toTrans⟩

/-- Is `p` a terminal place of `X`? -/
def ExportNet.isTerm (X : ExportNet) (p : String) : Bool := decide (p ∈ X.term)

/-- Some arc of some transition of `X` touches `p`. -/
def ExportNet.Touched (X : ExportNet) (p : String) : Prop := ∃ t ∈ X.trans, p ∈ t.touched

/-- The transitions of `X` have pairwise distinct names, and no transition has two input arcs on
one place ([CORE-030]). Statements that count the nodes of a transition, or that read one input
edge per input arc, assume it; the exporter keys transition nodes by name. -/
def ExportNet.Distinct (X : ExportNet) : Prop :=
  (X.trans.map ExportTrans.name).Nodup ∧ ∀ t ∈ X.trans, (t.core.inputs.map (·.place)).Nodup

/-- The layout direction of a drawing. -/
inductive RankDir where
  /-- Top to bottom. -/
  | TB
  /-- Left to right. -/
  | LR
  /-- Bottom to top. -/
  | BT
  /-- Right to left. -/
  | RL
  deriving DecidableEq, Repr

/-- Where cluster keys come from ([EXP-016], [MOD-040]). -/
inductive ClusterSource where
  /-- Membership metadata, else the instance prefix. -/
  | auto
  /-- Membership metadata only. -/
  | metadata
  /-- The instance prefix only. -/
  | «prefix»
  /-- No clustering. -/
  | none
  deriving DecidableEq, Repr

/-- **The export configuration** ([EXP-007]): layout direction, the three show flags, the
environment places ([ENV-001]; the runtimes take them from the configuration, not from the net)
and the cluster source. The defaults are the runtimes' defaults. The show-types flag is accepted
and changes nothing: no mapper draws token types (ruling D41). -/
structure ExportCfg where
  /-- Layout direction. -/
  dir           : RankDir := .TB
  /-- Show token types (no effect, ruling D41). -/
  showTypes     : Bool := true
  /-- Show the timing interval on transitions. -/
  showIntervals : Bool := true
  /-- Show a non-zero priority on transitions. -/
  showPriority  : Bool := true
  /-- Environment places ([ENV-001]). -/
  env           : List String := []
  /-- Cluster source. -/
  cluster       : ClusterSource := .auto

/-- Is `p` an environment place under `cfg`? -/
def ExportCfg.isEnv (cfg : ExportCfg) (p : String) : Bool := decide (p ∈ cfg.env)

/-! ## DOT IDs -/

/-- The character `sanitize` keeps or replaces: an ASCII letter, digit or `_` is kept, every other
character becomes `_` ([EXP-014]; ruling D46: the rule is stated for ASCII names, other
characters are implementation-defined). -/
def sanitizeChar (c : Char) : Char := if c.isAlphanum || c == '_' then c else '_'

/-- **Glossary: sanitize** ([EXP-014]): the name with every character outside `[A-Za-z0-9_]`
replaced by `_`. -/
def sanitize (s : String) : String := String.ofList (s.toList.map sanitizeChar)

/-- **Glossary: Node ID** ([EXP-014]): `p_<sanitize p>` for a place, `t_<sanitize t>` for a
transition, `j_<sanitize t>__<kind>_<idx>` for junction `idx` of kind `kind` of `t`. -/
def nodeId : NodeRef → String
  | .place p => "p_" ++ sanitize p
  | .trans t => "t_" ++ sanitize t
  | .junction t k i => "j_" ++ sanitize t ++ "__" ++ k.tag ++ "_" ++ toString i

/-! ## The exported graph -/

/-- The glyph a junction node of kind `k` is labelled with ([EXP-012]): `✕` for `Xor`, `✚` for
`And`. A visual constant: statements do not read it. -/
def JKind.glyph : JKind → String
  | .xor => "✕"
  | .and => "✚"

/-- The transition or junction-owning transition a node belongs to: `t` for the node of `t` and
for every junction of `t`, none for a place. -/
def NodeRef.owner? : NodeRef → Option String
  | .trans t => some t
  | .junction t _ _ => some t
  | .place _ => none

/-- **Glossary: Node** (of the exported graph): what it stands for (`ref`), its DOT ID, its node
category (a row of the node table), its label and its external label (`xlabel`). -/
structure XNode where
  /-- What the node stands for. -/
  ref    : NodeRef
  /-- The DOT ID. -/
  id     : String
  /-- The node category (style row). -/
  cat    : NodeCat
  /-- The label drawn inside the node. -/
  label  : String
  /-- The label drawn beside the node, if any. -/
  xlabel : Option String
  deriving DecidableEq, Repr

/-- **Glossary: Cluster** (of the exported graph, [EXP-016]): its key, its DOT ID, its label, the
key of the cluster it is nested in (none at top level), and the nodes that are its direct
members. -/
structure XCluster where
  /-- The cluster key. -/
  key     : String
  /-- The DOT ID. -/
  id      : String
  /-- The label. -/
  label   : String
  /-- The key of the enclosing cluster, if any. -/
  parent  : Option String
  /-- The direct members. -/
  members : List NodeRef
  deriving DecidableEq, Repr

/-- **Glossary: Exported graph**: the typed graph a mapper builds before DOT text (the runtimes'
graph layer): layout direction, the `compound` graph attribute ([EXP-017]), nodes, edges and
clusters, each list in the order drawn. -/
structure XGraph where
  /-- Layout direction. -/
  dir      : RankDir
  /-- The `compound` graph attribute. -/
  compound : Bool
  /-- Nodes. -/
  nodes    : List XNode
  /-- Edges, ghost edges included. -/
  edges    : List XEdge
  /-- Clusters. -/
  clusters : List XCluster
  deriving DecidableEq, Repr

/-- **An exporter**: the typed graph a configuration and a net are drawn as. It reads no marking
([EXP-011] AC2). Every export requirement but EXP-005, EXP-006, EXP-007's label line, EXP-008 and
EXP-012 is a predicate over an exporter. -/
abbrev Exporter := ExportCfg → ExportNet → XGraph

/-- **A transition labeller** ([EXP-007]): the label of a transition node, from the
configuration, the transition's name, timing and priority. -/
abbrev TransLabeller := ExportCfg → String → Timing → Int → String

/-- The label of a correlated input edge ([EXP-018]): `⟨n⟩`, then a space and the cardinality
label when the arc has one. -/
def corrLabel (card : Option String) : String :=
  "⟨n⟩" ++ (match card with | some c => " " ++ c | none => "")

/-- What emitter `Em` draws for the output side of `t`: nothing without an output spec. -/
def Emitter.ofTrans (Em : Emitter) (t : ExportTrans) : Emitted :=
  match t.out with
  | some o => Em t.name t.core.resets o
  | none => {}

/-- Is `e` on the output side of transition `t`: an edge of arc type `output` or `resetOutput`
whose source is the node of `t` or a junction of `t`? -/
def XEdge.outSideOf (t : String) (e : XEdge) : Bool :=
  e.src.owner? == some t && (e.arc == .output || e.arc == .resetOutput)

/-- The output side of transition `t` in a drawn graph: its edges `XEdge.outSideOf t`, in the
order drawn. -/
def XGraph.outEdges (g : XGraph) (t : String) : List XEdge := g.edges.filter (XEdge.outSideOf t)

/-- The (kind, index) of `r` when it is a junction of transition `t`. -/
def NodeRef.junctionOf (t : String) : NodeRef → Option (JKind × Nat)
  | .junction t' k i => if t' = t then some (k, i) else none
  | _ => none

/-- The junction nodes of transition `t` in a drawn graph, as (kind, index), in the order drawn. -/
def XGraph.junctionsOf (g : XGraph) (t : String) : List (JKind × Nat) :=
  g.nodes.filterMap fun n => n.ref.junctionOf t

/-- **The export agreement** (`ExportAgrees`). Exporter `E`, output emitter `Em`, cardinality
labeller `L`, transition labeller `TL` and place classifier `C` (EXP-008's `PlaceClassifier`)
describe one mapper: on every net whose transition names are distinct and whose transitions have
at most one input arc per place,

* the output side of each transition, and its junction nodes, are what `Em` draws for it, up to
  order, and the edges out of each junction node are `Em`'s in `Em`'s order (the order of the
  children, [EXP-005]);
* each transition node is labelled by `TL`;
* each place node has the category `C` gives it, with the configuration's environment places and
  the net's terminal places;
* each input edge of a transition carries the label `L` gives its cardinality, prefixed with
  `⟨n⟩` when the place is correlated ([EXP-018]).

The EXP blocks quantify over different abstract functions; without this predicate each could be
met by a different function and their conjunction would say nothing about one mapper. -/
def ExportAgrees (E : Exporter) (Em : Emitter) (L : Card → Option String) (TL : TransLabeller)
    (C : Reference.Net String → (String → Bool) → (String → Bool) → String → NodeCat) : Prop :=
  ∀ (cfg : ExportCfg) (X : ExportNet), X.Distinct →
    (∀ t ∈ X.trans,
      ((E cfg X).outEdges t.name).Perm (Em.ofTrans t).edges ∧
      ((E cfg X).junctionsOf t.name).Perm (Em.ofTrans t).junctions ∧
      ∀ (k : JKind) (i : Nat),
        ((E cfg X).outEdges t.name).filter (fun e => e.src == .junction t.name k i) =
          (Em.ofTrans t).edges.filter (fun e => e.src == .junction t.name k i)) ∧
    (∀ n ∈ (E cfg X).nodes, ∀ t ∈ X.trans, n.ref = .trans t.name →
      n.label = TL cfg t.name t.timing t.prio) ∧
    (∀ n ∈ (E cfg X).nodes, ∀ p, n.ref = .place p →
      n.cat = C X.toNet cfg.isEnv X.isTerm p) ∧
    (∀ e ∈ (E cfg X).edges, ∀ t ∈ X.trans, ∀ s ∈ t.core.inputs,
      e.arc = .input → e.src = .place s.place → e.dst = .trans t.name →
      e.label = if s.place ∈ t.corr then some (corrLabel (L s.card)) else L s.card)

end Libpetri.Spec
