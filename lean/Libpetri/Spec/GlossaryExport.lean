import Libpetri.Spec.Glossary
import Libpetri.Export.Styles

set_option linter.missingDocs true

/-!
# Glossary: graph export (`spec/09-export.md`)

The vocabulary the export requirements are stated in. The exporter has no marking and no state:
it maps a net definition to a typed graph (the runtimes' `graph` module of the Rust export crate, `graph.ts`, the Java
`export/graph` layer, before DOT text), so the export model is pure functions, and a requirement
is a predicate over an abstract function, as EXEC-002 is over an ordering function.

This file holds the emitter half: the n-ary output tree as the runtimes hold it (`OutTree`), the
graph's node references and edges (`NodeRef`, `XEdge`), the per-transition output emitter
(`Emitter`), the labels of EXP-012 and the drawing rule of EXP-012 (`OutTree.junctions`,
`drawOut`), and the projection `OutTree.toOut` onto the firing model's binary `Reference.Out`,
which ties the diagram to the glossary's output arcs (`outPlaces`, `OutputArc`).

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

end Libpetri.Spec
