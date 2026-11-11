import Libpetri.Spec.GlossaryExport
import Libpetri.Spec.Req.EXP_006
import Libpetri.Spec.Req.EXP_008
import Libpetri.Reference.Build

set_option linter.missingDocs true

/-!
# Reference export: the output emitter (`spec/09-export.md`)

The reference for the output side of one transition in an exported graph: the junction emitter
every runtime mapper runs (`emit_output` / `emit_group` / `push_leaf_edge` in the Rust crate
`libpetri-export`, module `mapper`; `emitOutput` / `emitGroup` / `pushLeafEdge` in
`PetriNetGraphMapper.java` and `petri-net-mapper.ts`). It is written as the mappers are: one pass
over the tree with a running junction counter, appending to the emitted junctions and edges.

* LEAF: a `Place` leaf for `p` (or a `ForwardInput` leaf into `p`, dashed, its label
  `forwardLabel`) appends one edge from the parent: the combined reset+output edge when `p` is a
  reset place ([EXP-013]), else an output edge with the inherited label.
* TIMEOUT: the child, with the timeout label in place of the inherited one.
* GROUP: a group with two or more children takes the next index, appends its junction and one
  output edge from the parent with the inherited label, and walks its children below the
  junction; below an `Xor` junction each child's label is inferred from the child, below an
  `And` junction it is none. A shorter group passes parent and label through.

The emitter half (wave W4 tracer) comes first. The mapper half follows it: the transition
label (`refTransLabel`), the edges of one transition (`refTransEdges`: input, output, inhibitor,
read, then the standalone reset edges), the place, transition and junction nodes (`refNodes`), and
the exporter `refExportWith S`, parametric in a cluster stage `S` that may only add clusters and
ghost edges. The clustering itself (`Reference/ExportCluster.lean`) supplies the stage of the
final exporter; `refExportFlat` is the exporter with no clustering (the runtimes' cluster source
`none`). Every lemma of the mapper half holds for every stage, so a block proved for
`refExportWith S` holds of the clustered exporter as well.

Two facts tie the emitter to the rest: `refEmit_draws` (the emitter draws `drawOut`, the drawing
rule of the glossary, by mutual structural induction) and `refEmit_leafTargets` (the places its
edges end in are exactly the output places `outPlaces` the firing model reads off the same
output spec, the join to `OutputArc`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## The reference emitter -/

/-- The label the mappers infer for the edge into a child of an `Xor` junction
(`infer_branch_label` / `inferBranchLabel`): the place name, the target of a `ForwardInput`,
the timeout label, none for a group. -/
def refInferBranchLabel : OutTree → Option String
  | .place p => some p
  | .timeout ms _ => some ("⏱" ++ toString ms ++ "ms")
  | .forward _ dst => some dst
  | _ => none

/-- The label the reference emitter hands child `c` (the mappers' `childLabel`): the passed label
through a short group, the inferred branch label below `Xor`, none below `And`. -/
def refChildLabel : Under → OutTree → Option String
  | .pass l, _ => l
  | .junction .xor, c => refInferBranchLabel c
  | .junction .and, _ => none

/-- The leaf edge into `p` from `par` (`push_leaf_edge` / `pushLeafEdge`): the combined
reset+output edge, labelled `reset+out`, when `p` is a reset place ([EXP-013]); else an output
edge with label `l`, dashed for a `ForwardInput` leaf. -/
def refLeafEdge (R : List String) (par : NodeRef) (p : String) (dashed : Bool)
    (l : Option String) : XEdge :=
  if p ∈ R then ⟨par, .place p, .resetOutput, .resetOutput, false, some "reset+out", none, none⟩
  else ⟨par, .place p, .output, .output, dashed, l, none, none⟩

/-- The edge from `par` into junction `j` (`emit_group` / `emitGroup`): an output edge with the
inherited label. -/
def refJunctionEdge (par j : NodeRef) (l : Option String) : XEdge :=
  ⟨par, j, .output, .output, false, l, none, none⟩

mutual
/-- The reference emitter's walk. State: the next junction index and what was emitted so far. -/
def refEmitOut (t : String) (R : List String) (par : NodeRef) (l : Option String) :
    OutTree → Nat × Emitted → Nat × Emitted
  | .place p, (n, e) => (n, { e with edges := e.edges ++ [refLeafEdge R par p false l] })
  | .forward src dst, (n, e) =>
    let fl := (match l with | some l => l ++ " " | none => "") ++ "⟵" ++ src
    (n, { e with edges := e.edges ++ [refLeafEdge R par dst true (some fl)] })
  | .timeout ms c, s => refEmitOut t R par (some ("⏱" ++ toString ms ++ "ms")) c s
  | .and cs, (n, e) =>
    if 2 ≤ cs.length then
      refEmitOutL t R (.junction t .and n) (.junction .and) cs
        (n + 1, { junctions := e.junctions ++ [(.and, n)],
                  edges := e.edges ++ [refJunctionEdge par (.junction t .and n) l] })
    else refEmitOutL t R par (.pass l) cs (n, e)
  | .xor cs, (n, e) =>
    if 2 ≤ cs.length then
      refEmitOutL t R (.junction t .xor n) (.junction .xor) cs
        (n + 1, { junctions := e.junctions ++ [(.xor, n)],
                  edges := e.edges ++ [refJunctionEdge par (.junction t .xor n) l] })
    else refEmitOutL t R par (.pass l) cs (n, e)
/-- The walk over the children of a group, left to right. -/
def refEmitOutL (t : String) (R : List String) (par : NodeRef) (u : Under) :
    List OutTree → Nat × Emitted → Nat × Emitted
  | [], s => s
  | c :: cs, s => refEmitOutL t R par u cs (refEmitOut t R par (refChildLabel u c) c s)
end

/-- **The reference output emitter** (witness model): the junctions and edges the output side of
transition `t` with reset places `R` and output tree `o` is drawn with, from the transition,
junctions numbered from 0. -/
def refEmit : Emitter := fun t R o => (refEmitOut t R (.trans t) none o (0, {})).2

#spec_witness refEmit

/-! ## The emitter draws the drawing rule -/

/-- The edge the reference draws for an edge of the drawing rule: the combined edge into a reset
place, else an output edge with the rule's dash and label. -/
def refRealize (R : List String) (d : DrawnEdge) : XEdge :=
  match d.dst with
  | .place p =>
    if p ∈ R then ⟨d.src, .place p, .resetOutput, .resetOutput, false, some "reset+out", none, none⟩
    else ⟨d.src, .place p, .output, .output, d.dashed, d.label, none, none⟩
  | j => ⟨d.src, j, .output, .output, d.dashed, d.label, none, none⟩

/-- The mappers' inferred branch label is the glossary's branch label. -/
theorem refInferBranchLabel_eq (c : OutTree) : refInferBranchLabel c = branchLabel c := by
  cases c <;> rfl

/-- The reference's child label is the glossary's inherited label. -/
theorem refChildLabel_eq (u : Under) (c : OutTree) : refChildLabel u c = u.label c := by
  rcases u with l | k
  · rfl
  · cases k
    · exact refInferBranchLabel_eq c
    · rfl

mutual
/-- The reference walk, in closed form: it advances the counter by the number of junctions of
`o`, appends the junctions of `o` numbered from `n`, and appends the edges of the drawing rule. -/
theorem refEmitOut_eq (t : String) (R : List String) (par : NodeRef) (l : Option String) :
    ∀ (o : OutTree) (n : Nat) (e : Emitted),
      refEmitOut t R par l o (n, e) =
        (n + (OutTree.junctions o).length,
          { junctions := e.junctions ++ (OutTree.junctions o).zipIdx n,
            edges := e.edges ++ (drawOut t par l n o).map (refRealize R) })
  | .place p, n, e => by
    simp only [refEmitOut, OutTree.junctions, drawOut, List.length_nil, Nat.add_zero,
      List.zipIdx_nil, List.append_nil, List.map_cons, List.map_nil]
    congr 2
  | .forward s d, n, e => by
    simp only [refEmitOut, OutTree.junctions, drawOut, List.length_nil, Nat.add_zero,
      List.zipIdx_nil, List.append_nil, List.map_cons, List.map_nil, forwardLabel]
    congr 2
  | .timeout ms c, n, e => by
    simp only [refEmitOut, OutTree.junctions, drawOut, timeoutLabel]
    exact refEmitOut_eq t R par _ c n e
  | .and cs, n, e => by
    by_cases h : 2 ≤ cs.length
    · have ih := refEmitOutL_eq t R (.junction t .and n) (.junction .and) cs (n + 1)
        { junctions := e.junctions ++ [(.and, n)],
          edges := e.edges ++ [refJunctionEdge par (.junction t .and n) l] }
      simp only [refEmitOut, OutTree.junctions, drawOut, h, if_true] at ih ⊢
      rw [ih]
      simp only [List.length_cons, List.zipIdx_cons, List.append_assoc,
        List.cons_append, List.nil_append, List.map_cons, refJunctionEdge, refRealize]
      congr 1
      omega
    · have ih := refEmitOutL_eq t R par (.pass l) cs n e
      simp only [refEmitOut, OutTree.junctions, drawOut, h, if_false] at ih ⊢
      simpa using ih
  | .xor cs, n, e => by
    by_cases h : 2 ≤ cs.length
    · have ih := refEmitOutL_eq t R (.junction t .xor n) (.junction .xor) cs (n + 1)
        { junctions := e.junctions ++ [(.xor, n)],
          edges := e.edges ++ [refJunctionEdge par (.junction t .xor n) l] }
      simp only [refEmitOut, OutTree.junctions, drawOut, h, if_true] at ih ⊢
      rw [ih]
      simp only [List.length_cons, List.zipIdx_cons, List.append_assoc,
        List.cons_append, List.nil_append, List.map_cons, refJunctionEdge, refRealize]
      congr 1
      omega
    · have ih := refEmitOutL_eq t R par (.pass l) cs n e
      simp only [refEmitOut, OutTree.junctions, drawOut, h, if_false] at ih ⊢
      simpa using ih
/-- The walk over a list of children, in closed form. -/
theorem refEmitOutL_eq (t : String) (R : List String) (par : NodeRef) (u : Under) :
    ∀ (cs : List OutTree) (n : Nat) (e : Emitted),
      refEmitOutL t R par u cs (n, e) =
        (n + (OutTree.junctionsL cs).length,
          { junctions := e.junctions ++ (OutTree.junctionsL cs).zipIdx n,
            edges := e.edges ++ (drawOutL t par u n cs).map (refRealize R) })
  | [], n, e => by simp [refEmitOutL, OutTree.junctionsL, drawOutL]
  | c :: cs, n, e => by
    have h1 := refEmitOut_eq t R par (refChildLabel u c) c n e
    simp only [refEmitOutL, h1]
    rw [refEmitOutL_eq t R par u cs]
    simp only [OutTree.junctionsL, drawOutL, refChildLabel_eq, List.length_append,
      List.zipIdx_append, List.map_append, List.append_assoc, Nat.add_assoc]
end

/-- The reference emitter in closed form: the junctions of `o` in pre-order, numbered from 0,
and the edges of the drawing rule, each realised as the reference draws it. -/
theorem refEmit_draws (t : String) (R : List String) (o : OutTree) :
    refEmit t R o = { junctions := (OutTree.junctions o).zipIdx,
                      edges := (Drawing t o).map (refRealize R) } := by
  simp [refEmit, Drawing, refEmitOut_eq]

/-! ## The join: the places the emitter draws into are the firing model's output places -/

mutual
/-- The edges of the drawing rule that end in a place end in the leaf places, in order. -/
theorem drawOut_places (t : String) (par : NodeRef) (l : Option String) :
    ∀ (o : OutTree) (n : Nat),
      (drawOut t par l n o).filterMap (fun d => d.dst.place?) = OutTree.leafPlaces o
  | .place p, n => by simp [drawOut, OutTree.leafPlaces, NodeRef.place?]
  | .forward s d, n => by simp [drawOut, OutTree.leafPlaces, NodeRef.place?]
  | .timeout ms c, n => by simp only [drawOut, OutTree.leafPlaces]; exact drawOut_places t par _ c n
  | .and cs, n => by
    by_cases h : 2 ≤ cs.length
    · simp only [drawOut, OutTree.leafPlaces, h, if_true, List.filterMap_cons, NodeRef.place?]
      exact drawOutL_places t _ _ cs (n + 1)
    · simp only [drawOut, OutTree.leafPlaces, h, if_false]
      exact drawOutL_places t _ _ cs n
  | .xor cs, n => by
    by_cases h : 2 ≤ cs.length
    · simp only [drawOut, OutTree.leafPlaces, h, if_true, List.filterMap_cons, NodeRef.place?]
      exact drawOutL_places t _ _ cs (n + 1)
    · simp only [drawOut, OutTree.leafPlaces, h, if_false]
      exact drawOutL_places t _ _ cs n
/-- The list form of `drawOut_places`. -/
theorem drawOutL_places (t : String) (par : NodeRef) (u : Under) :
    ∀ (cs : List OutTree) (n : Nat),
      (drawOutL t par u n cs).filterMap (fun d => d.dst.place?) = OutTree.leafPlacesL cs
  | [], n => by simp [drawOutL, OutTree.leafPlacesL]
  | c :: cs, n => by
    simp only [drawOutL, OutTree.leafPlacesL, List.filterMap_append]
    rw [drawOut_places t par _ c n, drawOutL_places t par u cs _]
end

/-- Folding right-nested keeps the output places in order. -/
theorem nestOpt_places (mk : Out String → Out String → Out String)
    (hmk : ∀ a b, outPlaces (mk a b) = outPlaces a ++ outPlaces b) :
    ∀ (xs : List (Out String)) (y : Out String), nestOpt mk xs = some y →
      outPlaces y = xs.flatMap outPlaces
  | [], y, h => by simp [nestOpt] at h
  | [x], y, h => by simp [nestOpt] at h; subst h; simp
  | x :: x2 :: xs, y, h => by
    simp only [nestOpt, Option.map_eq_some_iff] at h
    obtain ⟨z, hz, rfl⟩ := h
    rw [hmk, nestOpt_places mk hmk (x2 :: xs) z hz]
    simp

mutual
/-- The firing model's view of an output tree names the leaf places, in order. -/
theorem toOut_places : ∀ (o : OutTree) (o' : Out String), o.toOut = some o' →
    outPlaces o' = OutTree.leafPlaces o
  | .place p, o', h => by simp [OutTree.toOut] at h; subst h; rfl
  | .forward s d, o', h => by simp [OutTree.toOut] at h; subst h; rfl
  | .timeout ms c, o', h => by
    simp only [OutTree.toOut, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact toOut_places c x hx
  | .and cs, o', h => by
    simp only [OutTree.toOut, Option.bind_eq_some_iff] at h
    obtain ⟨xs, hxs, hy⟩ := h
    rw [nestOpt_places .and (fun _ _ => rfl) xs o' hy, OutTree.leafPlaces]
    exact toOutL_places cs xs hxs
  | .xor cs, o', h => by
    simp only [OutTree.toOut, Option.bind_eq_some_iff] at h
    obtain ⟨xs, hxs, hy⟩ := h
    rw [nestOpt_places .xor (fun _ _ => rfl) xs o' hy, OutTree.leafPlaces]
    exact toOutL_places cs xs hxs
/-- The list form of `toOut_places`. -/
theorem toOutL_places : ∀ (cs : List OutTree) (xs : List (Out String)), OutTree.toOutL cs = some xs →
    xs.flatMap outPlaces = OutTree.leafPlacesL cs
  | [], xs, h => by simp [OutTree.toOutL] at h; subst h; rfl
  | c :: cs, xs, h => by
    simp only [OutTree.toOutL] at h
    split at h
    · rename_i x ys hx hys
      simp at h; subst h
      rw [List.flatMap_cons, toOut_places c x hx, toOutL_places cs ys hys, OutTree.leafPlacesL]
    · simp at h
end

/-- **The join to the firing model** (`refEmit_leafTargets`). When the output tree `o` has a
firing-model view `o'` (no empty group), the places the reference emitter's edges end in are
exactly the output places of `o'`, in order: an output arc of the transition the firing relation
fires (`OutputArc`) is a place some output-side edge of the diagram ends in, and conversely. -/
theorem refEmit_leafTargets (t : String) (R : List String) (o : OutTree) (o' : Out String)
    (h : o.toOut = some o') :
    (refEmit t R o).edges.filterMap XEdge.placeTarget = outPlaces o' := by
  rw [refEmit_draws, toOut_places o o' h, List.filterMap_map]
  have : (XEdge.placeTarget ∘ refRealize R) = fun d : DrawnEdge => d.dst.place? := by
    funext d
    simp only [Function.comp, XEdge.placeTarget, refRealize]
    split
    next p hd => split <;> simp [NodeRef.place?, hd]
    next => simp [NodeRef.place?]
  rw [this]
  exact drawOut_places t (.trans t) none o 0

/-- `refEmit_leafTargets` read with the glossary's output arc: for a transition `T` of the
firing model whose output spec is the view of `o`, `p` is an output place of `T` exactly when
some edge the reference emitter draws for `o` ends in `p`. -/
theorem refEmit_outputArc (t : String) (R : List String) (o : OutTree) (T : Trans String)
    (hT : T.out = o.toOut) (p : String) :
    (o.toOut).isSome → (OutputArc T p ↔ ∃ e ∈ (refEmit t R o).edges, e.placeTarget = some p) := by
  intro hs
  obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp hs
  have hl := refEmit_leafTargets t R o o' ho'
  constructor
  · rintro ⟨o'', h1, h2⟩
    rw [hT, ho'] at h1; cases h1
    rw [← hl] at h2
    simpa [List.mem_filterMap] using h2
  · rintro ⟨e, he, hp⟩
    refine ⟨o', by rw [hT, ho'], ?_⟩
    rw [← hl]
    exact List.mem_filterMap.mpr ⟨e, he, hp⟩

/-! # The mapper half -/

open Libpetri.Novel.Seam (NTransition NInSpec)
open Libpetri.Novel.TimedScg (Timing)

/-! ## The firing model's view of a transition -/

/-- A right-nested fold is empty exactly when its list is. -/
theorem nestOpt_eq_none (mk : Out String → Out String → Out String) :
    ∀ xs : List (Out String), nestOpt mk xs = none → xs = []
  | [], _ => rfl
  | [_], h => by simp [nestOpt] at h
  | _ :: x2 :: xs, h => by
    simp only [nestOpt, Option.map_eq_none_iff] at h
    exact absurd (nestOpt_eq_none mk (x2 :: xs) h) (List.cons_ne_nil _ _)

/-- The places a right-nested fold names are the places of the list, in order, the empty fold
naming none. -/
theorem nestOpt_places_getD (mk : Out String → Out String → Out String)
    (hmk : ∀ a b, outPlaces (mk a b) = outPlaces a ++ outPlaces b) (xs : List (Out String)) :
    ((nestOpt mk xs).map outPlaces).getD [] = xs.flatMap outPlaces := by
  cases h : nestOpt mk xs with
  | none => simp [nestOpt_eq_none mk xs h]
  | some y => simp [nestOpt_places mk hmk xs y h]

mutual
/-- The places the total view of an output tree names are its leaf places, in order. -/
theorem view_places : ∀ o : OutTree, ((OutTree.view o).map outPlaces).getD [] = OutTree.leafPlaces o
  | .place _ => rfl
  | .forward _ _ => rfl
  | .timeout _ c => by
    have hc := view_places c
    simp only [OutTree.view, OutTree.leafPlaces, Option.map_map]
    exact hc
  | .and cs => by
    simp only [OutTree.view, OutTree.leafPlaces]
    rw [nestOpt_places_getD .and (fun _ _ => rfl)]
    exact viewL_places cs
  | .xor cs => by
    simp only [OutTree.view, OutTree.leafPlaces]
    rw [nestOpt_places_getD .xor (fun _ _ => rfl)]
    exact viewL_places cs
/-- The list form of `view_places`. -/
theorem viewL_places : ∀ cs : List OutTree,
    (OutTree.viewL cs).flatMap outPlaces = OutTree.leafPlacesL cs
  | [] => rfl
  | c :: cs => by
    have hc := view_places c
    simp only [OutTree.viewL, OutTree.leafPlacesL, List.flatMap_append]
    rw [viewL_places cs, ← hc]
    cases OutTree.view c <;> simp
end

mutual
/-- On a tree without an empty group the total view is `toOut`. -/
theorem view_of_toOut : ∀ (o : OutTree) (o' : Out String), o.toOut = some o' → o.view = some o'
  | .place _, _, h => by simpa [OutTree.toOut, OutTree.view] using h
  | .forward _ _, _, h => by simpa [OutTree.toOut, OutTree.view] using h
  | .timeout _ c, _, h => by
    simp only [OutTree.toOut, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    simp [OutTree.view, view_of_toOut c x hx]
  | .and cs, _, h => by
    simp only [OutTree.toOut, Option.bind_eq_some_iff] at h
    obtain ⟨xs, hxs, hy⟩ := h
    simp only [OutTree.view]
    rw [viewL_of_toOutL cs xs hxs]
    exact hy
  | .xor cs, _, h => by
    simp only [OutTree.toOut, Option.bind_eq_some_iff] at h
    obtain ⟨xs, hxs, hy⟩ := h
    simp only [OutTree.view]
    rw [viewL_of_toOutL cs xs hxs]
    exact hy
/-- The list form of `view_of_toOut`. -/
theorem viewL_of_toOutL : ∀ (cs : List OutTree) (xs : List (Out String)),
    OutTree.toOutL cs = some xs → OutTree.viewL cs = xs
  | [], xs, h => by simp [OutTree.toOutL] at h; simp [OutTree.viewL, h]
  | c :: cs, xs, h => by
    simp only [OutTree.toOutL] at h
    split at h
    · rename_i x ys hx hys
      simp at h; subst h
      simp [OutTree.viewL, view_of_toOut c x hx, viewL_of_toOutL cs ys hys]
    · simp at h
end

/-- **`toTrans_core`**: the firing view of a transition has the transition's own arcs, so the
glossary's `InputArc`, `InhibitorArc`, `ReadArc` and `ResetArc` over `t.toTrans` are the arcs the
exporter reads. -/
@[simp] theorem ExportTrans.toTrans_core (t : ExportTrans) : t.toTrans.core = t.core := rfl

/-- On an output spec without an empty group the firing view's output spec is `toOut`'s. -/
theorem ExportTrans.toTrans_out {t : ExportTrans} {o : OutTree} {o' : Out String}
    (ht : t.out = some o) (ho : o.toOut = some o') : t.toTrans.out = some o' := by
  simp [ExportTrans.toTrans, ht, view_of_toOut o o' ho]

/-- **The output-arc join**: `p` is an output place of the firing view of `t` exactly when a
leaf of `t`'s output spec names it. -/
theorem ExportTrans.outputArc_iff (t : ExportTrans) (p : String) :
    OutputArc t.toTrans p ↔ p ∈ t.outLeaves := by
  unfold OutputArc ExportTrans.toTrans ExportTrans.outLeaves
  cases ht : t.out with
  | none => simp
  | some o =>
    have hv := view_places o
    cases hw : o.view with
    | none => rw [hw] at hv; simp at hv; simp [hw, hv]
    | some y => rw [hw] at hv; simp at hv; simp [hw, hv]

/-- The firing view of the net reads the exporter's transitions. -/
@[simp] theorem ExportNet.toNet_transitions (X : ExportNet) :
    X.toNet.transitions = X.trans.map ExportTrans.toTrans := rfl

/-! ## The join to the build model -/

/-- `t` is the export view of the built definition `d`: the same arcs, an output spec whose firing
view is `d`'s, the same timing and priority. -/
def ExportTrans.ViewOf {A : Type} (d : TransDef String A) (t : ExportTrans) : Prop :=
  t.core = d.core ∧ t.out.bind OutTree.view = d.out ∧ t.timing = d.timing ∧ t.prio = d.priority

/-- The firing view of an export view is the firing view of the definition. -/
theorem ExportTrans.toTrans_viewOf {A : Type} {d : TransDef String A} {t : ExportTrans}
    (h : t.ViewOf d) : t.toTrans = d.toTrans := by
  obtain ⟨h1, h2, h3, _⟩ := h
  simp [ExportTrans.toTrans, TransDef.toTrans, h1, h2, h3]

/-- `X` is the export view of the built net `b`: the same places and terminal places, and one
export view per definition, in order (`ExportNet.ofBuilt` of the design, as a relation: the n-ary
tree is not recoverable from the binary `Out`). -/
def ExportNet.ViewOf {A : Type} (b : BuiltNet String A) (X : ExportNet) : Prop :=
  X.places = b.places ∧ List.Forall₂ (fun d t => ExportTrans.ViewOf d t) b.trans X.trans ∧
    X.term = b.terminals

/-- The firing view of an export view of a built net is the built net's firing view. -/
theorem ExportNet.toNet_viewOf {A : Type} {b : BuiltNet String A} {X : ExportNet}
    (h : X.ViewOf b) : X.toNet = b.toNet := by
  obtain ⟨h1, h2, _⟩ := h
  have key : ∀ (ds : List (TransDef String A)) (ts : List ExportTrans),
      List.Forall₂ (fun d t => ExportTrans.ViewOf d t) ds ts →
        ts.map ExportTrans.toTrans = ds.map TransDef.toTrans := by
    intro ds ts h
    induction h with
    | nil => rfl
    | cons hd _ ih => simp [ExportTrans.toTrans_viewOf hd, ih]
  simp [ExportNet.toNet, BuiltNet.toNet, h1, key _ _ h2]

/-! ## Labels -/

/-- **The reference transition labeller** (witness model, [EXP-007], ruling D41): the name; then,
when intervals are shown, ` [e, l]ms` with `l` written `∞` without a deadline (`Immediate` shows
`[0, ∞]ms`); then, when priority is shown and is not 0, ` prio=n`. It is `transition_label` of
the Rust mapper and `transitionLabel` of the Java and TypeScript mappers. -/
def refTransLabel : TransLabeller := fun cfg name tm prio =>
  name ++
    (if cfg.showIntervals then
      " [" ++ toString tm.earliest ++ ", " ++
        (if tm.hasDeadline then toString tm.latest else "∞") ++ "]ms"
    else "") ++
    (if cfg.showPriority && prio != 0 then " prio=" ++ toString prio else "")

#spec_witness refTransLabel

/-- The reference label starts with the name ([EXP-003]). -/
theorem refTransLabel_prefix (cfg : ExportCfg) (n : String) (tm : Timing) (p : Int) :
    n.toList <+: (refTransLabel cfg n tm p).toList := by
  simp only [refTransLabel, String.toList_append, List.append_assoc]
  exact List.prefix_append _ _

/-- With intervals and priority hidden, the reference label is the name. -/
theorem refTransLabel_hidden (cfg : ExportCfg) (n : String) (tm : Timing) (p : Int)
    (hi : cfg.showIntervals = false) (hp : cfg.showPriority = false) :
    refTransLabel cfg n tm p = n := by
  simp [refTransLabel, hi, hp]

/-- The label of an input edge: the cardinality label (`refCardLabel`, [EXP-006]), prefixed with
`⟨n⟩` when the place is correlated ([EXP-018]). -/
def refInputLabel (t : ExportTrans) (s : NInSpec String) : Option String :=
  if s.place ∈ t.corr then some (corrLabel (refCardLabel s.card)) else refCardLabel s.card

/-! ## The edges of one transition -/

/-- The input edge of arc `s` of `t`: place to transition, row `matchInput` when the place is
correlated, else `input`. -/
def refInputEdge (t : ExportTrans) (s : NInSpec String) : XEdge :=
  ⟨.place s.place, .trans t.name, .input, if s.place ∈ t.corr then .matchInput else .input, false,
    refInputLabel t s, none, none⟩

/-- The inhibitor edge on `p`: place to transition, no label. -/
def refInhibitorEdge (t : ExportTrans) (p : String) : XEdge :=
  ⟨.place p, .trans t.name, .inhibitor, .inhibitor, false, none, none, none⟩

/-- The read edge on `p`: place to transition, labelled `read`. -/
def refReadEdge (t : ExportTrans) (p : String) : XEdge :=
  ⟨.place p, .trans t.name, .read, .read, false, some "read", none, none⟩

/-- The standalone reset edge on `p`: transition to place (the drawing convention of all three
mappers), labelled `reset`. -/
def refResetEdge (t : ExportTrans) (p : String) : XEdge :=
  ⟨.trans t.name, .place p, .reset, .reset, false, some "reset", none, none⟩

/-- The reset places of `t` that get a standalone reset edge: those no output leaf names (the
others are drawn by the combined edge of [EXP-013]), in the order of the reset arcs. -/
def refStandaloneResets (t : ExportTrans) : List String :=
  t.core.resets.filter fun p => decide (p ∉ t.outLeaves)

/-- **The edges of one transition**, in the order the three mappers draw them: one input edge per
input arc, the output side (`refEmit`), one inhibitor edge per inhibitor arc, one read edge per
read arc, one standalone reset edge per reset arc whose place no output leaf names. -/
def refTransEdges (t : ExportTrans) : List XEdge :=
  t.core.inputs.map (refInputEdge t) ++ (refEmit.ofTrans t).edges ++
    t.core.inhibitors.map (refInhibitorEdge t) ++ t.core.reads.map (refReadEdge t) ++
    (refStandaloneResets t).map (refResetEdge t)

/-! ## Nodes -/

/-- The places that get a node: every declared place and every place an arc touches, without
repetition (the Rust shape, the end state of ruling D60; Java and TypeScript draw only the
touched ones). -/
def refPlaceNames (X : ExportNet) : List String := (X.places ++ X.trans.flatMap ExportTrans.touched).dedup

/-- The node of place `p`: ID `p_<sanitize p>`, the category `refPlaceCategory` gives it, no
label, the raw name as external label. -/
def refPlaceNode (cfg : ExportCfg) (X : ExportNet) (p : String) : XNode :=
  ⟨.place p, nodeId (.place p), refPlaceCategory X.toNet cfg.isEnv X.isTerm p, "", some p⟩

/-- The node of transition `t`: ID `t_<sanitize t>`, the transition category, the label
`refTransLabel`. -/
def refTransNode (cfg : ExportCfg) (t : ExportTrans) : XNode :=
  ⟨.trans t.name, nodeId (.trans t.name), .transition, refTransLabel cfg t.name t.timing t.prio,
    none⟩

/-- The node of junction `j` of transition `t`: its junction ID, the junction category of its
kind, the kind's glyph. -/
def refJunctionNode (t : String) (j : JKind × Nat) : XNode :=
  ⟨.junction t j.1 j.2, nodeId (.junction t j.1 j.2), j.1.cat, j.1.glyph, none⟩

/-- The junction nodes of `t`, in pre-order. -/
def refJunctionNodes (t : ExportTrans) : List XNode :=
  (refEmit.ofTrans t).junctions.map (refJunctionNode t.name)

/-- **The nodes**: place nodes, then transition nodes in declaration order, then the junction
nodes of each transition. -/
def refNodes (cfg : ExportCfg) (X : ExportNet) : List XNode :=
  (refPlaceNames X).map (refPlaceNode cfg X) ++ X.trans.map (refTransNode cfg) ++
    X.trans.flatMap refJunctionNodes

/-- What the nodes stand for; it does not depend on the configuration (`refNodes_refs`). -/
def refNodeRefs (X : ExportNet) : List NodeRef :=
  (refPlaceNames X).map NodeRef.place ++ X.trans.map (fun t => NodeRef.trans t.name) ++
    X.trans.flatMap fun t => (refEmit.ofTrans t).junctions.map fun j => .junction t.name j.1 j.2

/-- **The edges**: the edges of each transition, in declaration order. -/
def refEdges (X : ExportNet) : List XEdge := X.trans.flatMap refTransEdges

/-! ## The exporter -/

/-- **A cluster stage**: what clustering adds to a drawn graph, from the cluster source, the net,
the node references and the edges. It adds clusters and ghost edges and nothing else: every edge
it adds is a ghost edge between two drawn nodes. `Reference/ExportCluster.lean` defines the
stage of the runtimes ([EXP-016], [EXP-017]). -/
structure ClusterStage where
  /-- The clusters. -/
  clusters : ClusterSource → ExportNet → List NodeRef → List XEdge → List XCluster
  /-- The ghost edges. -/
  ghosts : ClusterSource → ExportNet → List NodeRef → List XEdge → List XEdge
  /-- Every added edge is a ghost edge. -/
  ghosts_arc : ∀ src X rs es, ∀ e ∈ ghosts src X rs es, e.arc = .ghost
  /-- Every added edge joins two drawn nodes. -/
  ghosts_ends : ∀ src X rs es, ∀ e ∈ ghosts src X rs es, e.src ∈ rs ∧ e.dst ∈ rs

/-- The stage that adds nothing: the runtimes' cluster source `none`. -/
def ClusterStage.flat : ClusterStage :=
  ⟨fun _ _ _ _ => [], fun _ _ _ _ => [], by simp, by simp⟩

/-- **The reference exporter, parametric in its cluster stage** (witness model): the configured
direction, `compound` set ([EXP-017] AC1, unconditionally), the nodes `refNodes`, the edges
`refEdges` followed by the stage's ghost edges, and the stage's clusters. -/
def refExportWith (S : ClusterStage) : Exporter := fun cfg X =>
  { dir := cfg.dir, compound := true, nodes := refNodes cfg X,
    edges := refEdges X ++ S.ghosts cfg.cluster X (refNodeRefs X) (refEdges X),
    clusters := S.clusters cfg.cluster X (refNodeRefs X) (refEdges X) }

#spec_witness refExportWith

/-- **The reference exporter without clustering** (witness model): `refExportWith` with the
stage that adds nothing. -/
def refExportFlat : Exporter := refExportWith .flat

#spec_witness refExportFlat

/-! ## Lemmas: the output side -/

/-- The reference realises an edge of the drawing rule with the same source. -/
@[simp] theorem refRealize_src (R : List String) (d : DrawnEdge) : (refRealize R d).src = d.src := by
  unfold refRealize
  split
  · split <;> rfl
  · rfl

/-- The reference realises an edge of the drawing rule with the same target. -/
@[simp] theorem refRealize_dst (R : List String) (d : DrawnEdge) : (refRealize R d).dst = d.dst := by
  unfold refRealize
  split
  next p h => split <;> simp [h]
  next => rfl

mutual
/-- **Where the edges of the drawing rule start and end**: at the parent or at a junction of the
subtree, and at a place or at a junction of the subtree; the junctions are the subtree's, numbered
from `n` in pre-order. -/
theorem drawOut_ends (t : String) (par : NodeRef) (l : Option String) :
    ∀ (o : OutTree) (n : Nat), ∀ d ∈ drawOut t par l n o,
      (d.src = par ∨ ∃ k i, d.src = .junction t k i ∧ (k, i) ∈ (OutTree.junctions o).zipIdx n) ∧
      ((∃ p, d.dst = .place p) ∨
        ∃ k i, d.dst = .junction t k i ∧ (k, i) ∈ (OutTree.junctions o).zipIdx n)
  | .place p, n, d, hd => by
    simp only [drawOut, List.mem_singleton] at hd; subst hd; simp
  | .forward s q, n, d, hd => by
    simp only [drawOut, List.mem_singleton] at hd; subst hd; simp
  | .timeout ms c, n, d, hd => by
    simp only [drawOut] at hd
    simpa only [OutTree.junctions] using drawOut_ends t par _ c n d hd
  | .and cs, n, d, hd => by
    by_cases h : 2 ≤ cs.length
    · simp only [drawOut, h, if_true, List.mem_cons] at hd
      simp only [OutTree.junctions, h, if_true, List.singleton_append, List.zipIdx_cons,
        List.mem_cons]
      rcases hd with rfl | hd
      · exact ⟨Or.inl rfl, Or.inr ⟨.and, n, rfl, Or.inl rfl⟩⟩
      · obtain ⟨hs, ht⟩ := drawOutL_ends t (.junction t .and n) (.junction .and) cs (n + 1) d hd
        refine ⟨?_, ?_⟩
        · rcases hs with hs | ⟨k, i, hs, hm⟩
          · exact Or.inr ⟨.and, n, hs, Or.inl rfl⟩
          · exact Or.inr ⟨k, i, hs, Or.inr hm⟩
        · rcases ht with ht | ⟨k, i, ht, hm⟩
          · exact Or.inl ht
          · exact Or.inr ⟨k, i, ht, Or.inr hm⟩
    · simp only [drawOut, h, if_false] at hd
      simpa only [OutTree.junctions, h, if_false, List.nil_append]
        using drawOutL_ends t par (.pass l) cs n d hd
  | .xor cs, n, d, hd => by
    by_cases h : 2 ≤ cs.length
    · simp only [drawOut, h, if_true, List.mem_cons] at hd
      simp only [OutTree.junctions, h, if_true, List.singleton_append, List.zipIdx_cons,
        List.mem_cons]
      rcases hd with rfl | hd
      · exact ⟨Or.inl rfl, Or.inr ⟨.xor, n, rfl, Or.inl rfl⟩⟩
      · obtain ⟨hs, ht⟩ := drawOutL_ends t (.junction t .xor n) (.junction .xor) cs (n + 1) d hd
        refine ⟨?_, ?_⟩
        · rcases hs with hs | ⟨k, i, hs, hm⟩
          · exact Or.inr ⟨.xor, n, hs, Or.inl rfl⟩
          · exact Or.inr ⟨k, i, hs, Or.inr hm⟩
        · rcases ht with ht | ⟨k, i, ht, hm⟩
          · exact Or.inl ht
          · exact Or.inr ⟨k, i, ht, Or.inr hm⟩
    · simp only [drawOut, h, if_false] at hd
      simpa only [OutTree.junctions, h, if_false, List.nil_append]
        using drawOutL_ends t par (.pass l) cs n d hd
/-- The list form of `drawOut_ends`. -/
theorem drawOutL_ends (t : String) (par : NodeRef) (u : Under) :
    ∀ (cs : List OutTree) (n : Nat), ∀ d ∈ drawOutL t par u n cs,
      (d.src = par ∨ ∃ k i, d.src = .junction t k i ∧ (k, i) ∈ (OutTree.junctionsL cs).zipIdx n) ∧
      ((∃ p, d.dst = .place p) ∨
        ∃ k i, d.dst = .junction t k i ∧ (k, i) ∈ (OutTree.junctionsL cs).zipIdx n)
  | [], n, d, hd => by simp [drawOutL] at hd
  | c :: cs, n, d, hd => by
    simp only [drawOutL, List.mem_append] at hd
    simp only [OutTree.junctionsL, List.zipIdx_append, List.mem_append]
    rcases hd with hd | hd
    · obtain ⟨hs, ht⟩ := drawOut_ends t par (u.label c) c n d hd
      refine ⟨?_, ?_⟩
      · rcases hs with hs | ⟨k, i, hs, hm⟩
        · exact Or.inl hs
        · exact Or.inr ⟨k, i, hs, Or.inl hm⟩
      · rcases ht with ht | ⟨k, i, ht, hm⟩
        · exact Or.inl ht
        · exact Or.inr ⟨k, i, ht, Or.inl hm⟩
    · obtain ⟨hs, ht⟩ := drawOutL_ends t par u cs _ d hd
      refine ⟨?_, ?_⟩
      · rcases hs with hs | ⟨k, i, hs, hm⟩
        · exact Or.inl hs
        · exact Or.inr ⟨k, i, hs, Or.inr hm⟩
      · rcases ht with ht | ⟨k, i, ht, hm⟩
        · exact Or.inl ht
        · exact Or.inr ⟨k, i, ht, Or.inr hm⟩
end

/-- The junctions the reference emitter draws are the junctions of the tree in pre-order,
numbered from 0. -/
theorem refEmit_junctions (t : String) (R : List String) (o : OutTree) :
    (refEmit t R o).junctions = (OutTree.junctions o).zipIdx := by
  rw [refEmit_draws]

/-- **Wiring of the reference emitter**: every edge starts at the transition or at one of the
junctions it draws, and ends at a place or at one of the junctions it draws ([EXP-014]'s wiring
half). -/
theorem refEmit_ends {t : String} {R : List String} {o : OutTree} {e : XEdge}
    (he : e ∈ (refEmit t R o).edges) :
    (e.src = .trans t ∨ ∃ k i, e.src = .junction t k i ∧ (k, i) ∈ (refEmit t R o).junctions) ∧
      ((∃ p, e.dst = .place p) ∨
        ∃ k i, e.dst = .junction t k i ∧ (k, i) ∈ (refEmit t R o).junctions) := by
  rw [refEmit_junctions]
  rw [refEmit_draws] at he
  simp only [List.mem_map] at he
  obtain ⟨d, hd, rfl⟩ := he
  rw [refRealize_src, refRealize_dst]
  exact drawOut_ends t (.trans t) none o 0 d hd

/-- Every edge of the reference emitter starts at a node of transition `t`. -/
theorem refEmit_owner {t : String} {R : List String} {o : OutTree} {e : XEdge}
    (he : e ∈ (refEmit t R o).edges) : e.src.owner? = some t := by
  rcases (refEmit_ends he).1 with h | ⟨k, i, h, _⟩ <;> simp [h, NodeRef.owner?]

/-- **The arc types of the reference emitter's edges** ([EXP-013]): each is an `output` edge in
the `output` row, or the combined `resetOutput` edge in its own row, solid, labelled
`reset+out`; it is the combined edge exactly when it ends in a reset place; and no edge is
clipped at a cluster. -/
theorem refEmit_arc {t : String} {R : List String} {o : OutTree} {e : XEdge}
    (he : e ∈ (refEmit t R o).edges) :
    ((e.arc = .output ∧ e.row = .output) ∨
      (e.arc = .resetOutput ∧ e.row = .resetOutput ∧ e.dashed = false ∧
        e.label = some "reset+out")) ∧
    (e.arc = .resetOutput ↔ ∃ p ∈ R, e.dst = .place p) ∧
    e.ltail = none ∧ e.lhead = none := by
  rw [refEmit_draws] at he
  simp only [List.mem_map] at he
  obtain ⟨d, _, rfl⟩ := he
  unfold refRealize
  split
  next p h =>
    by_cases hp : p ∈ R
    · simp [hp]
    · simp [hp]
  next j h =>
    refine ⟨Or.inl ⟨rfl, rfl⟩, ?_, rfl, rfl⟩
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro p _ hj
    exact h p hj

/-- **The places the reference emitter draws into** are the leaf places of the tree, in order,
whatever the tree (the generalisation of `refEmit_leafTargets` to trees with empty groups). -/
theorem refEmit_places (t : String) (R : List String) (o : OutTree) :
    (refEmit t R o).edges.filterMap XEdge.placeTarget = OutTree.leafPlaces o := by
  rw [refEmit_draws, List.filterMap_map]
  have : (XEdge.placeTarget ∘ refRealize R) = fun d : DrawnEdge => d.dst.place? := by
    funext d
    simp [XEdge.placeTarget]
  rw [this]
  exact drawOut_places t (.trans t) none o 0

/-! ## Lemmas: one transition -/

/-- An emitter on a transition without an output spec draws nothing. -/
theorem Emitter.ofTrans_none (Em : Emitter) {t : ExportTrans} (h : t.out = none) :
    Em.ofTrans t = {} := by
  simp [Emitter.ofTrans, h]

/-- An emitter on a transition with output spec `o` draws what it draws for `o`. -/
theorem Emitter.ofTrans_some (Em : Emitter) {t : ExportTrans} {o : OutTree} (h : t.out = some o) :
    Em.ofTrans t = Em t.name t.core.resets o := by
  simp [Emitter.ofTrans, h]

/-- An edge the emitter draws for a transition is one it draws for the transition's output
spec. -/
theorem Emitter.mem_ofTrans_edges (Em : Emitter) {t : ExportTrans} {e : XEdge}
    (he : e ∈ (Em.ofTrans t).edges) :
    ∃ o, t.out = some o ∧ e ∈ (Em t.name t.core.resets o).edges := by
  unfold Emitter.ofTrans at he
  split at he
  next o h => exact ⟨o, h, he⟩
  next => simp at he

/-- The reference's output side of `t` ends in exactly the leaf places of its output spec, in
order. -/
theorem refEmit_ofTrans_places (t : ExportTrans) :
    (refEmit.ofTrans t).edges.filterMap XEdge.placeTarget = t.outLeaves := by
  unfold Emitter.ofTrans ExportTrans.outLeaves
  cases t.out <;> simp [refEmit_places]

/-- The reference's junctions of `t` are those of its output spec in pre-order, numbered from 0. -/
theorem refEmit_ofTrans_junctions (t : ExportTrans) :
    (refEmit.ofTrans t).junctions = ((t.out.map OutTree.junctions).getD []).zipIdx := by
  unfold Emitter.ofTrans
  cases t.out <;> simp [refEmit_junctions]

/-- `refEmit_ends` for the output side of a transition. -/
theorem refEmit_ofTrans_ends {t : ExportTrans} {e : XEdge} (he : e ∈ (refEmit.ofTrans t).edges) :
    (e.src = .trans t.name ∨
        ∃ k i, e.src = .junction t.name k i ∧ (k, i) ∈ (refEmit.ofTrans t).junctions) ∧
      ((∃ p, e.dst = .place p) ∨
        ∃ k i, e.dst = .junction t.name k i ∧ (k, i) ∈ (refEmit.ofTrans t).junctions) := by
  obtain ⟨o, ho, he⟩ := Emitter.mem_ofTrans_edges refEmit he
  rw [Emitter.ofTrans_some refEmit ho]
  exact refEmit_ends he

/-- `refEmit_arc` for the output side of a transition. -/
theorem refEmit_ofTrans_arc {t : ExportTrans} {e : XEdge} (he : e ∈ (refEmit.ofTrans t).edges) :
    ((e.arc = .output ∧ e.row = .output) ∨
      (e.arc = .resetOutput ∧ e.row = .resetOutput ∧ e.dashed = false ∧
        e.label = some "reset+out")) ∧
    (e.arc = .resetOutput ↔ ∃ p ∈ t.core.resets, e.dst = .place p) ∧
    e.ltail = none ∧ e.lhead = none := by
  obtain ⟨o, _, he⟩ := Emitter.mem_ofTrans_edges refEmit he
  exact refEmit_arc he

/-- `refEmit_owner` for the output side of a transition. -/
theorem refEmit_ofTrans_owner {t : ExportTrans} {e : XEdge} (he : e ∈ (refEmit.ofTrans t).edges) :
    e.src.owner? = some t.name := by
  obtain ⟨o, _, he⟩ := Emitter.mem_ofTrans_edges refEmit he
  exact refEmit_owner he

/-- **The edges of one transition, by kind.** -/
theorem mem_refTransEdges {t : ExportTrans} {e : XEdge} :
    e ∈ refTransEdges t ↔
      (∃ s ∈ t.core.inputs, e = refInputEdge t s) ∨ e ∈ (refEmit.ofTrans t).edges ∨
      (∃ p ∈ t.core.inhibitors, e = refInhibitorEdge t p) ∨
      (∃ p ∈ t.core.reads, e = refReadEdge t p) ∨
      (∃ p ∈ t.core.resets, p ∉ t.outLeaves ∧ e = refResetEdge t p) := by
  simp only [refTransEdges, refStandaloneResets, List.mem_append, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ((((⟨s, hs, rfl⟩ | h) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) | ⟨p, ⟨hp, hn⟩, rfl⟩)
    · exact Or.inl ⟨s, hs, rfl⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hn, rfl⟩)))
  · rintro (⟨s, hs, rfl⟩ | h | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, hn, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨s, hs, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr ⟨p, hp, rfl⟩))
    · exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
    · exact Or.inr ⟨p, ⟨hp, hn⟩, rfl⟩

/-- An input edge of a transition is the edge of one of its input arcs. -/
theorem refTransEdges_input {t : ExportTrans} {e : XEdge} (he : e ∈ refTransEdges t)
    (ha : e.arc = .input) : ∃ s ∈ t.core.inputs, e = refInputEdge t s := by
  rcases mem_refTransEdges.mp he with h | h | ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ | ⟨p, _, _, rfl⟩
  · exact h
  · rcases (refEmit_ofTrans_arc h).1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at ha <;> cases ha
  all_goals cases ha

/-- An inhibitor edge of a transition is the edge of one of its inhibitor arcs. -/
theorem refTransEdges_inhibitor {t : ExportTrans} {e : XEdge} (he : e ∈ refTransEdges t)
    (ha : e.arc = .inhibitor) : ∃ p ∈ t.core.inhibitors, e = refInhibitorEdge t p := by
  rcases mem_refTransEdges.mp he with ⟨s, _, rfl⟩ | h | h | ⟨p, _, rfl⟩ | ⟨p, _, _, rfl⟩
  · cases ha
  · rcases (refEmit_ofTrans_arc h).1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at ha <;> cases ha
  · exact h
  all_goals cases ha

/-- A read edge of a transition is the edge of one of its read arcs. -/
theorem refTransEdges_read {t : ExportTrans} {e : XEdge} (he : e ∈ refTransEdges t)
    (ha : e.arc = .read) : ∃ p ∈ t.core.reads, e = refReadEdge t p := by
  rcases mem_refTransEdges.mp he with ⟨s, _, rfl⟩ | h | ⟨p, _, rfl⟩ | h | ⟨p, _, _, rfl⟩
  · cases ha
  · rcases (refEmit_ofTrans_arc h).1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at ha <;> cases ha
  · cases ha
  · exact h
  · cases ha

/-- A standalone reset edge of a transition is the edge of one of its reset arcs on a place no
output leaf names. -/
theorem refTransEdges_reset {t : ExportTrans} {e : XEdge} (he : e ∈ refTransEdges t)
    (ha : e.arc = .reset) : ∃ p ∈ t.core.resets, p ∉ t.outLeaves ∧ e = refResetEdge t p := by
  rcases mem_refTransEdges.mp he with ⟨s, _, rfl⟩ | h | ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ | h
  · cases ha
  · rcases (refEmit_ofTrans_arc h).1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at ha <;> cases ha
  · cases ha
  · cases ha
  · exact h

/-- An `output` or `resetOutput` edge of a transition is one of its output side. -/
theorem refTransEdges_out {t : ExportTrans} {e : XEdge} (he : e ∈ refTransEdges t)
    (ha : e.arc = .output ∨ e.arc = .resetOutput) : e ∈ (refEmit.ofTrans t).edges := by
  rcases mem_refTransEdges.mp he with ⟨s, _, rfl⟩ | h | ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ | ⟨p, _, _, rfl⟩
  · rcases ha with ha | ha <;> cases ha
  · exact h
  all_goals (rcases ha with ha | ha <;> cases ha)

/-- No edge of a transition is a ghost edge. -/
theorem refTransEdges_ne_ghost {t : ExportTrans} {e : XEdge} (he : e ∈ refTransEdges t) :
    e.arc ≠ .ghost := by
  intro ha
  rcases mem_refTransEdges.mp he with ⟨s, _, rfl⟩ | h | ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ | ⟨p, _, _, rfl⟩
  · cases ha
  · rcases (refEmit_ofTrans_arc h).1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at ha <;> cases ha
  all_goals cases ha

/-- Every edge of a transition starts or ends at the transition's node or one of its junctions. -/
theorem refTransEdges_owner {t : ExportTrans} {e : XEdge} (he : e ∈ refTransEdges t) :
    e.src.owner? = some t.name ∨ e.dst = .trans t.name := by
  rcases mem_refTransEdges.mp he with ⟨s, _, rfl⟩ | h | ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ | ⟨p, _, _, rfl⟩
  · exact Or.inr rfl
  · exact Or.inl (refEmit_ofTrans_owner h)
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Which end of an edge of a transition is the transition's: an edge from the transition or one
of its junctions ends at a place or at one of its junctions; an edge into the transition comes
from a place. -/
theorem refTransEdges_ends_owner {t : ExportTrans} {e : XEdge} (he : e ∈ refTransEdges t) :
    (e.src.owner? = some t.name ∧ (e.dst.owner? = none ∨ e.dst.owner? = some t.name)) ∨
      (e.src.owner? = none ∧ e.dst = .trans t.name) := by
  rcases mem_refTransEdges.mp he with ⟨s, _, rfl⟩ | h | ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ | ⟨p, _, _, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · refine Or.inl ⟨refEmit_ofTrans_owner h, ?_⟩
    rcases (refEmit_ofTrans_ends h).2 with ⟨p, hp⟩ | ⟨k, i, hj, _⟩
    · exact Or.inl (by simp [hp, NodeRef.owner?])
    · exact Or.inr (by simp [hj, NodeRef.owner?])
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, Or.inl rfl⟩

/-- No edge of a transition is clipped at a cluster. -/
theorem refTransEdges_noClip {t : ExportTrans} {e : XEdge} (he : e ∈ refTransEdges t) :
    e.ltail = none ∧ e.lhead = none := by
  rcases mem_refTransEdges.mp he with ⟨s, _, rfl⟩ | h | ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ | ⟨p, _, _, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact (refEmit_ofTrans_arc h).2.2
  all_goals exact ⟨rfl, rfl⟩

/-- The output side of a transition, read off its edges: the emitter's edges for the transition
of that name, none for another name. -/
theorem refTransEdges_filter_outSide (t : ExportTrans) (n : String) :
    (refTransEdges t).filter (XEdge.outSideOf n) =
      if t.name = n then (refEmit.ofTrans t).edges else [] := by
  have hin : ∀ s, XEdge.outSideOf n (refInputEdge t s) = false := fun _ => rfl
  have hinh : ∀ p, XEdge.outSideOf n (refInhibitorEdge t p) = false := fun _ => rfl
  have hrd : ∀ p, XEdge.outSideOf n (refReadEdge t p) = false := fun _ => rfl
  have hrs : ∀ p, XEdge.outSideOf n (refResetEdge t p) = false := fun _ => by
    simp [XEdge.outSideOf, refResetEdge]
  have hout : ∀ e ∈ (refEmit.ofTrans t).edges, XEdge.outSideOf n e = (t.name == n) := by
    intro e he
    have h1 := refEmit_ofTrans_owner he
    rcases (refEmit_ofTrans_arc he).1 with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
      simp [XEdge.outSideOf, h1, ha]
  simp only [refTransEdges, List.filter_append, List.filter_map]
  have e1 : (t.core.inputs.filter (XEdge.outSideOf n ∘ refInputEdge t)) = [] := by
    simp [List.filter_eq_nil_iff, hin]
  have e2 : (t.core.inhibitors.filter (XEdge.outSideOf n ∘ refInhibitorEdge t)) = [] := by
    simp [List.filter_eq_nil_iff, hinh]
  have e3 : (t.core.reads.filter (XEdge.outSideOf n ∘ refReadEdge t)) = [] := by
    simp [List.filter_eq_nil_iff, hrd]
  have e4 : ((refStandaloneResets t).filter (XEdge.outSideOf n ∘ refResetEdge t)) = [] := by
    simp [List.filter_eq_nil_iff, hrs]
  rw [e1, e2, e3, e4]
  by_cases hn : t.name = n
  · simp only [hn, if_true, List.map_nil, List.nil_append, List.append_nil]
    rw [List.filter_eq_self]
    intro e he; rw [hout e he]; simp [hn]
  · simp only [hn, if_false, List.map_nil, List.nil_append, List.append_nil]
    rw [List.filter_eq_nil_iff]
    intro e he; rw [hout e he]; simp [hn]

/-! ## Lemmas: the whole graph -/

section Graph

variable {S : ClusterStage} {cfg : ExportCfg} {X : ExportNet}

@[simp] theorem refExportWith_dir : (refExportWith S cfg X).dir = cfg.dir := rfl

@[simp] theorem refExportWith_compound : (refExportWith S cfg X).compound = true := rfl

@[simp] theorem refExportWith_nodes : (refExportWith S cfg X).nodes = refNodes cfg X := rfl

theorem refExportWith_edges :
    (refExportWith S cfg X).edges =
      refEdges X ++ S.ghosts cfg.cluster X (refNodeRefs X) (refEdges X) := rfl

theorem refExportWith_clusters :
    (refExportWith S cfg X).clusters = S.clusters cfg.cluster X (refNodeRefs X) (refEdges X) := rfl

/-- The edges of the transitions. -/
theorem mem_refEdges {e : XEdge} : e ∈ refEdges X ↔ ∃ t ∈ X.trans, e ∈ refTransEdges t :=
  List.mem_flatMap

/-- **Every edge of the exporter** is an edge of one transition, or a ghost edge the stage added
between two drawn nodes. -/
theorem refExportWith_edge {e : XEdge} (he : e ∈ (refExportWith S cfg X).edges) :
    (∃ t ∈ X.trans, e ∈ refTransEdges t) ∨
      (e.arc = .ghost ∧ e.src ∈ refNodeRefs X ∧ e.dst ∈ refNodeRefs X) := by
  rw [refExportWith_edges, List.mem_append] at he
  rcases he with he | he
  · exact Or.inl (mem_refEdges.mp he)
  · exact Or.inr ⟨S.ghosts_arc _ _ _ _ e he, S.ghosts_ends _ _ _ _ e he⟩

/-- Every edge of the exporter that is not a ghost edge is an edge of one transition. -/
theorem refExportWith_edge_of_ne_ghost {e : XEdge} (he : e ∈ (refExportWith S cfg X).edges)
    (hg : e.arc ≠ .ghost) : ∃ t ∈ X.trans, e ∈ refTransEdges t := by
  rcases refExportWith_edge he with h | ⟨h, _⟩
  · exact h
  · exact absurd h hg

/-- Every edge of every transition is an edge of the exporter. -/
theorem refExportWith_edge_of_trans {t : ExportTrans} (ht : t ∈ X.trans) {e : XEdge}
    (he : e ∈ refTransEdges t) : e ∈ (refExportWith S cfg X).edges := by
  rw [refExportWith_edges]
  exact List.mem_append_left _ (mem_refEdges.mpr ⟨t, ht, he⟩)

/-- **Clustering adds only ghost edges**: the non-ghost edges of the exporter are `refEdges`, in
order, whatever the stage. -/
theorem refExportWith_nonGhost :
    (refExportWith S cfg X).edges.filter (fun e => e.arc != .ghost) = refEdges X := by
  rw [refExportWith_edges, List.filter_append]
  have h1 : (refEdges X).filter (fun e => e.arc != .ghost) = refEdges X := by
    rw [List.filter_eq_self]
    intro e he
    obtain ⟨t, _, he⟩ := mem_refEdges.mp he
    simpa using refTransEdges_ne_ghost he
  have h2 : (S.ghosts cfg.cluster X (refNodeRefs X) (refEdges X)).filter
      (fun e => e.arc != .ghost) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    simp [S.ghosts_arc _ _ _ _ e he]
  rw [h1, h2, List.append_nil]

/-- The nodes' references do not depend on the configuration. -/
theorem refNodes_refs : (refNodes cfg X).map XNode.ref = refNodeRefs X := by
  simp [refNodes, refNodeRefs, List.map_flatMap, refPlaceNode, refTransNode, refJunctionNodes,
    refJunctionNode, Function.comp_def]

/-- **The nodes of the exporter, by kind.** -/
theorem mem_refNodes {n : XNode} :
    n ∈ refNodes cfg X ↔
      (∃ p ∈ refPlaceNames X, n = refPlaceNode cfg X p) ∨ (∃ t ∈ X.trans, n = refTransNode cfg t) ∨
      (∃ t ∈ X.trans, ∃ j ∈ (refEmit.ofTrans t).junctions, n = refJunctionNode t.name j) := by
  simp only [refNodes, refJunctionNodes, List.mem_append, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ((⟨p, hp, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, j, hj, rfl⟩)
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr (Or.inl ⟨t, ht, rfl⟩)
    · exact Or.inr (Or.inr ⟨t, ht, j, hj, rfl⟩)
  · rintro (⟨p, hp, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, j, hj, rfl⟩)
    · exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
    · exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
    · exact Or.inr ⟨t, ht, j, hj, rfl⟩

/-- **Every node's DOT ID is the node ID of what it stands for** ([EXP-014]). -/
theorem refNodes_id {n : XNode} (h : n ∈ refNodes cfg X) : n.id = nodeId n.ref := by
  rcases mem_refNodes.mp h with ⟨p, _, rfl⟩ | ⟨t, _, rfl⟩ | ⟨t, _, j, _, rfl⟩ <;> rfl

/-- The places that get a node: the declared places and the places some arc touches. -/
theorem mem_refPlaceNames {p : String} : p ∈ refPlaceNames X ↔ p ∈ X.places ∨ X.Touched p := by
  simp [refPlaceNames, ExportNet.Touched, List.mem_flatMap]

/-- Each place gets one node. -/
theorem refPlaceNames_nodup : (refPlaceNames X).Nodup := List.nodup_dedup _

/-- `ExportTrans.touched`, read with the glossary's arc predicates over the firing view. -/
theorem ExportTrans.mem_touched (t : ExportTrans) (p : String) :
    p ∈ t.touched ↔ p ∈ inPlaces t.toTrans ∨ OutputArc t.toTrans p ∨ InhibitorArc t.toTrans p ∨
      ReadArc t.toTrans p ∨ ResetArc t.toTrans p := by
  rw [ExportTrans.outputArc_iff]
  simp [ExportTrans.touched, inPlaces, ExportTrans.toTrans]

/-- A place node stands for one of the places that get a node; a node of transition `n` for a
transition of that name; a junction node for a junction the emitter draws for a transition of
that name. -/
theorem refNodes_ref_cases {n : XNode} (h : n ∈ refNodes cfg X) :
    (∀ p, n.ref = .place p → p ∈ refPlaceNames X ∧ n = refPlaceNode cfg X p) ∧
    (∀ tn, n.ref = .trans tn → ∃ t ∈ X.trans, t.name = tn ∧ n = refTransNode cfg t) ∧
    (∀ tn k i, n.ref = .junction tn k i → ∃ t ∈ X.trans, t.name = tn ∧
      (k, i) ∈ (refEmit.ofTrans t).junctions ∧ n = refJunctionNode t.name (k, i)) := by
  rcases mem_refNodes.mp h with ⟨p, hp, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, j, hj, rfl⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro q hq; simp [refPlaceNode] at hq; subst hq; exact ⟨hp, rfl⟩
    · intro tn hq; simp [refPlaceNode] at hq
    · intro tn k i hq; simp [refPlaceNode] at hq
  · refine ⟨?_, ?_, ?_⟩
    · intro q hq; simp [refTransNode] at hq
    · intro tn hq; simp [refTransNode] at hq; exact ⟨t, ht, hq, rfl⟩
    · intro tn k i hq; simp [refTransNode] at hq
  · refine ⟨?_, ?_, ?_⟩
    · intro q hq; simp [refJunctionNode] at hq
    · intro tn hq; simp [refJunctionNode] at hq
    · intro tn k i hq
      obtain ⟨k', i'⟩ := j
      simp [refJunctionNode] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      exact ⟨t, ht, rfl, hj, rfl⟩

/-- In a list of transitions with distinct names, the transition of a name is unique. -/
theorem ExportNet.eq_of_name {X : ExportNet} (hX : (X.trans.map ExportTrans.name).Nodup)
    {t t' : ExportTrans} (ht : t ∈ X.trans) (ht' : t' ∈ X.trans) (h : t.name = t'.name) : t = t' :=
  List.inj_on_of_nodup_map hX ht ht' h

/-- Gathering, over transitions with distinct names, what belongs to one name gathers what
belongs to the transition of that name. -/
theorem flatMap_name_eq {β : Type} {ts : List ExportTrans}
    (hts : (ts.map ExportTrans.name).Nodup) {t : ExportTrans} (ht : t ∈ ts)
    (f : ExportTrans → List β) :
    ts.flatMap (fun t' => if t'.name = t.name then f t' else []) = f t := by
  induction ts with
  | nil => cases ht
  | cons a ts ih =>
    simp only [List.map_cons, List.nodup_cons] at hts
    obtain ⟨ha, hts⟩ := hts
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · have : ts.flatMap (fun t' => if t'.name = t.name then f t' else []) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro b hb
        have : b.name ≠ t.name := fun h => ha (h ▸ List.mem_map_of_mem hb)
        simp [this]
      rw [this]
      simp
    · have hne : a.name ≠ t.name := fun h => ha (h ▸ List.mem_map_of_mem ht)
      simp [hne, ih hts ht]

/-- **The output side of a transition in the exporter's graph** is what the reference emitter
draws for it, in order, whatever the cluster stage. -/
theorem refExportWith_outEdges (hX : (X.trans.map ExportTrans.name).Nodup) {t : ExportTrans}
    (ht : t ∈ X.trans) : (refExportWith S cfg X).outEdges t.name = (refEmit.ofTrans t).edges := by
  unfold XGraph.outEdges
  rw [refExportWith_edges, List.filter_append]
  have h2 : (S.ghosts cfg.cluster X (refNodeRefs X) (refEdges X)).filter (XEdge.outSideOf t.name)
      = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    simp [XEdge.outSideOf, S.ghosts_arc _ _ _ _ e he]
  rw [h2, List.append_nil, refEdges, List.filter_flatMap]
  simp only [refTransEdges_filter_outSide]
  exact flatMap_name_eq hX ht (fun t' => (refEmit.ofTrans t').edges)

/-- **The edges of one transition in the exporter's graph.** On a net with distinct transition
names, the edges a predicate `P` picks are those of transition `t` alone, in the order drawn,
whenever `P` picks no ghost edge and only edges that leave a node of `t` or enter `t`: the
exporter's edges of a transition are `refTransEdges`, whatever the cluster stage. -/
theorem refExportWith_filter_trans (hX : (X.trans.map ExportTrans.name).Nodup) {t : ExportTrans}
    (ht : t ∈ X.trans) (P : XEdge → Bool)
    (hP : ∀ e, P e = true → e.arc ≠ .ghost ∧
      (e.src.owner? = some t.name ∨ e.dst = .trans t.name)) :
    (refExportWith S cfg X).edges.filter P = (refTransEdges t).filter P := by
  rw [refExportWith_edges, List.filter_append]
  have h2 : (S.ghosts cfg.cluster X (refNodeRefs X) (refEdges X)).filter P = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he hpe
    exact (hP e hpe).1 (S.ghosts_arc _ _ _ _ e he)
  rw [h2, List.append_nil, refEdges, List.filter_flatMap]
  have h3 : ∀ t' : ExportTrans, (refTransEdges t').filter P =
      if t'.name = t.name then (refTransEdges t').filter P else [] := by
    intro t'
    by_cases hn : t'.name = t.name
    · simp [hn]
    · simp only [hn, if_false]
      rw [List.filter_eq_nil_iff]
      intro e he hpe
      have h1 := (hP e hpe).2
      rcases refTransEdges_ends_owner he with ⟨hs, hd⟩ | ⟨hs, hd⟩
      · rcases h1 with h1 | h1
        · rw [hs] at h1; exact hn (Option.some.inj h1)
        · rw [h1] at hd; simp [NodeRef.owner?] at hd; exact hn hd.symm
      · rcases h1 with h1 | h1
        · rw [hs] at h1; cases h1
        · rw [h1] at hd; exact hn (NodeRef.trans.inj hd).symm
  rw [List.flatMap_congr (fun t' _ => h3 t')]
  exact flatMap_name_eq hX ht (fun t' => (refTransEdges t').filter P)

/-- A node reference is drawn exactly when some node stands for it. -/
theorem mem_refNodeRefs {r : NodeRef} : r ∈ refNodeRefs X ↔ ∃ n ∈ refNodes cfg X, n.ref = r := by
  rw [← refNodes_refs (cfg := cfg), List.mem_map]

/-- **The junction nodes of a transition in the exporter's graph** are the junctions the
reference emitter draws for it, in pre-order. -/
theorem refExportWith_junctionsOf (hX : (X.trans.map ExportTrans.name).Nodup) {t : ExportTrans}
    (ht : t ∈ X.trans) :
    (refExportWith S cfg X).junctionsOf t.name = (refEmit.ofTrans t).junctions := by
  have hp : ∀ n ∈ (refPlaceNames X).map (refPlaceNode cfg X) ++ X.trans.map (refTransNode cfg),
      n.ref.junctionOf t.name = none := by
    intro n hn
    simp only [List.mem_append, List.mem_map] at hn
    rcases hn with ⟨p, _, rfl⟩ | ⟨u, _, rfl⟩ <;> rfl
  have h3 : ∀ t' : ExportTrans,
      (refJunctionNodes t').filterMap (fun n : XNode => n.ref.junctionOf t.name) =
        if t'.name = t.name then (refEmit.ofTrans t').junctions else [] := by
    intro t'
    rw [refJunctionNodes, List.filterMap_map]
    by_cases hn : t'.name = t.name
    · simp only [hn, if_true]
      conv => rhs; rw [← List.filterMap_some (l := (refEmit.ofTrans t').junctions)]
      apply List.filterMap_congr
      intro j _
      simp [refJunctionNode, NodeRef.junctionOf]
    · simp only [hn, if_false]
      rw [List.filterMap_eq_nil_iff]
      intro j _
      simp [refJunctionNode, NodeRef.junctionOf, hn]
  unfold XGraph.junctionsOf
  rw [refExportWith_nodes, refNodes, List.filterMap_append,
    (List.filterMap_eq_nil_iff (f := fun n : XNode => n.ref.junctionOf t.name)).mpr hp,
    List.nil_append, List.filterMap_flatMap]
  simp only [h3]
  exact flatMap_name_eq hX ht (fun t' => (refEmit.ofTrans t').junctions)

end Graph

/-! ## The agreement -/

/-- **The reference exporter agrees with the reference emitter, labellers and classifier**
(`ExportAgrees`), whatever its cluster stage: one mapper meets the emitter, label and category
blocks and the exporter blocks at once. -/
theorem refExportWith_agrees (S : ClusterStage) :
    ExportAgrees (refExportWith S) refEmit refCardLabel refTransLabel refPlaceCategory := by
  intro cfg X ⟨hX, hin⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [refExportWith_outEdges hX ht, refExportWith_junctionsOf hX ht]
    exact ⟨List.Perm.refl _, List.Perm.refl _, fun _ _ => rfl⟩
  · intro n hn t ht hr
    obtain ⟨t', ht', hname, rfl⟩ := (refNodes_ref_cases hn).2.1 t.name hr
    rw [ExportNet.eq_of_name hX ht' ht hname]
    rfl
  · intro n hn p hr
    obtain ⟨_, rfl⟩ := (refNodes_ref_cases hn).1 p hr
    rfl
  · intro e he t ht s hs ha hsrc hdst
    have hg : e.arc ≠ .ghost := by rw [ha]; exact nofun
    obtain ⟨t', ht', he'⟩ := refExportWith_edge_of_ne_ghost he hg
    obtain ⟨s', hs', rfl⟩ := refTransEdges_input he' ha
    have hname : t'.name = t.name := by simpa [refInputEdge] using hdst
    have htt := ExportNet.eq_of_name hX ht' ht hname
    subst htt
    have hp : s'.place = s.place := by simpa [refInputEdge] using hsrc
    have hss : s' = s := List.inj_on_of_nodup_map (hin t' ht') hs' hs hp
    subst hss
    rfl

/-! ## Lemmas: the configuration -/

/-- The show-types flag changes nothing (ruling D41). -/
theorem refExportWith_showTypes (S : ClusterStage) (cfg : ExportCfg) (X : ExportNet) (b : Bool) :
    refExportWith S { cfg with showTypes := b } X = refExportWith S cfg X := rfl

/-- A node with the label of a transition node blanked; every other node unchanged. -/
def XNode.eraseTransLabel (n : XNode) : XNode :=
  match n.ref with
  | .trans _ => { n with label := "" }
  | _ => n

/-- **The show flags change only transition labels**: two configurations with the same
environment places and cluster source give the same edges and clusters, and the same nodes once
the transition labels are blanked. -/
theorem refExportWith_flags (S : ClusterStage) (X : ExportNet) {cfg cfg' : ExportCfg}
    (he : cfg.env = cfg'.env) (hc : cfg.cluster = cfg'.cluster) :
    (refExportWith S cfg X).edges = (refExportWith S cfg' X).edges ∧
    (refExportWith S cfg X).clusters = (refExportWith S cfg' X).clusters ∧
    (refExportWith S cfg X).nodes.map XNode.eraseTransLabel =
      (refExportWith S cfg' X).nodes.map XNode.eraseTransLabel := by
  have hi : cfg.isEnv = cfg'.isEnv := by funext p; simp [ExportCfg.isEnv, he]
  refine ⟨by simp [refExportWith_edges, hc], by simp [refExportWith_clusters, hc], ?_⟩
  simp [refNodes, List.map_flatMap, refPlaceNode, refTransNode, refJunctionNodes,
    refJunctionNode, XNode.eraseTransLabel, hi, Function.comp_def]

/-! ## Lemmas: DOT IDs -/

/-- `sanitize` maps each character. -/
@[simp] theorem sanitize_toList (s : String) : (sanitize s).toList = s.toList.map sanitizeChar := by
  simp [sanitize]

/-- Place IDs are equal exactly when the sanitised names are. -/
theorem nodeId_place_inj (p q : String) :
    nodeId (.place p) = nodeId (.place q) ↔ sanitize p = sanitize q := by
  simp only [nodeId, ← String.toList_inj, String.toList_append]
  constructor
  · intro h; exact List.append_cancel_left h
  · intro h; rw [h]

/-- Transition IDs are equal exactly when the sanitised names are. -/
theorem nodeId_trans_inj (t u : String) :
    nodeId (.trans t) = nodeId (.trans u) ↔ sanitize t = sanitize u := by
  simp only [nodeId, ← String.toList_inj, String.toList_append]
  constructor
  · intro h; exact List.append_cancel_left h
  · intro h; rw [h]

/-- A place ID is no transition ID. -/
theorem nodeId_place_ne_trans (p t : String) : nodeId (.place p) ≠ nodeId (.trans t) := by
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp [nodeId, String.toList_append] at this

/-- A junction ID is no place ID ([EXP-014] guarantee 1). -/
theorem nodeId_junction_ne_place (t : String) (k : JKind) (i : Nat) (p : String) :
    nodeId (.junction t k i) ≠ nodeId (.place p) := by
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp [nodeId, String.toList_append] at this

/-- A junction ID is no transition ID ([EXP-014] guarantee 1). -/
theorem nodeId_junction_ne_trans (t : String) (k : JKind) (i : Nat) (u : String) :
    nodeId (.junction t k i) ≠ nodeId (.trans u) := by
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp [nodeId, String.toList_append] at this

/-! ## A worked example: the DOT of EXP-013 -/

/-- Transition `Try` of [EXP-013]'s worked DOT: `Xor(P_Ok, P_Fail)` and `reset(P_Fail)`. -/
def exportExTry : ExportTrans :=
  { core := ⟨"Try", [⟨"In", .one⟩], [], [], ["Fail"]⟩,
    out := some (.xor [.place "Ok", .place "Fail"]) }

/-- Transition `RefreshCache` of [EXP-013]'s worked DOT, `Out.Place(P_Cache)` and
`reset(P_Cache)`, with an `Exactly(2)` input, an inhibitor, a read arc, a second reset arc, a
window timing and a priority added. -/
def exportExCache : ExportTrans :=
  { core := ⟨"RefreshCache", [⟨"Q", .exactly 2⟩], ["Stop"], ["Cfg"], ["Cache", "Junk"]⟩,
    out := some (.place "Cache"), timing := .window 1 5, prio := 3 }

/-- The worked net: the two transitions, `Ok` a terminal place. -/
def exportExNet : ExportNet := { trans := [exportExTry, exportExCache], term := ["Ok"] }

/-- The reference draws [EXP-013]'s worked DOT: the combined edges `t_RefreshCache → p_Cache` and
`j_Try__xor_0 → p_Fail`, the plain `j_Try__xor_0 → p_Ok` labelled `Ok`, no standalone reset
edge into a combined place, and the standalone reset edge into `Junk`. -/
theorem refExportFlat_example_edges :
    (refExportFlat {} exportExNet).edges.map (fun e => (nodeId e.src, nodeId e.dst, e.arc, e.label)) =
      [("p_In", "t_Try", .input, none),
       ("t_Try", "j_Try__xor_0", .output, none),
       ("j_Try__xor_0", "p_Ok", .output, some "Ok"),
       ("j_Try__xor_0", "p_Fail", .resetOutput, some "reset+out"),
       ("p_Q", "t_RefreshCache", .input, some "×2"),
       ("t_RefreshCache", "p_Cache", .resetOutput, some "reset+out"),
       ("p_Stop", "t_RefreshCache", .inhibitor, none),
       ("p_Cfg", "t_RefreshCache", .read, some "read"),
       ("t_RefreshCache", "p_Junk", .reset, some "reset")] := by
  decide

/-- The nodes of the worked net, with their categories and labels. -/
theorem refExportFlat_example_nodes :
    (refExportFlat {} exportExNet).nodes.map (fun n => (n.id, n.cat, n.label)) =
      [("p_In", .start, ""), ("p_Ok", .terminal, ""), ("p_Fail", .«end», ""),
       ("p_Q", .start, ""), ("p_Stop", .start, ""), ("p_Cfg", .start, ""),
       ("p_Cache", .«end», ""), ("p_Junk", .start, ""),
       ("t_Try", .transition, "Try [0, ∞]ms"),
       ("t_RefreshCache", .transition, "RefreshCache [1, 5]ms prio=3"),
       ("j_Try__xor_0", .xorJunction, "✕")] := by
  decide

end Libpetri.Spec
