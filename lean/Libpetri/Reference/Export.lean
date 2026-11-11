import Libpetri.Spec.GlossaryExport

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

This file is the emitter half of the export model (wave W4 tracer). The mapper half (input,
inhibitor, read and standalone reset edges, place and transition nodes, `refExport`) and the
clustering (`Reference/ExportCluster.lean`) follow.

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

end Libpetri.Spec
