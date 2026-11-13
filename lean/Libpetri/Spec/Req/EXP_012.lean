import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Spec.Text.EXP_012

set_option linter.missingDocs true

/-!
# EXP-012: XOR/AND junction nodes (`spec/09-export.md`)

Which junctions and output edges an exporter draws for the output spec of one transition, and
their labels. The requirement is a predicate over an abstract output emitter `E : Emitter`
(glossary `GlossaryExport.lean`): given a transition name `t`, its reset places `R` and its
output tree `o`, the junctions and edges drawn for the output side of `t`. The block compares
them with the glossary's drawing rule `Drawing t o` (`drawOut`, one clause per sentence), as
lists up to order and up to a one-to-one renumbering of the junction indices.

The witness is the reference emitter `refEmit` (`Reference/Export.lean`), written as the three
runtime mappers run (`emit_output` in the Rust crate `libpetri-export`, `emitOutput` in
`PetriNetGraphMapper.java` and `petri-net-mapper.ts`). The wrong emitters are the four the
export design names (a junction for a single-child group, the binary-nesting emitter that draws
the right-nested `Reference.Out`, the flat pre-EXP-012 emitter, AND children labelled like XOR
children) plus a split-junction emitter for the renumbering and a timeout-dropping emitter for
ruling D26 item 2.

The sentences are the restatement of ruling D26 (items 1 to 3): a short group of either kind is
a pass-through, a `Timeout` labels the edge into its child wherever it sits, a `ForwardInput` is
drawn as a dashed `Place` leaf with `⟵<from>` appended, and the combined edge of EXP-013 takes
its own label and style.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## EXP-012: XOR/AND junction nodes -/

requirement EXP_012
  id "EXP-012"
  title "XOR/AND Junction Nodes"
  kind F
  scope "every exporter, the output side of one transition"
  source verbatim "spec/09-export.md"
  covers EXP_012.s1, EXP_012.s2, EXP_012.s3, EXP_012.s4, EXP_012.s5, EXP_012.s6, EXP_012.s7,
        EXP_012.s8, EXP_012.s9, EXP_012.s10
  reading "For every transition name t, reset places R and output tree o (any tree, short and empty groups included), there is a one-to-one renumbering ρ of the junction indices the emitter E uses, such that:"
          "the junctions E draws, renumbered, are the groups of o with two or more children, one junction each, of the group's kind (OutTree.junctions), in any order;"
          "the edges E draws, renumbered, are the edges of the drawing rule (Drawing t o), one each, in any order: both ends of every edge, and for every edge that does not end in a reset place also its arc type output, style row output, dash and label as the rule gives them."
  assumes "The model is an output emitter E : Emitter (glossary): from a transition name t, its reset places R and its output tree o (glossary OutTree: n-ary And and Xor groups, a Timeout with its duration in ms, Place and ForwardInput leaves), the junctions, as (kind, index), and the edges (glossary XEdge: ends, arc type, style row, dash, label) the exporter draws for the output side of t. The input, inhibitor, read and standalone reset edges and the place and transition nodes are drawn outside the emitter and are other blocks' subject (EXP-001 to EXP-004, EXP-013)."
          "The drawing rule Drawing t o is the glossary's drawOut from the transition, with no inherited label, junctions numbered from 0, one clause per sentence: a group with two or more children gives one junction of its kind and one solid output edge into it from the parent with the inherited label, then its children below it (the first and third shall sentences); a shorter group gives no junction and draws its children from the parent with the inherited label (the second); a Place leaf gives one solid edge into its place from the parent with the inherited label (the third); below an Xor junction a child inherits its branch label (glossary branchLabel), below an And junction and from the transition nothing (the fourth and fifth); a Timeout hands its child the label ⏱<n>ms in place of the inherited one (the sixth); a ForwardInput leaf from F into P is the Place leaf for P, dashed, labelled forwardLabel (⟵F after the inherited label and a space, or ⟵F alone) (the seventh). The two body sentences that open the section say what the first two shall sentences say."
          "Junction indices are compared up to a one-to-one renumbering ρ: which index each junction gets (pre-order from 0) is EXP-014's line, so an emitter that numbers its junctions in post-order still meets this block. The renumbering must be one to one, so an emitter that draws the edge into a junction at one index and the edges out of it at another (two nodes in the graph for one group) violates the block (EXP_012_forbids_split)."
          "Order is not stated: the junctions and edges are compared as lists up to permutation (List.Perm), membership and multiplicity only. Node and edge order across languages is open ruling R2 (exp-b) and kind Q; the order of an Xor junction's children is EXP-005's line."
          "The last shall sentence is the guard of the third line: for an edge that ends in a place of R only its two ends are compared, and its arc type, style row, label and dash are EXP-013's. Its ends and the count, one edge per leaf, still bind, so an emitter that draws a combined edge next to an output edge for one leaf violates this block."
          "The block quantifies over every output tree, including a group with fewer than two children (Rust's Out::Xor is a public variant and a TypeScript node a plain object, so a short Xor reaches the mappers' pass-through arm), an empty group (no junction and no edge, as all three mappers draw it) and a ForwardInput below an Xor junction, which no transition that builds has (IO-013, IO-014): the seventh shall sentence draws it as the Place leaf for its target, so its label is the target name, a space and ⟵F, which is what all three mappers draw."
          "The junction node attributes (shape diamond, fill, stroke, pen width, size, the glyphs ✕ and ✚, font size, fixed size) and the node categories xor-junction and and-junction belong to the exporter's nodes and the style table (Libpetri.Export.Styles), not to the emitter. The category ('Style category xor-junction', 'Style category and-junction') is EXP-014's eighth line: every junction node of kind k has the row JKind.cat k, which the reference's refJunctionNode draws and an exporter that swaps the two rows violates (EXP_014_forbids_junctionCatSwap). The other attributes are the table's constants, checked by tests (kind Q)."
          "This block states the third shall sentence ('one junction node for each group ..., and no other junction node') for one output spec, on the emitter. On the graph it is carried by the junction clause of the export agreement (ExportAgrees, glossary: on a net with distinct transition names the junction nodes of each transition of the net are the emitter's for its output spec, up to order), which the export consistency theorem carries, together with EXP-014's seventh line (no junction node for a transition the net does not have): an exporter that adds a junction node for a name no transition of the net has meets the agreement and violates EXP-014 (EXP_014_forbids_strayJunction)."
          "AC1, AC2, AC3 and AC4 are EXP_012_nonvacuous on the reference emitter: XOR(P_a, P_b) gives one xor junction and the edges junction to P_a and junction to P_b; AND(P_c, P_d) one and junction and two edges; AND(P_a) a direct edge from the transition to P_a and no junction (AC3 is stated with AND by ruling D26 item 1, since IO-012 gives every Xor two or more children); XOR(AND(P_a, P_b), P_c) an and junction nested below the xor junction. Their junction attributes (diamond, ✕, ✚) are the exporter's, as above."
          "AC5 (Java, TypeScript and Rust mappers produce byte-identical junction nodes and edges) is kind Q: a Lean function is deterministic and cross-language equality is a property of three programs (export design P3, ruling D60 (c)); the export corpus EP-2 replays the reference against the runtimes after the migration. The test derivation is AC1 to AC4."
  signoff "2026-11-13 058caa2740b22067 ai"
  statement : Emitter → Prop :=
    fun E => ∀ t R o, ∃ ρ : Nat → Nat, (∀ i j, ρ i = ρ j → i = j) ∧
      List.Perm ((E t R o).junctions.map fun kj => (kj.1, ρ kj.2)) (OutTree.junctions o).zipIdx ∧
      List.Perm ((E t R o).edges.map (XEdge.seen R ρ)) ((Drawing t o).map (DrawnEdge.seen R))

/- The pinned readable form of EXP-012: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_012 : Emitter → Prop :=
fun E =>
  ∀ (t : String) (R : List String) (o : OutTree),
    ∃ ρ,
      (∀ (i j : ℕ), ρ i = ρ j → i = j) ∧
        (List.map (fun kj => (kj.1, ρ kj.2)) (E t R o).junctions).Perm o.junctions.zipIdx ∧
          (List.map (XEdge.seen R ρ) (E t R o).edges).Perm (List.map (DrawnEdge.seen R) (Drawing t o))
-/
#guard_msgs in #print EXP_012

/-! ### The reference -/

/-- Renaming junction indices by the identity changes no node. -/
theorem NodeRef.renJ_id (r : NodeRef) : r.renJ id = r := by
  cases r <;> rfl

/-- An edge of the drawing rule, as the reference draws it, shows EXP-012 what the rule says. -/
theorem refRealize_seen (R : List String) (d : DrawnEdge) :
    XEdge.seen R id (refRealize R d) = DrawnEdge.seen R d := by
  rcases d with ⟨src, dst, dashed, label⟩
  cases dst with
  | place p =>
    by_cases hp : p ∈ R <;>
      simp [refRealize, XEdge.seen, DrawnEdge.seen, NodeRef.renJ_id, NodeRef.inPlaces, hp]
  | trans t => simp [refRealize, XEdge.seen, DrawnEdge.seen, NodeRef.renJ_id, NodeRef.inPlaces]
  | junction t k i =>
    simp [refRealize, XEdge.seen, DrawnEdge.seen, NodeRef.renJ_id, NodeRef.inPlaces]

/-- The reference emitter satisfies EXP-012 with the identity renumbering: it draws exactly the
junctions and edges of the drawing rule, in the rule's order (`refEmit_draws`, by mutual
structural induction over the tree). -/
@[evidence holds EXP_012]
theorem EXP_012_reference : EXP_012 refEmit := by
  intro t R o
  refine ⟨id, fun _ _ h => h, ?_, ?_⟩
  · rw [refEmit_draws]
    simp
  · rw [refEmit_draws, List.map_map]
    have : (XEdge.seen R id ∘ refRealize R) = DrawnEdge.seen R := funext (refRealize_seen R)
    rw [this]

/-! ### Wrong emitters, one per line -/

/-- A copy of the reference walk with two switches: groups with at least `minKids` children get
a junction, and with `andBranch` the children of an `And` junction are labelled like those of an
`Xor` junction. `exp012Walk 2 false` is the reference. -/
def exp012Walk (minKids : Nat) (andBranch : Bool) : Emitter := fun t R o =>
  (go t R (.trans t) none o (0, {})).2
where
  /-- The walk over one subtree. -/
  go (t : String) (R : List String) (par : NodeRef) (l : Option String) :
      OutTree → Nat × Emitted → Nat × Emitted
    | .place p, (n, e) => (n, { e with edges := e.edges ++ [refLeafEdge R par p false l] })
    | .forward src dst, (n, e) =>
      (n, { e with edges := e.edges ++ [refLeafEdge R par dst true (some (forwardLabel l src))] })
    | .timeout ms c, s => go t R par (some (timeoutLabel ms)) c s
    | .and cs, (n, e) =>
      if minKids ≤ cs.length then
        goL t R (.junction t .and n) (if andBranch then .junction .xor else .junction .and) cs
          (n + 1, { junctions := e.junctions ++ [(.and, n)],
                    edges := e.edges ++ [refJunctionEdge par (.junction t .and n) l] })
      else goL t R par (.pass l) cs (n, e)
    | .xor cs, (n, e) =>
      if minKids ≤ cs.length then
        goL t R (.junction t .xor n) (.junction .xor) cs
          (n + 1, { junctions := e.junctions ++ [(.xor, n)],
                    edges := e.edges ++ [refJunctionEdge par (.junction t .xor n) l] })
      else goL t R par (.pass l) cs (n, e)
  /-- The walk over the children of a group. -/
  goL (t : String) (R : List String) (par : NodeRef) (u : Under) :
      List OutTree → Nat × Emitted → Nat × Emitted
    | [], s => s
    | c :: cs, s => goL t R par u cs (go t R par (u.label c) c s)

/-- An emitter that gives a group with a single child a junction (the second line). -/
def exp012_shortJunction : Emitter := exp012Walk 1 false

/-- ✗ A junction for the single-child group `AND(a)` violates EXP-012 (line 2: the drawing rule
has no junction for it; AC3). -/
@[evidence forbids EXP_012]
theorem EXP_012_forbids_shortJunction : ¬ EXP_012 exp012_shortJunction := by
  intro h
  obtain ⟨ρ, -, hj, -⟩ := h "T" [] (.and [.place "a"])
  have := hj.length_eq
  rw [List.length_map] at this
  revert this
  decide

/-- Keep the first child and nest the rest into one group of the same kind, while three or more
are left. -/
def exp012Nest (mk : List OutTree → OutTree) : List OutTree → List OutTree
  | x :: y :: z :: rest => [x, mk (exp012Nest mk (y :: z :: rest))]
  | cs => cs

mutual
/-- Right-nest every group into groups of two children, as the binary `Reference.Out` holds it
(`OutTree.toOut` folds `XOR(a, b, c)` into `XOR(a, XOR(b, c))`). -/
def exp012Binarize : OutTree → OutTree
  | .and cs => .and (exp012Nest .and (exp012BinarizeL cs))
  | .xor cs => .xor (exp012Nest .xor (exp012BinarizeL cs))
  | .timeout ms c => .timeout ms (exp012Binarize c)
  | o => o
/-- `exp012Binarize` on each child. -/
def exp012BinarizeL : List OutTree → List OutTree
  | [] => []
  | c :: cs => exp012Binarize c :: exp012BinarizeL cs
end

/-- The binary-nesting emitter: the reference drawing of the tree the firing model holds, with
every group of three or more children nested right into groups of two. -/
def exp012_binary : Emitter := fun t R o => refEmit t R (exp012Binarize o)

/-- ✗ Drawing `XOR(a, b, c)` with two junctions violates EXP-012 (line 2: one junction per
group). -/
@[evidence forbids EXP_012]
theorem EXP_012_forbids_binary : ¬ EXP_012 exp012_binary := by
  intro h
  obtain ⟨ρ, -, hj, -⟩ := h "T" [] (.xor [.place "a", .place "b", .place "c"])
  have := hj.length_eq
  rw [List.length_map] at this
  revert this
  decide

/-- The flat pre-EXP-012 emitter: one edge from the transition into the place of every leaf,
no junction. -/
def exp012_flat : Emitter := fun t R o =>
  { junctions := [], edges := o.leafPlaces.map fun p => refLeafEdge R (.trans t) p false none }

/-- ✗ The flat emitter violates EXP-012 on `XOR(a, b)` (line 2: no junction; AC1). -/
@[evidence forbids EXP_012]
theorem EXP_012_forbids_flat : ¬ EXP_012 exp012_flat := by
  intro h
  obtain ⟨ρ, -, hj, -⟩ := h "T" [] (.xor [.place "a", .place "b"])
  have := hj.length_eq
  rw [List.length_map] at this
  revert this
  decide

/-- An emitter that labels the children of an `And` junction with their branch labels, as it
does for an `Xor` junction. -/
def exp012_andLabelled : Emitter := exp012Walk 2 true

/-- What the third line compares of an edge apart from its ends; the renumbering plays no part
in it. -/
theorem exp012_seen_look (R : List String) (ρ : Nat → Nat) :
    (fun x : NodeRef × NodeRef × Option (ArcType × EdgeRow × Bool × Option String) => x.2.2) ∘
        XEdge.seen R ρ =
      fun e => if e.dst.inPlaces R then none else some (e.arc, e.row, e.dashed, e.label) := by
  funext e
  rfl

/-- ✗ Labelling the children of `AND(a, b)` with `a` and `b` violates EXP-012 (line 3: the edge
into a child of an `And` junction carries no label of its own). -/
@[evidence forbids EXP_012]
theorem EXP_012_forbids_andLabelled : ¬ EXP_012 exp012_andLabelled := by
  intro h
  obtain ⟨ρ, -, -, he⟩ := h "T" [] (.and [.place "a", .place "b"])
  have := he.map (fun x => x.2.2)
  rw [List.map_map, List.map_map, exp012_seen_look] at this
  revert this
  decide

mutual
/-- Drop every `Timeout` that is a direct child of an `And` group, keeping its child: the
literal reading of the pre-D26 sentence "Edge junction → child for an AND junction: output
style, no label", which leaves no label for a `Timeout` below an `And` junction. -/
def exp012DropAndTimeout : OutTree → OutTree
  | .and cs => .and (exp012DropAndTimeoutL cs)
  | .xor cs => .xor (exp012KeepL cs)
  | .timeout ms c => .timeout ms (exp012DropAndTimeout c)
  | o => o
/-- The children of an `And` group: a `Timeout` child gives way to its child. -/
def exp012DropAndTimeoutL : List OutTree → List OutTree
  | [] => []
  | .timeout _ c :: cs => exp012DropAndTimeout c :: exp012DropAndTimeoutL cs
  | c :: cs => exp012DropAndTimeout c :: exp012DropAndTimeoutL cs
/-- The children of any other group, each transformed. -/
def exp012KeepL : List OutTree → List OutTree
  | [] => []
  | c :: cs => exp012DropAndTimeout c :: exp012KeepL cs
end

/-- The emitter that draws no timeout label below an `And` junction. -/
def exp012_andTimeoutDropped : Emitter := fun t R o => refEmit t R (exp012DropAndTimeout o)

/-- ✗ Dropping the timeout label of `AND(a, Timeout(5, b))` violates EXP-012 (line 3: a
`Timeout` labels the edge into its child wherever it sits, ruling D26 item 2). -/
@[evidence forbids EXP_012]
theorem EXP_012_forbids_andTimeoutDropped : ¬ EXP_012 exp012_andTimeoutDropped := by
  intro h
  obtain ⟨ρ, -, -, he⟩ := h "T" [] (.and [.place "a", .timeout 5 (.place "b")])
  have := he.map (fun x => x.2.2)
  rw [List.map_map, List.map_map, exp012_seen_look] at this
  revert this
  decide

/-- Move the source of every edge that leaves a junction to the next index. -/
def exp012Bump : NodeRef → NodeRef
  | .junction t k i => .junction t k (i + 1)
  | r => r

/-- An emitter that draws the edge into a junction at its index and the edges out of it at the
next index: two graph nodes for one group. -/
def exp012_split : Emitter := fun t R o =>
  let d := refEmit t R o
  { d with edges := d.edges.map fun e => { e with src := exp012Bump e.src } }

/-- ✗ The split emitter violates EXP-012 on `XOR(a, b)` (line 1: the renumbering must be one to
one, and the edge into the junction and the edges out of it name indices 0 and 1). -/
@[evidence forbids EXP_012]
theorem EXP_012_forbids_split : ¬ EXP_012 exp012_split := by
  intro h
  obtain ⟨ρ, hinj, hj, he⟩ := h "T" [] (.xor [.place "a", .place "b"])
  have hJ : (exp012_split "T" [] (.xor [.place "a", .place "b"])).junctions = [(.xor, 0)] := by
    decide
  have hE : (exp012_split "T" [] (.xor [.place "a", .place "b"])).edges =
      [refJunctionEdge (.trans "T") (.junction "T" .xor 0) none,
       refLeafEdge [] (.junction "T" .xor 1) "a" false (some "a"),
       refLeafEdge [] (.junction "T" .xor 1) "b" false (some "b")] := by
    decide
  have hR : (OutTree.junctions (.xor [.place "a", .place "b"])).zipIdx = [(.xor, 0)] := by
    decide
  rw [hJ, hR] at hj
  rw [hE] at he
  have h0 : ρ 0 = 0 := by
    have := hj.mem_iff.mp (List.mem_singleton_self _)
    simpa using this
  have h1 : ρ 1 = 0 := by
    have hm := he.mem_iff.mp (List.mem_map_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    simp [XEdge.seen, Drawing, drawOut, drawOutL, DrawnEdge.seen, refLeafEdge, NodeRef.renJ,
      NodeRef.inPlaces, Under.label, branchLabel] at hm
    omega
  exact absurd (hinj 1 0 (by rw [h0, h1])) (by decide)

/-! ### Non-vacuity: the acceptance criteria on the reference -/

/-- AC1 to AC4 and the two D26 label rules on the reference emitter: `XOR(P_a, P_b)` draws one
xor junction and an edge into each child labelled with its name; `AND(P_c, P_d)` one and
junction and unlabelled edges; `AND(P_a)` a direct edge and no junction; `XOR(AND(P_a, P_b),
P_c)` the and junction numbered 1 below the xor junction 0; a `Timeout` below an `And` junction
labels the edge into its child; a `ForwardInput` below a `Timeout` is dashed and labelled after
the timeout label. -/
@[evidence nonvacuous EXP_012]
theorem EXP_012_nonvacuous :
    refEmit "T" [] (.xor [.place "P_a", .place "P_b"]) =
      { junctions := [(.xor, 0)],
        edges := [refJunctionEdge (.trans "T") (.junction "T" .xor 0) none,
                  refLeafEdge [] (.junction "T" .xor 0) "P_a" false (some "P_a"),
                  refLeafEdge [] (.junction "T" .xor 0) "P_b" false (some "P_b")] } ∧
    refEmit "T" [] (.and [.place "P_c", .place "P_d"]) =
      { junctions := [(.and, 0)],
        edges := [refJunctionEdge (.trans "T") (.junction "T" .and 0) none,
                  refLeafEdge [] (.junction "T" .and 0) "P_c" false none,
                  refLeafEdge [] (.junction "T" .and 0) "P_d" false none] } ∧
    refEmit "T" [] (.and [.place "P_a"]) =
      { junctions := [], edges := [refLeafEdge [] (.trans "T") "P_a" false none] } ∧
    (refEmit "T" [] (.xor [.and [.place "P_a", .place "P_b"], .place "P_c"])).junctions =
      [(.xor, 0), (.and, 1)] ∧
    (refEmit "T" [] (.xor [.and [.place "P_a", .place "P_b"], .place "P_c"])).edges.map
        (fun e => (e.src, e.dst)) =
      [(.trans "T", .junction "T" .xor 0), (.junction "T" .xor 0, .junction "T" .and 1),
       (.junction "T" .and 1, .place "P_a"), (.junction "T" .and 1, .place "P_b"),
       (.junction "T" .xor 0, .place "P_c")] ∧
    (refEmit "T" [] (.and [.place "a", .timeout 5 (.place "b")])).edges.map (·.label) =
      [none, none, some "⏱5ms"] ∧
    (refEmit "T" [] (.timeout 5 (.forward "i" "b"))).edges.map (fun e => (e.dashed, e.label)) =
      [(true, some "⏱5ms ⟵i")] := by
  decide

end Libpetri.Spec
