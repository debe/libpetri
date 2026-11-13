import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Spec.Req.EXP_012
import Libpetri.Spec.Text.EXP_005

set_option linter.missingDocs true

/-!
# EXP-005: XOR branch labels (`spec/09-export.md`)

How a viewer tells the branches of an `Xor` group apart in the exported graph. The requirement is
a predicate over an abstract output emitter `E : Emitter` (glossary `GlossaryExport.lean`), as
[EXP-012] is: given a transition name `t`, its reset places `R` and its output tree `o`, the
junctions and edges drawn for the output side of `t`.

Three lines, each a property a viewer can check on the drawn graph alone: every `Xor` group with
two or more children, at any depth, is an xor junction with one edge out of it per child, the
k-th edge paired with the k-th child; the places reached from the k-th edge, following the drawn
edges down, are the leaf places of the k-th child, one per leaf; and the edge into a `Place`,
`ForwardInput` or `Timeout` child has the dash and label EXP-012 draws for it (`exp005Head`), or,
where EXP-013 combines it into a reset place, a label that is not empty.

The block is derived from [EXP-012]: the reference emitter `refEmit` meets it by the closed form
of its walk (`refEmit_draws`, the drawing rule `drawOut`). It is not a consequence of the EXP-012
statement, which compares edges up to order: the child order of an `Xor` junction is this
block's line. The wrong emitters are the flat pre-EXP-012 emitter of the export design
(`exp012_flat`, under which `XOR(AND(a, b), c)` and `AND(a, b, c)` draw the same), an emitter
that draws an `And` junction for an `Xor` group, one that splices an `And` child's children into
the `Xor` junction, one that reverses the children of an `Xor` junction (refuted by its leaves
and, on children with the same leaves, by its labels), one that reverses a nested `Xor` group,
one that draws no label, one that draws empty labels, one that draws the combined reset edge
with an empty label and one that draws a `ForwardInput` edge solid.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## The block's vocabulary (local to EXP-005) -/

mutual
/-- The child lists of the `Xor` groups with two or more children of an output tree, in
pre-order. Local to EXP-005. -/
def exp005XorGroups : OutTree → List (List OutTree)
  | .place _ => []
  | .forward _ _ => []
  | .timeout _ c => exp005XorGroups c
  | .and cs => exp005XorGroupsL cs
  | .xor cs => (if 2 ≤ cs.length then [cs] else []) ++ exp005XorGroupsL cs
/-- `exp005XorGroups` of a list of children, concatenated. -/
def exp005XorGroupsL : List OutTree → List (List OutTree)
  | [] => []
  | c :: cs => exp005XorGroups c ++ exp005XorGroupsL cs
end

/-- The edges drawn out of node `m`, in the order drawn. Local to EXP-005. -/
def exp005OutOf (es : List XEdge) (m : NodeRef) : List XEdge :=
  es.filter fun e => decide (e.src = m)

/-- The places a viewer reaches from node `m` by following the drawn edges `es` down, at most
`k` edges deep, one entry per path: `m` itself when it is a place, else the places reached from
the ends of the edges out of `m`. Local to EXP-005. -/
def exp005Below (es : List XEdge) : Nat → NodeRef → List String
  | 0, m => m.place?.toList
  | k + 1, m =>
    match m with
    | .place p => [p]
    | _ => (exp005OutOf es m).flatMap fun e => exp005Below es k e.dst

mutual
/-- The dash and label of the edge EXP-012 draws into the subtree `c` when the edge into `c`
would carry `l` (the head edge of the drawing rule `drawOut`): a `Place` leaf keeps `l`, a
`ForwardInput` leaf from `s` is dashed with `forwardLabel l s`, a `Timeout` passes its own label
down, a group with two or more children keeps `l` on the edge into its junction, and a shorter
group passes `l` to its child. Local to EXP-005. -/
def exp005Head : Option String → OutTree → Bool × Option String
  | l, .place _ => (false, l)
  | l, .forward s _ => (true, some (forwardLabel l s))
  | _, .timeout ms c => exp005Head (some (timeoutLabel ms)) c
  | l, .and cs => if 2 ≤ cs.length then (false, l) else exp005HeadL l cs
  | l, .xor cs => if 2 ≤ cs.length then (false, l) else exp005HeadL l cs
/-- `exp005Head` of the first child of a short group. -/
def exp005HeadL : Option String → List OutTree → Bool × Option String
  | l, [] => (false, l)
  | l, c :: _ => exp005Head l c
end

/-! ## EXP-005: XOR branch labels -/

requirement EXP_005
  id "EXP-005"
  title "XOR Branch Labels"
  kind F
  scope "every exporter, the output side of one transition"
  source verbatim "spec/09-export.md"
  covers EXP_005.s1, EXP_005.s2, EXP_005.s3, EXP_005.s4, EXP_005.s5, EXP_005.s6
  reading "For every transition name t, reset places R and output tree o without an empty group (OutTree.toOut o is some), and for every Xor group of o with two or more children cs, at any depth (exp005XorGroups), E draws some xor junction j of t with exactly as many edges out of it as cs has children; the k-th edge out, in the order drawn, is paired with the k-th child c;"
          "the places reached from the end of the k-th edge, following the drawn edges down and counting the paths that end in a place (exp005Below, as deep as E draws edges), are the leaf places of c, one per leaf, up to order (List.Perm);"
          "and when c is a Place, ForwardInput or Timeout child (glossary branchLabel is some), the k-th edge has the dash and the label of the edge EXP-012 draws into c below an Xor junction (exp005Head, from the branch label), unless it ends in a reset place, where its label is some text that is not empty."
  assumes "The model is an output emitter E : Emitter (glossary), as for EXP-012: from a transition name t, its reset places R and its output tree o, the junctions, as (kind, index), and the edges the exporter draws for the output side of t. The block reads the drawn graph only: which edges leave a junction, in the order drawn, where they end, whether they are dashed and what label they carry."
          "The block is stated over the emitter, not over the exported graph. The glossary agreement ExportAgrees ties an exporter to its emitter: the output edges and the junction nodes of each transition are the emitter's up to order, and the edges out of each junction node are the emitter's in the emitter's order. So the order of the children reaches the exported graph through that agreement in the export consistency theorem, and an exporter that lists the branch edges of an Xor junction in reverse order does not agree with an emitter that meets this block."
          "Trees with an empty And or Xor group are out of scope (the hypothesis that OutTree.toOut o is some): IO-011 and IO-012 give every group children, and an empty group draws no edge, so its Xor parent has fewer edges than children (EXP-012 draws it so)."
          "Line 1 asks for some xor junction of t for each group, not for one of its own: two groups whose children reach the same places with the same head labels, as two copies of XOR(a, b) under one And, may be shown by one junction. That each group has its own junction, of its kind and no other, that the junction hangs from the transition or from its parent junction by an edge into it, and the number of the junction (EXP-014) are EXP-012's lines, and EXP-012 rejects an emitter that drops the edge into a junction."
          "\"Reach\" follows drawn edges from a node to the ends of the edges out of it, stopping at a place, at most as many edges deep as the emitter draws (exp005Below). A path that ends at a node other than a place, such as a junction with no edge out of it, reaches no place and is not counted: line 2 bounds the places reached, and the exact set of edges is EXP-012's line. A place shared by two branches, as in XOR(AND(a, b), AND(a, c)) (IO-012 allows overlapping branches), is reached from both: line 2 compares each branch with its own leaves, not the branches with each other (EXP_005_allows_shared)."
          "The order of the children in line 1 is checked through lines 2 and 3: the k-th edge must reach the leaves of the k-th child and, for a Place, ForwardInput or Timeout child, carry its dash and label, so XOR(Timeout(5, a), a) drawn the other way round is rejected (EXP_005_forbids_reversed_sameLeaves). Two group children that reach the same places are not told apart by this block: in XOR(AND(a, b), AND(b, a)) the picture is the same either way round, and where they differ only below the edge into them, as XOR(AND(Timeout(5, a), b), AND(a, b)), the drawing below that edge is EXP-012's line. Two children whose edges EXP-013 combines into the same reset place both carry its label, so their order is not visible."
          "Line 3 asks for the dash and label of EXP-012 (exp005Head): for a Place child the place name, solid; for a ForwardInput child to P from F, P, a space and ⟵F, dashed; for a Timeout child the edge into its child as EXP-012 draws it, labelled ⏱<n>ms, or with the label of a Timeout or ForwardInput nested below it. Where EXP-013 combines the edge into a reset place, line 3 asks only for a label that is not empty, an empty label counting as none because the Rust and TypeScript DOT renderers write it as label=\"\", which Graphviz draws as no label; which label and style it is belongs to EXP-013 (reset+out). A group child carries no label of its own and line 3 asks nothing of its edge, including a short group that EXP-012 passes through: in XOR(AND(a), b) the edge into a is unlabelled (EXP_005_allows_shortGroup, ruling D26 item 1)."
          "The four EARS sentences are lines 1, 2 and 3, the Where sentence being the reset place case of line 3. The two body sentences say the same: branches labelled to indicate the structure is line 3, each branch visually identifiable is lines 1, 2 and 3. AC1 (branches have labels or visual grouping) is line 2 (grouping) and line 3 (labels). AC2 (the viewer can identify which outputs belong to which branch) is line 2. The test derivation (a net with an Xor output is exported and its branches are labelled) is EXP_005_nonvacuous."
          "Shapes, colours and the junction glyph are the exporter's and the style table's (EXP-012, kind Q)."
          "Form: the EARS sentences use 'shall' inside a SHOULD requirement, as IO-016, TIME-015, CONC-023 and EXP-006 do. The priority stays SHOULD; the shall sentences say what an exporter that meets it draws, and the Java, TypeScript and Rust mappers all draw it: they walk the children of a group in order and append one edge per child, with the labels and dashes of EXP-012 (the walk refEmit models)."
  signoff "2026-11-13 39ff9acf25e72cc3 ai"
  statement : Emitter → Prop :=
    fun E => ∀ t R o, (OutTree.toOut o).isSome = true →
      ∀ cs ∈ exp005XorGroups o, ∃ j ∈ (E t R o).junctions, j.1 = .xor ∧
        (exp005OutOf (E t R o).edges (.junction t .xor j.2)).length = cs.length ∧
        ∀ ec ∈ (exp005OutOf (E t R o).edges (.junction t .xor j.2)).zip cs,
          (exp005Below (E t R o).edges (E t R o).edges.length ec.1.dst).Perm
              (OutTree.leafPlaces ec.2) ∧
            ((branchLabel ec.2).isSome = true →
              (ec.1.dst.inPlaces R = false →
                (ec.1.dashed, ec.1.label) = exp005Head (branchLabel ec.2) ec.2) ∧
              (ec.1.dst.inPlaces R = true → ec.1.label.any (fun s => s != "") = true))

/- The pinned readable form of EXP-005: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_005 : Emitter → Prop :=
fun E =>
  ∀ (t : String) (R : List String) (o : OutTree),
    o.toOut.isSome = true →
      ∀ cs ∈ exp005XorGroups o,
        ∃ j ∈ (E t R o).junctions,
          j.1 = JKind.xor ∧
            (exp005OutOf (E t R o).edges (NodeRef.junction t JKind.xor j.2)).length = cs.length ∧
              ∀ ec ∈ (exp005OutOf (E t R o).edges (NodeRef.junction t JKind.xor j.2)).zip cs,
                (exp005Below (E t R o).edges (E t R o).edges.length ec.1.dst).Perm ec.2.leafPlaces ∧
                  ((branchLabel ec.2).isSome = true →
                    (NodeRef.inPlaces R ec.1.dst = false →
                        (ec.1.dashed, ec.1.label) = exp005Head (branchLabel ec.2) ec.2) ∧
                      (NodeRef.inPlaces R ec.1.dst = true → Option.any (fun s => s != "") ec.1.label = true))
-/
#guard_msgs in #print EXP_005

/-! ### The reference

The reference emitter draws the drawing rule (`refEmit_draws`). Read along the drawn graph, the
drawing of a subtree `c` below node `par` has exactly one edge out of `par` (`exp005_head`), and
the places reached from that edge's end are the leaf places of `c`, provided the edges the whole
graph draws out of the junctions of `c` are those of `c`'s drawing (`exp005Agree`: the junctions
of sibling subtrees have other numbers) and the depth bound is at least the size of `c`. -/

mutual
/-- The number of edges the drawing rule draws for a tree. -/
def exp005Size : OutTree → Nat
  | .place _ => 1
  | .forward _ _ => 1
  | .timeout _ c => exp005Size c
  | .and cs => (if 2 ≤ cs.length then 1 else 0) + exp005SizeL cs
  | .xor cs => (if 2 ≤ cs.length then 1 else 0) + exp005SizeL cs
/-- `exp005Size` of a list of children, summed. -/
def exp005SizeL : List OutTree → Nat
  | [] => 0
  | c :: cs => exp005Size c + exp005SizeL cs
end

mutual
/-- The drawing rule draws `exp005Size o` edges for `o`. -/
theorem exp005_drawOut_length (t : String) (par : NodeRef) (l : Option String) :
    ∀ (o : OutTree) (n : Nat), (drawOut t par l n o).length = exp005Size o
  | .place _, _ => rfl
  | .forward _ _, _ => rfl
  | .timeout _ c, n => by
    simp only [drawOut, exp005Size]
    exact exp005_drawOut_length t par _ c n
  | .and cs, n => by
    by_cases h : 2 ≤ cs.length
    · simp only [drawOut, exp005Size, h, if_true, List.length_cons]
      rw [exp005_drawOutL_length]
      omega
    · simp only [drawOut, exp005Size, h, if_false, Nat.zero_add]
      exact exp005_drawOutL_length t par _ cs n
  | .xor cs, n => by
    by_cases h : 2 ≤ cs.length
    · simp only [drawOut, exp005Size, h, if_true, List.length_cons]
      rw [exp005_drawOutL_length]
      omega
    · simp only [drawOut, exp005Size, h, if_false, Nat.zero_add]
      exact exp005_drawOutL_length t par _ cs n
/-- The list form of `exp005_drawOut_length`. -/
theorem exp005_drawOutL_length (t : String) (par : NodeRef) (u : Under) :
    ∀ (cs : List OutTree) (n : Nat), (drawOutL t par u n cs).length = exp005SizeL cs
  | [], _ => rfl
  | c :: cs, n => by
    simp only [drawOutL, exp005SizeL, List.length_append]
    rw [exp005_drawOut_length t par _ c n, exp005_drawOutL_length t par u cs _]
end

/-- A child is no larger than its siblings together. -/
theorem exp005_size_le_of_mem : ∀ {cs : List OutTree} {c : OutTree}, c ∈ cs →
    exp005Size c ≤ exp005SizeL cs
  | _ :: _, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [exp005SizeL]
      omega
    · have := exp005_size_le_of_mem h
      simp only [exp005SizeL]
      omega

/-- The children of a list with a firing view all have one. -/
theorem exp005_toOutL_isSome : ∀ {cs : List OutTree} {xs : List (Out String)},
    OutTree.toOutL cs = some xs → xs.length = cs.length ∧ ∀ c ∈ cs, (OutTree.toOut c).isSome = true
  | [], xs, h => by
    simp only [OutTree.toOutL, Option.some.injEq] at h
    subst h
    simp
  | c :: cs, xs, h => by
    simp only [OutTree.toOutL] at h
    split at h
    · rename_i x ys hx hys
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := exp005_toOutL_isSome hys
      refine ⟨by simp [h1], ?_⟩
      intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · simp [hx]
      · exact h2 c' hc'
    · simp at h

/-- A group with a firing view has children, each with a firing view. -/
theorem exp005_group_isSome {mk : Out String → Out String → Out String} {cs : List OutTree}
    (h : ((OutTree.toOutL cs).bind (nestOpt mk)).isSome = true) :
    cs ≠ [] ∧ ∀ c ∈ cs, (OutTree.toOut c).isSome = true := by
  cases hx : OutTree.toOutL cs with
  | none => simp [hx] at h
  | some xs =>
    rw [hx] at h
    obtain ⟨h1, h2⟩ := exp005_toOutL_isSome hx
    refine ⟨?_, h2⟩
    rintro rfl
    have : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using h1)
    subst this
    simp [nestOpt] at h

/-- An edge of the drawing of `c` from junction number `n` starts at the parent or at a junction
of `c`, numbered from `n` to below `n` plus the number of junctions of `c`. -/
theorem exp005_src {t : String} {par : NodeRef} {l : Option String} {n : Nat} {c : OutTree}
    {d : DrawnEdge} (hd : d ∈ drawOut t par l n c) :
    d.src = par ∨ ∃ k i, d.src = .junction t k i ∧ n ≤ i ∧ i < n + (OutTree.junctions c).length := by
  rcases (drawOut_ends t par l c n d hd).1 with h | ⟨k, i, h, hm⟩
  · exact Or.inl h
  · have := List.mem_zipIdx hm
    exact Or.inr ⟨k, i, h, this.1, this.2.1⟩

/-- The list form of `exp005_src`. -/
theorem exp005_srcL {t : String} {par : NodeRef} {u : Under} {n : Nat} {cs : List OutTree}
    {d : DrawnEdge} (hd : d ∈ drawOutL t par u n cs) :
    d.src = par ∨
      ∃ k i, d.src = .junction t k i ∧ n ≤ i ∧ i < n + (OutTree.junctionsL cs).length := by
  rcases (drawOutL_ends t par u cs n d hd).1 with h | ⟨k, i, h, hm⟩
  · exact Or.inl h
  · have := List.mem_zipIdx hm
    exact Or.inr ⟨k, i, h, this.1, this.2.1⟩

/-- No edge of `ds` starts at `m`: none is kept. -/
theorem exp005_filter_nil {ds : List DrawnEdge} {m : NodeRef} (h : ∀ d ∈ ds, d.src ≠ m) :
    ds.filter (fun d => decide (d.src = m)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro d hd
  simpa using h d hd

/-- The edges `es` draws out of the junctions `js` of transition `t` are those the drawing `ds`
draws, as the reference realises them. -/
def exp005Agree (es : List XEdge) (t : String) (R : List String) (js : List (JKind × Nat))
    (ds : List DrawnEdge) : Prop :=
  ∀ k i, (k, i) ∈ js → exp005OutOf es (.junction t k i) =
    (ds.filter fun d => decide (d.src = .junction t k i)).map (refRealize R)

/-- Agreement on a list of siblings gives agreement on the first and on the rest: the junctions
of the one are numbered apart from those of the other. -/
theorem exp005_agree_split {es : List XEdge} {t : String} {R : List String} {par : NodeRef}
    {u : Under} {n : Nat} {c : OutTree} {cs : List OutTree}
    (hpar : ∀ k i, par = .junction t k i → i < n)
    (h : exp005Agree es t R ((OutTree.junctionsL (c :: cs)).zipIdx n)
      (drawOutL t par u n (c :: cs))) :
    exp005Agree es t R ((OutTree.junctions c).zipIdx n) (drawOut t par (u.label c) n c) ∧
    exp005Agree es t R ((OutTree.junctionsL cs).zipIdx (n + (OutTree.junctions c).length))
      (drawOutL t par u (n + (OutTree.junctions c).length) cs) := by
  simp only [OutTree.junctionsL, List.zipIdx_append, drawOutL] at h
  constructor
  · intro k i hki
    obtain ⟨h1, h2, -⟩ := List.mem_zipIdx hki
    rw [h k i (List.mem_append_left _ hki), List.filter_append, exp005_filter_nil (ds := drawOutL ..),
      List.append_nil]
    intro d hd heq
    rcases exp005_srcL hd with hs | ⟨k', i', hs, h3, h4⟩
    · rw [hs] at heq
      exact absurd (hpar k i heq) (by omega)
    · rw [hs] at heq
      injection heq with _ _ hi
      omega
  · intro k i hki
    obtain ⟨h1, h2, -⟩ := List.mem_zipIdx hki
    rw [h k i (List.mem_append_right _ hki), List.filter_append, exp005_filter_nil (ds := drawOut ..),
      List.nil_append]
    intro d hd heq
    rcases exp005_src hd with hs | ⟨k', i', hs, h3, h4⟩
    · rw [hs] at heq
      exact absurd (hpar k i heq) (by omega)
    · rw [hs] at heq
      injection heq with _ _ hi
      omega

/-- Agreement on a group drawn as junction `n` gives the edges out of the junction and agreement
on its children. -/
theorem exp005_agree_group {es : List XEdge} {t : String} {R : List String} {par : NodeRef}
    {l : Option String} {n : Nat} {k : JKind} {cs : List OutTree}
    (hpar : ∀ k i, par = .junction t k i → i < n)
    (h : exp005Agree es t R ((k, n) :: (OutTree.junctionsL cs).zipIdx (n + 1))
      (⟨par, .junction t k n, false, l⟩ :: drawOutL t (.junction t k n) (.junction k) (n + 1) cs)) :
    exp005OutOf es (.junction t k n) =
      ((drawOutL t (.junction t k n) (.junction k) (n + 1) cs).filter
        fun d => decide (d.src = .junction t k n)).map (refRealize R) ∧
    exp005Agree es t R ((OutTree.junctionsL cs).zipIdx (n + 1))
      (drawOutL t (.junction t k n) (.junction k) (n + 1) cs) := by
  have hne : ∀ k' i, n ≤ i → par ≠ .junction t k' i :=
    fun k' i hi hp => absurd (hpar k' i hp) (by omega)
  constructor
  · rw [h k n (List.mem_cons_self ..), List.filter_cons, if_neg (by simpa using hne k n le_rfl)]
  · intro k' i hki
    have := List.mem_zipIdx hki
    rw [h k' i (List.mem_cons_of_mem _ hki), List.filter_cons,
      if_neg (by simpa using hne k' i (by omega))]

/-- The reference realises an edge of the drawing rule with the rule's dash and label, unless it
ends in a reset place, where it carries `reset+out` (EXP-013). -/
theorem exp005_realize (R : List String) (d : DrawnEdge) :
    (d.dst.inPlaces R = false →
      ((refRealize R d).dashed, (refRealize R d).label) = (d.dashed, d.label)) ∧
    (d.dst.inPlaces R = true → (refRealize R d).label = some "reset+out") := by
  rcases d with ⟨src, dst, dashed, label⟩
  cases dst with
  | place p => by_cases hp : p ∈ R <;> simp_all [refRealize, NodeRef.inPlaces]
  | trans _ => simp [refRealize, NodeRef.inPlaces]
  | junction _ _ _ => simp [refRealize, NodeRef.inPlaces]

/-- What the heads of the children of a group give: the dash and label of `exp005Head` from the
inherited label, and the child's leaf places below. -/
def exp005HeadOk (es : List XEdge) (F : Nat) (u : Under) (h : DrawnEdge) (c : OutTree) : Prop :=
  (h.dashed, h.label) = exp005Head (u.label c) c ∧ exp005Below es F h.dst = OutTree.leafPlaces c

/-- The places below the heads of the children are the leaf places of the children. -/
theorem exp005_flatMap_below {es : List XEdge} {F : Nat} {u : Under} :
    ∀ {hs : List DrawnEdge} {cs : List OutTree}, List.Forall₂ (exp005HeadOk es F u) hs cs →
      hs.flatMap (fun h => exp005Below es F h.dst) = OutTree.leafPlacesL cs
  | _, _, .nil => rfl
  | _, _, .cons h1 h2 => by
    simp only [List.flatMap_cons, OutTree.leafPlacesL, h1.2, exp005_flatMap_below h2]

mutual
/-- **The head of a subtree's drawing**: the drawing of `c` below `par` has exactly one edge out
of `par`; it has the dash and label `exp005Head l c`; and the places reached from its end are the
leaf places of `c`. -/
theorem exp005_head (t : String) (R : List String) (es : List XEdge) :
    ∀ (c : OutTree) (par : NodeRef) (l : Option String) (n F : Nat),
      (OutTree.toOut c).isSome = true → (∀ k i, par = .junction t k i → i < n) →
      exp005Agree es t R ((OutTree.junctions c).zipIdx n) (drawOut t par l n c) →
      exp005Size c ≤ F →
      ∃ d, (drawOut t par l n c).filter (fun d => decide (d.src = par)) = [d] ∧
        (d.dashed, d.label) = exp005Head l c ∧ exp005Below es F d.dst = OutTree.leafPlaces c
  | .place p, par, l, n, F, _, _, _, _ =>
    ⟨⟨par, .place p, false, l⟩, by simp [drawOut], by simp [exp005Head], by cases F <;> rfl⟩
  | .forward s q, par, l, n, F, _, _, _, _ =>
    ⟨⟨par, .place q, true, some (forwardLabel l s)⟩, by simp [drawOut], by simp [exp005Head],
      by cases F <;> rfl⟩
  | .timeout ms c, par, l, n, F, hne, hpar, hag, hF => by
    simp only [drawOut, OutTree.junctions, OutTree.leafPlaces, exp005Size, exp005Head] at hag hF ⊢
    have hne' : (OutTree.toOut c).isSome = true := by simpa [OutTree.toOut] using hne
    exact exp005_head t R es c par _ n F hne' hpar hag hF
  | .and cs, par, l, n, F, hne, hpar, hag, hF => by
    obtain ⟨hcs, hall⟩ := exp005_group_isSome (mk := .and) (by simpa [OutTree.toOut] using hne)
    by_cases h : 2 ≤ cs.length
    · simp only [drawOut, OutTree.junctions, exp005Size, h, if_true, List.singleton_append,
        List.zipIdx_cons, OutTree.leafPlaces, exp005Head] at hag hF ⊢
      obtain ⟨hJ, hag'⟩ := exp005_agree_group hpar hag
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      obtain ⟨hs, hhs, h2⟩ := exp005_heads t R es cs (.junction t .and n) (.junction .and) (n + 1)
        F' hall (fun k i hk => by injection hk with _ _ hi; omega) hag'
        (fun c hc => le_trans (exp005_size_le_of_mem hc) (by omega))
      refine ⟨⟨par, .junction t .and n, false, l⟩, ?_, rfl, ?_⟩
      · rw [List.filter_cons, if_pos (by simp), exp005_filter_nil]
        intro d hd heq
        rcases exp005_srcL hd with hs | ⟨k', i', hs, h3, h4⟩
        · rw [hs] at heq
          exact absurd (hpar _ _ heq.symm) (by omega)
        · rw [hs] at heq
          exact absurd (hpar _ _ heq.symm) (by omega)
      · simp only [exp005Below]
        rw [hJ, hhs, List.flatMap_map]
        simp only [refRealize_dst]
        exact exp005_flatMap_below h2
    · simp only [drawOut, OutTree.junctions, exp005Size, h, if_false, List.nil_append,
        Nat.zero_add, OutTree.leafPlaces, exp005Head] at hag hF ⊢
      obtain ⟨hs, hhs, h2⟩ := exp005_heads t R es cs par (.pass l) n F hall hpar hag
        (fun c hc => le_trans (exp005_size_le_of_mem hc) hF)
      obtain ⟨x, rfl⟩ : ∃ x, cs = [x] := by
        match cs, hcs, h with
        | [x], _, _ => exact ⟨x, rfl⟩
        | [], hcs, _ => exact absurd rfl hcs
        | _ :: _ :: _, _, h => simp at h
      rcases h2 with _ | ⟨hP, hrest⟩
      rcases hrest with _ | _
      exact ⟨_, hhs, by simpa [exp005HeadL, Under.label] using hP.1,
        by simpa [OutTree.leafPlacesL] using hP.2⟩
  | .xor cs, par, l, n, F, hne, hpar, hag, hF => by
    obtain ⟨hcs, hall⟩ := exp005_group_isSome (mk := .xor) (by simpa [OutTree.toOut] using hne)
    by_cases h : 2 ≤ cs.length
    · simp only [drawOut, OutTree.junctions, exp005Size, h, if_true, List.singleton_append,
        List.zipIdx_cons, OutTree.leafPlaces, exp005Head] at hag hF ⊢
      obtain ⟨hJ, hag'⟩ := exp005_agree_group hpar hag
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      obtain ⟨hs, hhs, h2⟩ := exp005_heads t R es cs (.junction t .xor n) (.junction .xor) (n + 1)
        F' hall (fun k i hk => by injection hk with _ _ hi; omega) hag'
        (fun c hc => le_trans (exp005_size_le_of_mem hc) (by omega))
      refine ⟨⟨par, .junction t .xor n, false, l⟩, ?_, rfl, ?_⟩
      · rw [List.filter_cons, if_pos (by simp), exp005_filter_nil]
        intro d hd heq
        rcases exp005_srcL hd with hs | ⟨k', i', hs, h3, h4⟩
        · rw [hs] at heq
          exact absurd (hpar _ _ heq.symm) (by omega)
        · rw [hs] at heq
          exact absurd (hpar _ _ heq.symm) (by omega)
      · simp only [exp005Below]
        rw [hJ, hhs, List.flatMap_map]
        simp only [refRealize_dst]
        exact exp005_flatMap_below h2
    · simp only [drawOut, OutTree.junctions, exp005Size, h, if_false, List.nil_append,
        Nat.zero_add, OutTree.leafPlaces, exp005Head] at hag hF ⊢
      obtain ⟨hs, hhs, h2⟩ := exp005_heads t R es cs par (.pass l) n F hall hpar hag
        (fun c hc => le_trans (exp005_size_le_of_mem hc) hF)
      obtain ⟨x, rfl⟩ : ∃ x, cs = [x] := by
        match cs, hcs, h with
        | [x], _, _ => exact ⟨x, rfl⟩
        | [], hcs, _ => exact absurd rfl hcs
        | _ :: _ :: _, _, h => simp at h
      rcases h2 with _ | ⟨hP, hrest⟩
      rcases hrest with _ | _
      exact ⟨_, hhs, by simpa [exp005HeadL, Under.label] using hP.1,
        by simpa [OutTree.leafPlacesL] using hP.2⟩
/-- The list form of `exp005_head`: the drawing of the children below `par` has, out of `par`,
exactly the heads of the children, in child order. -/
theorem exp005_heads (t : String) (R : List String) (es : List XEdge) :
    ∀ (cs : List OutTree) (par : NodeRef) (u : Under) (n F : Nat),
      (∀ c ∈ cs, (OutTree.toOut c).isSome = true) → (∀ k i, par = .junction t k i → i < n) →
      exp005Agree es t R ((OutTree.junctionsL cs).zipIdx n) (drawOutL t par u n cs) →
      (∀ c ∈ cs, exp005Size c ≤ F) →
      ∃ hs, (drawOutL t par u n cs).filter (fun d => decide (d.src = par)) = hs ∧
        List.Forall₂ (exp005HeadOk es F u) hs cs
  | [], _, _, _, _, _, _, _, _ => ⟨[], by simp [drawOutL], .nil⟩
  | c :: cs, par, u, n, F, hne, hpar, hag, hF => by
    obtain ⟨hag1, hag2⟩ := exp005_agree_split hpar hag
    obtain ⟨d, hd1, hd2, hd3⟩ := exp005_head t R es c par (u.label c) n F
      (hne c (List.mem_cons_self ..)) hpar hag1 (hF c (List.mem_cons_self ..))
    obtain ⟨hs, hhs, h2⟩ := exp005_heads t R es cs par u (n + (OutTree.junctions c).length) F
      (fun c' h' => hne c' (List.mem_cons_of_mem _ h'))
      (fun k i h => by have := hpar k i h; omega) hag2
      (fun c' h' => hF c' (List.mem_cons_of_mem _ h'))
    refine ⟨d :: hs, ?_, .cons ⟨hd2, hd3⟩ h2⟩
    simp only [drawOutL, List.filter_append, hd1, hhs, List.singleton_append]
end

/-- What the statement asks of junction `i` for the group with children `cs`. -/
def exp005Good (es : List XEdge) (t : String) (R : List String) (i : Nat) (cs : List OutTree) :
    Prop :=
  (exp005OutOf es (.junction t .xor i)).length = cs.length ∧
  ∀ ec ∈ (exp005OutOf es (.junction t .xor i)).zip cs,
    (exp005Below es es.length ec.1.dst).Perm (OutTree.leafPlaces ec.2) ∧
      ((branchLabel ec.2).isSome = true →
        (ec.1.dst.inPlaces R = false →
          (ec.1.dashed, ec.1.label) = exp005Head (branchLabel ec.2) ec.2) ∧
        (ec.1.dst.inPlaces R = true → ec.1.label.any (fun s => s != "") = true))

/-- The heads of the children of an `Xor` junction, as the reference realises them, meet the
statement. -/
theorem exp005_good_of {es : List XEdge} {R : List String} :
    ∀ {hs : List DrawnEdge} {cs : List OutTree},
      List.Forall₂ (exp005HeadOk es es.length (.junction .xor)) hs cs →
      (hs.map (refRealize R)).length = cs.length ∧
      ∀ ec ∈ (hs.map (refRealize R)).zip cs,
        (exp005Below es es.length ec.1.dst).Perm (OutTree.leafPlaces ec.2) ∧
          ((branchLabel ec.2).isSome = true →
            (ec.1.dst.inPlaces R = false →
              (ec.1.dashed, ec.1.label) = exp005Head (branchLabel ec.2) ec.2) ∧
            (ec.1.dst.inPlaces R = true → ec.1.label.any (fun s => s != "") = true))
  | _, _, .nil => by simp
  | _, _, .cons h1 h2 => by
    obtain ⟨ih1, ih2⟩ := exp005_good_of (R := R) h2
    refine ⟨by simp [ih1], ?_⟩
    intro ec hec
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hec
    rcases hec with rfl | hec
    · refine ⟨by rw [refRealize_dst, h1.2], fun _ => ⟨fun hR => ?_, fun hR => ?_⟩⟩
      · rw [refRealize_dst] at hR
        rw [(exp005_realize R _).1 hR]
        exact h1.1
      · rw [refRealize_dst] at hR
        rw [(exp005_realize R _).2 hR]
        rfl
    · exact ih2 ec hec

mutual
/-- **Every `Xor` group of a subtree is drawn as one of its junctions** meeting the statement. -/
theorem exp005_groups (t : String) (R : List String) (es : List XEdge) :
    ∀ (c : OutTree) (par : NodeRef) (l : Option String) (n : Nat),
      (OutTree.toOut c).isSome = true → (∀ k i, par = .junction t k i → i < n) →
      exp005Agree es t R ((OutTree.junctions c).zipIdx n) (drawOut t par l n c) →
      exp005Size c ≤ es.length →
      ∀ g ∈ exp005XorGroups c,
        ∃ j ∈ (OutTree.junctions c).zipIdx n, j.1 = .xor ∧ exp005Good es t R j.2 g
  | .place _, _, _, _, _, _, _, _, g, hg => by simp [exp005XorGroups] at hg
  | .forward _ _, _, _, _, _, _, _, _, g, hg => by simp [exp005XorGroups] at hg
  | .timeout ms c, par, l, n, hne, hpar, hag, hF, g, hg => by
    simp only [drawOut, OutTree.junctions, exp005Size, exp005XorGroups] at hag hF hg ⊢
    exact exp005_groups t R es c par _ n (by simpa [OutTree.toOut] using hne) hpar hag hF g hg
  | .and cs, par, l, n, hne, hpar, hag, hF, g, hg => by
    obtain ⟨-, hall⟩ := exp005_group_isSome (mk := .and) (by simpa [OutTree.toOut] using hne)
    simp only [exp005XorGroups] at hg
    by_cases h : 2 ≤ cs.length
    · simp only [drawOut, OutTree.junctions, exp005Size, h, if_true, List.singleton_append,
        List.zipIdx_cons] at hag hF ⊢
      obtain ⟨-, hag'⟩ := exp005_agree_group hpar hag
      obtain ⟨j, hj, h1, h2⟩ := exp005_groupsL t R es cs (.junction t .and n) (.junction .and)
        (n + 1) hall (fun k i hk => by injection hk with _ _ hi; omega) hag' (by omega) g hg
      exact ⟨j, List.mem_cons_of_mem _ hj, h1, h2⟩
    · simp only [drawOut, OutTree.junctions, exp005Size, h, if_false, List.nil_append,
        Nat.zero_add] at hag hF ⊢
      exact exp005_groupsL t R es cs par (.pass l) n hall hpar hag hF g hg
  | .xor cs, par, l, n, hne, hpar, hag, hF, g, hg => by
    obtain ⟨-, hall⟩ := exp005_group_isSome (mk := .xor) (by simpa [OutTree.toOut] using hne)
    by_cases h : 2 ≤ cs.length
    · simp only [drawOut, OutTree.junctions, exp005Size, h, if_true, List.singleton_append,
        List.zipIdx_cons] at hag hF ⊢
      simp only [exp005XorGroups, h, if_true, List.singleton_append, List.mem_cons] at hg
      obtain ⟨hJ, hag'⟩ := exp005_agree_group hpar hag
      have hparJ : ∀ k i, NodeRef.junction t .xor n = .junction t k i → i < n + 1 :=
        fun k i hk => by injection hk with _ _ hi; omega
      rcases hg with rfl | hg
      · obtain ⟨hs, hhs, h2⟩ := exp005_heads t R es g (.junction t .xor n) (.junction .xor) (n + 1)
          es.length hall hparJ hag' (fun c hc => le_trans (exp005_size_le_of_mem hc) (by omega))
        refine ⟨(.xor, n), List.mem_cons_self .., rfl, ?_⟩
        unfold exp005Good
        rw [hJ, hhs]
        exact exp005_good_of h2
      · obtain ⟨j, hj, h1, h2⟩ := exp005_groupsL t R es cs (.junction t .xor n) (.junction .xor)
          (n + 1) hall hparJ hag' (by omega) g hg
        exact ⟨j, List.mem_cons_of_mem _ hj, h1, h2⟩
    · simp only [drawOut, OutTree.junctions, exp005Size, h, if_false, List.nil_append,
        Nat.zero_add] at hag hF ⊢
      simp only [exp005XorGroups, h, if_false, List.nil_append] at hg
      exact exp005_groupsL t R es cs par (.pass l) n hall hpar hag hF g hg
/-- The list form of `exp005_groups`. -/
theorem exp005_groupsL (t : String) (R : List String) (es : List XEdge) :
    ∀ (cs : List OutTree) (par : NodeRef) (u : Under) (n : Nat),
      (∀ c ∈ cs, (OutTree.toOut c).isSome = true) → (∀ k i, par = .junction t k i → i < n) →
      exp005Agree es t R ((OutTree.junctionsL cs).zipIdx n) (drawOutL t par u n cs) →
      exp005SizeL cs ≤ es.length →
      ∀ g ∈ exp005XorGroupsL cs,
        ∃ j ∈ (OutTree.junctionsL cs).zipIdx n, j.1 = .xor ∧ exp005Good es t R j.2 g
  | [], _, _, _, _, _, _, _, g, hg => by simp [exp005XorGroupsL] at hg
  | c :: cs, par, u, n, hne, hpar, hag, hF, g, hg => by
    obtain ⟨hag1, hag2⟩ := exp005_agree_split hpar hag
    simp only [exp005XorGroupsL, List.mem_append] at hg
    simp only [exp005SizeL] at hF
    simp only [OutTree.junctionsL, List.zipIdx_append, List.mem_append]
    rcases hg with hg | hg
    · obtain ⟨j, hj, h1, h2⟩ := exp005_groups t R es c par (u.label c) n
        (hne c (List.mem_cons_self ..)) hpar hag1 (by omega) g hg
      exact ⟨j, Or.inl hj, h1, h2⟩
    · obtain ⟨j, hj, h1, h2⟩ := exp005_groupsL t R es cs par u _
        (fun c' h' => hne c' (List.mem_cons_of_mem _ h'))
        (fun k i h => by have := hpar k i h; omega) hag2 (by omega) g hg
      exact ⟨j, Or.inr hj, h1, h2⟩
end

/-- The reference emitter satisfies EXP-005, for every tree without an empty group: each `Xor`
group with two or more children is its junction in the pre-order numbering, the edges out of it
are the heads of the children's drawings in child order, and the places below each head are the
child's leaf places (`exp005_groups`, by mutual structural induction over the tree, on the closed
form `refEmit_draws`). -/
@[evidence holds EXP_005]
theorem EXP_005_reference : EXP_005 refEmit := by
  intro t R o hne cs hcs
  have hag : exp005Agree (refEmit t R o).edges t R ((OutTree.junctions o).zipIdx 0)
      (drawOut t (.trans t) none 0 o) := by
    intro k i _
    rw [refEmit_draws]
    simp [exp005OutOf, Drawing, List.filter_map, Function.comp_def, refRealize_src]
  have hsz : exp005Size o ≤ (refEmit t R o).edges.length := by
    rw [refEmit_draws]
    simp [Drawing, exp005_drawOut_length]
  obtain ⟨j, hj, h1, h2⟩ := exp005_groups t R (refEmit t R o).edges o (.trans t) none 0 hne
    (fun k i h => by cases h) hag hsz cs hcs
  rw [refEmit_junctions]
  exact ⟨j, hj, h1, h2⟩

/-! ### Wrong emitters, one per line -/

/-- An emitter that draws every `Xor` group as an `And` group: an and junction, unlabelled
branches. -/
def exp005_andKind : Emitter := fun t R o =>
  refEmit t R (match o with | .xor cs => .and cs | o => o)

/-- ✗ Drawing `XOR(a, b)` with an and junction violates EXP-005 (line 1: no xor junction). -/
@[evidence forbids EXP_005]
theorem EXP_005_forbids_andKind : ¬ EXP_005 exp005_andKind := by
  intro h
  have := h "T" [] (.xor [.place "a", .place "b"]) (by decide) [.place "a", .place "b"]
    (by simp [exp005XorGroups, exp005XorGroupsL])
  revert this
  decide

/-- ✗ The flat pre-EXP-012 emitter (EXP-012's `exp012_flat`) violates EXP-005 on `XOR(AND(a, b),
c)` (line 1: no junction at all, so the branches cannot be told from `AND(a, b, c)`). -/
@[evidence forbids EXP_005]
theorem EXP_005_forbids_flat : ¬ EXP_005 exp012_flat := by
  intro h
  have := h "T" [] (.xor [.and [.place "a", .place "b"], .place "c"]) (by decide)
    [.and [.place "a", .place "b"], .place "c"] (by simp [exp005XorGroups, exp005XorGroupsL])
  revert this
  decide

/-- Splice the children of every `And` child of a top-level `Xor` group into the group. -/
def exp005Splice : OutTree → OutTree
  | .xor cs => .xor (cs.flatMap fun c => match c with | .and ds => ds | c => [c])
  | o => o

/-- An emitter that draws the leaves of an `And` child of an `Xor` group straight from the xor
junction. -/
def exp005_spliced : Emitter := fun t R o => refEmit t R (exp005Splice o)

/-- ✗ Drawing `XOR(AND(a, b), c)` with three edges out of the xor junction violates EXP-005 (line
1: one edge per child). -/
@[evidence forbids EXP_005]
theorem EXP_005_forbids_spliced : ¬ EXP_005 exp005_spliced := by
  intro h
  have := h "T" [] (.xor [.and [.place "a", .place "b"], .place "c"]) (by decide)
    [.and [.place "a", .place "b"], .place "c"] (by simp [exp005XorGroups, exp005XorGroupsL])
  revert this
  decide

/-- An emitter that draws the children of a top-level `Xor` group in reverse order. -/
def exp005_reversed : Emitter := fun t R o =>
  refEmit t R (match o with | .xor cs => .xor cs.reverse | o => o)

/-- ✗ Drawing the branches of `XOR(a, b)` in reverse violates EXP-005 (line 2: the first edge out
of the junction reaches `b`, not the leaf `a` of the first child; both edges are labelled and
there are two, so lines 1 and 3 hold). -/
@[evidence forbids EXP_005]
theorem EXP_005_forbids_reversed : ¬ EXP_005 exp005_reversed := by
  intro h
  have := h "T" [] (.xor [.place "a", .place "b"]) (by decide) [.place "a", .place "b"]
    (by simp [exp005XorGroups, exp005XorGroupsL])
  revert this
  decide

/-- An emitter that draws the reference's junctions and edges with no label. -/
def exp005_unlabelled : Emitter := fun t R o =>
  let d := refEmit t R o
  { d with edges := d.edges.map fun e => { e with label := none } }

/-- ✗ Drawing `XOR(a, b)` without branch labels violates EXP-005 (line 3: the edge into a `Place`
child carries a label). -/
@[evidence forbids EXP_005]
theorem EXP_005_forbids_unlabelled : ¬ EXP_005 exp005_unlabelled := by
  intro h
  have := h "T" [] (.xor [.place "a", .place "b"]) (by decide) [.place "a", .place "b"]
    (by simp [exp005XorGroups, exp005XorGroupsL])
  revert this
  decide

/-- ✗ The reversing emitter also violates EXP-005 on `XOR(Timeout(5, a), a)`, whose two children
reach the same place: line 2 holds both ways round, and line 3 refutes it, since the first edge
out of the xor junction carries `a` where the `Timeout` child's edge carries `⏱5ms`. -/
@[evidence forbids EXP_005]
theorem EXP_005_forbids_reversed_sameLeaves : ¬ EXP_005 exp005_reversed := by
  intro h
  have := h "T" [] (.xor [.timeout 5 (.place "a"), .place "a"]) (by decide)
    [.timeout 5 (.place "a"), .place "a"] (by simp [exp005XorGroups, exp005XorGroupsL])
  revert this
  decide

/-- Reverse the children of every `Xor` child of a top-level `And` group. -/
def exp005RevNested : OutTree → OutTree
  | .and cs => .and (cs.map fun c => match c with | .xor ds => .xor ds.reverse | c => c)
  | o => o

/-- An emitter that draws a top-level group as the reference does and the children of an `Xor`
group nested below it in reverse order. -/
def exp005_nestedReversed : Emitter := fun t R o => refEmit t R (exp005RevNested o)

/-- ✗ Drawing the nested `Xor` of `AND(XOR(a, b), c)` in reverse violates EXP-005 (lines 1 and 2
reach every `Xor` group at any depth: the first edge out of xor junction 1 reaches `b`, not the
leaf `a` of the first child). -/
@[evidence forbids EXP_005]
theorem EXP_005_forbids_nestedReversed : ¬ EXP_005 exp005_nestedReversed := by
  intro h
  have := h "T" [] (.and [.xor [.place "a", .place "b"], .place "c"]) (by decide)
    [.place "a", .place "b"] (by simp [exp005XorGroups, exp005XorGroupsL])
  revert this
  decide

/-- An emitter that draws every label of the reference as the empty string, a port slip such
as `label: branchLabel ? '' : undefined`; the DOT renderers write `label=""`, which Graphviz draws
as no label. -/
def exp005_emptyLabel : Emitter := fun t R o =>
  let d := refEmit t R o
  { d with edges := d.edges.map fun e => { e with label := e.label.map fun _ => "" } }

/-- ✗ Drawing the branches of `XOR(a, b)` with empty labels violates EXP-005 (line 3: the edge
into a `Place` child carries the place name). -/
@[evidence forbids EXP_005]
theorem EXP_005_forbids_emptyLabel : ¬ EXP_005 exp005_emptyLabel := by
  intro h
  have := h "T" [] (.xor [.place "a", .place "b"]) (by decide) [.place "a", .place "b"]
    (by simp [exp005XorGroups, exp005XorGroupsL])
  revert this
  decide

/-- An emitter that draws the combined reset+output edges of the reference with an empty label
and every other edge as the reference does. -/
def exp005_emptyResetLabel : Emitter := fun t R o =>
  let d := refEmit t R o
  { d with edges := d.edges.map fun e =>
      if e.arc = .resetOutput then { e with label := some "" } else e }

/-- ✗ Drawing the combined edge into the reset place `a` of `XOR(a, b)` with an empty label
violates EXP-005 (line 3, the reset place case: a label that is not empty). -/
@[evidence forbids EXP_005]
theorem EXP_005_forbids_emptyResetLabel : ¬ EXP_005 exp005_emptyResetLabel := by
  intro h
  have := h "T" ["a"] (.xor [.place "a", .place "b"]) (by decide) [.place "a", .place "b"]
    (by simp [exp005XorGroups, exp005XorGroupsL])
  revert this
  decide

/-- An emitter that draws every edge of the reference solid. -/
def exp005_solidForward : Emitter := fun t R o =>
  let d := refEmit t R o
  { d with edges := d.edges.map fun e => { e with dashed := false } }

/-- ✗ Drawing the `ForwardInput` branch of `XOR(ForwardInput(x → a), b)` solid violates EXP-005
(line 3: the edge into a `ForwardInput` child is dashed). -/
@[evidence forbids EXP_005]
theorem EXP_005_forbids_solidForward : ¬ EXP_005 exp005_solidForward := by
  intro h
  have := h "T" [] (.xor [.forward "x" "a", .place "b"]) (by decide) [.forward "x" "a", .place "b"]
    (by simp [exp005XorGroups, exp005XorGroupsL])
  revert this
  decide

/-! ### What the block allows -/

/-- ✓ EXP-005 allows a place shared by two branches: in `XOR(AND(a, b), AND(a, c))` (overlapping
branches, which IO-012 allows) the reference meets the block and draws one edge into `a` under
each and junction, so `a` is reached from both branches. -/
@[evidence allows EXP_005]
theorem EXP_005_allows_shared :
    EXP_005 refEmit ∧
    ((refEmit "T" [] (.xor [.and [.place "a", .place "b"], .and [.place "a", .place "c"]])).edges.filter
        fun e => decide (e.dst = .place "a")).map (·.src) =
      [.junction "T" .and 1, .junction "T" .and 2] := by
  exact ⟨EXP_005_reference, by decide⟩

/-- ✓ EXP-005 allows an unlabelled edge into a short group's child: in `XOR(AND(a), b)` the
single-child `And` passes through (EXP-012, ruling D26 item 1), the edge from the xor junction
into `a` carries the label of a group child, none, and the reference meets the block. -/
@[evidence allows EXP_005]
theorem EXP_005_allows_shortGroup :
    EXP_005 refEmit ∧
    ((exp005OutOf (refEmit "T" [] (.xor [.and [.place "a"], .place "b"])).edges
        (.junction "T" .xor 0)).map fun e => (e.dst, e.label)) =
      [(.place "a", none), (.place "b", some "b")] := by
  exact ⟨EXP_005_reference, by decide⟩

/-! ### Non-vacuity: the acceptance criteria on the reference -/

/-- The test derivation and AC1, AC2 on the reference emitter: `XOR(AND(P_a, P_b), P_c)` has no
empty group and one `Xor` group; its xor junction 0 has two edges out, into the and junction 1
(no label of its own) and into `P_c` (labelled `P_c`); the places below the first are `P_a`,
`P_b` and below the second `P_c`. `XOR(P_a, Timeout(5, P_b))` labels its branches `P_a` and
`⏱5ms`, and with `P_a` a reset place the combined edge keeps a label, `reset+out` (EXP-013).
`XOR(ForwardInput(x → P_a), Timeout(5, ForwardInput(y → P_b)))` draws both branches dashed,
labelled `P_a ⟵x` and `⏱5ms ⟵y`. -/
@[evidence nonvacuous EXP_005]
theorem EXP_005_nonvacuous :
    (OutTree.toOut (.xor [.and [.place "P_a", .place "P_b"], .place "P_c"])).isSome = true ∧
    exp005XorGroups (.xor [.and [.place "P_a", .place "P_b"], .place "P_c"]) ≠ [] ∧
    ((exp005OutOf (refEmit "T" [] (.xor [.and [.place "P_a", .place "P_b"], .place "P_c"])).edges
        (.junction "T" .xor 0)).map fun e => (e.dst, e.label)) =
      [(.junction "T" .and 1, none), (.place "P_c", some "P_c")] ∧
    (let es := (refEmit "T" [] (.xor [.and [.place "P_a", .place "P_b"], .place "P_c"])).edges
     (exp005Below es es.length (.junction "T" .and 1), exp005Below es es.length (.place "P_c"))) =
      (["P_a", "P_b"], ["P_c"]) ∧
    ((exp005OutOf (refEmit "T" [] (.xor [.place "P_a", .timeout 5 (.place "P_b")])).edges
        (.junction "T" .xor 0)).map (·.label)) = [some "P_a", some "⏱5ms"] ∧
    ((exp005OutOf (refEmit "T" ["P_a"] (.xor [.place "P_a", .place "P_b"])).edges
        (.junction "T" .xor 0)).map (·.label)) = [some "reset+out", some "P_b"] ∧
    ((exp005OutOf (refEmit "T" []
        (.xor [.forward "x" "P_a", .timeout 5 (.forward "y" "P_b")])).edges
        (.junction "T" .xor 0)).map fun e => (e.dst, e.dashed, e.label)) =
      [(.place "P_a", true, some "P_a ⟵x"), (.place "P_b", true, some "⏱5ms ⟵y")] := by
  refine ⟨by decide, by simp [exp005XorGroups, exp005XorGroupsL], by decide, by decide, by decide,
    by decide, by decide⟩

end Libpetri.Spec
