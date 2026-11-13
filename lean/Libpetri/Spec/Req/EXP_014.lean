import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Reference.ExportCluster
import Libpetri.Spec.Text.EXP_014

set_option linter.missingDocs true

/-!
# EXP-014: Junction ID format and layout stability (`spec/09-export.md`)

The DOT IDs of the exported graph: every node's ID is a fixed function of what the node stands
for (`p_<s>`, `t_<s>`, `j_<s>__<kind>_<idx>`, with `<s>` the sanitised name), the junctions of a
transition are numbered in depth-first pre-order with one counter, the edges of the output side
use those numbers, no two nodes share an ID when the names of the net are ASCII and stay
distinct after sanitising, a junction never shares an ID with a place or a transition,
whatever the names, every junction node belongs to a transition of the net, and a junction node
is drawn with the category of its kind (`xor-junction`, `and-junction`).

The requirement is a predicate over an abstract `Exporter` (glossary `GlossaryExport.lean`),
not over an `Emitter`: an emitter's output carries no IDs, and the wiring is a property of the
drawn graph (export design, skeptic corrections S-2 and S-3). The witness is the reference
exporter `refExportWith S` for every cluster stage `S` (`EXP_014_any`), registered on
the clustered exporter `refExport`.

The name rules follow ruling D46 (a): the ID rule is stated for ASCII names, other characters
are implementation-defined (Rust keeps every Unicode letter and digit, TypeScript replaces per
UTF-16 code unit, Java per code point), and uniqueness assumes the sanitised names are pairwise
distinct. Guarantee 1 (a junction ID is no place or transition ID) holds for every name in all
three runtimes and is stated for every name. Ruling D60 (c) keeps the byte-equality guarantees as
kind Q.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## Block-local vocabulary -/

/-- The name a node reference carries: the place's name, the transition's name, or for a
junction the name of its transition. -/
def NodeRef.refName : NodeRef → String
  | .trans t => t
  | .junction t _ _ => t
  | .place p => p

/-- Whether a node reference is a junction (rather than a place or a transition). -/
def NodeRef.isJunction : NodeRef → Bool
  | .junction .. => true
  | _ => false

/-- **ASCII name** (ruling D46 (a)): every character of the name is an ASCII character. -/
def AsciiName (s : String) : Prop := ∀ c ∈ s.toList, c.toNat < 128

instance (s : String) : Decidable (AsciiName s) :=
  inferInstanceAs (Decidable (∀ c ∈ s.toList, c.toNat < 128))

/-- Every place name of `X` the exporter can draw: the declared places, then every place an arc
touches (with repetitions). -/
def ExportNet.allPlaceNames (X : ExportNet) : List String :=
  X.places ++ X.trans.flatMap ExportTrans.touched

/-- **The name assumption of EXP-014** (ruling D46 (a), kind A): the place names and the
transition names of `X` are ASCII, and no two place names, nor two transition names, become equal
when each character outside `[A-Za-z0-9_]` is replaced by `_`. -/
def ExportNet.IdNames (X : ExportNet) : Prop :=
  (∀ p ∈ X.allPlaceNames, AsciiName p) ∧ (∀ t ∈ X.trans, AsciiName t.name) ∧
  (∀ p ∈ X.allPlaceNames, ∀ q ∈ X.allPlaceNames, sanitize p = sanitize q → p = q) ∧
  (∀ t ∈ X.trans, ∀ u ∈ X.trans, sanitize t.name = sanitize u.name → t.name = u.name)

/-! ## EXP-014: Junction ID format and layout stability -/

requirement EXP_014
  id "EXP-014"
  title "Junction ID Format and Layout Stability"
  kind F
  scope "every exporter, the DOT IDs, the junction nodes and the junction numbering of the exported graph"
  source verbatim "spec/09-export.md"
  covers EXP_014.s1, EXP_014.s2, EXP_014.s3, EXP_014.s4, EXP_014.s5, EXP_014.s6, EXP_014.s7,
        EXP_014.s8, EXP_014.s9, EXP_014.s10, EXP_014.s11, EXP_014.s12, EXP_014.s13, EXP_014.s14,
        EXP_014.s15, EXP_014.s16
  reading "For every configuration cfg and net X, the graph E cfg X satisfies:"
          "every node whose name (the place's, the transition's, or for a junction its transition's) is ASCII has the ID nodeId of what it stands for: p_<sanitize p>, t_<sanitize t> or j_<sanitize t>__<kind>_<idx>, the index in decimal without leading zeros;"
          "on a net with pairwise distinct transition names, the junction nodes of each transition t, as (kind, index), are the kinds of the groups of t's output spec with two or more children in depth-first pre-order, numbered 0, 1, 2 in that order, one node per group and no other, in any order of drawing (List.Perm);"
          "on such a net, the output side of each transition t (its output and reset+output edges from t or a junction of t), as (source, target) pairs, is the drawing rule of EXP-012 for t's output spec with these junction numbers (Drawing, no renumbering), each pair as often as Drawing has it, in any order;"
          "every junction an edge starts or ends at is the reference of a node of the graph;"
          "on such a net whose names meet the name assumption (ExportNet.IdNames: ASCII place and transition names, pairwise distinct after sanitize), the node IDs are pairwise distinct;"
          "for every net, whatever its names, no junction node has the ID of a node that is not a junction (a place or a transition node);"
          "every junction node stands for a junction of a transition of X: some transition of X has the name the junction carries;"
          "and every junction node of kind k has the category of its kind, xor-junction for xor and and-junction for and (JKind.cat)."
  assumes "The model is an exporter E : Exporter (glossary): the typed graph (nodes with reference, ID, category and labels; edges; clusters) a configuration and a net are drawn as, before DOT text. The node references (place, transition, junction (t, kind, index)) are the graph's own data; this block constrains the IDs it gives them, the junction indices and kinds it uses, the transition a junction node belongs to, the category of a junction node and the ends of the output edges. Every other attribute of a node or edge is another block's subject (EXP-001 to EXP-013)."
          "The ID function is the glossary's nodeId over sanitize, which keeps an ASCII letter, digit or underscore and replaces every other character by an underscore, and writes the index with toString (decimal, no leading zeros). By ruling D46 (a) the first line binds only nodes whose name is ASCII: on other names the runtimes differ (Rust keeps every Unicode letter and digit, Java replaces per code point as the model does, TypeScript per UTF-16 code unit, so a character outside the basic plane becomes two underscores) and the spec leaves them implementation-defined, which is the plain sentence quoted after the first shall sentence."
          "The sixth line is guarantee 1 and the second shall sentence, for every name: all three runtimes keep the prefixes p_, t_ and j_ for every name, so a junction ID, which starts with j_, is no place or transition ID. Without it a mapper that writes non-ASCII names verbatim, without a prefix, meets every other line and gives the transition Ü and its junction one ID (EXP_014_forbids_rawNonAscii, exp014_rawNonAscii_rest). The reference meets it by EXP_014_guarantee1."
          "The second and third lines restate the numbering bullet and the third, fourth and fifth shall sentences: the junction nodes of a transition are one per group with two or more children, of that group's kind (and for And, xor for Xor, which the spec's example implies and the third shall sentence states), the index of a junction is the position of its group in the pre-order of those groups (OutTree.junctions, which skips a short group, so a collapsed group consumes no counter slot), and the output edges are exactly the edges of EXP-012's drawing rule wired to those indices, so an extra, missing or repeated output edge breaks the third line (EXP_014_forbids_dupOutEdge). EXP-012 compares junctions and edges only up to a one-to-one renumbering; these two lines fix the renumbering to the identity. Both lines read a transition by its name, so they are stated on nets with pairwise distinct transition names, which every net that builds has and which the shall sentences state as their condition; the input-arc half of X.Distinct (CORE-030) plays no part here."
          "The third line reads the output side by arc type: an output or reset+output edge from the transition or one of its junctions. An edge from a junction drawn with another arc type escapes it but not the fourth line, which still requires its junction end to be drawn; arc types are EXP-012's subject and the export agreement's (ExportAgrees)."
          "The fourth line is the sixth shall sentence: an edge whose end is a junction no node stands for would make Graphviz invent an unstyled node with a junction ID. Ghost edges (EXP-017) are included."
          "The seventh line is the shall sentence on junction nodes for a transition the net does not have, for every net. Lines 2 and 3 read the junctions of each transition of X by its name, so without the seventh line an exporter that adds a junction node for a name no transition of X has (a junction left over from an earlier export, say) meets lines 1 to 6 on every net and draws a junction on a net with no output spec at all (EXP_014_forbids_strayJunction, exp014_strayJunction_rest). With line 2 on nets with distinct transition names, and with the junction clause of the export agreement (ExportAgrees, glossary), it carries EXP-012's 'and no other junction node' from one output spec to the whole graph. All three mappers make a junction node only while walking the output spec of a transition of the net (emit_output in the Rust crate libpetri-export, emitOutput in PetriNetGraphMapper.java and petri-net-mapper.ts), as the reference does."
          "The eighth line is the shall sentence on the category of a junction node, and EXP-012's 'Style category xor-junction' and 'Style category and-junction' attributes: a junction node of kind k has the row JKind.cat k of the node table (Libpetri.Export.Styles, generated from spec/petri-net-styles.json). Java and TypeScript set the category from the kind (PetriNetGraphMapper.java, petri-net-mapper.ts); Rust draws the XOR_JUNCTION or AND_JUNCTION style by kind (mapper.rs), which is that row. An exporter that swaps the two rows violates it (EXP_014_forbids_junctionCatSwap). The other junction attributes (shape, glyph, size, font) are the table's constants and kind Q, as EXP-012 says."
          "The fifth line is the uniqueness shall sentence, the uniqueness that 'uniquely determined' claims, under the name assumption of ruling D46 (a) (kind A, ExportNet.IdNames, on a net with pairwise distinct transition names): ASCII names, and no two place names nor two transition names equal after sanitize. Without it two names such as b1/x and b1_x get one ID in every runtime. A place and a transition never share an ID (prefixes p_ and t_), and a junction ID is no place or transition ID (prefix j_) and determines its transition's sanitised name, kind and index (EXP_014_junctionId_inj, by reading the ID from its end: the index has no underscore, the kind word is three letters after a double underscore). Ruling D46 (a) also names non-empty names; uniqueness does not need that (an empty place name, an empty transition name and their junctions still get the IDs p_, t_ and j___<kind>_<idx>), so ExportNet.IdNames leaves it out and only AC1 is scoped to non-empty names. The assumption's 'no empty / segment' clause is EXP-016's and plays no part here."
          "The 'uniquely determined by the depth-first traversal' clause of the flat-counter paragraph is the second and third lines."
          "AC1 (all junction IDs match j_[A-Za-z0-9_]+__(xor|and)_[0-9]+) follows from the first line, for every exporter meeting EXP-014, for a junction of a transition whose name is non-empty and ASCII (EXP_014_ac1), which is what the last quoted plain sentence scopes AC1 to. An empty transition name builds in every runtime and gives j___xor_0, which the regex rejects; a non-ASCII name gives an implementation-defined ID, and Rust's j_é__xor_0 does not match the regex either."
          "Guarantee 2 and AC2 (two exports of one net are byte-equal) have no content over a Lean function, which is deterministic; across processes they fail today for Java and Rust (HashSet order, ruling R2 (exp-b)); kind Q. Guarantee 3 and AC3 (Java, TypeScript and Rust exports are byte-equal) are a property of three programs and kind Q by ruling D60 (c); the export corpus EP-2 replays the reference against the runtimes after the migration. The order of nodes and edges is not stated (List.Perm), only the numbering the spec pins."
          "The test derivation (export twice and diff; export in three languages and diff) is AC2 and AC3, kind Q. EXP_014_nonvacuous decides the spec's example AND(XOR(a,b), XOR(c,d)) on t Nested, a deeper tree that separates pre-order from breadth-first numbering, a collapsed group, sanitised place, transition and junction IDs, and a junction ID apart from the transition ID on a non-ASCII name, on the reference."
  signoff "2026-11-13 f1aaffb0ce9c4adf ai"
  statement : Exporter → Prop :=
    fun E => ∀ (cfg : ExportCfg) (X : ExportNet),
      (∀ n ∈ (E cfg X).nodes, AsciiName n.ref.refName → n.id = nodeId n.ref) ∧
      ((X.trans.map ExportTrans.name).Nodup → ∀ t ∈ X.trans,
        ((E cfg X).junctionsOf t.name).Perm ((t.out.map OutTree.junctions).getD []).zipIdx) ∧
      ((X.trans.map ExportTrans.name).Nodup → ∀ t ∈ X.trans,
        (((E cfg X).outEdges t.name).map fun e => (e.src, e.dst)).Perm
          (((t.out.map (Drawing t.name)).getD []).map fun d => (d.src, d.dst))) ∧
      (∀ e ∈ (E cfg X).edges, ∀ u k i, (e.src = .junction u k i ∨ e.dst = .junction u k i) →
        ∃ n ∈ (E cfg X).nodes, n.ref = .junction u k i) ∧
      ((X.trans.map ExportTrans.name).Nodup → X.IdNames → ((E cfg X).nodes.map XNode.id).Nodup) ∧
      (∀ n ∈ (E cfg X).nodes, ∀ m ∈ (E cfg X).nodes,
        n.ref.isJunction = true → m.ref.isJunction = false → n.id ≠ m.id) ∧
      (∀ n ∈ (E cfg X).nodes, ∀ u k i, n.ref = .junction u k i → ∃ t ∈ X.trans, t.name = u) ∧
      (∀ n ∈ (E cfg X).nodes, ∀ u k i, n.ref = .junction u k i → n.cat = k.cat)

/- The pinned readable form of EXP-014: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_014 : Exporter → Prop :=
fun E =>
  ∀ (cfg : ExportCfg) (X : ExportNet),
    (∀ n ∈ (E cfg X).nodes, AsciiName n.ref.refName → n.id = nodeId n.ref) ∧
      ((List.map ExportTrans.name X.trans).Nodup →
          ∀ t ∈ X.trans, ((E cfg X).junctionsOf t.name).Perm ((Option.map OutTree.junctions t.out).getD []).zipIdx) ∧
        ((List.map ExportTrans.name X.trans).Nodup →
            ∀ t ∈ X.trans,
              (List.map (fun e => (e.src, e.dst)) ((E cfg X).outEdges t.name)).Perm
                (List.map (fun d => (d.src, d.dst)) ((Option.map (Drawing t.name) t.out).getD []))) ∧
          (∀ e ∈ (E cfg X).edges,
              ∀ (u : String) (k : JKind) (i : ℕ),
                e.src = NodeRef.junction u k i ∨ e.dst = NodeRef.junction u k i →
                  ∃ n ∈ (E cfg X).nodes, n.ref = NodeRef.junction u k i) ∧
            ((List.map ExportTrans.name X.trans).Nodup → X.IdNames → (List.map XNode.id (E cfg X).nodes).Nodup) ∧
              (∀ n ∈ (E cfg X).nodes,
                  ∀ m ∈ (E cfg X).nodes, n.ref.isJunction = true → m.ref.isJunction = false → n.id ≠ m.id) ∧
                (∀ n ∈ (E cfg X).nodes,
                    ∀ (u : String) (k : JKind) (i : ℕ), n.ref = NodeRef.junction u k i → ∃ t ∈ X.trans, t.name = u) ∧
                  ∀ n ∈ (E cfg X).nodes,
                    ∀ (u : String) (k : JKind) (i : ℕ), n.ref = NodeRef.junction u k i → n.cat = k.cat
-/
#guard_msgs in #print EXP_014

/-! ### DOT IDs -/

/-- Split two lists at the first occurrence of a character neither prefix holds. -/
theorem exp014_split_char (c : Char) :
    ∀ (a b x y : List Char), c ∉ a → c ∉ x → a ++ c :: b = x ++ c :: y → a = x ∧ b = y
  | [], b, [], y, _, _, h => by simpa using h
  | [], b, z :: x, y, _, hx, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self ..) hx
  | z :: a, b, [], y, ha, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self ..) ha
  | z :: a, b, w :: x, y, ha, hx, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have := exp014_split_char c a b x y (fun h => ha (List.mem_cons_of_mem _ h))
      (fun h => hx (List.mem_cons_of_mem _ h)) h
    exact ⟨by rw [this.1], this.2⟩

/-- The kind word of a junction ID determines the kind. -/
theorem exp014_tag_inj {k k' : JKind} (h : k.tag.toList.reverse = k'.tag.toList.reverse) :
    k = k' := by
  cases k <;> cases k' <;> first | rfl | (revert h; decide)

/-- **A junction ID determines its transition's sanitised name, its kind and its index**: read
from its end, the index has no underscore and the kind word is three letters after a double
underscore, so the sanitised name may itself hold `__xor_` and the ID still reads back. -/
theorem EXP_014_junctionId_inj {t u : String} {k k' : JKind} {i i' : Nat}
    (h : nodeId (.junction t k i) = nodeId (.junction u k' i')) :
    sanitize t = sanitize u ∧ k = k' ∧ i = i' := by
  have h := congrArg (fun s => s.toList.reverse) h
  simp only [nodeId, String.toList_append, Nat.toString_eq_ofList_toDigits, String.toList_ofList,
    List.reverse_append] at h
  have hu : ("_" : String).toList = ['_'] := by decide
  have hu2 : ("__" : String).toList = ['_', '_'] := by decide
  rw [hu, hu2] at h
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h
  have hn : ∀ n : Nat, '_' ∉ (Nat.toDigits 10 n).reverse := fun n => by
    simp [Nat.underscore_not_in_toDigits]
  have hk : ∀ k : JKind, '_' ∉ k.tag.toList.reverse := fun k => by cases k <;> decide
  obtain ⟨hd, h⟩ := exp014_split_char '_' _ _ _ _ (hn i) (hn i') h
  obtain ⟨ht, h⟩ := exp014_split_char '_' _ _ _ _ (hk k) (hk k') h
  simp only [List.cons.injEq, true_and, List.append_cancel_right_eq, List.reverse_inj,
    String.toList_inj] at h
  refine ⟨h, exp014_tag_inj ht, ?_⟩
  rw [List.reverse_inj] at hd
  have := congrArg (fun l => Nat.ofDigitChars 10 l 0) hd
  simpa only [Nat.ofDigitChars_ten_toDigits] using this

/-! ### The reference -/

section Reference

variable {S : ClusterStage} {cfg : ExportCfg} {X : ExportNet}

/-- The node references the reference draws are pairwise distinct on a net with distinct
transition names. -/
theorem exp014_refNodeRefs_nodup (hX : (X.trans.map ExportTrans.name).Nodup) :
    (refNodeRefs X).Nodup := by
  have hj : ∀ t : ExportTrans,
      ((refEmit.ofTrans t).junctions.map fun j => NodeRef.junction t.name j.1 j.2).Nodup := by
    intro t
    refine List.Nodup.map (fun a b h => ?_) ?_
    · obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only [NodeRef.junction.injEq, true_and] at h
      rw [h.1, h.2]
    · rw [refEmit_ofTrans_junctions]
      refine List.Nodup.of_map Prod.snd ?_
      rw [List.zipIdx_map_snd]
      exact List.nodup_range' ..
  have hp : List.Pairwise (fun a b : ExportTrans => a.name ≠ b.name) X.trans :=
    List.pairwise_map.mp hX
  unfold refNodeRefs
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨refPlaceNames_nodup.map (fun a b h => NodeRef.place.inj h), ?_, ?_⟩, ?_, ?_⟩
  · have : X.trans.map (fun t => NodeRef.trans t.name) = (X.trans.map ExportTrans.name).map
        NodeRef.trans := by simp [Function.comp_def]
    rw [this]
    exact hX.map (fun a b h => NodeRef.trans.inj h)
  · simp
  · rw [List.nodup_flatMap]
    refine ⟨fun t _ => hj t, hp.imp fun {a b} hab => ?_⟩
    intro r ha hb
    simp only [List.mem_map] at ha hb
    obtain ⟨j, _, rfl⟩ := ha
    obtain ⟨j', _, h⟩ := hb
    simp only [NodeRef.junction.injEq] at h
    exact hab h.1.symm
  · intro a ha b hb
    simp only [List.mem_append, List.mem_map] at ha
    rcases ha with ⟨p, _, rfl⟩ | ⟨u, _, rfl⟩
    all_goals
      simp only [List.mem_flatMap, List.mem_map] at hb
      obtain ⟨_, _, _, _, rfl⟩ := hb
      exact nofun

/-- Under the name assumption, the node IDs of the references the reference draws are pairwise
distinct: `nodeId` is one to one on them. -/
theorem exp014_nodeId_inj (hN : X.IdNames) {r r' : NodeRef} (hr : r ∈ refNodeRefs X)
    (hr' : r' ∈ refNodeRefs X) (h : nodeId r = nodeId r') : r = r' := by
  obtain ⟨-, -, hP, hT⟩ := hN
  simp only [refNodeRefs, List.mem_append, List.mem_map, List.mem_flatMap] at hr hr'
  rcases hr with (⟨p, hp, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, ⟨k, i⟩, -, rfl⟩ <;>
    rcases hr' with (⟨q, hq, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨u, hu, ⟨k', i'⟩, -, rfl⟩
  · rw [hP p (List.mem_dedup.mp hp) q (List.mem_dedup.mp hq) ((nodeId_place_inj p q).mp h)]
  · exact absurd h (nodeId_place_ne_trans _ _)
  · exact absurd h.symm (nodeId_junction_ne_place _ _ _ _)
  · exact absurd h.symm (nodeId_place_ne_trans _ _)
  · rw [hT t ht u hu ((nodeId_trans_inj _ _).mp h)]
  · exact absurd h.symm (nodeId_junction_ne_trans _ _ _ _)
  · exact absurd h (nodeId_junction_ne_place _ _ _ _)
  · exact absurd h (nodeId_junction_ne_trans _ _ _ _)
  · obtain ⟨hs, rfl, rfl⟩ := EXP_014_junctionId_inj h
    rw [hT t ht u hu hs]

/-- **Guarantee 1 on the reference**: whatever the cluster stage, configuration and net, the ID of
a junction node is the ID of no place node and no transition node. -/
@[evidence cites "EXP-014" "guarantee 1: junction IDs do not collide with place IDs (p_…) or transition IDs (t_…), on the reference exporter for every cluster stage, configuration and net, whatever the names"]
theorem EXP_014_guarantee1 (S : ClusterStage) (cfg : ExportCfg) (X : ExportNet) :
    ∀ n ∈ (refExportWith S cfg X).nodes, ∀ m ∈ (refExportWith S cfg X).nodes,
      n.ref.isJunction = true → m.ref.isJunction = false → n.id ≠ m.id := by
  intro n hn m hm hnj hmj
  rw [refNodes_id hn, refNodes_id hm]
  cases hnr : n.ref with
  | junction t k i =>
    cases hmr : m.ref with
    | place p => exact nodeId_junction_ne_place _ _ _ _
    | trans u => exact nodeId_junction_ne_trans _ _ _ _
    | junction => simp [hmr, NodeRef.isJunction] at hmj
  | trans => simp [hnr, NodeRef.isJunction] at hnj
  | place => simp [hnr, NodeRef.isJunction] at hnj

/-- **The reference exporter meets EXP-014 whatever its cluster stage**: IDs by `refNodes_id`,
the numbering by `refExportWith_junctionsOf` and `refEmit_ofTrans_junctions`, the wiring by
`refExportWith_outEdges` and `refEmit_draws`, the junction ends of every edge by
`refEmit_ofTrans_ends` and the stage's `ghosts_ends`, unique IDs by
`exp014_refNodeRefs_nodup` and `exp014_nodeId_inj`, guarantee 1 by `EXP_014_guarantee1`, and the
owner and category of a junction node by `refJunctionNode`, drawn only for the transitions of the
net. -/
theorem EXP_014_any (S : ClusterStage) : EXP_014 (refExportWith S) := by
  intro cfg X
  refine ⟨?_, ?_, ?_, ?_, ?_, EXP_014_guarantee1 S cfg X, ?_, ?_⟩
  · intro n hn _
    exact refNodes_id hn
  · intro hX t ht
    rw [refExportWith_junctionsOf hX ht, refEmit_ofTrans_junctions]
  · intro hX t ht
    rw [refExportWith_outEdges hX ht]
    cases ho : t.out with
    | none => simp [Emitter.ofTrans_none refEmit ho]
    | some o =>
      rw [Emitter.ofTrans_some refEmit ho, refEmit_draws]
      simp [Function.comp_def]
  · intro e he u k i hj
    rcases refExportWith_edge he with ⟨t, ht, het⟩ | ⟨-, hs, hd⟩
    · rcases mem_refTransEdges.mp het with
        ⟨s, _, rfl⟩ | hem | ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ | ⟨p, _, _, rfl⟩
      · simp [refInputEdge] at hj
      · have hends := refEmit_ofTrans_ends hem
        have hnode : ∀ k' i', (k', i') ∈ (refEmit.ofTrans t).junctions →
            NodeRef.junction u k i = .junction t.name k' i' →
            ∃ n ∈ (refExportWith S cfg X).nodes, n.ref = .junction u k i := by
          intro k' i' hm heq
          refine ⟨refJunctionNode t.name (k', i'), ?_, ?_⟩
          · exact mem_refNodes.mpr (Or.inr (Or.inr ⟨t, ht, (k', i'), hm, rfl⟩))
          · rw [heq]; rfl
        rcases hj with hj | hj
        · rcases hends.1 with h | ⟨k', i', h, hm⟩
          · rw [hj] at h; cases h
          · exact hnode k' i' hm (hj.symm.trans h)
        · rcases hends.2 with ⟨p, h⟩ | ⟨k', i', h, hm⟩
          · rw [hj] at h; cases h
          · exact hnode k' i' hm (hj.symm.trans h)
      · simp [refInhibitorEdge] at hj
      · simp [refReadEdge] at hj
      · simp [refResetEdge] at hj
    · have hr : NodeRef.junction u k i ∈ refNodeRefs X := by
        rcases hj with hj | hj
        · exact hj ▸ hs
        · exact hj ▸ hd
      exact (mem_refNodeRefs (cfg := cfg)).mp hr
  · intro hX hN
    have hid : (refExportWith S cfg X).nodes.map XNode.id =
        (refNodeRefs X).map nodeId := by
      rw [refExportWith_nodes, ← refNodes_refs (cfg := cfg), List.map_map]
      exact List.map_congr_left fun n hn => refNodes_id hn
    rw [hid]
    exact (exp014_refNodeRefs_nodup hX).map_on fun r hr r' hr' h => exp014_nodeId_inj hN hr hr' h
  · intro n hn u k i hr
    rcases mem_refNodes.mp hn with ⟨p, _, rfl⟩ | ⟨t, _, rfl⟩ | ⟨t, ht, j, _, rfl⟩
    · simp [refPlaceNode] at hr
    · simp [refTransNode] at hr
    · simp only [refJunctionNode, NodeRef.junction.injEq] at hr
      exact ⟨t, ht, hr.1⟩
  · intro n hn u k i hr
    rcases mem_refNodes.mp hn with ⟨p, _, rfl⟩ | ⟨t, _, rfl⟩ | ⟨t, _, j, _, rfl⟩
    · simp [refPlaceNode] at hr
    · simp [refTransNode] at hr
    · simp only [refJunctionNode, NodeRef.junction.injEq] at hr ⊢
      rw [hr.2.1]

end Reference

/-- The clustered reference exporter `refExport` (the witness of the export consistency theorem)
meets EXP-014 (`EXP_014_any` at the reference cluster stage). -/
@[evidence holds EXP_014]
theorem EXP_014_reference : EXP_014 refExport := EXP_014_any _


/-! ### Wrong exporters, one per line -/

/-- The reference with every junction index renamed by `f`, in the nodes (reference and ID
alike) and in the edge ends: a mapper with another numbering, wired and named consistently. -/
def exp014Renum (f : Nat → Nat) : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with
    nodes := g.nodes.map fun n => { n with ref := n.ref.renJ f, id := nodeId (n.ref.renJ f) },
    edges := g.edges.map fun e => { e with src := e.src.renJ f, dst := e.dst.renJ f } }

/-- The index renaming that swaps `a` and `b`. -/
def exp014Swap (a b i : Nat) : Nat := if i = a then b else if i = b then a else i

/-- A net of one transition `T`, with an input arc on `in` and output spec `o`. -/
def exp014Net (o : OutTree) : ExportNet :=
  { trans := [{ core := ⟨"T", [⟨"in", .one⟩], [], [], []⟩, out := some o }] }

/-- A one-transition net has pairwise distinct transition names. -/
theorem exp014Net_names (o : OutTree) : ((exp014Net o).trans.map ExportTrans.name).Nodup := by
  simp [exp014Net]

/-- Post-order numbering: on `AND(XOR(a, b), c)` the junction of the `Xor` group gets 0 and that
of the `And` group 1 (the index renaming that swaps 0 and 1). -/
def exp014_postOrder : Exporter := exp014Renum (exp014Swap 0 1)

/-- ✗ Post-order numbering violates EXP-014 on `AND(XOR(a, b), c)` (line 2: the `And` group comes
first in pre-order, so junction 0 is an and junction). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_postOrder : ¬ EXP_014 exp014_postOrder := by
  intro h
  have := (h {} (exp014Net (.and [.xor [.place "a", .place "b"], .place "c"]))).2.1
    (exp014Net_names _) _ (.head _)
  revert this
  decide

/-- A collapsed single-child group that consumes a counter slot: on `AND(XOR(a), XOR(b, c))` the
junction of `XOR(b, c)` gets 2 (every index after 0 moved up by one). -/
def exp014_collapsedCounts : Exporter := exp014Renum fun i => if i = 0 then 0 else i + 1

/-- ✗ A collapsed group that consumes a counter slot violates EXP-014 on `AND(XOR(a), XOR(b, c))`
(line 2: the junction of `XOR(b, c)` is number 1). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_collapsedCounts : ¬ EXP_014 exp014_collapsedCounts := by
  intro h
  have := (h {} (exp014Net (.and [.xor [.place "a"], .xor [.place "b", .place "c"]]))).2.1
    (exp014Net_names _) _ (.head _)
  revert this
  decide

/-- Breadth-first numbering: on `AND(XOR(AND(a, b), c), XOR(d, e))` the two `Xor` groups get 1
and 2 and the inner `And` group 3 (the renaming that swaps 2 and 3). The spec's own example
`AND(XOR(a,b), XOR(c,d))` does not separate breadth-first from pre-order. -/
def exp014_breadthFirst : Exporter := exp014Renum (exp014Swap 2 3)

/-- ✗ Breadth-first numbering violates EXP-014 on `AND(XOR(AND(a, b), c), XOR(d, e))` (line 2:
in pre-order the inner `And` group is number 2). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_breadthFirst : ¬ EXP_014 exp014_breadthFirst := by
  intro h
  have := (h {} (exp014Net (.and [.xor [.and [.place "a", .place "b"], .place "c"],
    .xor [.place "d", .place "e"]]))).2.1 (exp014Net_names _) _ (.head _)
  revert this
  decide

/-- Two junctions of one kind swapped: on `XOR(XOR(a, b), XOR(c, d))` the junction of
`XOR(c, d)` gets 1 and that of `XOR(a, b)` 2. The junction nodes are still xor 0, 1 and 2, so the
numbering line does not see it (`exp014_sameKindSwap_junctions`). -/
def exp014_sameKindSwap : Exporter := exp014Renum (exp014Swap 1 2)

/-- The same-kind swap draws the junction nodes of pre-order numbering: only the wiring tells. -/
theorem exp014_sameKindSwap_junctions :
    ((exp014_sameKindSwap {} (exp014Net (.xor [.xor [.place "a", .place "b"],
      .xor [.place "c", .place "d"]]))).junctionsOf "T").Perm [(.xor, 0), (.xor, 1), (.xor, 2)] := by
  decide

/-- ✗ Swapping two junctions of one kind violates EXP-014 on `XOR(XOR(a, b), XOR(c, d))` (line 3:
the edges into `a` and `b` leave junction 1, the junction of the first inner group in
pre-order). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_sameKindSwap : ¬ EXP_014 exp014_sameKindSwap := by
  intro h
  have := (h {} (exp014Net (.xor [.xor [.place "a", .place "b"],
    .xor [.place "c", .place "d"]]))).2.2.1 (exp014Net_names _) _ (.head _)
  revert this
  decide

/-- Every edge end at a junction moved to index 0, the junction nodes kept (the design's
`badWiring`). -/
def exp014_badWiring : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with edges := g.edges.map fun e =>
      { e with src := e.src.renJ fun _ => 0, dst := e.dst.renJ fun _ => 0 } }

/-- ✗ Wiring every edge to index 0 violates EXP-014 on `AND(XOR(a, b), c)` (line 4: the edge
from the and junction into the xor junction ends at `j_T__xor_0`, which no node stands for). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_badWiring : ¬ EXP_014 exp014_badWiring := by
  intro h
  have := (h {} (exp014Net (.and [.xor [.place "a", .place "b"], .place "c"]))).2.2.2.1
    _ (List.getElem_mem (l := (exp014_badWiring {} (exp014Net (.and [.xor [.place "a",
      .place "b"], .place "c"]))).edges) (n := 2) (by decide)) "T" .xor 0 (Or.inr (by decide))
  revert this
  decide

/-- A sanitize that keeps `/`, as an ID rule that only replaces spaces and dots would. -/
def exp014SanitizeSlash (s : String) : String :=
  String.ofList (s.toList.map fun c => if c = '/' then c else sanitizeChar c)

/-- The node IDs with `exp014SanitizeSlash` in place of `sanitize`. -/
def exp014IdSlash : NodeRef → String
  | .place p => "p_" ++ exp014SanitizeSlash p
  | .trans t => "t_" ++ exp014SanitizeSlash t
  | .junction t k i => "j_" ++ exp014SanitizeSlash t ++ "__" ++ k.tag ++ "_" ++ toString i

/-- The reference with node IDs that keep `/`. -/
def exp014_keepSlash : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with nodes := g.nodes.map fun n => { n with id := exp014IdSlash n.ref } }

/-- ✗ Keeping `/` in IDs violates EXP-014 on a net declaring the place `b1/x` (line 1: its ID is
`p_b1_x`). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_keepSlash : ¬ EXP_014 exp014_keepSlash := by
  intro h
  exact absurd (h {} { places := ["b1/x"] }).1 (by decide)

/-- Place nodes drawn for every place occurrence, without removing repetitions. -/
def exp014_noDedup : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with nodes := X.allPlaceNames.map (refPlaceNode cfg X) ++ X.trans.map (refTransNode cfg) ++
      X.trans.flatMap refJunctionNodes }

/-- The net of `T` with an input arc on `a` and output spec `Place(a)`. -/
def exp014LoopNet : ExportNet :=
  { trans := [{ core := ⟨"T", [⟨"a", .one⟩], [], [], []⟩, out := some (.place "a") }] }

/-- ✗ Not removing repeated place names violates EXP-014 on a transition that takes from and
gives to `a` (line 5: two nodes with ID `p_a`). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_noDedup : ¬ EXP_014 exp014_noDedup := by
  intro h
  have hD : (exp014LoopNet.trans.map ExportTrans.name).Nodup := by
    unfold exp014LoopNet
    decide
  have hN : exp014LoopNet.IdNames := by
    unfold ExportNet.IdNames ExportNet.allPlaceNames exp014LoopNet
    decide
  exact absurd ((h {} exp014LoopNet).2.2.2.2.1 hD hN) (by decide)

/-- The reference with each junction's kind word swapped (`and` for `Xor`, `xor` for `And`), in
the nodes (reference and ID alike) and in the edge ends: a mapper that names a group's junction by
the wrong kind, consistently. -/
def exp014FlipKind : JKind → JKind
  | .xor => .and
  | .and => .xor

/-- A node reference with the kind of a junction swapped by `exp014FlipKind`. -/
def exp014FlipRef : NodeRef → NodeRef
  | .junction t k i => .junction t (exp014FlipKind k) i
  | r => r

/-- The reference with every junction's kind swapped, wired and named consistently. -/
def exp014_kindFlip : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with
    nodes := g.nodes.map fun n =>
      { n with ref := exp014FlipRef n.ref, id := nodeId (exp014FlipRef n.ref) },
    edges := g.edges.map fun e => { e with src := exp014FlipRef e.src, dst := exp014FlipRef e.dst } }

/-- ✗ Naming a junction by the wrong kind violates EXP-014 on `XOR(a, b)` (line 2: the junction of
the `Xor` group is an xor junction). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_kindFlip : ¬ EXP_014 exp014_kindFlip := by
  intro h
  have := (h {} (exp014Net (.xor [.place "a", .place "b"]))).2.1 (exp014Net_names _) _ (.head _)
  revert this
  decide

/-- The reference with every edge drawn twice: the junction nodes and the ends are right, the
output side has each edge once too often. -/
def exp014_dupOutEdge : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with edges := g.edges ++ g.edges }

/-- ✗ Drawing an output edge twice violates EXP-014 on `XOR(a, b)` (line 3: the output side of `T`
holds each edge of the drawing rule exactly once). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_dupOutEdge : ¬ EXP_014 exp014_dupOutEdge := by
  intro h
  have := (h {} (exp014Net (.xor [.place "a", .place "b"]))).2.2.1 (exp014Net_names _) _ (.head _)
  revert this
  decide

/-- The reference with a leading zero in every junction index (`j_T__xor_00`). -/
def exp014_padIdx : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with nodes := g.nodes.map fun n => { n with id := match n.ref with
      | .junction t k i => "j_" ++ sanitize t ++ "__" ++ k.tag ++ "_0" ++ toString i
      | _ => n.id } }

/-- ✗ A leading zero in a junction index violates EXP-014 on `XOR(a, b)` (line 1: the index is
written in decimal without leading zeros, `j_T__xor_0`). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_padIdx : ¬ EXP_014 exp014_padIdx := by
  intro h
  exact absurd (h {} (exp014Net (.xor [.place "a", .place "b"]))).1 (by decide)

/-- A net with a non-ASCII transition name: transition `Ü` with an input arc on `in` and output
spec `XOR(a, b)`. -/
def exp014UNet : ExportNet :=
  { trans := [{ core := ⟨"Ü", [⟨"in", .one⟩], [], [], []⟩,
                out := some (.xor [.place "a", .place "b"]) }] }

/-- The reference with every node whose name is not ASCII given that name verbatim as its ID,
without a prefix: a mapper that writes non-ASCII names as quoted DOT IDs. -/
def exp014_rawNonAscii : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with nodes := g.nodes.map fun n =>
      { n with id := if AsciiName n.ref.refName then n.id else n.ref.refName } }

/-- ✗ Writing non-ASCII names verbatim violates EXP-014 on the transition `Ü` with output
`XOR(a, b)` (line 6: the transition node and its junction node both get the ID `Ü`). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_rawNonAscii : ¬ EXP_014 exp014_rawNonAscii := by
  intro h
  have := (h {} exp014UNet).2.2.2.2.2.1
  revert this
  decide

/-- Every node the reference draws on a net meeting the name assumption has an ASCII name. -/
theorem exp014_ref_ascii {cfg : ExportCfg} {X : ExportNet} (hN : X.IdNames) :
    ∀ m ∈ (refExportFlat cfg X).nodes, AsciiName m.ref.refName := by
  intro m hm
  rcases mem_refNodes.mp hm with ⟨p, hp, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, j, -, rfl⟩
  · exact hN.1 p (by simpa [refPlaceNames, ExportNet.allPlaceNames] using hp)
  · exact hN.2.1 t ht
  · exact hN.2.1 t ht

/-- **Only the sixth line sees the verbatim mapper**: it meets every other line of EXP-014 on
every configuration and net, since lines 1 and 5 bind ASCII names only and lines 2 to 4, 7 and 8
read node references and categories, never IDs. -/
theorem exp014_rawNonAscii_rest (cfg : ExportCfg) (X : ExportNet) :
    let g := exp014_rawNonAscii cfg X
    (∀ n ∈ g.nodes, AsciiName n.ref.refName → n.id = nodeId n.ref) ∧
    ((X.trans.map ExportTrans.name).Nodup → ∀ t ∈ X.trans,
      (g.junctionsOf t.name).Perm ((t.out.map OutTree.junctions).getD []).zipIdx) ∧
    ((X.trans.map ExportTrans.name).Nodup → ∀ t ∈ X.trans,
      ((g.outEdges t.name).map fun e => (e.src, e.dst)).Perm
        (((t.out.map (Drawing t.name)).getD []).map fun d => (d.src, d.dst))) ∧
    (∀ e ∈ g.edges, ∀ u k i, (e.src = .junction u k i ∨ e.dst = .junction u k i) →
      ∃ n ∈ g.nodes, n.ref = .junction u k i) ∧
    ((X.trans.map ExportTrans.name).Nodup → X.IdNames → (g.nodes.map XNode.id).Nodup) ∧
    (∀ n ∈ g.nodes, ∀ u k i, n.ref = .junction u k i → ∃ t ∈ X.trans, t.name = u) ∧
    (∀ n ∈ g.nodes, ∀ u k i, n.ref = .junction u k i → n.cat = k.cat) := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8⟩ := (EXP_014_any _ : EXP_014 refExportFlat) cfg X
  refine ⟨?_, ?_, h3, ?_, ?_, ?_, ?_⟩
  · intro n hn ha
    simp only [exp014_rawNonAscii, List.mem_map] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    simp only at ha ⊢
    rw [if_pos ha]
    exact h1 m hm ha
  · intro hX t ht
    have : (exp014_rawNonAscii cfg X).junctionsOf t.name =
        (refExportFlat cfg X).junctionsOf t.name := by
      simp [exp014_rawNonAscii, XGraph.junctionsOf, List.filterMap_map]
    rw [this]
    exact h2 hX t ht
  · intro e he u k i hj
    obtain ⟨n, hn, hr⟩ := h4 e he u k i hj
    exact ⟨_, List.mem_map_of_mem hn, hr⟩
  · intro hX hN
    have heq : (exp014_rawNonAscii cfg X).nodes.map XNode.id =
        (refExportFlat cfg X).nodes.map XNode.id := by
      simp only [exp014_rawNonAscii, List.map_map]
      apply List.map_congr_left
      intro m hm
      simp [exp014_ref_ascii hN m hm]
    rw [heq]
    exact h5 hX hN
  · intro n hn u k i hr
    simp only [exp014_rawNonAscii, List.mem_map] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    exact h7 m hm u k i hr
  · intro n hn u k i hr
    simp only [exp014_rawNonAscii, List.mem_map] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    exact h8 m hm u k i hr

/-- Concatenation of a list of strings. -/
def exp014Big (L : List String) : String := L.foldr (· ++ ·) ""

/-- Every string of `L` is at most as long as their concatenation. -/
theorem exp014_le_big : ∀ (L : List String), ∀ x ∈ L, x.length ≤ (exp014Big L).length
  | [], x, hx => by cases hx
  | y :: L, x, hx => by
    simp only [exp014Big, List.foldr_cons, String.length_append]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := exp014_le_big L x hx
      simp only [exp014Big] at this
      omega

/-- A string longer than every string of `L`, holding the non-ASCII `é`. -/
def exp014Fresh (L : List String) : String := exp014Big L ++ "é"

/-- `exp014Fresh L` is no string of `L`. -/
theorem exp014_fresh_ne (L : List String) : ∀ x ∈ L, x ≠ exp014Fresh L := by
  intro x hx h
  have h1 := exp014_le_big L x hx
  have h2 : (exp014Fresh L).length = (exp014Big L).length + 1 := by
    have he : "é".length = 1 := by decide
    simp [exp014Fresh, String.length_append, he]
  rw [h] at h1
  omega

/-- `exp014Fresh L` is not an ASCII name. -/
theorem exp014_fresh_not_ascii (L : List String) : ¬ AsciiName (exp014Fresh L) := by
  intro h
  have : 'é' ∈ (exp014Fresh L).toList := by simp [exp014Fresh, String.toList_append]
  have := h _ this
  revert this
  decide

/-- A stray junction node: an xor junction, numbered 0, of a name no transition of `X` has, with
an ID no node of `g` has. -/
def exp014StrayNode (X : ExportNet) (g : XGraph) : XNode :=
  ⟨.junction (exp014Fresh (X.trans.map ExportTrans.name)) .xor 0,
   exp014Fresh (g.nodes.map XNode.id), JKind.xor.cat, JKind.xor.glyph, none⟩

/-- The clustered reference with one stray junction node added: a mapper whose junction left over
from an earlier export (a leaked or static mapper context) reaches the next graph. -/
def exp014_strayJunction : Exporter := fun cfg X =>
  let g := refExport cfg X
  { g with nodes := g.nodes ++ [exp014StrayNode X g] }

/-- The stray node is no junction of a transition of the net. -/
theorem exp014_stray_junctionsOf (cfg : ExportCfg) (X : ExportNet) (t : ExportTrans)
    (ht : t ∈ X.trans) :
    (exp014_strayJunction cfg X).junctionsOf t.name = (refExport cfg X).junctionsOf t.name := by
  have hne : t.name ≠ exp014Fresh (X.trans.map ExportTrans.name) :=
    exp014_fresh_ne _ _ (List.mem_map_of_mem ht)
  simp only [exp014_strayJunction, XGraph.junctionsOf, List.filterMap_append]
  have : (exp014StrayNode X (refExport cfg X)).ref.junctionOf t.name = none := by
    simp only [exp014StrayNode, NodeRef.junctionOf]
    rw [if_neg (Ne.symm hne)]
  simp [this]

/-- **Only the seventh line sees the stray junction**: the mutant meets every other line of
EXP-014 on every configuration and net, since lines 2 and 3 read the junctions of the net's own
transitions, line 4 the junctions edges touch, lines 1 and 5 bind ASCII names and the stray ID is
fresh, and the stray node has the xor row. -/
theorem exp014_strayJunction_rest (cfg : ExportCfg) (X : ExportNet) :
    let g := exp014_strayJunction cfg X
    (∀ n ∈ g.nodes, AsciiName n.ref.refName → n.id = nodeId n.ref) ∧
    ((X.trans.map ExportTrans.name).Nodup → ∀ t ∈ X.trans,
      (g.junctionsOf t.name).Perm ((t.out.map OutTree.junctions).getD []).zipIdx) ∧
    ((X.trans.map ExportTrans.name).Nodup → ∀ t ∈ X.trans,
      ((g.outEdges t.name).map fun e => (e.src, e.dst)).Perm
        (((t.out.map (Drawing t.name)).getD []).map fun d => (d.src, d.dst))) ∧
    (∀ e ∈ g.edges, ∀ u k i, (e.src = .junction u k i ∨ e.dst = .junction u k i) →
      ∃ n ∈ g.nodes, n.ref = .junction u k i) ∧
    ((X.trans.map ExportTrans.name).Nodup → X.IdNames → (g.nodes.map XNode.id).Nodup) ∧
    (∀ n ∈ g.nodes, ∀ m ∈ g.nodes,
      n.ref.isJunction = true → m.ref.isJunction = false → n.id ≠ m.id) ∧
    (∀ n ∈ g.nodes, ∀ u k i, n.ref = .junction u k i → n.cat = k.cat) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := EXP_014_reference cfg X
  have hmem : ∀ n, n ∈ (exp014_strayJunction cfg X).nodes ↔
      n ∈ (refExport cfg X).nodes ∨ n = exp014StrayNode X (refExport cfg X) := by
    intro n
    simp [exp014_strayJunction]
  have hfresh : ∀ m ∈ (refExport cfg X).nodes, m.id ≠ (exp014StrayNode X (refExport cfg X)).id :=
    fun m hm => exp014_fresh_ne _ _ (List.mem_map_of_mem hm)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn ha
    rcases (hmem n).mp hn with hn | rfl
    · exact h1 n hn ha
    · exact absurd ha (exp014_fresh_not_ascii _)
  · intro hX t ht
    rw [exp014_stray_junctionsOf cfg X t ht]
    exact h2 hX t ht
  · intro hX t ht
    exact h3 hX t ht
  · intro e he u k i hj
    obtain ⟨n, hn, hr⟩ := h4 e he u k i hj
    exact ⟨n, (hmem n).mpr (Or.inl hn), hr⟩
  · intro hX hN
    have := h5 hX hN
    simp only [exp014_strayJunction, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨this, List.nodup_singleton _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ha
    exact hfresh m hm
  · intro n hn m hm hnj hmj
    rcases (hmem n).mp hn with hn | rfl <;> rcases (hmem m).mp hm with hm | rfl
    · exact h6 n hn m hm hnj hmj
    · simp [exp014StrayNode, NodeRef.isJunction] at hmj
    · exact (hfresh m hm).symm
    · simp [exp014StrayNode, NodeRef.isJunction] at hmj
  · intro n hn u k i hr
    rcases (hmem n).mp hn with hn | rfl
    · exact h8 n hn u k i hr
    · simp only [exp014StrayNode, NodeRef.junction.injEq] at hr ⊢
      rw [← hr.2.1]

/-- ✗ A junction node for a name no transition of the net has violates EXP-014 on the empty net
(line 7: the mutant draws a junction there, although the net has no transition and no output
spec). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_strayJunction : ¬ EXP_014 exp014_strayJunction := by
  intro h
  obtain ⟨t, ht, -⟩ := (h {} {}).2.2.2.2.2.2.1 (exp014StrayNode {} (refExport {} {}))
    (by simp [exp014_strayJunction]) _ .xor 0 rfl
  simp at ht

/-- The reference with the rows of the two junction kinds swapped: an xor junction drawn with
the `and-junction` row and an and junction with the `xor-junction` row. -/
def exp014_junctionCatSwap : Exporter := fun cfg X =>
  let g := refExportFlat cfg X
  { g with nodes := g.nodes.map fun n => match n.ref with
      | .junction _ k _ => { n with cat := (exp014FlipKind k).cat }
      | _ => n }

/-- ✗ Drawing an xor junction with the `and-junction` row violates EXP-014 on `XOR(a, b)` (line 8:
the junction node of the `Xor` group has the `xor-junction` row). -/
@[evidence forbids EXP_014]
theorem EXP_014_forbids_junctionCatSwap : ¬ EXP_014 exp014_junctionCatSwap := by
  intro h
  have := (h {} (exp014Net (.xor [.place "a", .place "b"]))).2.2.2.2.2.2.2
    { refJunctionNode "T" (.xor, 0) with cat := .andJunction } (by decide) "T" .xor 0 rfl
  revert this
  decide

/-! ### Non-vacuity and the acceptance criteria -/

/-- The spec's example net: transition `Nested` with output `AND(XOR(a,b), XOR(c,d))`. -/
def exp014NestedNet : ExportNet :=
  { trans := [{ core := ⟨"Nested", [], [], [], []⟩,
                out := some (.and [.xor [.place "a", .place "b"], .xor [.place "c", .place "d"]]) }] }

/-- A net whose names need sanitising: transition `my-t.x` with input `b1/x` and output
`XOR(a/b, c)`. -/
def exp014SanNet : ExportNet :=
  { trans := [{ core := ⟨"my-t.x", [⟨"b1/x", .one⟩], [], [], []⟩,
                out := some (.xor [.place "a/b", .place "c"]) }] }

/-- The IDs of a graph's junction nodes, in the order drawn. -/
def exp014JunctionIds (g : XGraph) : List String :=
  g.nodes.filterMap fun n => match n.ref with
    | .junction .. => some n.id
    | _ => none

/-- The spec's example and the junction numbering on the reference: `AND(XOR(a,b), XOR(c,d))` of
`Nested` gives `j_Nested__and_0`, `j_Nested__xor_1`, `j_Nested__xor_2`;
`AND(XOR(AND(a, b), c), XOR(d, e))` gives `and_0`, `xor_1`, `and_2`, `xor_3` (pre-order, not
breadth-first); the collapsed `XOR(a)` of `AND(XOR(a), XOR(b, c))` takes no slot; on a
transition `my-t.x` with input `b1/x` and output `XOR(a/b, c)` every ID is sanitised and the
output edges are wired to `j_my_t_x__xor_0`; and on the non-ASCII transition `Ü` the transition
and its junction keep their prefixes, `t__` and `j____xor_0`. -/
@[evidence nonvacuous EXP_014]
theorem EXP_014_nonvacuous :
    exp014JunctionIds (refExportFlat {} exp014NestedNet) =
      ["j_Nested__and_0", "j_Nested__xor_1", "j_Nested__xor_2"] ∧
    exp014JunctionIds (refExportFlat {} (exp014Net (.and [.xor [.and [.place "a", .place "b"],
        .place "c"], .xor [.place "d", .place "e"]]))) =
      ["j_T__and_0", "j_T__xor_1", "j_T__and_2", "j_T__xor_3"] ∧
    exp014JunctionIds (refExportFlat {} (exp014Net (.and [.xor [.place "a"],
        .xor [.place "b", .place "c"]]))) = ["j_T__and_0", "j_T__xor_1"] ∧
    (refExportFlat {} exp014SanNet).nodes.map XNode.id =
      ["p_b1_x", "p_a_b", "p_c", "t_my_t_x", "j_my_t_x__xor_0"] ∧
    (refExportFlat {} exp014SanNet).edges.map
        (fun e => (nodeId e.src, nodeId e.dst)) =
      [("p_b1_x", "t_my_t_x"), ("t_my_t_x", "j_my_t_x__xor_0"), ("j_my_t_x__xor_0", "p_a_b"),
       ("j_my_t_x__xor_0", "p_c")] ∧
    (refExportFlat {} exp014UNet).nodes.map XNode.id =
      ["p_in", "p_a", "p_b", "t__", "j____xor_0"] := by
  decide

/-- A character AC1's regex allows in the name part: an ASCII letter or digit, or `_`. -/
def exp014IdChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- **AC1's regex** `j_[A-Za-z0-9_]+__(xor|and)_[0-9]+`, as a predicate on a string: `j_`, a
non-empty name part of letters, digits and underscores, `__`, the kind word, `_`, and a non-empty
run of digits. -/
def exp014JunctionIdShape (id : String) : Prop :=
  ∃ s k d, id = "j_" ++ s ++ "__" ++ JKind.tag k ++ "_" ++ d ∧ s ≠ "" ∧
    (∀ c ∈ s.toList, exp014IdChar c = true) ∧ d ≠ "" ∧ ∀ c ∈ d.toList, c.isDigit = true

/-- The junction ID `nodeId` gives a transition with a non-empty name matches AC1's regex. -/
theorem exp014_junctionId_shape {t : String} (k : JKind) (i : Nat) (ht : t ≠ "") :
    exp014JunctionIdShape (nodeId (.junction t k i)) := by
  refine ⟨sanitize t, k, toString i, rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    apply ht
    have := congrArg String.toList h
    simp only [sanitize_toList, String.toList_empty, List.map_eq_nil_iff] at this
    exact String.toList_inj.mp (by simpa using this)
  · intro c hc
    simp only [sanitize_toList, List.mem_map] at hc
    obtain ⟨c', -, rfl⟩ := hc
    unfold sanitizeChar exp014IdChar
    split <;> simp_all
  · simp
  · intro c hc
    simp only [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

/-- **AC1 for every exporter meeting EXP-014**: by the first line, every junction node of a
transition whose name is not empty and holds only ASCII characters has an ID that matches AC1's
regex. The empty transition name gives `j___xor_0`, which the regex rejects, and a non-ASCII name
gives an implementation-defined ID. -/
@[evidence cites "EXP-014" "AC1: all junction IDs match the regex j_[A-Za-z0-9_]+__(xor|and)_[0-9]+, for every exporter meeting EXP-014, for every junction of a transition whose name is not empty and holds only ASCII characters"]
theorem EXP_014_ac1 (E : Exporter) (hE : EXP_014 E) (cfg : ExportCfg) (X : ExportNet) :
    ∀ n ∈ (E cfg X).nodes, ∀ t k i, n.ref = .junction t k i → t ≠ "" → AsciiName t →
      exp014JunctionIdShape n.id := by
  intro n hn t k i hr ht ha
  rw [(hE cfg X).1 n hn (by rw [hr]; exact ha), hr]
  exact exp014_junctionId_shape k i ht

/-- **AC1 on the reference**, for every cluster stage. -/
theorem EXP_014_ac1_reference (S : ClusterStage) (cfg : ExportCfg) (X : ExportNet) :
    ∀ n ∈ (refExportWith S cfg X).nodes, ∀ t k i, n.ref = .junction t k i → t ≠ "" →
      AsciiName t → exp014JunctionIdShape n.id :=
  EXP_014_ac1 _ (EXP_014_any S) cfg X

end Libpetri.Spec
