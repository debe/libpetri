import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExportCluster
import Libpetri.Spec.Text.MOD_040

set_option linter.missingDocs true

/-!
# MOD-040 (a): `subnetOf` and the instance-prefix helper (`spec/11-modular-composition.md`)

MOD-040 has two halves. This block is the first (slice (a)): the accessor `subnetOf(name)`, which
answers which subnet a place or transition of a net belongs to, and the instance-prefix helper
`instancePrefixOf`, the part of a name before its last `/`. The second half (slice (b), the block
`MOD_040_b` in `MOD_040_b.lean`) is the DOT export: one `subgraph cluster_<key>` per cluster key, nested by prefix, over the
exporter of EXP-016.

The model is a pair `M : SubnetAccess`: an accessor `M.subnetOf` over the names of a net and its
membership mapping ([MOD-026]), and a helper `M.prefixOf`. The accessor's four steps are four
lines: a name that is no node of the net is absent; a membership entry wins; otherwise the
longest `/`-prefix of the name under which some transition of the net lives; otherwise absent.
The fifth line is the helper. The `/`-prefix and the instance prefix are the export glossary's
(`IsSlashPrefix`, `instancePrefix`, `Spec/GlossaryExportCluster.lean`), written over the
characters of a name so that `decide` closes every example; the accessor and the exporter's
default cluster key (`clusterKey .auto`) therefore speak about one prefix.

The witness is `refSubnetAccess`, which walks the `/`-prefixes of the name from the longest, as
Java, TypeScript and Rust do (Python calls the Rust accessor). Every model of the block answers
`s1` for the place `s1/obs/TURN` of an instance `s1` whose transitions are all `s1/…`, while the
exporter's default cluster key is `s1/obs` (`mod040_differs_from_clusterKey`): the difference
the markdown documents.
-/

namespace Libpetri.Spec

open Libpetri

/-! ## Block-local vocabulary -/

/-- The part of a built net `subnetOf` reads: the names of its places, the names of its
transitions, and its subnet-membership mapping ([MOD-026]; `none`: no entry). -/
structure SubnetNet where
  /-- The names of the places of the net. -/
  places : List String := []
  /-- The names of the transitions of the net. -/
  trans  : List String := []
  /-- The membership mapping: the owning subnet of a node, when it has an entry. -/
  member : String → Option String := fun _ => none

/-- `n` is the name of a place or of a transition of `X`. -/
def SubnetNet.IsNode (X : SubnetNet) (n : String) : Prop := n ∈ X.places ∨ n ∈ X.trans

instance (X : SubnetNet) (n : String) : Decidable (X.IsNode n) := by
  unfold SubnetNet.IsNode; infer_instance

/-- The `/`-prefix `P` heads a transition of `X`: the name of some transition of `X` begins with
`P/` (`IsSlashPrefix`: `P` is not empty and is followed by `/` in the name). -/
def SubnetNet.Heads (X : SubnetNet) (P : String) : Prop := ∃ t ∈ X.trans, IsSlashPrefix P t

instance (X : SubnetNet) (P : String) : Decidable (X.Heads P) := by
  unfold SubnetNet.Heads; infer_instance

/-- **The model of MOD-040 (a)**: the accessor `subnetOf` and the instance-prefix helper. -/
structure SubnetAccess where
  /-- `subnetOf(name)` on a net; `none`: absent. -/
  subnetOf : SubnetNet → String → Option String
  /-- The instance-prefix helper `instancePrefixOf(name)`; `none`: absent. -/
  prefixOf : String → Option String

/-! ## The witness: the walk every runtime does -/

/-- The `/`-prefixes of a name, longest first: `a/b/c/x` gives `a/b/c`, `a/b`, `a`. -/
def slashPrefixes (n : String) : List String :=
  ((cutsAux [] n.toList).filter fun u => !u.isEmpty).reverse.map String.ofList

/-- The first `/`-prefix of `n`, longest first, that heads a transition of `X`. -/
def subnetWalk (X : SubnetNet) (n : String) : Option String :=
  (slashPrefixes n).find? fun P => decide (X.Heads P)

/-- **The reference accessor**: absent for a name that is no node; else the membership entry;
else the walk. Java `PetriNet.subnetOf`, TypeScript `PetriNet.subnetOf` and Rust
`PetriNet::subnet_of` compute it: each tries the prefixes ending before a `/` at a position
greater than 0, from the last `/` down, against the set of such prefixes of transition names. -/
def refSubnetOf (X : SubnetNet) (n : String) : Option String :=
  if X.IsNode n then (X.member n).or (subnetWalk X n) else none

/-- **The reference pair** (witness model): the reference accessor and the glossary's
`instancePrefix` (Java `SubnetPrefixes.instancePrefixOf`, TypeScript `instancePrefixOf`, Rust
`instance_prefix_of`). -/
def refSubnetAccess : SubnetAccess := ⟨refSubnetOf, instancePrefix⟩

#spec_witness refSubnetAccess

/-! ## MOD-040 (a): `subnetOf` and the instance-prefix helper -/

requirement MOD_040
  id "MOD-040"
  title "Export Grouping (subgraph cluster_* per instance prefix)"
  kind F
  scope "the subnetOf accessor of every built net, and the instance-prefix helper"
  source verbatim "spec/11-modular-composition.md"
  covers MOD_040.s2, MOD_040.s3, MOD_040.s4, MOD_040.s5, MOD_040.s6, MOD_040.s7, MOD_040.s8
  reading "For the pair M of an accessor M.subnetOf and an instance-prefix helper M.prefixOf, with a net X given by its place names, its transition names and its membership mapping X.member, a name n of X a node when it is one of those place or transition names, and a /-prefix P heading a transition of X (X.Heads P) when IsSlashPrefix P t for some transition name t of X (P is not empty and t begins with P followed by /):"
          "a name that is no node of X is absent;"
          "a node with a membership entry s gets s;"
          "a node without a membership entry, and a /-prefix P of it that heads a transition of X and is at least as long as every /-prefix of it that heads a transition of X, gets P;"
          "a node without a membership entry none of whose /-prefixes heads a transition of X is absent;"
          "the helper gives q for n exactly when q is not empty and n is q, a /, and a rest without / (the part before the last /)."
  assumes "The model is a pair: the accessor subnetOf over the names of a net (SubnetNet: place names, transition names, the MOD-026 membership mapping as a function, none for no entry) and the instance-prefix helper. Names are strings read as their characters (String.toList), as in the export glossary (IsSlashPrefix, instancePrefix, cutsAux in Spec/GlossaryExportCluster.lean), so the cluster key of EXP-016 and this accessor share one notion of prefix. The accessor reads names only: Java compares place names, not (name, token type) records, and Rust and TypeScript key nodes by name."
          "The SHOULD priority of subnetOf and the helper is read by the scoping sentence: it is whether an implementation offers them, not how they answer; the SHOULD sentences of the export half are slice (b). Java (PetriNet.subnetOf, SubnetPrefixes.instancePrefixOf), TypeScript (PetriNet.subnetOf, instancePrefixOf from libpetri/export) and Rust (PetriNet::subnet_of in libpetri-core petri_net.rs, instance_prefix_of in libpetri-core subnet_prefixes.rs, re-exported by libpetri_export::subnet_prefixes) offer both; Python offers Net.subnet_of, which calls the Rust accessor, and no helper. That an implementation offers them is an existence clause, not a line, and it needs no coverage clause: a model is a pair of total functions, so every model answers every name, absent being the answer none. The coverage convention of GlossaryExec.lean is for relations, where a sub-relation can drop a step; a function cannot drop an answer. Which language offers which of the two is the list above, a fact about the code bases that no Lean statement carries."
          "Lines 1 to 4 are steps 1 to 4 of the rule as an accessor. Step 3 says 'the longest /-prefix of name that some transition of the net lives under' and gives its test (some transition's name begins with P/); it is not a fact about instances: when a subnet uses / for a transition of its own namespace (a transition s1/obs/tick), the place s1/obs/TURN answers s1/obs, which is no instance (mod040_ownNamespaceTransition). Line 3 states the longest qualifying prefix declaratively; the reference finds it by walking from the longest (subnetWalk), as the runtimes do. An index that keeps only the part before the last / of each transition name loses the outer prefixes of a nested transition and breaks line 3 (MOD_040_forbids_immediateIndex). The five lines fix both functions on every input: every model is the reference pair (mod040_unique)."
          "The sentence 'For a transition name step 3 returns its own instance prefix (the transition itself begins with it), so transitions are attributed as by the part before the last /' is mod040_transition_eq_instancePrefix, for every model: a transition without a membership entry answers its instance prefix. The phrase that subnetOf 'follows the default (AUTO) cluster rule above without its nesting, except that the prefix it falls back to is one some transition lives under' is mod040_agrees_auto: on a node whose part before the last / heads a transition, or that has none, subnetOf equals the AUTO cluster key of EXP-016; the exception is mod040_differs_from_clusterKey."
          "A /-prefix is non-empty in line 3. The step-3 prose 'the prefixes of name ending before one of its / characters' also covered the empty prefix of a name that starts with /; no runtime answers it (the walks stop at position 0: Rust instance_prefix_of returns none for idx 0, Java and TypeScript loop while the position is greater than 0, and the transition-prefix sets skip position 0), so the markdown now says 'the first non-empty P'. The runtimes agree on every name, empty segments included: Rust collects a transition's prefixes by walking instance_prefix_of up (stopping early at a prefix already collected, whose own prefixes are then collected too), Java and TypeScript by scanning every / after position 0; both give the non-empty prefixes followed by /. The block needs no assumption on names (no D46 name assumption)."
          "Line 5 is the instance-prefix helper, the 'instance-prefix detection' bullet's prefix: Java, TypeScript and Rust return the substring before the last / and none when there is no / or the last / is at position 0 (instancePrefix_eq_some). The default (AUTO) cluster key of EXP-016 is the membership entry, else this helper (mod040_clusterKey_auto, for every model of the block), so the exporter clusters s1/obs/TURN under s1/obs while subnetOf answers s1 (mod040_differs_from_clusterKey): the sentence that subnetOf differs from the DOT AUTO cluster rule is a consequence of lines 3 and 5."
          "The export half of MOD-040 is slice (b), the block MOD_040_b (MOD_040_b.lean) over the exporter of EXP-016: the opening sentence (a subgraph cluster per subnet), the membership and instance-prefix bullets, the preference and fall-back sentence, the caller-selectable cluster source (kind N), the sanitisation sentence, the label sentence and the sentence that the requirement changes no styling, junction or arc rule. EXP-016's block states the same rule for every exporter today (EXP_016, Spec/Req/EXP_016.lean), and its forbids theorem EXP_016_forbids_walkUp kills an exporter that clusters by subnetOf."
          "Quality, kind Q and tested, not proven: 'The set of prefixes that head a transition SHOULD be computed once per net, lazily, so subnetOf costs O(depth of the name)' (all three runtimes build the index on the first call, Rust subnet_index OnceLock, Java volatile subnetIndex, TypeScript _nameIndex), and 'subnetOf is additive: no export output, membership mapping or event changes' together with 'The exporter's instance-prefix helper and its clustering are unchanged by this rule' (a property of a change to the code, which a statement about the accessor cannot carry)."
          "AC1 (two instances b1 and b2 give subgraph cluster_b1 and subgraph cluster_b2), AC2 (each cluster block holds exactly the nodes under its prefix), AC3 (nested prefixes give nested subgraphs), AC4 (no composed instance, no metadata and no / gives no cluster subgraph), AC5 (cluster IDs match cluster_[A-Za-z0-9_]+), AC6 (one cluster block per subnet of the membership metadata, a shared place at the top level) and AC7 (metadata nodes cluster by subnet name, prefix-named nodes by prefix) are the export half, slice (b), the block MOD_040_b; EXP-016 states them for every exporter too (EXP_016_nonvacuous for AC1 and AC3, EXP_016_ac2, EXP_016_ac4, EXP_016_ac5, and its first line under a membership map for AC6 and AC7)."
          "AC8 is decided on the reference in MOD_040_nonvacuous: a directly composed node answers its subnet name (line 2), the instance-composed node b1/inner/p answers b1/inner (line 3, the net having the transition b1/inner/t; an instance composed from a subnet with no transition has no transition under its prefix, and its nodes answer an outer prefix or are absent), and a shared rendezvous place without /, a flat node without / and a name the net does not declare are absent (lines 1, 2 and 4: a shared place has no entry, by MOD-026 rule 3, and without / it has no /-prefix). A shared place whose /-prefix heads a transition answers that prefix by line 3 (mod040_sharedPlaceUnderPrefix), which is why AC8 says 'without /'."
          "On a net a MOD-026 builder produces, every membership key is a node, so line 1 is binding only in the abstract model, whose mapping may have an entry for a name that is no node; there it also rules out an accessor that looks the entry up before the node test. No runtime does: Java (PetriNet.java subnetOf, the index.nodes().contains test), TypeScript (petri-net.ts subnetOf, the index.nodes.has test) and Rust (petri_net.rs subnet_of, index.nodes.get(name)?) test the node first. The statement is stronger than the observable contract here, not weaker."
          "AC9 is decided on the reference in MOD_040_nonvacuous: with a transition s1/t the place s1/obs/TURN answers s1 (line 3, walking up past s1/obs to a prefix some transition lives under), x/y with no transition under x/ is absent (line 4), with a transition outer/inner/t the place outer/inner/p answers outer/inner, and a membership entry wins over each (line 2). Its last sentence, that the DOT export of the same nets is byte-identical to before, is the export half (slice (b), the block MOD_040_b) and kind Q for the bytes."
          "The test derivation (a composed net with two instances, and a directly composed net of two subnets, exported and checked for cluster blocks) is the export half, slice (b), the block MOD_040_b."
  signoff "2026-11-13 e3074a4aeb304e8b ai"
  statement : SubnetAccess → Prop :=
    fun M =>
      (∀ (X : SubnetNet) n, ¬ X.IsNode n → M.subnetOf X n = none) ∧
      (∀ (X : SubnetNet) n s, X.IsNode n → X.member n = some s → M.subnetOf X n = some s) ∧
      (∀ (X : SubnetNet) n P, X.IsNode n → X.member n = none → IsSlashPrefix P n → X.Heads P →
        (∀ Q, IsSlashPrefix Q n → X.Heads Q → Q.toList.length ≤ P.toList.length) →
        M.subnetOf X n = some P) ∧
      (∀ (X : SubnetNet) n, X.IsNode n → X.member n = none →
        (∀ P, IsSlashPrefix P n → ¬ X.Heads P) → M.subnetOf X n = none) ∧
      (∀ n q, M.prefixOf n = some q ↔
        q.toList ≠ [] ∧ ∃ r, n.toList = q.toList ++ '/' :: r ∧ '/' ∉ r)

/- The pinned readable form of MOD-040: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_040 : SubnetAccess → Prop :=
fun M =>
  (∀ (X : SubnetNet) (n : String), ¬X.IsNode n → M.subnetOf X n = none) ∧
    (∀ (X : SubnetNet) (n s : String), X.IsNode n → X.member n = some s → M.subnetOf X n = some s) ∧
      (∀ (X : SubnetNet) (n P : String),
          X.IsNode n →
            X.member n = none →
              IsSlashPrefix P n →
                X.Heads P →
                  (∀ (Q : String), IsSlashPrefix Q n → X.Heads Q → Q.toList.length ≤ P.toList.length) →
                    M.subnetOf X n = some P) ∧
        (∀ (X : SubnetNet) (n : String),
            X.IsNode n → X.member n = none → (∀ (P : String), IsSlashPrefix P n → ¬X.Heads P) → M.subnetOf X n = none) ∧
          ∀ (n q : String), M.prefixOf n = some q ↔ q.toList ≠ [] ∧ ∃ r, n.toList = q.toList ++ '/' :: r ∧ '/' ∉ r
-/
#guard_msgs in #print MOD_040

/-! ### The five lines, named (for the mutants) -/

section Lines

/-- Line 1 of MOD-040 (a): a name that is no node is absent. -/
def mod040_line1 (M : SubnetAccess) : Prop :=
  ∀ (X : SubnetNet) n, ¬ X.IsNode n → M.subnetOf X n = none

/-- Line 2 of MOD-040 (a): a membership entry wins. -/
def mod040_line2 (M : SubnetAccess) : Prop :=
  ∀ (X : SubnetNet) n s, X.IsNode n → X.member n = some s → M.subnetOf X n = some s

/-- Line 3 of MOD-040 (a): otherwise the longest `/`-prefix that heads a transition. -/
def mod040_line3 (M : SubnetAccess) : Prop :=
  ∀ (X : SubnetNet) n P, X.IsNode n → X.member n = none → IsSlashPrefix P n → X.Heads P →
    (∀ Q, IsSlashPrefix Q n → X.Heads Q → Q.toList.length ≤ P.toList.length) →
    M.subnetOf X n = some P

/-- Line 4 of MOD-040 (a): otherwise absent. -/
def mod040_line4 (M : SubnetAccess) : Prop :=
  ∀ (X : SubnetNet) n, X.IsNode n → X.member n = none →
    (∀ P, IsSlashPrefix P n → ¬ X.Heads P) → M.subnetOf X n = none

/-- Line 5 of MOD-040 (a): the helper is the part before the last `/`, when not empty. -/
def mod040_line5 (M : SubnetAccess) : Prop :=
  ∀ n q, M.prefixOf n = some q ↔ q.toList ≠ [] ∧ ∃ r, n.toList = q.toList ++ '/' :: r ∧ '/' ∉ r

/-- MOD-040 (a) is its five lines. -/
theorem mod040_iff (M : SubnetAccess) :
    MOD_040 M ↔ mod040_line1 M ∧ mod040_line2 M ∧ mod040_line3 M ∧ mod040_line4 M ∧
      mod040_line5 M :=
  Iff.rfl

end Lines

/-! ### The walk -/

/-- The `/`-prefixes listed by `slashPrefixes` are exactly the `/`-prefixes of the name. -/
theorem mem_slashPrefixes (n q : String) : q ∈ slashPrefixes n ↔ IsSlashPrefix q n := by
  rw [isSlashPrefix_iff]
  simp only [slashPrefixes, List.mem_map, List.mem_reverse, List.mem_filter, mem_cutsAux,
    List.nil_append, Bool.not_eq_true', List.isEmpty_eq_false_iff]
  constructor
  · rintro ⟨u, ⟨⟨v, r, rfl, hr⟩, hu⟩, rfl⟩
    exact ⟨by simpa using hu, r, by simp [hr]⟩
  · rintro ⟨hq, r, hr⟩
    exact ⟨q.toList, ⟨⟨q.toList, r, rfl, hr⟩, hq⟩, String.ofList_toList⟩

/-- The cuts of `cutsAux` come shortest first, strictly. -/
theorem cutsAux_pairwise (acc l : List Char) :
    (cutsAux acc l).Pairwise (fun a b => a.length < b.length) := by
  induction l generalizing acc with
  | nil => exact List.Pairwise.nil
  | cons c cs ih =>
    simp only [cutsAux]
    split
    · refine List.pairwise_append.2 ⟨List.pairwise_singleton _ _, ih _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at ha
      obtain ⟨v, r, rfl, -⟩ := (mem_cutsAux _ _ _).1 hb
      subst ha
      simp
    · simpa using ih (acc ++ [c])

/-- `slashPrefixes` lists the prefixes strictly longest first. -/
theorem slashPrefixes_pairwise (n : String) :
    (slashPrefixes n).Pairwise (fun a b => b.toList.length < a.toList.length) := by
  unfold slashPrefixes
  rw [List.pairwise_map, List.pairwise_reverse]
  simp only [String.toList_ofList]
  exact (cutsAux_pairwise [] n.toList).filter _

/-- **The walk finds the longest**: when `P` is a `/`-prefix of `n` that heads a transition and
no `/`-prefix of `n` heading a transition is longer, the walk answers `P`. -/
theorem subnetWalk_longest {X : SubnetNet} {n P : String} (hP : IsSlashPrefix P n)
    (hH : X.Heads P)
    (hmax : ∀ Q, IsSlashPrefix Q n → X.Heads Q → Q.toList.length ≤ P.toList.length) :
    subnetWalk X n = some P := by
  unfold subnetWalk
  have hmem : P ∈ slashPrefixes n := (mem_slashPrefixes n P).2 hP
  cases hf : (slashPrefixes n).find? (fun P => decide (X.Heads P)) with
  | none =>
    have := List.find?_eq_none.1 hf P hmem
    simp [hH] at this
  | some a =>
    obtain ⟨ha, as, bs, hl, has⟩ := List.find?_eq_some_iff_append.1 hf
    have haH : X.Heads a := by simpa using ha
    have haP : IsSlashPrefix a n :=
      (mem_slashPrefixes n a).1 (by rw [hl]; simp)
    have hle := hmax a haP haH
    have hpw := slashPrefixes_pairwise n
    rw [hl] at hpw hmem
    rw [List.pairwise_append, List.pairwise_cons] at hpw
    rcases List.mem_append.1 hmem with hin | hin
    · have := has P hin
      simp [hH] at this
    · rcases List.mem_cons.1 hin with rfl | hin
      · rfl
      · have := hpw.2.1.1 P hin
        omega

/-- The walk is absent when no `/`-prefix of the name heads a transition. -/
theorem subnetWalk_none {X : SubnetNet} {n : String} (h : ∀ P, IsSlashPrefix P n → ¬ X.Heads P) :
    subnetWalk X n = none := by
  unfold subnetWalk
  refine List.find?_eq_none.2 fun P hP => ?_
  simpa using h P ((mem_slashPrefixes n P).1 hP)

/-! ### The reference -/

/-- The reference accessor meets lines 1 to 4. -/
theorem refSubnetOf_lines (h : SubnetAccess) (hs : h.subnetOf = refSubnetOf) :
    mod040_line1 h ∧ mod040_line2 h ∧ mod040_line3 h ∧ mod040_line4 h := by
  refine ⟨fun X n hn => ?_, fun X n s hn hm => ?_, fun X n P hn hm hP hH hmax => ?_,
    fun X n hn hm hno => ?_⟩
  · rw [hs]; simp [refSubnetOf, hn]
  · rw [hs]; simp [refSubnetOf, hn, hm]
  · rw [hs]; simp [refSubnetOf, hn, hm, subnetWalk_longest hP hH hmax]
  · rw [hs]; simp [refSubnetOf, hn, hm, subnetWalk_none hno]

/-- ✓ **The reference meets MOD-040 (a)**. In a net with the transition `s1/t`, the place
`s1/obs/TURN` belongs to `s1`: the walk tries `s1/obs`, under which no transition lives, then
`s1`. A node with a membership entry answers that entry, and a name that is no node of the net
answers nothing. The helper gives `s1/obs` for `s1/obs/TURN`, the part before its last `/`. -/
@[evidence holds MOD_040]
theorem MOD_040_reference : MOD_040 refSubnetAccess := by
  obtain ⟨h1, h2, h3, h4⟩ := refSubnetOf_lines refSubnetAccess rfl
  exact ⟨h1, h2, h3, h4, fun n q => instancePrefix_eq_some n q⟩

/-! ### Consequences for every model of the block -/

/-- Every model's helper is the export glossary's instance prefix. -/
theorem mod040_prefixOf_eq {M : SubnetAccess} (h : mod040_line5 M) (n : String) :
    M.prefixOf n = instancePrefix n := by
  apply Option.ext
  intro q
  rw [h n q, instancePrefix_eq_some]

/-- **The default cluster key, through the helper**: under every model of the block, the
exporter's default (`AUTO`) cluster key of EXP-016 is the membership entry, else the helper's
answer. For a node `b1/x` without an entry that is `b1`. -/
theorem mod040_clusterKey_auto {M : SubnetAccess} (h : MOD_040 M)
    (m : String → Option String) (n : String) :
    clusterKey .auto m n = (m n).or (M.prefixOf n) := by
  rw [clusterKey_auto, mod040_prefixOf_eq h.2.2.2.2]

/-- Line 3 on a concrete name, with the maximality premise decided over the finite list of the
name's `/`-prefixes. -/
theorem mod040_line3_of {M : SubnetAccess} (h : mod040_line3 M) {X : SubnetNet} {n P : String}
    (hn : X.IsNode n) (hm : X.member n = none) (hP : IsSlashPrefix P n) (hH : X.Heads P)
    (hmax : ∀ Q ∈ slashPrefixes n, X.Heads Q → Q.toList.length ≤ P.toList.length) :
    M.subnetOf X n = some P :=
  h X n P hn hm hP hH fun Q hQ => hmax Q ((mem_slashPrefixes n Q).2 hQ)

/-- Line 4 on a concrete name, with its premise decided over the name's `/`-prefixes. -/
theorem mod040_line4_of {M : SubnetAccess} (h : mod040_line4 M) {X : SubnetNet} {n : String}
    (hn : X.IsNode n) (hm : X.member n = none) (hno : ∀ P ∈ slashPrefixes n, ¬ X.Heads P) :
    M.subnetOf X n = none :=
  h X n hn hm fun P hP => hno P ((mem_slashPrefixes n P).2 hP)

/-- Two cuts of one name: when a name is `Q`, a `/` and a rest, and also `u`, a `/` and a rest
without `/`, then `Q` is no longer than `u`. -/
theorem cut_length_le {Q u r r' : List Char} (h : Q ++ '/' :: r' = u ++ '/' :: r)
    (hr : '/' ∉ r) : Q.length ≤ u.length := by
  rcases List.append_eq_append_iff.1 h with ⟨a', rfl, -⟩ | ⟨c', rfl, hc⟩
  · simp
  · cases c' with
    | nil => simp
    | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at hc
      exact absurd (by rw [hc.2]; simp) hr

/-- A name with a `/`-prefix has an instance prefix, and no `/`-prefix of the name is longer
than it. -/
theorem isSlashPrefix_instancePrefix {Q n : String} (hQ : IsSlashPrefix Q n) :
    ∃ q, instancePrefix n = some q ∧ Q.toList.length ≤ q.toList.length := by
  obtain ⟨hQe, r', hr'⟩ := (isSlashPrefix_iff Q n).1 hQ
  cases hl : lastCut n.toList with
  | none => exact absurd (by rw [hr']; simp) ((lastCut_eq_none _).1 hl)
  | some u =>
    obtain ⟨r, hu, hr⟩ := (lastCut_eq_some _ _).1 hl
    have hle := cut_length_le (hr'.symm.trans hu) hr
    have hne : u ≠ [] := by
      rintro rfl
      exact hQe (List.eq_nil_of_length_eq_zero (by simpa using hle))
    refine ⟨String.ofList u, ?_, by simpa using hle⟩
    simp [instancePrefix, hl, hne]

/-- What the walk answers is a `/`-prefix of the name that heads a transition, and no such
prefix is longer. -/
theorem subnetWalk_some_max {X : SubnetNet} {n a : String} (hf : subnetWalk X n = some a) :
    IsSlashPrefix a n ∧ X.Heads a ∧
      ∀ Q, IsSlashPrefix Q n → X.Heads Q → Q.toList.length ≤ a.toList.length := by
  unfold subnetWalk at hf
  obtain ⟨ha, as, bs, hl, has⟩ := List.find?_eq_some_iff_append.1 hf
  have haP : IsSlashPrefix a n := (mem_slashPrefixes n a).1 (by rw [hl]; simp)
  refine ⟨haP, by simpa using ha, fun Q hQ hH => ?_⟩
  have hmem : Q ∈ slashPrefixes n := (mem_slashPrefixes n Q).2 hQ
  have hpw := slashPrefixes_pairwise n
  rw [hl] at hpw hmem
  rw [List.pairwise_append, List.pairwise_cons] at hpw
  rcases List.mem_append.1 hmem with hin | hin
  · have := has Q hin
    simp [hH] at this
  · rcases List.mem_cons.1 hin with rfl | hin
    · exact le_refl _
    · have := hpw.2.1.1 Q hin
      omega

/-- **The block pins its model**: every model of MOD-040 (a) is the reference pair. Its accessor
is the reference accessor on every net and every name, and its helper is the instance prefix of
every name. So an implementation that answers differently from the reference on even one name of
one net does not meet the requirement. -/
theorem mod040_unique {M : SubnetAccess} (h : MOD_040 M) :
    M.subnetOf = refSubnetOf ∧ M.prefixOf = instancePrefix := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨funext fun X => funext fun n => ?_, funext fun n => mod040_prefixOf_eq h5 n⟩
  by_cases hn : X.IsNode n
  · cases hm : X.member n with
    | some s => simp [refSubnetOf, hn, hm, h2 X n s hn hm]
    | none =>
      cases hw : subnetWalk X n with
      | some a =>
        obtain ⟨hP, hH, hmax⟩ := subnetWalk_some_max hw
        simp [refSubnetOf, hn, hm, hw, h3 X n a hn hm hP hH hmax]
      | none =>
        have hno : ∀ P, IsSlashPrefix P n → ¬ X.Heads P := by
          intro P hP hH
          have := List.find?_eq_none.1 hw P ((mem_slashPrefixes n P).2 hP)
          simp [hH] at this
        simp [refSubnetOf, hn, hm, hw, h4 X n hn hm hno]
  · simp [refSubnetOf, hn, h1 X n hn]

/-- **`subnetOf` follows the default cluster rule where a transition lives under the prefix**:
under every model, on a node whose part before the last `/` heads a transition (or that has no
such part), `subnetOf` answers the exporter's default (`AUTO`) cluster key of EXP-016: the
membership entry, else the part before the last `/`. With the transition `b1/t`, the place
`b1/x` answers `b1` both ways. -/
theorem mod040_agrees_auto {M : SubnetAccess} (h : MOD_040 M) {X : SubnetNet} {n : String}
    (hn : X.IsNode n) (hH : ∀ q, instancePrefix n = some q → X.Heads q) :
    M.subnetOf X n = clusterKey .auto X.member n := by
  rw [clusterKey_auto]
  cases hm : X.member n with
  | some s => simpa using h.2.1 X n s hn hm
  | none =>
    cases hq : instancePrefix n with
    | some q =>
      simpa using h.2.2.1 X n q hn hm (instancePrefix_isSlashPrefix hq) (hH q hq)
        fun Q hQ _ => by
          obtain ⟨q', hq', hle⟩ := isSlashPrefix_instancePrefix hQ
          rw [hq] at hq'
          cases hq'
          exact hle
    | none =>
      simpa using h.2.2.2.1 X n hn hm fun P hP _ => by
        obtain ⟨q', hq', -⟩ := isSlashPrefix_instancePrefix hP
        rw [hq] at hq'
        cases hq'

/-- **A transition belongs to its own instance prefix**, under every model: a transition with no
membership entry answers the part of its name before the last `/`, because the transition
itself lives under that prefix. The transition `outer/inner/t` answers `outer/inner`. -/
theorem mod040_transition_eq_instancePrefix {M : SubnetAccess} (h : MOD_040 M) {X : SubnetNet}
    {t q : String} (ht : t ∈ X.trans) (hm : X.member t = none) (hq : instancePrefix t = some q) :
    M.subnetOf X t = some q := by
  rw [mod040_agrees_auto h (Or.inr ht) fun q' hq' => ⟨t, ht, instancePrefix_isSlashPrefix hq'⟩,
    clusterKey_auto, hm, hq]
  rfl

/-! ### Example nets -/

/-- The nets of AC8 and AC9 in one: the transitions `s1/t`, `outer/inner/t` and `b1/inner/t`;
the places `s1/obs/TURN`, `x/y`, `outer/inner/p`, `b1/inner/p`, the shared place `pipe` and the
flat place `flat`; the directly composed transition `emit` and place `buf`, both of the subnet
`PipeProducer`. -/
def mod040Net : SubnetNet :=
  { places := ["s1/obs/TURN", "x/y", "outer/inner/p", "b1/inner/p", "pipe", "flat", "buf"],
    trans := ["s1/t", "outer/inner/t", "b1/inner/t", "emit"],
    member := fun n => if n = "emit" ∨ n = "buf" then some "PipeProducer" else none }

/-- The same net with a membership entry `Direct` for `s1/obs/TURN`, `x/y` and
`outer/inner/p`. -/
def mod040MetaNet : SubnetNet :=
  { mod040Net with
    member := fun n => if n = "s1/obs/TURN" ∨ n = "x/y" ∨ n = "outer/inner/p" then some "Direct"
      else mod040Net.member n }

/-- ✓ **AC8 and AC9 on the reference.** On a net with the transitions `s1/t`, `outer/inner/t`,
`b1/inner/t` and the directly composed `emit`: the place `s1/obs/TURN` belongs to `s1` (no
transition lives under `s1/obs`, so the walk goes up one more step), `x/y` belongs to nothing
(no transition under `x/`), `outer/inner/p` to `outer/inner`, `b1/inner/p` to `b1/inner`, the
transition `outer/inner/t` to its own prefix; `emit` belongs to its subnet `PipeProducer`; the
shared place `pipe`, the flat place `flat` and the undeclared name `no-such-node` belong to
nothing. With a membership entry `Direct` for `s1/obs/TURN`, `x/y` and `outer/inner/p`, each of
them answers `Direct`. The helper answers `s1/obs` for `s1/obs/TURN`, `outer` for `outer/q`, and
nothing for `flat` and `/x`. -/
@[evidence nonvacuous MOD_040]
theorem MOD_040_nonvacuous :
    refSubnetAccess.subnetOf mod040Net "s1/obs/TURN" = some "s1" ∧
    refSubnetAccess.subnetOf mod040Net "x/y" = none ∧
    refSubnetAccess.subnetOf mod040Net "outer/inner/p" = some "outer/inner" ∧
    refSubnetAccess.subnetOf mod040Net "b1/inner/p" = some "b1/inner" ∧
    refSubnetAccess.subnetOf mod040Net "outer/inner/t" = some "outer/inner" ∧
    refSubnetAccess.subnetOf mod040Net "emit" = some "PipeProducer" ∧
    refSubnetAccess.subnetOf mod040Net "pipe" = none ∧
    refSubnetAccess.subnetOf mod040Net "flat" = none ∧
    refSubnetAccess.subnetOf mod040Net "no-such-node" = none ∧
    refSubnetAccess.subnetOf mod040MetaNet "s1/obs/TURN" = some "Direct" ∧
    refSubnetAccess.subnetOf mod040MetaNet "x/y" = some "Direct" ∧
    refSubnetAccess.subnetOf mod040MetaNet "outer/inner/p" = some "Direct" ∧
    refSubnetAccess.prefixOf "s1/obs/TURN" = some "s1/obs" ∧
    refSubnetAccess.prefixOf "outer/q" = some "outer" ∧
    refSubnetAccess.prefixOf "flat" = none ∧
    refSubnetAccess.prefixOf "/x" = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The net of the documented difference: one transition `s1/t` and the place `s1/obs/TURN`. -/
def mod040S1Net : SubnetNet := { places := ["s1/obs/TURN"], trans := ["s1/t"] }

/-- **`subnetOf` differs from the default cluster key**, for every model of MOD-040: with the
transition `s1/t`, the place `s1/obs/TURN` belongs to `s1`, while the exporter's default cluster
key of the same name is `s1/obs`, the part before its last `/`. -/
theorem mod040_differs_from_clusterKey {M : SubnetAccess} (h : MOD_040 M) :
    M.subnetOf mod040S1Net "s1/obs/TURN" = some "s1" ∧
      clusterKey .auto mod040S1Net.member "s1/obs/TURN" = some "s1/obs" := by
  refine ⟨mod040_line3_of h.2.2.1 (by decide) rfl (by decide) (by decide) (by decide), ?_⟩
  rw [mod040_clusterKey_auto h, mod040_prefixOf_eq h.2.2.2.2]
  decide

/-- **A transition in a subnet's own namespace**, for every model of MOD-040: with the
transitions `s1/t` and `s1/obs/tick`, the place `s1/obs/TURN` belongs to `s1/obs`, which heads
the transition `s1/obs/tick` though it is no instance. Step 3's test is "some transition lives
under the prefix", not "the prefix is an instance". -/
theorem mod040_ownNamespaceTransition {M : SubnetAccess} (h : MOD_040 M) :
    M.subnetOf { places := ["s1/obs/TURN"], trans := ["s1/t", "s1/obs/tick"] } "s1/obs/TURN" =
      some "s1/obs" :=
  mod040_line3_of h.2.2.1 (by decide) rfl (by decide) (by decide) (by decide)

/-- **A shared place under a prefix**, for every model of MOD-040: a shared rendezvous place has
no membership entry, but when it is named `b1/x` in a net with the transition `b1/t`, it answers
`b1`, because a transition lives under `b1`. Only a shared place none of whose `/`-prefixes heads
a transition (one without `/`, like `pipe`) is absent. -/
theorem mod040_sharedPlaceUnderPrefix {M : SubnetAccess} (h : MOD_040 M) :
    M.subnetOf { places := ["b1/x"], trans := ["b1/t"] } "b1/x" = some "b1" :=
  mod040_line3_of h.2.2.1 (by decide) rfl (by decide) (by decide) (by decide)

/-! ### Wrong models -/

/-- A pair with the reference helper and the accessor `f`. -/
def mod040With (f : SubnetNet → String → Option String) : SubnetAccess := ⟨f, instancePrefix⟩

/-- An accessor without the node test: a membership entry, else the walk, for any name. -/
def mod040NoNodeTest : SubnetAccess :=
  mod040With fun X n => (X.member n).or (subnetWalk X n)

/-- An accessor that ignores the membership mapping: the walk, for every node. -/
def mod040IgnoresMember : SubnetAccess :=
  mod040With fun X n => if X.IsNode n then subnetWalk X n else none

/-- An accessor that answers the part before the last `/` when it heads a transition, and is
absent otherwise (the reading that does not walk up). -/
def mod040LastSlash : SubnetAccess :=
  mod040With fun X n =>
    if X.IsNode n then
      (X.member n).or ((instancePrefix n).bind fun q => if X.Heads q then some q else none)
    else none

/-- An accessor that falls back to the part before the last `/` when no prefix heads a
transition. -/
def mod040PrefixFallback : SubnetAccess :=
  mod040With fun X n =>
    if X.IsNode n then (X.member n).or ((subnetWalk X n).or (instancePrefix n)) else none

/-- An accessor that walks the `/`-prefixes from the shortest. -/
def mod040Shortest : SubnetAccess :=
  mod040With fun X n =>
    if X.IsNode n then
      (X.member n).or ((slashPrefixes n).reverse.find? fun P => decide (X.Heads P))
    else none

/-- The reference accessor with a helper that answers the part before the first `/`. -/
def mod040FirstSlashHelper : SubnetAccess := ⟨refSubnetOf, fun n => (slashPrefixes n).getLast?⟩

/-- The reference accessor with a helper that answers the part before the last `/` even when it
is empty (`/x` gives the empty string). -/
def mod040EmptyHelper : SubnetAccess := ⟨refSubnetOf, fun n => (lastCut n.toList).map String.ofList⟩

/-- ✗ Answering by the part before the first `/` violates MOD-040 (line 3): with the transitions
`b1/t` and `b1/inner/t`, the place `b1/inner/p` gets `b1` from a walk that starts at the
shortest prefix, but `b1/inner` is the longest prefix that heads a transition. -/
@[evidence forbids MOD_040]
theorem MOD_040_forbids_shortest : ¬ MOD_040 mod040Shortest := by
  intro h
  have := mod040_line3_of (X := { places := ["b1/inner/p"], trans := ["b1/t", "b1/inner/t"] })
    (n := "b1/inner/p") (P := "b1/inner") h.2.2.1 (by decide) rfl (by decide) (by decide)
    (by decide)
  revert this
  decide

/-- ✗ A helper that keeps an empty prefix violates MOD-040 (line 5): it answers the empty string
for `/x`, which has no instance prefix. -/
@[evidence forbids MOD_040]
theorem MOD_040_forbids_emptyHelper : ¬ MOD_040 mod040EmptyHelper := by
  intro h
  have := mod040_prefixOf_eq h.2.2.2.2 "/x"
  revert this
  decide

/-- An accessor whose index of transition prefixes keeps only the part before the last `/` of
each transition name, not the shorter prefixes above it (a walk-up loop cut after its first
step). -/
def mod040ImmediateIndex : SubnetAccess :=
  mod040With fun X n =>
    if X.IsNode n then
      (X.member n).or ((slashPrefixes n).find? fun P => X.trans.any fun t => instancePrefix t == some P)
    else none

/-- ✗ An index that keeps only each transition's own instance prefix violates MOD-040 (line 3):
in a net whose only transition is the nested `b1/inner/t`, the place `b1/p` must answer `b1`,
because a transition lives under `b1`. The short index holds only `b1/inner`, so it answers
nothing. On the nets of AC8 and AC9 it gives the right answers, since there every instance has a
transition directly under its own prefix. -/
@[evidence forbids MOD_040]
theorem MOD_040_forbids_immediateIndex : ¬ MOD_040 mod040ImmediateIndex := by
  intro h
  have := mod040_line3_of (X := { places := ["b1/p"], trans := ["b1/inner/t"] }) (n := "b1/p")
    (P := "b1") h.2.2.1 (by decide) rfl (by decide) (by decide) (by decide)
  revert this
  decide

/-! ### Mutants, one per line -/

/-- Mutant reading: MOD-040 (a) without line 1 (no node test). -/
def MOD_040_mutant_noNodeTest (M : SubnetAccess) : Prop :=
  mod040_line2 M ∧ mod040_line3 M ∧ mod040_line4 M ∧ mod040_line5 M

/-- The accessor without the node test kills the mutant: it meets lines 2 to 5, but with the
transition `b1/t` it answers `b1` for the undeclared name `b1/ghost` (line 1). -/
@[evidence mutant MOD_040]
theorem MOD_040_mutant_noNodeTest_killed :
    MOD_040_mutant_noNodeTest mod040NoNodeTest ∧ ¬ MOD_040 mod040NoNodeTest := by
  refine ⟨⟨fun X n s _ hm => ?_, fun X n P _ hm hP hH hmax => ?_, fun X n _ hm hno => ?_,
    fun n q => instancePrefix_eq_some n q⟩, fun h => ?_⟩
  · simp [mod040NoNodeTest, mod040With, hm]
  · simp [mod040NoNodeTest, mod040With, hm, subnetWalk_longest hP hH hmax]
  · simp [mod040NoNodeTest, mod040With, hm, subnetWalk_none hno]
  · have := h.1 { trans := ["b1/t"] } "b1/ghost" (by decide)
    revert this
    decide

/-- Mutant reading: MOD-040 (a) without line 2 (membership not preferred). -/
def MOD_040_mutant_noMember (M : SubnetAccess) : Prop :=
  mod040_line1 M ∧ mod040_line3 M ∧ mod040_line4 M ∧ mod040_line5 M

/-- The accessor that ignores the membership mapping kills the mutant: it meets lines 1, 3, 4
and 5, but the directly composed transition `emit` of subnet `PipeProducer` gets nothing
(line 2). -/
@[evidence mutant MOD_040]
theorem MOD_040_mutant_noMember_killed :
    MOD_040_mutant_noMember mod040IgnoresMember ∧ ¬ MOD_040 mod040IgnoresMember := by
  refine ⟨⟨fun X n hn => ?_, fun X n P hn _ hP hH hmax => ?_, fun X n hn _ hno => ?_,
    fun n q => instancePrefix_eq_some n q⟩, fun h => ?_⟩
  · simp [mod040IgnoresMember, mod040With, hn]
  · simp [mod040IgnoresMember, mod040With, hn, subnetWalk_longest hP hH hmax]
  · simp [mod040IgnoresMember, mod040With, hn, subnetWalk_none hno]
  · have := h.2.1 mod040Net "emit" "PipeProducer" (by decide) (by decide)
    revert this
    decide

/-- Mutant reading: MOD-040 (a) without line 3 (no walk up). -/
def MOD_040_mutant_noWalk (M : SubnetAccess) : Prop :=
  mod040_line1 M ∧ mod040_line2 M ∧ mod040_line4 M ∧ mod040_line5 M

/-- The accessor that stops at the part before the last `/` kills the mutant: it meets lines 1,
2, 4 and 5, but with the transition `s1/t` it answers nothing for the place `s1/obs/TURN`, whose
longest `/`-prefix heading a transition is `s1` (line 3). -/
@[evidence mutant MOD_040]
theorem MOD_040_mutant_noWalk_killed :
    MOD_040_mutant_noWalk mod040LastSlash ∧ ¬ MOD_040 mod040LastSlash := by
  refine ⟨⟨fun X n hn => ?_, fun X n s hn hm => ?_, fun X n hn hm hno => ?_,
    fun n q => instancePrefix_eq_some n q⟩, fun h => ?_⟩
  · simp [mod040LastSlash, mod040With, hn]
  · simp [mod040LastSlash, mod040With, hn, hm]
  · simp only [mod040LastSlash, mod040With, if_pos hn, hm, Option.none_or]
    cases hq : instancePrefix n with
    | none => rfl
    | some q => simp [hno q (instancePrefix_isSlashPrefix hq)]
  · have := mod040_differs_from_clusterKey h
    revert this
    decide

/-- Mutant reading: MOD-040 (a) without line 4 (no absence when nothing heads a transition). -/
def MOD_040_mutant_noAbsence (M : SubnetAccess) : Prop :=
  mod040_line1 M ∧ mod040_line2 M ∧ mod040_line3 M ∧ mod040_line5 M

/-- The accessor that falls back to the part before the last `/` kills the mutant: it meets
lines 1, 2, 3 and 5, but answers `x` for the place `x/y` of a net with no transition under `x/`
(line 4). -/
@[evidence mutant MOD_040]
theorem MOD_040_mutant_noAbsence_killed :
    MOD_040_mutant_noAbsence mod040PrefixFallback ∧ ¬ MOD_040 mod040PrefixFallback := by
  refine ⟨⟨fun X n hn => ?_, fun X n s hn hm => ?_, fun X n P hn hm hP hH hmax => ?_,
    fun n q => instancePrefix_eq_some n q⟩, fun h => ?_⟩
  · simp [mod040PrefixFallback, mod040With, hn]
  · simp [mod040PrefixFallback, mod040With, hn, hm]
  · simp [mod040PrefixFallback, mod040With, hn, hm, subnetWalk_longest hP hH hmax]
  · have := mod040_line4_of h.2.2.2.1 (X := mod040Net) (n := "x/y") (by decide) (by decide)
      (by decide)
    revert this
    decide

/-- Mutant reading: MOD-040 (a) without line 5 (the helper unconstrained). -/
def MOD_040_mutant_noHelper (M : SubnetAccess) : Prop :=
  mod040_line1 M ∧ mod040_line2 M ∧ mod040_line3 M ∧ mod040_line4 M

/-- The helper that answers the part before the first `/` kills the mutant: the accessor is the
reference, so lines 1 to 4 hold, but the helper answers `outer` for `outer/inner/leaf`, whose
part before the last `/` is `outer/inner` (line 5). -/
@[evidence mutant MOD_040]
theorem MOD_040_mutant_noHelper_killed :
    MOD_040_mutant_noHelper mod040FirstSlashHelper ∧ ¬ MOD_040 mod040FirstSlashHelper := by
  refine ⟨refSubnetOf_lines mod040FirstSlashHelper rfl, fun h => ?_⟩
  have := mod040_prefixOf_eq h.2.2.2.2 "outer/inner/leaf"
  revert this
  decide

end Libpetri.Spec
