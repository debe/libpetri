import Libpetri.Spec.GlossaryExport

set_option linter.missingDocs true

/-!
# Glossary: export clusters and ghost edges (`spec/09-export.md`, EXP-016, EXP-017)

The words the EXP-016 and EXP-017 blocks are stated in. They are pure functions of names and
lists, written over `List Char`, because `String.isPrefixOf` and `String.splitOn` do not reduce in
the kernel:

* `instancePrefix`: the part of a name before its last `/`, none without a `/` or when the only
  `/` is the first character (`instance_prefix_of`, and `parent_of` for keys);
* `clusterKey` / `nodeKey`: membership entry, else instance prefix, per cluster source; a junction
  takes its transition's key ([EXP-016] sentence added by ruling D26 item 5);
* `IsSlashPrefix`, `keyChain`: the `/`-prefixes of a key, the clusters it opens;
* `clusterId`: `cluster_` followed by the sanitised key;
* `bridgeWitnesses`: every one-hop bridge `a → o → b` through a keyless node `o`, in the order the
  spec scans them (node order, then the edges into `o`, then the edges out of `o`; ruling D26
  item 6); the first one per ordered key pair is the ghost edge's anchor pair;
* `ghostEdge`: the edge EXP-017 draws for a bridged ordered key pair;
* `NoEmptySegment`: the D46 assumption on keys.

The lemmas that characterise them (`instancePrefix_eq_some`, `mem_keyChain`,
`mem_bridgeWitnesses` and their helpers) sit beside them. The reference cluster builder that
computes clusters and ghost edges from these words is `Reference/ExportCluster.lean`; it is a
witness model, not part of what a block states.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Export

/-! ## Vocabulary: cluster keys -/

/-- The characters before the last `/` of a name, none when it has no `/`. -/
def lastCut : List Char → Option (List Char)
  | [] => none
  | c :: cs =>
    match lastCut cs with
    | some u => some (c :: u)
    | none => if c = '/' then some [] else none

/-- **Glossary: Instance prefix** ([EXP-016], [MOD-010], [MOD-040]): the part of a name before its
last `/`; none when the name has no `/` or its only `/` is its first character. The same function
gives the parent of a cluster key (`parent_of`). -/
def instancePrefix (s : String) : Option String :=
  (lastCut s.toList).bind fun u => if u.isEmpty then none else some (String.ofList u)

/-- **Glossary: Cluster key of a name** ([EXP-016], [MOD-040]), under cluster source `src`, with
membership map `member` ([MOD-026]): the membership entry, else the instance prefix (`auto`, the
default); only the entry (`metadata`); only the prefix (`prefix`); none (`none`). -/
def clusterKey (src : ClusterSource) (member : String → Option String) (name : String) :
    Option String :=
  match src with
  | .auto => (member name).or (instancePrefix name)
  | .metadata => member name
  | .prefix => instancePrefix name
  | .none => none

/-- The name whose cluster key a node takes: the place's name, the transition's name, and for a
junction the name of its transition. -/
def NodeRef.keyName : NodeRef → String
  | .place p => p
  | .trans t => t
  | .junction t _ _ => t

/-- **Glossary: Cluster key of a node** ([EXP-016]): the cluster key of its name; a junction has
its transition's key (ruling D26 item 5). A node with no key is a top-level ("orphan") node. -/
def nodeKey (src : ClusterSource) (member : String → Option String) (r : NodeRef) :
    Option String :=
  clusterKey src member r.keyName

/-- **Glossary: Cluster ID** ([EXP-016]): `cluster_` followed by the sanitised key (`sanitize` of
[EXP-014]). -/
def clusterId (k : String) : String := "cluster_" ++ sanitize k

/-- `q` is a proper `/`-prefix of key `k`: `q` is not empty and `k` starts with `q` followed by
`/` ([EXP-016]: nested instance prefixes open nested clusters). -/
def IsSlashPrefix (q k : String) : Prop := q.toList ≠ [] ∧ q.toList ++ ['/'] <+: k.toList

instance (q k : String) : Decidable (IsSlashPrefix q k) := by
  unfold IsSlashPrefix; infer_instance

/-- **The D46 assumption on a cluster key**: it is not empty and none of its `/`-segments is
empty (it neither starts nor ends with `/` and has no `//`). -/
def NoEmptySegment (k : String) : Prop :=
  k.toList ≠ [] ∧ k.toList.head? ≠ some '/' ∧ k.toList.getLast? ≠ some '/' ∧
    ¬ ['/', '/'] <:+: k.toList

instance (k : String) : Decidable (NoEmptySegment k) := by
  unfold NoEmptySegment; infer_instance

/-- The prefixes of `acc ++ l` that end just before a `/` of `l`, shortest first. -/
def cutsAux : List Char → List Char → List (List Char)
  | _, [] => []
  | acc, c :: cs => (if c = '/' then [acc] else []) ++ cutsAux (acc ++ [c]) cs

/-- **The chain of a key**: its non-empty `/`-prefixes, outermost first, then the key itself; the
clusters a node with this key sits in (`mem_keyChain`). -/
def keyChain (k : String) : List String :=
  ((cutsAux [] k.toList).filter fun u => !u.isEmpty).map String.ofList ++ [k]

/-! ## Vocabulary: ghost edges -/

/-- The witness an edge `a → o` and an edge `o → b` give, from the keys of `a` and `b`: one when
both have a key and the keys differ, none otherwise. -/
def bridgeEntry : Option String → Option String → NodeRef → NodeRef →
    List ((String × String) × (NodeRef × NodeRef))
  | some x, some y, a, b => if x = y then [] else [((x, y), (a, b))]
  | _, _, _, _ => []

/-- **Glossary: Bridge witnesses** ([EXP-017], ruling D26 item 6). For a key function `key`, the
nodes `rs` and the edges `es`, every `((x, y), (a, b))` such that some node `o` without a key has
an edge `a → o` with `key a = x` and an edge `o → b` with `key b = y`, and `x ≠ y`: one entry per
(o, edge into o, edge out of o), in the order the spec scans them, nodes in their order, then the
edges into `o` in edge order, then the edges out of `o` in edge order. Edges are those of the
graph, of every arc type, in the direction drawn; `a` and `b` may be junctions. -/
def bridgeWitnesses (key : NodeRef → Option String) (rs : List NodeRef) (es : List XEdge) :
    List ((String × String) × (NodeRef × NodeRef)) :=
  rs.flatMap fun o =>
    if key o = none then
      es.flatMap fun ei =>
        if ei.dst = o then
          es.flatMap fun eo =>
            if eo.src = o then
              bridgeEntry (key ei.src) (key eo.dst) ei.src eo.dst
            else []
        else []
    else []

/-- **Glossary: Ghost edge** ([EXP-017]) for the ordered key pair `(x, y)` with anchors `a` and
`b`: from `a` to `b`, arc type `ghost`, clipped at `cluster_<sanitize x>` and
`cluster_<sanitize y>`. It is drawn invisible with no arrowhead; those are visual constants, and
its style row (`output`) and dash are not read for a ghost edge. -/
def ghostEdge (x y : String) (a b : NodeRef) : XEdge :=
  ⟨a, b, .ghost, .output, false, none, some (clusterId x), some (clusterId y)⟩

/-- The ghost edge of a witness. -/
def ghostEdgeOf (w : (String × String) × (NodeRef × NodeRef)) : XEdge :=
  ghostEdge w.1.1 w.1.2 w.2.1 w.2.2

/-! ## Lemmas: instance prefixes and chains -/

theorem lastCut_eq_none (l : List Char) : lastCut l = none ↔ '/' ∉ l := by
  induction l with
  | nil => simp [lastCut]
  | cons c cs ih =>
    unfold lastCut
    cases h : lastCut cs with
    | some u =>
      have : '/' ∈ cs := by
        by_contra hn; rw [← ih] at hn; rw [hn] at h; cases h
      simp [this]
    | none =>
      have hn : '/' ∉ cs := ih.mp h
      by_cases hc : c = '/'
      · simp [hc]
      · simp only [hc, if_false, List.mem_cons, not_or, true_iff]
        exact ⟨fun h => hc h.symm, hn⟩

/-- **The last cut**: `lastCut l = some u` exactly when `l` is `u`, a `/`, and a rest with no
`/`. -/
theorem lastCut_eq_some (l : List Char) (u : List Char) :
    lastCut l = some u ↔ ∃ r, l = u ++ '/' :: r ∧ '/' ∉ r := by
  induction l generalizing u with
  | nil => simp [lastCut]
  | cons c cs ih =>
    unfold lastCut
    cases h : lastCut cs with
    | some u' =>
      obtain ⟨r', hr', hn'⟩ := (ih u').mp h
      simp only [Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨r', by simp [hr'], hn'⟩
      · rintro ⟨r, hr, hn⟩
        rcases List.cons_eq_append_iff.mp hr with ⟨rfl, h2⟩ | ⟨v, rfl, hv⟩
        · simp only [List.cons.injEq] at h2
          obtain ⟨_, rfl⟩ := h2
          exact absurd (by rw [hr']; simp) hn
        · have := (ih v).mpr ⟨r, hv, hn⟩
          rw [h] at this
          cases this
          rfl
    | none =>
      have hn : '/' ∉ cs := (lastCut_eq_none cs).mp h
      by_cases hc : c = '/'
      · simp only [hc, if_true, Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨cs, by simp, hn⟩
        · rintro ⟨r, hr, _⟩
          rcases List.cons_eq_append_iff.mp hr with ⟨rfl, _⟩ | ⟨v, rfl, hv⟩
          · rfl
          · exact absurd (by rw [hv]; simp) hn
      · simp only [hc, if_false, reduceCtorEq, false_iff, not_exists, not_and]
        intro r hr _
        rcases List.cons_eq_append_iff.mp hr with ⟨rfl, h2⟩ | ⟨v, rfl, hv⟩
        · simp only [List.cons.injEq] at h2; exact hc h2.1.symm
        · exact hn (by rw [hv]; simp)

/-- **What the instance prefix is** ([EXP-016]): `instancePrefix s = some q` exactly when `q` is
not empty and `s` is `q`, a `/`, and a rest with no `/` (the part before the last `/`). -/
theorem instancePrefix_eq_some (s q : String) :
    instancePrefix s = some q ↔ q.toList ≠ [] ∧ ∃ r, s.toList = q.toList ++ '/' :: r ∧ '/' ∉ r := by
  unfold instancePrefix
  constructor
  · intro h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, h⟩ := h
    by_cases he : u.isEmpty
    · rw [if_pos he] at h; cases h
    · rw [if_neg he, Option.some.injEq] at h
      subst h
      rw [String.toList_ofList]
      refine ⟨by simpa using he, (lastCut_eq_some _ _).mp hu⟩
  · rintro ⟨hq, hs⟩
    rw [Option.bind_eq_some_iff]
    refine ⟨q.toList, (lastCut_eq_some _ _).mpr hs, ?_⟩
    have : q.toList.isEmpty = false := by simpa using hq
    rw [this]
    simp [String.ofList_toList]

/-- A name without `/` has no instance prefix. -/
theorem instancePrefix_eq_none_of (s : String) (h : '/' ∉ s.toList) : instancePrefix s = none := by
  unfold instancePrefix
  rw [(lastCut_eq_none _).mpr h]
  rfl

/-- The instance prefix of a name is a `/`-prefix of it. -/
theorem instancePrefix_isSlashPrefix {s q : String} (h : instancePrefix s = some q) :
    IsSlashPrefix q s := by
  obtain ⟨hq, r, hr, _⟩ := (instancePrefix_eq_some s q).mp h
  exact ⟨hq, ⟨r, by rw [hr]; simp⟩⟩

theorem isSlashPrefix_iff (q k : String) :
    IsSlashPrefix q k ↔ q.toList ≠ [] ∧ ∃ r, k.toList = q.toList ++ '/' :: r := by
  unfold IsSlashPrefix
  constructor
  · rintro ⟨hq, r, hr⟩
    exact ⟨hq, r, by rw [← hr]; simp⟩
  · rintro ⟨hq, r, hr⟩
    exact ⟨hq, r, by rw [hr]; simp⟩

/-- A `/`-prefix of a `/`-prefix is a `/`-prefix. -/
theorem IsSlashPrefix.trans {a b c : String} (hab : IsSlashPrefix a b) (hbc : IsSlashPrefix b c) :
    IsSlashPrefix a c := by
  rw [isSlashPrefix_iff] at *
  obtain ⟨ha, r, hr⟩ := hab
  obtain ⟨_, r', hr'⟩ := hbc
  exact ⟨ha, r ++ '/' :: r', by rw [hr', hr]; simp⟩

theorem mem_cutsAux (acc l u : List Char) :
    u ∈ cutsAux acc l ↔ ∃ v r, u = acc ++ v ∧ l = v ++ '/' :: r := by
  induction l generalizing acc with
  | nil => simp [cutsAux]
  | cons c cs ih =>
    simp only [cutsAux, List.mem_append, ih]
    constructor
    · rintro (h | ⟨v, r, rfl, rfl⟩)
      · split at h
        · rename_i hc
          rw [List.mem_singleton] at h
          exact ⟨[], cs, by simp [h], by simp [hc]⟩
        · cases h
      · exact ⟨c :: v, r, by simp, rfl⟩
    · rintro ⟨v, r, rfl, hl⟩
      rcases List.cons_eq_append_iff.mp hl with ⟨rfl, h2⟩ | ⟨v', rfl, hv⟩
      · simp only [List.cons.injEq] at h2
        obtain ⟨rfl, _⟩ := h2
        exact Or.inl (by simp)
      · exact Or.inr ⟨v', r, by simp, hv⟩

/-- **The chain of a key** is the key and its `/`-prefixes. -/
theorem mem_keyChain (k q : String) : q ∈ keyChain k ↔ q = k ∨ IsSlashPrefix q k := by
  rw [isSlashPrefix_iff]
  simp only [keyChain, List.mem_append, List.mem_map, List.mem_filter, mem_cutsAux,
    List.nil_append, List.mem_singleton, Bool.not_eq_true', List.isEmpty_eq_false_iff]
  constructor
  · rintro (⟨u, ⟨⟨v, r, rfl, hr⟩, hu⟩, rfl⟩ | h)
    · exact Or.inr ⟨by simpa using hu, r, by simp [hr]⟩
    · exact Or.inl h
  · rintro (h | ⟨hq, r, hr⟩)
    · exact Or.inr h
    · exact Or.inl ⟨q.toList, ⟨⟨q.toList, r, rfl, hr⟩, hq⟩, String.ofList_toList⟩

/-! ## Lemmas: bridge witnesses -/

section Ghosts

variable {key : NodeRef → Option String} {rs : List NodeRef} {es : List XEdge}

/-- What one pair of edges contributes. -/
theorem mem_bridgeEntry {kx ky : Option String} {a b : NodeRef}
    {w : (String × String) × (NodeRef × NodeRef)} :
    w ∈ bridgeEntry kx ky a b ↔ ∃ x y, kx = some x ∧ ky = some y ∧ x ≠ y ∧ w = ((x, y), (a, b)) := by
  cases kx with
  | none => simp [bridgeEntry]
  | some x =>
    cases ky with
    | none => simp [bridgeEntry]
    | some y =>
      by_cases hxy : x = y
      · simp [bridgeEntry, hxy]
      · simp [bridgeEntry, hxy]

/-- **The bridge witnesses**, one by one: an entry `((x, y), (a, b))` is there exactly when some
drawn node `o` without a key has an edge `a → o` and an edge `o → b`, with `key a = x`,
`key b = y` and `x ≠ y`. -/
theorem mem_bridgeWitnesses {w : (String × String) × (NodeRef × NodeRef)} :
    w ∈ bridgeWitnesses key rs es ↔
      ∃ o ∈ rs, key o = none ∧ ∃ ei ∈ es, ∃ eo ∈ es, ei.dst = o ∧ eo.src = o ∧
        key ei.src = some w.1.1 ∧ key eo.dst = some w.1.2 ∧ w.1.1 ≠ w.1.2 ∧
        w.2 = (ei.src, eo.dst) := by
  simp only [bridgeWitnesses, List.mem_flatMap, List.mem_ite_nil_right, mem_bridgeEntry]
  constructor
  · rintro ⟨o, ho, hko, ei, hei, hd, eo, heo, hs, x, y, hx, hy, hxy, rfl⟩
    exact ⟨o, ho, hko, ei, hei, eo, heo, hd, hs, hx, hy, hxy, rfl⟩
  · rintro ⟨o, ho, hko, ei, hei, eo, heo, hd, hs, hx, hy, hxy, hw⟩
    exact ⟨o, ho, hko, ei, hei, hd, eo, heo, hs, w.1.1, w.1.2, hx, hy, hxy, by rw [← hw]⟩

end Ghosts

/-! ## Lemmas: keys and IDs -/

/-- A junction has its transition's key. -/
@[simp] theorem nodeKey_junction (src : ClusterSource) (m : String → Option String) (t : String)
    (k : JKind) (i : Nat) : nodeKey src m (.junction t k i) = nodeKey src m (.trans t) := rfl

/-- The default source: the membership entry, else the instance prefix. -/
theorem clusterKey_auto (m : String → Option String) (n : String) :
    clusterKey .auto m n = (m n).or (instancePrefix n) := rfl

/-- The `metadata` source: the membership entry only. -/
theorem clusterKey_metadata (m : String → Option String) (n : String) :
    clusterKey .metadata m n = m n := rfl

/-- The `prefix` source: the instance prefix only. -/
theorem clusterKey_prefix (m : String → Option String) (n : String) :
    clusterKey .prefix m n = instancePrefix n := rfl

/-- Cluster IDs are equal exactly when the sanitised keys are. -/
theorem clusterId_inj (a b : String) : clusterId a = clusterId b ↔ sanitize a = sanitize b := by
  simp only [clusterId, ← String.toList_inj, String.toList_append]
  constructor
  · intro h; exact List.append_cancel_left h
  · intro h; rw [h]

end Libpetri.Spec
