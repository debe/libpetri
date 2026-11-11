import Libpetri.Reference.Export
import Libpetri.Spec.GlossaryExportCluster

set_option linter.missingDocs true

/-!
# Reference export: clusters and ghost edges (`spec/09-export.md`, EXP-016, EXP-017)

The cluster stage of the reference exporter. It groups the nodes of a composed net into nested
clusters by their cluster key, and adds one invisible ghost edge per ordered pair of clusters that
a keyless node bridges in one hop. It is written as the three runtime cluster builders run them:
`partition` and `register_prefix_chain` in the Rust crate `libpetri-export` (module
`cluster_builder`), with `cluster_key_of` of its `mapper` module; `ClusterBuilder.java`;
`cluster-builder.ts`. The three builders are the same loops (export design, exp-b map).

**Vocabulary.** The words the EXP-016 and EXP-017 blocks are stated in (`instancePrefix`,
`clusterKey`, `nodeKey`, `IsSlashPrefix`, `keyChain`, `clusterId`, `bridgeWitnesses`,
`ghostEdge`, `NoEmptySegment`) and the lemmas that characterise them are glossary vocabulary, in
`Spec/GlossaryExportCluster.lean`. This file is the witness model built on them.

**Reference.** The builder: `refClusterKeys` (every key in use and its
`/`-prefixes, first appearance first, as `register_prefix_chain` fills `prefix_order`),
`refClusters` (one cluster per key: its ID, its label, its parent key, its direct members),
`refGhostPairs` (Rust's `incoming_by_orphan` and `outgoing_by_orphan` lists, the orphan loop and the
first-witness map), `refGhosts`, the stage `refClusterStage` and the final exporter `refExport`.
The builder is parametric in the key function, so `ClusterStage.byKey` (another key rule) and
`ClusterStage.ofPairs` (another ghost loop) give the blocks their mutant exporters in one line.

**Not modelled.** Edge routing into clusters (`deepest_common_prefix`: which subgraph block an edge
is written in) is a property of the DOT text; the typed graph keeps one flat edge list. Cluster
styling is a visual constant. Sibling cluster order is stated by no requirement and differs between
the runtimes (ruling R2 (exp-b)); the model keeps Rust's order of first appearance.

**Empty segments (ruling D46).** A key with an empty `/`-segment (from a name such as `a//x` or
`http://host/x`) makes the Rust builder panic (`expect` in `partition`: `register_prefix_chain` skips
the empty segment and so never registers the key itself) and the Java builder throw; TypeScript
draws a cluster for the empty segment. This is a recorded runtime defect (RD-12 in
`spec/runtime-defects.md`). The model stays total and
coherent there (`keyChain` cuts at every `/`, so every key and its parent are clusters), and the
blocks assume `NoEmptySegment` of every key in use, under which `keyChain` is Rust's chain
(`registerChain`, decided on examples below).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## The reference cluster builder -/

/-- Append `x` unless it is already there (`if seen.insert(..) { accumulator.push(..) }`). -/
def insertNew {α : Type} [DecidableEq α] (acc : List α) (x : α) : List α :=
  if x ∈ acc then acc else acc ++ [x]

/-- Append the pair `p` unless its key is already there (the `ghost_anchors` map: the first
witness of a key wins, keys kept in order of first appearance). -/
def keepFirst {κ β : Type} [DecidableEq κ] (acc : List (κ × β)) (p : κ × β) : List (κ × β) :=
  if p.1 ∈ acc.map Prod.fst then acc else acc ++ [p]

/-- **The key of a drawn node**, as the runtimes' `node_id_to_prefix` map holds it: the key
`key` gives a node in `rs`, none for anything else (the map is filled while the nodes are
emitted). -/
def refKey (key : NodeRef → Option String) (rs : List NodeRef) (r : NodeRef) : Option String :=
  if r ∈ rs then key r else none

/-- **The cluster keys** (`prefix_order`): walking the nodes in order, the chain of each node's
key, each key once, at its first appearance; parents come before their children. -/
def refClusterKeys (key : NodeRef → Option String) (rs : List NodeRef) : List String :=
  ((rs.filterMap key).flatMap keyChain).foldl insertNew []

/-- **The cluster of key `k`**: ID `cluster_<sanitize k>`, label `k`, parent the instance prefix
of `k` (`parent_of`), direct members the nodes whose key is `k`, in node order. -/
def refCluster (key : NodeRef → Option String) (rs : List NodeRef) (k : String) : XCluster :=
  { key := k, id := clusterId k, label := k, parent := instancePrefix k,
    members := rs.filter fun r => key r = some k }

/-- **The clusters**: one per cluster key. -/
def refClusters (key : NodeRef → Option String) (rs : List NodeRef) : List XCluster :=
  (refClusterKeys key rs).map (refCluster key rs)

/-- The edges into `o` from a node with a key, as (source, key) in edge order
(`incoming_by_orphan`). -/
def refIncoming (key : NodeRef → Option String) (es : List XEdge) (o : NodeRef) :
    List (NodeRef × String) :=
  es.filterMap fun e => if e.dst = o then (key e.src).map (e.src, ·) else none

/-- The edges out of `o` into a node with a key, as (target, key) in edge order
(`outgoing_by_orphan`). -/
def refOutgoing (key : NodeRef → Option String) (es : List XEdge) (o : NodeRef) :
    List (NodeRef × String) :=
  es.filterMap fun e => if e.src = o then (key e.dst).map (e.dst, ·) else none

/-- The orphan loop of the runtimes: for each node without a key, in node order, each incoming
(a, x), each outgoing (b, y), with `x ≠ y`, the candidate `((x, y), (a, b))`. -/
def refGhostCandidates (key : NodeRef → Option String) (rs : List NodeRef) (es : List XEdge) :
    List ((String × String) × (NodeRef × NodeRef)) :=
  (rs.filter fun o => key o = none).flatMap fun o =>
    (refIncoming key es o).flatMap fun ax =>
      (refOutgoing key es o).filterMap fun bx =>
        if ax.2 = bx.2 then none else some ((ax.2, bx.2), (ax.1, bx.1))

/-- **The ghost pairs**: the first candidate of each ordered key pair, pairs in order of first
appearance (`ghost_keys` and `ghost_anchors`). -/
def refGhostPairs (key : NodeRef → Option String) (rs : List NodeRef) (es : List XEdge) :
    List ((String × String) × (NodeRef × NodeRef)) :=
  (refGhostCandidates key rs es).foldl keepFirst []

/-- **The ghost edges**: one per ghost pair, keys read from the drawn nodes. -/
def refGhosts (key : NodeRef → Option String) (rs : List NodeRef) (es : List XEdge) :
    List XEdge :=
  (refGhostPairs (refKey key rs) rs es).map ghostEdgeOf

/-! ## Lemmas: the folds -/

theorem mem_foldl_insertNew {α : Type} [DecidableEq α] (l : List α) (acc : List α) (x : α) :
    x ∈ l.foldl insertNew acc ↔ x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons y l ih =>
    rw [List.foldl_cons, ih]
    unfold insertNew
    split
    · rename_i hy
      simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hy
        · exact Or.inr h
    · simp [or_assoc]

theorem nodup_foldl_insertNew {α : Type} [DecidableEq α] (l : List α) (acc : List α)
    (h : acc.Nodup) : (l.foldl insertNew acc).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons y l ih =>
    rw [List.foldl_cons]
    apply ih
    unfold insertNew
    split
    · exact h
    · rw [List.nodup_append]
      refine ⟨h, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro hab; subst hab; contradiction

theorem mem_foldl_keepFirst {κ β : Type} [DecidableEq κ] (l acc : List (κ × β)) (p : κ × β) :
    p ∈ l.foldl keepFirst acc ↔
      p ∈ acc ∨ (p.1 ∉ acc.map Prod.fst ∧ l.find? (fun q => decide (q.1 = p.1)) = some p) := by
  induction l generalizing acc with
  | nil => simp
  | cons q l ih =>
    rw [List.foldl_cons, ih, List.find?_cons]
    unfold keepFirst
    by_cases hq : q.1 ∈ acc.map Prod.fst
    · rw [if_pos hq]
      by_cases hqp : q.1 = p.1
      · simp only [hqp, decide_true]
        rw [hqp] at hq
        simp [hq]
      · simp [hqp]
    · rw [if_neg hq]
      by_cases hqp : q.1 = p.1
      · simp only [hqp, decide_true, List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_singleton, Option.some.injEq]
        rw [hqp] at hq
        constructor
        · rintro ((h | rfl) | ⟨h, _⟩)
          · exact Or.inl h
          · exact Or.inr ⟨hq, rfl⟩
          · simp at h
        · rintro (h | ⟨_, rfl⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr rfl)
      · simp only [hqp, decide_false, List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_singleton, not_or]
        constructor
        · rintro ((h | rfl) | ⟨⟨h1, _⟩, h3⟩)
          · exact Or.inl h
          · exact absurd rfl hqp
          · exact Or.inr ⟨h1, h3⟩
        · rintro (h | ⟨h1, h3⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr ⟨⟨h1, fun h => hqp h.symm⟩, h3⟩

theorem nodup_foldl_keepFirst {κ β : Type} [DecidableEq κ] (l acc : List (κ × β))
    (h : (acc.map Prod.fst).Nodup) : ((l.foldl keepFirst acc).map Prod.fst).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons q l ih =>
    rw [List.foldl_cons]
    apply ih
    unfold keepFirst
    split
    · exact h
    · rw [List.map_append, List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      intro hab; subst hab; contradiction

/-! ## Lemmas: the clusters -/

section Clusters

variable {key : NodeRef → Option String} {rs : List NodeRef}

/-- **The cluster keys** are the keys of the nodes and their `/`-prefixes. -/
theorem mem_refClusterKeys {k : String} :
    k ∈ refClusterKeys key rs ↔
      ∃ r ∈ rs, ∃ K, key r = some K ∧ (k = K ∨ IsSlashPrefix k K) := by
  unfold refClusterKeys
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_filterMap, mem_keyChain]
  constructor
  · rintro ⟨K, ⟨r, hr, hK⟩, h⟩; exact ⟨r, hr, K, hK, h⟩
  · rintro ⟨r, hr, K, hK, h⟩; exact ⟨K, ⟨r, hr, hK⟩, h⟩

/-- Each cluster key appears once. -/
theorem refClusterKeys_nodup : (refClusterKeys key rs).Nodup :=
  nodup_foldl_insertNew _ _ List.nodup_nil

/-- The keys of the clusters, in order. -/
theorem refClusters_keys : (refClusters key rs).map XCluster.key = refClusterKeys key rs := by
  simp [refClusters, refCluster, Function.comp_def]

/-- **The clusters, one per key.** -/
theorem mem_refClusters {c : XCluster} :
    c ∈ refClusters key rs ↔ ∃ k ∈ refClusterKeys key rs, c = refCluster key rs k := by
  simp only [refClusters, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

/-- **The fields of a cluster**: its ID is `cluster_<sanitize key>`, its label is its key, its
parent is the instance prefix of its key, and its direct members are exactly the drawn nodes whose
key is its key. -/
theorem refClusters_fields {c : XCluster} (hc : c ∈ refClusters key rs) :
    c.id = clusterId c.key ∧ c.label = c.key ∧ c.parent = instancePrefix c.key ∧
      ∀ r, r ∈ c.members ↔ r ∈ rs ∧ key r = some c.key := by
  obtain ⟨k, _, rfl⟩ := mem_refClusters.mp hc
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r
  simp [refCluster]

/-- **Every key in use has its cluster.** -/
theorem refClusters_of_key {r : NodeRef} {K : String} (hr : r ∈ rs)
    (hK : key r = some K) : ∃ c ∈ refClusters key rs, c.key = K :=
  ⟨refCluster key rs K, mem_refClusters.mpr ⟨K, mem_refClusterKeys.mpr ⟨r, hr, K, hK, Or.inl rfl⟩,
    rfl⟩, rfl⟩

/-- **Nesting**: the parent key of a cluster is the key of a cluster. -/
theorem refClusters_parent {c : XCluster} (hc : c ∈ refClusters key rs) {p : String}
    (hp : c.parent = some p) : ∃ c' ∈ refClusters key rs, c'.key = p := by
  obtain ⟨k, hk, rfl⟩ := mem_refClusters.mp hc
  have hpk : IsSlashPrefix p k := instancePrefix_isSlashPrefix hp
  obtain ⟨r, hr, K, hK, h⟩ := mem_refClusterKeys.mp hk
  refine ⟨refCluster key rs p, mem_refClusters.mpr ⟨p, ?_, rfl⟩, rfl⟩
  refine mem_refClusterKeys.mpr ⟨r, hr, K, hK, Or.inr ?_⟩
  rcases h with rfl | h
  · exact hpk
  · exact hpk.trans h

/-- **One cluster per key**: two clusters with one key are one cluster. -/
theorem refClusters_key_inj {c c' : XCluster} (hc : c ∈ refClusters key rs)
    (hc' : c' ∈ refClusters key rs) (h : c.key = c'.key) : c = c' := by
  obtain ⟨k, _, rfl⟩ := mem_refClusters.mp hc
  obtain ⟨k', _, rfl⟩ := mem_refClusters.mp hc'
  simp only [refCluster] at h
  subst h; rfl

/-- **A drawn node is a direct member of exactly the cluster of its key**, and of none when it has
no key. -/
theorem refClusters_member {c : XCluster} (hc : c ∈ refClusters key rs) {r : NodeRef}
    (hr : r ∈ rs) : r ∈ c.members ↔ key r = some c.key := by
  rw [(refClusters_fields hc).2.2.2]
  exact ⟨fun h => h.2, fun h => ⟨hr, h⟩⟩

/-- **No key, no cluster.** -/
theorem refClusters_eq_nil :
    refClusters key rs = [] ↔ ∀ r ∈ rs, key r = none := by
  constructor
  · intro h r hr
    cases hK : key r with
    | none => rfl
    | some K =>
      obtain ⟨c, hc, _⟩ := refClusters_of_key hr hK
      rw [h] at hc; cases hc
  · intro h
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    obtain ⟨k, hk, _⟩ := mem_refClusters.mp hc
    obtain ⟨r, hr, K, hK, _⟩ := mem_refClusterKeys.mp hk
    rw [h r hr] at hK; cases hK

end Clusters

/-! ## Lemmas: the ghost edges -/

section Ghosts

variable {key : NodeRef → Option String} {rs : List NodeRef} {es : List XEdge}

/-- The `incoming` list, read edge by edge. -/
theorem refIncoming_flatMap {β : Type} (o : NodeRef) (F : NodeRef × String → List β) :
    (refIncoming key es o).flatMap F =
      es.flatMap fun ei => if ei.dst = o then
        (match key ei.src with | some x => F (ei.src, x) | none => []) else [] := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [refIncoming, List.filterMap_cons, List.flatMap_cons] at ih ⊢
    rw [← ih]
    by_cases hd : e.dst = o
    · simp only [hd, if_true]
      cases key e.src <;> simp
    · simp [hd]

/-- The `outgoing` list, read edge by edge. -/
theorem refOutgoing_filterMap {β : Type} (o : NodeRef) (G : NodeRef × String → Option β) :
    (refOutgoing key es o).filterMap G =
      es.flatMap fun eo => if eo.src = o then
        (match key eo.dst with | some y => (G (eo.dst, y)).toList | none => []) else [] := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [refOutgoing, List.filterMap_cons, List.flatMap_cons] at ih ⊢
    rw [← ih]
    by_cases hs : e.src = o
    · simp only [hs, if_true]
      cases key e.dst with
      | none => simp
      | some y =>
        show List.filterMap G ((e.dst, y) :: _) = (G (e.dst, y)).toList ++ _
        rw [List.filterMap_cons]
        cases G (e.dst, y) <;> rfl
    · simp [hs]

theorem flatMap_filter' {α β : Type} (l : List α) (p : α → Bool) (f : α → List β) :
    (l.filter p).flatMap f = l.flatMap fun a => if p a then f a else [] := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/-- The runtimes' orphan loop over the `incoming` and `outgoing` lists scans the witnesses in the
spec's order: the candidates are the bridge witnesses. -/
theorem refGhostCandidates_eq : refGhostCandidates key rs es = bridgeWitnesses key rs es := by
  unfold refGhostCandidates bridgeWitnesses
  rw [flatMap_filter']
  apply List.flatMap_congr
  intro o _
  by_cases hko : key o = none
  · simp only [hko, decide_true, if_true]
    rw [refIncoming_flatMap]
    apply List.flatMap_congr
    intro ei _
    by_cases hd : ei.dst = o
    · simp only [hd, if_true]
      cases hx : key ei.src with
      | none =>
        symm
        rw [List.flatMap_eq_nil_iff]
        intro eo _
        split <;> simp [bridgeEntry]
      | some x =>
        simp only
        rw [refOutgoing_filterMap]
        apply List.flatMap_congr
        intro eo _
        by_cases hs : eo.src = o
        · simp only [hs, if_true]
          cases key eo.dst with
          | none => simp [bridgeEntry]
          | some y => by_cases hxy : x = y <;> simp [hxy, bridgeEntry]
        · simp [hs]
    · simp [hd]
  · simp [hko]

/-- **The ghost pairs** are the first bridge witness of each ordered key pair: an entry is a ghost
pair exactly when it is the first witness, in the spec's scan order, whose key pair is its key
pair. -/
theorem mem_refGhostPairs {p : (String × String) × (NodeRef × NodeRef)} :
    p ∈ refGhostPairs key rs es ↔
      (bridgeWitnesses key rs es).find? (fun q => decide (q.1 = p.1)) = some p := by
  unfold refGhostPairs
  rw [mem_foldl_keepFirst, refGhostCandidates_eq]
  simp

/-- **At most one ghost pair per ordered key pair.** -/
theorem refGhostPairs_nodup : ((refGhostPairs key rs es).map Prod.fst).Nodup :=
  nodup_foldl_keepFirst _ _ List.nodup_nil

/-- Every ghost pair is a bridge witness. -/
theorem refGhostPairs_witness {p : (String × String) × (NodeRef × NodeRef)}
    (hp : p ∈ refGhostPairs key rs es) : p ∈ bridgeWitnesses key rs es :=
  List.mem_of_find?_eq_some (mem_refGhostPairs.mp hp)

/-- **A ghost pair for each bridged ordered key pair, and only for those**: `(x, y)` is the key
pair of a ghost pair exactly when some bridge witness has key pair `(x, y)`. -/
theorem refGhostPairs_key {xy : String × String} :
    xy ∈ (refGhostPairs key rs es).map Prod.fst ↔ ∃ w ∈ bridgeWitnesses key rs es, w.1 = xy := by
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, refGhostPairs_witness hp, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    cases h : (bridgeWitnesses key rs es).find? (fun q => decide (q.1 = w.1)) with
    | none =>
      rw [List.find?_eq_none] at h
      exact absurd (by simp) (h w hw)
    | some p =>
      have hp1 : p.1 = w.1 := by simpa using List.find?_some h
      refine ⟨p, mem_refGhostPairs.mpr ?_, hp1⟩
      rw [hp1]; exact h

/-- The ends of a ghost pair: its anchors have its keys, and the keys differ. -/
theorem refGhostPairs_keys {p : (String × String) × (NodeRef × NodeRef)}
    (hp : p ∈ refGhostPairs key rs es) :
    key p.2.1 = some p.1.1 ∧ key p.2.2 = some p.1.2 ∧ p.1.1 ≠ p.1.2 := by
  obtain ⟨o, _, _, ei, _, eo, _, _, _, hx, hy, hxy, hab⟩ :=
    mem_bridgeWitnesses.mp (refGhostPairs_witness hp)
  rw [hab]
  exact ⟨hx, hy, hxy⟩

/-- `flatMap` of a guarded function over a list on which the guard never holds is empty. -/
theorem flatMap_ite_nil {α β : Type} (l : List α) (P : α → Prop) [DecidablePred P]
    (f : α → List β) (h : ∀ a ∈ l, ¬ P a) : (l.flatMap fun a => if P a then f a else []) = [] := by
  rw [List.flatMap_eq_nil_iff]
  intro a ha
  rw [if_neg (h a ha)]

/-- **Edges between keyed nodes bridge nothing**: appending edges whose two ends both have a key
(ghost edges are such edges) leaves the bridge witnesses as they are. -/
theorem bridgeWitnesses_append_keyed {gs : List XEdge}
    (hg : ∀ e ∈ gs, key e.src ≠ none ∧ key e.dst ≠ none) :
    bridgeWitnesses key rs (es ++ gs) = bridgeWitnesses key rs es := by
  unfold bridgeWitnesses
  apply List.flatMap_congr
  intro o _
  split
  · rename_i hko
    rw [List.flatMap_append, flatMap_ite_nil gs _ _
      (fun e he hd => (hg e he).2 (by rw [hd]; exact hko)), List.append_nil]
    apply List.flatMap_congr
    intro ei _
    split
    · rw [List.flatMap_append, flatMap_ite_nil gs _ _
        (fun e he hs => (hg e he).1 (by rw [hs]; exact hko)), List.append_nil]
    · rfl
  · rfl

/-- The bridge witnesses depend only on the keys of the nodes and of the edges' ends. -/
theorem bridgeWitnesses_congr {key' : NodeRef → Option String}
    (hr : ∀ o ∈ rs, key o = key' o)
    (he : ∀ e ∈ es, key e.src = key' e.src ∧ key e.dst = key' e.dst) :
    bridgeWitnesses key rs es = bridgeWitnesses key' rs es := by
  unfold bridgeWitnesses
  apply List.flatMap_congr
  intro o ho
  rw [hr o ho]
  split
  · apply List.flatMap_congr
    intro ei hei
    split
    · apply List.flatMap_congr
      intro eo heo
      split
      · rw [(he ei hei).1, (he eo heo).2]
      · rfl
    · rfl
  · rfl

end Ghosts

/-! ## The stage and the exporter -/

section Stage

variable {key : NodeRef → Option String} {rs : List NodeRef} {es : List XEdge}

/-- The key of a drawn node is its node key; anything else has none. -/
theorem refKey_eq_some {r : NodeRef} {k : String} (h : refKey key rs r = some k) :
    r ∈ rs ∧ key r = some k := by
  unfold refKey at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

theorem refKey_of_mem {r : NodeRef} (h : r ∈ rs) : refKey key rs r = key r := by
  simp [refKey, h]

/-- **The ghost edges**: one per ghost pair, from its first anchor to its second, clipped at the
clusters of its keys. -/
theorem mem_refGhosts {e : XEdge} :
    e ∈ refGhosts key rs es ↔ ∃ p ∈ refGhostPairs (refKey key rs) rs es, e = ghostEdgeOf p := by
  simp only [refGhosts, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

/-- Every added edge is a ghost edge. -/
theorem refGhosts_arc {e : XEdge} (he : e ∈ refGhosts key rs es) : e.arc = .ghost := by
  obtain ⟨p, _, rfl⟩ := mem_refGhosts.mp he
  rfl

/-- Every ghost edge joins two drawn nodes with keys: its ends have the keys it is clipped at. -/
theorem refGhosts_ends_keyed {e : XEdge} (he : e ∈ refGhosts key rs es) :
    ∃ x y, x ≠ y ∧ e.src ∈ rs ∧ e.dst ∈ rs ∧ key e.src = some x ∧
      key e.dst = some y ∧ e.ltail = some (clusterId x) ∧
      e.lhead = some (clusterId y) := by
  obtain ⟨p, hp, rfl⟩ := mem_refGhosts.mp he
  obtain ⟨ha, hb, hxy⟩ := refGhostPairs_keys hp
  obtain ⟨ha1, ha2⟩ := refKey_eq_some ha
  obtain ⟨hb1, hb2⟩ := refKey_eq_some hb
  exact ⟨p.1.1, p.1.2, hxy, ha1, hb1, ha2, hb2, rfl, rfl⟩

/-- Every ghost edge joins two drawn nodes. -/
theorem refGhosts_ends {e : XEdge} (he : e ∈ refGhosts key rs es) : e.src ∈ rs ∧ e.dst ∈ rs := by
  obtain ⟨_, _, _, h1, h2, _⟩ := refGhosts_ends_keyed he
  exact ⟨h1, h2⟩

/-- **No key, no ghost edge.** -/
theorem refGhosts_eq_nil (h : ∀ r ∈ rs, key r = none) :
    refGhosts key rs es = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro e he
  obtain ⟨_, _, _, h1, _, h2, _⟩ := refGhosts_ends_keyed he
  rw [h _ h1] at h2
  cases h2

end Stage

/-- **The cluster stage of a key function** `kf` (a key per cluster source, net and node): the
clusters `refClusters` and the ghost edges `refGhosts` of the key `kf src X`, with the two proofs
the stage contract asks for. Mutant stages for the blocks change the key function (a first-`/`
key, junctions without a key, metadata only by default). -/
def ClusterStage.byKey (kf : ClusterSource → ExportNet → NodeRef → Option String) :
    ClusterStage :=
  ⟨fun src X rs _ => refClusters (kf src X) rs, fun src X rs es => refGhosts (kf src X) rs es,
    fun _ _ _ _ _ he => refGhosts_arc he, fun _ _ _ _ _ he => refGhosts_ends he⟩

/-- **A cluster stage from any ghost pairs**, for the blocks' mutants of the ghost-edge loop (no
dedup, unordered pairs, a ghost edge for one cluster, the last witness): the clusters of the key
function `kf`, and one ghost edge per pair `pairs` gives (from the key read off the drawn nodes,
the drawn nodes and the edges) whose two anchors are drawn nodes. -/
def ClusterStage.ofPairs (kf : ClusterSource → ExportNet → NodeRef → Option String)
    (pairs : (NodeRef → Option String) → List NodeRef → List XEdge →
      List ((String × String) × (NodeRef × NodeRef))) : ClusterStage where
  clusters src X rs _ := refClusters (kf src X) rs
  ghosts src X rs es :=
    ((pairs (refKey (kf src X) rs) rs es).filter
      fun p => decide (p.2.1 ∈ rs) && decide (p.2.2 ∈ rs)).map ghostEdgeOf
  ghosts_arc := by
    intro _ _ _ _ e he
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
    rfl
  ghosts_ends := by
    intro _ _ _ _ e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    have := (List.mem_filter.mp hp).2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this

/-- **The reference cluster stage** (witness model): the stage of the node key `nodeKey`. -/
def refClusterStage : ClusterStage := ClusterStage.byKey fun src X => nodeKey src X.member

/-- **The reference exporter** (witness model): the mapper of `Reference/Export.lean` with the
reference cluster stage, the exporter all three runtimes run. -/
def refExport : Exporter := refExportWith refClusterStage

#spec_witness refExport

/-! ## Lemmas: the reference exporter -/

section Exporter

variable {cfg : ExportCfg} {X : ExportNet}

theorem refExport_eq : refExport = refExportWith refClusterStage := rfl

theorem refExport_edges :
    (refExport cfg X).edges =
      refEdges X ++ refGhosts (nodeKey cfg.cluster X.member) (refNodeRefs X) (refEdges X) := rfl

theorem refExport_clusters :
    (refExport cfg X).clusters = refClusters (nodeKey cfg.cluster X.member) (refNodeRefs X) := rfl

/-- What the nodes of the reference exporter stand for. -/
theorem refExport_nodeRefs : (refExport cfg X).nodes.map XNode.ref = refNodeRefs X :=
  refNodes_refs

/-- A place some arc of a transition of `X` touches is drawn. -/
theorem place_mem_refNodeRefs {t : ExportTrans} (ht : t ∈ X.trans) {p : String}
    (hp : p ∈ t.touched) : NodeRef.place p ∈ refNodeRefs X := by
  unfold refNodeRefs
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ?_))
  exact mem_refPlaceNames.mpr (Or.inr ⟨t, ht, hp⟩)

/-- A transition of `X` is drawn. -/
theorem trans_mem_refNodeRefs {t : ExportTrans} (ht : t ∈ X.trans) :
    NodeRef.trans t.name ∈ refNodeRefs X := by
  unfold refNodeRefs
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map_of_mem (f := fun t : ExportTrans => NodeRef.trans t.name) ht))

/-- A junction the emitter draws for a transition of `X` is drawn. -/
theorem junction_mem_refNodeRefs {t : ExportTrans} (ht : t ∈ X.trans) {k : JKind} {i : Nat}
    (hj : (k, i) ∈ (refEmit.ofTrans t).junctions) : NodeRef.junction t.name k i ∈ refNodeRefs X := by
  unfold refNodeRefs
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ht, ?_⟩)
  exact List.mem_map.mpr ⟨(k, i), hj, rfl⟩

/-- **Both ends of every edge of a transition are drawn nodes.** -/
theorem refEdges_ends_mem {e : XEdge} (he : e ∈ refEdges X) :
    e.src ∈ refNodeRefs X ∧ e.dst ∈ refNodeRefs X := by
  obtain ⟨t, ht, he⟩ := mem_refEdges.mp he
  have hT : ∀ p, p ∈ t.core.inputs.map (·.place) ∨ p ∈ t.outLeaves ∨ p ∈ t.core.inhibitors ∨
      p ∈ t.core.reads ∨ p ∈ t.core.resets → NodeRef.place p ∈ refNodeRefs X := by
    intro p hp
    apply place_mem_refNodeRefs ht
    simp only [ExportTrans.touched, List.mem_append]
    rcases hp with h | h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  rcases mem_refTransEdges.mp he with ⟨s, hs, rfl⟩ | h | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ |
      ⟨p, hp, _, rfl⟩
  · exact ⟨hT _ (Or.inl (List.mem_map_of_mem hs)), trans_mem_refNodeRefs ht⟩
  · obtain ⟨h1, h2⟩ := refEmit_ofTrans_ends h
    constructor
    · rcases h1 with h1 | ⟨k, i, h1, hj⟩
      · rw [h1]; exact trans_mem_refNodeRefs ht
      · rw [h1]; exact junction_mem_refNodeRefs ht hj
    · rcases h2 with ⟨p, h2⟩ | ⟨k, i, h2, hj⟩
      · rw [h2]
        apply hT
        refine Or.inr (Or.inl ?_)
        rw [← refEmit_ofTrans_places]
        exact List.mem_filterMap.mpr ⟨e, h, by simp [XEdge.placeTarget, h2, NodeRef.place?]⟩
      · rw [h2]; exact junction_mem_refNodeRefs ht hj
  · exact ⟨hT _ (Or.inr (Or.inr (Or.inl hp))), trans_mem_refNodeRefs ht⟩
  · exact ⟨hT _ (Or.inr (Or.inr (Or.inr (Or.inl hp)))), trans_mem_refNodeRefs ht⟩
  · exact ⟨trans_mem_refNodeRefs ht, hT _ (Or.inr (Or.inr (Or.inr (Or.inr hp))))⟩

/-- **The bridge witnesses of the exported graph** (over its nodes and all its edges, ghost edges
included, keys by `nodeKey`) are those the reference builder scans (over the drawn nodes and the
edges of the transitions, keys read from the drawn nodes). -/
theorem refExport_witnesses :
    bridgeWitnesses (nodeKey cfg.cluster X.member) ((refExport cfg X).nodes.map XNode.ref)
        (refExport cfg X).edges =
      bridgeWitnesses (refKey (nodeKey cfg.cluster X.member) (refNodeRefs X)) (refNodeRefs X) (refEdges X) := by
  rw [refExport_nodeRefs, refExport_edges, bridgeWitnesses_append_keyed]
  · symm
    apply bridgeWitnesses_congr
    · intro o ho; exact refKey_of_mem ho
    · intro e he
      obtain ⟨h1, h2⟩ := refEdges_ends_mem he
      exact ⟨refKey_of_mem h1, refKey_of_mem h2⟩
  · intro e he
    obtain ⟨x, y, _, _, _, hx, hy, _⟩ := refGhosts_ends_keyed he
    rw [hx, hy]
    exact ⟨nofun, nofun⟩

/-- The same over the non-ghost edges of the exported graph. -/
theorem refExport_witnesses_nonGhost :
    bridgeWitnesses (nodeKey cfg.cluster X.member) ((refExport cfg X).nodes.map XNode.ref)
        ((refExport cfg X).edges.filter fun e => e.arc != .ghost) =
      bridgeWitnesses (refKey (nodeKey cfg.cluster X.member) (refNodeRefs X)) (refNodeRefs X) (refEdges X) := by
  rw [refExport_eq, refExportWith_nonGhost, ← refExport_eq, refExport_nodeRefs]
  symm
  apply bridgeWitnesses_congr
  · intro o ho; exact refKey_of_mem ho
  · intro e he
    obtain ⟨h1, h2⟩ := refEdges_ends_mem he
    exact ⟨refKey_of_mem h1, refKey_of_mem h2⟩

/-- **The ghost edges of the reference exporter** ([EXP-017] lines 2 to 4): an edge of the exported
graph is a ghost edge exactly when it is the ghost edge of a pair that is the first bridge witness
of its ordered key pair, the witnesses read off the exported graph itself. -/
theorem refExport_ghost_iff {e : XEdge} :
    (e ∈ (refExport cfg X).edges ∧ e.arc = .ghost) ↔
      ∃ p, e = ghostEdgeOf p ∧
        (bridgeWitnesses (nodeKey cfg.cluster X.member) ((refExport cfg X).nodes.map XNode.ref)
          (refExport cfg X).edges).find? (fun q => decide (q.1 = p.1)) = some p := by
  rw [refExport_witnesses]
  constructor
  · rintro ⟨he, hg⟩
    rw [refExport_edges, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨t, _, he⟩ := mem_refEdges.mp he
      exact absurd hg (refTransEdges_ne_ghost he)
    · obtain ⟨p, hp, rfl⟩ := mem_refGhosts.mp he
      exact ⟨p, rfl, mem_refGhostPairs.mp hp⟩
  · rintro ⟨p, rfl, hp⟩
    refine ⟨?_, rfl⟩
    rw [refExport_edges]
    exact List.mem_append_right _ (mem_refGhosts.mpr ⟨p, mem_refGhostPairs.mpr hp, rfl⟩)

/-- **The ghost edges of the reference exporter, in order**: the edges of arc type `ghost` are the
ghost edges of the ghost pairs. -/
theorem refExport_ghosts :
    (refExport cfg X).edges.filter (fun e => e.arc == .ghost) =
      (refGhostPairs (refKey (nodeKey cfg.cluster X.member) (refNodeRefs X)) (refNodeRefs X) (refEdges X)).map
        ghostEdgeOf := by
  rw [refExport_edges, List.filter_append]
  have h1 : (refEdges X).filter (fun e => e.arc == .ghost) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    obtain ⟨t, _, he⟩ := mem_refEdges.mp he
    simpa using refTransEdges_ne_ghost he
  have h2 : (refGhosts (nodeKey cfg.cluster X.member) (refNodeRefs X) (refEdges X)).filter
      (fun e => e.arc == .ghost) = refGhosts (nodeKey cfg.cluster X.member) (refNodeRefs X) (refEdges X) := by
    rw [List.filter_eq_self]
    intro e he
    simp [refGhosts_arc he]
  rw [h1, h2, List.nil_append]
  rfl

/-- **Clustering changes no node** ([EXP-016]): the nodes are those of the exporter without
clustering. -/
theorem refExport_nodes_flat : (refExport cfg X).nodes = (refExportFlat cfg X).nodes := rfl

/-- **Clustering changes no non-ghost edge** ([EXP-016], [EXP-017]): the non-ghost edges are those
of the exporter without clustering, in order. -/
theorem refExport_nonGhost_flat :
    (refExport cfg X).edges.filter (fun e => e.arc != .ghost) =
      (refExportFlat cfg X).edges.filter (fun e => e.arc != .ghost) := by
  rw [refExport_eq, refExportFlat, refExportWith_nonGhost, refExportWith_nonGhost]

/-- **With no node key, the reference exporter is the exporter without clustering**: no cluster,
no ghost edge. -/
theorem refExport_eq_flat (h : ∀ r ∈ refNodeRefs X, nodeKey cfg.cluster X.member r = none) :
    refExport cfg X = refExportFlat cfg X := by
  have hc : refClusters (nodeKey cfg.cluster X.member) (refNodeRefs X) = [] :=
    refClusters_eq_nil.mpr h
  have hg : refGhosts (nodeKey cfg.cluster X.member) (refNodeRefs X) (refEdges X) = [] := refGhosts_eq_nil h
  simp only [refExport, refExportFlat, refExportWith, refClusterStage, ClusterStage.byKey,
    ClusterStage.flat]
  rw [hc, hg]

/-- Cluster source `none` keys nothing. -/
theorem nodeKey_none (m : String → Option String) (r : NodeRef) : nodeKey .none m r = none := rfl

/-- **Cluster source `none` gives the exporter without clustering** ([EXP-016]). -/
theorem refExport_source_none (h : cfg.cluster = .none) : refExport cfg X = refExportFlat cfg X :=
  refExport_eq_flat fun r _ => by rw [h]; rfl

end Exporter

/-! ## Rust's prefix chain, and the empty-segment defect -/

/-- The `/`-segments of a name, empty ones included (`str::split('/')`). -/
def splitSlash : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    match splitSlash cs with
    | s :: ss => if c = '/' then [] :: s :: ss else (c :: s) :: ss
    | [] => [[c]]

/-- `register_prefix_chain` of the Rust builder (and its Java and TypeScript mirrors): the
non-empty segments joined by `/`, each partial join once. It skips an empty segment, so on a key
with one it never registers the key itself; the builder then fails at the node's key (`expect`),
the recorded defect behind the D46 assumption (RD-12 in `spec/runtime-defects.md`). -/
def registerChain (k : String) : List String :=
  ((splitSlash k.toList).foldl
      (fun (acc : List Char × List (List Char)) seg =>
        if seg.isEmpty then acc
        else
          let b := if acc.1.isEmpty then seg else acc.1 ++ '/' :: seg
          (b, acc.2 ++ [b]))
      ([], [])).2.map String.ofList

/-- On keys without an empty segment the model's chain is Rust's. -/
example : registerChain "outer/inner/leaf" = keyChain "outer/inner/leaf" ∧
    keyChain "outer/inner/leaf" = ["outer", "outer/inner", "outer/inner/leaf"] ∧
    registerChain "b1" = keyChain "b1" ∧ NoEmptySegment "outer/inner/leaf" := by decide

/-- On a name with an empty segment (`a//x`, key `a/`) Rust's chain lacks the key, so the Rust
builder panics; the model keeps a cluster for it. `NoEmptySegment` rules the key out. -/
example : instancePrefix "a//x" = some "a/" ∧ registerChain "a/" = ["a"] ∧
    keyChain "a/" = ["a", "a/"] ∧ ¬ NoEmptySegment "a/" := by decide

/-- The instance prefix: before the last `/`; none without `/` or with only a leading one. -/
example : instancePrefix "producer1/internal" = some "producer1" ∧
    instancePrefix "outer/inner/leaf" = some "outer/inner" ∧ instancePrefix "flat" = none ∧
    instancePrefix "" = none ∧ instancePrefix "/" = none ∧ instancePrefix "/x" = none := by decide

/-! ## Worked examples -/

/-- A transition `name` with one input place `i` and the output tree `o`. -/
def clusterExTrans (name i : String) (o : OutTree) : ExportTrans :=
  { core := ⟨name, [⟨i, .one⟩], [], [], []⟩, out := some o }

/-- Two instances `b1` and `b2`, an orphan transition `bridge` between them, a second orphan
`bridge2` bridging the same pair, an orphan `back` bridging the reverse pair, an orphan `loop`
inside `b1`, a nested instance `outer/inner`, a clustered `Xor` transition `b2/split`, and an
orphan `Xor` transition `fan` from `b1` into `b2` and `outer`. -/
def clusterExNet : ExportNet :=
  { trans := [clusterExTrans "b1/work" "b1/in" (.place "b1/out"),
              clusterExTrans "bridge" "b1/out" (.place "b2/in"),
              clusterExTrans "bridge2" "b1/out" (.place "b2/in"),
              clusterExTrans "back" "b2/in" (.place "b1/in"),
              clusterExTrans "loop" "b1/in" (.place "b1/out"),
              clusterExTrans "outer/inner/t" "outer/inner/p" (.place "outer/q"),
              clusterExTrans "b2/split" "b2/in" (.xor [.place "b2/x", .place "b2/y"]),
              clusterExTrans "fan" "b1/out" (.xor [.place "b2/in", .place "outer/q"])] }

/-- The clusters of the example: `b1`, `outer`, `outer/inner` nested in it, and `b2`, with their
IDs, labels, parents and direct members; the junction of `b2/split` sits in `b2`, the orphans at
top level, `outer/inner/p` in `outer/inner` and not in `outer`. The order is the order of first
appearance over the mapper's node order (not stated by the spec). -/
theorem refExport_example_clusters :
    (refExport {} clusterExNet).clusters.map
        (fun c => (c.key, c.id, c.label, c.parent, c.members.map nodeId)) =
      [("b1", "cluster_b1", "b1", none, ["p_b1_in", "p_b1_out", "t_b1_work"]),
       ("outer", "cluster_outer", "outer", none, ["p_outer_q"]),
       ("outer/inner", "cluster_outer_inner", "outer/inner", some "outer",
         ["p_outer_inner_p", "t_outer_inner_t"]),
       ("b2", "cluster_b2", "b2", none,
         ["p_b2_x", "p_b2_y", "p_b2_in", "t_b2_split", "j_b2_split__xor_0"])] := by
  decide

/-- The ghost edges of the example: one for `(b1, b2)` (three bridges, one edge, anchored at the
first witness), one for `(b2, b1)`, none for the orphan `loop` with `b1` on both sides, none
for the orphan `fan`, whose edges into the clusters leave its (keyless) junction. -/
theorem refExport_example_ghosts :
    ((refExport {} clusterExNet).edges.filter (fun e => e.arc == .ghost)).map
        (fun e => (nodeId e.src, nodeId e.dst, e.ltail, e.lhead)) =
      [("p_b1_out", "p_b2_in", some "cluster_b1", some "cluster_b2"),
       ("p_b2_in", "p_b1_in", some "cluster_b2", some "cluster_b1")] := by
  decide

/-- Under cluster source `none` the example has no cluster and no ghost edge. -/
theorem refExport_example_none :
    (refExport { cluster := .none } clusterExNet).clusters = [] ∧
      (refExport { cluster := .none } clusterExNet).edges.filter (fun e => e.arc == .ghost) = [] := by
  decide


end Libpetri.Spec
