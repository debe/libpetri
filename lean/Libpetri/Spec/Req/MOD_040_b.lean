import Libpetri.Spec.Registry
import Libpetri.Spec.Req.EXP_016
import Libpetri.Spec.Req.MOD_040

set_option linter.missingDocs true

/-!
# MOD-040 (b): the export half, cluster subgraphs of a composed net (`spec/11-modular-composition.md`)

MOD-040 has two halves. Slice (a) (`Spec/Req/MOD_040.lean`) is the accessor `subnetOf` and the
instance-prefix helper. This block is slice (b): the DOT export of a composed net draws one
`subgraph cluster_<key>` per cluster key, nested by prefix, with the sanitised key as ID and the
key as label, and clustering changes no node and no visible edge.

EXP-016 states the same rule for every net (`Spec/Req/EXP_016.lean`). Ruling D26 (a) item 7 makes
it one rule stated once: the markdown of MOD-040 restates the shall sentences of EXP-016 that this
requirement names, and this block is a predicate over the same abstract `Exporter`, in the same
words (`nodeKey`, `IsSlashPrefix`, `instancePrefix`, `clusterId`, the name assumption
`ExportNet.ClusterNames`). Its seven lines are EXP-016's lines without the at-most-once half of
EXP-016's second line, which MOD-040 does not say; `MOD_040_b_of_EXP_016` derives the block from
EXP-016 for every exporter, so the two cannot drift apart in Lean, and the holds theorem is that
derivation on the reference exporter `refExport`.

The bridge to slice (a) is `mod040b_inside_subnetOf`: under the default cluster source, a drawn
node sits, directly or through nested clusters, inside the cluster of what `subnetOf` answers for
its name. The documented difference between `subnetOf` and the exporter (`s1/obs/TURN`: `subnetOf`
answers `s1`, the exporter clusters it under `s1/obs`) is a difference of depth only.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## MOD-040 (b): the export half -/

requirement MOD_040_b
  id "MOD-040"
  title "Export Grouping (subgraph cluster_* per instance prefix): the export half"
  kind F
  scope "every exporter that draws cluster subgraphs, the clusters of the exported graph of a composed net"
  source verbatim "spec/11-modular-composition.md"
  quote "DOT export per [EXP-001] of a composed net SHOULD emit a `subgraph cluster_<sanitizedKey>` block grouping the nodes of each subnet."
        "The sanitization function applied to the key MUST match the existing DOT ID sanitization per [EXP-014] (non-`[A-Za-z0-9_]` characters, including `/`, replaced by `_`)."
        "This requirement does NOT change the styling, junction, or arc-rendering rules of EXP-002..EXP-015; it only adds grouping structure."
        "For the export half of this requirement (the sentences on DOT export: the opening sentence and its two bullets, the preference and cluster-source sentences, the sanitization and label sentences and the sentence on EXP-002..EXP-015), the SHOULD priority is whether an exporter draws cluster subgraphs at all; an exporter that draws them reads every MAY, SHOULD and MUST sentence of the export half as *shall*, lets the caller select the metadata-only, prefix-only and no-clustering sources, uses the default source when the caller selects none, takes the cluster key of a node and the covered nets as [EXP-016] defines them, and follows the next three sentences, which restate shall sentences of [EXP-016]."
        "The exporter *shall* make each node that has a cluster key a direct member of the cluster of that key and of no other cluster, make a node without a cluster key a member of no cluster, and list as a member of a cluster only a node it draws."
        "The exporter *shall* draw exactly one cluster for each cluster key of a drawn node and for each `/`-prefix of such a key and no other cluster, nest each cluster directly in the cluster whose key is the part of its own key before the last `/` and draw a cluster whose key has no `/` at the top level, and give the cluster of key K the ID `cluster_` followed by K sanitized per [EXP-014] and the label K."
        "The exporter *shall* draw, in any order, the same nodes, and the same edges other than the ghost edges of [EXP-017], as it draws for the same net and configuration under no clustering."
  reading "For every configuration cfg and net X that meets EXP-016's name assumption (ExportNet.ClusterNames: ASCII place and transition names, no two place names and no two transition names equal after sanitize, every cluster key of a place or transition name of X under cfg.cluster ASCII and non-empty with no empty /-segment), with key the glossary's nodeKey cfg.cluster X.member (membership entry, else instancePrefix, per cluster source; a junction takes its transition's key), the graph E cfg X satisfies:"
          "every drawn node is a direct member of a cluster exactly when the cluster's key is the node's key;"
          "every member of a cluster is the reference of a drawn node;"
          "a string is the key of a cluster exactly when it is the key of a drawn node or a /-prefix of such a key (IsSlashPrefix);"
          "no two clusters have the same key;"
          "the parent of every cluster is the instance prefix of its key (the part before its last /, none without one, so a cluster whose key has no / is at the top level);"
          "every cluster has the ID clusterId of its key (cluster_ followed by sanitize of the key) and its key as label;"
          "the nodes are those E draws for cfg with cluster source none, and the edges other than ghost edges are those E draws for cfg with cluster source none, each up to order (List.Perm)."
  assumes "The model is an exporter E : Exporter (Spec/GlossaryExport.lean), the typed graph a configuration and a net are drawn as, before DOT text, and the words are EXP-016's (nodeKey, clusterKey, instancePrefix, IsSlashPrefix, clusterId, ExportNet.ClusterNames). A composed net reaches the exporter as its names and its MOD-026 membership map, so the block quantifies over every net and membership map the exporter can see, as EXP-016 does: which names composition builds is MOD-010 and MOD-013, and which membership map it records is MOD-026, on the composition model. Which subgraph block an edge is written in, cluster styling and the order of sibling clusters are properties of the DOT text, not stated (ruling R2 (exp-b))."
          "Ruling D26 (a) item 7: one statement of the clustering rule. The scoping sentence names the sentences of the export half and reads its SHOULD, MAY and MUST sentences as an exporter that clusters shall, as EXP-016's scoping sentence does: the opening sentence (a cluster block per subnet), the membership bullet, the instance-prefix bullet with its nesting clause, the preference and fall-back sentence, the caller-selectable cluster source with its default, the sanitisation sentence, the label sentence and the sentence that the requirement changes no styling, junction or arc rule are the seven lines through EXP-016's definition of the cluster key (clusterKey under cfg.cluster). That the caller may select the metadata-only, prefix-only and no-clustering sources is the shape of the model: an exporter is a total function of the configuration, so it accepts every cluster source, and the statement quantifies over all four; an exporter that ignores the caller's choice fails the first and third lines (MOD_040_b_forbids_fixedSource draws the default clusters under no clustering). All three runtimes offer the four sources. The opening sentence asks for a cluster block 'grouping the nodes of each subnet'; it is weaker than the third line and shaped differently (the third line draws a cluster for s1/obs, which is no subnet, and none for a subnet of the membership map with no drawn node), and the scoping sentence ties it to the next three sentences, which the lines state. The phrase 'the exporter still clusters s1/obs/TURN under s1/obs' is the first line with the key rule (mod040b_walkNet on the reference; MOD_040_b_forbids_walkUp kills an exporter that clusters by subnetOf), and the bridge to slice (a) is mod040b_inside_subnetOf."
          "The seventh line reads the ghost edges of EXP-017 as the edges of arc type ghost (the glossary's ArcType.ghost), as EXP-016 does, so it sets aside every ghost edge, also one EXP-017 does not ask for: an exporter whose ghost-edge loop lacks the check that the two clusters differ draws a ghost edge from cluster_left to itself and still meets this block, and drawing no ghost edge other than those EXP-017 asks for is EXP-017's obligation (EXP_017_forbids_sameCluster kills that exporter). Likewise a rule of EXP-002..EXP-015 that holds of the whole drawing rather than of its nodes and edges, such as the direction of EXP-007, is that block's obligation: a drawing that turns top to bottom once it has clusters meets the seven lines and fails EXP_007_config."
          "MOD_040_b_of_EXP_016: every exporter meeting EXP-016 meets this block, so the consistency theorem gets the block from EXP_016. The converse fails only by the at-most-once half of EXP-016's second line (no cluster lists a member twice, on a net with distinct transition names), which MOD-040's sentences do not state; it is EXP-016's obligation, not repeated here."
          "Ruling D46 (a) with (x), kind A: the block covers the nets of EXP-016's name assumption (ExportNet.ClusterNames); on other nets the clustering is implementation-defined. On a cluster key with an empty /-segment the Rust builder panics and the Java builder throws (RD-12 in spec/runtime-defects.md), a non-ASCII membership key gets a Unicode cluster ID in Rust (RD-13), and the runtimes look a node's key up by its DOT ID (RD-14); all three are outside the block, as they are outside EXP-016."
          "Quality, kind Q: the sentence of slice (a) that the exporter's instance-prefix helper and its clustering are unchanged by the subnetOf rule, and the last sentence of AC9 (the DOT export of the same nets is byte-identical to before), are properties of a change to the code and of DOT bytes, tested, not stated."
          "AC1 (instances b1 and b2 give subgraph cluster_b1 and subgraph cluster_b2) and AC3 (nested prefixes give nested subgraphs) are decided on the reference in MOD_040_b_nonvacuous and follow from the third, fifth and sixth lines for every exporter meeting the block. AC2 (each cluster block contains, directly or through the cluster blocks nested in it, exactly the places and transitions whose cluster key is the cluster's key or begins with it followed by /, and the junction nodes of those transitions) is mod040b_ac2; it is worded as EXP-016's AC2, which ruling D26 item 5 reads the same way. AC4 (no composed instance, no metadata and no / gives no cluster) is mod040b_ac4. AC5 (cluster IDs match cluster_[A-Za-z0-9_]+) is mod040b_ac5 for every cluster with a non-empty key."
          "AC6 (one cluster block per subnet of the membership metadata, a shared place whose name has no instance prefix at the top level) and AC7 (metadata nodes cluster by subnet name, prefix-named nodes by prefix) are the first line under a membership map, decided on the reference in MOD_040_b_nonvacuous; by ruling D26 item 7 a shared place has no membership entry and falls back to its instance prefix, so it is at the top level when its name has no / (hub), and in the cluster of its prefix otherwise (rv/x in cluster_rv), which is why AC6 and the test derivation name the shared place without /. AC8 and AC9 are slice (a) (MOD_040_nonvacuous)."
          "The test derivation (a composed net with two top-level instances and a directly composed net of two subnets whose shared place is named without /, exported and checked for cluster blocks, members and IDs) is AC1, AC2, AC5 and AC6 on composed nets."
  signoff "pending"
  statement : Exporter → Prop :=
    fun E => ∀ (cfg : ExportCfg) (X : ExportNet), X.ClusterNames cfg.cluster →
      (∀ n ∈ (E cfg X).nodes, ∀ c ∈ (E cfg X).clusters,
        n.ref ∈ c.members ↔ nodeKey cfg.cluster X.member n.ref = some c.key) ∧
      (∀ c ∈ (E cfg X).clusters, ∀ r ∈ c.members, ∃ n ∈ (E cfg X).nodes, n.ref = r) ∧
      (∀ q, q ∈ (E cfg X).clusters.map XCluster.key ↔
        ∃ n ∈ (E cfg X).nodes, ∃ K, nodeKey cfg.cluster X.member n.ref = some K ∧
          (q = K ∨ IsSlashPrefix q K)) ∧
      ((E cfg X).clusters.map XCluster.key).Nodup ∧
      (∀ c ∈ (E cfg X).clusters, c.parent = instancePrefix c.key) ∧
      (∀ c ∈ (E cfg X).clusters, c.id = clusterId c.key ∧ c.label = c.key) ∧
      ((E cfg X).nodes.Perm (E { cfg with cluster := .none } X).nodes ∧
        ((E cfg X).edges.filter fun e => e.arc != .ghost).Perm
          ((E { cfg with cluster := .none } X).edges.filter fun e => e.arc != .ghost))

/- The pinned readable form of MOD-040 (b): a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.MOD_040_b : Exporter → Prop :=
fun E =>
  ∀ (cfg : ExportCfg) (X : ExportNet),
    ExportNet.ClusterNames cfg.cluster X →
      (∀ n ∈ (E cfg X).nodes,
          ∀ c ∈ (E cfg X).clusters, n.ref ∈ c.members ↔ nodeKey cfg.cluster X.member n.ref = some c.key) ∧
        (∀ c ∈ (E cfg X).clusters, ∀ r ∈ c.members, ∃ n ∈ (E cfg X).nodes, n.ref = r) ∧
          (∀ (q : String),
              q ∈ List.map XCluster.key (E cfg X).clusters ↔
                ∃ n ∈ (E cfg X).nodes, ∃ K, nodeKey cfg.cluster X.member n.ref = some K ∧ (q = K ∨ IsSlashPrefix q K)) ∧
            (List.map XCluster.key (E cfg X).clusters).Nodup ∧
              (∀ c ∈ (E cfg X).clusters, c.parent = instancePrefix c.key) ∧
                (∀ c ∈ (E cfg X).clusters, c.id = clusterId c.key ∧ c.label = c.key) ∧
                  (E cfg X).nodes.Perm
                      (E
                          { dir := cfg.dir, showTypes := cfg.showTypes, showIntervals := cfg.showIntervals,
                            showPriority := cfg.showPriority, env := cfg.env, cluster := ClusterSource.none }
                          X).nodes ∧
                    (List.filter (fun e => e.arc != ArcType.ghost) (E cfg X).edges).Perm
                      (List.filter (fun e => e.arc != ArcType.ghost)
                        (E
                            { dir := cfg.dir, showTypes := cfg.showTypes, showIntervals := cfg.showIntervals,
                              showPriority := cfg.showPriority, env := cfg.env, cluster := ClusterSource.none }
                            X).edges)
-/
#guard_msgs in #print MOD_040_b

/-! ## One rule: EXP-016 gives the block -/

/-- **EXP-016 gives MOD-040 (b)**, for every exporter: the seven lines of this block are EXP-016's
lines, the second without its at-most-once half. So an exporter that clusters as EXP-016 says
clusters a composed net as MOD-040 says, and the two statements of the rule cannot drift apart. -/
theorem MOD_040_b_of_EXP_016 {E : Exporter} (h : EXP_016 E) : MOD_040_b E := by
  intro cfg X hX
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h cfg X hX
  exact ⟨h1, fun c hc => (h2 c hc).1, h3, h4, h5, h6, h7⟩

/-- ✓ **The reference exporter meets MOD-040 (b)**. Two instances `b1` and `b2` are drawn as the
clusters `cluster_b1` and `cluster_b2`, each holding the places and the transition of its
instance; a place `outer/inner/p` sits in `cluster_outer_inner`, which is nested in
`cluster_outer`; the nodes and the visible edges are the ones drawn without clustering. -/
@[evidence holds MOD_040_b]
theorem MOD_040_b_reference : MOD_040_b refExport :=
  MOD_040_b_of_EXP_016 EXP_016_reference

/-! ## The bridge to slice (a) -/

/-- Two `/`-prefixes of one name: a `/`-prefix `s` of a name is the name's instance prefix `q`, or
a `/`-prefix of it. -/
theorem mod040b_slashPrefix_instancePrefix {s n q : String} (hs : IsSlashPrefix s n)
    (hq : instancePrefix n = some q) : s = q ∨ IsSlashPrefix s q := by
  obtain ⟨hse, r', hr'⟩ := (isSlashPrefix_iff s n).1 hs
  obtain ⟨-, r, hr, hnr⟩ := (instancePrefix_eq_some n q).1 hq
  have heq : s.toList ++ '/' :: r' = q.toList ++ '/' :: r := hr'.symm.trans hr
  rcases List.append_eq_append_iff.1 heq with ⟨a', ha, hc⟩ | ⟨c', hc, hd⟩
  · cases a' with
    | nil => exact Or.inl (String.toList_inj.1 (by simpa using ha.symm))
    | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      exact Or.inr ((isSlashPrefix_iff s q).2 ⟨hse, xs, by simp [ha]⟩)
  · cases c' with
    | nil => exact Or.inl (String.toList_inj.1 (by simpa using hc))
    | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at hd
      exact absurd (by rw [hd.2]; simp) hnr

/-- **A drawn node sits inside the cluster of its `subnetOf`**, for every model of both slices:
under the default cluster source, when `subnetOf` answers `s` for the name of a drawn node (a
junction counts by its transition's name), some cluster whose key is `s` or nested under `s` holds
the node. With the transition `s1/t`, `subnetOf` answers `s1` for the place `s1/obs/TURN`, and the
exporter puts the place in `cluster_s1_obs`, which is nested in `cluster_s1`: the two halves of
MOD-040 differ in depth, never in the subnet. -/
theorem mod040b_inside_subnetOf {M : SubnetAccess} (hM : MOD_040 M) {E : Exporter}
    (hE : MOD_040_b E) {cfg : ExportCfg} (hc : cfg.cluster = .auto) {X : ExportNet}
    (hX : X.ClusterNames cfg.cluster) {S : SubnetNet} (hS : S.member = X.member)
    {n : XNode} (hn : n ∈ (E cfg X).nodes) {s : String}
    (hs : M.subnetOf S n.ref.keyName = some s) :
    ∃ c ∈ (E cfg X).clusters, (c.key = s ∨ IsSlashPrefix s c.key) ∧ n.ref ∈ c.members := by
  obtain ⟨h1, -, h3, -⟩ := hE cfg X hX
  have hkey : ∀ K, nodeKey cfg.cluster X.member n.ref = some K → (K = s ∨ IsSlashPrefix s K) →
      ∃ c ∈ (E cfg X).clusters, (c.key = s ∨ IsSlashPrefix s c.key) ∧ n.ref ∈ c.members := by
    intro K hK hsK
    obtain ⟨c, hcm, hck⟩ := List.mem_map.1 ((h3 K).2 ⟨n, hn, K, hK, Or.inl rfl⟩)
    refine ⟨c, hcm, ?_, (h1 n hn c hcm).2 (by rw [hck]; exact hK)⟩
    rw [hck]
    exact hsK
  have hnk : nodeKey cfg.cluster X.member n.ref =
      (X.member n.ref.keyName).or (instancePrefix n.ref.keyName) := by
    simp [nodeKey, hc, clusterKey_auto]
  rw [(mod040_unique hM).1] at hs
  unfold refSubnetOf at hs
  split at hs
  · rw [hS] at hs
    cases hm : X.member n.ref.keyName with
    | some e =>
      rw [hm] at hs
      cases hs
      exact hkey s (by rw [hnk, hm]; rfl) (Or.inl rfl)
    | none =>
      rw [hm] at hs
      simp only [Option.none_or] at hs
      have hsp : IsSlashPrefix s n.ref.keyName := (subnetWalk_some_max hs).1
      obtain ⟨q, hq, -⟩ := isSlashPrefix_instancePrefix hsp
      rcases mod040b_slashPrefix_instancePrefix hsp hq with rfl | hsq
      · exact hkey s (by rw [hnk, hm, hq]; rfl) (Or.inl rfl)
      · exact hkey q (by rw [hnk, hm, hq]; rfl) (Or.inr hsq)
  · cases hs

/-! ## Example nets -/

/-- MOD-040's own example on the exporter: the transition `s1/t` moves a token from `s1/obs/TURN`
to `s1/o`. -/
def mod040bWalkNet : ExportNet := exp016WalkNet

/-- The documented difference, on the reference: the exporter draws `s1/obs/TURN` in
`cluster_s1_obs`, nested in `cluster_s1`, while `subnetOf` answers `s1` for it (slice (a)). -/
theorem mod040b_walkNet :
    exp016Clusters (refExport {} mod040bWalkNet) =
      [("cluster_s1", "s1", none, ["p_s1_o", "t_s1_t"]),
       ("cluster_s1_obs", "s1/obs", some "s1", ["p_s1_obs_TURN"])] ∧
    refSubnetAccess.subnetOf { places := ["s1/obs/TURN", "s1/o"], trans := ["s1/t"] }
      "s1/obs/TURN" = some "s1" := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ✓ **The composed nets of MOD-040's criteria, on the reference.** Two instances `b1` and `b2`
give `cluster_b1` and `cluster_b2`, each with its two places and its transition (AC1). A nested
instance `outer/inner` gives `cluster_outer_inner` inside `cluster_outer` (AC3). A directly
composed net of the subnets `S1` and `S2` gives `cluster_S1` and `cluster_S2` with their private
nodes, the shared place `hub` stays at the top level (AC6), and the shared place `rv/x`, which has
no membership entry, falls back to its prefix `rv`. A net that mixes the subnet `S` (transition `A`,
place `a`) with the instance node `b/c` draws both `cluster_S` and `cluster_b` (AC7). Every one of
these nets meets the name assumption. -/
@[evidence nonvacuous MOD_040_b]
theorem MOD_040_b_nonvacuous :
    exp016TwoNet.ClusterNames .auto ∧ exp016DeepNet.ClusterNames .auto ∧
    exp016DirectNet.ClusterNames .auto ∧ exp016MetaNet.ClusterNames .auto ∧
    exp016Clusters (refExport {} exp016TwoNet) =
      [("cluster_b1", "b1", none, ["p_b1_a", "p_b1_b", "t_b1_t"]),
       ("cluster_b2", "b2", none, ["p_b2_a", "p_b2_b", "t_b2_t"])] ∧
    exp016Clusters (refExport {} exp016DeepNet) =
      [("cluster_outer", "outer", none, []),
       ("cluster_outer_inner", "outer/inner", some "outer",
         ["p_outer_inner_p", "p_outer_inner_q", "t_outer_inner_t"])] ∧
    exp016Clusters (refExport {} exp016DirectNet) =
      [("cluster_S1", "S1", none, ["p_p1", "t_T1"]),
       ("cluster_S2", "S2", none, ["p_p2", "t_T2"]),
       ("cluster_rv", "rv", none, ["p_rv_x"])] ∧
    exp016TopLevel (refExport {} exp016DirectNet) = ["p_hub"] ∧
    exp016Clusters (refExport {} exp016MetaNet) =
      [("cluster_S", "S", none, ["p_a", "t_A"]),
       ("cluster_b", "b", none, ["p_b_c"])] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Consequences: the acceptance criteria for every exporter meeting the block -/

/-- **AC2 for every exporter meeting MOD-040 (b)**: a drawn node sits in the cluster of `K`,
directly or in a cluster nested in it, exactly when its own key is `K` or has `K` as a
`/`-prefix. The place `outer/inner/p` is inside `cluster_outer` (through `cluster_outer_inner`)
and inside `cluster_outer_inner`, and in no other cluster. -/
@[evidence cites "MOD-040" "AC2: each cluster block contains, directly or through the cluster blocks nested in it, exactly the nodes whose cluster key is the cluster's key or begins with it followed by /, for every exporter meeting the export half"]
theorem mod040b_ac2 (E : Exporter) (hE : MOD_040_b E) (cfg : ExportCfg) (X : ExportNet)
    (hX : X.ClusterNames cfg.cluster) :
    ∀ n ∈ (E cfg X).nodes, ∀ K : String,
      (∃ c ∈ (E cfg X).clusters, (c.key = K ∨ IsSlashPrefix K c.key) ∧ n.ref ∈ c.members) ↔
        ∃ K', nodeKey cfg.cluster X.member n.ref = some K' ∧ (K' = K ∨ IsSlashPrefix K K') := by
  obtain ⟨h1, -, h3, -⟩ := hE cfg X hX
  intro n hn K
  constructor
  · rintro ⟨c, hc, hk, hm⟩
    exact ⟨c.key, (h1 n hn c hc).mp hm, hk⟩
  · rintro ⟨K', hK', hk⟩
    obtain ⟨c, hc, hck⟩ := List.mem_map.mp ((h3 K').mpr ⟨n, hn, K', hK', Or.inl rfl⟩)
    exact ⟨c, hc, by rw [hck]; exact hk, (h1 n hn c hc).mpr (by rw [hck]; exact hK')⟩

/-- **AC4 for every exporter meeting MOD-040 (b)**: a net with no `/` in any place or transition
name and no membership entry, whose names meet EXP-014's name assumption, is drawn with no cluster,
under every cluster source. A net of the places `a`, `b` and the transition `t` has no cluster. -/
@[evidence cites "MOD-040" "AC4: a net with no composed instances and no membership metadata (no / in any name) produces no cluster subgraphs, for every exporter meeting the export half"]
theorem mod040b_ac4 (E : Exporter) (hE : MOD_040_b E) (cfg : ExportCfg) (X : ExportNet)
    (hN : X.IdNames) (hX : ∀ s ∈ X.exp016Names, '/' ∉ s.toList ∧ X.member s = none)
    (hn : ∀ n ∈ (E cfg X).nodes, '/' ∉ n.ref.keyName.toList ∧ X.member n.ref.keyName = none) :
    (E cfg X).clusters = [] := by
  have hok : X.ClusterNames cfg.cluster := by
    refine ⟨hN, ?_⟩
    intro K hK
    obtain ⟨s, hs, hK⟩ := List.mem_filterMap.mp hK
    rw [exp016_clusterKey_none _ _ _ (hX s hs).1 (hX s hs).2] at hK
    cases hK
  obtain ⟨-, -, h3, -⟩ := hE cfg X hok
  rw [List.eq_nil_iff_forall_not_mem]
  intro c hc
  obtain ⟨n, hn', K, hK, -⟩ := (h3 c.key).mp (List.mem_map_of_mem hc)
  have : nodeKey cfg.cluster X.member n.ref = none :=
    exp016_clusterKey_none _ _ _ (hn n hn').1 (hn n hn').2
  rw [this] at hK
  cases hK

/-- **AC5 for every exporter meeting MOD-040 (b)**: every cluster with a non-empty key has an ID
of the shape `cluster_[A-Za-z0-9_]+`. The key `outer/inner` gets the ID `cluster_outer_inner`. -/
@[evidence cites "MOD-040" "AC5: cluster IDs match the regex cluster_[A-Za-z0-9_]+, for every exporter meeting the export half, for every cluster whose key is not empty"]
theorem mod040b_ac5 (E : Exporter) (hE : MOD_040_b E) (cfg : ExportCfg) (X : ExportNet)
    (hX : X.ClusterNames cfg.cluster) :
    ∀ c ∈ (E cfg X).clusters, c.key ≠ "" → exp016ClusterIdShape c.id := by
  intro c hc hk
  refine ⟨sanitize c.key, ((hE cfg X hX).2.2.2.2.2.1 c hc).1, ?_, ?_⟩
  · intro h
    apply hk
    have := congrArg String.toList h
    simp only [sanitize_toList, String.toList_empty, List.map_eq_nil_iff] at this
    exact String.toList_inj.mp (by simpa using this)
  · intro ch hch
    simp only [sanitize_toList, List.mem_map] at hch
    obtain ⟨c', -, rfl⟩ := hch
    unfold sanitizeChar exp016IdChar
    split <;> simp_all

/-! ## Wrong exporters, one or more per line -/

/-- An exporter whose default source ignores the membership metadata: under the default source it
keys every node by its instance prefix alone. -/
def mod040b_ignoresMember : Exporter := exp016ByKey fun src X r =>
  match src with
  | .auto => instancePrefix r.keyName
  | s => nodeKey s X.member r

/-- A net that mixes both kinds of composition under one key: the instance transition `b/t` moves
a token from `b/x` to the place `y`, which a direct composition put in the subnet named `b`. -/
def mod040bMixNet : ExportNet :=
  { trans := [exp016Trans "b/t" "b/x" (.place "y")],
    member := fun s => if s = "y" then some "b" else none }

/-- ✗ Ignoring the membership metadata violates MOD-040 (b) (line 1): the place `y` belongs to
the subnet `b` by membership, so its cluster key is `b`, but this exporter keys it by its name,
which has no `/`, and leaves it at the top level beside `cluster_b`. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_ignoresMember : ¬ MOD_040_b mod040b_ignoresMember := by
  intro h
  have := (h {} mod040bMixNet (by decide)).1
  revert this
  decide

/-- ✗ Clustering by `subnetOf` violates MOD-040 (b) (line 1, a node in a cluster that is not of
its key): with the transition `s1/t`, `subnetOf` answers `s1` for the place `s1/obs/TURN`, and an
exporter that clusters by that answer puts the place in `cluster_s1`, while its key is `s1/obs`. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_walkUp : ¬ MOD_040_b exp016_walkUp := by
  intro h
  have := (h {} mod040bWalkNet (by decide)).1
  revert this
  decide

/-- An exporter that ignores the caller's cluster source and always clusters by the default one. -/
def mod040b_fixedSource : Exporter := exp016ByKey fun _ X r => nodeKey .auto X.member r

/-- ✗ Ignoring the caller's choice violates MOD-040 (b) (line 1): the caller asks for no
clustering on the instances `b1` and `b2`, so no node has a cluster key, but this exporter still
puts `b1/a` in `cluster_b1`. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_fixedSource : ¬ MOD_040_b mod040b_fixedSource := by
  intro h
  have := (h { cluster := .none } exp016TwoNet (by decide)).1
  revert this
  decide

/-- The same exporter fails line 3 too: under no clustering it draws `cluster_b1`, and no drawn
node has the key `b1` or a key below it. -/
theorem mod040b_fixedSource_line3 (h : MOD_040_b mod040b_fixedSource) : False := by
  have hk : "b1" ∈ (mod040b_fixedSource { cluster := .none } exp016TwoNet).clusters.map
      XCluster.key := by decide
  obtain ⟨n, -, K, hK, -⟩ :=
    ((h { cluster := .none } exp016TwoNet (by decide)).2.2.1 "b1").mp hk
  simp [nodeKey, clusterKey] at hK

/-- ✗ Listing a node the exporter does not draw violates MOD-040 (b) (line 2): an exporter that
adds a member `phantom` to every cluster lists, in `cluster_outer`, a place no node stands for. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_phantomMember : ¬ MOD_040_b exp016_phantomMember := by
  intro h
  have := (h {} exp016NestNet (by decide)).2.1
  revert this
  decide

/-- ✗ Leaving out the cluster of a `/`-prefix violates MOD-040 (b) (line 3): with the places of
`outer/inner/t` all in `outer/inner`, the cluster `outer` must still be drawn to hold
`cluster_outer_inner`, and an exporter that draws only clusters with direct members drops it. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_noChain : ¬ MOD_040_b exp016_noChain := by
  intro h
  have hw : ∃ n ∈ (exp016_noChain {} exp016DeepNet).nodes,
      nodeKey ({} : ExportCfg).cluster exp016DeepNet.member n.ref = some "outer/inner" := by
    decide
  obtain ⟨n, hn, hK⟩ := hw
  have := ((h {} exp016DeepNet (by decide)).2.2.1 "outer").mpr
    ⟨n, hn, "outer/inner", hK, Or.inr (by decide)⟩
  revert this
  decide

/-- ✗ A cluster for a key no node has violates MOD-040 (b) (line 3, the other direction): an
exporter that adds an empty cluster `extra` to the drawing of `outer/inner/t` draws a cluster
whose key is neither the key of a drawn node nor a `/`-prefix of one. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_extraCluster : ¬ MOD_040_b exp016_extraCluster := by
  intro h
  have hk : "extra" ∈ (exp016_extraCluster {} exp016NestNet).clusters.map XCluster.key := by
    decide
  obtain ⟨n, hn, K, hK, hq⟩ := ((h {} exp016NestNet (by decide)).2.2.1 "extra").mp hk
  have hno : ∀ n ∈ (exp016_extraCluster {} exp016NestNet).nodes,
      ∀ K ∈ (nodeKey ({} : ExportCfg).cluster exp016NestNet.member n.ref).toList,
        ¬ ("extra" = K ∨ IsSlashPrefix "extra" K) := by decide
  exact hno n hn K (by rw [hK]; simp) hq

/-- ✗ Drawing a cluster twice violates MOD-040 (b) (line 4): an exporter that draws every cluster
twice draws two blocks `cluster_outer`. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_dupClusters : ¬ MOD_040_b exp016_dupClusters := by
  intro h
  have := (h {} exp016NestNet (by decide)).2.2.2.1
  revert this
  decide

/-- ✗ Flat clusters violate MOD-040 (b) (line 5): the nested instance `outer/inner` must be drawn
inside `cluster_outer`, and an exporter that draws every cluster at the top level does not. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_flatClusters : ¬ MOD_040_b exp016_noNesting := by
  intro h
  have := (h {} exp016DeepNet (by decide)).2.2.2.2.1
  revert this
  decide

/-- An exporter that nests every top-level cluster after the first one in the first cluster it
draws. -/
def mod040b_nestUnderFirst : Exporter := fun cfg X =>
  let g := refExport cfg X
  let first := g.clusters.head?.map XCluster.key
  { g with clusters := g.clusters.map fun c =>
      if c.parent.isNone && some c.key != first then { c with parent := first } else c }

/-- ✗ Nesting a cluster whose key has no `/` violates MOD-040 (b) (line 5): the instances `b1` and
`b2` are both drawn at the top level, and an exporter that draws `cluster_b2` inside
`cluster_b1` does not. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_nestUnderFirst : ¬ MOD_040_b mod040b_nestUnderFirst := by
  intro h
  have := (h {} exp016TwoNet (by decide)).2.2.2.2.1
  revert this
  decide

/-- ✗ An unsanitised cluster ID violates MOD-040 (b) (line 6): the cluster of `outer/inner` must
be `cluster_outer_inner`, not `cluster_outer/inner`. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_rawId : ¬ MOD_040_b exp016_rawId := by
  intro h
  have := (h {} exp016DeepNet (by decide)).2.2.2.2.2.1
  revert this
  decide

/-- ✗ A sanitised label violates MOD-040 (b) (line 6): the label of the cluster of `outer/inner`
is the original key `outer/inner`, not `outer_inner`. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_sanitizedLabel : ¬ MOD_040_b exp016_sanitizedLabel := by
  intro h
  have := (h {} exp016DeepNet (by decide)).2.2.2.2.2.1
  revert this
  decide

/-- ✗ Dropping the edges between clusters violates MOD-040 (b) (line 7): the transition `b1/t`
outputs to `b2/x` in another instance, and that edge is drawn without clustering, so it must be
drawn with clustering too. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_dropCross : ¬ MOD_040_b exp016_dropCross := by
  intro h
  have := (h {} exp016CrossNet (by decide)).2.2.2.2.2.2.2
  revert this
  decide

/-- ✗ Renaming the nodes of a cluster violates MOD-040 (b) (line 7): an exporter that prefixes the
ID of every clustered node with its cluster ID draws other nodes than without clustering. -/
@[evidence forbids MOD_040_b]
theorem MOD_040_b_forbids_scopedIds : ¬ MOD_040_b exp016_scopedIds := by
  intro h
  have := (h {} exp016CrossNet (by decide)).2.2.2.2.2.2.1
  revert this
  decide

end Libpetri.Spec
