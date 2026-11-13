import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Reference.ExportCluster
import Libpetri.Spec.Req.EXP_014
import Libpetri.Spec.Text.EXP_016

set_option linter.missingDocs true

/-!
# EXP-016: Subnet instance cluster subgraphs (`spec/09-export.md`)

The clusters of the exported graph: every node with a cluster key (its membership entry, else its
instance prefix, under the default cluster source; a junction takes its transition's key) is a
direct member of the cluster of that key and of no other, a cluster lists only drawn nodes and
each once, the clusters are the keys in use and their `/`-prefixes, one each, nested by the part of
the key before its last `/`, with ID
`cluster_<sanitize key>` and the key as label, and clustering changes no node and no edge other
than the ghost edges of EXP-017.

The requirement is a predicate over an abstract `Exporter` (glossary `GlossaryExport.lean`); the
key rule is the cluster vocabulary of `Spec/GlossaryExportCluster.lean` (`clusterKey`, `nodeKey`,
`instancePrefix`, `IsSlashPrefix`, `clusterId`, `NoEmptySegment`), a fixed definition, so a mapper
with another key rule (a first-`/` key, metadata only by default, MOD-040's walk-up, junctions at
top level) breaks the membership lines. The name assumption is EXP-014's (`ExportNet.IdNames`)
together with well-formed cluster keys: two names with one DOT ID cannot be drawn as two nodes in
two places of the cluster tree. The witness is the clustered reference exporter `refExport`.

Rulings: D26 (a) items 5 and 7 (a junction belongs to its transition's cluster, AC2 is transitive
for nested prefixes, a shared place "is not grouped by metadata", "an exporter that clusters
shall"); D46 (a) with (x) (the block covers nets whose names meet EXP-014's name assumption and whose
cluster keys are ASCII, non-empty and have no empty `/`-segment; on a key with an empty segment the
three mappers register the glossary's `keyChain`, as the reference does, and the premise keeps that
half only because the scope sentence of the requirement does);
D60 (c) (AC6, cross-language byte equality, stays kind Q).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## Block-local vocabulary -/

/-- Every place and transition name of `X` the exporter can draw a node for: the declared places,
every place an arc touches, and the transition names. -/
def ExportNet.exp016Names (X : ExportNet) : List String :=
  X.places ++ X.trans.flatMap ExportTrans.touched ++ X.trans.map ExportTrans.name

/-- **The cluster-key half of EXP-016's name assumption** (ruling D46 (a) with (x), kind A): under
cluster source `src`, every cluster key of a place or transition name of `X` is ASCII, non-empty
and has no empty `/`-segment. A key from membership metadata ([MOD-026]) is a subnet name, not a
node name, so EXP-014's ASCII names do not make it ASCII. -/
def ExportNet.ClusterKeysWellFormed (src : ClusterSource) (X : ExportNet) : Prop :=
  ∀ K ∈ X.exp016Names.filterMap (clusterKey src X.member), AsciiName K ∧ NoEmptySegment K

instance (src : ClusterSource) (X : ExportNet) : Decidable (X.ClusterKeysWellFormed src) := by
  unfold ExportNet.ClusterKeysWellFormed; infer_instance

instance exp016IdNamesDecidable (X : ExportNet) : Decidable X.IdNames := by
  unfold ExportNet.IdNames ExportNet.allPlaceNames; infer_instance

/-- **The name assumption of EXP-016** (ruling D46 (a) with (x), kind A): EXP-014's name assumption
`ExportNet.IdNames` (ASCII place and transition names, no two place names nor two transition names
equal after `sanitize`, so that no two names share a DOT ID), and well-formed cluster keys under
cluster source `src`. -/
def ExportNet.ClusterNames (src : ClusterSource) (X : ExportNet) : Prop :=
  X.IdNames ∧ X.ClusterKeysWellFormed src

instance (src : ClusterSource) (X : ExportNet) : Decidable (X.ClusterNames src) := by
  unfold ExportNet.ClusterNames; infer_instance

/-! ## EXP-016: Subnet instance cluster subgraphs -/

requirement EXP_016
  id "EXP-016"
  title "Subnet Instance Cluster Subgraphs"
  kind F
  scope "every exporter, the clusters of the exported graph"
  source verbatim "spec/09-export.md"
  covers EXP_016.s1, EXP_016.s2, EXP_016.s3, EXP_016.s4, EXP_016.s5, EXP_016.s6, EXP_016.s7,
        EXP_016.s8, EXP_016.s9, EXP_016.s10, EXP_016.s11, EXP_016.s12, EXP_016.s13, EXP_016.s14,
        EXP_016.s15, EXP_016.s16
  reading "For every configuration cfg and net X that meets the name assumption (ExportNet.ClusterNames: EXP-014's ExportNet.IdNames, ASCII place and transition names with no two place names and no two transition names equal after sanitize, and every cluster key of a place or transition name of X under cfg.cluster ASCII and non-empty with no empty /-segment), with key the glossary's nodeKey cfg.cluster X.member (membership entry, else instancePrefix, per cluster source; a junction takes its transition's key), the graph E cfg X satisfies:"
          "every drawn node is a direct member of a cluster exactly when the cluster's key is the node's key (so a node with a key is in the cluster of its key and no other, and a node without a key is in no cluster);"
          "every member of a cluster is the reference of a drawn node, and when the transition names of X are pairwise distinct no cluster lists a member twice;"
          "a string is the key of a cluster exactly when it is the key of a drawn node or a /-prefix of such a key (IsSlashPrefix: a non-empty initial segment of the key that is followed by / in it);"
          "no two clusters have the same key;"
          "the parent of every cluster is the instance prefix of its key (the part before its last /, none without one);"
          "every cluster has the ID clusterId of its key (cluster_ followed by sanitize of the key) and its key as label;"
          "the nodes are those E draws for cfg with cluster source none, and the edges other than ghost edges are those E draws for cfg with cluster source none, each up to order (List.Perm: the same multiset, every field of each node and edge included)."
  assumes "The model is an exporter E : Exporter (glossary): the typed graph a configuration and a net are drawn as, before DOT text. Clusters are the graph's XCluster list (key, ID, label, parent key, direct members). Which subgraph block an edge is written in (deepest_common_prefix in the runtimes), cluster styling and the order of sibling clusters are properties of the DOT text, not stated (ruling R2 (exp-b) on order); the block states membership, nesting, IDs and labels."
          "The key rule is a fixed glossary definition (clusterKey, nodeKey, instancePrefix in Spec/GlossaryExportCluster.lean), the same three lines in all three mappers (cluster_key_of in Rust, autoClusterKeyOf and its switch in TypeScript, PetriNetGraphMapper in Java), so a mapper with another key rule breaks the first and third lines: the first-/ key (EXP_016_forbids_firstSlash), metadata only under the default source (EXP_016_forbids_metadataDefault), MOD-040's subnetOf walk-up used for clustering (EXP_016_forbids_walkUp; MOD-040 itself says the exporter still clusters s1/obs/TURN under s1/obs) and junctions left at the top level (EXP_016_forbids_junctionTop)."
          "The membership bullet, the prefix bullet and the fall-back sentence are the key rule under the default source auto. By ruling D26 item 7 a shared place has no membership entry and is therefore not grouped by metadata; under the default source it falls back to its instance prefix like every node without an entry, so it is at the top level only when its name has no instance prefix (the old wording 'stays top-level' contradicted the fall-back sentence). The junction sentence is ruling D26 item 5 (all three mappers put a junction in its transition's cluster)."
          "The SHOULD priority is whether an exporter clusters at all (ruling D26 item 7: the MUST sentences inside a SHOULD requirement read 'an exporter that clusters shall'). The scoping sentence extends that reading to the MAY and SHOULD sentences: for an exporter that clusters, 'MAY be caller-selectable', 'the default SHOULD be metadata-when-present', 'SHOULD prefer it and fall back' and 'the cluster label attribute SHOULD carry the original key' are obligations, as the block states them (all three runtimes meet them). The model takes the caller's choice as cfg.cluster and the statement quantifies over all four sources, so an exporter that ignores the choice fails the first and third lines; the glossary's ExportCfg defaults cfg.cluster to auto (metadata when present, else the prefix), which is the default-source sentence. An exporter that never draws clusters does not meet the predicate and is outside the requirement."
          "Ruling D46 (a) with (x), kind A: the block covers nets that meet ExportNet.ClusterNames. Its first half is EXP-014's name assumption ExportNet.IdNames (ASCII names, no two place names and no two transition names equal after sanitize). The first line depends on it: all three runtimes look a node's key up by its DOT ID (node_id_to_prefix in Rust, nodeIdToPrefix in Java and TypeScript), so on b1/t from b1/x to b1_x the two places are one node p_b1_x, which no exporter can put both in cluster_b1 and at the top level (exp016_collide_outside); under IdNames the ID is one to one on the nodes the reference draws (exp014_nodeId_inj), so looking a key up by ID finds the node's own key. Its second half (ExportNet.ClusterKeysWellFormed, over the declared places, the places the arcs touch and the transition names of X) is that every cluster key is ASCII and non-empty with no empty /-segment. The ASCII half is needed because a membership key is a subnet name (MOD-026), not a node name, so it can hold other characters while every node name is ASCII; Rust's sanitize keeps Unicode letters (ruling D46 (a) makes them implementation-defined), so for a key Größe Rust draws the cluster ID cluster_Größe where Java and TypeScript draw cluster_Gr__e, and the sixth line, which states the ID through the glossary's ASCII sanitize, would bind Rust on a character D46 leaves open (exp016_nonAsciiKey_outside). On a key with an empty segment (a name such as a//x, /a/x or http://host/x) all three mappers register the glossary's keyChain, every non-empty /-prefix followed by / and then the key itself (register_prefix_chain in Rust, registerPrefixChain in Java and TypeScript), and route an edge by the longest entry of one key's chain that is in the other's, so they draw the clusters the reference draws and neither panic nor throw (exp_016_key_with_empty_segment_registers_its_key_chain in Rust, partitionRegistersTheKeyChainOfAKeyWithAnEmptySegment_EXP016 in Java, the EXP-016 empty-segment test of typescript/tests/export/cluster-builder.test.ts, and python/tests/test_dot_export.py). A Rust chain that skipped the empty segment and never registered the key, the Java failure on a key with a leading or trailing /, and the TypeScript failure on a key with a leading / or the empty key, are the behaviour RD-12 recorded. The empty-segment half of the premise is there because the scope sentence of the requirement excludes such keys. Dropping it needs that sentence reworded in the markdown and the lines checked there, on a key with a leading / (no instance prefix, so a top-level cluster) and on the empty membership key (cluster ID cluster_, outside AC5's pattern). The Unicode cluster ID is implementation-defined under ruling D46 (a), and the lookup by DOT ID is the Known limit sentence of EXP-016. On a net outside the assumption the whole predicate is silent, the seventh line included. The reference model stays total there (the reference builder of Reference/ExportCluster.lean registers the keyChain of Spec/GlossaryExportCluster.lean, which holds the key and its parent)."
          "Two membership keys whose sanitised forms are equal (a/b and a_b) get one cluster ID; the sixth line states that ID as the runtimes draw it, and no line depends on the keys' sanitised forms being distinct."
          "The second line's at-most-once half (EXP_016_forbids_dupJunction) carries the premise that the transition names of X are pairwise distinct, as EXP-014's uniqueness line does: two transitions with one name draw one node reference twice, and the members of a cluster list each drawn reference in node order."
          "The sixth line is the sanitisation sentence and the label sentence: sanitize is EXP-014's (each character outside [A-Za-z0-9_], / included, replaced by _). The seventh line is 'does NOT alter the styling, junction, or arc rendering rules of EXP-002..EXP-015; it adds grouping structure only' together with the last shall sentence: ghost edges are excluded because EXP-017 adds them only when there are clusters (export design, skeptic correction S-4), and EXP-017 itself keeps the visible edge set. The statement reads ghost edges as the glossary's ArcType.ghost, so the [EXP-017] in the shall sentence is a citation, not a dependency (EXP-017 depends on EXP-016); likewise MOD-040 in the Depends-on line is a spec cross-reference (MOD-040, wave W8, cites this block), not a Lean import. 'MUST produce no cluster subgraphs' on a net without metadata and without / is a consequence of the first and third lines (EXP_016_ac4)."
          "AC1 (cluster_b1 and cluster_b2 for instances b1 and b2) and AC3 (cluster_outer containing cluster_outer_inner) are decided on the reference in EXP_016_nonvacuous, and follow from the third, fifth and sixth lines for every exporter meeting the block. AC2, restated by ruling D26 item 5 to count nested cluster blocks and the junctions of a cluster's transitions, follows from the first and third lines (EXP_016_ac2): a node is inside the cluster of K, directly or through a nested cluster, exactly when its key is K or has K as a /-prefix."
          "AC4 (no / in any node name and no membership metadata gives no cluster) is EXP_016_ac4, for every exporter meeting the block on a net meeting EXP-014's name assumption. AC5: the regex half (cluster_[A-Za-z0-9_]+) is EXP_016_ac5 for every cluster with a non-empty key, and the name assumption makes every key of the net's names non-empty; the determinism half has no content over a Lean function, which is deterministic, and is kind Q. AC6 (Java, TypeScript and Rust produce byte-identical cluster blocks) is a property of three programs and kind Q by ruling D60 (c); the runtimes differ today in the order of sibling clusters (ruling R2 (exp-b)). AC7, restated by ruling D26 item 7 to shared places whose names carry no instance prefix, is the first line under a membership map, decided on a directly composed net in EXP_016_nonvacuous."
          "The test derivation (compose two instances, nested instances and a direct composition; assert blocks, members and sanitised IDs) is AC1, AC3, AC2, AC5 and AC7 on composed nets; how compose builds names and the membership map is MOD-010, MOD-013 and MOD-026 on the composition model (W8), and the block quantifies over every net and membership map the mapper can see."
  signoff "2026-11-13 2fc6972b040c7f87 ai"
  statement : Exporter → Prop :=
    fun E => ∀ (cfg : ExportCfg) (X : ExportNet), X.ClusterNames cfg.cluster →
      (∀ n ∈ (E cfg X).nodes, ∀ c ∈ (E cfg X).clusters,
        n.ref ∈ c.members ↔ nodeKey cfg.cluster X.member n.ref = some c.key) ∧
      (∀ c ∈ (E cfg X).clusters, (∀ r ∈ c.members, ∃ n ∈ (E cfg X).nodes, n.ref = r) ∧
        ((X.trans.map ExportTrans.name).Nodup → c.members.Nodup)) ∧
      (∀ q, q ∈ (E cfg X).clusters.map XCluster.key ↔
        ∃ n ∈ (E cfg X).nodes, ∃ K, nodeKey cfg.cluster X.member n.ref = some K ∧
          (q = K ∨ IsSlashPrefix q K)) ∧
      ((E cfg X).clusters.map XCluster.key).Nodup ∧
      (∀ c ∈ (E cfg X).clusters, c.parent = instancePrefix c.key) ∧
      (∀ c ∈ (E cfg X).clusters, c.id = clusterId c.key ∧ c.label = c.key) ∧
      ((E cfg X).nodes.Perm (E { cfg with cluster := .none } X).nodes ∧
        ((E cfg X).edges.filter fun e => e.arc != .ghost).Perm
          ((E { cfg with cluster := .none } X).edges.filter fun e => e.arc != .ghost))

/- The pinned readable form of EXP-016: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_016 : Exporter → Prop :=
fun E =>
  ∀ (cfg : ExportCfg) (X : ExportNet),
    ExportNet.ClusterNames cfg.cluster X →
      (∀ n ∈ (E cfg X).nodes,
          ∀ c ∈ (E cfg X).clusters, n.ref ∈ c.members ↔ nodeKey cfg.cluster X.member n.ref = some c.key) ∧
        (∀ c ∈ (E cfg X).clusters,
            (∀ r ∈ c.members, ∃ n ∈ (E cfg X).nodes, n.ref = r) ∧
              ((List.map ExportTrans.name X.trans).Nodup → c.members.Nodup)) ∧
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
#guard_msgs in #print EXP_016

/-! ## The reference meets EXP-016 -/

/-- The nodes of the reference exporter do not depend on the cluster source. -/
theorem exp016_refNodes_cluster (cfg : ExportCfg) (X : ExportNet) (src : ClusterSource) :
    refNodes { cfg with cluster := src } X = refNodes cfg X := rfl

/-- **The clustered reference exporter meets EXP-016**, for every net, whatever its names (the
name assumption is not needed by the reference, which keys a node by its name, not its ID, and
stays total on keys with an empty segment). -/
@[evidence holds EXP_016]
theorem EXP_016_reference : EXP_016 refExport := by
  intro cfg X _
  have hnodes : ∀ n ∈ (refExport cfg X).nodes, n.ref ∈ refNodeRefs X := by
    intro n hn
    rw [← refExport_nodeRefs (cfg := cfg)]
    exact List.mem_map_of_mem hn
  have hdrawn : ∀ r ∈ refNodeRefs X, ∃ n ∈ (refExport cfg X).nodes, n.ref = r := by
    intro r hr
    rw [← refExport_nodeRefs (cfg := cfg)] at hr
    exact List.mem_map.mp hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn c hc
    rw [refExport_clusters] at hc
    exact refClusters_member hc (hnodes n hn)
  · intro c hc
    rw [refExport_clusters] at hc
    refine ⟨fun r hr => hdrawn r (((refClusters_fields hc).2.2.2 r).mp hr).1, fun hT => ?_⟩
    obtain ⟨k, -, rfl⟩ := mem_refClusters.mp hc
    exact (exp014_refNodeRefs_nodup hT).filter _
  · intro q
    rw [refExport_clusters, refClusters_keys, mem_refClusterKeys]
    constructor
    · rintro ⟨r, hr, K, hK, h⟩
      obtain ⟨n, hn, rfl⟩ := hdrawn r hr
      exact ⟨n, hn, K, hK, h⟩
    · rintro ⟨n, hn, K, hK, h⟩
      exact ⟨n.ref, hnodes n hn, K, hK, h⟩
  · rw [refExport_clusters, refClusters_keys]
    exact refClusterKeys_nodup
  · intro c hc
    rw [refExport_clusters] at hc
    exact (refClusters_fields hc).2.2.1
  · intro c hc
    rw [refExport_clusters] at hc
    exact ⟨(refClusters_fields hc).1, (refClusters_fields hc).2.1⟩
  · refine ⟨?_, ?_⟩
    · show (refNodes cfg X).Perm (refNodes { cfg with cluster := .none } X)
      exact List.Perm.of_eq (exp016_refNodes_cluster cfg X .none).symm
    · rw [refExport_nonGhost_flat, refExport_nonGhost_flat]
      rfl

/-! ## Example nets -/

/-- A transition `name` with one input place `i` and the output spec `o`. -/
def exp016Trans (name i : String) (o : OutTree) : ExportTrans :=
  { core := ⟨name, [⟨i, .one⟩], [], [], []⟩, out := some o }

/-- A nested instance: `outer/inner/t` from `outer/inner/p` to `outer/q` (keys `outer/inner` and
`outer`). -/
def exp016NestNet : ExportNet :=
  { trans := [exp016Trans "outer/inner/t" "outer/inner/p" (.place "outer/q")] }

/-- A nested instance whose outer prefix keys no node: `outer/inner/t` from `outer/inner/p` to
`outer/inner/q` (the cluster `outer` has no direct member). -/
def exp016DeepNet : ExportNet :=
  { trans := [exp016Trans "outer/inner/t" "outer/inner/p" (.place "outer/inner/q")] }

/-- A clustered `Xor` transition: `b/t` from `b/i` to `XOR(b/x, b/y)`; its junction has key `b`. -/
def exp016JNet : ExportNet :=
  { trans := [exp016Trans "b/t" "b/i" (.xor [.place "b/x", .place "b/y"])] }

/-- Membership metadata and an instance prefix in one net: `A` and `a` belong to subnet `S`,
`A` moves a token from `a` to `b/c`, which has no entry and the prefix `b`. -/
def exp016MetaNet : ExportNet :=
  { trans := [exp016Trans "A" "a" (.place "b/c")],
    member := fun s => if s = "A" ∨ s = "a" then some "S" else none }

/-- MOD-040's example: a transition `s1/t` and a place `s1/obs/TURN` inside the instance `s1`
(key `s1/obs`, while `subnetOf` walks up to `s1`). -/
def exp016WalkNet : ExportNet :=
  { trans := [exp016Trans "s1/t" "s1/obs/TURN" (.place "s1/o")] }

/-- An edge across two clusters: `b1/t` from `b1/a` to `b2/x`. -/
def exp016CrossNet : ExportNet :=
  { trans := [exp016Trans "b1/t" "b1/a" (.place "b2/x")] }

/-! ## Wrong exporters, one or more per line -/

/-- The reference with another key function `kf` (per cluster source, net and node): the
clusters and ghost edges of that key. -/
def exp016ByKey (kf : ClusterSource → ExportNet → NodeRef → Option String) : Exporter :=
  refExportWith (ClusterStage.byKey kf)

/-- The reference with every cluster changed by `f`. -/
def exp016MapClusters (f : XCluster → XCluster) : Exporter := fun cfg X =>
  let g := refExport cfg X
  { g with clusters := g.clusters.map f }

/-- The part of a name before its first `/`, none without `/` or when it is empty. -/
def exp016FirstPrefix (s : String) : Option String :=
  if '/' ∈ s.toList then
    let u := s.toList.takeWhile (· ≠ '/')
    if u.isEmpty then none else some (String.ofList u)
  else none

/-- A mapper that keys a node by the part of its name before the first `/`. -/
def exp016_firstSlash : Exporter := exp016ByKey fun src X r =>
  match src with
  | .auto => (X.member r.keyName).or (exp016FirstPrefix r.keyName)
  | .metadata => X.member r.keyName
  | .prefix => exp016FirstPrefix r.keyName
  | .none => none

/-- ✗ The first-`/` key violates EXP-016 on `outer/inner/t` (line 1: the transition sits in
`cluster_outer`, but its key is `outer/inner`). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_firstSlash : ¬ EXP_016 exp016_firstSlash := by
  intro h
  have := (h {} exp016NestNet (by decide)).1
  revert this
  decide

/-- A mapper whose default source reads the membership metadata only, as soon as a net carries
any. -/
def exp016_metadataDefault : Exporter := exp016ByKey fun src X r =>
  match src with
  | .auto => X.member r.keyName
  | s => nodeKey s X.member r

/-- ✗ Metadata only under the default source violates EXP-016 on a net that mixes a membership
entry with the instance prefix `b` (line 3: `b/c` has the key `b`, and no cluster has it). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_metadataDefault : ¬ EXP_016 exp016_metadataDefault := by
  intro h
  have hw : ∃ n ∈ (exp016_metadataDefault {} exp016MetaNet).nodes,
      nodeKey ({} : ExportCfg).cluster exp016MetaNet.member n.ref = some "b" := by decide
  obtain ⟨n, hn, hK⟩ := hw
  have := ((h {} exp016MetaNet (by decide)).2.2.1 "b").mpr ⟨n, hn, "b", hK, Or.inl rfl⟩
  revert this
  decide

/-- MOD-040's `subnetOf` fall-back: the longest `/`-prefix of the name under which some
transition of the net lives. -/
def exp016WalkUp (X : ExportNet) (s : String) : Option String :=
  (((cutsAux [] s.toList).filter fun u => !u.isEmpty).reverse.find? fun u =>
    X.trans.any fun t => decide (u ++ ['/'] <+: t.name.toList)).map String.ofList

/-- A mapper that clusters by MOD-040's `subnetOf` (membership entry, else the walk-up prefix). -/
def exp016_walkUp : Exporter := exp016ByKey fun src X r =>
  match src with
  | .auto => (X.member r.keyName).or (exp016WalkUp X r.keyName)
  | .prefix => exp016WalkUp X r.keyName
  | s => nodeKey s X.member r

/-- ✗ Clustering by `subnetOf` violates EXP-016 on MOD-040's own example (line 1: `s1/obs/TURN`
sits in `cluster_s1`, but its key is `s1/obs`). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_walkUp : ¬ EXP_016 exp016_walkUp := by
  intro h
  have := (h {} exp016WalkNet (by decide)).1
  revert this
  decide

/-- A mapper that leaves every junction node at the top level. -/
def exp016_junctionTop : Exporter := exp016ByKey fun src X r =>
  match r with
  | .junction .. => none
  | _ => nodeKey src X.member r

/-- ✗ Junctions at the top level violate EXP-016 on `b/t` with `XOR(b/x, b/y)` (line 1: the
junction has its transition's key `b` and is in no cluster). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_junctionTop : ¬ EXP_016 exp016_junctionTop := by
  intro h
  have := (h {} exp016JNet (by decide)).1
  revert this
  decide

/-- A mapper that lists a node it does not draw in every cluster. -/
def exp016_phantomMember : Exporter :=
  exp016MapClusters fun c => { c with members := c.members ++ [.place "phantom"] }

/-- ✗ A member no node stands for violates EXP-016 (line 2). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_phantomMember : ¬ EXP_016 exp016_phantomMember := by
  intro h
  have := (h {} exp016NestNet (by decide)).2.1
  revert this
  decide

/-- A mapper that lists every junction member of a cluster a second time (the junction's node
statement would appear twice in the cluster block). -/
def exp016_dupJunction : Exporter :=
  exp016MapClusters fun c => { c with members := c.members ++ c.members.filter fun
    | .junction .. => true
    | _ => false }

/-- ✗ Listing a member twice violates EXP-016 on `b/t` with `XOR(b/x, b/y)`, whose transition names
are distinct (line 2: the junction of `b/t` is listed twice in `cluster_b`). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_dupJunction : ¬ EXP_016 exp016_dupJunction := by
  intro h
  have := (h {} exp016JNet (by decide)).2.1
  revert this
  decide

/-- A mapper that draws one more, empty cluster `extra`. -/
def exp016_extraCluster : Exporter := fun cfg X =>
  let g := refExport cfg X
  { g with clusters := g.clusters ++ [⟨"extra", clusterId "extra", "extra", none, []⟩] }

/-- ✗ A cluster for a key no node has violates EXP-016 (line 3, from left to right). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_extraCluster : ¬ EXP_016 exp016_extraCluster := by
  intro h
  have hk : "extra" ∈ (exp016_extraCluster {} exp016NestNet).clusters.map XCluster.key := by
    decide
  obtain ⟨n, hn, K, hK, hq⟩ := ((h {} exp016NestNet (by decide)).2.2.1 "extra").mp hk
  have hno : ∀ n ∈ (exp016_extraCluster {} exp016NestNet).nodes,
      ∀ K ∈ (nodeKey ({} : ExportCfg).cluster exp016NestNet.member n.ref).toList,
        ¬ ("extra" = K ∨ IsSlashPrefix "extra" K) := by decide
  exact hno n hn K (by rw [hK]; simp) hq

/-- A mapper that draws a cluster only for a key some node has, without the clusters of their
`/`-prefixes. -/
def exp016_noChain : Exporter := fun cfg X =>
  let g := refExport cfg X
  { g with clusters := g.clusters.filter fun c => !c.members.isEmpty }

/-- ✗ Leaving out the cluster of a `/`-prefix violates EXP-016 on `outer/inner/t` with its
places in `outer/inner` (line 3, from right to left: `outer` is a `/`-prefix of the key
`outer/inner` and has no cluster). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_noChain : ¬ EXP_016 exp016_noChain := by
  intro h
  have hw : ∃ n ∈ (exp016_noChain {} exp016DeepNet).nodes,
      nodeKey ({} : ExportCfg).cluster exp016DeepNet.member n.ref = some "outer/inner" := by
    decide
  obtain ⟨n, hn, hK⟩ := hw
  have := ((h {} exp016DeepNet (by decide)).2.2.1 "outer").mpr
    ⟨n, hn, "outer/inner", hK, Or.inr (by decide)⟩
  revert this
  decide

/-- A mapper that draws every cluster twice. -/
def exp016_dupClusters : Exporter := fun cfg X =>
  let g := refExport cfg X
  { g with clusters := g.clusters ++ g.clusters }

/-- ✗ Two clusters with one key violate EXP-016 (line 4). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_dupClusters : ¬ EXP_016 exp016_dupClusters := by
  intro h
  have := (h {} exp016NestNet (by decide)).2.2.2.1
  revert this
  decide

/-- A mapper that draws every cluster at the top level (no nesting). -/
def exp016_noNesting : Exporter := exp016MapClusters fun c => { c with parent := none }

/-- ✗ Flat clusters violate EXP-016 on a nested instance (line 5: `outer/inner` belongs in
`outer`). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_noNesting : ¬ EXP_016 exp016_noNesting := by
  intro h
  have := (h {} exp016DeepNet (by decide)).2.2.2.2.1
  revert this
  decide

/-- A mapper that writes the key into the cluster ID unsanitised. -/
def exp016_rawId : Exporter := exp016MapClusters fun c => { c with id := "cluster_" ++ c.key }

/-- ✗ An unsanitised cluster ID violates EXP-016 (line 6: `cluster_outer/inner` for
`cluster_outer_inner`). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_rawId : ¬ EXP_016 exp016_rawId := by
  intro h
  have := (h {} exp016DeepNet (by decide)).2.2.2.2.2.1
  revert this
  decide

/-- A mapper that labels a cluster with its sanitised key. -/
def exp016_sanitizedLabel : Exporter :=
  exp016MapClusters fun c => { c with label := sanitize c.key }

/-- ✗ A sanitised cluster label violates EXP-016 (line 6: the label of `outer/inner` is
`outer/inner`, not `outer_inner`). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_sanitizedLabel : ¬ EXP_016 exp016_sanitizedLabel := by
  intro h
  have := (h {} exp016DeepNet (by decide)).2.2.2.2.2.1
  revert this
  decide

/-- A mapper that, when it clusters, drops every edge whose ends have different cluster keys. -/
def exp016_dropCross : Exporter := fun cfg X =>
  let g := refExport cfg X
  if cfg.cluster = .none then g else
    { g with edges := g.edges.filter fun e =>
        nodeKey cfg.cluster X.member e.src == nodeKey cfg.cluster X.member e.dst }

/-- ✗ Dropping the edges between clusters violates EXP-016 on `b1/t` with output `b2/x` (line 7:
the edge into `b2/x` is drawn without clustering). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_dropCross : ¬ EXP_016 exp016_dropCross := by
  intro h
  have := (h {} exp016CrossNet (by decide)).2.2.2.2.2.2.2
  revert this
  decide

/-- A mapper that, when it clusters, scopes the ID of a node with a key by its cluster ID. -/
def exp016_scopedIds : Exporter := fun cfg X =>
  let g := refExport cfg X
  { g with nodes := g.nodes.map fun n =>
      match nodeKey cfg.cluster X.member n.ref with
      | some k => { n with id := clusterId k ++ "__" ++ n.id }
      | none => n }

/-- ✗ Renaming the nodes under clustering violates EXP-016 (line 7: the nodes differ from those
drawn without clustering). -/
@[evidence forbids EXP_016]
theorem EXP_016_forbids_scopedIds : ¬ EXP_016 exp016_scopedIds := by
  intro h
  have := (h {} exp016CrossNet (by decide)).2.2.2.2.2.2.1
  revert this
  decide

/-- `b1/t` moves a token from `b1/x` to `b1_x`: the cluster keys are well formed, but the two
places share the ID `p_b1_x`. -/
def exp016CollideNet : ExportNet :=
  { trans := [exp016Trans "b1/t" "b1/x" (.place "b1_x")] }

/-- **Why the name assumption includes EXP-014's**: on `exp016CollideNet` the cluster keys are well
formed, yet `b1/x` (key `b1`) and `b1_x` (no key) get one node ID, so one DOT node would have to sit
both in `cluster_b1` and at the top level; all three runtimes route a node to its cluster by its ID
and put it in `cluster_b1`. The net is outside `ExportNet.IdNames`, so the block says nothing on
it. -/
theorem exp016_collide_outside :
    exp016CollideNet.ClusterKeysWellFormed .auto ∧ ¬ exp016CollideNet.IdNames ∧
      nodeId (.place "b1/x") = nodeId (.place "b1_x") ∧
      nodeKey .auto exp016CollideNet.member (.place "b1/x") = some "b1" ∧
      nodeKey .auto exp016CollideNet.member (.place "b1_x") = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ASCII node names, with the transition `t` placed by membership metadata in the subnet
`Größe`. -/
def exp016NonAsciiNet : ExportNet :=
  { trans := [exp016Trans "t" "a" (.place "b")],
    member := fun n => if n = "t" then some "Größe" else none }

/-- **Why the cluster keys must be ASCII**: on `exp016NonAsciiNet` every node name is ASCII and
EXP-014's name assumption holds, but the membership key `Größe` is not ASCII, so the net is
outside `ExportNet.ClusterNames`. The glossary's `clusterId` gives `cluster_Gr__e`, as Java and
TypeScript draw it; Rust's sanitize keeps the letters and draws `cluster_Größe` (ruling D46 (a):
non-ASCII characters are implementation-defined). -/
theorem exp016_nonAsciiKey_outside :
    exp016NonAsciiNet.IdNames ∧ ¬ exp016NonAsciiNet.ClusterKeysWellFormed .auto ∧
      clusterId "Größe" = "cluster_Gr__e" ∧ clusterId "Größe" ≠ "cluster_Größe" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Non-vacuity and the acceptance criteria -/

/-- Two top-level instances `b1` and `b2` (AC1): `b1/t` from `b1/a` to `b1/b`, `b2/t` from `b2/a`
to `b2/b`. -/
def exp016TwoNet : ExportNet :=
  { trans := [exp016Trans "b1/t" "b1/a" (.place "b1/b"), exp016Trans "b2/t" "b2/a" (.place "b2/b")] }

/-- A directly composed net (AC7): subnets `S1` (`T1`, `p1`) and `S2` (`T2`, `p2`), the shared
place `hub` without an entry and without a prefix, and the shared place `rv/x` without an entry,
which falls back to its prefix `rv`. -/
def exp016DirectNet : ExportNet :=
  { trans := [exp016Trans "T1" "hub" (.place "p1"), exp016Trans "T2" "p2" (.place "rv/x")],
    member := fun s =>
      if s = "T1" ∨ s = "p1" then some "S1" else if s = "T2" ∨ s = "p2" then some "S2" else none }

/-- The clusters of a graph as (ID, label, parent key, member IDs). -/
def exp016Clusters (g : XGraph) : List (String × String × Option String × List String) :=
  g.clusters.map fun c => (c.id, c.label, c.parent, c.members.map nodeId)

/-- The IDs of a graph's top-level nodes (in no cluster). -/
def exp016TopLevel (g : XGraph) : List String :=
  (g.nodes.filter fun n => g.clusters.all fun c => !(c.members.contains n.ref)).map XNode.id

/-- The name assumption holds of the examples, and on the reference: two instances give
`cluster_b1` and `cluster_b2` with their nodes (AC1); a nested instance gives `cluster_outer`
with `cluster_outer_inner` nested in it (AC3); the junction of `b/t` sits in `cluster_b` (ruling
D26 item 5); a directly composed net gives `cluster_S1` and `cluster_S2` with the private nodes,
the shared place `hub` at the top level and the shared place `rv/x` in `cluster_rv` by its prefix
(AC7 and ruling D26 item 7); MOD-040's `s1/obs/TURN` sits in `cluster_s1_obs`, nested in
`cluster_s1`. -/
@[evidence nonvacuous EXP_016]
theorem EXP_016_nonvacuous :
    exp016TwoNet.ClusterNames .auto ∧ exp016DeepNet.ClusterNames .auto ∧
    exp016JNet.ClusterNames .auto ∧ exp016DirectNet.ClusterNames .auto ∧
    exp016WalkNet.ClusterNames .auto ∧
    exp016Clusters (refExport {} exp016TwoNet) =
      [("cluster_b1", "b1", none, ["p_b1_a", "p_b1_b", "t_b1_t"]),
       ("cluster_b2", "b2", none, ["p_b2_a", "p_b2_b", "t_b2_t"])] ∧
    exp016Clusters (refExport {} exp016DeepNet) =
      [("cluster_outer", "outer", none, []),
       ("cluster_outer_inner", "outer/inner", some "outer",
         ["p_outer_inner_p", "p_outer_inner_q", "t_outer_inner_t"])] ∧
    exp016Clusters (refExport {} exp016JNet) =
      [("cluster_b", "b", none, ["p_b_i", "p_b_x", "p_b_y", "t_b_t", "j_b_t__xor_0"])] ∧
    exp016Clusters (refExport {} exp016DirectNet) =
      [("cluster_S1", "S1", none, ["p_p1", "t_T1"]),
       ("cluster_S2", "S2", none, ["p_p2", "t_T2"]),
       ("cluster_rv", "rv", none, ["p_rv_x"])] ∧
    exp016TopLevel (refExport {} exp016DirectNet) = ["p_hub"] ∧
    exp016Clusters (refExport {} exp016WalkNet) =
      [("cluster_s1", "s1", none, ["p_s1_o", "t_s1_t"]),
       ("cluster_s1_obs", "s1/obs", some "s1", ["p_s1_obs_TURN"])] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **AC2 for every exporter meeting EXP-016** (restated by ruling D26 item 5): a drawn node is a
direct member of a cluster whose key is `K` or has `K` as a `/`-prefix (the cluster of `K` or one
nested in it) exactly when its own key is `K` or has `K` as a `/`-prefix; a junction counts by its
transition's key. -/
@[evidence cites "EXP-016" "AC2: each cluster block contains, directly or through the cluster blocks nested in it, exactly the places and transitions whose cluster key is the cluster's key or begins with it followed by /, and the junction nodes of those transitions, for every exporter meeting EXP-016"]
theorem EXP_016_ac2 (E : Exporter) (hE : EXP_016 E) (cfg : ExportCfg) (X : ExportNet)
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
    refine ⟨c, hc, by rw [hck]; exact hk, (h1 n hn c hc).mpr (by rw [hck]; exact hK')⟩

/-- A name without `/` and without a membership entry has no cluster key, under every source. -/
theorem exp016_clusterKey_none (src : ClusterSource) (m : String → Option String) (s : String)
    (h1 : '/' ∉ s.toList) (h2 : m s = none) : clusterKey src m s = none := by
  cases src <;> simp [clusterKey, h2, instancePrefix_eq_none_of _ h1]

/-- **AC4 for every exporter meeting EXP-016**: on a net that meets EXP-014's name assumption, with
no `/` in any place or transition name and no membership entry, an exporter meeting the block whose
nodes stand for names of that kind draws no cluster, under every cluster source. -/
@[evidence cites "EXP-016" "AC4: a net with no / in any node name and no membership metadata produces no cluster subgraphs, for every exporter meeting EXP-016"]
theorem EXP_016_ac4 (E : Exporter) (hE : EXP_016 E) (cfg : ExportCfg) (X : ExportNet)
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

/-- A character AC5's regex allows after `cluster_`: an ASCII letter or digit, or `_`. -/
def exp016IdChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- **AC5's regex** `cluster_[A-Za-z0-9_]+`, as a predicate on a string. -/
def exp016ClusterIdShape (id : String) : Prop :=
  ∃ s, id = "cluster_" ++ s ∧ s ≠ "" ∧ ∀ c ∈ s.toList, exp016IdChar c = true

/-- **AC5 for every exporter meeting EXP-016**: every cluster with a non-empty key has an ID that
matches `cluster_[A-Za-z0-9_]+`; the name assumption makes every key of the net's names
non-empty. -/
@[evidence cites "EXP-016" "AC5: cluster IDs match the regex cluster_[A-Za-z0-9_]+, for every exporter meeting EXP-016, for every cluster whose key is not empty"]
theorem EXP_016_ac5 (E : Exporter) (hE : EXP_016 E) (cfg : ExportCfg) (X : ExportNet)
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

end Libpetri.Spec
