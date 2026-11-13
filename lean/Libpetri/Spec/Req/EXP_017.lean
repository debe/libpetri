import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryExport
import Libpetri.Reference.Export
import Libpetri.Reference.ExportCluster
import Libpetri.Spec.Req.EXP_016
import Libpetri.Spec.Text.EXP_017

set_option linter.missingDocs true

/-!
# EXP-017: compound cluster layout hints (`spec/09-export.md`)

The `compound` graph attribute and the invisible ghost edges an exporter adds between two
clusters that a top-level node bridges in one hop. The requirement is a predicate over an
abstract exporter `E : Exporter` (glossary `GlossaryExport.lean`). It reads, off the graph
`E cfg X` itself, the bridges ([EXP-017] sentence of ruling D26 item 6): every
`((X, Y), (a, b))` such that some node `o` of the graph with no cluster key has an edge `a → o`
with `a` of key `X` and an edge `o → b` with `b` of key `Y`, and `X ≠ Y`, over the non-ghost
edges, of every arc type, in the direction drawn, in the scan order the spec fixes (nodes in
their order, then the edges into `o`, then the edges out of `o`). The cluster key of a node is
EXP-016's (`nodeKey` of `Reference/ExportCluster.lean`, under the configuration's cluster source
and the net's membership map), so a node with a key lies in the deepest cluster of that key and a
junction has its transition's key.

Five lines: `compound` is set, on every net; and, on nets that meet EXP-016's name assumption
(`ExportNet.ClusterNames`, ruling D46), every bridged ordered pair has a ghost edge at the anchors
of its first bridge, clipped at the pair's two cluster IDs; every ghost edge is such an edge; at
most one ghost edge per ordered key pair; the edges other than ghost edges are, up to order, those
drawn with no clustering.

The witness is the reference exporter `refExport` (`Reference/ExportCluster.lean`), the mapper of
`Reference/Export.lean` with the reference cluster stage. The wrong exporters are those the export
design and the exp-b map name: no `compound`, no ghost edges, unordered pairs (AC4), a ghost edge
for one cluster on both sides (AC5), the last bridge as anchor, the literal reading of the anchor
sentence (the `b` of the first edge out of `o`), no dedup (AC3), plus two for the readings of
ruling D26 item 6 (the outermost cluster in place of the deepest, token flow in place of drawn
edges) and one that draws the ghost edge a second time as a visible edge. Each line of the
statement has a mutant that fails it alone (the examples at the end of the file). One more mutant
leaves out a cluster and a cluster nested in it, the geometric reading of `X == Y`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## What the block reads off a drawn graph -/

/-- The edges of `g` that are not ghost edges, in the order drawn (the visible edge set). -/
def exp017Real (g : XGraph) : List XEdge := g.edges.filter fun e => e.arc != .ghost

/-- The ghost edges of `g`, in the order drawn. -/
def exp017Ghosts (g : XGraph) : List XEdge := g.edges.filter fun e => e.arc == .ghost

/-- **The bridges of a drawn graph** under configuration `cfg` and net `X`: the bridge witnesses
(`bridgeWitnesses`) over the nodes of `g` in their order and its non-ghost edges in their order,
keys by EXP-016's `nodeKey` under the configuration's cluster source and the net's membership
map. -/
def exp017Bridges (cfg : ExportCfg) (X : ExportNet) (g : XGraph) :
    List ((String × String) × (NodeRef × NodeRef)) :=
  bridgeWitnesses (nodeKey cfg.cluster X.member) (g.nodes.map XNode.ref) (exp017Real g)

/-- The first bridge in `ws` whose ordered key pair is `xy`. -/
def exp017First (ws : List ((String × String) × (NodeRef × NodeRef))) (xy : String × String) :
    Option ((String × String) × (NodeRef × NodeRef)) :=
  ws.find? fun q => decide (q.1 = xy)

/-- What the block reads of an edge: its source, its target, `ltail` and `lhead`. -/
def exp017Ends (e : XEdge) : NodeRef × NodeRef × Option String × Option String :=
  (e.src, e.dst, e.ltail, e.lhead)

/-- The ghost edge a bridge asks for: from its anchor `a` to its anchor `b`, `ltail` the cluster
ID of `X`, `lhead` the cluster ID of `Y`. -/
def exp017Hint (p : (String × String) × (NodeRef × NodeRef)) :
    NodeRef × NodeRef × Option String × Option String :=
  (p.2.1, p.2.2, some (clusterId p.1.1), some (clusterId p.1.2))

/-- The ordered pair of cluster keys of the two ends of an edge. -/
def exp017KeyPair (cfg : ExportCfg) (X : ExportNet) (e : XEdge) : Option String × Option String :=
  (nodeKey cfg.cluster X.member e.src, nodeKey cfg.cluster X.member e.dst)

/-! ## EXP-017: compound cluster layout hints -/

requirement EXP_017
  id "EXP-017"
  title "Compound Cluster Layout Hints"
  kind F
  scope "every exporter, the graph attribute compound and the ghost edges between clusters"
  source verbatim "spec/09-export.md"
  covers EXP_017.s1, EXP_017.s2, EXP_017.s3, EXP_017.s4, EXP_017.s5, EXP_017.s6, EXP_017.s7,
        EXP_017.s8, EXP_017.s9, EXP_017.s10, EXP_017.s11, EXP_017.s12, EXP_017.s13, EXP_017.s14,
        EXP_017.s15, EXP_017.s16, EXP_017.s17, EXP_017.s18, EXP_017.s19, EXP_017.s20, EXP_017.s21
  reading "For every configuration cfg and net X, in the graph E cfg X, with the bridges ws read off that graph (exp017Bridges: the bridge witnesses over its nodes in their order and its non-ghost edges in their order, keys by EXP-016's nodeKey under cfg's cluster source and X's membership map):"
          "the graph attribute compound is true;"
          "and, when X meets EXP-016's name assumption under cfg's cluster source (ExportNet.ClusterNames), the following four lines hold:"
          "for every bridge w in ws, some ghost edge of the graph (an edge of arc type ghost) runs from the anchor a to the anchor b of the first bridge in ws with w's ordered key pair, with ltail the cluster ID of its first key and lhead the cluster ID of its second (exp017Hint);"
          "every ghost edge of the graph is, in its ends, ltail and lhead, the ghost edge of a bridge p in ws that is the first bridge with its ordered key pair;"
          "the ordered pairs of cluster keys of the two ends of the ghost edges are pairwise distinct;"
          "and the edges other than ghost edges are, up to order (List.Perm), those of E drawn for X under cfg with cluster source none."
  assumes "The model is an exporter E : Exporter (glossary): from a configuration (with its cluster source, EXP-016) and the export view of a net (with its membership map, MOD-026), the typed graph a mapper builds before DOT text. The block reads the compound attribute, the nodes in their order and the edges in their order; a ghost edge is an edge of arc type ghost, and of it the block reads its source, target, ltail and lhead."
          "The cluster key of a node is EXP-016's (nodeKey: the membership entry, else the part of the name before its last /, per cluster source; a junction has its transition's key). So the key of a node is its deepest cluster: outer/inner/a to an orphan to other/b bridges (outer/inner, other) and not (outer, other), and outer/a to an orphan to outer/inner/b bridges a cluster to its own child (ruling D26 item 6; exp_b probe cases 8 and 9; exp017NetE in EXP_017_nonvacuous, EXP_017_forbids_skipNested). The sentence 'Orphan paths that fall entirely inside a single cluster (X == Y)' compares keys, not the drawn boxes: both ends of outer/a to o to outer/inner/b lie inside the box of outer, yet the keys differ and the pair is bridged, as the quoted sentence on nested clusters says. Graphviz may warn about and ignore ltail and lhead when one cluster contains the other, so such a ghost edge may constrain less than a ghost edge between two sibling clusters; whether to keep drawing it is a feature question outside the migration. A place shared by two subnets of a direct composition has no membership entry and no prefix, so it is an orphan too. Cluster IDs are compared as EXP-016 draws them (clusterId, cluster_ followed by the sanitised key)."
          "Ruling D46 (a) with (x), kind A: lines 2 to 5 cover the nets EXP-016 covers, as the scope sentence of the requirement says: nets that meet ExportNet.ClusterNames under cfg's cluster source (EXP-014's name assumption, and every cluster key ASCII and non-empty with no empty /-segment). The compound line binds every net, since its sentence says 'in every export'. On other nets the runtimes do not draw what lines 2 to 5 would ask. All three look a node's key up by its DOT ID (node_id_to_prefix in Rust, nodeIdToPrefix in Java and TypeScript), so on a net where b1/t outputs to b1_x, b2/u consumes b1_x and b1/v consumes b1/x, the place b1/x gives the shared ID p_b1_x the key b1, the orphan b1_x is not seen as an orphan, and no runtime draws the ghost edge for (b1, b2) that the bridges keyed by node reference ask for. On a non-ASCII membership key Rust draws a cluster ID that the glossary's clusterId does not give. The Unicode cluster ID is implementation-defined under ruling D46 (a), and the lookup by DOT ID is the Known limit sentence of EXP-016; the block is silent on such nets. A key with an empty segment (a name such as a//x) is outside the premise only because EXP-016's scope sentence excludes it: all three mappers register the key chain the reference draws there (see EXP-016). Inside the premise a cluster key may hold the NUL character (it is ASCII), and the block binds on such nets. All three mappers dedup ghost edges by the ordered pair: Rust keys by the (String, String) pair, Java by List.of(X, Y), and TypeScript by the string of the length of X, a colon, X and Y, which no two pairs share (ghostEdgesDedupByOrderedPair_nulInKeyDoesNotMerge_EXP017 in Java, the EXP-017 ordered-pair test of typescript/tests/export/cluster-builder.test.ts). A dedup by the string X, NUL, Y (the behaviour RD-37 recorded) merges the distinct pairs (a NUL b, c) and (a, b NUL c) and draws one ghost edge where the second line asks for two (EXP_017_forbids_nulDedup on exp017NulNet). The reference meets the block without the premise (EXP_017_reference does not use it), and every mutant below fails it on a net that meets the premise."
          "Bridges are read over the drawn edges of every arc type in the direction drawn (ruling D26 item 6), as all three mappers scan them: a reset edge into an orphan place and a read edge out of it bridge two clusters although no token moves between them (exp_b probe case F, EXP_017_forbids_tokenFlow), and an orphan transition whose output spec has a junction bridges nothing through it, since its junction is itself an orphan whose only incoming edge leaves the keyless transition. Whether these should change is a feature question outside the migration. The ghost edges are left out of the scan; they join two nodes with keys, so they would bridge nothing anyway, and the quoted definition of an edge leaves them out, so the definition does not refer to itself."
          "The scan order is the graph's own node and edge order, so the first bridge depends on the order the exporter draws its nodes and edges, which differs between the runtimes (ruling R2 (exp-b)) and is stated by no requirement. The block fixes the anchors relative to the drawn order, which is what each mapper computes."
          "Order of the ghost edges is not stated: the second and third lines are membership statements and the fourth line counts, so the ghost edges are compared up to order. Order of the other edges is not stated either: the fifth line compares them with the edges drawn under cluster source none up to order (List.Perm), the visible edge set of the body, as EXP-016's seventh line does. The first bridge is read in the order of the graph drawn under cfg, so an exporter that draws its edges in another order when it clusters anchors at the first bridge of that order."
          "The style of a ghost edge (style invis, arrowhead none) is a visual constant of the DOT renderer, checked by tests (kind Q); so is the claim that the line is a no-op for flat nets in Graphviz. That ghost edges change no cluster membership is EXP-016's (its members are read off node keys, not edges); the fifth line states that they change no other edge."
          "The header says SHOULD and the body MUST; the EARS sentences read an exporter that clusters shall (ruling D26 item 7). The SHOULD priority is whether an exporter clusters at all. The predicate is what an exporter that clusters draws: its bridges are read off the cluster keys (nodeKey under cfg's cluster source and X's membership map), which are the clusters an exporter meeting EXP-016 draws, not off the clusters the exporter happens to draw. An exporter that never draws clusters does not meet it on a net with a bridge and is outside the requirement, as in EXP-016. With cluster source none no node has a key, so there is no bridge and, by the third line, no ghost edge."
          "AC1, AC2, AC3, AC4, AC5, AC6 and AC7 are EXP_017_nonvacuous on the reference exporter: every export has compound true, a flat net has no ghost edge (AC1, AC7); the net exp017NetA has three orphan transitions bridging (left, right), one bridging (right, left), one with left on both sides and one with a single clustered neighbour, and gets exactly two ghost edges, one per direction, anchored at the first bridge (AC2 to AC6). AC2's literal net, exp017NetAC2 (left and right bridged by one orphan transition), gets exactly one ghost edge with ltail cluster_left and lhead cluster_right."
          "AC8 (anchor selection matches across Java, TypeScript and Rust byte for byte) is kind Q: a Lean function is deterministic and cross-language equality is a property of three programs (export design P3, ruling D60 (c)); the export corpus EP-2 replays the reference against the runtimes after the migration. The test derivation is AC2 to AC7."
  signoff "2026-11-13 6669d2bdd6e263e5 ai"
  statement : Exporter → Prop :=
    fun E => ∀ (cfg : ExportCfg) (X : ExportNet),
      (E cfg X).compound = true ∧
      (X.ClusterNames cfg.cluster →
      (∀ w ∈ exp017Bridges cfg X (E cfg X), ∃ e ∈ exp017Ghosts (E cfg X),
        (exp017First (exp017Bridges cfg X (E cfg X)) w.1).map exp017Hint = some (exp017Ends e)) ∧
      (∀ e ∈ exp017Ghosts (E cfg X), ∃ p ∈ exp017Bridges cfg X (E cfg X),
        exp017First (exp017Bridges cfg X (E cfg X)) p.1 = some p ∧ exp017Ends e = exp017Hint p) ∧
      ((exp017Ghosts (E cfg X)).map (exp017KeyPair cfg X)).Nodup ∧
      (exp017Real (E cfg X)).Perm (exp017Real (E { cfg with cluster := .none } X)))

/- The pinned readable form of EXP-017: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXP_017 : Exporter → Prop :=
fun E =>
  ∀ (cfg : ExportCfg) (X : ExportNet),
    (E cfg X).compound = true ∧
      (ExportNet.ClusterNames cfg.cluster X →
        (∀ w ∈ exp017Bridges cfg X (E cfg X),
            ∃ e ∈ exp017Ghosts (E cfg X),
              Option.map exp017Hint (exp017First (exp017Bridges cfg X (E cfg X)) w.1) = some (exp017Ends e)) ∧
          (∀ e ∈ exp017Ghosts (E cfg X),
              ∃ p ∈ exp017Bridges cfg X (E cfg X),
                exp017First (exp017Bridges cfg X (E cfg X)) p.1 = some p ∧ exp017Ends e = exp017Hint p) ∧
            (List.map (exp017KeyPair cfg X) (exp017Ghosts (E cfg X))).Nodup ∧
              (exp017Real (E cfg X)).Perm
                (exp017Real
                  (E
                    { dir := cfg.dir, showTypes := cfg.showTypes, showIntervals := cfg.showIntervals,
                      showPriority := cfg.showPriority, env := cfg.env, cluster := ClusterSource.none }
                    X)))
-/
#guard_msgs in #print EXP_017

/-! ### The reference -/

section Reference

variable {cfg : ExportCfg} {X : ExportNet}

/-- The bridges of the reference graph are those the reference cluster builder scans. -/
theorem exp017Bridges_ref :
    exp017Bridges cfg X (refExport cfg X) =
      bridgeWitnesses (refKey (nodeKey cfg.cluster X.member) (refNodeRefs X)) (refNodeRefs X)
        (refEdges X) :=
  refExport_witnesses_nonGhost

/-- The ghost edges of the reference graph are those of the ghost pairs. -/
theorem exp017Ghosts_ref :
    exp017Ghosts (refExport cfg X) =
      (refGhostPairs (refKey (nodeKey cfg.cluster X.member) (refNodeRefs X)) (refNodeRefs X)
        (refEdges X)).map ghostEdgeOf :=
  refExport_ghosts

/-- The visible edges of the reference graph are the edges of the transitions, whatever the
configuration. -/
theorem exp017Real_ref : exp017Real (refExport cfg X) = refEdges X :=
  refExportWith_nonGhost

/-- The ghost edge of a pair shows the block the pair's hint. -/
theorem exp017Ends_ghostEdgeOf (p : (String × String) × (NodeRef × NodeRef)) :
    exp017Ends (ghostEdgeOf p) = exp017Hint p := rfl

end Reference

/-- The reference exporter satisfies EXP-017: `compound` is set by the mapper, the ghost edges
are those of the ghost pairs, which are the first bridges of their ordered key pairs
(`mem_refGhostPairs`), one per pair (`refGhostPairs_nodup`), and the visible edges are the edges of
the transitions under every cluster source (`refExportWith_nonGhost`). -/
@[evidence holds EXP_017]
theorem EXP_017_reference : EXP_017 refExport := by
  intro cfg X
  refine ⟨rfl, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro w hw
    rw [exp017Bridges_ref] at hw ⊢
    cases h : exp017First (bridgeWitnesses (refKey (nodeKey cfg.cluster X.member) (refNodeRefs X))
        (refNodeRefs X) (refEdges X)) w.1 with
    | none =>
      unfold exp017First at h
      rw [List.find?_eq_none] at h
      exact absurd (by simp) (h w hw)
    | some p =>
      have hp1 : p.1 = w.1 := by simpa using List.find?_some h
      refine ⟨ghostEdgeOf p, ?_, rfl⟩
      rw [exp017Ghosts_ref]
      refine List.mem_map_of_mem (mem_refGhostPairs.mpr ?_)
      rw [hp1]; exact h
  · intro e he
    rw [exp017Ghosts_ref] at he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    rw [exp017Bridges_ref]
    exact ⟨p, refGhostPairs_witness hp, mem_refGhostPairs.mp hp, rfl⟩
  · rw [exp017Ghosts_ref, List.map_map]
    have hc : ∀ p ∈ refGhostPairs (refKey (nodeKey cfg.cluster X.member) (refNodeRefs X))
        (refNodeRefs X) (refEdges X),
        (exp017KeyPair cfg X ∘ ghostEdgeOf) p = (fun xy : String × String => (some xy.1, some xy.2)) p.1 := by
      intro p hp
      obtain ⟨ha, hb, _⟩ := refGhostPairs_keys hp
      simp only [Function.comp, exp017KeyPair, ghostEdgeOf, ghostEdge]
      rw [(refKey_eq_some ha).2, (refKey_eq_some hb).2]
    rw [List.map_congr_left hc]
    have : (List.map (fun a : (String × String) × (NodeRef × NodeRef) =>
        (fun xy : String × String => (some xy.1, some xy.2)) a.1)
        (refGhostPairs (refKey (nodeKey cfg.cluster X.member) (refNodeRefs X)) (refNodeRefs X)
          (refEdges X))) =
        ((refGhostPairs (refKey (nodeKey cfg.cluster X.member) (refNodeRefs X)) (refNodeRefs X)
          (refEdges X)).map Prod.fst).map (fun xy : String × String => (some xy.1, some xy.2)) := by
      rw [List.map_map]; rfl
    rw [this]
    refine List.Nodup.map ?_ refGhostPairs_nodup
    intro a b h
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    exact Prod.ext h.1 h.2
  · rw [exp017Real_ref, exp017Real_ref]

/-! ### Example nets -/

/-- A flat net: one transition `t` from `x` to `y`, no `/` in any name (AC1, AC7). -/
def exp017FlatNet : ExportNet := { trans := [clusterExTrans "t" "x" (.place "y")] }

/-- AC2's literal net: one orphan transition `o1` from `left/a` to `right/b`. -/
def exp017NetAC2 : ExportNet := { trans := [clusterExTrans "o1" "left/a" (.place "right/b")] }

/-- A cluster and a cluster nested in it: the orphan transition `o` from `outer/a` to
`outer/inner/b` bridges `(outer, outer/inner)`. -/
def exp017NetE : ExportNet := { trans := [clusterExTrans "o" "outer/a" (.place "outer/inner/b")] }

/-- The acceptance-criteria net: three orphan transitions bridging `left` to `right` with three
different anchor pairs (AC2, AC3), an orphan `back` bridging `right` to `left` (AC4), an orphan
`loop` with `left` on both sides (AC5) and an orphan `half` whose only other neighbour is the
keyless place `free` (AC6). -/
def exp017NetA : ExportNet :=
  { trans := [clusterExTrans "o1" "left/a" (.place "right/b"),
              clusterExTrans "o2" "left/c" (.place "right/d"),
              clusterExTrans "o3" "left/e" (.place "right/f"),
              clusterExTrans "back" "right/b" (.place "left/c"),
              clusterExTrans "loop" "left/a" (.place "left/c"),
              clusterExTrans "half" "left/a" (.place "free")] }

/-- An orphan place `hub` fed by `outer/inner/V` and read by `mid/W` and then `right/X`: it
bridges `(outer/inner, mid)` and `(outer/inner, right)`, and its first edge out leads to `mid`. -/
def exp017NetB : ExportNet :=
  { trans := [clusterExTrans "outer/inner/V" "outer/inner/in" (.place "hub"),
              clusterExTrans "mid/W" "hub" (.place "mid/out"),
              clusterExTrans "right/X" "hub" (.place "right/out")] }

/-- Two orphan transitions with the same anchors: two equal bridges for `(l, r)`. -/
def exp017NetC : ExportNet :=
  { trans := [clusterExTrans "p" "l/a" (.place "r/b"),
              clusterExTrans "q" "l/a" (.place "r/b")] }

/-- Bridges made of drawn edges that carry no token: `l/T` resets the orphan place `o` (edge
`l/T → o`) and `r/U` reads it (edge `o → r/U`); and a junction anchor: the `Xor` junction of `m/J`
feeds the orphan place `hub2`, which `r/K` consumes. -/
def exp017NetD : ExportNet :=
  { trans := [{ core := ⟨"l/T", [⟨"l/in", .one⟩], [], [], ["o"]⟩, out := some (.place "l/out") },
              { core := ⟨"r/U", [⟨"r/in", .one⟩], [], ["o"], []⟩ },
              clusterExTrans "m/J" "m/in" (.xor [.place "hub2", .place "m/x"]),
              { core := ⟨"r/K", [⟨"hub2", .one⟩], [], [], []⟩ }] }

/-- What the examples read of a ghost edge: DOT IDs of its ends, `ltail`, `lhead`. -/
def exp017Show (e : XEdge) : String × String × Option String × Option String :=
  (nodeId e.src, nodeId e.dst, e.ltail, e.lhead)

/-- ✓ The reference on the acceptance criteria. AC1 and AC7: a flat net has `compound` set, no
bridge and no ghost edge. AC2 to AC6: `exp017NetA` has four bridges, three for `(left, right)`
and one for `(right, left)` (none for `loop`, AC5, and none for `half`, AC6), and exactly two
ghost edges, one per direction (AC3, AC4), each at the anchors of its first bridge (AC2).
`exp017NetAC2`, AC2's literal net: exactly one ghost edge, from `cluster_left` to `cluster_right`.
`exp017NetB`: the deepest cluster `outer/inner` is the tail, and each pair is anchored at its own
target. `exp017NetD`: a reset edge into and a read edge out of an orphan place bridge `(l, r)`,
and a junction is an anchor. `exp017NetE`: a cluster and a cluster nested in it are bridged. -/
@[evidence nonvacuous EXP_017]
theorem EXP_017_nonvacuous :
    (refExport {} exp017FlatNet).compound = true ∧
    exp017Bridges {} exp017FlatNet (refExport {} exp017FlatNet) = [] ∧
    exp017Ghosts (refExport {} exp017FlatNet) = [] ∧
    (exp017Bridges {} exp017NetA (refExport {} exp017NetA)).map Prod.fst =
      [("left", "right"), ("left", "right"), ("left", "right"), ("right", "left")] ∧
    (exp017Ghosts (refExport {} exp017NetA)).map exp017Show =
      [("p_left_a", "p_right_b", some "cluster_left", some "cluster_right"),
       ("p_right_b", "p_left_c", some "cluster_right", some "cluster_left")] ∧
    (exp017Ghosts (refExport {} exp017NetAC2)).map exp017Show =
      [("p_left_a", "p_right_b", some "cluster_left", some "cluster_right")] ∧
    (exp017Ghosts (refExport {} exp017NetB)).map exp017Show =
      [("t_outer_inner_V", "t_mid_W", some "cluster_outer_inner", some "cluster_mid"),
       ("t_outer_inner_V", "t_right_X", some "cluster_outer_inner", some "cluster_right")] ∧
    (exp017Ghosts (refExport {} exp017NetD)).map exp017Show =
      [("t_l_T", "t_r_U", some "cluster_l", some "cluster_r"),
       ("j_m_J__xor_0", "t_r_K", some "cluster_m", some "cluster_r")] ∧
    (exp017Bridges {} exp017NetE (refExport {} exp017NetE)).map Prod.fst =
      [("outer", "outer/inner")] ∧
    (exp017Ghosts (refExport {} exp017NetE)).map exp017Show =
      [("p_outer_a", "p_outer_inner_b", some "cluster_outer", some "cluster_outer_inner")] := by
  and_intros <;> decide

/-! ### Wrong exporters, one per line -/

/-- The reference key function of the cluster stage (EXP-016's `nodeKey`). -/
def exp017KF : ClusterSource → ExportNet → NodeRef → Option String := fun src X => nodeKey src X.member

/-- The reference exporter with another ghost loop: `pairs` from the key read off the drawn
nodes, the drawn nodes and the edges of the transitions. -/
def exp017WithPairs (pairs : (NodeRef → Option String) → List NodeRef → List XEdge →
    List ((String × String) × (NodeRef × NodeRef))) : Exporter :=
  refExportWith (ClusterStage.ofPairs exp017KF pairs)

/-- An exporter that leaves `compound` unset (the first line). -/
def exp017_noCompound : Exporter := fun cfg X => { refExport cfg X with compound := false }

/-- ✗ No `compound` attribute violates EXP-017 (line 1; AC1). -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_noCompound : ¬ EXP_017 exp017_noCompound := by
  intro h
  have := (h {} exp017FlatNet).1
  revert this
  decide

/-- ✗ The pre-EXP-017 mapper, clusters without ghost edges, violates EXP-017 (line 2; AC2). -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_noGhosts : ¬ EXP_017 refExportFlat := by
  intro h
  have := ((h {} exp017NetA).2 (by decide)).1
  revert this
  decide

/-- One ghost edge per unordered pair of keys: a bridge is dropped when its pair or the reverse
pair is already there. -/
def exp017Unordered (key : NodeRef → Option String) (rs : List NodeRef) (es : List XEdge) :
    List ((String × String) × (NodeRef × NodeRef)) :=
  (bridgeWitnesses key rs es).foldl
    (fun acc p => if acc.any (fun q => decide (q.1 = p.1) || decide (q.1 = (p.1.2, p.1.1)))
      then acc else acc ++ [p]) []

/-- An exporter that dedups ghost edges by unordered pair. -/
def exp017_unordered : Exporter := exp017WithPairs exp017Unordered

/-- ✗ Dedup by unordered pair loses `(right, left)` and violates EXP-017 (line 2; AC4). -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_unordered : ¬ EXP_017 exp017_unordered := by
  intro h
  have := ((h {} exp017NetA).2 (by decide)).1
  revert this
  decide

/-- A dedup by the NUL-joined string (the behaviour RD-37 recorded): one ghost edge per string
`X ++ "\x00" ++ Y`, not per ordered pair, so two pairs whose keys hold a NUL character can share
one string. -/
def exp017NulDedup (key : NodeRef → Option String) (rs : List NodeRef) (es : List XEdge) :
    List ((String × String) × (NodeRef × NodeRef)) :=
  (bridgeWitnesses key rs es).foldl
    (fun acc p => if acc.any (fun q => decide (q.1.1 ++ "\x00" ++ q.1.2 = p.1.1 ++ "\x00" ++ p.1.2))
      then acc else acc ++ [p]) []

/-- An exporter that dedups ghost edges by the NUL-joined key string. -/
def exp017_nulDedup : Exporter := exp017WithPairs exp017NulDedup

/-- Two orphan transitions: `o1` bridges (`a\x00b`, `c`) and `o2` bridges (`a`, `b\x00c`); both
pairs join to the string `a\x00b\x00c`. The net meets `ExportNet.ClusterNames` (ASCII keys, no
empty segment). -/
def exp017NulNet : ExportNet :=
  { trans := [clusterExTrans "o1" "a\x00b/p" (.place "c/q"),
              clusterExTrans "o2" "a/r" (.place "b\x00c/s")] }

/-- ✗ Dedup by the NUL-joined string loses (`a`, `b\x00c`) on a net inside the premise and
violates EXP-017 (line 2): the reference draws two ghost edges, this exporter one. -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_nulDedup : ¬ EXP_017 exp017_nulDedup := by
  intro h
  have := ((h {} exp017NulNet).2 (by decide)).1
  revert this
  decide

/-- The NUL net is inside the premise, and the reference draws two ghost edges on it where the
NUL-joined dedup draws one. -/
theorem exp017_nulNet_counts : exp017NulNet.ClusterNames .auto ∧
    (exp017Ghosts (refExport {} exp017NulNet)).length = 2 ∧
    (exp017Ghosts (exp017_nulDedup {} exp017NulNet)).length = 1 := by decide

/-- The witness of a pair of edges with no `x ≠ y` check. -/
def exp017EntryAny : Option String → Option String → NodeRef → NodeRef →
    List ((String × String) × (NodeRef × NodeRef))
  | some x, some y, a, b => [((x, y), (a, b))]
  | _, _, _, _ => []

/-- The bridge scan with `X = Y` allowed. -/
def exp017WitnessesAny (key : NodeRef → Option String) (rs : List NodeRef) (es : List XEdge) :
    List ((String × String) × (NodeRef × NodeRef)) :=
  rs.flatMap fun o =>
    if key o = none then
      es.flatMap fun ei =>
        if ei.dst = o then
          es.flatMap fun eo => if eo.src = o then exp017EntryAny (key ei.src) (key eo.dst) ei.src eo.dst else []
        else []
    else []

/-- An exporter that also draws a ghost edge for an orphan with one cluster on both sides. -/
def exp017_sameCluster : Exporter :=
  exp017WithPairs fun key rs es => (exp017WitnessesAny key rs es).foldl keepFirst []

/-- ✗ A ghost edge from `cluster_left` to itself for `loop` violates EXP-017 (line 3; AC5). -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_sameCluster : ¬ EXP_017 exp017_sameCluster := by
  intro h
  have := ((h {} exp017NetA).2 (by decide)).2.1
  revert this
  decide

/-- An exporter that anchors each ghost edge at the last bridge of its pair. -/
def exp017_lastWitness : Exporter :=
  exp017WithPairs fun key rs es => (bridgeWitnesses key rs es).reverse.foldl keepFirst []

/-- ✗ Anchoring `(left, right)` at `o3`'s ends violates EXP-017 (lines 2 and 3: the anchor sentence,
first bridge, not last). -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_lastWitness : ¬ EXP_017 exp017_lastWitness := by
  intro h
  have := ((h {} exp017NetA).2 (by decide)).2.1
  revert this
  decide

/-- The literal reading of the anchor sentence: for each orphan, the `b` is the target of the
first edge out of it, whatever cluster that edge leads to. -/
def exp017Literal (key : NodeRef → Option String) (rs : List NodeRef) (es : List XEdge) :
    List ((String × String) × (NodeRef × NodeRef)) :=
  (rs.flatMap fun o =>
    if key o = none then
      es.flatMap fun ei =>
        if ei.dst = o then
          match es.find? (fun e => decide (e.src = o)) with
          | some e0 => es.flatMap fun eo =>
              if eo.src = o then bridgeEntry (key ei.src) (key eo.dst) ei.src e0.dst else []
          | none => []
        else []
    else []).foldl keepFirst []

/-- An exporter that reads the anchor sentence literally. -/
def exp017_literalAnchor : Exporter := exp017WithPairs exp017Literal

/-- ✗ Anchoring `(outer/inner, right)` at `mid/W`, the target of `hub`'s first edge out, violates
EXP-017 (lines 2, 3 and 4, both ghost edges then end at `mid/W`; ruling D26 item 6). -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_literalAnchor : ¬ EXP_017 exp017_literalAnchor := by
  intro h
  have := ((h {} exp017NetB).2 (by decide)).2.1
  revert this
  decide

/-- The outermost segment of a key. -/
def exp017Outermost (k : String) : String := String.ofList (k.toList.takeWhile (· ≠ '/'))

/-- An exporter that reads "a node in cluster_X" as the outermost cluster around the node. -/
def exp017_outerKey : Exporter :=
  refExportWith (ClusterStage.byKey fun src X r => (nodeKey src X.member r).map exp017Outermost)

/-- ✗ A ghost edge from `cluster_outer` in place of `cluster_outer_inner` violates EXP-017
(lines 2 and 3; ruling D26 item 6: the key is the deepest cluster). -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_outerKey : ¬ EXP_017 exp017_outerKey := by
  intro h
  have := ((h {} exp017NetB).2 (by decide)).2.1
  revert this
  decide

/-- An exporter that reads the bridges over token flow only (input, output and reset+output
edges), not over every drawn edge. -/
def exp017_tokenFlow : Exporter :=
  exp017WithPairs fun key rs es =>
    (bridgeWitnesses key rs
      (es.filter fun e => e.arc == .input || e.arc == .output || e.arc == .resetOutput)).foldl
      keepFirst []

/-- ✗ No ghost edge for the reset and read bridge of `exp017NetD` violates EXP-017 (line 2;
ruling D26 item 6: every drawn edge counts). -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_tokenFlow : ¬ EXP_017 exp017_tokenFlow := by
  intro h
  have := ((h {} exp017NetD).2 (by decide)).1
  revert this
  decide

/-- An exporter that reads `X == Y` geometrically: it draws no ghost edge for a pair of keys one
of which is a `/`-prefix of the other (a cluster and a cluster nested in it). -/
def exp017_skipNested : Exporter :=
  exp017WithPairs fun key rs es =>
    ((bridgeWitnesses key rs es).filter fun p =>
      !(decide (IsSlashPrefix p.1.1 p.1.2) || decide (IsSlashPrefix p.1.2 p.1.1))).foldl keepFirst []

/-- ✗ No ghost edge for `(outer, outer/inner)` violates EXP-017 (line 2; the sentence on nested
clusters). -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_skipNested : ¬ EXP_017 exp017_skipNested := by
  intro h
  have := ((h {} exp017NetE).2 (by decide)).1
  revert this
  decide

/-- An exporter that draws one ghost edge per bridge, without dedup. -/
def exp017_noDedup : Exporter := exp017WithPairs bridgeWitnesses

/-- ✗ Two ghost edges for `(l, r)`, one per orphan, violate EXP-017 (line 4; AC3), although each
is drawn at the anchors of the first bridge. -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_noDedup : ¬ EXP_017 exp017_noDedup := by
  intro h
  have := ((h {} exp017NetC).2 (by decide)).2.2.1
  revert this
  decide

/-- An exporter that also draws each ghost edge as a visible output edge. -/
def exp017_visibleGhost : Exporter := fun cfg X =>
  { refExport cfg X with
    edges := (refExport cfg X).edges ++ (exp017Ghosts (refExport cfg X)).map
      fun e => { e with arc := .output, ltail := none, lhead := none } }

/-- ✗ A visible copy of the ghost edge changes the visible edge set and violates EXP-017 (line 5),
although its ghost edges are right: the copies join two nodes with keys and bridge nothing. -/
@[evidence forbids EXP_017]
theorem EXP_017_forbids_visibleGhost : ¬ EXP_017 exp017_visibleGhost := by
  intro h
  have := ((h {} exp017NetA).2 (by decide)).2.2.2
  revert this
  decide

/-- The mutants filed under lines 3, 4 and 5 fail only that line: on their example net each meets
the other lines of the statement (lines 1 and 2 of `exp017_sameCluster`, `exp017_noDedup` and
`exp017_visibleGhost`, and the rest as listed). Together with `exp017_noCompound` (line 1 only)
and `refExportFlat`, `exp017_unordered`, `exp017_tokenFlow` and `exp017_skipNested` (line 2 only), every line of the
statement has a mutant that only it kills. -/
example :
    -- `exp017_sameCluster` on `exp017NetA`: lines 2, 4 and 5 hold.
    (∀ w ∈ exp017Bridges {} exp017NetA (exp017_sameCluster {} exp017NetA),
      ∃ e ∈ exp017Ghosts (exp017_sameCluster {} exp017NetA),
        (exp017First (exp017Bridges {} exp017NetA (exp017_sameCluster {} exp017NetA)) w.1).map
          exp017Hint = some (exp017Ends e)) ∧
    ((exp017Ghosts (exp017_sameCluster {} exp017NetA)).map (exp017KeyPair {} exp017NetA)).Nodup ∧
    (exp017Real (exp017_sameCluster {} exp017NetA)).Perm
      (exp017Real (exp017_sameCluster { cluster := .none } exp017NetA)) := by
  decide

/-- `exp017_noDedup` on `exp017NetC`: lines 2, 3 and 5 hold. -/
example :
    (∀ w ∈ exp017Bridges {} exp017NetC (exp017_noDedup {} exp017NetC),
      ∃ e ∈ exp017Ghosts (exp017_noDedup {} exp017NetC),
        (exp017First (exp017Bridges {} exp017NetC (exp017_noDedup {} exp017NetC)) w.1).map
          exp017Hint = some (exp017Ends e)) ∧
    (∀ e ∈ exp017Ghosts (exp017_noDedup {} exp017NetC),
      ∃ p ∈ exp017Bridges {} exp017NetC (exp017_noDedup {} exp017NetC),
        exp017First (exp017Bridges {} exp017NetC (exp017_noDedup {} exp017NetC)) p.1 = some p ∧
          exp017Ends e = exp017Hint p) ∧
    (exp017Real (exp017_noDedup {} exp017NetC)).Perm
      (exp017Real (exp017_noDedup { cluster := .none } exp017NetC)) := by
  refine ⟨by decide, by decide, by decide⟩

/-- `exp017_visibleGhost` on `exp017NetA`: lines 2, 3 and 4 hold. -/
example :
    (∀ w ∈ exp017Bridges {} exp017NetA (exp017_visibleGhost {} exp017NetA),
      ∃ e ∈ exp017Ghosts (exp017_visibleGhost {} exp017NetA),
        (exp017First (exp017Bridges {} exp017NetA (exp017_visibleGhost {} exp017NetA)) w.1).map
          exp017Hint = some (exp017Ends e)) ∧
    (∀ e ∈ exp017Ghosts (exp017_visibleGhost {} exp017NetA),
      ∃ p ∈ exp017Bridges {} exp017NetA (exp017_visibleGhost {} exp017NetA),
        exp017First (exp017Bridges {} exp017NetA (exp017_visibleGhost {} exp017NetA)) p.1 = some p ∧
          exp017Ends e = exp017Hint p) ∧
    ((exp017Ghosts (exp017_visibleGhost {} exp017NetA)).map (exp017KeyPair {} exp017NetA)).Nodup := by
  refine ⟨by decide, by decide, by decide⟩

end Libpetri.Spec
