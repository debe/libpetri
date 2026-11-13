import Libpetri.Reference.ExportCluster
import Libpetri.Spec.Req.EXP_001
import Libpetri.Spec.Req.EXP_002
import Libpetri.Spec.Req.EXP_003
import Libpetri.Spec.Req.EXP_004
import Libpetri.Spec.Req.EXP_005
import Libpetri.Spec.Req.EXP_006
import Libpetri.Spec.Req.EXP_007
import Libpetri.Spec.Req.EXP_008
import Libpetri.Spec.Req.EXP_012
import Libpetri.Spec.Req.EXP_013
import Libpetri.Spec.Req.EXP_014
import Libpetri.Spec.Req.EXP_016
import Libpetri.Spec.Req.EXP_017
import Libpetri.Spec.Req.EXP_018
import Libpetri.Spec.Req.IO_012
import Libpetri.Spec.Req.IO_013
import Libpetri.Spec.Req.IO_014

set_option linter.missingDocs true

/-!
# The export clashes (EXP-001 to EXP-018), after the rulings

The plan's section 6 confirms 26 clashes that touch an export requirement: exp-a#1 to #10, exp-b#1
to #13, and the design's S-4, S-6 and the open Rust and Java failure on an empty `/` segment.
Every one is tied to a ruling the user accepted as recommended (D20, D26, D41, D46, D51, D60), and
each of those rulings restates the spec to what the three mappers draw, or keeps a common form
and records the open case. No export clash is left as a contradiction between two blocks, so the
evidence here is `consistent`: for each clash that names two or more blocks, one reference
exporter (`refExport`, the clustered exporter of `Reference/ExportCluster.lean`) together with
the reference emitter, labellers and classifier it agrees with (`ExportAgrees`, through
`refExportWith_agrees`) meets every block the clash names at once, and a small net decided on
the reference shows the case the clash was about, drawn the way the restated text says.

| Clash | Blocks | Ruling | Evidence here |
|---|---|---|---|
| exp-a#2, exp-b#8 (a) | EXP-001, EXP-014 | D60 (c) | `clashExport_placeSet`: both runtime shapes of the place set meet both blocks |
| exp-a#3, exp-b#6, exp-b#5 (EXP-014 half) | EXP-001, EXP-014 | D46 (a) | `clashExport_sanitize`: two names that collide after sanitising get two nodes and one ID, outside the name assumption |
| exp-a#4 | EXP-004, EXP-012 | D20 | `clashExport_forward`: the ForwardInput edge is an output edge drawn dashed with `⟵<from>` |
| exp-a#5 | EXP-004, EXP-008 | D20, D51 | `clashExport_resetDirection`: the reset edge runs from the transition, and the reset arc counts for no category |
| exp-a#6, S-6 | EXP-006, EXP-018 | D41 | `clashExport_corrOne`: a One arc has no cardinality label, a correlated One input the label `⟨n⟩` |
| exp-a#7 | EXP-003, EXP-007 | D41 | `clashExport_showTypes`: the show-types option changes nothing |
| exp-a#8, exp-b#8 (c) | EXP-002, EXP-008, EXP-014 | D51 (a) | `clashExport_readOnly`: both classifier shapes meet EXP-008, the read-only place is left open |
| exp-a#9, exp-a#10 | EXP-002, EXP-008 | D51 (a) | `clashExport_categories`: five place rows, terminal and environment first |
| exp-b#1 | EXP-012, IO-012 | D26 | `clashExport_shortGroup`: a one-child group draws one direct edge, and the one-child And is a legal spec |
| exp-b#2 | EXP-012, IO-013, IO-014 | D26 | `clashExport_timeoutForward`: the Timeout and ForwardInput labels of two transitions that build |
| exp-b#3 | EXP-013, IO-012 | D26 | `clashExport_multiLeaf`: one reset+out edge per leaf of a spec IO-012 accepts |
| exp-b#4 | EXP-005, EXP-012, EXP-013 | D26 | `clashExport_combined`: the combined edge drops the Timeout and ForwardInput labels and the dash |
| exp-b#5 (EXP-016 and EXP-017 half), exp-b#9, exp-b#10, exp-b#11, exp-b#12, S-4 | EXP-014, EXP-016, EXP-017 | D26, D46 (a) | `clashExport_cluster`: a junction takes its transition's cluster key, clustering changes no node and no non-ghost edge, one ghost edge per bridged ordered key pair at its first bridge, and a key with an empty segment is outside the name assumption |
| exp-b#8 | EXP-001, EXP-008, EXP-012, EXP-013, EXP-014, EXP-016, EXP-017, EXP-018 | D60 (c) | `clashExport_joint`: one exporter meets them all; byte equality stays kind Q |

Not here:

* exp-a#1 (EXP-001's stale Rust note) and exp-b#13 (EXP-016 and MOD-040 drifted apart) are
  editorial (D20, D26) and change no statement.
* exp-b#7 (the empty transition name against AC1's regex) is EXP-014's own scope sentence and
  its `EXP_014_ac1`; it names no second block.
* A cluster key with an empty `/` segment (exp-b#9, D46 (a)) is outside the name assumption of
  EXP-016 and EXP-017 (`ExportNet.ClusterNames`), and `clashExport_cluster` shows the key `a/` of
  the name `a//x` is one (`NoEmptySegment` fails). The Java, TypeScript and Rust builders register
  the model's `keyChain` on such a key; the wrong chain that skips the empty segment, the
  behaviour RD-12 recorded, is `registerChain` in `Reference/ExportCluster.lean`. A non-ASCII
  membership key is outside the assumption too, and Rust draws its cluster ID with the letters
  kept (`exp016_nonAsciiKey_outside` in EXP-016).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Export

/-! ## The reference family -/

/-- The clustered reference exporter agrees with the reference emitter, cardinality labeller,
transition labeller and place classifier. -/
theorem clashExport_agrees :
    ExportAgrees refExport refEmit refCardLabel refTransLabel refPlaceCategory :=
  refExportWith_agrees refClusterStage

/-! ## exp-a#2 and exp-b#8 (a): the place set (ruling D60 (c)) -/

/-- The Java and TypeScript shape names no place that the net itself does not name. -/
theorem clashExport_dropPlaces_names {X : ExportNet} {p : String}
    (hp : p ∈ ({ X with places := [] } : ExportNet).allPlaceNames) : p ∈ X.allPlaceNames := by
  simp only [ExportNet.allPlaceNames, List.nil_append] at hp
  exact List.mem_append_right _ hp

/-- Dropping the declared places keeps the name assumption of EXP-014. -/
theorem clashExport_dropPlaces_idNames {X : ExportNet} (h : X.IdNames) :
    ({ X with places := [] } : ExportNet).IdNames :=
  ⟨fun p hp => h.1 p (clashExport_dropPlaces_names hp), h.2.1,
    fun p hp q hq => h.2.2.1 p (clashExport_dropPlaces_names hp) q (clashExport_dropPlaces_names hq),
    h.2.2.2⟩

/-- The Java and TypeScript shape (`exp001_arcDerived`: place nodes for the touched places only)
meets EXP-014: it is the reference on the net without its declared places, which has the same
transitions and keeps the name assumption. -/
theorem clashExport_arcDerived_EXP_014 : EXP_014 exp001_arcDerived := by
  intro cfg X
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := EXP_014_any .flat cfg { X with places := [] }
  exact ⟨h1, h2, h3, h4, fun hn hI => h5 hn (clashExport_dropPlaces_idNames hI), h6⟩

/-- On the net that declares `d` and touches nothing, the reference draws a node for `d` and the
Java and TypeScript shape none. -/
theorem clashExport_untouched :
    (refExport {} exp001_untouchedNet).nodes.map XNode.ref = [.place "d", .trans "t"] ∧
      (exp001_arcDerived {} exp001_untouchedNet).nodes.map XNode.ref = [.trans "t"] := by
  rw [refExport_nodes_flat]
  decide

/-- ✓ **exp-a#2, exp-b#8 (a), ruling D60 (c).** EXP-001 and EXP-014 hold together of both
runtime shapes of the place set: the reference (Rust and Python, a node for every declared place,
the end state of D60) and the Java and TypeScript mappers (a node for the touched places only).
Neither block decides a declared place that no arc touches, which the two shapes draw
differently, so the byte equality of EXP-014 AC3 across the three runtimes is not a consequence
of the blocks and stays kind Q. -/
@[evidence consistent EXP_001 EXP_014]
theorem clashExport_placeSet :
    (EXP_001 refExport ∧ EXP_014 refExport) ∧
      (EXP_001 exp001_arcDerived ∧ EXP_014 exp001_arcDerived) ∧
      (refExport {} exp001_untouchedNet).nodes.map XNode.ref = [.place "d", .trans "t"] ∧
      (exp001_arcDerived {} exp001_untouchedNet).nodes.map XNode.ref = [.trans "t"] :=
  ⟨⟨EXP_001_any _, EXP_014_any _⟩, ⟨EXP_001_allows_arcDerived, clashExport_arcDerived_EXP_014⟩,
    clashExport_untouched⟩

/-! ## exp-a#3, exp-b#6 and exp-b#5: sanitising (ruling D46 (a)) -/

/-- Transition `t` consumes from the instance place `b1/x` and produces into the host place
`b1_x`: two names that sanitise to one. -/
def clashExportCollideNet : ExportNet :=
  { trans := [{ core := ⟨"t", [⟨"b1/x", .one⟩], [], [], []⟩, out := some (.place "b1_x") }] }

/-- The collision net fails the name assumption of EXP-014. -/
theorem clashExportCollideNet_not_idNames : ¬ clashExportCollideNet.IdNames := by
  intro h
  have := h.2.2.1 "b1/x" (by decide) "b1_x" (by decide) (by decide)
  exact absurd this (by decide)

/-- The reference draws a node for each of the two places, and the two nodes get one ID. -/
theorem clashExport_collide_ids :
    (refExport {} clashExportCollideNet).nodes.map (fun n => (n.ref, n.id)) =
      [(.place "b1/x", "p_b1_x"), (.place "b1_x", "p_b1_x"), (.trans "t", "t_t")] := by
  rw [refExport_nodes_flat]
  decide

/-- A name outside ASCII: `ö` and `ß` are replaced by `_` in the reference (as Java and TypeScript
do), where Rust keeps them; EXP-014's ID line binds only ASCII names. -/
theorem clashExport_nonAscii : ¬ AsciiName "Größe" ∧ sanitize "Größe" = "Gr__e" := by
  decide

/-- ✓ **exp-a#3, exp-b#6, and the EXP-014 half of exp-b#5, ruling D46 (a).** EXP-001 and EXP-014
hold together of the reference although sanitising is not injective. EXP-001 identifies a node
by what it stands for, so the places `b1/x` and `b1_x` get two nodes (all places represented);
EXP-014 gives them one DOT ID, which its uniqueness line allows because the net fails the name
assumption (distinct names after sanitising). A name outside ASCII is implementation-defined. -/
@[evidence consistent EXP_001 EXP_014]
theorem clashExport_sanitize :
    (EXP_001 refExport ∧ EXP_014 refExport) ∧
      ¬ clashExportCollideNet.IdNames ∧
      (refExport {} clashExportCollideNet).nodes.map (fun n => (n.ref, n.id)) =
        [(.place "b1/x", "p_b1_x"), (.place "b1_x", "p_b1_x"), (.trans "t", "t_t")] ∧
      (¬ AsciiName "Größe" ∧ sanitize "Größe" = "Gr__e") :=
  ⟨⟨EXP_001_any _, EXP_014_any _⟩, clashExportCollideNet_not_idNames, clashExport_collide_ids,
    clashExport_nonAscii⟩

/-! ## exp-a#4 and exp-b#2: ForwardInput and Timeout edges (rulings D20, D26) -/

/-- `T` consumes `i` and has `Timeout(5, And(A, ForwardInput(i, B)))`, IO-014's accepted form. -/
def clashExportFwdT : ExportTrans :=
  { core := ⟨"T", [⟨"i", .one⟩], [], [], []⟩,
    out := some (.timeout 5 (.and [.place "A", .forward "i" "B"])) }

/-- `U` has `And(C, Timeout(7, D))`. -/
def clashExportTmoU : ExportTrans :=
  { core := ⟨"U", [], [], [], []⟩, out := some (.and [.place "C", .timeout 7 (.place "D")]) }

/-- The net of `T` and `U`. -/
def clashExportFwdNet : ExportNet := { trans := [clashExportFwdT, clashExportTmoU] }

/-- An edge as (source, target, arc type, dashed, label). -/
def clashExportLook (e : XEdge) : NodeRef × NodeRef × ArcType × Bool × Option String :=
  (e.src, e.dst, e.arc, e.dashed, e.label)

/-- What the reference draws for `T` and `U`: the Timeout labels the edge entering its child,
an And junction adds no label, and the ForwardInput leaf edge is an output edge drawn dashed and
labelled `⟵i`. -/
theorem clashExport_fwdNet_edges :
    (refExport {} clashExportFwdNet).edges.map clashExportLook =
      [(.place "i", .trans "T", .input, false, none),
       (.trans "T", .junction "T" .and 0, .output, false, some "⏱5ms"),
       (.junction "T" .and 0, .place "A", .output, false, none),
       (.junction "T" .and 0, .place "B", .output, true, some "⟵i"),
       (.trans "U", .junction "U" .and 0, .output, false, none),
       (.junction "U" .and 0, .place "C", .output, false, none),
       (.junction "U" .and 0, .place "D", .output, false, some "⏱7ms")] := by
  decide

/-- Both transitions build under the reference builder. -/
theorem clashExport_fwdNet_build :
    refBuild clashExportFwdT.toTrans = none ∧ refBuild clashExportTmoU.toTrans = none := by
  decide

/-- ✓ **exp-a#4, ruling D20.** EXP-004 and EXP-012 hold together of the reference exporter and
the reference emitter it agrees with: the edge into the target of a ForwardInput is an output
edge (EXP-004's output line counts it, as the glossary's output arc does) drawn dashed with the
label `⟵<from>`, the form EXP-004 now states and EXP-012's drawing rule produces. -/
@[evidence consistent EXP_004 EXP_012]
theorem clashExport_forward :
    EXP_004 refExport ∧ EXP_012 refEmit ∧
      ExportAgrees refExport refEmit refCardLabel refTransLabel refPlaceCategory ∧
      (refExport {} clashExportFwdNet).edges.map clashExportLook =
        [(.place "i", .trans "T", .input, false, none),
         (.trans "T", .junction "T" .and 0, .output, false, some "⏱5ms"),
         (.junction "T" .and 0, .place "A", .output, false, none),
         (.junction "T" .and 0, .place "B", .output, true, some "⟵i"),
         (.trans "U", .junction "U" .and 0, .output, false, none),
         (.junction "U" .and 0, .place "C", .output, false, none),
         (.junction "U" .and 0, .place "D", .output, false, some "⏱7ms")] :=
  ⟨EXP_004_any _, EXP_012_reference, clashExport_agrees, clashExport_fwdNet_edges⟩

/-- ✓ **exp-b#2, ruling D26.** EXP-012 holds of the reference emitter together with IO-013 and
IO-014 on the reference builder and firing relations, and on two transitions that build (a
ForwardInput inside the child of a Timeout, as IO-014 requires, and a Timeout below an And) the
emitter labels the edge entering a Timeout's child `⏱<n>ms`, wherever the Timeout sits, adds no
label for an And junction, and draws the ForwardInput leaf edge dashed with `⟵<from>`. The
XOR rule's 'target name for ForwardInput' case does not occur in a transition that builds. -/
@[evidence consistent EXP_012 IO_013 IO_014]
theorem clashExport_timeoutForward :
    EXP_012 refEmit ∧
      IO_013 (refBuild (N := String)) (RefFire (N := String)) (refTimeoutOutcomeFire (N := String)) ∧
      IO_014 (refBuild (N := String)) (refTimedOutFire (N := String)) ∧
      (refBuild clashExportFwdT.toTrans = none ∧ refBuild clashExportTmoU.toTrans = none) ∧
      (refExport {} clashExportFwdNet).edges.map clashExportLook =
        [(.place "i", .trans "T", .input, false, none),
         (.trans "T", .junction "T" .and 0, .output, false, some "⏱5ms"),
         (.junction "T" .and 0, .place "A", .output, false, none),
         (.junction "T" .and 0, .place "B", .output, true, some "⟵i"),
         (.trans "U", .junction "U" .and 0, .output, false, none),
         (.junction "U" .and 0, .place "C", .output, false, none),
         (.junction "U" .and 0, .place "D", .output, false, some "⏱7ms")] :=
  ⟨EXP_012_reference, IO_013_reference, IO_014_reference, clashExport_fwdNet_build,
    clashExport_fwdNet_edges⟩

/-! ## exp-a#5: the direction of a reset edge (rulings D20, D51) -/

/-- `T` consumes `a`, produces into `b` and resets `r`. -/
def clashExportRstT : ExportTrans :=
  { core := ⟨"T", [⟨"a", .one⟩], [], [], ["r"]⟩, out := some (.place "b") }

/-- The net of `T`. -/
def clashExportRstNet : ExportNet := { trans := [clashExportRstT] }

/-- The reference draws the reset edge from `T` to `r`, and `r`, which only the reset arc
touches, is a start place: the reset arc is neither incoming nor outgoing. -/
theorem clashExport_rstNet :
    ResetArc clashExportRstT.toTrans "r" ∧
      (refExport {} clashExportRstNet).edges.map clashExportLook =
        [(.place "a", .trans "T", .input, false, none),
         (.trans "T", .place "b", .output, false, none),
         (.trans "T", .place "r", .reset, false, some "reset")] ∧
      (refExport {} clashExportRstNet).nodes.map (fun n => (n.ref, n.cat)) =
        [(.place "a", .start), (.place "b", .«end»), (.place "r", .start),
         (.trans "T", .transition)] := by
  decide

/-- ✓ **exp-a#5, rulings D20 and D51.** EXP-004 and EXP-008 hold together of the reference
exporter and the reference classifier it agrees with: the reset edge is drawn from the
transition to the place, a drawing convention that is not the glossary's arc direction (the
reset arc is still an arc from the place to the transition, `ResetArc`), and EXP-008 counts a
reset arc as neither incoming nor outgoing, so the place it touches is a start place. -/
@[evidence consistent EXP_004 EXP_008]
theorem clashExport_resetDirection :
    EXP_004 refExport ∧ EXP_008 (refPlaceCategory (N := String)) ∧
      ExportAgrees refExport refEmit refCardLabel refTransLabel refPlaceCategory ∧
      ResetArc clashExportRstT.toTrans "r" ∧
      (refExport {} clashExportRstNet).edges.map clashExportLook =
        [(.place "a", .trans "T", .input, false, none),
         (.trans "T", .place "b", .output, false, none),
         (.trans "T", .place "r", .reset, false, some "reset")] ∧
      (refExport {} clashExportRstNet).nodes.map (fun n => (n.ref, n.cat)) =
        [(.place "a", .start), (.place "b", .«end»), (.place "r", .start),
         (.trans "T", .transition)] :=
  ⟨EXP_004_any _, EXP_008_reference, clashExport_agrees, clashExport_rstNet⟩

/-! ## exp-a#6 and S-6: the label of a correlated One input (ruling D41) -/

/-- `J` consumes `a` (One, correlated), `b` (Exactly 3, correlated) and `c` (One). -/
def clashExportCorrT : ExportTrans :=
  { core := ⟨"J", [⟨"a", .one⟩, ⟨"b", .exactly 3⟩, ⟨"c", .one⟩], [], [], []⟩,
    corr := ["a", "b"] }

/-- The input edges of `J`, as (source, row, label). -/
theorem clashExport_corrNet :
    (refExport {} { trans := [clashExportCorrT] }).edges.map (fun e => (e.src, e.row, e.label)) =
      [(.place "a", .matchInput, some "⟨n⟩"), (.place "b", .matchInput, some "⟨n⟩ ×3"),
       (.place "c", .input, none)] := by
  decide

/-- ✓ **exp-a#6 and S-6, ruling D41.** EXP-006 and EXP-018 hold together of the reference
cardinality labeller and the reference exporter that agrees with it: a One arc has no
cardinality label (EXP-006 AC2, reworded), the label forms are pinned to `×n`, `*` and `≥m`,
and a correlated One input is labelled `⟨n⟩` alone, with the cardinality label after a space
otherwise (EXP-018 AC3). -/
@[evidence consistent EXP_006 EXP_018]
theorem clashExport_corrOne :
    EXP_006 refCardLabel ∧ EXP_018 refExport ∧
      ExportAgrees refExport refEmit refCardLabel refTransLabel refPlaceCategory ∧
      refCardLabel .one = none ∧
      (refExport {} { trans := [clashExportCorrT] }).edges.map (fun e => (e.src, e.row, e.label)) =
        [(.place "a", .matchInput, some "⟨n⟩"), (.place "b", .matchInput, some "⟨n⟩ ×3"),
         (.place "c", .input, none)] :=
  ⟨EXP_006_reference, EXP_018_any _, clashExport_agrees, rfl, clashExport_corrNet⟩

/-! ## exp-a#7: the show-types option (ruling D41) -/

/-- ✓ **exp-a#7, ruling D41.** EXP-003 (the transition node and its label), the label and
configuration lines of EXP-007 hold together of the reference: the transition label is
`refTransLabel`, and the show-types option, which no mapper reads, changes nothing in the
exported graph. -/
@[evidence consistent EXP_003 EXP_007_label EXP_007_config]
theorem clashExport_showTypes :
    EXP_003 refExport ∧ EXP_007_label refTransLabel ∧ EXP_007_config refExport ∧
      ExportAgrees refExport refEmit refCardLabel refTransLabel refPlaceCategory ∧
      ∀ (cfg : ExportCfg) (X : ExportNet) (b : Bool),
        refExport { cfg with showTypes := b } X = refExport cfg X :=
  ⟨EXP_003_any _, EXP_007_label_reference, EXP_007_config_any _, clashExport_agrees,
    fun cfg X b => refExportWith_showTypes _ cfg X b⟩

/-! ## exp-a#8 and exp-b#8 (c): a place that is written and only read (ruling D51 (a)) -/

/-- `w` produces into `P`; `r` reads `P`; no transition consumes from `P`. -/
def clashExportReadOnlyNet : ExportNet :=
  { trans := [{ core := ⟨"w", [], [], [], []⟩, out := some (.place "P") },
              { core := ⟨"r", [], [], ["P"], []⟩ }] }

/-- The reference draws `P` as a regular place (a read arc is outgoing, the Java and TypeScript
reading and the end state of D51); the Rust classifier makes it an end place. -/
theorem clashExport_readOnly_open :
    (refExport {} clashExportReadOnlyNet).nodes.map (fun n => (n.ref, n.cat)) =
        [(.place "P", .place), (.trans "w", .transition), (.trans "r", .transition)] ∧
      exp008_inputsOnly clashExportReadOnlyNet.toNet (ExportCfg.isEnv {})
        clashExportReadOnlyNet.isTerm "P" = .«end» := by
  rw [refExport_nodes_flat]
  decide

/-- ✓ **exp-a#8 and exp-b#8 (c), ruling D51 (a).** EXP-002 and EXP-014 hold of the reference
exporter, EXP-008 of the reference classifier it agrees with (the Java and TypeScript shape) and
of the Rust classifier `exp008_inputsOnly`. On the place that is written and only read the two
classifiers differ, and no block decides between them, so the byte equality the clash asks
about is not a consequence of the blocks; it stays kind Q until the Rust mapper changes. -/
@[evidence consistent EXP_002 EXP_008 EXP_014]
theorem clashExport_readOnly :
    EXP_002 refExport ∧ EXP_014 refExport ∧ EXP_008 (refPlaceCategory (N := String)) ∧
      EXP_008 (exp008_inputsOnly (N := String)) ∧
      ExportAgrees refExport refEmit refCardLabel refTransLabel refPlaceCategory ∧
      (refExport {} clashExportReadOnlyNet).nodes.map (fun n => (n.ref, n.cat)) =
        [(.place "P", .place), (.trans "w", .transition), (.trans "r", .transition)] ∧
      exp008_inputsOnly clashExportReadOnlyNet.toNet (ExportCfg.isEnv {})
        clashExportReadOnlyNet.isTerm "P" = .«end» := by
  refine ⟨EXP_002_any _, EXP_014_any _, EXP_008_reference, ?_, clashExport_agrees,
    clashExport_readOnly_open⟩
  -- `EXP_008_allows_inputsOnly` is stated at `Nat`; the same case split at `String`.
  intro X env term p
  unfold exp008_inputsOnly
  cases term p <;> cases env p <;> cases HasOutputArc X p <;> cases HasInputArc X p <;>
    cases HasReadArc X p <;> simp +contextual

/-! ## exp-a#9 and exp-a#10: the five place categories (ruling D51 (a)) -/

/-- `T` consumes the environment place `e` and produces into the terminal place `z`; `U`
inhibits on `h`. -/
def clashExportCatNet : ExportNet :=
  { trans := [{ core := ⟨"T", [⟨"e", .one⟩], [], [], []⟩, out := some (.place "z") },
              { core := ⟨"U", [], ["h"], [], []⟩ }],
    term := ["z"] }

/-- The configuration that names `e` an environment place. -/
def clashExportEnvCfg : ExportCfg := { env := ["e"] }

/-- The categories the reference draws: `e` has no incoming arc and is an environment place,
not a start place; `z` has no outgoing arc and is terminal, not an end place; `h`, which only
an inhibitor arc touches, is a start place. -/
theorem clashExport_catNet :
    (refExport clashExportEnvCfg clashExportCatNet).nodes.map (fun n => (n.ref, n.cat)) =
      [(.place "e", .environment), (.place "z", .terminal), (.place "h", .start),
       (.trans "T", .transition), (.trans "U", .transition)] := by
  rw [refExport_nodes_flat]
  decide

/-- ✓ **exp-a#9 and exp-a#10, ruling D51 (a).** EXP-002 and EXP-008 hold together of the
reference exporter and the reference classifier it agrees with: every place node gets one of the
five place rows of the style table, with terminal first, then environment, then start, then end,
and inhibitor and reset arcs count for neither incoming nor outgoing. -/
@[evidence consistent EXP_002 EXP_008]
theorem clashExport_categories :
    EXP_002 refExport ∧ EXP_008 (refPlaceCategory (N := String)) ∧
      ExportAgrees refExport refEmit refCardLabel refTransLabel refPlaceCategory ∧
      (refExport clashExportEnvCfg clashExportCatNet).nodes.map (fun n => (n.ref, n.cat)) =
        [(.place "e", .environment), (.place "z", .terminal), (.place "h", .start),
         (.trans "T", .transition), (.trans "U", .transition)] :=
  ⟨EXP_002_any _, EXP_008_reference, clashExport_agrees, clashExport_catNet⟩

/-! ## exp-b#1: a group with one child (ruling D26) -/

/-- A one-child And and a one-child Xor both draw one direct edge and no junction, and the
one-child And is the spec `Place(a)` in the firing view. -/
theorem clashExport_short :
    (refEmit "T" [] (.and [.place "a"])).junctions = [] ∧
      (refEmit "T" [] (.and [.place "a"])).edges.map (fun e => (e.src, e.dst, e.label)) =
        [(.trans "T", .place "a", none)] ∧
      refEmit "T" [] (.xor [.place "a"]) = refEmit "T" [] (.and [.place "a"]) ∧
      (OutTree.and [.place "a"]).view = some (.place "a") :=
  ⟨by decide, by decide, by decide, rfl⟩

/-- ✓ **exp-b#1, ruling D26.** EXP-012 holds of the reference emitter together with IO-012 on
the reference check, builder and firing relation. IO-012 makes an Xor a node with two or more
children (the binary `Out.xor` has two), so AC3 is restated with `AND(P_a)`; the emitter draws a
group with fewer than two children as one direct edge, whatever its kind, so the mappers'
pass-through arm for a hand-built one-child Xor draws the same thing. -/
@[evidence consistent EXP_012 IO_012]
theorem clashExport_shortGroup :
    EXP_012 refEmit ∧
      IO_012 (IO_012_check (N := String)) refBuild (RefFire (N := String)) ∧
      (refEmit "T" [] (.and [.place "a"])).junctions = [] ∧
      (refEmit "T" [] (.and [.place "a"])).edges.map (fun e => (e.src, e.dst, e.label)) =
        [(.trans "T", .place "a", none)] ∧
      refEmit "T" [] (.xor [.place "a"]) = refEmit "T" [] (.and [.place "a"]) ∧
      (OutTree.and [.place "a"]).view = some (.place "a") :=
  ⟨EXP_012_reference, IO_012_reference, clashExport_short⟩

/-! ## exp-b#3: a reset place named by two leaves (ruling D26) -/

/-- `T` resets `P` and has `Xor(P, And(P, Q))`: two branches that differ, so IO-012 accepts it. -/
def clashExportMultT : ExportTrans :=
  { core := ⟨"T", [], [], [], ["P"]⟩, out := some (.xor [.place "P", .and [.place "P", .place "Q"]]) }

/-- `T` builds, IO-012's check accepts its spec, and the reference draws one reset+out edge per
leaf naming `P` and no standalone reset edge. -/
theorem clashExport_multNet :
    refBuild clashExportMultT.toTrans = none ∧
      clashExportMultT.toTrans.out.map IO_012_check = some none ∧
      (refExport {} { trans := [clashExportMultT] }).edges.map clashExportLook =
        [(.trans "T", .junction "T" .xor 0, .output, false, none),
         (.junction "T" .xor 0, .place "P", .resetOutput, false, some "reset+out"),
         (.junction "T" .xor 0, .junction "T" .and 1, .output, false, none),
         (.junction "T" .and 1, .place "P", .resetOutput, false, some "reset+out"),
         (.junction "T" .and 1, .place "Q", .output, false, none)] := by
  decide

/-- ✓ **exp-b#3, ruling D26.** EXP-013 holds of the reference exporter together with IO-012 on
the reference: a spec that names a reset place in two leaves builds, and every output edge to the
place is drawn as a reset+out edge, one per leaf, with no standalone reset edge, which is the
restated sentence; 'exactly one edge to P' held only for a spec that names P once. -/
@[evidence consistent EXP_013 IO_012]
theorem clashExport_multiLeaf :
    EXP_013 refExport ∧
      IO_012 (IO_012_check (N := String)) refBuild (RefFire (N := String)) ∧
      refBuild clashExportMultT.toTrans = none ∧
      clashExportMultT.toTrans.out.map IO_012_check = some none ∧
      (refExport {} { trans := [clashExportMultT] }).edges.map clashExportLook =
        [(.trans "T", .junction "T" .xor 0, .output, false, none),
         (.junction "T" .xor 0, .place "P", .resetOutput, false, some "reset+out"),
         (.junction "T" .xor 0, .junction "T" .and 1, .output, false, none),
         (.junction "T" .and 1, .place "P", .resetOutput, false, some "reset+out"),
         (.junction "T" .and 1, .place "Q", .output, false, none)] :=
  ⟨EXP_013_any _, IO_012_reference, clashExport_multNet⟩

/-! ## exp-b#4: the combined edge replaces the leaf's label and style (ruling D26) -/

/-- `T` consumes `i`, resets `P` and `Q`, and has `Timeout(5, And(P, ForwardInput(i, Q)))`. -/
def clashExportComboT : ExportTrans :=
  { core := ⟨"T", [⟨"i", .one⟩], [], [], ["P", "Q"]⟩,
    out := some (.timeout 5 (.and [.place "P", .forward "i" "Q"])) }

/-- `S` resets `P` and has `Timeout(5, P)`. -/
def clashExportComboS : ExportTrans :=
  { core := ⟨"S", [], [], [], ["P"]⟩, out := some (.timeout 5 (.place "P")) }

/-- Both build; the leaf edges into the reset places are solid reset+out edges, without the
Timeout label of `S` and without the ForwardInput label and dash of `T`. -/
theorem clashExport_comboNet :
    refBuild clashExportComboT.toTrans = none ∧ refBuild clashExportComboS.toTrans = none ∧
      (refExport {} { trans := [clashExportComboT, clashExportComboS] }).edges.map clashExportLook =
        [(.place "i", .trans "T", .input, false, none),
         (.trans "T", .junction "T" .and 0, .output, false, some "⏱5ms"),
         (.junction "T" .and 0, .place "P", .resetOutput, false, some "reset+out"),
         (.junction "T" .and 0, .place "Q", .resetOutput, false, some "reset+out"),
         (.trans "S", .place "P", .resetOutput, false, some "reset+out")] := by
  decide

/-- ✓ **exp-b#4, ruling D26.** EXP-005 and EXP-012 hold of the reference emitter and EXP-013 of
the reference exporter that agrees with it. Where a leaf edge ends in a reset place of its
transition, EXP-013's combined edge replaces the label and style EXP-012 would give it: no
Timeout label (`S`), no ForwardInput label and no dash (`T`), the label `reset+out` and the
reset+out row. A Timeout above a junction keeps its label on the edge into the junction. -/
@[evidence consistent EXP_005 EXP_012 EXP_013]
theorem clashExport_combined :
    EXP_005 refEmit ∧ EXP_012 refEmit ∧ EXP_013 refExport ∧
      ExportAgrees refExport refEmit refCardLabel refTransLabel refPlaceCategory ∧
      refBuild clashExportComboT.toTrans = none ∧ refBuild clashExportComboS.toTrans = none ∧
      (refExport {} { trans := [clashExportComboT, clashExportComboS] }).edges.map clashExportLook =
        [(.place "i", .trans "T", .input, false, none),
         (.trans "T", .junction "T" .and 0, .output, false, some "⏱5ms"),
         (.junction "T" .and 0, .place "P", .resetOutput, false, some "reset+out"),
         (.junction "T" .and 0, .place "Q", .resetOutput, false, some "reset+out"),
         (.trans "S", .place "P", .resetOutput, false, some "reset+out")] :=
  ⟨EXP_005_reference, EXP_012_reference, EXP_013_any _, clashExport_agrees, clashExport_comboNet⟩

/-! ## exp-b#8: cross-language byte equality (ruling D60 (c)) -/

/-- ✓ **exp-b#8, ruling D60 (c).** The blocks whose acceptance criteria repeat the byte-equality
claim hold together of one reference: EXP-001, EXP-013, EXP-014, EXP-016, EXP-017 and EXP-018
of the clustered exporter, EXP-012 of the emitter and EXP-008 of the classifier it agrees with.
None of them states node or edge order or byte equality across runtimes; those stay kind Q (the
export corpus EP-2 after the migration). -/
@[evidence consistent EXP_001 EXP_008 EXP_012 EXP_013 EXP_014 EXP_016 EXP_017 EXP_018]
theorem clashExport_joint :
    EXP_001 refExport ∧ EXP_008 (refPlaceCategory (N := String)) ∧ EXP_012 refEmit ∧
      EXP_013 refExport ∧ EXP_014 refExport ∧ EXP_016 refExport ∧ EXP_017 refExport ∧
      EXP_018 refExport ∧
      ExportAgrees refExport refEmit refCardLabel refTransLabel refPlaceCategory :=
  ⟨EXP_001_any _, EXP_008_reference, EXP_012_reference, EXP_013_any _, EXP_014_any _,
    EXP_016_reference, EXP_017_reference, EXP_018_any _, clashExport_agrees⟩

/-! ## exp-b#5, exp-b#9 to exp-b#12 and S-4: clusters and ghost edges (rulings D26, D46 (a)) -/

/-- ✓ **exp-b#5 (EXP-016 and EXP-017 half), exp-b#9, exp-b#10, exp-b#11, exp-b#12 and S-4,
rulings D26 and D46 (a).** EXP-014, EXP-016 and EXP-017 hold together of the clustered reference
exporter, and on it:
* a junction takes its transition's cluster key (exp-b#10, D26 item 5);
* under the default source a node takes its membership entry, else its instance prefix
  (exp-b#11);
* clustering changes no node and no edge other than the ghost edges (S-4: "clustering changes no
  edge" is read over the non-ghost edges);
* on the worked example, three orphans bridging `b1` to `b2` give one ghost edge, anchored at the
  first bridge, and one orphan bridging `b2` to `b1` gives the other (exp-b#12);
* the name `a//x` has the cluster key `a/`, which has an empty `/` segment and so lies outside
  the name assumption of EXP-016 and EXP-017 (exp-b#9). -/
@[evidence consistent EXP_014 EXP_016 EXP_017]
theorem clashExport_cluster :
    EXP_014 refExport ∧ EXP_016 refExport ∧ EXP_017 refExport ∧
      (∀ (src : ClusterSource) (m : String → Option String) (t : String) (k : JKind) (i : Nat),
        nodeKey src m (.junction t k i) = nodeKey src m (.trans t)) ∧
      (∀ (m : String → Option String) (n : String),
        clusterKey .auto m n = (m n).or (instancePrefix n)) ∧
      (∀ (cfg : ExportCfg) (X : ExportNet),
        (refExport cfg X).nodes = (refExportFlat cfg X).nodes ∧
        (refExport cfg X).edges.filter (fun e => e.arc != .ghost) =
          (refExportFlat cfg X).edges.filter (fun e => e.arc != .ghost)) ∧
      ((refExport {} clusterExNet).edges.filter (fun e => e.arc == .ghost)).map
          (fun e => (nodeId e.src, nodeId e.dst, e.ltail, e.lhead)) =
        [("p_b1_out", "p_b2_in", some "cluster_b1", some "cluster_b2"),
         ("p_b2_in", "p_b1_in", some "cluster_b2", some "cluster_b1")] ∧
      instancePrefix "a//x" = some "a/" ∧ ¬ NoEmptySegment "a/" :=
  ⟨EXP_014_any _, EXP_016_reference, EXP_017_reference, nodeKey_junction, clusterKey_auto,
    fun _ _ => ⟨refExport_nodes_flat, refExport_nonGhost_flat⟩, refExport_example_ghosts,
    by decide⟩

end Libpetri.Spec
