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
import Libpetri.Reference.Export
import Libpetri.Reference.ExportCluster

set_option linter.missingDocs true

/-!
# Consistency of the export requirements

One theorem, `joint_export_sketch`, picks one witness for every abstract function the EXP blocks
quantify over (the exporter, the output emitter, the cardinality labeller, the transition
labeller and the place classifier), ties them together with the glossary predicate
`ExportAgrees` (the exporter's output edges and junctions are the emitter's, with the edges out
of each junction in the emitter's order, its input labels the
labeller's, its transition labels and place categories the label function's and the
classifier's), and shows that every EXP block holds of them:

`∃ E Em L TL C, ExportAgrees E Em L TL C ∧ EXP_001 E ∧ … ∧ EXP_012 Em ∧ … ∧ EXP_018 E`,
instantiated by `refExport`, `refEmit`, `refCardLabel`, `refTransLabel`, `refPlaceCategory`.

Without the agreement predicate each block could be met by a different function and the
conjunction would say nothing about one exporter. The exporter is the clustered reference
`refExport = refExportWith refClusterStage` (`Reference/ExportCluster.lean`): the blocks that do
not read clusters hold of `refExportWith S` for every cluster stage `S` (their `_any` lemmas),
EXP-016 and EXP-017 hold of `refExport` itself, and `refExportWith_agrees` gives the agreement at
that stage.

The export model reads no marking, so the join with the firing chain is not a shared witness but
a lemma over one output spec: `refEmit_leafTargets` (the places the emitter's output edges end in
are `outPlaces` of the firing model's view of the same output spec, hence `OutputArc`). The
mapper half of the join is `ExportTrans.toTrans_core` and `ExportNet.toNet_viewOf`
(`Reference/Export.lean`): the arcs the exporter draws are the arcs the firing model fires on, and
the net it reads is the view of a built net (wave W2).

The name keeps the tracer's, since the CI axiom list and the proof graph refer to it; the theorem
is the whole export conjunction.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

/-- ✓ **The export requirements hold together** of one reference family: the clustered reference
exporter `refExport`, the reference emitter `refEmit`, the cardinality labeller `refCardLabel`,
the transition labeller `refTransLabel` and the place classifier `refPlaceCategory`, tied by
`ExportAgrees`. Every EXP block of waves W0, W1 and W4 holds of its member of the family, and the
emitter draws its output edges into exactly the places the firing model's view of the same
output spec names (`outPlaces`, hence `OutputArc`), whenever that view exists. -/
@[evidence consistent EXP_001 EXP_002 EXP_003 EXP_004 EXP_005 EXP_006 EXP_007_label
  EXP_007_config EXP_008 EXP_012 EXP_013 EXP_014 EXP_016 EXP_017 EXP_018]
theorem joint_export_sketch :
    ∃ (E : Exporter) (Em : Emitter) (L : Card → Option String) (TL : TransLabeller)
      (C : PlaceClassifier String),
      ExportAgrees E Em L TL C ∧
      EXP_001 E ∧ EXP_002 E ∧ EXP_003 E ∧ EXP_004 E ∧ EXP_005 Em ∧ EXP_006 L ∧
      EXP_007_label TL ∧ EXP_007_config E ∧ EXP_008 C ∧ EXP_012 Em ∧ EXP_013 E ∧
      EXP_014 E ∧ EXP_016 E ∧ EXP_017 E ∧ EXP_018 E ∧
      ∀ (t : String) (R : List String) (o : OutTree) (o' : Out String), o.toOut = some o' →
        (Em t R o).edges.filterMap XEdge.placeTarget = outPlaces o' :=
  ⟨refExport, refEmit, refCardLabel, refTransLabel, refPlaceCategory,
    refExportWith_agrees refClusterStage,
    EXP_001_any _, EXP_002_any _, EXP_003_any _, EXP_004_any _, EXP_005_reference,
    EXP_006_reference, EXP_007_label_reference, EXP_007_config_any _, EXP_008_reference,
    EXP_012_reference, EXP_013_any _, EXP_014_any _, EXP_016_reference, EXP_017_reference,
    EXP_018_any _, refEmit_leafTargets⟩

end Libpetri.Spec
