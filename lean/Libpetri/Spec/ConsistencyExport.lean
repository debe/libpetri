import Libpetri.Spec.Req.EXP_012
import Libpetri.Spec.Req.EXP_008
import Libpetri.Reference.Export

set_option linter.missingDocs true

/-!
# Consistency of the export requirements (skeleton)

The target of this module is one theorem, `spec_consistent_export`, that picks one witness for
every abstract function the EXP blocks quantify over (the exporter, the output emitter, the
cardinality labeller, the transition labeller and the place classifier), ties them together with
the glossary predicate `ExportAgrees` (the exporter's output edges are the emitter's, its input
labels the labeller's, its transition labels and place categories the label function's and the
classifier's), and shows that every EXP block holds of them:

`∃ E Em L TL C, ExportAgrees E Em L TL C ∧ EXP_001 E ∧ … ∧ EXP_012 Em ∧ … ∧ EXP_018 E`,
instantiated by `refExport`, `refEmit`, `refCardLabel`, `refTransLabel`, `refClassify`.

Without the agreement predicate each block could be met by a different function and the
conjunction would say nothing about one exporter, so every later block of wave W4 adds its
conjunct here with the witness its own holds theorem uses.

The export model reads no marking, so the join with the firing chain is not a shared witness but
a pair of lemmas over one net definition: `toTrans_core` (the mapper half: the arcs the exporter
draws are the arcs `RefFire` fires on) and `refEmit_leafTargets` (the places the output edges end
in are `outPlaces` of the firing model's view of the same output spec). The whole-spec theorem is
then `spec_consistent_coreIO_time (N := String) ∧ spec_consistent_export ∧ refExport_reads_net`.

This file is the skeleton of the W4 tracer: `joint_export_sketch` fixes the shape with the first
block, EXP-012, and the emitter half of the join. Wave W1 adds EXP-008 on the reference place
classifier `refPlaceCategory`, as its own conjunct: the agreement that ties the classifier to the
exporter's place nodes is EXP-002's join line (wave W4).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

/-- ✓ The skeleton of `spec_consistent_export`: one output emitter satisfies EXP-012 and draws
its output edges into exactly the places the firing model's view of the same output spec names
(`outPlaces`, hence `OutputArc`), whenever that view exists. The witness is the reference
emitter `refEmit`. One place classifier satisfies EXP-008; the witness is `refPlaceCategory`. -/
@[evidence consistent EXP_012 EXP_008]
theorem joint_export_sketch :
    (∃ Em : Emitter, EXP_012 Em ∧
      ∀ (t : String) (R : List String) (o : OutTree) (o' : Out String), o.toOut = some o' →
        (Em t R o).edges.filterMap XEdge.placeTarget = outPlaces o') ∧
    (∃ C : PlaceClassifier String, EXP_008 C) :=
  ⟨⟨refEmit, EXP_012_reference, refEmit_leafTargets⟩, ⟨_, EXP_008_reference⟩⟩

end Libpetri.Spec
