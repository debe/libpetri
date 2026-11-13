import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.EVT_025
import Libpetri.Spec.Text.EVT_025

runtime_defect RD_17
  title "Java's archive header order changes from one JVM to the next"
  requirements r#"EVT-025 (two archives of identical run data are identical)."#
  runtimes r#"Java."#
  defect r#"the V2 and V3 header build the tags and the metadata histogram with `Map.copyOf`,
whose iteration order is randomised per JVM, and the writer serialises maps in iteration order.
The compact constructors of `SessionArchive.V2` and `SessionArchive.V3`
(`java/src/main/java/org/libpetri/debug/archive/SessionArchive.java`) and of `SessionMetadata`
(`java/src/main/java/org/libpetri/debug/archive/SessionMetadata.java`). The writer makes its own
`Map.copyOf` of the tags before the header does (`writeV2` and `writeV3` in
`java/src/main/java/org/libpetri/debug/archive/SessionArchiveWriter.java`), so every
V2 and V3 header the writer writes is affected."#
  evidence r#"⟪EVT_025_mutant_seededTags⟫ (EVT_025.lean)."#
  fix r#"the header tags and the metadata histogram are unmodifiable maps in ascending code-point
order of their keys (`CodePointOrder.sortedCopy`), and the writer hands the session's tags to the
header without a copy of its own. Java
`SessionArchiveV3Test.headerRendersTagsAndHistogramInAscendingKeyOrder_EVT025` and
`readBackTagsAndHistogramIterateInAscendingKeyOrder_EVT025`."#
  status "fixed, unreleased"
