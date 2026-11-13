import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.EVT_032
import Libpetri.Spec.Text.EVT_032

runtime_defect RD_22
  title "Java's `computeAt` does not clamp the index"
  requirements r#"EVT-032 (AC2: an index beyond the stream length is clamped; ruling D83 (a))."#
  runtimes r#"Java."#
  defect r#"`MarkingCache.computeAt` passes the index to `subList` and throws
`IndexOutOfBoundsException` past the stream length.
`java/src/main/java/org/libpetri/debug/MarkingCache.java`. The debug protocol handler has the
same unclamped `subList` on its fallback path (RD-46)."#
  evidence r#"⟪EVT_032_mutant_noClamp⟫ (EVT_032.lean)."#
  fix r#"`computeAt` clamps the index to the stream length after its check for an index of 0 or
less. Java `MarkingCacheTest.computeAtBeyondStreamLengthClampsToEnd_EVT032_AC2`."#
  status "fixed, unreleased"
