import Libpetri.Spec.Ledger
import Libpetri.Spec.Req.EVT_032
import Libpetri.Spec.Text.EVT_032

runtime_defect RD_46
  title "Java's debug protocol handler does not clamp a replay index"
  requirements r#"EVT-032 (AC2: an index beyond the stream length is clamped)."#
  runtimes r#"Java."#
  defect r#"`DebugProtocolHandler.ClientState.computeStateAt` passes the index to `subList` on its
fallback without a subscription
(`java/src/main/java/org/libpetri/debug/DebugProtocolHandler.java`), the same unclamped
call as RD-22. It was latent: the protocol commands reach that fallback only with an index within
the stream."#
  evidence r#"⟪EVT_032_mutant_noClamp⟫ (EVT_032.lean)."#
  fix r#"the call clamps the index with `Math.clamp(targetIndex, 0, events.size())`. It has no
test of its own: `ClientState` is private and no protocol command reaches the fallback with an
index past the end; `MarkingCacheTest.computeAtBeyondStreamLengthClampsToEnd_EVT032_AC2` covers
the clamp of RD-22."#
  status "fixed, unreleased"
