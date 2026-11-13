import Libpetri.Spec.Ledger
import Libpetri.Spec.Text.EVT_032

runtime_defect RD_48
  title "No debug protocol handler invalidates its replay cache after an eviction"
  requirements r#"EVT-032 (AC3: a cache whose event list changed other than by growing at its end
needs `invalidate()` before the next call)."#
  runtimes r#"Java, TypeScript, Rust, Python."#
  defect r#"the debug protocol handler kept one marking replay cache per session and reused it
after the session's debug event store evicted events. A seek or a step backward after an eviction
replayed from a snapshot of events the store no longer held, so it returned a state that is not
the replay of the retained events."#
  evidence r#"none; EVT_032 and EVT_032_B state the cache contract and assume a coherent
caller."#
  fix r#"the handler invalidates the cache before it computes a state whenever the store's
evicted count changed since the cache was last used (Java also compares the first retained
event). Java `DebugProtocolHandler.SubscriptionState.computeStateAt`, TypeScript
`SubscriptionState.computeStateAt` in `debug-protocol-handler.ts`, Rust `compute_state_at` in
`debug_protocol_handler.rs`; Python uses the Rust handler. Tests: Java
`DebugProtocolHandlerTest.SeekAndStepFlow.seekAfterEvictionReplaysTheRetainedEvents_EVT032_AC3`
and the step-backward twin, the TypeScript and Rust handler tests citing EVT-032."#
  status "fixed, unreleased"
