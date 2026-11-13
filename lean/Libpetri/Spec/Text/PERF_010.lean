import Libpetri.Spec.Text

requirement_text PERF_010
  id "PERF-010"
  title "Noop Event Store Zero-Cost"
  priority MUST
  kind Q
  body r#"When the noop event store is used (isEnabled() returns false), the executor MUST skip event object creation entirely. No allocation occurs for events that will be discarded.

**Acceptance Criteria:**
1. Executor checks isEnabled() before creating event objects.
2. With noop store, no event objects are allocated.
3. Measurable performance difference between noop and in-memory stores under load.

**Depends on:** [EVT-022]
**Test derivation:** Benchmark same net with noop vs in-memory store; verify noop is faster (no allocation overhead)."#
