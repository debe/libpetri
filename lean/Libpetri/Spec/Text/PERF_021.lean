import Libpetri.Spec.Text

requirement_text PERF_021
  id "PERF-021"
  title "Target Performance Ranges"
  priority SHOULD
  kind Q
  body r#"The following ranges are reference targets, not hard requirements. They represent expected performance for a reasonably optimized implementation on modern hardware:

| Scenario | Target | Notes |
|----------|--------|-------|
| Single passthrough | < 10µs | Minimum overhead per transition |
| Chain of 5 | < 50µs | ~10µs per hop |
| Chain of 10 | < 100µs | ~10µs per hop |
| Chain of 50 | < 500µs | Orchestration overhead per cycle |
| Complex workflow (~50 transitions) | < 500µs per orchestration cycle | Real-world target |

These targets assume:
- Passthrough/sync actions (no async I/O)
- Warm JVM / optimized build
- No event store overhead (noop store)

**Acceptance Criteria:**
1. Implementations document their actual performance against these targets.
2. Significant deviations (> 10×) are investigated and documented.

**Test derivation:** Run benchmarks; record results; compare against targets."#
