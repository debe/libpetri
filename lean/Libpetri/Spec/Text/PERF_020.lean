import Libpetri.Spec.Text

requirement_text PERF_020
  id "PERF-020"
  title "Benchmark Suite"
  priority MUST
  kind Q
  body r#"Each implementation MUST include a benchmark suite covering the following scenarios:

1. **Single passthrough**: One transition with passthrough action.
2. **Linear chain**: Sequence of N transitions (for N = 5, 10, 50, 100, 500).
3. **Parallel branches**: Multiple independent branches firing concurrently.
4. **Sync-only chain**: Chain of synchronous actions (inline execution path).
5. **Async chain**: Chain of actions with async work (task dispatch path).
6. **Mixed net**: Combination of sync and async actions.

**Acceptance Criteria:**
1. Benchmarks are executable as part of the build/test pipeline.
2. Results are reproducible (low variance).
3. Benchmarks cover both sync-inline and async-dispatch paths.

**Test derivation:** Run benchmark suite; verify all scenarios execute without errors."#
