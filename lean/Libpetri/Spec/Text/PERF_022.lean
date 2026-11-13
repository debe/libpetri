import Libpetri.Spec.Text

requirement_text PERF_022
  id "PERF-022"
  title "Regression Detection"
  priority MUST
  kind Q
  body r#"Benchmarks MUST be runnable in CI pipelines for regression detection. A significant performance regression (e.g., > 20% slowdown) should be flagged.

**Acceptance Criteria:**
1. Benchmark suite can run in CI.
2. Results can be compared against baseline.
3. Regressions are detectable (via comparison tool or threshold check).

**Test derivation:** Introduce artificial slowdown; verify CI detects regression."#
