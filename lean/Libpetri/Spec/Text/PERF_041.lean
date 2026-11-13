import Libpetri.Spec.Text

requirement_text PERF_041
  id "PERF-041"
  title "Precompiled Executor Target Speedup"
  priority SHOULD
  kind Q
  body r#"The precompiled flat-array executor SHOULD achieve 2–4× speedup on synchronous chains compared to the bitmap executor. This target assumes trivial synchronous actions, warm runtime, and noop event store.

Benchmark scenarios SHOULD include precompiled executor results alongside bitmap executor results [PERF-020] for direct comparison.

**Acceptance Criteria:**
1. Benchmark suite includes precompiled executor variants for chain scenarios.
2. Precompiled executor achieves measurable speedup over bitmap executor on sync chains.
3. Results are documented alongside bitmap executor benchmarks.

**Depends on:** [CONC-020], [PERF-020]
**Test derivation:** Run sync chain benchmarks with both executors; compare throughput."#
