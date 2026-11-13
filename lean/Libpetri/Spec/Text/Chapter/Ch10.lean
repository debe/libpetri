import Libpetri.Spec.Text
import Libpetri.Spec.Text.PERF_001
import Libpetri.Spec.Text.PERF_002
import Libpetri.Spec.Text.PERF_003
import Libpetri.Spec.Text.PERF_004
import Libpetri.Spec.Text.PERF_010
import Libpetri.Spec.Text.PERF_011
import Libpetri.Spec.Text.PERF_020
import Libpetri.Spec.Text.PERF_021
import Libpetri.Spec.Text.PERF_022
import Libpetri.Spec.Text.PERF_030
import Libpetri.Spec.Text.PERF_031
import Libpetri.Spec.Text.PERF_040
import Libpetri.Spec.Text.PERF_041
import Libpetri.Spec.Text.PERF_042

spec_chapter "10-performance.md"
  scope "Scaling, benchmarks, memory efficiency, flat-array executor performance"
  md r#"# 10 — Performance

This document specifies scaling requirements, benchmark expectations, and performance-related design constraints.

---

## Scaling Requirements"#
  req PERF_001
  md r#"---"#
  req PERF_002
  md r#"---"#
  req PERF_003
  md r#"---"#
  req PERF_004
  md r#"---

## Noop Event Store"#
  req PERF_010
  md r#"---

## Inline Execution"#
  req PERF_011
  md r#"---

## Benchmark Suite"#
  req PERF_020
  md r#"---"#
  req PERF_021
  md r#"---"#
  req PERF_022
  md r#"---

## Memory Efficiency"#
  req PERF_030
  md r#"---"#
  req PERF_031
  md r#"---

## Flat-Array Executor Performance"#
  req PERF_040
  md r#"---"#
  req PERF_041
  md r#"---"#
  req PERF_042
