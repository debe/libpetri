import Libpetri.Spec.Text

requirement_text PERF_001
  id "PERF-001"
  title "Linear Scaling"
  priority MUST
  kind Q
  body r#"Execution time scales linearly with the number of transitions in the net. There MUST be no quadratic or worse blowup in the orchestrator loop.

**Acceptance Criteria:**
1. A net with 2N transitions takes approximately 2× the orchestrator time of a net with N transitions (for equivalent workloads).
2. No O(n²) iteration over all transitions on each cycle (dirty set ensures only affected transitions are re-evaluated).

**Depends on:** [CONC-005]
**Test derivation:** Benchmark chain nets of 5, 50, and 500 transitions; verify near-linear scaling of orchestrator overhead."#
