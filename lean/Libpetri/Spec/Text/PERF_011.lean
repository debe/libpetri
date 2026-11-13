import Libpetri.Spec.Text

requirement_text PERF_011
  id "PERF-011"
  title "Inline Action Optimization"
  priority SHOULD
  kind Q
  body r#"Synchronous actions (passthrough, simple transforms) that complete immediately SHOULD be executed inline on the orchestrator thread, avoiding task dispatch overhead.

**Acceptance Criteria:**
1. Passthrough action executes without spawning a task.
2. Chain of N transitions bound to trivial synchronous actions completes with overhead proportional to N, not N × task_spawn_cost.

**Depends on:** [CONC-011]
**Test derivation:** Chain of 100 transitions bound to trivial synchronous actions; measure total time; verify sub-millisecond per transition."#
