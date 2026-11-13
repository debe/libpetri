import Libpetri.Spec.Text

requirement_text PERF_003
  id "PERF-003"
  title "Dirty Set O(affected)"
  priority MUST
  kind Q
  body r#"Each orchestrator cycle re-evaluates only the transitions affected by token changes since the last cycle. The cost is O(D) where D is the number of dirty transitions, not O(T) where T is the total transition count.

**Acceptance Criteria:**
1. Adding a token to a place with 3 connected transitions causes exactly 3 re-evaluations.
2. Transitions connected to unchanged places are not re-evaluated.

**Depends on:** [CONC-005]
**Test derivation:** Net with 50 transitions; token change affects 3; verify only 3 re-evaluated (via instrumentation or timing)."#
