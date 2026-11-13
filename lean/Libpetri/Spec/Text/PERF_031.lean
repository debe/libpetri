import Libpetri.Spec.Text

requirement_text PERF_031
  id "PERF-031"
  title "Token Storage Efficiency"
  priority SHOULD
  kind Q
  body r#"Token storage should be efficient for the common case where places hold 0-5 tokens. Implementations SHOULD avoid excessive pre-allocation.

**Acceptance Criteria:**
1. Empty places consume minimal memory.
2. Places with few tokens use compact sequential storage (e.g., array-backed deque or array).

**Test derivation:** Create marking with 100 places, 3 tokens each; verify memory usage is reasonable."#
