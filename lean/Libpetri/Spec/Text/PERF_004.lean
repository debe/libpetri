import Libpetri.Spec.Text

requirement_text PERF_004
  id "PERF-004"
  title "Lock-Free Hot Path"
  priority MUST
  kind Q
  body r#"The completion signaling path (action completing → orchestrator notified) uses lock-free data structures. No mutex/lock acquisition on the hot path.

**Acceptance Criteria:**
1. Completion queue is lock-free (CAS-based, channel-based, or similar).
2. Wake-up signal does not require acquiring a contended lock.

**Depends on:** [CONC-006]
**Test derivation:** 100 concurrent action completions; verify no lock contention in profiler."#
