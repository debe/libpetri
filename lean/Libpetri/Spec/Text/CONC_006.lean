import Libpetri.Spec.Text

requirement_text CONC_006
  id "CONC-006"
  title "Lock-Free Completion Signaling"
  priority MUST
  kind Q
  body r#"Action completions are communicated to the orchestrator via a lock-free mechanism (lock-free queue, mpsc channel, or similar). The hot path avoids contention on shared locks.

**Acceptance Criteria:**
1. Multiple actions completing simultaneously do not contend on a single lock.
2. Completion notification is O(1) per completion.

**Test derivation:** 10 actions complete near-simultaneously; verify no lock contention (measured via timing, not exceeding linear overhead)."#
