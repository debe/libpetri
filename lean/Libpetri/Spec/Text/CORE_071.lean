import Libpetri.Spec.Text

requirement_text CORE_071
  id "CORE-071"
  title "Marking Thread Safety"
  priority MUST
  kind A
  body r#"The live marking is mutated only by the orchestrator thread. It is NOT thread-safe. Transition actions must NOT directly access the marking.

An implementation MAY additionally expose a read-only observation path that returns an owned, independent copy of the marking to a non-orchestrator caller (see `marking()` used cross-thread, and [ENV-014]). Such a copy is explicitly best-effort: it is produced without blocking the orchestrator, so places may be captured at different instants and the copy carries no consistency guarantee. It MUST NOT mutate, or force synchronization onto, the live marking, and the live marking itself remains lock-free.

**Acceptance Criteria:**
1. No synchronization primitives are used in the marking implementation.
2. Token production from actions goes through the context/output mechanism, not direct marking access.
3. Any cross-thread observation returns an independent copy; it never hands out the live marking instance while the orchestrator is running.

**Test derivation:** Architectural review; verify marking has no locks/atomics; verify a cross-thread read returns a distinct instance from the live marking."#
