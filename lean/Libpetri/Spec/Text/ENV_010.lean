import Libpetri.Spec.Text

requirement_text ENV_010
  id "ENV-010"
  title "Implicit Long-Running Behavior"
  priority MUST
  kind B
  body r#"⟦s1|When environment places are registered with the executor, the executor does NOT terminate at quiescence (no transition armed, no firing in flight, and no completion, publication or external event queued, as in [EXEC-040]) while it has not been drained ([ENV-011]), closed ([ENV-013]) or stopped by an immediate termination ([ENV-015]) and no terminal place is marked ([EXEC-042]).⟧ ⟦s2|Instead, it waits for external events that may enable new transitions.⟧ ⟦s3|This behavior is derived from the presence of environment places: no explicit flag is needed.⟧

When no environment places are registered, the executor terminates at quiescence per [EXEC-040].

A drain, a close, an immediate termination or a marked terminal place lets such an executor end ([ENV-011], [ENV-013], [ENV-015], [EXEC-042]). In Rust, an executor whose signal channel has closed (every sender dropped) accepts no injection and ends at quiescence as a drained one does; dropping an `ExecutorHandle` sends a drain first. Rust's `run_sync` has no signal channel, so it accepts no injection and ends at quiescence whatever is registered; it is outside this requirement. In Java, an interrupt taken while the loop waits ends the run as interrupted ([EXEC-041]).

⟦s4|*While* environment places are registered, the executor is open (it has not been drained, closed or stopped by an immediate termination) and no terminal place is marked ([EXEC-042]), the executor *shall not* terminate as quiescent ([EXEC-041]).⟧

⟦s5|*While* environment places are registered, the executor is open and running and no terminal place is marked, *when* a caller asks to inject a token into a registered environment place, the executor *shall* answer the request and *shall* accept the injection.⟧

⟦s6|*While* environment places are registered, the executor is open and no terminal place is marked, *when* the loop reaches its termination test ([EXEC-040]), the executor *shall* go on to its firing pass ([EXEC-001]).⟧

⟦s7|*While* environment places are registered, the executor is open and no terminal place is marked, *when* an accepted injection is queued, the executor *shall* leave its wait ([ENV-005]) and *shall* inject the oldest queued injection in its event step ([ENV-003]).⟧

⟦s8|The executor *shall not* need a long-running flag or any setting other than the registered environment places to wait at quiescence.⟧

**Acceptance Criteria:**
1. Registering environment places causes executor to wait at quiescence instead of terminating.
2. No explicit long-running flag exists on the executor API.
3. Executor with environment places does not terminate at quiescence.
4. Executor without environment places terminates at quiescence.
5. Injecting a token resumes execution from quiescence.

**Depends on:** [ENV-001], [ENV-002], [ENV-003], [ENV-005], [EXEC-001], [EXEC-040], [EXEC-041], [EXEC-042], [TIME-010], [TIME-013]
**Test derivation:** Executor with environment places; all transitions fire; verify executor still running; inject token; verify new transition fires; drain executor; verify termination."#
