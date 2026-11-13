import Libpetri.Spec.Text

requirement_text CONC_011
  id "CONC-011"
  title "Inline Synchronous Execution"
  priority SHOULD
  kind Q
  body r#"When an action completes synchronously (returns an immediately-resolved future or signals inline execution support), the executor SHOULD avoid task pool dispatch entirely and run the action inline on the orchestrator thread. This eliminates scheduling overhead for pure-compute workflows.

**Acceptance Criteria:**
1. Passthrough actions execute inline without task dispatch.
2. Synchronous transform actions execute inline when the action signals inline support.
3. The orchestrator never dispatches actions itself; an async action returns a handle backed by its own executor, and the orchestrator continues once the handle is returned ([CONC-002]).

**Test derivation:** Chain of 10 transitions bound to trivial synchronous actions; measure overhead; verify no task dispatch."#
