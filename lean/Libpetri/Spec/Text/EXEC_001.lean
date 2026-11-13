import Libpetri.Spec.Text

requirement_text EXEC_001
  id "EXEC-001"
  title "Orchestrator Loop Steps"
  priority MUST
  kind B
  body r#"The executor runs a loop with the following steps, in order:

1. **Process completions**: collect outputs from actions that have finished; validate against output specs; deposit produced tokens into marking; emit events.
2. **Process external events**: dequeue and apply externally injected tokens (see [ENV-003]).
3. **Update enablement**: re-evaluate which transitions are enabled based on current marking. Only transitions affected by token changes need re-evaluation (see [CONC-005]).
4. **Enforce deadlines**: reap every armed reapable transition (`Deadline` / `Window`) whose elapsed time is strictly greater than its latest bound plus the deadline tolerance ([TIME-013]). `Exact` transitions are never reaped ([TIME-006]).
5. **Fire ready transitions**: among ready transitions (armed, past their earliest bound and not expired), sort by priority (then FIFO), and fire in order.
6. **Await work**: wait for a completion, a publication, an external event, a drain or close request, or a timer. The loop may wait while actions are in flight, but only if nothing was deposited and no transition with an input or reset arc started since the enablement update, and it must wake on each of these ([CONC-010]).

Between steps 1 and 2, Rust and Python deposit the queued mid-action publications ([IO-015]). A publication is a deposit outside a firing pass, as are the deposits of steps 1 and 2.

A cycle begins when the loop leaves the firing pass or the wait for another step; in the order above that step is step 1. The steps run in this order in every cycle, with two exceptions. The wait of step 6 may itself process the completion, publication or external event that ends it, before the next cycle begins ([ENV-003]). A synchronous action's completion may be admitted inside its own firing pass, after its start ([EXEC-003]).

Two further points about the cycle are checked by other requirements, not by this one. The termination test of [EXEC-040] is made after step 4 and before step 5. Steps 3 to 5 may each take their own reading of the firing clock; each reading is no earlier than the one before, and steps 4 and 5 and the decision to wait judge expiry and readiness at the reading of step 4 ([TIME-013], [CONC-010]).

⟦s1|*When* the executor begins a cycle or deposits tokens outside a firing pass, it *shall not* run a deadline step until it has run an enablement update.⟧

⟦s2|*When* the executor begins a cycle or deposits tokens outside a firing pass, it *shall not* start a transition until it has run a deadline step.⟧

⟦s3|*When* the executor begins a cycle, it *shall not* run an enablement update until it has ended step 2.⟧

⟦s4|*When* the executor begins a cycle or enters step 1, it *shall not* deposit a publication, inject an external event or start a transition until it has processed every finished action queued at that moment, whether the action completed, failed or timed out.⟧

⟦s5|*When* the executor enters step 2 of a cycle while it is neither closed nor terminated immediately, it *shall not* run the next enablement update until it has injected or discarded every external event queued at that moment ([ENV-003], [ENV-013], [ENV-015]).⟧

⟦s6|*If* the deadline step of a cycle reaps a transition, *then* the executor *shall not* start that transition before its next enablement update.⟧

⟦s7|*When* the executor starts a transition that has an input or reset arc, or deposits tokens outside a firing pass or inside a firing pass that has started a transition, it *shall not* wait for work until it has run an enablement update.⟧

⟦s8|*When* the executor runs an enablement update, it *shall* leave every transition whose enablement check fails without a clock, and every transition whose enablement check passes armed or reaped unless the executor is not re-entrant and a firing of that transition is in flight ([CONC-002], [NU-020]).⟧

**Acceptance Criteria:**
1. Each cycle runs steps 1 to 5 in order, except as the two exceptions above allow: the finished actions queued when the cycle begins are processed before any publication, injection or start; step 2 ends before the enablement update; the enablement update runs before the deadline step, and the deadline step before any start.
2. No transition starts before the completions queued when the cycle began are processed, nor, since the last deposit made outside a firing pass, before an enablement update and then a deadline step have run.
3. External events queued when step 2 began, while the executor was neither closed nor terminated, are injected, or discarded once the executor is closed or terminated ([ENV-013], [ENV-015]), before the next enablement update. A step 2 that begins after a close or an immediate termination may leave the queued events in the queue; they are discarded by the end of the run ([ENV-013]).
4. A transition reaped by a deadline step does not start before the next enablement update.
5. After a deposit, or the start of a transition with an input or reset arc, the executor does not wait for work before an enablement update.
6. After an enablement update, no transition whose enablement check fails holds a clock, and every transition whose enablement check passes is armed or reaped, unless the executor is not re-entrant and a firing of that transition is in flight.

A firing's inputs leave the marking in step 5 and its outputs arrive in step 1 of a later cycle
(or, for a synchronous action, inside the firing pass, invisibly to the rest of the pass,
[EXEC-003]). Other transitions fire in between. Verification models that gap for every
transition whose output another transition tests with an inhibitor, reset or drain ([VER-004]).

**Depends on:** [ENV-003]
**Test derivation:** Trace execution of a simple net; verify step ordering via event log."#
