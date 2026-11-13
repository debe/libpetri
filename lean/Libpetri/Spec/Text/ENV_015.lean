import Libpetri.Spec.Text

requirement_text ENV_015
  id "ENV-015"
  title "Immediate Termination"
  priority MAY
  kind B
  body r#"⟦s1|An implementation MAY provide an immediate-termination operation (`terminateNow()`) that stops the
orchestrator loop **without** waiting for in-flight actions, unlike `close()` ([ENV-013]) which lets
them complete.⟧ After it is invoked:
1. ⟦s2|New `inject()` calls are rejected (return error / false), as after [ENV-013].⟧
2. ⟦s3|Queued external events are discarded (completed with false).⟧
3. ⟦s4|The loop stops at the end of its current cycle, or at the termination test of that cycle
   ([EXEC-040]) if it finds no action in flight there; it does NOT wait for in-flight actions, and
   their results are discarded rather than admitted to the marking.⟧
4. ⟦s5|In-flight actions keep running where the runtime cannot cancel them ([IO-013]); their consumed
   tokens are lost ([EXEC-031]).⟧

⟦s6|It is an explicit escape hatch and MUST NOT be invoked implicitly by `close()`.⟧

⟦s7|The executor is **stopped** from the moment `terminateNow()` takes effect.⟧ ⟦s8|The call takes effect
between two steps of the loop ([EXEC-001]): a call that lands while a step is under way takes
effect when that step ends.⟧ ⟦s9|The current cycle is the one under way when the call takes effect; it
ends where the next cycle would start, before its step 1.⟧ ⟦s10|If the termination test of the current
cycle ([EXEC-040]) finds no action in flight, the run ends there, as a closed run does ([ENV-013]),
and the firing pass of that cycle does not run.⟧ ⟦s11|A request that lands before the call
takes effect may still be accepted; its event is then discarded, and its admission completes with
`false` ([ENV-004]).⟧

⟦s12|*When* `terminateNow()` takes effect, the executor *shall* become stopped, *shall* discard every
external event still queued ([ENV-004]) and *shall* end a wait under way in step 6 ([CONC-010]).⟧
⟦s13|*When* `terminateNow()` takes effect, the executor *shall not* change the marking and *shall not*
move its loop to another step: the tokens that the firings in flight consumed stay consumed
([EXEC-031]), and the current cycle goes on.⟧

⟦s14|The executor *shall* become stopped only when `terminateNow()` takes effect, and once stopped it
*shall* stay stopped; `close()` *shall not* stop it ([ENV-013]).⟧

⟦s15|*While* the executor is stopped, *if* `inject()` is called, *then* it *shall* return an error or
`false` ([ENV-006]).⟧

⟦s16|*While* the executor is stopped, it *shall not* inject an external event into the marking.⟧

⟦s17|*While* the executor is stopped, it *shall not* process the outcome of a firing, except in the
firing pass of the current cycle, for a synchronous action that pass waits for ([EXEC-001]).⟧

⟦s18|*While* the executor is stopped and its loop is at the start of a cycle, it *shall not* take any
step of the loop other than ending the run (answering a snapshot request ([ENV-014]) is not a
step of the loop).⟧

⟦s19|*When* the executor is stopped and its loop reaches the start of a cycle, it *shall* end the run
without waiting for the actions still in flight.⟧

⟦s20|*When* a stopped executor ends its run, it *shall* return the marking it holds at that point
without restoring the tokens that the firings in flight consumed, and *shall* discard every
external event still queued ([ENV-004]); unless a terminal place is marked ([EXEC-042]), it *shall*
end the run only at the start of a cycle or at a termination test ([EXEC-040]) that finds no
action in flight.⟧

⟦s21|*While* the executor is stopped, no terminal place is marked and no action is in flight, it
*shall* take no step at a termination test ([EXEC-040]) other than ending its run.⟧

⟦s22|*While* the executor is stopped, it *shall not* deposit a batch that an action published
mid-action ([IO-015]), except to finish a step 1b that was under way when the call took effect.⟧

⟦s23|*While* the executor is stopped, it *shall not* end the firing pass of the current cycle while
transitions remain in its ready order: the pass still starts each of them that it can start
([EXEC-002], [TIME-014]).⟧

⟦s24|Which termination reason the run reports is [EXEC-041]'s.⟧ ⟦s25|Whether an action left running is
cancelled is the runtime's capability ([IO-013]); the executor never deposits its result.⟧

**Acceptance Criteria:**
1. `terminateNow()` stops the loop without awaiting an outstanding in-flight action.
2. The in-flight action's eventual output is not admitted to the marking.
3. `inject()` after `terminateNow()` returns error / false, does not hang.

**Depends on:** [ENV-013]
**Status:** Proposed
**Test derivation:** Start a net with a gated in-flight action; call `terminateNow()`; verify the loop
terminates without releasing the gate and the action's output never reaches the marking."#
