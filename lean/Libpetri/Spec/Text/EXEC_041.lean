import Libpetri.Spec.Text

requirement_text EXEC_041
  id "EXEC-041"
  title "Execution Result"
  priority MUST
  kind B
  body r#"⟦s1|When execution completes, the executor returns the final marking (token distribution across all places).⟧

⟦s2|**Termination cause MUST be observable.**⟧ The returned marking says what the net *holds*, not
whether the run *finished*. ⟦s3|An executor that can stop for any reason other than quiescence
([EXEC-040]) — a close ([ENV-013]), a caller's run budget, a host cancellation — MUST make that
reason distinguishable to the caller, by the return value, by a distinct event, or by a raised
error.⟧ ⟦s4|Emitting the same completion signal for a quiesced run and a truncated one is
non-conforming: a partial marking presented as final cannot be told apart from a net that had
nothing left to do, so every consumer that treats completion as proof the run finished — a durable
checkpoint, a workflow step, an assertion on the final marking — silently accepts the truncation.⟧

**Ambient host state is not a stop request.** An executor MUST NOT treat host state it did not
itself set — a thread's pre-existing cancellation or interrupt flag, for example — as a request to
stop. Such state is not a request from the caller of *this* run: it may have been left by earlier
work on a reused thread, or set by the run's own action code following the host language's
convention for propagating a cancellation it caught (in a runtime that invokes actions inline on
the orchestrator's own thread, that convention is indistinguishable from a stop). An executor that
consults it as a loop condition can execute zero cycles, or truncate mid-run, and report success in
both cases. A cancellation the executor observes *itself*, raised while it waits, MAY stop the run
— but only under the distinguishability rule above.

⟦s5|*When* the executor finishes a run, it *shall* make the marking the run ended with, unchanged by the finish, and the termination reason of the finish available to the caller.⟧

⟦s6|The executor *shall* end a run only by finishing it, never as a side effect of another step such as a close.⟧

⟦s7|*While* a run is finished, the executor *shall not* take another step of its loop (answering a snapshot request ([ENV-014]) reads the state and is not a step of the loop), and *shall not* change the returned marking or the termination reason.⟧

⟦s8|The executor *shall* report the termination reason `quiescent` only when nothing is armed, in flight or queued ([EXEC-040]), and `terminal` only when a terminal place is marked ([EXEC-042]).⟧

⟦s9|The executor *shall* report `closed` only after a close ([ENV-013]) or an immediate termination ([ENV-015]) was requested, and `stopped` only after an immediate termination, another caller-requested stop, or a fault of the host runtime that ends the run with a raised error ([EXEC-030]).⟧

⟦s10|At a rest the run reached after a close or an immediate termination, `quiescent` and `closed` both conform, and after an immediate termination `stopped` conforms too.⟧

⟦s11|A run budget that expires ends the caller's wait, not the loop: the executor reports a truncating reason to the caller (`stopped`, or a raised error), and a loop that the timeout policy leaves running has not finished, so its later steps and its finish are not steps after a finish.⟧

*Where* the runtime has a cancellation the executor observes in its own wait, the executor *may* finish the run on it, and *shall* then report `interrupted`, and *shall* report `interrupted` only after such a cancellation.

The executor *shall not* treat host cancellation state that it did not set itself, such as a thread's interrupt flag set before the run or by the run's own action code, as a request to stop the run.

Where the runtime exposes no ambient cancellation state an executor could consult, the previous sentence and AC4/AC5 hold vacuously.

**Acceptance Criteria:**
1. Return value contains the token state after quiescence.
2. All places with tokens are represented.
3. A run that stops before quiescence is distinguishable by the caller from one that reached
   quiescence.
4. Ambient host cancellation state present *before* the run begins neither prevents the run from
   executing nor causes it to report completion having fired nothing.
5. Action code that sets the host's cancellation flag while running — the conventional way to
   propagate a caught cancellation — does not truncate the run.

**Depends on:** [EXEC-040], [ENV-013], [ENV-015]
**Test derivation:** Run net; inspect returned marking; verify expected token distribution. For
AC4, set the host's cancellation flag immediately before `run()` and assert the net still executes
to quiescence. For AC5, have an action set that flag mid-run and assert every downstream transition
still fires. For AC3, stop a run early and assert the caller can tell it apart from a quiesced one.
The AC4 and AC5 nets MUST actually reach a wait — an asynchronous action, a delayed transition —
because an all-synchronous chain never enters one and passes whether or not the flag is handled.
To test that a *real* cancellation still stops the run, raise it from a foreign thread while the
orchestrator is parked in the wait, not from an action — and do so under a host-supplied wait
([TIME-015]) as well as the built-in one, since the two report the interrupt differently.

**Termination reasons.** ⟦s12|Where an implementation exposes the reason as a value, the values are:
`quiescent` ([EXEC-040]), `terminal` ([EXEC-042]), `closed` ([ENV-013]), `stopped` (a run budget,
another caller-requested stop, or a host fault that ends the run with a raised error) and
`interrupted` (a cancellation observed in the wait, where the runtime has one).⟧ ⟦s13|`quiescent` and
`terminal` are the two **completed** reasons: the returned marking is the one the net was designed
to end in.⟧ ⟦s14|The others are truncations.⟧"#
