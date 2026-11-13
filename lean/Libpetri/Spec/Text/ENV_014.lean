import Libpetri.Spec.Text

requirement_text ENV_014
  id "ENV-014"
  title "Mid-Execution Marking Snapshot"
  priority SHOULD
  kind B
  body r#"⟦s1|The executor exposes a `snapshot()` operation that returns a point-in-time copy of the current
marking **without affecting lifecycle** — unlike `drain()` ([ENV-011]) and `close()` ([ENV-013]),
it neither stops nor pauses execution.⟧ The request is serviced within one orchestrator cycle and
the returned marking is an owned, independent copy. This backs observation and checkpoint-saver
patterns (e.g. periodic external persistence of the marking) without interrupting the run.

**Observation is not a restore point.** A marking taken while any work is in flight is a valid
*observation* but is **not** sufficient to resume from. ⟦s2|**Work in flight** means either of two
things: an **action** that has started and not completed, or an **external event the executor has
accepted but not yet injected** ([ENV-003], [ENV-004]).⟧ Three reasons, of different severity:

1. A firing whose action is in flight has already consumed its inputs ([EXEC-031], no rollback)
   and has not yet deposited its outputs. The snapshot captures neither, so those tokens are
   simply absent from it.
2. More fundamentally, the correspondence between an in-flight action and the **external work it
   started** — a remote call, a task handle, a cancellation scope — has no representation in the
   marking at all. A snapshot can therefore restore every token faithfully and still resume a net
   that has forgotten it has work outstanding. No amount of fidelity in the marking closes this;
   it is outside the marking by construction.
3. An accepted external event is the same conservation gap from the other side. The host has
   handed the token over — `inject()` returned, or was never going to be awaited ([TIME-015]'s
   admission rule forbids awaiting it from inside a host wait) — and the executor has not yet
   reached the external-events phase that places it ([EXEC-001] step 2). The token is in neither
   the host's hands nor the marking. A host that persists such a snapshot as a restore point and
   shuts down has lost it, and nothing in the snapshot says so.

⟦s3|Consequently a snapshot offered as a restore point for [CORE-073] MUST be taken at a moment when
no work is in flight — no action, and no accepted external event still awaiting injection.⟧ An
implementation MUST make that condition visible to the caller rather than leaving it implicit:
either by refusing a restore-point snapshot while work is in flight, by reporting alongside the
returned marking whether it was taken with none, or by offering a mode that defers servicing
until the executor next reaches that state. Which of the three is an implementation choice;
silently returning a marking the caller cannot tell is unusable for restore is not. Whichever is
chosen MUST cover **both** kinds of work and MUST be decided at the same instant the marking is
captured: an indication computed from the actions alone reports a restore point across exactly
the gap in (3).

**Two conforming shapes for the pending-event half.** An implementation whose `snapshot()` reads
the marking without passing through the orchestrator's event queue MUST fold "an accepted event
is still queued" into its indication. An implementation whose snapshot request travels the *same
ordered channel* as injections serves every injection accepted before it first, so at the moment
the marking is captured no earlier-accepted event can still be pending: it conforms by
construction, with the token **in** the marking rather than flagged. The two differ in what the
snapshot contains and agree on the property that matters — a token the executor has accepted is
never absent from a snapshot that reports itself a restore point.

**A snapshot requested from inside an action is a snapshot with work in flight.** The firing that
is running the caller has consumed its inputs and not deposited its outputs, which is reason (1)
exactly. ⟦s4|A firing therefore counts as in flight **from the moment its inputs are consumed** — not
from the moment its action first suspends — so the window covers the action's synchronous prefix
and any event-store callback the firing triggers, and the indication MUST report work in flight
throughout it.⟧ Where actions are invoked inline on the orchestrator's own thread, such a request
additionally cannot be queued for the orchestrator to service, because the orchestrator *is* the
caller and would park waiting for itself — with no error, no timeout and nothing to indicate what
happened, the same self-deadlock [TIME-015] describes for an awaited `inject()`. An
implementation with that shape MUST detect the case and capture directly on the calling thread,
after whatever synchronisation of internal token storage any other marking read performs.

⟦s5|**The answer and its two readings.** An answer to `snapshot()` is either a rejection or a marking, and a marking either reports a restore point (no work in flight) or reports work in flight.⟧ ⟦s6|A refusal of a restore-point snapshot while work is in flight reports work in flight; the rejection is reserved, while the run lasts, for an executor that has been drained, closed or terminated.⟧ ⟦s7|An answer that reports a restore point describes the instant at which the executor captured it.⟧ ⟦s8|An answer to a request the orchestrator could not serve reports work in flight and may describe an earlier instant of the same run, while a parked executor still answers with the current marking (AC9).⟧

⟦s9|*When* the executor answers a `snapshot()` request, it *shall* leave its whole state as it was, among it the marking, the lifecycle, the firings in flight, the queued completions, publications and external events, the clocks of the transitions, and the orchestrator's place in its cycle, a wait it is parked in included ([CORE-071]).⟧

⟦s10|*If* the executor has been drained or closed ([ENV-011], [ENV-013]), or terminated immediately ([ENV-015]), *then* it *shall* reject a `snapshot()` request.⟧

⟦s11|*While* the executor is running and has been neither drained, closed nor terminated, it *shall not* reject a `snapshot()` request.⟧

⟦s12|*If* a firing is in flight at the instant the executor captures the marking for a `snapshot()` answer, counted from the moment its inputs are consumed until the executor has processed its completion and deposited every token its action published ([IO-015]), *then* the executor *shall not* report that answer as a restore point.⟧

⟦s13|*If* an external event that the executor accepted before a `snapshot()` request is still queued for injection at the instant the executor captures the marking for that request's answer, *then* the executor *shall not* report that answer as a restore point.⟧

**Acceptance Criteria:**
1. `snapshot()` may be called at any time while the executor is running and has been neither drained, closed nor terminated.
2. The executor services the request within one orchestrator cycle and keeps running afterwards.
3. The returned marking is an owned copy, independent of subsequent executor state.
4. `snapshot()` is rejected (error / `None`) once the executor has been drained, closed or terminated.
5. A snapshot taken while an action is in flight is distinguishable by the caller from one taken
   with none in flight — by refusal, by an accompanying indication, or by the operation having
   waited for quiescence.
6. A net whose only marked place feeds a transition with an in-flight action yields a snapshot in
   which those consumed tokens are absent, and the caller can determine that the snapshot is not
   a valid restore point.
7. **An accepted event is never silently absent.** A snapshot requested after an external event
   has been accepted and before it has been injected either contains that event's token or is
   distinguishable as not a valid restore point. It never omits the token while reporting one.
8. **From inside an action.** `snapshot()` requested by a running action — from its synchronous
   prefix as well as after it has suspended — does not park the orchestrator against itself. Its
   result is either distinguishable as not a valid restore point, or **deferred until that firing
   has settled**, in which case it describes the settled instant — outputs deposited, no token
   missing — and may truthfully be a restore point. What it MUST NOT be is a result that omits the
   firing's consumed inputs *and* reports a restore point. An implementation that defers MUST NOT
   be blocked on from the orchestrator's own thread of control, since the reply cannot arrive until
   the action returns.
9. **A parked executor answers without waking.** A foreign read (`marking()` or `snapshot()`)
   of an executor whose orchestrator is parked in its wait — the built-in wait or a host's
   ([TIME-015]) — MUST be answered without the orchestrator's participation, and MUST return the
   current marking, not an earlier published one. A host that holds a lock the orchestrator needs
   in order to return from its wait (a deterministic workflow runtime answering a query, for
   example) otherwise gets a stale marking after a real-time delay. The work-in-flight indication
   of AC5–AC7 is computed as for any other capture.

**Depends on:** [ENV-003], [ENV-004], [ENV-010], [ENV-011], [ENV-013], [ENV-015], [EXEC-001], [EXEC-031], [EXEC-040], [CORE-071], [CORE-073],
[TIME-015]
**Test derivation:** Start a long-running net; call `snapshot()` mid-execution; verify the returned
marking reflects current state and the executor continues; call after `close()` and verify rejection.
For AC5/AC6, gate a transition's action open, snapshot while it is in flight, and assert the caller
can tell the result apart from a snapshot taken at quiescence — then release the gate, snapshot
again at quiescence, and assert that one restores to an equivalent marking per [CORE-073]. For
AC7, inject without awaiting admission and snapshot in the same turn; assert the token is present
or the result is flagged, on every executor. Where a foreign caller's wait for the orchestrator
is bounded, also hold an inline action past that bound with an accepted event already consumed by
it, and assert the unserved result is flagged. For AC8, call `snapshot()` from an action's first
synchronous statement and assert it returns flagged; bound the test by the call returning, not by
patience, since the failure mode is a self-deadlock."#
