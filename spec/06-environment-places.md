# 06 — Environment Places

This document specifies external event injection via environment places, implicit long-running behavior, and executor lifecycle (drain/close).

---

## Environment Place Declaration

#### ENV-001: Environment Place Wrapper

**Priority:** MUST

An environment place is a marker wrapper around a regular place that designates it as an external event injection point. Tokens can be injected into environment places from outside the executor.

**Acceptance Criteria:**
1. An environment place wraps a regular place.
2. The underlying place's name and type are accessible.
3. Environment places are registered with the executor at construction time.

**Note (orthogonality with interface places):** Environment places (per this requirement) and interface places (ports per [MOD-003]) are **orthogonal concepts**. An environment place marks a *world boundary* — the seam where the engine accepts injections from outside the executor. An interface place marks a *composition boundary* — the seam where two net fragments are wired together at build time. A single underlying place MAY simultaneously be an environment place and a port: the resulting flat net (after composition per [MOD-020]) treats it as a regular place that the executor accepts injections into and that arcs from both fragments reference. Where this dual role is used (e.g., a subnet's input port is also the host's external event injection point), the environment-place registration applies after composition, on the post-composition place identity.

**Test derivation:** Create environment place wrapping place "UserInput"; verify name and type accessible.

---

#### ENV-002: Environment Place Registration

**Priority:** MUST
**Kind:** B

Environment places must be registered with the executor before execution begins. The executor maintains a set of registered environment places.

**Acceptance Criteria:**
1. Executor builder accepts environment place registrations.
2. Where inject takes an environment-place handle (Java, TypeScript), only registered environment places accept injections.
3. Where inject takes an environment-place handle (Java, TypeScript), attempting to inject into a non-environment place returns an error.
4. Where inject takes a place name (Rust, Python), the host injects only into registered environment places.

The set of registered environment places is fixed when the executor is built; no step of a run adds or removes one.

*Where* an executor's inject takes an environment-place handle (Java, TypeScript), *if* a caller injects into a place that is not a registered environment place, *then* the executor *shall* answer with an error, and *shall not* answer with a refusal even when it is draining, closed, stopped or finished.

*Where* an executor's inject takes an environment-place handle (Java, TypeScript), *if* a caller injects into a place that is not a registered environment place, *then* the executor *shall* leave its state unchanged: it *shall not* queue the token and *shall not* change the marking.

*Where* an executor's inject takes an environment-place handle (Java, TypeScript), the executor *shall* answer an injection into a place that is not a registered environment place with an error in every state of the run, before and after the run finishes.

*Where* an executor's inject takes an environment-place handle (Java, TypeScript), the executor *shall not* answer an injection into a registered environment place with an error, in any state of the run.

*Where* an executor's inject takes an environment-place handle (Java, TypeScript), *while* the run has not finished and the executor is not draining, closed or stopped, the executor *shall* accept an injection into a registered environment place.

An executor whose inject takes a place name (Rust, Python) deposits an injected token into the place the name resolves to, whether or not that place is registered; for it, registration decides only whether the run waits at quiescence ([ENV-010]) and which arcs the dead-arc report lists ([CORE-037]).

*Where* an executor's inject takes a place name (Rust, Python), the host *shall* inject only into registered environment places.

**Depends on:** [ENV-001]
**Test derivation:** Java, TypeScript: register 3 environment places; inject into registered one → success; inject into unregistered → error. Rust, Python: AC4 is an assumption on the host, and no executor test checks it.

---

## Token Injection

#### ENV-003: inject() Thread Safety

**Priority:** MUST
**Kind:** B

The inject operation is safe to call from any thread, task, or coroutine — not just the orchestrator thread. It enqueues the token for processing on the next orchestrator cycle.

*When* the executor accepts an `inject()` call, it *shall* append the event to the tail of its queue of accepted events, as a new entry under a fresh ticket that identifies the call, and *shall not* change the marking or any other part of its state, except that it moves its ticket supply on and wakes the orchestrator if it is waiting ([ENV-005]).

*When* the orchestrator injects an accepted event, it *shall* take the oldest entry of the queue, *shall* remove that entry from the queue, *shall* add its token at the tail of its place (glossary: Queue order) and *shall not* change any other place.

The executor *shall not* change its queue of accepted events in any other way than appending a newly accepted event, injecting the oldest entry, discarding entries once it is closed ([ENV-013]) or terminated immediately ([ENV-015]), and emptying the queue when the run ends ([EXEC-041]), so that it injects accepted events in the order it accepted them.

*When* the executor discards queued events or the run ends, the executor *shall* only remove entries from its queue of accepted events and *shall* keep the remaining entries in the order it accepted them.

The executor *shall not* move its ticket supply back, so that no two accepted calls share a ticket.

*When* the executor accepts an `inject()` call, the orchestrator *shall* inject its token before the run finishes, unless after accepting it the executor is closed ([ENV-013]), is terminated immediately ([ENV-015]) or stops because a terminal place is marked ([EXEC-042]).

*While* the orchestrator is in the external-events step of a cycle ([EXEC-001] step 2), no terminal place is marked, the executor is neither closed ([ENV-013]) nor terminated immediately ([ENV-015]) and its queue of accepted events is not empty, the orchestrator *shall* inject the oldest entry.

**Acceptance Criteria:**
1. inject() can be called from a different thread than the orchestrator.
2. Multiple concurrent inject() calls do not cause data races.
3. Injected tokens are eventually processed by the orchestrator, unless the executor is closed, terminated immediately or stops because a terminal place is marked before it processes them.

**Depends on:** [ENV-002], [ENV-013], [ENV-015], [CONC-010], [EXEC-001], [EXEC-041], [EXEC-042]
**Test derivation:** Spawn 10 threads; each injects a token; verify all 10 tokens processed.

---

#### ENV-004: inject() Completion Semantics

**Priority:** MUST
**Kind:** B

In Java and TypeScript the inject operation returns a future/promise that completes with true when the token has been added to the marking. In Rust and Python the return value indicates whether the injection was accepted; in Java and TypeScript the future's value indicates whether the token was injected.

In Java and TypeScript the future is the admission signal of the accepted event. The orchestrator completes it with true in the external-events step ([EXEC-001] step 2), when it adds the token to the marking. It completes it with false when it discards the event because the executor is closed or stopped ([ENV-013], [ENV-015]), or when the run ends with the event still queued ([EXEC-041], [EXEC-042]). A drain does not discard the events accepted before it: the orchestrator still injects them ([ENV-011]), unless close() is called or the run ends first. Each accepted event has an admission signal of its own: an injection into a place whose earlier event is still queued neither replaces that event nor merges with it ([ENV-003]). Rust and Python have no admission signal, and no later answer reports a discard ([ENV-006]).

*When* the executor accepts an injection request, it *shall* queue the event as a new event, apart from every event already queued.

*When* the executor completes the admission signal of an accepted event with true, it *shall*, in the same step, add the event's token at the tail of its place's queue and change no other part of the marking.

*If* the executor completes the admission signal of an accepted event with false, *then* it *shall* leave the marking unchanged in that step.

*If* a step leaves the executor open or draining and does not end the run, *then* the executor *shall not* complete the admission signal of an accepted event with false in that step.

The executor *shall* complete the admission signal of an accepted event at most once.

**Acceptance Criteria:**
1. Future completes with true/success when token is in marking.
2. Future completes with false/error if inject() is called while the executor is draining, closed or finished ([ENV-006]), or if the event is still queued when the executor closes or the run ends; an event queued before a drain is not completed with false while the executor drains, unless the run ends or close() is called.
3. The future completes at most once.

**Depends on:** [ENV-003], [ENV-013]
**Test derivation:** Inject token; await future; verify token in marking after future resolves.

---

#### ENV-005: inject() Wake-Up

**Priority:** MUST
**Kind:** T

Injecting a token wakes the orchestrator from idle immediately. The orchestrator does not need to wait for a timer or poll.

**Acceptance Criteria:**
1. Orchestrator is idle (no ready transitions).
2. External inject() call wakes orchestrator.
3. Token is processed promptly (within one cycle).

An injection is queued from the moment inject() accepts it ([ENV-003]) until it leaves the queue: the executor puts its token into the marking, or, once the executor is closed or stopped or the run has ended, discards it ([ENV-013], [ENV-015], [EXEC-042]).

Once the executor is closed, an event that Java or TypeScript still holds in its queue counts as discarded from the first external-events step or wait after the close, though its inject() is answered only when the loop ends ([ENV-013], [ENV-004]).

An injection that inject() accepts after the external-events step of a cycle has last read the queue counts as accepted after that step ends, and is left to the next cycle.

*While* an accepted injection is queued, the executor *shall not* block in its wait ([EXEC-001] step 6, [CONC-010]), neither at the end of a cycle nor again after it has answered something during the wait, such as a marking snapshot.

*When* inject() accepts a token, the executor *shall* end any block of its wait at once, without waiting for a timer.

*While* an accepted injection is queued and the executor is in its wait with no terminal place marked, the executor *shall* be able to leave the wait at once, by waking up or by taking a queued injection from the queue, without waiting for a timer.

*While* an accepted injection is queued, the executor *shall not* end the external-events step of a cycle and *shall not* start the enablement update of a cycle ([EXEC-001] steps 2 and 3).

Read with the definition of queued above, this means that a token accepted while the executor waits has left the queue before the enablement update of the cycle the wake-up starts, and is in the marking by then unless the run has closed, stopped or ended first; the earlier sentences mean that no timer or polling is needed to find it.

The requirement on the external-events step covers every injection queued during that step, not only those queued when it begins ([EXEC-001] step 2), so the step has no limit on how many injections it takes.

The words immediately, promptly and at once mean that nothing in the executor waits between the acceptance and the injection; the latency itself is tested, not proven.

Under a host clock an implementation may leave the wait to the host ([TIME-015]); the wait these sentences speak of is then the host's, and [TIME-015] requires its readiness predicate to observe the queued injection.

**Depends on:** [CONC-010], [ENV-003], [ENV-013], [ENV-015], [EXEC-001], [EXEC-042], [TIME-015]
**Test derivation:** Start executor with environment places; wait for quiescence; inject token; verify processing within milliseconds.

---

#### ENV-006: inject() Rejection on Closed or Draining Executor

**Priority:** MUST
**Kind:** B

If the executor has been closed, is draining, or execution has completed, inject() returns an error or false rather than silently dropping the token.

*If* `inject()` is called while the executor is draining, closed or stopped ([ENV-011], [ENV-013], [ENV-015]), or after the run has finished, *then* it *shall* return an error or `false`.

*If* `inject()` is called while the executor is draining, closed or stopped, or after the run has finished, *then* the executor *shall* change nothing: the token *shall not* reach the marking, and no event *shall* be queued for injection.

Each accepted injection *shall* stay an event of its own until it is injected, discarded or dropped: the executor *shall not* merge two accepted injections into one.

*Where* `inject()` returns an admission signal ([ENV-004]), *when* a run that accepted an injection finishes, the executor *shall* have completed the signal of that injection, with the value [ENV-004] gives: by injecting the token, by discarding the event on a close ([ENV-013]), by dropping it on an immediate termination ([ENV-015]), or by dropping it at the finish of the run while it is still queued.

A run whose terminal place ([EXEC-042]) is marked has not finished until the executor ends it: an injection accepted in between is dropped when the run ends, and its admission signal, where one exists, completes with `false`. TypeScript refuses such a call at once, which gives the caller the same `false`.

In Java, in TypeScript and in Python, which has one handle per executor, every injector shares the executor's lifecycle, so every injector is refused from the moment of the drain or the close. In Rust the drained flag belongs to the `ExecutorHandle`: a handle refuses once it has itself drained or closed the executor, and every handle refuses once the run has finished. An event that another sender injects after that drain or close is answered `true`, and the executor drops it on receipt without a report. The first two sentences above therefore hold in Rust for one injector per executor, and for every sender the token still never reaches the marking.

Rust and Python return no admission signal ([ENV-004]): their `inject()` reports acceptance only, so an accepted event that a stop on a terminal place ([EXEC-042]) drops is not reported. Their executor still injects, discards or drops every event it accepted by the time the run finishes; only the report to the caller is missing. A form of `inject()` without a result (TypeScript's `injectNoAwait`, Java's `injectAsync`) is outside this requirement: it reports nothing, and on a draining, closed or finished executor it drops the token without an answer.

**Acceptance Criteria:**
1. After executor closes, inject() returns error/false.
2. After drain(), inject() returns error/false.
3. Where an admission signal exists ([ENV-004]), every accepted injection completes it by the time the run finishes.

**Depends on:** [ENV-002], [ENV-004], [ENV-011], [ENV-013], [ENV-015], [EXEC-042]
**Test derivation:** Run executor to completion; call inject(); verify error returned. Call drain(); inject(); verify error returned.

---

## Implicit Long-Running Behavior

#### ENV-010: Implicit Long-Running Behavior

**Priority:** MUST
**Kind:** B

When environment places are registered with the executor, the executor does NOT terminate at quiescence (no transition armed, no firing in flight, and no completion, publication or external event queued, as in [EXEC-040]) while it has not been drained ([ENV-011]), closed ([ENV-013]) or stopped by an immediate termination ([ENV-015]) and no terminal place is marked ([EXEC-042]). Instead, it waits for external events that may enable new transitions. This behavior is derived from the presence of environment places: no explicit flag is needed.

When no environment places are registered, the executor terminates at quiescence per [EXEC-040].

A drain, a close, an immediate termination or a marked terminal place lets such an executor end ([ENV-011], [ENV-013], [ENV-015], [EXEC-042]). In Rust, an executor whose signal channel has closed (every sender dropped) accepts no injection and ends at quiescence as a drained one does; dropping an `ExecutorHandle` sends a drain first. Rust's `run_sync` has no signal channel, so it accepts no injection and ends at quiescence whatever is registered; it is outside this requirement. In Java, an interrupt taken while the loop waits ends the run as interrupted ([EXEC-041]).

*While* environment places are registered, the executor is open (it has not been drained, closed or stopped by an immediate termination) and no terminal place is marked ([EXEC-042]), the executor *shall not* terminate as quiescent ([EXEC-041]).

*While* environment places are registered, the executor is open and running and no terminal place is marked, *when* a caller asks to inject a token into a registered environment place, the executor *shall* answer the request and *shall* accept the injection.

*While* environment places are registered, the executor is open and no terminal place is marked, *when* the loop reaches its termination test ([EXEC-040]), the executor *shall* go on to its firing pass ([EXEC-001]).

*While* environment places are registered, the executor is open and no terminal place is marked, *when* an accepted injection is queued, the executor *shall* leave its wait ([ENV-005]) and *shall* inject the oldest queued injection in its event step ([ENV-003]).

The executor *shall not* need a long-running flag or any setting other than the registered environment places to wait at quiescence.

**Acceptance Criteria:**
1. Registering environment places causes executor to wait at quiescence instead of terminating.
2. No explicit long-running flag exists on the executor API.
3. Executor with environment places does not terminate at quiescence.
4. Executor without environment places terminates at quiescence.
5. Injecting a token resumes execution from quiescence.

**Depends on:** [ENV-001], [ENV-002], [ENV-003], [ENV-005], [EXEC-001], [EXEC-040], [EXEC-041], [EXEC-042], [TIME-010], [TIME-013]
**Test derivation:** Executor with environment places; all transitions fire; verify executor still running; inject token; verify new transition fires; drain executor; verify termination.

---

## Executor Lifecycle

#### ENV-011: Graceful Drain

**Priority:** MUST
**Kind:** B

The executor provides a `drain()` method that signals graceful shutdown. After `drain()` is called:
1. New `inject()` calls are rejected (return error/false).
2. Already-queued external events are processed normally.
3. In-flight actions are allowed to complete.
4. The executor terminates when quiescent (no armed transitions, no in-flight, no pending events).

Items 2 to 4 hold while no terminal place is marked: a marked terminal place stops the executor at once, abandoning the actions in flight and ending the run with the queued external events unapplied ([EXEC-042]).

For executors without environment places, a drain does not change when the executor terminates, since the executor already terminates at quiescence.

*When* an open executor is drained, it *shall* enter the draining mode and *shall* leave the rest of its state as it was, apart from waking its wait ([CONC-010]): its marking, its queued external events and its firings in flight stay as they were.

*If* an executor that is not open (draining, closed or stopped) is drained, *then* the drain *shall* change nothing.

*While* the executor is draining, *when* an injection is requested, the executor *shall* reject it (error or false) and *shall* change nothing.

*While* the executor is draining, it *shall not* discard a queued external event.

*While* the executor is draining, it *shall* take every step of its cycle as it takes it while open, with the same effect: it *shall* inject the queued external events, let the actions in flight complete, settle their outcomes and start ready transitions as an open executor does; only the answers to requests and snapshot requests ([ENV-014]), and the wait and the termination test of an executor with environment places at quiescence, differ. A close or an immediate termination of a draining executor is governed by [ENV-013] and [ENV-015].

*While* the executor is draining and no terminal place is marked, it *shall not* terminate except at the termination test of a cycle ([EXEC-001]) that finds it quiescent: no transition armed, no firing in flight, and no completion, publication or external event queued.

*While* the executor is draining and no terminal place is marked, *when* the termination test of a cycle finds it quiescent, the executor *shall* terminate.

*While* the executor is draining and quiescent, *when* it enters or ends its wait, it *shall* change nothing but the wait, and ending the wait *shall* take it to the first step of the next cycle.

*While* the executor is draining and quiescent and no terminal place is marked, it *shall* end its wait at once, without waiting for an arrival or a timer ([CONC-010]).

**Acceptance Criteria:**
1. `drain()` method is available on the executor.
2. After `drain()`, `inject()` returns error/false.
3. Already-queued events are processed before termination.
4. In-flight actions complete before termination.
5. Executor terminates when quiescent after drain.

**Depends on:** [ENV-010], [EXEC-001], [EXEC-040], [EXEC-042], [CONC-010]
**Test derivation:** Executor with env places; inject tokens; call drain(); verify queued events processed; verify new inject rejected; verify termination at quiescence.

---

#### ENV-012: Event-Driven Workflow Pattern

**Priority:** SHOULD

The engine supports event-driven workflow patterns where ~10 environment places represent external event sources (activity signals, data streams, tool requests, state changes, etc.) and the executor runs indefinitely, processing events as they arrive.

**Acceptance Criteria:**
1. 10+ environment places can be registered simultaneously.
2. Injection from multiple concurrent sources works correctly.
3. The net reacts to each injection by enabling relevant transitions.

**Depends on:** [ENV-001], [ENV-002], [ENV-010]
**Test derivation:** Build a net with 10 environment places; inject events from multiple sources; verify correct transition firing.

---

#### ENV-013: Immediate Close

**Priority:** MUST
**Kind:** B

The executor provides a `close()` method for immediate shutdown. After `close()` is called:
1. New `inject()` calls are rejected (return error/false).
2. Queued external events are not injected. Where `inject()` reports when its event is injected (Java, TypeScript), every event still queued at the close is discarded after it, never injected, and completed with false (at the latest when the loop ends). Rust and Python answer `inject()` when the event is queued, and the close travels the signal channel behind the events sent before it, so those events are injected before the executor takes the close.
3. In-flight actions are allowed to complete, unless a terminal place is marked ([EXEC-042]).
4. The executor terminates after in-flight actions complete, unless a terminal place is marked first ([EXEC-042]).

Calling `close()` after `drain()` escalates from graceful to immediate shutdown.

A close does not stop the firing pass. While an action is in flight, a closed executor keeps running its cycles and may start ready transitions, whose actions are then in flight too; it terminates at the first termination test ([EXEC-040]) that finds no action in flight. A close alone therefore does not bound a run whose firings overlap; an immediate termination ([ENV-015]) does. A run budget ([ENV-016]) bounds only the caller's wait. In Java and TypeScript an awaited `inject()` of an event still queued at the close is answered when the loop ends.

*When* the executor takes a close, it *shall* enter the closed mode and *shall* leave every part of its state other than its mode and whether its loop waits ([CONC-010]) as it was: the marking, the clock of every transition, the clock reading of the cycle, the actions in flight, the queued outcomes, publications and external events, the supply of identities, the phase of its loop and the rest of a firing pass.

*While* the executor is closed, it *shall* reject every `inject()` call, and a rejected call *shall* change nothing.

The executor *shall* enter the closed mode only when it takes a close, and *shall* leave it only for an immediate termination ([ENV-015]).

*While* the executor is closed, it *shall not* inject a queued external event.

*When* a closed executor ends its run, it *shall* leave no external event queued.

*While* the executor is closed and no terminal place is marked, it *shall* end its run only when no action is in flight, or on a cancellation it observes in its wait ([EXEC-041]).

*While* the executor is closed, no terminal place is marked and no action is in flight, it *shall* take no step at a termination test ([EXEC-040]) other than ending its run.

*While* the executor is closed, it *shall* remove an action from the actions in flight only by settling its outcome.

*While* the executor is closed, it *shall* end step 1b of a cycle ([EXEC-001]) only when no publication is queued.

**Acceptance Criteria:**
1. `close()` signals immediate shutdown.
2. No queued event is injected after the close; where `inject()` reports injection, each event still queued is completed with false (not processed).
3. In-flight actions complete before termination.
4. `inject()` returns error/false after close.

**Depends on:** [ENV-010], [ENV-004], [EXEC-040]
**Test derivation:** Executor with in-flight action; call close(); verify action completes; verify queued events discarded; verify executor terminates.

---

#### ENV-014: Mid-Execution Marking Snapshot

**Priority:** SHOULD
**Kind:** B

The executor exposes a `snapshot()` operation that returns a point-in-time copy of the current
marking **without affecting lifecycle** — unlike `drain()` ([ENV-011]) and `close()` ([ENV-013]),
it neither stops nor pauses execution. The request is serviced within one orchestrator cycle and
the returned marking is an owned, independent copy. This backs observation and checkpoint-saver
patterns (e.g. periodic external persistence of the marking) without interrupting the run.

**Observation is not a restore point.** A marking taken while any work is in flight is a valid
*observation* but is **not** sufficient to resume from. **Work in flight** means either of two
things: an **action** that has started and not completed, or an **external event the executor has
accepted but not yet injected** ([ENV-003], [ENV-004]). Three reasons, of different severity:

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

Consequently a snapshot offered as a restore point for [CORE-073] MUST be taken at a moment when
no work is in flight — no action, and no accepted external event still awaiting injection. An
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
exactly. A firing therefore counts as in flight **from the moment its inputs are consumed** — not
from the moment its action first suspends — so the window covers the action's synchronous prefix
and any event-store callback the firing triggers, and the indication MUST report work in flight
throughout it. Where actions are invoked inline on the orchestrator's own thread, such a request
additionally cannot be queued for the orchestrator to service, because the orchestrator *is* the
caller and would park waiting for itself — with no error, no timeout and nothing to indicate what
happened, the same self-deadlock [TIME-015] describes for an awaited `inject()`. An
implementation with that shape MUST detect the case and capture directly on the calling thread,
after whatever synchronisation of internal token storage any other marking read performs.

**The answer and its two readings.** An answer to `snapshot()` is either a rejection or a marking, and a marking either reports a restore point (no work in flight) or reports work in flight. A refusal of a restore-point snapshot while work is in flight reports work in flight; the rejection is reserved, while the run lasts, for an executor that has been drained, closed or terminated. An answer that reports a restore point describes the instant at which the executor captured it. An answer to a request the orchestrator could not serve reports work in flight and may describe an earlier instant of the same run, while a parked executor still answers with the current marking (AC9).

*When* the executor answers a `snapshot()` request, it *shall* leave its whole state as it was, among it the marking, the lifecycle, the firings in flight, the queued completions, publications and external events, the clocks of the transitions, and the orchestrator's place in its cycle, a wait it is parked in included ([CORE-071]).

*If* the executor has been drained or closed ([ENV-011], [ENV-013]), or terminated immediately ([ENV-015]), *then* it *shall* reject a `snapshot()` request.

*While* the executor is running and has been neither drained, closed nor terminated, it *shall not* reject a `snapshot()` request.

*If* a firing is in flight at the instant the executor captures the marking for a `snapshot()` answer, counted from the moment its inputs are consumed until the executor has processed its completion and deposited every token its action published ([IO-015]), *then* the executor *shall not* report that answer as a restore point.

*If* an external event that the executor accepted before a `snapshot()` request is still queued for injection at the instant the executor captures the marking for that request's answer, *then* the executor *shall not* report that answer as a restore point.

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
**Implementation status:** AC1–AC8 in all four. AC9 in all four:
- **Rust** races the clock's wait against its signal channel, so a request is served mid-wait
  (Python rides on it).
- **TypeScript** is single-threaded, so no read can overlap a wait.
- **Java** has a park epoch. The orchestrator bumps a volatile counter just before and just after
  each wait. A foreign reader that finds it parked copies the state directly, checks the counter
  again, and falls back to the request protocol below only if the orchestrator moved in between.

`snapshot()` returns a result carrying the marking
**and** an in-flight indication, read in the same operation that captures the marking — a
separately-queryable flag would be read at a different instant, which is the race AC5 closes. The
field keeps its name (`actionInFlight` / `action_in_flight`) and means **work in flight: an action,
or an accepted but un-injected external event**. **TypeScript** and **Java** read the marking
outside the event queue, so they OR a pending-external-queue check into the flag at the instant
of capture; **TypeScript** counts a firing as in flight from consumption, and **Java**, whose
actions run inline, captures directly when called on the orchestrator thread (the precompiled
executor synchronising its ring buffers first, as its `marking()` does) and reports the flag
true. A Java request from a *foreign* thread waits for the orchestrator to serve it, bounded by a
2 s best-effort cap so a caller is never parked behind a blocking inline action; a request that
was **not served** within the cap returns the last published marking with the flag **forced
true**, whatever flag that older marking was published with — since then an accepted event may
have been injected and consumed by the very firing that is blocking, so an unserved request is
never a restore point (AC7). Both Java executors compute the published flag with one shared
expression, and an event that will be *refused* — queued behind a run that has already
terminated or closed, so `inject` answers `false` and the host keeps the token — was never
accepted and does not count. **Rust** and **Python** need neither: injections and the snapshot request share one FIFO
channel, so every earlier injection is already in the marking when the snapshot is served, and a
request is a non-blocking send whose reply arrives from the orchestrator's next cycle — an
**asynchronous** action that awaits it is, correctly, reported in flight, from its first statement
as well as after it has suspended (in Python the awaitable binds to the loop `start_async` /
`run_async` captured, since an action's thread has no running loop). As with `inject()` under
[TIME-015], that reply MUST NOT be *blocked on* from the orchestrator's own thread of control,
and there are two such places: an `ExecutorClock` wait, and a **synchronous** action under
`run_async` / `start_async`, which runs inline in the orchestrator loop. Such an action may send
the request, but the orchestrator cannot serve it until the action returns, so blocking on the
reply hangs the run; and the reply, once it comes, describes the instant *after* that firing
settled — outputs deposited, no token missing, and therefore possibly a restore point. That is
AC8's deferred arm: in Rust and Python an asynchronous action gets the flagged result, and an
inline synchronous one gets the deferred one. Under `run_sync` there is no signal channel and the
case does not arise.

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
patience, since the failure mode is a self-deadlock.

---

#### ENV-015: Immediate Termination

**Priority:** MAY
**Kind:** B

An implementation MAY provide an immediate-termination operation (`terminateNow()`) that stops the
orchestrator loop **without** waiting for in-flight actions, unlike `close()` ([ENV-013]) which lets
them complete. After it is invoked:
1. New `inject()` calls are rejected (return error / false), as after [ENV-013].
2. Queued external events are discarded (completed with false).
3. The loop stops at the end of its current cycle; it does NOT wait for in-flight actions, and their
   results are discarded rather than admitted to the marking.
4. In-flight actions keep running where the runtime cannot cancel them ([IO-013]); their consumed
   tokens are lost ([EXEC-031]).

It is an explicit escape hatch and MUST NOT be invoked implicitly by `close()`.

The executor is **stopped** from the moment `terminateNow()` takes effect. The call takes effect
between two steps of the loop ([EXEC-001]): a call that lands while a step is under way takes
effect when that step ends. The current cycle is the one under way when the call takes effect; it
ends where the next cycle would start, before its step 1. A request that lands before the call
takes effect may still be accepted; its event is then discarded, and its admission completes with
`false` ([ENV-004]).

*When* `terminateNow()` takes effect, the executor *shall* become stopped, *shall* discard every
external event still queued ([ENV-004]) and *shall* end a wait under way in step 6 ([CONC-010]).
*When* `terminateNow()` takes effect, the executor *shall not* change the marking and *shall not*
move its loop to another step: the tokens that the firings in flight consumed stay consumed
([EXEC-031]), and the current cycle goes on.

The executor *shall* become stopped only when `terminateNow()` takes effect, and once stopped it
*shall* stay stopped; `close()` *shall not* stop it ([ENV-013]).

*While* the executor is stopped, *if* `inject()` is called, *then* it *shall* return an error or
`false` ([ENV-006]).

*While* the executor is stopped, it *shall not* inject an external event into the marking.

*While* the executor is stopped, it *shall not* process the outcome of a firing, except in the
firing pass of the current cycle, for a synchronous action that pass waits for ([EXEC-001]).

*While* the executor is stopped and its loop is at the start of a cycle, it *shall not* take any
step of the loop other than ending the run (answering a snapshot request ([ENV-014]) is not a
step of the loop).

*When* the executor is stopped and its loop reaches the start of a cycle, it *shall* end the run
without waiting for the actions still in flight.

*When* the executor ends a run because it is stopped, it *shall* end it at the start of a cycle,
*shall* return the marking it holds at that point without restoring the tokens that the firings in
flight consumed, and *shall* discard every external event still queued ([ENV-004]).

*While* the executor is stopped, it *shall not* deposit a batch that an action published
mid-action ([IO-015]), except to finish a step 1b that was under way when the call took effect.

*While* the executor is stopped, it *shall not* end the firing pass of the current cycle while
transitions remain in its ready order: the pass still starts each of them that it can start
([EXEC-002], [TIME-014]).

Which termination reason the run reports is [EXEC-041]'s. Whether an action left running is
cancelled is the runtime's capability ([IO-013]); the executor never deposits its result.

**Acceptance Criteria:**
1. `terminateNow()` stops the loop without awaiting an outstanding in-flight action.
2. The in-flight action's eventual output is not admitted to the marking.
3. `inject()` after `terminateNow()` returns error / false, does not hang.

**Depends on:** [ENV-013]
**Status:** Proposed
**Implementation status:** Java implemented; Rust/TypeScript/Python pending.
**Test derivation:** Start a net with a gated in-flight action; call `terminateNow()`; verify the loop
terminates without releasing the gate and the action's output never reaches the marking.

---

#### ENV-016: Observable Termination

**Priority:** MAY
**Kind:** B

An implementation MAY provide `awaitTermination(timeout)`, which blocks until the orchestrator loop
has finished its termination bookkeeping (pending `inject()` futures completed, `ExecutionCompleted`
emitted), returning whether termination was observed within the timeout. It returns promptly when the
loop was never started, and it MUST NOT itself be defeated by a failure in that bookkeeping (for
example a throwing event store).

Independently, run-with-timeout (`run(timeout)`, whose timeout is the caller's run budget named in
[EXEC-041]; its expiry fails the caller's wait and does not by itself end the run) MAY expose a
policy for what happens to the loop when the caller's timeout expires: *abandon* (leave the loop
running; the historical default, rarely desirable) or *close* (stop it per [ENV-013]). The expiry
of the caller's timeout MUST NOT complete the loop's own result: an abandoned loop can still report
its real final marking.

*Where* an implementation exposes this policy, *when* the caller's timeout expires while the loop is running, the implementation *shall* act on the expiry under the policy the caller chose.

*When* the caller's timeout expires under *abandon*, the implementation *shall* leave the executor as it was, including its marking, its lifecycle mode, its queues, its firings in flight and the position of its loop, and a running loop *shall* go on running.

*When* the caller's timeout expires under *close* while the executor is open or draining, the implementation *shall* close the executor as a call of `close()` does ([ENV-013]), even while its loop is running.

*When* the caller's timeout expires under *close* after the executor is already closed or stopped, the implementation *shall* leave the executor as it was.

*When* the caller's timeout expires while the loop is running, the implementation *shall not* end the run and *shall not* change the marking.

**Acceptance Criteria:**
1. `awaitTermination` returns false while the loop is still running, true once it has stopped.
2. `awaitTermination` returns promptly (true) if the loop was never started.
3. Under a *close* policy the executor is closed on timeout and the loop then stops as [ENV-013]
   says, once its in-flight actions complete; under *abandon* it keeps running.

**Depends on:** [ENV-013], [EXEC-041]
**Status:** Proposed
**Implementation status:** Java implemented. TypeScript implements the run-timeout policy
(`run(timeoutMs, onTimeout)`) but not `awaitTermination`; Rust/Python pending.
**Test derivation:** Run a net whose action is still in flight when a short timeout expires, under
each policy; verify that under *close* the executor is closed and the loop stops once the action
completes, that under *abandon* the loop stays live and reports the action's output in its final
marking, and that `awaitTermination` reports the transition.
