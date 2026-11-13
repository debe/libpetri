# 04 — Execution Model

This document specifies the orchestrator loop, scheduling, token consumption, output validation, failure handling, and quiescence detection.

---

## Orchestrator Loop

#### EXEC-001: Orchestrator Loop Steps

**Priority:** MUST
**Kind:** B

The executor runs a loop with the following steps, in order:

1. **Process completions**: collect outputs from actions that have finished; validate against output specs; deposit produced tokens into marking; emit events.
2. **Process external events**: dequeue and apply externally injected tokens (see [ENV-003]).
3. **Update enablement**: re-evaluate which transitions are enabled based on current marking. Only transitions affected by token changes need re-evaluation (see [CONC-005]).
4. **Enforce deadlines**: reap every armed reapable transition (`Deadline` / `Window`) whose elapsed time is strictly greater than its latest bound plus the deadline tolerance ([TIME-013]). `Exact` transitions are never reaped ([TIME-006]).
5. **Fire ready transitions**: among ready transitions (armed, past their earliest bound and not expired), sort by priority (then FIFO), and fire in order.
6. **Await work**: wait for a completion, a publication, an external event, a drain or close request, or a timer. The loop may wait while actions are in flight, but only if nothing was deposited and no transition with an input or reset arc started since the enablement update, and it must wake on each of these ([CONC-010]).

Between steps 1 and 2, Rust and Python deposit the queued mid-action publications ([IO-015]). A publication is a deposit outside a firing pass, as are the deposits of steps 1 and 2.

A cycle begins when the loop leaves the firing pass or the wait for another step; in the order above that step is step 1. The steps run in this order in every cycle, with two exceptions. The wait of step 6 may itself process the completion, publication or external event that ends it, before the next cycle begins ([ENV-003]). A synchronous action's completion may be admitted inside its own firing pass, after its start ([EXEC-003]).

Two further points about the cycle are checked by other requirements, not by this one. The termination test of [EXEC-040] is made after step 4 and before step 5. Steps 3 to 5 may each take their own reading of the firing clock; each reading is no earlier than the one before, and steps 4 and 5 and the decision to wait judge expiry and readiness at the reading of step 4 ([TIME-013], [CONC-010]).

*When* the executor begins a cycle or deposits tokens outside a firing pass, it *shall not* run a deadline step until it has run an enablement update.

*When* the executor begins a cycle or deposits tokens outside a firing pass, it *shall not* start a transition until it has run a deadline step.

*When* the executor begins a cycle, it *shall not* run an enablement update until it has ended step 2.

*When* the executor begins a cycle or enters step 1, it *shall not* deposit a publication, inject an external event or start a transition until it has processed every finished action queued at that moment, whether the action completed, failed or timed out.

*When* the executor enters step 2 of a cycle while it is neither closed nor terminated immediately, it *shall not* run the next enablement update until it has injected or discarded every external event queued at that moment ([ENV-003], [ENV-013], [ENV-015]).

*If* the deadline step of a cycle reaps a transition, *then* the executor *shall not* start that transition before its next enablement update.

*When* the executor starts a transition that has an input or reset arc, or deposits tokens outside a firing pass or inside a firing pass that has started a transition, it *shall not* wait for work until it has run an enablement update.

*When* the executor runs an enablement update, it *shall* leave every transition whose enablement check fails without a clock, and every transition whose enablement check passes armed or reaped unless the executor is not re-entrant and a firing of that transition is in flight ([CONC-002], [NU-020]).

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

**Test derivation:** Trace execution of a simple net; verify step ordering via event log.

---

## Scheduling

#### EXEC-002: Priority-Based Firing Order

**Priority:** MUST
**Kind:** F

When multiple transitions are ready to fire (armed, past their earliest bound and not expired; see the glossary), they are sorted by:
1. **Priority**, descending: a higher priority fires first.
2. **Stamp**, ascending (FIFO): among equal priority, the transition armed first fires first ([TIME-010]).
3. **Declaration order**, ascending: among equal priority and equal stamp, the transition declared first fires first.

The ready order of a firing pass *shall* hold every ready transition exactly once and no other transition.

*Where* the net does not take the all-immediate fast path, the ready order *shall* offer a ready transition of higher priority before a ready transition of lower priority.

*Where* the net does not take the all-immediate fast path, the ready order *shall* offer, among ready transitions of equal priority, the one with the earlier stamp first.

The ready order *shall* offer, among ready transitions of equal priority and equal stamp, the earlier-declared one first.

*When* a firing pass starts transitions, the executor *shall* start only transitions of the ready order of that pass, in the order in which that order offers them.

*When* an enablement update newly arms several transitions, a restarted transition included ([TIME-012]), it *shall* give all of them one and the same stamp.

**All-immediate fast path.** When every transition is `Immediate` and all priorities are equal, backends fire straight from the enablement bitmap in ascending declaration order and do not read the enablement timestamp at all — including when two ready transitions carry different timestamps because one was held across cycles while in flight. This is deliberate, and every backend takes the path under the same condition. The sort above describes the general path.

**Acceptance Criteria:**
1. Transition with priority 10 fires before transition with priority 5.
2. Two transitions with equal priority on the general path: the one armed first (the earlier
   stamp) fires first.
3. Equal priority **and** equal stamp (transitions newly armed by the enablement update of
   the same orchestrator cycle share one stamp, [TIME-010]): the tie breaks by ascending
   declaration order, so the order is fully deterministic.
4. Every executor backend produces the **identical** ready order for the same net
   and marking. Stamp order is the general-path order; on the
   all-immediate single-priority fast path every backend fires in declaration
   order instead. Backends MUST NOT differ in which order they use, nor in the
   condition that selects it.

**Depends on:** [TIME-010]
**Test derivation:** Three transitions with priorities 5, 10, 5; enable all simultaneously; verify firing order: P10, then P5 (first enabled), then P5 (second enabled). For AC4, on a net that takes the general path (two priority levels, or one non-`Immediate` transition), enable two equal-priority transitions in different cycles with declaration order opposite to enablement order and verify every backend follows enablement order; on an all-immediate single-priority net, verify every backend fires in declaration order.

---

#### EXEC-003: Competitive Conflict Resolution

**Priority:** MUST
**Kind:** B

When multiple transitions compete for the same input tokens, the highest-priority ready transition fires first and consumes the tokens. Lower-priority transitions become disabled if their inputs are no longer satisfied.

A firing pass takes the transitions of its ready order ([EXEC-002]) one at a time from the front: it starts the next transition, or it drops it and goes on with the rest. The pass-visible marking is the marking a firing pass began with, minus the tokens earlier firings of the same pass consumed or drained; tokens a synchronous action deposited during the pass are not part of it.

*When* a firing pass starts or drops a transition, the transition *shall* be the next one of the pass's ready order, and it *shall* leave that order.

*When* a firing pass starts a transition, the transition *shall* hold a clock and be enabled on the pass-visible marking, with input counts, read arcs and inhibitor arcs all judged on that marking.

*If* the next transition of a firing pass's ready order holds a clock and is enabled on the pass-visible marking, *then* the executor *shall not* drop it.

*When* a firing pass drops a transition, the transition *shall* lose its clock ([TIME-012]), and the marking *shall* stay unchanged.

*While* a firing pass is under way, its ready order *shall* change only when the pass starts or drops a transition.

*When* a firing pass ends, its ready order *shall* be empty, so a transition of the order that does not hold a clock or is not enabled on the pass-visible marking when it is next is dropped, loses its clock and does not start in that pass.

*When* a transition starts in a firing pass, it *shall* consume, drain and hand its action only tokens of the pass-visible marking, so a token a synchronous action deposited earlier in the same pass survives its `all()`, `atLeast(n)` and reset arcs and does not reach its action.

*While* a firing pass is under way, the executor *shall* change the pass-visible marking only by starting a transition, and *shall* keep every token deposited earlier in the pass, so a token a synchronous action deposits in the pass does not become part of the pass-visible marking.

*When* a firing pass begins, the executor *shall* keep the marking, and every token of the marking *shall* be part of the pass-visible marking of the new pass.

**Acceptance Criteria:**
1. Two transitions sharing input place P; T1 (P=10) and T2 (P=5); one token in P; T1 fires; T2 disabled.
2. If T1 is not ready (timing not satisfied), T2 may fire.
3. Whether a loser's inputs are "no longer satisfied" is judged against the marking
   as consumed by earlier firings in the same firing pass, but before any tokens
   their synchronous actions produced: T1 (higher priority) consumes a token T2
   needs and refills the place via its own output in the same pass; T2 remains
   disabled and may fire no earlier than the next cycle, since the enablement
   recheck of the pass does not count a same-pass deposit (see [EXEC-001]).
4. AC3 governs token **counts**, not only presence. A cardinality gate
   (`exactly(n)`, `atLeast(n)`) re-evaluated during the pass MUST NOT count tokens
   a same-pass synchronous action deposited, and a ν-correlated join whose
   correlated input place received such a deposit fires no earlier than the next
   cycle. AC3 governs inhibitor arcs as well: inside a firing pass, the marking a
   transition fires from in the sense of [CORE-022] is the pass-visible marking, so a
   same-pass deposit into an inhibitor place does not block a transition later in
   the same pass. Deposits become visible to the enablement recheck and to
   consumption at the next cycle, never part-way through a pass.
5. Invisibility extends to consumption, not just to the enablement test. A
   draining arc — `all()`, `atLeast(n)`, or a reset arc — that fires later in the
   same pass takes only the tokens that were present when the pass began, as
   consumed by earlier firings; tokens a same-pass action deposited survive it and
   remain for the next cycle. Deposits land at the tail of each place's FIFO
   queue ([EXEC-010]), so this is the prefix of length `available - deposited`.
   Without this, a gate that correctly refused to *count* a same-pass deposit
   would still *swallow* it.

So a pass behaves as if every firing in it started before any of them deposited: a drain later
in the pass sees a place emptier than any one-at-a-time order leaves it. Verification reads a
firing whose output is drained, reset or inhibited as two steps for that reason ([VER-004]).

**Depends on:** [EXEC-001], [EXEC-002], [EXEC-010], [CORE-022]
**Test derivation:** Two competing transitions; verify only highest priority fires when only 1 token available.

---

## Token Consumption

#### EXEC-010: FIFO Token Consumption

**Priority:** MUST
**Kind:** B

When a transition fires, it consumes tokens from the oldest-first (FIFO) end of each input place's queue. The number of tokens consumed is determined by the input cardinality's `consumptionCount(available)`.

*When* a transition fires, it *shall* consume from each of its input places that is not a correlated input of its match specification ([NU-020]) the oldest tokens the place holds, as many as the consumption count of the input arc.

*When* a transition fires, its action *shall* receive the tokens consumed from each input place that is not a correlated input of its match specification in queue order, the oldest first.

*When* a transition fires, its action *shall* receive consumed tokens only from the input places of the transition.

A correlated input of a ν-net match specification is the one exception to oldest-first consumption: it takes the matched tokens of the chosen name, oldest first among the tokens of that name, so it can pass over an older token of another name ([NU-020]). Its non-correlated inputs consume as above.

*When* a transition starts in a firing pass, it *shall* remove from each of its input places that is neither a reset place nor a correlated input of its match specification the oldest tokens the place holds, as many as the consumption count of the input arc counted on the pass-visible marking ([EXEC-003]).

*When* a transition starts in a firing pass, its action *shall* receive from each of its input places that is not a correlated input of its match specification the oldest tokens the place holds, as many as that consumption count, in queue order.

**Acceptance Criteria:**
1. Tokens added in order A, B, C; One consumes A.
2. Exactly(2) consumes A, B.
3. All consumes A, B, C.

**Depends on:** [CORE-013], [IO-007], [NU-020]
**Test derivation:** Add tokens with identifiable values; fire transition; verify consumed tokens match FIFO order.

---

#### EXEC-011: ~~Guarded Token Consumption~~ (Removed)

**Status:** Removed

Guarded consumption was removed together with the guard predicate itself (see
[IO-006]). With no per-token value predicate in the input specification, token
selection is purely positional: [EXEC-010] (FIFO order) and [IO-007]
(`consumptionCount`) fully determine which tokens a firing consumes. The one
remaining per-token selection rule is the ν-name correlation of [NU-020], which is
specified there and is structural, not a value predicate.

Retained as a tombstone for traceability; excluded from the active requirement count.

---

#### EXEC-012: Read Arc Peek

**Priority:** MUST
**Kind:** B

When a transition fires, read arc values are provided to the action without consuming the tokens. The oldest token in the read place is peeked.

*When* a transition fires, its action *shall* receive, for each of its read places, the oldest token the place holds.

*When* a transition fires, its action *shall* receive read tokens only from the read places of the transition.

*When* a transition fires, each of its read places that is not one of its reset places *shall* end the firing holding the tokens it held before the firing, in the same queue order, followed by the tokens the firing deposits there.

*If* a transition declares an input arc and a read arc on the same place, *then* building the transition *shall* fail with

```
Transition '<t>' declares an input arc and a read arc on place '<p>'. A read of a place the same firing consumes from has no coherent semantics and is rejected (EXEC-012). Remove the read arc: the input arc already hands the consumed tokens to the action.
```

The message is the same, byte for byte, in every implementation. The read would peek the place after the firing's own consumption ([EXEC-013] AC4), which can leave it empty although the transition was enabled, so no reading of the pair is coherent. "The same place" is the implementation's own `Place` equality, as for [CORE-030] ([CORE-002]; name-and-type in Java, name-only in TypeScript and Rust).

The check runs when the transition is built, on every construction path, as the check of [CORE-030] does: the transitions that channel composition merges ([MOD-021]), that instantiation rewrites onto host places ([MOD-020]) and that fusion rewrites when the net is built ([MOD-061]) all pass through the transition builder. It runs after every input-arc check ([CORE-030], [IO-002], [IO-004]) and before the timing check ([TIME-001]) and the output-spec checks ([IO-011]–[IO-014]). It walks the read arcs in declaration order and names the place of the first read arc whose place is an input place of the transition.

**Acceptance Criteria:**
1. Read place has tokens A, B; action receives A; both A and B remain after firing.
2. A transition `t` with a `one()` input arc on `p` and a read arc on `p` → building `t` fails with the message above, `<t>` = `t` and `<p>` = `p`. With `all()`, `exactly(2)` or `atLeast(1)` in place of `one()` it fails the same way.
3. A transition `t` with input arcs on `a` and `b` and read arcs declared on `b`, then `a` → the message names `b`. A transition with two input arcs on `p` and a read arc on `p` → the [CORE-030] message, not this one.
4. A transition with an input arc on `a` and a read arc on `b`, or a read arc and a reset arc on the same place, builds.

**Depends on:** [CORE-032], [CORE-030]
**Test derivation:** Read place with 2 tokens; fire transition; verify both tokens remain; verify action received first. Build each rejected transition of AC2 and AC3 and verify the exact message; build each transition of AC4 and verify it builds.

---

#### EXEC-013: Reset Arc Execution

**Priority:** MUST
**Kind:** B

When a transition fires, all tokens are removed from each reset place. This happens during the firing step, before the action executes. Like input consumption, the drain lands in the intermediate marking, so it restarts the clocks of transitions it disables there (see [TIME-012]).

*When* a transition fires, it *shall* drain each of its reset places ([CORE-034]) before its action starts.

*When* a transition fires, it *shall* consume from its input places first, then peek its read places, then drain its reset places.

*When* a transition with a read arc and a reset arc on the same place fires, its action *shall* receive as the read token the oldest token the place held before the drain.

*If* a reset place of a firing transition is unmarked, *then* the drain *shall* remove nothing and the firing *shall* proceed.

A token a synchronous action deposited earlier in the same firing pass survives the drain ([EXEC-003] AC5).

*When* a transition starts in a firing pass, it *shall* drain each of its reset places in that same step, so the place keeps exactly the tokens a synchronous action deposited there earlier in the pass.

**Acceptance Criteria:**
1. Reset place with 5 tokens → all removed.
2. Reset place empty → no error.
3. If the reset place is also an input or read place of another enabled transition, that transition's clock restarts ([TIME-012]).
4. Reset draining occurs **after** read-arc peeking within the same firing: a
   transition with a read arc and a reset arc on the same place observes the
   pre-reset front token via `ctx.read()` (see [EXEC-012], [CORE-032]). The
   overall in-firing order is: input consumption, then read peeks, then reset
   draining.

**Depends on:** [CORE-034], [EXEC-012], [CORE-032], [EXEC-003]
**Test derivation:** Transition with reset on place with 3 tokens; verify all removed; verify clock restart for affected transitions.

---

## Output Handling

#### EXEC-020: Output Token Deposition

**Priority:** MUST
**Kind:** B

After an action completes and the executor admits the completion, the executor deposits produced tokens into the marking according to the output specification, unless output validation rejects them ([EXEC-021]). Each token is added to the end of the target place's FIFO queue, in the order the action produced it.

A completion is an action that returned normally; an action that throws or returns an error fails instead ([EXEC-030]). The executor **admits** a completion when it processes it: in step 1 of a cycle, or inside the firing pass for a synchronous action ([EXEC-001]). It never admits the completion of a firing that ended with its timeout outcome ([EXEC-022], [IO-013]), that a stop on a terminal place abandoned ([EXEC-042]) or that an immediate termination abandoned ([ENV-015]). A close ([ENV-013]) waits for in-flight actions and admits their completions.

*When* the executor admits the completion of an action and output validation does not reject the produced tokens ([EXEC-021], [CONC-026]), the executor *shall* add each produced token at the tail of its place's queue, in the order the action produced the tokens.

*If* the completion of an action is not admitted, or output validation rejects the produced tokens, *then* the executor *shall not* deposit any token the action produced at completion.

Tokens an action published before it completed ([IO-015], mid-action publication) are deposited when the executor processes the publication, which can be after the completion's own tokens. They are not deposited again, and once deposited they stay in the marking, whatever happens to the completion. A publication still queued when a terminal place stops the run ([EXEC-042]) is discarded.

*When* the executor deposits the tokens an action produced at completion, it *shall* do so only in the step that admits that completion, while the run is under way and no terminal place is marked, and *shall* add them at the tails of their places' queues in the order the action produced them.

The executor *shall* change the marking only when it starts a transition, deposits the tokens of an admitted completion, deposits a timeout outcome ([EXEC-022]), deposits a mid-action publication ([IO-015]) or injects an external event ([ENV-003]).

*When* a run has finished ([EXEC-041]), the executor *shall not* change the marking, so a completion, a timeout outcome or a publication that is still in flight or queued deposits nothing.

*When* the executor deposits the timeout outcome of a firing ([EXEC-022], [IO-013]), it *shall* do so only in a step in which a completion of that firing would be admitted, while the run is under way and no terminal place is marked, and *shall* add exactly the tokens of that outcome at the tails of their places' queues, in the order of the outcome.

**Acceptance Criteria:**
1. Action produces token with value V to place P; V appears at end of P's queue.
2. Multiple tokens to same place are added in order.
3. A completion that is not admitted (the firing ended with its timeout outcome, or a terminal place stopped the run while the action was in flight) deposits none of the action's tokens.
4. A completion whose produced tokens fail output validation deposits none of them ([EXEC-021]).

**Depends on:** [EXEC-021], [EXEC-022], [EXEC-042], [IO-015]
**Test derivation:** Action produces 3 tokens to P; verify all 3 appear in order. Action with a timeout budget that writes to P and then outlives the budget; verify P receives nothing from the action. Action that writes to a place outside its chosen output branch; verify nothing is deposited.

---

#### EXEC-021: Output Spec Validation

**Priority:** MUST
**Kind:** B

Before depositing tokens, the executor validates that the produced tokens satisfy the declared output specification (see [IO-015]). An executor with the validation skip of [CONC-026] enabled does not validate.

*When* an executor with output validation enabled admits the completion of an action, it *shall* validate the produced tokens against the transition's output spec ([IO-015]) before it deposits any of them.

*If* the produced tokens of an admitted completion fail output validation, *then* the executor *shall* deposit none of them and *shall* emit a TransitionFailed event ([EVT-008]).

*If* the produced tokens of an admitted completion fail output validation, *then* the executor *shall not* restore the tokens the firing consumed and *shall not* remove the tokens the action published before it completed ([IO-015]).

*When* an executor with output validation enabled validates the produced tokens of an admitted completion, it *shall* count the places of every batch the action published before it completed ([IO-015]) as produced, together with the places of the produced tokens.

*If* the produced tokens of an admitted completion pass output validation, *then* the executor *shall not* fail the firing.

The timeout outcome is not a completion of the action: [EXEC-022] and [IO-013] govern its deposit.

*When* a firing ends with its timeout outcome, the executor *shall not* validate the timeout outcome against the transition's output spec; the join-relay check of [NU-054] still runs on it.

**Acceptance Criteria:**
1. And: all children received tokens → valid.
2. Xor: exactly one child is selected; overlapping branches resolve without a tie-break, because [IO-015] requires the selected assignment's claim to *equal* the produced set, not merely be satisfied by it.
3. Violation → failure event emitted.
4. Validation is applied by every executor backend a language ships, not only the reference one.
5. Violation → the event is TransitionFailed, no produced token is deposited, the consumed tokens are not restored ([EXEC-030]), and tokens the action published mid-action stay in the marking.

**Depends on:** [IO-011], [IO-012], [IO-015], [EVT-008], [EXEC-030], [NU-054]
**Test derivation:** Xor output with tokens to 2 branches → violation event; verify neither branch place received a token.

---

#### EXEC-022: Action Timeout Handling

**Priority:** MUST
**Kind:** T

When a transition's output specification includes a Timeout node, the executor races the action against the timeout duration:
- Action completes first → normal output validation.
- Timeout fires first → the firing is abandoned (the action is stopped where the runtime can; see [IO-013]); the timeout child output receives tokens; ActionTimedOut event emitted.

The budget is host time: it elapses in real time, not on the firing clock ([TIME-015]). Only an action that hands control back to the executor before it completes races its budget; an action that completes before it hands control back, a synchronous action for example, never times out. When the action completes at the instant the budget runs out, either side may win.

*If* the output spec of a firing's transition has no `Timeout` node, or the action of the firing completed before it handed control back to the executor, *then* the executor *shall not* end the firing with its timeout outcome. *While* the budget of a firing has not elapsed, the executor *shall not* end the firing with its timeout outcome. *If* the action of a firing completes before the firing ends with its timeout outcome, *then* the executor *shall not* end the firing with its timeout outcome. *If* a firing has already ended, by the return of its action or by its budget running out, *then* the executor *shall not* change how it ended.

*When* the budget of a firing runs out before its action completes, the executor *shall* take as the timeout outcome the tokens of the `Timeout` child ([IO-013], [IO-014]): one minted token for each `Place` node, and for each `ForwardInput(from, to)` every token the firing consumed from `from`, in consumption order, each keeping its value and `created_at`. *When* the executor deposits the timeout outcome of a firing, it *shall* add exactly the tokens of that outcome, each at the tail of its place, and *shall not* deposit an outcome of that firing again or fail it afterwards.

*If* the budget of a firing runs out before its action completes, *then* the executor *shall not* deposit the completion of the action, and *shall not* deposit or publish any other output the action had not published before the budget ran out. Output the action published before the budget ran out stays in the marking ([EXEC-020], [IO-015]). The timeout outcome is not validated against the output spec, and the join-relay check of [NU-054] still runs on it ([EXEC-021]).

**Acceptance Criteria:**
1. Action completes in 50ms with 100ms timeout → normal completion.
2. An action that hands control back to the executor and takes 200ms, with a 100ms timeout → timeout branch activated; ActionTimedOut event.
3. ForwardInput in timeout child → **every** token consumed from the `from` place is forwarded to the `to` place, one output token per consumed token, in consumption order, each keeping its original `created_at` ([IO-014]).
4. Output the action wrote and had not published before the budget expired is discarded, not merged with the timeout branch ([IO-013] AC5); output it published before stays in the marking ([EXEC-020]).

**Depends on:** [IO-013], [IO-014], [EVT-010], [TIME-015], [EXEC-021], [NU-054]
**Test derivation:** Slow action with timeout; verify timeout branch tokens and event.

---

## Failure Handling

#### EXEC-030: Action Failure

**Priority:** MUST
**Kind:** B

If an action throws an exception or returns an error, the executor:
1. Emits a TransitionFailed event with error details.
2. Does NOT restore consumed input tokens (no rollback).
3. The transition is no longer in-flight.
4. Execution continues with remaining transitions.

A firing fails when its action throws an exception or returns an error, or when output validation or the join-relay check of [NU-054] rejects its outcome ([EXEC-021]).

*If* a firing fails, *then* the executor *shall* emit a TransitionFailed event ([EVT-008]) and *shall not* change the marking: it *shall not* restore the tokens the firing consumed and *shall not* deposit any token its action produced at completion.

*If* a firing fails, *then* the executor *shall* remove that firing from the firings in flight and its outcome from the queued outcomes, and *shall* leave every other firing in flight as it was and the other queued outcomes as they were, in the order they arrived.

*Where* an executor starts a transition again while an earlier firing of it is in flight ([CONC-002]), *if* one of those firings fails, *then* the executor *shall* leave the other firings of that transition in flight.

*If* a firing fails, *then* the executor *shall not* end the run and *shall not* change its lifecycle mode, and a failure inside a firing pass *shall* leave the pass to go on with its remaining transitions.

*If* a firing fails, *then* the executor *shall* leave the clock of every transition as it was, so that the next enablement update ([EXEC-001] step 3) evaluates the transition of the failed firing as it evaluates any other transition.

A fault of the host runtime itself is not an action failure: in Java, a `VirtualMachineError` or a `LinkageError` thrown inside a firing ends the run with that error, which [EXEC-041] requires the caller to be able to tell apart from quiescence.

**Acceptance Criteria:**
1. Failing action → TransitionFailed event with error message and type.
2. Consumed tokens are lost (not returned to input places).
3. Other transitions continue to fire.

**Depends on:** [EVT-008], [CONC-002], [NU-054]
**Test derivation:** Action throws; verify failure event; verify consumed tokens not restored; verify net continues.

---

#### EXEC-031: No Rollback

**Priority:** MUST
**Kind:** B

The engine does not provide transaction rollback. Once tokens are consumed by a firing transition, they are not restored if the action fails. This is a deliberate design choice — rollback would require complex compensation logic and conflicts with the async nature of actions.

A firing fails when its action throws or returns an error ([EXEC-030]), when its produced tokens fail output validation ([EXEC-021]), or when its produced tokens or its timeout outcome fail the join-relay check ([NU-054]).

*If* a firing fails, *then* the executor *shall not* restore the tokens the firing consumed.

*If* a firing fails, *then* the executor *shall not* later deposit a completion or a timeout outcome of that firing.

**Acceptance Criteria:**
1. Failed action → consumed tokens permanently removed.

**Depends on:** [EXEC-021], [EXEC-030], [NU-054]
**Test derivation:** Fire transition consuming token; action fails; verify token not in any place.

---

## Quiescence

#### EXEC-040: Standard Quiescence

**Priority:** MUST
**Kind:** B

When no environment places are registered and the net has no terminal places ([EXEC-042]), the executor terminates when ALL of the following hold at the termination test of a cycle, which follows the cycle's enablement update and deadline step ([EXEC-001]):
1. No transition is armed ([TIME-010]). A reaped transition that is still enabled holds no clock and does not keep the executor running ([TIME-013]).
2. No transitions are in-flight (executing actions). A firing counts as in flight until its completion and its queued publications are processed.
3. No external events are pending.

The final marking is returned.

The test is made there and nowhere else: straight after a deposit, before the next enablement update, a transition the deposit enabled is not yet armed ([TIME-010]), so the three conditions can hold while the net still has work to do.

*While* no terminal place is marked ([EXEC-042]), *when* the termination test of a cycle finds that no transition is armed, no firing is in flight and no completion, publication or external event is queued, an executor without environment places *shall* terminate and *shall* return the marking as it is.

An executor without environment places *shall not* terminate as quiescent ([EXEC-041]) anywhere in a cycle except at its termination test.

*When* an executor without environment places takes a step other than an enablement update or a deadline step, it *shall not* terminate as quiescent until it has run an enablement update.

*If* a transition is armed, a firing is in flight, or a completion, publication or external event is queued, *then* an executor without environment places *shall not* terminate as quiescent.

**Acceptance Criteria:**
1. Simple chain A→B→C: executor runs to completion; returns marking with token in C.
2. Parallel branches: waits for all in-flight actions before terminating.

**Test derivation:** Linear chain of 5 transitions; verify executor returns marking with token at end.

---

#### EXEC-041: Execution Result

**Priority:** MUST
**Kind:** B

When execution completes, the executor returns the final marking (token distribution across all places).

**Termination cause MUST be observable.** The returned marking says what the net *holds*, not
whether the run *finished*. An executor that can stop for any reason other than quiescence
([EXEC-040]) — a close ([ENV-013]), a caller's run budget, a host cancellation — MUST make that
reason distinguishable to the caller, by the return value, by a distinct event, or by a raised
error. Emitting the same completion signal for a quiesced run and a truncated one is
non-conforming: a partial marking presented as final cannot be told apart from a net that had
nothing left to do, so every consumer that treats completion as proof the run finished — a durable
checkpoint, a workflow step, an assertion on the final marking — silently accepts the truncation.

**Ambient host state is not a stop request.** An executor MUST NOT treat host state it did not
itself set — a thread's pre-existing cancellation or interrupt flag, for example — as a request to
stop. Such state is not a request from the caller of *this* run: it may have been left by earlier
work on a reused thread, or set by the run's own action code following the host language's
convention for propagating a cancellation it caught (in a runtime that invokes actions inline on
the orchestrator's own thread, that convention is indistinguishable from a stop). An executor that
consults it as a loop condition can execute zero cycles, or truncate mid-run, and report success in
both cases. A cancellation the executor observes *itself*, raised while it waits, MAY stop the run
— but only under the distinguishability rule above.

*When* the executor finishes a run, it *shall* make the marking the run ended with, unchanged by the finish, and the termination reason of the finish available to the caller.

The executor *shall* end a run only by finishing it, never as a side effect of another step such as a close.

*While* a run is finished, the executor *shall not* take another step of its loop (answering a snapshot request ([ENV-014]) reads the state and is not a step of the loop), and *shall not* change the returned marking or the termination reason.

The executor *shall* report the termination reason `quiescent` only when nothing is armed, in flight or queued ([EXEC-040]), and `terminal` only when a terminal place is marked ([EXEC-042]).

The executor *shall* report `closed` only after a close ([ENV-013]) or an immediate termination ([ENV-015]) was requested, and `stopped` only after an immediate termination, another caller-requested stop, or a fault of the host runtime that ends the run with a raised error ([EXEC-030]).

At a rest the run reached after a close or an immediate termination, `quiescent` and `closed` both conform, and after an immediate termination `stopped` conforms too.

A run budget that expires ends the caller's wait, not the loop: the executor reports a truncating reason to the caller (`stopped`, or a raised error), and a loop that the timeout policy leaves running has not finished, so its later steps and its finish are not steps after a finish.

*Where* the runtime has a cancellation the executor observes in its own wait, the executor *may* finish the run on it, and *shall* then report `interrupted`, and *shall* report `interrupted` only after such a cancellation.

The executor *shall not* treat host cancellation state that it did not set itself, such as a thread's interrupt flag set before the run or by the run's own action code, as a request to stop the run.

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
**Implementation status:** AC1–AC2 implemented everywhere. AC3–AC5 are new: **Java** implemented
(a queryable termination reason; a `WARN` log message accompanies it only where the stop was not
caller-requested, per [EVT-013] AC5). For AC4/AC5 Java does not merely avoid *reading* the
interrupt flag as a loop condition — that alone is not enough, because every blocking wait on the
platform throws at once when entered with the flag already set, so an ambient flag truncates the
run at its first wait instead of its first cycle. Both executors therefore **clear and remember**
the flag before every wait (the [TIME-015] host wait included) and after each inline action
returns, and **restore** it when `run()` returns. Only an interrupt that arrives during a wait
that was *entered with the flag clear* ends the run, as `INTERRUPTED`. A built-in wait reports
that by throwing. The [TIME-015] hosted wait (`ExecutionEnvironment.awaitWork`) cannot throw, so
there the executor reads the flag when the wait returns: **set on return from a wait entered
clear is the same event**, and ends the run `INTERRUPTED` the same way, with the same `WARN` and
the flag handed back when `run()` returns — otherwise an executor under an injected clock could
not be interrupted at all. The host's half of that contract is to let the flag survive its wait
(catch the exception, re-interrupt, return); a host that swallows the interrupt makes the run
uninterruptible while it waits. The consequences are documented rather than hidden: an external
interrupt that lands while an inline action is executing is indistinguishable from one the action
set itself, so it does not stop the run; it is deferred, and reappears on the thread when `run()`
returns. Inside the hosted wait the same ambiguity is resolved the other way — anything the host
runs on the orchestrator thread within `awaitWork` that sets the flag is indistinguishable from
an external interrupt, and ends the run — because an action is the run's own code and a wait is
not.
**TypeScript**, **Rust** and **Python** expose a queryable termination reason
(`quiescent`, `terminal`, `closed`, `stopped`), added with [EXEC-042]. That satisfies AC3; an
expired TypeScript run budget still raises as well. AC4/AC5 are vacuous where the runtime exposes no
ambient cancellation state an executor *could* consult, so no conformance test can even be written:
**Python** is the clearest case (actions run on Tokio threads with no running asyncio loop, there is
no thread-level interrupt flag, and the synchronous run loop never polls signals), then **Rust**
(which has no ambient cancellation state at all — task cancellation drops the future, which is not
state an executor reads) and **TypeScript** (a single-threaded event loop with nothing ambient to
consult).
**Test derivation:** Run net; inspect returned marking; verify expected token distribution. For
AC4, set the host's cancellation flag immediately before `run()` and assert the net still executes
to quiescence. For AC5, have an action set that flag mid-run and assert every downstream transition
still fires. For AC3, stop a run early and assert the caller can tell it apart from a quiesced one.
The AC4 and AC5 nets MUST actually reach a wait — an asynchronous action, a delayed transition —
because an all-synchronous chain never enters one and passes whether or not the flag is handled.
To test that a *real* cancellation still stops the run, raise it from a foreign thread while the
orchestrator is parked in the wait, not from an action — and do so under a host-supplied wait
([TIME-015]) as well as the built-in one, since the two report the interrupt differently.

**Termination reasons.** Where an implementation exposes the reason as a value, the values are:
`quiescent` ([EXEC-040]), `terminal` ([EXEC-042]), `closed` ([ENV-013]), `stopped` (a run budget,
another caller-requested stop, or a host fault that ends the run with a raised error) and
`interrupted` (a cancellation observed in the wait, where the runtime has one). `quiescent` and
`terminal` are the two **completed** reasons: the returned marking is the one the net was designed
to end in. The others are truncations.

---

#### EXEC-042: Terminal Places

**Priority:** SHOULD
**Kind:** B

A net MAY declare **terminal places** (`terminal(place)` on the net builder). A terminal place
states, in the model, that the run is over once the place holds a token. The executor ends the
run at that point. Nothing outside the net has to watch the marking and stop it.

A net that never quiesces makes this the only in-net way to say "done". Nets with environment
places are the usual example ([ENV-010]): a workflow that ends on a result, or a session that
ends on a cancel signal injected into a terminal environment place.

**Check points, and strictness.** An implementation MUST check terminal places at these points:
- on the initial marking, before the first cycle;
- after every token it deposits, from an action's completion, a mid-action publication
  ([IO-015]), an external injection, or a synchronous action's output within the firing pass
  ([EXEC-001]).

Once a deposit marks a terminal place, **no transition starts afterwards**. That includes a
transition that was already enabled later in the same firing pass. The deposit that marks the
terminal place completes atomically: all the tokens of that completion's outcome, or of that
published batch, are deposited. Strictness is what makes the runtime equal to the verification
encoding below. A check "at the next cycle boundary" would let transitions fire that the encoding
says cannot.

*While* a terminal place holds a token, the executor *shall not* take any step of its loop other than ending the run with the termination reason `terminal`: it starts no transition and processes no completion, publication or external event.

*When* the executor deposits the outcome of a completion (its returned emission or its timeout outcome) or a published batch ([IO-015]) and one of its tokens marks a terminal place, it *shall* deposit all of that outcome or batch before the run ends.

**What stopping means.** A stop on a terminal place is a hard stop:
- Actions still in flight are abandoned. Their late results are discarded and never deposited,
  as in [ENV-015].
- Completions and external events still queued behind the deposit are not admitted. A queued
  external event is refused ([ENV-004]), exactly as after [ENV-013].
- The run ends with the termination reason `terminal` ([EXEC-041]), a completed reason.
- No diagnostic event is emitted ([EVT-013] AC5): the stop was designed, not caller-requested.
- The reason `terminal` takes precedence: while a terminal place holds a token, the run does not
  end `quiescent`, `closed` or `stopped` ([EXEC-041]); a caller whose run budget expired earlier
  may still have been told `stopped` ([ENV-016]).
- A firing whose mid-action publication ([IO-015]) marked the terminal place is still running: it
  is abandoned like any other action in flight.
- A snapshot taken afterwards ([ENV-014]) still reports abandoned work as work in flight.
  Answering a snapshot request changes nothing and is not a step of the loop; [ENV-014] states
  the answer.

*If* no terminal place holds a token, *then* the executor *shall not* end the run with the termination reason `terminal`.

*When* a terminal place holds a token, the executor *shall* end the run with the termination reason `terminal` without waiting for the actions still in flight.

*When* the executor ends the run on a terminal place, it *shall* return the marking it holds at that point and *shall not* restore the tokens that abandoned firings consumed.

*When* the executor ends the run on a terminal place, it *shall* keep every firing still in flight as abandoned work in flight and *shall* refuse every external event still queued ([ENV-004]).

**Well-formedness.** A terminal place MUST NOT be an input or a read-arc place of any
transition: such a transition could never fire, so the net is rejected when it is built. A
terminal place MAY be an environment place: injecting into it ends the run.

*When* the executor injects an external event into a terminal place, it *shall* deposit the event's token there, which ends the run.

*If* a declared terminal place is an input place or a read-arc place of a transition of the net, *then* building the net *shall* fail.

*When* a net is built without composition and without fusion sets and no declared terminal place is an input place or a read-arc place of one of its transitions, building it *shall* succeed, and the built net's terminal places *shall* be exactly the declared ones.

**Composition.** Terminals are a property of the whole net. A subnet body ([MOD-001]) that
declares terminal places MUST be rejected by `compose` and `instantiate` with an error that names
the place. Scoped termination (ending one subnet instance) is not defined.

**Verification.** A verifier MUST apply terminal places automatically, with no restatement by
the caller. For each terminal place `P` it verifies the net, after the in-flight split of
[VER-004], in which:
- `P` inhibits every transition;
- `P` is a sink place ([VER-002]);
- `P` is a conditional-sink marker for every place ([VER-014]), i.e. `sinkPlacesWhen(P, all
  places)`.

This matches the runtime above for every transition the split of [VER-004] cuts in two: a
marking with `P` marked is quiescent and excused, and no transition fires once `P` is marked.
For a transition that stays atomic it holds for the properties named below. It is merged into
open-net contracts ([VER-022]) as a designed terminal. A net with no terminal places MUST
produce byte-identical scripts ([VER-013]).

The in-flight split of [VER-004] applies first. A transition that marks `P` is always split,
because `P` inhibits every transition, so the model has the executor's order: other actions
start while it is in flight, and its completion step marks `P` afterwards. `P` also inhibits
every completion step, so an action in flight when `P` is marked deposits nothing and leaves
its in-flight place marked, which `P` excuses. An abandoned action of a transition that stays
atomic is sound for monotone properties (place bounds, mutual exclusion, unreachability): the
abandoned marking lies below one the model reaches, where its outputs were deposited. It is
sound for `DeadlockFree` and `TerminatesAtSink` too, since `P` excuses every place at the
marking it ends in, and for `JoinedOrDeadLettered` and the upper bound of `QuiescentCount`,
which fewer tokens can only help.

A lower bound is the exception. Take `t: one(a) → ok` with a 100 ms action, `f: one(s) → done`
with a 10 ms action, `done` terminal, and `{a, s}` initially. The executor ends with
`a = ok = 0`, so `QuiescentCount([a, ok], 1, 1)` fails, while every atomic order counts one
token there. So when a `QuiescentCount` has `min > 0` and the net has a terminal place the
property does not list in `waivedBy`, every transition that deposits into a counted place or a
waiver place is split as well ([VER-004]). Its completion step is inhibited by `P` like any
other, so the model abandons the action as the executor does.

**Acceptance Criteria:**
1. A net whose initial marking marks a terminal place fires nothing and ends `terminal`.
2. An asynchronous completion that marks a terminal place ends the run `terminal`. With another
   action still in flight, the run does not wait for it, and its result never appears in the
   marking.
3. An injection that marks a terminal environment place ends the run `terminal`. An external
   event queued behind it is refused.
4. No transition starts after the deposit that marks a terminal place. Where synchronous outputs
   are deposited inside the firing pass, a second transition later in the same pass's order does
   not start. Where they are deposited in the completion phase, that transition may already have
   started, but its result is abandoned and never deposited.
5. A transition that consumes or reads a terminal place is rejected when the net is built.
6. `compose` and `instantiate` reject a subnet body that declares a terminal place.
7. Without the declaration, the net of AC2 is a `DeadlockFree` violation (its other in-flight
   work is stranded). With it, the verifier proves `DeadlockFree` without any sink option from
   the caller.
8. A net without terminal places produces byte-identical verification scripts.
9. On the net above (`t` 100 ms, `f` 10 ms, `done` terminal, `{a, s}`), `QuiescentCount([a, ok],
   1, 1)` is `Violated` and both executors end with `a = ok = 0`. With `done` in `waivedBy` it is
   `Proven`.

**Depends on:** [EXEC-001], [EXEC-020], [EXEC-022], [EXEC-040], [EXEC-041], [CONC-001], [IO-015],
[ENV-004], [ENV-013], [ENV-014], [ENV-015], [EVT-013], [VER-002], [VER-014], [VER-022], [MOD-001]
**Implementation status:** Java, TypeScript, Rust and Python (via Rust). Java and Rust deposit a
synchronous action's outputs inside the firing pass, so they break the pass there. TypeScript
deposits every output in the completion phase, so a transition started earlier in the same pass is
abandoned instead (AC4, second case). Either way it is an interleaving the atomic model allows: the
transition started before the terminal place was marked.
**Test derivation:** One net per AC. For AC4, build a pass with two enabled transitions ordered
by priority: the first is synchronous and marks the terminal place, the second must never fire.
For AC7, use a fork whose one arm marks the terminal place while the other arm's action is still
in flight.

---

## Stale Detection Pattern

#### EXEC-050: ~~Timestamp-Based Stale Detection~~ (Removed)

**Status:** Removed

Stale detection is a usage pattern built from read arcs ([CORE-032]), token timestamps ([CORE-010]) and XOR outputs ([IO-012]); it has no executor behaviour of its own. The pattern is kept as advice in [Usage guidance (non-normative)](00-index.md#usage-guidance-non-normative).

Retained as a tombstone for traceability; excluded from the active requirement count.
