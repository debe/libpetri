# 04 — Execution Model

This document specifies the orchestrator loop, scheduling, token consumption, output validation, failure handling, and quiescence detection.

---

## Orchestrator Loop

#### EXEC-001: Orchestrator Loop Steps

**Priority:** MUST

The executor runs a loop with the following steps, in order:

1. **Process completions** — collect outputs from actions that have finished; validate against output specs; deposit produced tokens into marking; emit events.
2. **Process external events** — dequeue and apply externally injected tokens (see [ENV-003]).
3. **Update enablement** — re-evaluate which transitions are enabled based on current marking. Only transitions affected by token changes need re-evaluation (see [CONC-004]).
4. **Enforce deadlines** — check enabled transitions with finite deadlines; disable those past their latest bound.
5. **Fire ready transitions** — among enabled transitions whose elapsed time >= earliest bound, sort by priority (then FIFO), and fire in order.
6. **Await work** — if no transitions are ready and none are in-flight, wait for a completion, external event, or timer.

**Acceptance Criteria:**
1. Steps execute in the specified order each cycle.
2. No transition fires before completions are processed.
3. External events are applied before enablement updates.

**Test derivation:** Trace execution of a simple net; verify step ordering via event log.

---

## Scheduling

#### EXEC-002: Priority-Based Firing Order

**Priority:** MUST

When multiple transitions are ready to fire (enabled and timing satisfied), they are sorted by:
1. **Priority** — descending (higher priority fires first)
2. **Enablement time** — ascending (FIFO; earliest enabled fires first among equal priority)

**All-immediate fast path.** When every transition is `Immediate` and all priorities are equal, backends fire straight from the enablement bitmap in ascending declaration order and do not read the enablement timestamp at all — including when two ready transitions carry different timestamps because one was held across cycles while in flight. This is deliberate, and every backend takes the path under the same condition. The sort above describes the general path.

**Acceptance Criteria:**
1. Transition with priority 10 fires before transition with priority 5.
2. Two transitions with equal priority on the general path: the one enabled first fires first.
3. Equal priority **and** equal enablement time (transitions enabled in the same
   orchestrator cycle share one enablement timestamp): the tie breaks by ascending
   declaration order, so the order is fully deterministic.
4. Every executor backend produces the **identical** ready order for the same net
   and marking. Enablement-time order is the general-path order; on the
   all-immediate single-priority fast path every backend fires in declaration
   order instead. Backends MUST NOT differ in which order they use, nor in the
   condition that selects it.

**Test derivation:** Three transitions with priorities 5, 10, 5; enable all simultaneously; verify firing order: P10, then P5 (first enabled), then P5 (second enabled). For AC4, on a net that takes the general path (two priority levels, or one non-`Immediate` transition), enable two equal-priority transitions in different cycles with declaration order opposite to enablement order and verify every backend follows enablement order; on an all-immediate single-priority net, verify every backend fires in declaration order.

---

#### EXEC-003: Competitive Conflict Resolution

**Priority:** MUST

When multiple transitions compete for the same input tokens, the highest-priority ready transition fires first and consumes the tokens. Lower-priority transitions become disabled if their inputs are no longer satisfied.

**Acceptance Criteria:**
1. Two transitions sharing input place P; T1 (P=10) and T2 (P=5); one token in P; T1 fires; T2 disabled.
2. If T1 is not ready (timing not satisfied), T2 may fire.
3. Whether a loser's inputs are "no longer satisfied" is judged against the marking
   as consumed by earlier firings in the same firing pass, but before any tokens
   their synchronous actions produced: T1 (higher priority) consumes a token T2
   needs and refills the place via its own output in the same pass; T2 remains
   disabled and may fire no earlier than the next cycle, since outputs deposit in
   step 1 and firing is step 5 (see [EXEC-001]).
4. AC3 governs token **counts**, not only presence. A cardinality gate
   (`exactly(n)`, `atLeast(n)`) re-evaluated during the pass MUST NOT count tokens
   a same-pass synchronous action deposited, and a ν-correlated join whose
   correlated input place received such a deposit fires no earlier than the next
   cycle. Deposits become visible to every transition uniformly at the next
   cycle's step 1, never part-way through a pass.
5. Invisibility extends to consumption, not just to the enablement test. A
   draining arc — `all()`, `atLeast(n)`, or a reset arc — that fires later in the
   same pass takes only the tokens that were present when the pass began, as
   consumed by earlier firings; tokens a same-pass action deposited survive it and
   remain for the next cycle. Deposits land at the tail of each place's FIFO
   queue ([EXEC-010]), so this is the prefix of length `available - deposited`.
   Without this, a gate that correctly refused to *count* a same-pass deposit
   would still *swallow* it.

**Test derivation:** Two competing transitions; verify only highest priority fires when only 1 token available.

---

## Token Consumption

#### EXEC-010: FIFO Token Consumption

**Priority:** MUST

When a transition fires, it consumes tokens from the oldest-first (FIFO) end of each input place's queue. The number of tokens consumed is determined by the input cardinality's `consumptionCount(available)`.

**Acceptance Criteria:**
1. Tokens added in order A, B, C; One consumes A.
2. Exactly(2) consumes A, B.
3. All consumes A, B, C.

**Depends on:** [CORE-013], [IO-007]
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

When a transition fires, read arc values are provided to the action without consuming the tokens. The oldest token in the read place is peeked.

**Acceptance Criteria:**
1. Read place has tokens A, B; action receives A; both A and B remain after firing.

**Depends on:** [CORE-032]
**Test derivation:** Read place with 2 tokens; fire transition; verify both tokens remain; verify action received first.

---

#### EXEC-013: Reset Arc Execution

**Priority:** MUST

When a transition fires, all tokens are removed from each reset place. This happens during the firing step, before the action executes. Like input consumption, the drain lands in the intermediate marking, so it restarts the clocks of transitions it disables there (see [TIME-012]).

**Acceptance Criteria:**
1. Reset place with 5 tokens → all removed.
2. Reset place empty → no error.
3. If the reset place is also an input or read place of another enabled transition, that transition's clock restarts ([TIME-012]).
4. Reset draining occurs **after** read-arc peeking within the same firing: a
   transition with a read arc and a reset arc on the same place observes the
   pre-reset front token via `ctx.read()` (see [EXEC-012], [CORE-032]). The
   overall in-firing order is: input consumption, then read peeks, then reset
   draining.

**Depends on:** [CORE-034], [EXEC-012], [CORE-032]
**Test derivation:** Transition with reset on place with 3 tokens; verify all removed; verify clock restart for affected transitions.

---

## Output Handling

#### EXEC-020: Output Token Deposition

**Priority:** MUST

After an action completes, the executor deposits produced tokens into the marking according to the output specification. Each token is added to the end of the target place's FIFO queue.

**Acceptance Criteria:**
1. Action produces token with value V to place P; V appears at end of P's queue.
2. Multiple tokens to same place are added in order.

**Test derivation:** Action produces 3 tokens to P; verify all 3 appear in order.

---

#### EXEC-021: Output Spec Validation

**Priority:** MUST

After depositing tokens, the executor validates that the produced tokens satisfy the declared output specification (see [IO-015]).

**Acceptance Criteria:**
1. And: all children received tokens → valid.
2. Xor: exactly one child is selected; overlapping branches resolve without a tie-break, because [IO-015] requires the selected assignment's claim to *equal* the produced set, not merely be satisfied by it.
3. Violation → failure event emitted.
4. Validation is applied by every executor backend a language ships, not only the reference one.

**Depends on:** [IO-011], [IO-012], [IO-015]
**Test derivation:** Xor output with tokens to 2 branches → violation event.

---

#### EXEC-022: Action Timeout Handling

**Priority:** MUST

When a transition's output specification includes a Timeout node, the executor races the action against the timeout duration:
- Action completes first → normal output validation.
- Timeout fires first → the firing is abandoned (the action is stopped where the runtime can; see [IO-013]); the timeout child output receives tokens; ActionTimedOut event emitted.

**Acceptance Criteria:**
1. Action completes in 50ms with 100ms timeout → normal completion.
2. Action takes 200ms with 100ms timeout → timeout branch activated; ActionTimedOut event.
3. ForwardInput in timeout child → **every** token consumed from the `from` place is forwarded to the `to` place, one output token per consumed token, in consumption order ([IO-014]).
4. Output the action wrote before the budget expired is discarded, not merged with the timeout branch ([IO-013] AC5).

**Depends on:** [IO-013], [IO-014], [EVT-009]
**Test derivation:** Slow action with timeout; verify timeout branch tokens and event.

---

## Failure Handling

#### EXEC-030: Action Failure

**Priority:** MUST

If an action throws an exception or returns an error, the executor:
1. Emits a TransitionFailed event with error details.
2. Does NOT restore consumed input tokens (no rollback).
3. The transition is no longer in-flight.
4. Execution continues with remaining transitions.

**Acceptance Criteria:**
1. Failing action → TransitionFailed event with error message and type.
2. Consumed tokens are lost (not returned to input places).
3. Other transitions continue to fire.

**Depends on:** [EVT-007]
**Test derivation:** Action throws; verify failure event; verify consumed tokens not restored; verify net continues.

---

#### EXEC-031: No Rollback

**Priority:** MUST

The engine does not provide transaction rollback. Once tokens are consumed by a firing transition, they are not restored if the action fails. This is a deliberate design choice — rollback would require complex compensation logic and conflicts with the async nature of actions.

**Acceptance Criteria:**
1. Failed action → consumed tokens permanently removed.

**Test derivation:** Fire transition consuming token; action fails; verify token not in any place.

---

## Quiescence

#### EXEC-040: Standard Quiescence

**Priority:** MUST

When no environment places are registered, the executor terminates when ALL of the following hold:
1. No transitions are enabled.
2. No transitions are in-flight (executing actions).
3. No external events are pending.

The final marking is returned.

**Acceptance Criteria:**
1. Simple chain A→B→C: executor runs to completion; returns marking with token in C.
2. Parallel branches: waits for all in-flight actions before terminating.

**Test derivation:** Linear chain of 5 transitions; verify executor returns marking with token at end.

---

#### EXEC-041: Execution Result

**Priority:** MUST

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

**Acceptance Criteria:**
1. Return value contains the token state after quiescence.
2. All places with tokens are represented.
3. A run that stops before quiescence is distinguishable by the caller from one that reached
   quiescence.
4. Ambient host cancellation state present *before* the run begins neither prevents the run from
   executing nor causes it to report completion having fired nothing.
5. Action code that sets the host's cancellation flag while running — the conventional way to
   propagate a caught cancellation — does not truncate the run.

**Depends on:** [EXEC-040], [ENV-013]
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
`quiescent` ([EXEC-040]), `terminal` ([EXEC-042]), `closed` ([ENV-013]), `stopped` (a run budget
or another caller-requested stop) and `interrupted` (a cancellation observed in the wait, where
the runtime has one). `quiescent` and `terminal` are the two **completed** reasons: the returned
marking is the one the net was designed to end in. The others are truncations.

---

#### EXEC-042: Terminal Places

**Priority:** SHOULD

A net MAY declare **terminal places** (`terminal(place)` on the net builder). A terminal place
states, in the model, that the run is over once the place holds a token. The executor ends the
run at that point. Nothing outside the net has to watch the marking and stop it.

A net that never quiesces makes this the only in-net way to say "done". Nets with environment
places are the usual example ([ENV-010]): a workflow that ends on a result, or a session that
ends on a cancel signal injected into a terminal environment place.

**Check points, and strictness.** An implementation MUST check terminal places at these points:
- on the initial marking, before the first cycle;
- after every token it deposits, from an action's completion, an external injection, or a
  synchronous action's output within the firing pass ([EXEC-001]).

Once a deposit marks a terminal place, **no transition starts afterwards**. That includes a
transition that was already enabled later in the same firing pass. The firing that made the
deposit completes atomically: all its outputs are deposited. Strictness is what makes the runtime
equal to the verification encoding below. A check "at the next cycle boundary" would let
transitions fire that the encoding says cannot.

**What stopping means.** A stop on a terminal place is a hard stop:
- Actions still in flight are abandoned. Their late results are discarded and never deposited,
  as in [ENV-015].
- Completions and external events still queued behind the deposit are not admitted. A queued
  external event is refused ([ENV-004]), exactly as after [ENV-013].
- The run ends with the termination reason `terminal` ([EXEC-041]), a completed reason.
- No diagnostic event is emitted ([EVT-013] AC5): the stop was designed, not caller-requested.
- A snapshot taken afterwards ([ENV-014]) still reports abandoned work as work in flight.

**Well-formedness.** A terminal place MUST NOT be an input or a read-arc place of any
transition: such a transition could never fire, so the net is rejected when it is built. A
terminal place MAY be an environment place: injecting into it ends the run.

**Composition.** Terminals are a property of the whole net. A subnet body ([MOD-001]) that
declares terminal places MUST be rejected by `compose` and `instantiate` with an error that names
the place. Scoped termination (ending one subnet instance) is not defined.

**Verification.** A verifier MUST apply terminal places automatically, with no restatement by
the caller. For each terminal place `P` it verifies the net in which:
- `P` inhibits every transition;
- `P` is a sink place ([VER-002]);
- `P` is a conditional-sink marker for every place ([VER-014]), i.e. `sinkPlacesWhen(P, all
  places)`.

This is exact for the runtime above. A marking with `P` marked is quiescent and excused, and no
transition fires once `P` is marked. It is merged into open-net contracts ([VER-022]) as a
designed terminal. A net with no terminal places MUST produce byte-identical scripts ([VER-013]).

Abandoned in-flight actions are sound for monotone properties (place bounds, mutual exclusion,
unreachability): the abandoned marking lies below one the model reaches. Where the transition
that marks `P` tests an input of an abandoned action by an inhibitor, reset or consume-all arc,
that interleaving is not an atomic-firing behaviour ([VER-010] AC4 applies unchanged).

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

**Depends on:** [EXEC-001], [EXEC-040], [EXEC-041], [ENV-004], [ENV-013], [ENV-015], [VER-002],
[VER-014], [VER-022], [MOD-001]
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

#### EXEC-050: Timestamp-Based Stale Detection

**Priority:** SHOULD

Transitions can implement stale detection by comparing timestamps. A transition reads a "latest search timestamp" via a read arc and compares it with the consumed token's timestamp to determine if the data is still current.

This is a **usage pattern**, not a built-in feature — the engine provides the primitives (read arcs, token timestamps) and the action logic performs the comparison.

**Acceptance Criteria:**
1. Read arc provides timestamp from shared state.
2. Action can compare consumed token timestamp with read value.
3. Stale data detected → action can route to discard branch (via XOR output).

**Depends on:** [CORE-032], [CORE-010]
**Test derivation:** CommitProductList pattern: read LATEST_SEARCH_TIMESTAMP; compare with consumed token; discard if stale.
