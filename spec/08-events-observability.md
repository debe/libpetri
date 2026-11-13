# 08 — Events & Observability

This document specifies the event types emitted during execution, the event store interface, and observability features.

The ordering sentences of this chapter (which event comes before which within a start, a deposit or a run) read the event store with two kinds of event left out where Java appends them from outside the orchestrator: ActionTimedOut events ([EVT-010]), which Java emits from the action's timer, and the log messages Java captures from actions ([EVT-013]). Such an event can fall between the events of one orchestrator step. TypeScript and Rust append every event from the orchestrator, so in their stores no event falls inside a step.

---

## Event Hierarchy

#### EVT-001: Event Immutability

**Priority:** MUST
**Kind:** Q

All events are immutable value objects. Once created, no field can be modified. Collections within events (e.g., consumed tokens) are defensive copies.

**Acceptance Criteria:**
1. Event fields are read-only.
2. Collections within events are immutable copies (not live references).

**Test derivation:** Create event with list; modify original list; verify event's list unchanged.

---

#### EVT-002: ExecutionStarted Event

**Priority:** MUST
**Kind:** B

Emitted when the executor begins running. Contains:
- Timestamp
- Net name
- Execution ID (Java and TypeScript): the ID of the executor that runs, drawn when it is constructed

*When* a run starts, the executor *shall* emit an ExecutionStarted event before its first cycle ([EXEC-001]) and before any event of the run other than a log message ([EVT-013]).

The executor *shall* emit at most one ExecutionStarted event per run.

A run's events reach the event store only while the store is enabled ([EVT-020]).

Two executors constructed in one process from the same copy of the library *shall* carry different execution IDs, whatever the clock reads when each is constructed ([TIME-015] AC14).

*Where* the lifecycle events carry the execution ID (Java and TypeScript), the ExecutionStarted and ExecutionCompleted events of every run *shall* carry the ID of the executor that runs it.

An executor keeps its execution ID for all its runs, so the runs of one executor share it. [EVT-003] says when an ExecutionCompleted event is emitted.

**Acceptance Criteria:**
1. Emitted exactly once per execution run, before any transitions fire.
2. Two executors constructed in one process from the same copy of the library carry different execution IDs, even at the same clock reading.

**Test derivation:** Run net; verify the first event other than a log message is ExecutionStarted with correct net name.

---

#### EVT-003: ExecutionCompleted Event

**Priority:** MUST
**Kind:** B

Emitted when a run ends: the executor's loop finishes the run, whatever the termination reason ([EXEC-041]). Contains:
- Timestamp
- Net name
- Execution ID (Java and TypeScript, [EVT-002])
- Total duration (Java and TypeScript)

*When* the executor finishes a run ([EXEC-041]), it *shall* emit exactly one ExecutionCompleted event, whatever the termination reason.

The executor *shall* emit ExecutionCompleted events only when it finishes a run.

*If* the executor has emitted the ExecutionCompleted event of a run, *then* it *shall not* emit another event of that run other than a log message ([EVT-013]) or an ActionTimedOut event ([EVT-010]).

*When* the executor finishes a run with the termination reason `quiescent` ([EXEC-040]), it *shall* have no firing in flight, so every firing of the run has ended before its ExecutionCompleted event.

The event marks the end of the run, not its outcome. A run that a terminal stop ([EXEC-042]) or an immediate termination ([ENV-015]) ends can leave firings in flight: both abandon them, and the timer of an abandoned action can still emit its ActionTimedOut after the end. The event carries no termination reason: a consumer reads the reason as [EXEC-041] says, never the event alone as proof that the net quiesced. A loop that a caller's run budget leaves running has not finished, so it emits the event when it finishes, not when the caller's wait ends.

*Where* the ExecutionCompleted event carries a total duration (Java and TypeScript), the total duration *shall* be at least the time the run took on the executor's firing clock ([TIME-015]), from the reading at its ExecutionStarted event to the reading at its ExecutionCompleted event.

Java and TypeScript measure the total duration from the construction of the executor, so for a later run of the same executor it also counts the earlier runs and the time between them.

**Acceptance Criteria:**
1. Emitted exactly once per run that finishes, whatever the termination reason, and followed by no event of the run other than a log message or an ActionTimedOut.
2. At a quiescent finish no firing is in flight; a terminal stop or an immediate termination may leave firings in flight.
3. Where the event carries a total duration (Java and TypeScript), it is at least the time the run took on the executor's firing clock.

**Test derivation:** Run a net to quiescence; verify the last event is ExecutionCompleted, emitted once; with a firing clock that advances during the run, verify the duration is at least the time between the run's ExecutionStarted and ExecutionCompleted.

---

#### EVT-004: TransitionEnabled Event

**Priority:** MUST
**Kind:** B

Emitted when a transition becomes armed ([TIME-010]): when it is armed for the first time, or armed again after the executor disarmed it.

Enabled in this requirement means armed: a transition that is armed again after its own firing, after the enablement recheck of a firing pass disarmed it, or after a reap and a later write of one of its arc places is announced again, even when the marking kept it enabled. A transition whose clock restarts while it stays armed is announced with `TransitionClockRestarted` instead ([EVT-005]). As in the timing requirements, the transitions of a net are taken to have pairwise distinct names ([TIME-010]).

*When* a transition is armed after an enablement update and was not armed before it, the executor *shall* emit, at that update, exactly one TransitionEnabled event naming the transition.

The executor *shall* emit a TransitionEnabled event naming a transition only at an enablement update before which the transition was not armed and after which it is armed.

**Acceptance Criteria:**
1. Emitted each time a transition that was not armed before an enablement update is armed after it.
2. Not emitted if the transition was already armed, including when its clock restarts ([EVT-005]).

**Test derivation:** Add token enabling transition T; verify TransitionEnabled event for T.

---

#### EVT-005: TransitionClockRestarted Event

**Priority:** MUST
**Kind:** B

Emitted when a transition's timing clock restarts while the transition stays armed: another transition's firing left it disabled in the intermediate marking, and the marking enabled it again before the executor observed the gap (see [TIME-012]).

A transition's clock restart is pending when it is armed, a start of another transition since the last enablement update left it not enabled in that start's intermediate marking ([TIME-012]), and neither the enablement recheck of a firing pass nor a start of its own has disarmed it since. An enablement update restarts the clock of a transition when it leaves the transition armed with the update's clock reading as its stamp and its clock restart no longer pending. As in [EVT-004], the transitions of a net are taken to have pairwise distinct names.

*When* an enablement update restarts the clock of a transition whose clock restart was pending before the update, the executor *shall* emit, at that update, exactly one TransitionClockRestarted event naming the transition.

The executor *shall* emit a TransitionClockRestarted event naming a transition only at an enablement update before which the transition's clock restart was pending and that restarts the transition's clock.

**Acceptance Criteria:**
1. Emitted only when the transition stays armed but its clock restarts.
2. Not emitted on initial enablement, nor on re-enablement after an observed disablement (both are `TransitionEnabled`).

**Depends on:** [TIME-012]
**Test derivation:** Transition T is armed but not yet ready (for example `delayed(d)` before `d` has elapsed); another transition consumes T's input token, and its synchronous action deposits a new one before the executor re-evaluates T; verify TransitionClockRestarted for T. An executor that re-evaluates between consumption and deposit reports TransitionEnabled instead ([TIME-012] AC6), and so does a firing pass that rechecks a ready T after the consumption, since the recheck disarms it.

---

#### EVT-006: TransitionStarted Event

**Priority:** MUST
**Kind:** B

Emitted when a transition begins firing (tokens consumed, action dispatched). Contains:
- Timestamp
- Transition name
- List of removed tokens, consumed by input arcs and drained by reset arcs (Java and TypeScript only; defensive copy)

*When* a transition starts, the executor *shall* emit exactly one TransitionStarted event naming that transition as the last event of the start, and no event before it in that start other than TokenRemoved events ([EVT-012]).

The executor *shall* emit TransitionStarted events only when a transition starts.

*Where* the TransitionStarted event carries the removed tokens (Java and TypeScript), it *shall* list the tokens of the TokenRemoved events of the same start, in the same order.

*Where* the TransitionStarted event carries the removed tokens (Java and TypeScript), the list *shall* hold every token the firing rule removes from the marking visible to the pass ([EXEC-003], [EXEC-013]): the tokens the input arcs consume, then the tokens the reset arcs drain, each group in declaration order and each place's tokens oldest first.

**Acceptance Criteria:**
1. Emitted after token consumption, before action execution.
2. (Java and TypeScript) The list of removed tokens matches the tokens the start actually removes, consumed and drained.

**Test derivation:** Fire a transition that consumes 2 tokens through an input arc and drains 1 through a reset arc; verify its 3 TokenRemoved events, then TransitionStarted as the last event of the start, which in Java and TypeScript lists the same 3 tokens in the same order.

---

#### EVT-007: TransitionCompleted Event

**Priority:** MUST
**Kind:** B

Emitted when the executor deposits the outcome of a firing whose action completed successfully: the tokens the action produced at completion (an admitted completion, [EXEC-021]). Contains:
- Timestamp
- Transition name
- List of produced tokens (Java and TypeScript; defensive copy)
- Duration of action execution (Java and TypeScript)

*When* the executor deposits an admitted completion ([EXEC-021]), it *shall* emit the TokenAdded events of the deposited tokens followed by exactly one TransitionCompleted event naming the firing's transition, and no other event in that deposit except log messages ([EVT-013]).

The executor *shall* emit TransitionCompleted events only when it deposits an admitted completion or a timeout outcome ([EXEC-022]).

*If* the executor emits a TransitionCompleted event when it deposits a timeout outcome, *then* that event *shall* name the firing's transition and be the only TransitionCompleted event of the deposit and its last event other than log messages.

*Where* the TransitionCompleted event carries the produced tokens (Java and TypeScript), the TokenAdded events of the deposit of an admitted completion *shall* carry the tokens the action produced at completion in emission order ([EXEC-020]), and the TransitionCompleted event *shall* list the same tokens in the same order.

*Where* the TransitionCompleted event carries the produced tokens (Java and TypeScript), a TransitionCompleted event emitted when the executor deposits a timeout outcome *shall* list the tokens of that timeout outcome.

*Where* the TransitionCompleted event carries the duration of the action (Java and TypeScript), the duration *shall* be at most the firing-clock time from the start of the firing to the moment the executor deposits its outcome ([TIME-015]).

**Acceptance Criteria:**
1. Emitted after successful action completion and after the TokenAdded events of the tokens the action produced at completion. Tokens the action published before it completed ([IO-015]) may be deposited and reported after the event ([EXEC-020]).
2. (Java and TypeScript) The duration is at most the firing-clock time between the start of the firing and the deposit of its outcome; zero is allowed.

**Depends on:** [EVT-011], [EXEC-020], [EXEC-021], [EXEC-022]
**Implementation status:** Java and TypeScript also emit TransitionCompleted when they deposit a timeout outcome, after ActionTimedOut ([EVT-010]); Rust and Python do not. Java and TypeScript carry the produced tokens and the duration, and Java reports a zero duration for every synchronously completed action. The Rust event, which Python also uses, carries the transition name and a timestamp only.
**Test derivation:** Fire a transition whose action produces a token after the clock advanced; verify the TokenAdded event, then TransitionCompleted naming the transition, which in Java and TypeScript lists the produced token with a duration no larger than the clock advance.

---

#### EVT-008: TransitionFailed Event

**Priority:** MUST
**Kind:** B

Emitted when a firing fails ([EXEC-021], [EXEC-030]): its action throws an exception or returns an error, or output validation or the join-relay check of [NU-054] rejects its outcome. Contains:
- Timestamp
- Transition name
- Error message
- Exception type name (Java and TypeScript)

*If* a firing fails, because its action throws an exception or returns an error or because output validation or the join-relay check of [NU-054] rejects its outcome ([EXEC-021], [EXEC-030]), *then* the executor *shall* emit exactly one TransitionFailed event naming the firing's transition, and *shall not* emit a TransitionCompleted event or a TokenAdded event when it settles that firing.

The executor *shall* emit TransitionFailed events only when a firing fails.

Each TransitionFailed event *shall* carry the error message of the failure.

*Where* the TransitionFailed event carries the exception type (Java and TypeScript), it *shall* carry the name of the exception type of the failure.

**Acceptance Criteria:**
1. Emitted when action fails.
2. The error message is captured, and the exception type name where the event carries it (Java and TypeScript).

**Depends on:** [EXEC-030], [EXEC-021], [NU-054]
**Implementation status:** Java and TypeScript carry the error message and the exception type name (TypeScript also the stack trace). The Rust event, which Python also uses, carries one error text and no exception type.
**Test derivation:** Action throws; verify TransitionFailed with error details.

---

#### EVT-009: TransitionTimedOut Event

**Priority:** MUST
**Kind:** B

Reports a reap of a transition ([TIME-013]). Contains:
- Timestamp
- Transition name
- Deadline duration (Java and TypeScript)
- Elapsed time when reaped (Java and TypeScript): the time since the transition was last newly armed ([TIME-010])

*When* the executor reaps a transition ([TIME-013]), it *shall* emit exactly one TransitionTimedOut event naming that transition.

The executor *shall* emit a TransitionTimedOut event only when it reaps a transition, and the event *shall* name the transition it reaps.

*Where* the TransitionTimedOut event carries the deadline and the elapsed time (Java and TypeScript), the deadline *shall* be the latest bound of the transition, without the deadline tolerance, and the elapsed time *shall* be the transition's elapsed time ([TIME-010]) at the reading of the deadline step that reaps it.

Transition names are taken to be pairwise distinct, as in the timing requirements ([TIME-010]).

**Acceptance Criteria:**
1. Emitted in the deadline step of a cycle at whose reading a reapable, armed transition's
   elapsed time is strictly greater than its latest bound plus the deadline tolerance; never for
   an `Exact` transition ([TIME-006]).
2. After this event the transition is reaped: it stays enabled but is not armed, and does not
   fire until one of its arc places is written ([TIME-013]).

**Depends on:** [TIME-013]
**Implementation status:** Java and TypeScript carry the deadline and the elapsed time. The Rust event, which Python also uses, carries the timestamp and the transition name only.
**Test derivation:** Transition with Deadline(100ms); delay firing 200ms; verify TransitionTimedOut event.

---

#### EVT-010: ActionTimedOut Event

**Priority:** MUST
**Kind:** B

Emitted when a firing ends with its timeout outcome ([EXEC-022]): the budget of the `Out.Timeout` node of its output spec runs out before its action completes. It is distinct from TransitionTimedOut, which reports a transition reaped at its timing deadline ([EVT-009]). Contains:
- Timestamp
- Transition name
- Timeout duration

The executor *shall* emit an ActionTimedOut event only when the budget of a firing runs out or when it settles a firing that ended with its timeout outcome, and the event *shall* name that firing's transition.

*When* the executor emits the ActionTimedOut event of a firing as it deposits the firing's timeout outcome, it *shall* emit that event before the TokenAdded events of the outcome.

The executor *shall* emit at most one ActionTimedOut event for each firing, and, for a firing that ended with its timeout outcome, *shall* emit one no later than when it settles that outcome, whether it deposits the outcome or fails the firing because the join-relay check of [NU-054] rejects it.

Each ActionTimedOut event *shall* carry the duration of the `Timeout` node of the firing's output spec.

**Acceptance Criteria:**
1. Emitted for a firing that ends with its timeout outcome (its action's Out.Timeout budget runs out before the action completes, [EXEC-022]), and never for a transition reaped at its timing deadline.
2. The TokenAdded events of the timeout branch come after this event.

**Depends on:** [IO-013], [EXEC-022], [EVT-009], [NU-054]
**Implementation status:** Java and TypeScript emit the event from the action's timer when the budget runs out, and emit TransitionCompleted after the timeout branch is deposited ([EVT-007]). Rust, which Python also uses, emits it when the executor settles the timeout outcome, and emits no TransitionCompleted for it. Every runtime carries the timeout duration (Java as a Duration, TypeScript and Rust in milliseconds).
**Test derivation:** Action sleeps 500ms; Out.Timeout at 100ms; verify ActionTimedOut event.

---

#### EVT-011: TokenAdded Event

**Priority:** MUST
**Kind:** B

Emitted when the executor adds a token to a place: from an action's output, a timeout outcome, a mid-action publication (where the implementation offers one, [IO-015]) or an external injection. The tokens of the initial marking are not added by the executor and get no TokenAdded event; where the executor emits a MarkingSnapshot at the start of a run, that snapshot reports them ([EVT-014]). Contains:
- Timestamp
- Place name
- The token (Java and TypeScript; Rust and Python when the event store captures tokens)

*When* the executor deposits tokens into a place, by settling a completion or a timeout outcome, by depositing a mid-action publication (where the implementation offers one, [IO-015]) or by injecting an environment token, it *shall* emit one TokenAdded event naming that place for each token it deposits there.

The executor *shall* emit TokenAdded events only when it deposits tokens, and *shall not* emit a TokenAdded event for a token of the initial marking.

*Where* the TokenAdded event carries the token (Java and TypeScript; Rust and Python when the event store captures tokens), the TokenAdded events of a deposit *shall* carry, for each place, the tokens deposited there in the order they are appended, so that the place's queue before the deposit followed by these tokens is its queue after the deposit.

**Acceptance Criteria:**
1. Emitted for every token the executor deposits during a run, and at no other time: not for the tokens of the initial marking, not when a transition starts and not when an injection is requested.
2. Place name identifies the target place.
3. Where the event carries the token, the tokens reported for a place in one deposit are the deposited tokens, in the order they are appended.

**Test derivation:** Add token to place; verify TokenAdded event with correct place name.

---

#### EVT-012: TokenRemoved Event

**Priority:** MUST
**Kind:** B

Emitted when a token is removed from a place (consumed by input arc or cleared by reset arc). Contains:
- Timestamp
- Place name
- The token (Java and TypeScript; Rust and Python when the event store captures tokens)

*When* a transition starts, the executor *shall* emit, for each place, one TokenRemoved event naming that place for each token the start removes from it, whether an input arc consumes the token or a reset arc drains it.

The executor *shall* emit TokenRemoved events only when a transition starts.

*Where* the TokenRemoved event carries the token (Java and TypeScript; Rust and Python when the event store captures tokens), the TokenRemoved events of a start *shall* carry, for each place, the tokens the start removes from it in the order they stood in the place's queue, and, where no correlated input of a match specification takes them ([NU-020]), these tokens followed by the tokens the place keeps *shall* be the place's queue before the start.

**Acceptance Criteria:**
1. Emitted for every token removal.
2. Place name identifies the source place.

**Test derivation:** Fire transition consuming token; verify TokenRemoved event.

---

#### EVT-013: LogMessage Event

**Priority:** SHOULD
**Kind:** B

Emitted when a transition action produces log output. The engine captures log statements from within actions and wraps them as events. Contains:
- Timestamp
- Transition name, empty or absent when no transition is responsible for the message (see below)
- Logger name (Java and TypeScript)
- Log level
- Message
- Error/throwable details (optional; Java and TypeScript)

*Where* the implementation captures the log statements of actions (Java and TypeScript), the executor *shall* report each log statement it captures from the action of a firing as one LogMessage event that carries the firing's transition name, the statement's level and its message.

**The engine may also emit diagnostics of its own** through this event rather than adding an event
type per diagnostic: a dead arc ([CORE-037]), an unknown place ([CORE-072]), a repeated output
place ([IO-016]), and similar. A diagnostic that a transition is responsible for carries that
transition's name: the transition that declares the dead arc, or the transition whose firing
deposited the tokens. A diagnostic that no transition is responsible for, at the initial-marking
and injection seams, carries an empty or absent transition name.
Consumers MUST therefore treat the transition name as optional and MUST NOT key, filter or group on
it without handling its absence.

*When* the executor emits an engine diagnostic before the first step of a run, the diagnostic *shall* carry an empty or absent transition name, unless it reports a dead arc ([CORE-037]), in which case it *shall* carry the name of the transition that declares the arc.

*When* the executor emits an engine diagnostic as it injects a token into an environment place, the diagnostic *shall* carry an empty or absent transition name.

*When* the executor emits an engine diagnostic as it deposits the outcome of a firing or a batch that the firing published ([IO-015]), the diagnostic *shall* carry the name of that firing's transition.

An engine diagnostic SHOULD be emitted only where it reports something the caller did not ask for
and would otherwise not learn. A diagnostic on a path the caller explicitly requested, such as a
`close()` it called itself ([ENV-013]), is a false positive: it fires on every run of a net whose
normal ending is a shutdown ([ENV-012]), and a warning that always fires trains its reader to
ignore the level. Where a queryable result already carries the information ([EXEC-041] AC3), the
event is an addition to it and MUST NOT be the only signal.

*When* the caller drains, closes or stops the executor ([ENV-011], [ENV-013], [ENV-015]), the executor *shall not* emit an engine diagnostic for the request or for the queued external events it discards because of it.

*When* the executor refuses an injection request because it is draining, closed or stopped, or because the run has finished ([ENV-006]), it *shall not* emit an engine diagnostic for the refusal.

*When* a run ends because it is quiescent, a terminal place is marked, or the caller closed or stopped it ([EXEC-041]), the executor *shall not* emit an engine diagnostic for that end.

**Acceptance Criteria:**
1. Log statements within actions are captured as LogMessage events.
2. Log level (INFO, WARN, ERROR, etc.) is preserved.
3. Exception details are included when present.
4. An engine diagnostic that no transition is responsible for carries an empty or absent
   transition name, one that a transition is responsible for carries that transition's name, and
   every consumer of the event tolerates an absent name.
5. No engine diagnostic is emitted on a caller-requested termination path (a drain, a close or a
   stop), nor when a run ends as quiescent, terminal, closed or stopped, nor when an injection
   request is refused.

**Depends on:** [CORE-072], [ENV-012], [ENV-013], [EXEC-041]
**Implementation notes:**
- Java: Captures SLF4J output via LogCaptureScope
- TypeScript: Captures via context.log() method
- Rust: Emits the engine diagnostics as LogMessage events, but does not capture the log statements of actions (the transition context's log function is never installed); Python, which runs on Rust, captures none either.

**Test derivation:** Action logs a warning; verify LogMessage event with correct level and message.

---

#### EVT-014: MarkingSnapshot Event

**Priority:** SHOULD
**Kind:** B

Emitted at specific points during execution to capture the marking. Contains:
- Timestamp
- Map of place name → list of tokens

*Where* an executor emits MarkingSnapshot events (Java and TypeScript), *when* a run starts, the executor *shall* emit, before the run's first cycle, an ExecutionStarted event and, after it, a MarkingSnapshot event that carries the initial marking.

*Where* an executor emits MarkingSnapshot events (Java and TypeScript), *when* a run finishes ([EXEC-041]), whatever its termination reason, the executor *shall* emit a MarkingSnapshot event that carries the marking the run ends with and, after it, an ExecutionCompleted event.

*Where* an executor emits MarkingSnapshot events (Java and TypeScript), the marking a MarkingSnapshot event carries *shall* list every place the net declares that holds a token, *shall* list each place it lists with all of that place's tokens in FIFO order, and *shall not* list a place that holds no token.

*Where* an executor emits MarkingSnapshot events (Java and TypeScript), the marking a MarkingSnapshot event carries *shall* list each place at most once and *shall* list its places in ascending code-point order of the place name, also for a place name above U+FFFF ([CORE-073]).

A place the net does not declare may be listed with its tokens (Java) or left out (TypeScript). Rust and Python have no producer of this event (see the implementation status below).

A marking snapshot carried on this event is the snapshot form of [CORE-073], and [CORE-073]'s
canonical place-order rule applies to it: where an implementation emits this event, the places of
the marking it carries MUST appear in ascending code-point order of the place name. The event is
an ordered, in-process value, so the order is both meetable and observable there, and it is one
of the two places a host takes a snapshot from.

The order is **not** promised past the event. A JSON session archive ([EVT-025]) and the JSON
debug protocol are unordered media, and code-point order is deliberately not required of them.
What is required of any rendering of this event — those two included — is **reproducibility
across runs of the same implementation**: two runs over identical data MUST produce identical
output, so a rendering MUST NOT pass the marking through a container whose iteration order is
randomised per process ([CORE-073]).

Emitting this event MUST NOT fail the run. In particular the refusal [CORE-073] requires for two
same-named places belongs to the host-facing snapshot and restore operations, not to this event.

**Acceptance Criteria:**
1. Emitted at least at execution start (initial marking) and before execution completion.
2. Snapshot is a deep defensive copy (not a live reference).
3. Only non-empty places are included.
4. The places of the marking carried on the event appear in ascending code-point order of the
   place name ([CORE-073] AC12), on every executor that emits the event (Java and TypeScript), including for a place name above U+FFFF.
5. Rendering the same event stream twice with one implementation — into an archive or onto the
   debug protocol — yields identical output.

**Depends on:** [CORE-073]
**Implementation status:** **Java** and **TypeScript** emit the event at start and before
completion, on both executors, in canonical order. **Rust** — and **Python**, which rides it —
declares the event and consumes it (debug converter, marking cache, archive metadata) but has **no
producer**: no executor emits it, so AC1–AC4 are unmet there and a test that constructs the event
by hand is not coverage of them. AC5 holds in all four. Rust's tests cite this requirement for
AC5 alone — the `libpetri-debug` rendering-order tests over debug frames, the marking cache, the
net structure and archive headers, each of which failed on the per-process-randomised map they
replaced. A converter-level test of event-to-JSON order would prove nothing (`serde_json`'s map is
ordered unless `preserve_order` is enabled, and it is not), so there is deliberately none.

**Test derivation:** Run net; verify MarkingSnapshot at start and end; verify snapshot accuracy.
For AC4, run a net whose place names include one above U+FFFF and one in U+E000–U+FFFF and assert
the order on the emitted event. For AC5, render one recorded stream twice — in two processes where
the implementation's default map is randomised per process — and compare the output.

---

## Event Store Interface

#### EVT-020: EventStore Interface

**Priority:** MUST
**Kind:** F

The event store provides:
- `append(event)` — thread-safe event addition
- `events()` — a subsequence of the appended events, in append order
- `isEnabled()` — whether event capture is active

The list `events()` returns *shall* be a subsequence of the events appended to the store: only appended events, in the order they were appended, each append at most once. A store that keeps token payloads only for some places (the Python binding's `capture_tokens` filter) is compared with the appended events after the same payloads are removed from them. Which appended events the list leaves out, and whether it is a copy or a live view of the store, is up to each store ([EVT-021], [EVT-022], [EVT-024]).

Events reach a store through the executor, which appends them only while the store reports itself as enabled (`isEnabled()` returns true; in Rust, the store type's `ENABLED` constant is true).

**Acceptance Criteria:**
1. append() is safe to call from any thread.
2. events() returns a subsequence of the appended events, in append order; whether that list is a copy or a live view is not specified.
3. isEnabled() controls whether the executor appends events to the store.

**Test derivation:** Append events from multiple threads; verify events() returns only appended events, each at most once, in the order the appends took effect (on the in-memory store, all of them, [EVT-021]).

---

#### EVT-021: InMemoryEventStore

**Priority:** MUST
**Kind:** F

A thread-safe in-memory event store that retains all events in the order they were appended.

A new in-memory event store *shall* return no event from `events()`.

*When* an event is appended to the in-memory event store, a call of `events()` made right after the append *shall* return the events that a call made right before the append returns, with that event added at the end.

*Where* the in-memory event store provides `clear()`, a call of `events()` made right after `clear()` *shall* return no event.

The in-memory event store *shall* report itself as enabled, so that an executor appends every event it emits to it (see [EVT-020]): `isEnabled()` returns true in Java and TypeScript, the store type's `ENABLED` constant is true in Rust, and the Python binding's store is written through a Rust store whose `ENABLED` constant is true.

A call of `events()` changes nothing that a later call of `events()` returns, so the sentences above speak of what a call returns after the appends and clears made so far.

**Acceptance Criteria:**
1. Events are stored in insertion order.
2. Thread-safe append (concurrent callers do not lose events).
3. events() returns the events appended since the last clear() (every appended event where the store has no clear()), in the order they were appended; what a returned list shows after later operations, whether it is a copy or a live view, is not specified.
4. Where the store provides clear() (TypeScript; in Java only on the package-private InMemoryEventStore class, which EventStore.inMemory() returns as the EventStore interface), clear() empties it for test reuse.

**Test derivation:** Append 100 events; verify events() returns 100 in order.

---

#### EVT-022: NoopEventStore

**Priority:** MUST
**Kind:** F

A zero-cost event store that discards all events. When used, the executor skips event object creation entirely.

The noop event store *shall* return no event from `events()`, whatever was appended to it, and the list it returns *shall* stay empty whatever is appended to it later.

*When* an event is appended to the noop event store, the store *shall* discard it.

The noop event store *shall* report itself as not enabled (`isEnabled()` returns false; in Rust, the store type's `ENABLED` constant is false).

**Acceptance Criteria:**
1. append() is a no-op.
2. events() returns empty.
3. isEnabled() returns false.
4. The executor does not allocate event objects when the noop store is used.

**Test derivation:** Run net with noop store; verify no events captured; verify no allocation overhead (benchmark).

---

#### EVT-023: LoggingEventStore

**Priority:** SHOULD
**Kind:** F

An event store decorator that logs events to the platform's logging framework at appropriate levels before delegating to a wrapped store.

*When* an event is appended to the logging event store, the store *shall* log the event once, at the level of the event's kind, *shall* then pass the event once to the wrapped store, and *shall* log no other record and pass no other event, whatever store it wraps.

The logging event store *shall* make the logging call of an event whenever the logging framework has the call's level enabled, and *may* skip the call when the framework has that level disabled.

The logging event store *shall* log TransitionFailed, TransitionTimedOut and ActionTimedOut events at WARN level.

The logging event store *shall* log ExecutionStarted and ExecutionCompleted events at INFO level.

The logging event store *shall* log TransitionEnabled, TransitionClockRestarted, TransitionStarted and TransitionCompleted events at DEBUG level.

The logging event store *shall* log TokenAdded, TokenRemoved, MarkingSnapshot and LogMessage events at TRACE level.

The logging event store *shall* return from `events()` what the wrapped store returns.

The logging event store *shall* report itself as enabled, whatever the wrapped store reports (`isEnabled()` returns true).

**Acceptance Criteria:**
1. Failure events (TransitionFailed, TransitionTimedOut, ActionTimedOut) logged at WARN level.
2. Lifecycle events (ExecutionStarted, ExecutionCompleted) logged at INFO level.
3. The other transition events (TransitionEnabled, TransitionClockRestarted, TransitionStarted, TransitionCompleted) logged at DEBUG level.
4. Token events (TokenAdded, TokenRemoved), MarkingSnapshot and LogMessage logged at TRACE level.
5. Delegates to wrapped store after logging; `events()` returns the wrapped store's events.
6. Reports itself as enabled whatever store it wraps.

**Implementation notes:**
- Java: Full implementation with `java.lang.System.Logger`
- TypeScript: Not implemented
- Rust: Not implemented
- Python: Not implemented

**Test derivation:** Run net with logging store; verify log output at correct levels.

---

#### EVT-024: DebugEventStore

**Priority:** SHOULD
**Kind:** F

An event store with live tailing support for debug UIs. Supports:
- Subscriptions (consumers notified of new events)
- Capacity management (eviction of old events)
- Session tracking

A debug event store has a capacity: a positive number of events, 10,000 unless the caller gives another. A debug event store is open until its `close()` is called.

*When* events have been appended to a debug event store one after the other, a call of `events()` *shall* return the newest of them, as many as the store's capacity allows, in the order they were appended.

*When* an event is appended to an open debug event store, the append *shall* complete without waiting for any subscriber to receive the event.

Each subscriber of a debug event store *shall* receive only events appended to the store, each at most once and, for appends that do not overlap in time, in the order they were appended. A subscriber may receive an event after the append that added it has returned.

*While* a debug event store is open, a caller *shall* be able to add a further subscriber, whatever subscribers the store already has.

*While* a debug event store is open, each subscriber that has not cancelled its subscription *shall* still be able to receive every event appended since it subscribed, whatever the other subscribers have received.

**Acceptance Criteria:**
1. While the store is open, each subscriber that has not cancelled can receive the events appended since it subscribed, each at most once and, for appends that do not overlap in time, in the order they were appended.
2. Old events are evicted when capacity is exceeded.
3. Multiple subscribers can be active simultaneously.

**Implementation notes:**
- Java: Full implementation with virtual-thread broadcast
- TypeScript: Full implementation with microtask broadcast
- Rust: Implemented (`libpetri-debug::DebugEventStore`, crossbeam-channel subscriptions)

**Test derivation:** Subscribe to debug store; append event; verify subscriber receives it.

---

#### EVT-025: Session Archive Format

**Priority:** SHOULD
**Kind:** F

Completed debug sessions can be serialized to a length-prefixed compressed archive (LZ4
for Java, gzip for TypeScript and Rust) for later replay. The archive has a versioned
header followed by one length-prefixed JSON record per event.

Three header versions exist; readers MUST accept all three and dispatch into the matching
sealed variant (`V1`/`V2`/`V3`) so callers can pattern-match on writer guarantees.

**Header format** (the same field names and JSON types in every language; the encoding of time values differs, see below):

| Header | First shipped | Adds over previous |
|---|---|---|
| v1 | libpetri 1.5.x | baseline: `sessionId`, `netName`, `dotDiagram`, `startTime`, `eventCount`, `structure` |
| v2 | libpetri 1.7.x | `endTime`, `tags`, pre-computed `metadata` (event-type histogram, first/last, hasErrors) |
| v3 | libpetri 1.8.0 | same fields as v2; bump signals typed-token event bodies |

**Event body format** (per-language, because each implementation serializes its
own event shape — Java serializes the `NetEvent` record directly, TypeScript and Rust
serialize a `NetEventInfo` debug-protocol projection). Archive bodies are therefore not
byte-compatible across languages, and neither are whole archives: Java compresses with LZ4 and
the others with gzip, and every time value (the header's `startTime` and `endTime`, the event and
token timestamps of the body) is ISO-8601 text in Java and TypeScript and decimal epoch
milliseconds in Rust and Python. The Rust reader rejects an archive whose event timestamps are
ISO-8601 text, and the TypeScript reader reads decimal epoch milliseconds as invalid dates, so an
archive is read correctly only by an implementation of the language that wrote it. All languages
agree on *semantic* content, not wire layout.

- **Java (v3):** `token: {valueType: <FQN>, v: <structured JSON>, createdAt: <iso>}`.
  Special cases: `{valueType: "void", createdAt}` for unit tokens (no `v`);
  `{valueType, text, createdAt}` fallback when Jackson cannot structure the value;
  legacy `{value, valueType: simpleName, createdAt}` from v1/v2 also accepted.
- **TypeScript (v3):** `token: {id, type, value: <String(value)>, structured?: <JSON>, timestamp}`.
  The `value` string is retained alongside the new optional `structured` field so the
  bundled debug UI keeps rendering without change. `type` is `value.constructor.name`
  (simple name — TypeScript has no portable FQN).
- **Rust (v3):** `token: {id, type, value, structured?, timestamp}`, with the field names and
  JSON shapes of TypeScript via a shared `NetEventInfo` camelCase serde contract; the
  `timestamp` is decimal epoch milliseconds where TypeScript writes ISO-8601 text. `type` is
  `std::any::type_name::<T>()` at token-erasure time; `structured` is populated by
  [`TokenProjectorRegistry`](../rust/libpetri-debug/src/token_projector_registry.rs)
  when the token's inner `T` is registered, else falls back to
  `{"type": <type_name>, "text": <Debug repr>}` — parallel to Java's `{valueType, text}`
  shape.

**Key order in an archive is not guaranteed, and [CORE-073]'s canonical order does not reach it.**
A JSON object is an *unordered* collection by definition, so an archive that renders a marking as
one carries no order regardless of what the producer did. Some implementations preserve insertion
order incidentally; JavaScript cannot, because it orders integer-like keys numerically ahead of
every other key whatever the insertion order — a net with a place named `2` reorders itself. The
JSON debug protocol is the same medium and is bound the same way.

This is a bound on the medium, not a defect to fix: canonical order is guaranteed **on the snapshot
form and on the event** ([CORE-073], [EVT-014]), which is where a host that hashes, diffs or
content-addresses should take it. A host needing a byte-stable archive artefact *across
implementations* MUST canonicalise at its own serialization boundary rather than relying on the
object's key order.

What the medium does not excuse is **irreproducibility**. An archive written twice by the same
implementation from identical run data MUST NOT differ ([CORE-073], [EVT-014] AC5). JavaScript's
numeric-first key order is arbitrary but fixed, so it satisfies this; a marking copied through a
per-process-randomised map does not, and an implementation MUST NOT put one on the path to the
archive or the debug protocol. This asks for no change of archive format.

*Where* an implementation provides session archives, *when* its reader reads a well-formed archive of header version 1, 2 or 3 in its own implementation's format (one whose `eventCount` and metadata are those of its body, as its writer writes them), the reader *shall* return the header variant of that version (`V1`, `V2` or `V3`).

*Where* an implementation provides session archives, *if* its reader reads an archive in its own implementation's format whose header version is not 1, 2 or 3, *then* the reader *shall* reject the archive with the error `Unsupported archive version: <version> (reader supports 1..3)`, which names the version it found and the supported range.

*Where* an implementation provides session archives, *when* its reader accepts a well-formed archive in its own implementation's format, it *shall* return the header's `eventCount` unchanged, the header's session fields and metadata as written, and one event for each record of the body, in body order.

*Where* an implementation provides session archives, *when* its writer writes an archive of a session for header version 1, 2 or 3 (`writeV1`, `writeV2`, or `write` for version 3), the header *shall* carry that version and the session's own header fields.

*Where* an implementation provides session archives, *when* its writer writes an archive, the writer *shall* take one snapshot of the event store, the header's `eventCount` *shall* be the number of events in that snapshot, a V1 header *shall* carry no metadata, the V2 and V3 metadata *shall* be computed from that snapshot, and the body *shall* hold one record for each event of that snapshot, in the order of the snapshot.

*Where* an implementation provides session archives, two archives its writer writes for the same header version from identical run data *shall* be identical.

*Where* an implementation provides session archives, its writer *shall* write an archive of any session for each of the header versions 1, 2 and 3 (`writeV1`, `writeV2`, and `write` for version 3), whatever the session's event store holds.

**Acceptance Criteria:**
1. Each language's v3-capable writer defaults to emitting v3; `writeV1` / `writeV2` still
   exist and emit the corresponding header. The event body is always the writer's current
   token shape regardless of header version — byte-identical 1.7.x event bodies are not
   producible from 1.8.0+.
2. Each v3-capable reader reads v1, v2, and v3 archives; an archive with an unknown
   version is rejected with an error/exception that names the encountered version and
   the supported range.
3. Record, enum, boxed primitive, and unit tokens written under Java v3 round-trip with
   their original concrete type when the class is on the reader's classpath.
4. When a Java-side `valueType` FQN cannot be resolved (class not on classpath, shaded,
   cross-language write), the token hydrates as `Token<JsonNode>` — the deserializer
   never throws on unknown types.
5. TypeScript + Rust archives preserve the `structured` JSON payload across a full
   write→read round-trip; replay consumers receive `TokenInfo.structured` (TS) or a
   `ReplayedTokenPayload` on `NetEvent::TokenAdded`/`TokenRemoved` (Rust) carrying the
   same JSON shape the writer emitted.
6. Legacy (`{value, valueType: simpleName}`) tokens continue to hydrate as string-valued
   tokens on any v3-capable reader.
7. TypeScript archives omit the `structured` field entirely when it would be empty or
   unprojectable (wire size is neutral for unstructurable tokens).
8. The header `eventCount` field MUST equal the number of event records that follow in
   the body. Implementations MUST NOT populate `eventCount` from a cumulative lifetime
   counter on the event store; the value reflects retained body length only. After a
   write→read round-trip, `archive.eventCount() == archive.events().size()` for all
   three header versions and across all three language implementations. The writer
   MUST take exactly one snapshot of the event store; header `eventCount`, V2/V3
   metadata, and the event body MUST all derive from that single snapshot.

**Implementation notes:**
- Java: Full implementation — default writer emits v3, deserializer reconstructs original
  token types via `Class.forName`. The V2 and V3 header holds the tags and the metadata histogram
  in ascending code-point order of their keys, so two JVMs write the same header for the same run
  data.
- TypeScript: Full implementation — default writer emits v3, `structured` projection via
  `JSON.parse(JSON.stringify(value))`.
- Rust: Full implementation — default writer emits v3 via a user-supplied
  `TokenProjectorRegistry`; reader hydrates into a `ReplayedTokenPayload` exposing the
  `structured` JSON without attempting to revive the original `T` (Rust has no
  `Class.forName` equivalent).
- Python: `SessionArchiveWriter.write_from_store` writes version 3 through the Rust writer, and
  `write_v1` and `write_v2` write versions 1 and 2. Each archives every event of the store's
  snapshot, whatever its size, and a header whose `structure` lists the net's places and
  transitions. For an empty store the start time is 0 and there is no end time, so two archives of
  the same empty session are identical.

**Cross-language replay:** Java → Java reconstructs typed tokens. TypeScript and Rust
archive bodies share field names and JSON shapes (shared `NetEventInfo` contract) but not the
time encoding, so neither reader reads the other's archives correctly; both preserve `structured` across
a round-trip. Java archive bodies use a different shape
(`NetEvent` direct serialization) and are not interchangeable at the body level — use
language-native archives for full-fidelity replay.

**Security note:** Java v3 deserialization resolves the archive-supplied `valueType`
FQN via `Class.forName`. TypeScript's `structuredValue` uses
`JSON.parse(JSON.stringify(v))` — safe against code execution and prototype pollution,
but respects any `toJSON()` method on the value. Rust's `TokenProjectorRegistry`
projects only user-registered types; unregistered values fall back to `Debug` repr and
never execute arbitrary code. Archives are a trust boundary: **do not deserialize
archives from untrusted network sources** without a guard — in Java because of
static-initializer side effects, in TypeScript because a hostile `toJSON()` override
could return misleading data, and in Rust because a hostile archive could claim any
`type_name` string.

**Test derivation:**
- Java: `SessionArchiveV3Test` (record/enum/primitive/unit round-trip, v2-on-v3
  back-compat, unknown-version rejection) and `NetEventConverterTest.TokenInfoConversion`
  (structured field projection).
- TypeScript: `session-archive-v3.test.ts` (analogous round-trip) and
  `session-archive-v2.test.ts` (explicit v2 emission remains possible).
- Rust: `session_archive_reader::tests::v3_roundtrip_preserves_structured_token` (end-to-end
  writer→reader through `TokenProjectorRegistry`),
  `reader_accepts_v3_archives` (third-party v3 archive hydration), and
  `read_rejects_unsupported_version`.

---

## Event Query Helpers

#### EVT-030: Event Filtering

**Priority:** SHOULD
**Kind:** F

The event store or helper functions support:
- Filter by event type
- Filter by transition name
- Filter by place name (for token events)
- Pagination (offset / limit) over the filtered result
- Filter for failure events
- Count events, and an event-type histogram (counters)

*Where* an implementation provides a query over the events of an event store, the query without offset and limit *shall* return exactly the events that `events()` returns and that match every filter the query gives, in the order `events()` returns them, for every query whose transition filter does not name the empty name.

A filter by event type *shall* match the events of the given types, a filter by transition name *shall* match the events that carry one of the given transition names, and a filter by place name *shall* match the events that carry one of the given place names.

An event that carries no transition name *shall* match no filter by transition name, and its presence in the store *shall not* change which other events such a filter returns.

*Where* an implementation provides offset and limit on a query, the query *shall* skip the first `offset` matching events and return the first `limit` of the matching events that follow (all of them when no limit is given), so that the page is taken over the filtered result and not over the store.

*Where* an implementation provides `failures()`, it *shall* return exactly the TransitionFailed, TransitionTimedOut and ActionTimedOut events that `events()` returns, in the order `events()` returns them.

*Where* an implementation provides `counters()`, it *shall* name each event type that occurs among the events `events()` returns exactly once, with the number of those events of that type, and *shall* name no other event type.

*Where* an implementation provides a count of events, the count *shall* be the number of events that `events()` returns whose type is one of the given types, or the number of all of them when no type is given.

**Acceptance Criteria:**
1. `eventsOfType(TransitionCompleted)` returns only completed events.
2. `transitionEvents("MyTransition")` returns all events that carry that transition name, also when the store holds events that carry no transition name.
3. Place filtering returns only token events for the named place(s); offset/limit page the result.
4. `failures()` returns TransitionFailed, TransitionTimedOut, and ActionTimedOut events.
5. `counters()` returns a `{eventType: count}` histogram whose values sum to the total event count.

**Implementation status:** the helpers differ per language. Filter by type: Java and TypeScript (`eventsOfType`), Python (`events(types=...)`); the Rust store has none. Filter by transition name: Java and TypeScript (`transitionEvents`), Rust (`transition_events`), Python (`events(transitions=...)`). Filter by place name, offset/limit and `counters()`: Python only. Count: all four count every event (`size()` in Java, TypeScript and Rust, `len()` in Python), and Python also counts by type (`count(types=...)`). `failures()`: all four. Every implementation marks the missing transition name of an engine diagnostic at the initial-marking seam by the empty name, so a filter for the empty name returns those diagnostics; such a filter is outside this requirement. Java's `transitionEvents` skips an event with no transition name, such as the engine diagnostic of an interrupted run.
**Test derivation:** Run net with mixed events; verify each filter, pagination, and the counters
histogram return correct subsets / totals.

---

## Live Streaming & Replay

#### EVT-031: EventStore Live Subscriptions

**Priority:** SHOULD
**Kind:** B

An event store may expose a live subscription that streams events as they are appended, distinct
from the post-hoc snapshot reads of [EVT-020]. A subscription:
- delivers only events matching its server-side filters (by type, transition, and place);
- is forward-only: events appended **before** the subscription was created are not replayed;
- batches delivery by a caller-chosen `batch_size` and `batch_timeout_ms` (a `batch_size = 1`,
  `batch_timeout_ms = 0` "unary" mode delivers one event at a time for low latency);
- is bounded: it uses a finite channel capacity, and an append of a matching event that finds the channel full ends that subscription instead of waiting for room;
- terminates cleanly on explicit close, when the store is dropped, or when its channel overflows.

This differs from [EVT-024] (DebugEventStore live tailing for debug UIs): EVT-031 governs
subscriptions over the ordinary observability store, with server-side filtering and batching.

*Where* an event store provides live subscriptions, the events a subscription has received at any point, taken over all its batches in the order it received them, *shall* be events that match its filters and were appended to the store after the subscription was created and before that point, in append order, each at most once.

Each batch a subscription receives *shall* hold at least one event and at most `batch_size` events, so that with `batch_size = 1` it receives one event per batch.

Each subscription *shall* have a finite channel capacity.

*When* a receive has taken the first event of its batch, it *shall* add further events until the batch holds `batch_size` events, `batch_timeout_ms` have elapsed since it took that first event, or no further event can arrive, and *shall* then return the batch; with `batch_timeout_ms = 0` it *shall* add only the events already in the channel.

*When* an append of an event that matches the filters of a subscription finds its channel full, the store *shall* end that subscription: the subscription *shall* receive no event appended from then on, and, if none of its receives is pending at that append, its receives *shall* take the events its channel holds and then report the end of the stream, unless the subscription is closed first.

Until the store is dropped, an append *shall* be accepted at every point; in particular it *shall not* wait for room in the channel of a subscription.

*When* a subscription is closed while none of its receives is pending, it *shall* receive no further event, and its next receive *shall* report the end of the stream.

*When* the store is dropped, the receives of each of its subscriptions that has no receive pending *shall* take the events its channel holds and then report the end of the stream, unless the subscription is closed first.

**Acceptance Criteria:**
1. A subscriber receives only events matching its filters, in append order.
2. Events appended before the subscription are not delivered (forward-only).
3. Unary mode delivers one event per batch; batched mode delivers up to `batch_size`, flushing
   early after `batch_timeout_ms`.
4. Explicit close with no receive pending ends iteration cleanly; a full channel ends the subscription: it receives no later event, the append does not wait, and with no receive pending its receives report the end after they have taken the events its channel holds.

**Depends on:** [EVT-020], [EVT-021], [EVT-030]
**Status:** Proposed
**Implementation status:** Rust binding + Python (`InMemoryEventStore.subscribe(...)`,
`async for batch in ...`, and `subscribe_stream(...)`, which is `batch_size = 1` without the list wrapper) implemented; Java/TypeScript pending. Python's defaults are `batch_size = 64`, `batch_timeout_ms = 10` and `channel_capacity = 4096`, and a `batch_size` or `channel_capacity` of 0 is rejected with `ValueError`. In Python, `close()` called while a receive is pending does nothing, so the pending receive keeps waiting; this case is outside the requirement. A receive pending when an append finds its channel full is outside the requirement too. The end of the stream is reported the same way after a close, a drop and an overflow.
**Test derivation:** Run an async net feeding environment events; subscribe with a transition
filter; verify batched forward-only delivery and clean close.

---

#### EVT-032: Marking Replay Cache

**Priority:** SHOULD
**Kind:** F

A replay cache reconstructs execution state at an arbitrary event index from a recorded event
stream, for debug-protocol seek / step. `compute_at(events, index)` returns a `ComputedState`
— the marking (token counts per place), enabled transitions, and in-flight transitions — replayed
from the nearest periodically-cached snapshot rather than from the start of the stream.

*While* every snapshot in the replay cache is at an index no greater than the length of `events` and is the replay of `events` up to that index, `compute_at(events, index)` *shall* return the replay of the first `index` events of `events`, or of all of `events` when `index` is beyond its length.

*When* `compute_at(events, index)` returns, every snapshot it leaves in the replay cache *shall* be at an index no greater than the length of `events` and be the replay of `events` up to that index, provided every snapshot in the cache met both conditions before the call.

The replay of an event stream *shall* start from the empty state (no token in any place, no enabled and no in-flight transition) and apply its events in order, each as follows: a `MarkingSnapshot` sets the token count of every place it carries to the count it carries and of every other place to zero; a `TokenAdded` adds one token to its place; a `TokenRemoved` removes one token from its place, and does nothing if the place has none; a `TransitionEnabled` adds its transition to the enabled transitions; a `TransitionStarted` removes its transition from the enabled transitions and adds it to the in-flight transitions; a `TransitionCompleted`, `TransitionFailed`, `TransitionTimedOut` or `ActionTimedOut` removes its transition from the in-flight transitions; any other event (`ExecutionStarted`, `ExecutionCompleted`, `TransitionClockRestarted`, `LogMessage`) leaves the state unchanged.

The enabled transitions are those with a `TransitionEnabled` event and no later `TransitionStarted` event, so they over-approximate the transitions enabled at that point of the run: a transition whose tokens another firing took, or a reaped transition, stays listed. The in-flight transitions are a set of names, so a transition with two firings in flight at once leaves it when its first firing ends. The replayed token counts include the initial marking only for a stream that reports it: a Java or TypeScript stream reports the initial marking in a `MarkingSnapshot` right after its `ExecutionStarted` event, while a Rust or Python stream reports no initial token. The two transition lists of a `ComputedState` are sets: their order is not specified.

*Where* the executor is a Java or TypeScript executor, which reports the initial marking in a `MarkingSnapshot` right after `ExecutionStarted` ([EVT-014]), the replay of all events a run has emitted before its first step, or up to the end of any of its steps, *shall* count, for every place the net declares, the tokens that place holds at that point, and *shall* list among the enabled transitions every transition that holds a clock at that point, also one whose clock restart is pending ([EVT-005]). At an index inside the events of one step, for example between the `TokenRemoved` events of a firing that starts, the replayed counts can match no marking the executor held. The count is required only on the places the net declares: a TypeScript snapshot lists only the declared places, so the snapshot before `ExecutionCompleted` sets the replayed count of an undeclared place back to zero.

**Acceptance Criteria:**
1. `compute_at(events, 0)` is the empty state; `compute_at(events, len)` is the replay of the whole
   stream.
2. An index beyond the stream length is clamped to the end (no panic).
3. Repeated calls on a stream that only grows at its end return state equal to a from-scratch
   replay: the same token count per place and the same sets of enabled and in-flight transitions,
   in an unspecified order. A stream that changed otherwise, for example by the eviction of its
   oldest events ([EVT-024]), needs `invalidate()` before the next call. Reusing cached snapshots
   is expected for speed only: it does not change the state returned.
4. The marking in `ComputedState` carries token counts; replayed tokens need not carry value
   payloads (events carry type + structured metadata, not live objects).
5. In Java and TypeScript, before the first step of a run and after each of its steps, the replay
   of the events emitted so far counts on every declared place the tokens it holds, and lists as
   enabled every transition that holds a clock; a Rust or Python stream of a net with an initial
   token fails this before the first step.

**Depends on:** [EVT-021], [EVT-004], [EVT-006], [EVT-007], [EVT-008], [EVT-009], [EVT-010], [EVT-011], [EVT-012], [EVT-014]
**Implementation status:** Implemented in all four: Rust (`libpetri-debug::MarkingCache`), Python
(`MarkingCache`, `ComputedState`), Java (`org.libpetri.debug.MarkingCache.computeAt`) and
TypeScript (`MarkingCache.computeAt` in `libpetri/debug`). Known gap:
no debug protocol handler calls `invalidate()` when its debug store evicts events ([EVT-024]), so a
seek after an eviction can return a state that is not the replay (AC3).
**Test derivation:** Record a multi-firing run; `compute_at` at 0, an intermediate index, the end,
and beyond-end; verify clamping and snapshot reuse. In Java and TypeScript, run a net with token 1 in
place 0 and one transition that takes it and puts 9 back; before the first step and after each
step, compare the replayed counts with the executor's marking and check that every transition
that holds a clock is listed as enabled.
