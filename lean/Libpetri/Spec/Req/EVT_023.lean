import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryStore
import Libpetri.Spec.GlossaryEvents
import Libpetri.Spec.Req.EVT_021

set_option linter.missingDocs true

/-!
# EVT-023: LoggingEventStore (`spec/08-events-observability.md`)

The logging event store is a decorator: it logs each appended event to the platform's logging
framework at a level fixed by the event's kind, then passes the event to the store it wraps,
and answers `events()` from that store. Only Java implements it (`EventStore.logging()` and
`EventStore.logging(delegate)`, `java/src/main/java/org/libpetri/event/EventStore.java:212-242`,
`334-428`).

The requirement is a predicate over an abstract decorator `D : LogDecorator E`: the effects one
append makes (`onAppend W th e`: log calls and passes to the wrapped store, in order, for the
decorator around the store `W` with the logging framework at the threshold `th`) and the store a
caller sees when `D` wraps a store `W` (`over W`, a `StoreObs E` of the glossary
`GlossaryStore.lean`). The event type `E` is a parameter; the block reads an event only through
`kind : E → NetEventKind`, the thirteen kinds of net event. The level table is ruling D29 (a)
(evt-c ruling EVT-C3 (a)): Java's table, which names every kind once, so the acceptance
criteria no longer overlap (clash evt-c#3).

Line 1 compares what the framework lets a caller observe (`observed th`): the log calls at a
level the threshold enables, which are the records the framework writes, and every pass. So a
decorator may skip a call at a disabled level, as Java's early return does, and the effects may
not depend on the wrapped store, since line 1 holds around every `W`.

The witness is `refLogStore kind`, the shape of Java's `LoggingEventStore`, early return
included. The wrong decorators are one per load-bearing part of a line: the table with the
transition events first (AC3 read literally, `TransitionFailed` at DEBUG), a decorator that
passes the event before logging it, one that logs and swallows the event, one that logs twice,
one that passes twice, one whose early return forgets `ActionTimedOut`, one that logs nothing
around a store that is not enabled, one that keeps its own list, and one that reports the
wrapped store's enabled flag. Consequences tie the block to the store tier: the wrapped store
receives exactly the decorator's appends, an executor's events all reach the decorator whatever
it wraps (`storeSink`, [EVT-020] AC3), so the decorator over an in-memory store returns them in
order ([EVT-021]) and the decorator over the noop store is not a noop store ([EVT-022]).

`NetEventKind`, `NetEventKind.isFailure` and `LogLevel` are the event glossary's
(`GlossaryEvents.lean`): one kind type and one failure set for the whole event model, the set
[EVT-030]'s `failures()` reads (design events.md, section 3).
-/

namespace Libpetri.Spec

/-! ## Block-local vocabulary -/

/-- The level table of the logging event store (ruling D29 (a), evt-c EVT-C3 (a): Java's table,
`EventStore.java:374-416`): the failure kinds at WARN, the two lifecycle kinds at INFO, the other
four transition kinds at DEBUG, and the token kinds, `MarkingSnapshot` and `LogMessage` at
TRACE. -/
def eventLogLevel : NetEventKind → LogLevel
  | .transitionFailed | .transitionTimedOut | .actionTimedOut => .warn
  | .executionStarted | .executionCompleted => .info
  | .transitionEnabled | .transitionClockRestarted | .transitionStarted
  | .transitionCompleted => .debug
  | .tokenAdded | .tokenRemoved | .markingSnapshot | .logMessage => .trace

/-- One effect of an append on the logging decorator: a call of the logging framework for an
event at a level, or passing an event to the wrapped store (its `append`). -/
inductive LogEffect (E : Type) where
  /-- Log the event at the level. -/
  | log (lvl : LogLevel) (e : E)
  /-- Pass the event to the wrapped store. -/
  | pass (e : E)
  deriving DecidableEq, Repr

variable {E : Type}

/-- The effects of an append a caller observes with the logging framework at the threshold `th`:
the log calls at a level `th` enables (the records the framework writes) and every pass, in
order. A log call at a disabled level writes nothing and is not observed. -/
def observed (th : LogLevel) (fx : List (LogEffect E)) : List (LogEffect E) :=
  fx.filter fun
    | .log l _ => l.loggableAt th
    | .pass _ => true

/-- The logging decorator, as a caller observes it:

* `onAppend W th e`: the effects of one call of `append(e)` on the decorator around the store
  `W`, with the logging framework at the threshold `th`, in the order they happen;
* `over W`: the decorator wrapped around the store `W`, observed as a store (its enabled flag,
  whether it provides `clear()`, and what its `events()` shows after a history, glossary: Event
  store). -/
structure LogDecorator (E : Type) where
  /-- The effects of `append(e)` around `W` at the threshold `th`, in order. -/
  onAppend : StoreObs E → LogLevel → E → List (LogEffect E)
  /-- The decorator around the wrapped store `W`, observed as a store. -/
  over : StoreObs E → StoreObs E

/-- The log records the framework at the threshold `th` writes for an executor's events `tr`
appended to `D` around `W`, in order: each written record's level and event. -/
def logRecords (D : LogDecorator E) (W : StoreObs E) (th : LogLevel) (tr : List E) :
    List (LogLevel × E) :=
  tr.flatMap fun e => (observed th (D.onAppend W th e)).filterMap fun
    | .log l x => some (l, x)
    | .pass _ => none

/-- The events the wrapped store `W` receives when the events `tr` are appended to `D` around
it with the framework at the threshold `th`, in order (`observed` keeps every pass). -/
def passedOn (D : LogDecorator E) (W : StoreObs E) (th : LogLevel) (tr : List E) : List E :=
  tr.flatMap fun e => (observed th (D.onAppend W th e)).filterMap fun
    | .log _ _ => none
    | .pass x => some x

/-- Java's early-return guard `isWarnOrInfo` (`EventStore.java:418-425`): the kinds logged at
WARN or INFO. -/
def NetEventKind.isWarnOrInfo : NetEventKind → Bool
  | .executionStarted | .executionCompleted | .transitionFailed | .transitionTimedOut
  | .actionTimedOut => true
  | _ => false

/-- The calls of Java's `LoggingEventStore.append` for an event of kind `k` with the framework at
the threshold `th` and the early-return guard `g`: when DEBUG is not loggable and `g k` is false,
no log call (`EventStore.java:370`); otherwise one call at the level of the kind. Then the pass. -/
def guardedCalls (g : NetEventKind → Bool) (th : LogLevel) (k : NetEventKind) (e : E) :
    List (LogEffect E) :=
  if !(LogLevel.debug.loggableAt th) && !(g k) then [.pass e]
  else [.log (eventLogLevel k) e, .pass e]

/-- The reference logging decorator (Java `LoggingEventStore`, `EventStore.java:334-428`): an
append logs the event at the level of its kind, skipping the call for a DEBUG or TRACE kind when
DEBUG is not loggable, then passes it to the wrapped store; `events()` is the wrapped store's; it
reports itself enabled whatever it wraps (`EventStore.java:355-358`) and provides no
`clear()`. -/
def refLogStore (kind : E → NetEventKind) : LogDecorator E where
  onAppend _ th e := guardedCalls NetEventKind.isWarnOrInfo th (kind e) e
  over W := { enabled := true, hasClear := false, read := W.read }

#spec_witness refLogStore

/-! ## EVT-023: LoggingEventStore -/

requirement EVT_023
  id "EVT-023"
  title "LoggingEventStore"
  kind F
  scope "the logging event store decorator (Java EventStore.logging() and EventStore.logging(delegate)); TypeScript, Rust and Python have none"
  source verbatim "spec/08-events-observability.md"
  quote "*When* an event is appended to the logging event store, the store *shall* log the event once, at the level of the event's kind, *shall* then pass the event once to the wrapped store, and *shall* log no other record and pass no other event, whatever store it wraps."
        "The logging event store *shall* make the logging call of an event whenever the logging framework has the call's level enabled, and *may* skip the call when the framework has that level disabled."
        "The logging event store *shall* log TransitionFailed, TransitionTimedOut and ActionTimedOut events at WARN level."
        "The logging event store *shall* log ExecutionStarted and ExecutionCompleted events at INFO level."
        "The logging event store *shall* log TransitionEnabled, TransitionClockRestarted, TransitionStarted and TransitionCompleted events at DEBUG level."
        "The logging event store *shall* log TokenAdded, TokenRemoved, MarkingSnapshot and LogMessage events at TRACE level."
        "The logging event store *shall* return from `events()` what the wrapped store returns."
        "The logging event store *shall* report itself as enabled, whatever the wrapped store reports (`isEnabled()` returns true)."
  reading "For every event type E with its kind function kind : E → NetEventKind, and every logging decorator D over E:"
          "for every wrapped store W, every framework threshold th and every event e, the effects of an append of e that a caller observes with the framework at th (the log calls at a level th enables, which are the records the framework writes, and every pass) are those of one log call for e at the level eventLogLevel (kind e) followed by one pass of e to the wrapped store, and no other; the table eventLogLevel gives WARN to the three failure kinds, INFO to ExecutionStarted and ExecutionCompleted, DEBUG to the other four transition kinds, and TRACE to TokenAdded, TokenRemoved, MarkingSnapshot and LogMessage;"
          "for every wrapped store W and all histories h and h', a call of events() on D around W shows what a call of events() on W shows;"
          "for every wrapped store W, D around W reports itself as enabled."
  assumes "The model is the observation of one decorator, D : LogDecorator E: onAppend W th e, the effects of one append(e) on the decorator around the store W with the logging framework at the threshold th, in order (a log call at a level, or passing an event to the wrapped store), and over W, the decorator around W observed as a store (glossary: Event store). The event type E is a parameter and is read only through kind : E → NetEventKind, so the block says nothing about an event's payload or about the text of a log message (Java logs the transition name, token counts and durations; a message format is not a line). The kind function is the event model's (wave W7's glossary of events: the kind of each of the thirteen events of EVT-002 to EVT-014), not a choice of the implementation: a decorator paired with a kind function that maps every event to TokenAdded would log everything at TRACE and meet the line, so the line binds only with the event model's kind function, and tying the two is an obligation of the W7 integrator, recorded in the consistency module of the events (ConsistencyEvents.lean)."
          "The configuration of the logging framework is a threshold th: a level is enabled when it is th or more severe (LogLevel.loggableAt; System.Logger levels are ordered, and its default backend, java.util.logging, filters by a threshold). A log call at a disabled level writes no record, so line 1 compares the observed effects only, and a decorator may make or skip such a call, as the second quoted sentence says. Java skips it: logEvent returns early when DEBUG is not loggable and the event is not a WARN or INFO kind (EventStore.java:370, 418-425), and refLogStore has that guard. EVT_023_mutant_slipGuard is the guard with ActionTimedOut left out: with every level enabled it logs as Java does, but with the framework at INFO it writes no WARN record for an ActionTimedOut, so it violates line 1. A framework filter that is not a threshold, and a logging call that throws, are out of scope."
          "Line 1 is the first six quoted sentences. The first fixes the two effects, their order, that there is no other, and that they do not depend on the wrapped store: onAppend is given W, and line 1 holds for every W. EVT_023_mutant_logTwice and EVT_023_mutant_passTwice keep the order and log or pass a second time, so they violate 'once'. EVT_023_mutant_gatedOnWrapped logs and passes nothing around a store that reports itself not enabled, as an append guarded by the wrapped store's isEnabled() would, so EventStore.logging() would log nothing; it meets line 1 around the in-memory store and violates it around the noop store. The second sentence is the threshold. The other four are the level table eventLogLevel, which names each of the thirteen kinds once."
          "AC1, AC2, AC3 and AC4 (failure events at WARN, lifecycle events at INFO, the other transition events at DEBUG, token events, MarkingSnapshot and LogMessage at TRACE) are the table of line 1. As first written they overlapped and did not cover every kind: TransitionFailed, TransitionTimedOut and ActionTimedOut are both failure and transition events, and MarkingSnapshot and LogMessage were in no class (clash evt-c#3). Ruling D29 (a) (evt-c EVT-C3 (a)) writes Java's table into the requirement, failures first, and the spec edit of this wave names the kinds in each AC. EVT_023_mutant_transitionFirst is AC3 read literally (TransitionFailed at DEBUG) and violates line 1. eventLogLevel_failure states that every failure kind, the set EVT-030's failures() returns, is logged at WARN."
          "AC5 (delegates to the wrapped store after logging) is the order in line 1 and line 2. evt023_passedOn states the consequence that the wrapped store receives exactly the events appended to the decorator, in order, so line 2 compares the decorator and W after the same history; with line 2 the decorator holds no list of its own (Java's events(), size() and isEmpty() call the delegate). The clause of AC5 on events() and the sixth quoted sentence were added under ruling D20: they restate what Java, the only implementation, does. size() and isEmpty() are not named by the spec and not modelled. Line 2 quantifies over every history, clears included, so a clear() the decorator provided would have to leave events() as a clear on the wrapped store does; Java's decorator provides none, and the block does not constrain hasClear."
          "AC6 (reports itself as enabled whatever store it wraps) is line 3 and the last quoted sentence, both added under ruling D20 as what Java does. It is what makes EventStore.logging(), the decorator around the noop store, log anything: an executor appends only to a store that reports itself enabled (the glossary's storeSink, EVT-020 AC3), so a decorator that reported the noop store's flag would receive no event. Java's LoggingEventStore.isEnabled() returns true (EventStore.java:355-358; LoggingEventStoreTest.shouldAlwaysBeEnabled). evt023_sink states the consequence; evt023_not_noop shows that the decorator around any store is not a noop store, which is EVT-022's mutant evt022_discardEnabled."
          "Scope: Java only. TypeScript, Rust and the Python binding have no logging store, as the implementation notes say; the requirement is a SHOULD. The implementation note naming SLF4J is out of date: the class logs through java.lang.System.Logger (EventStore.java:336), and the spec edit of this wave corrects it and adds the missing Python line (ruling D20, evt-c EVT-C11 item 4)."
          "The test derivation (run a net with the logging store and check the levels of the log output) is EVT_023_nonvacuous: the thirteen kinds appended through an executor's sink to the reference around the in-memory store give, with every level enabled, the log records at the table's levels in order, and with the framework at INFO only the WARN and INFO records; events() returns the thirteen events; the transition-first table gives other records."
  signoff "pending"
  statement : ∀ {E : Type}, (E → NetEventKind) → LogDecorator E → Prop :=
    fun kind D =>
      (∀ W th e, observed th (D.onAppend W th e) =
        observed th [.log (eventLogLevel (kind e)) e, .pass e]) ∧
      (∀ W h h', (D.over W).read h h' = W.read h h') ∧
      (∀ W, (D.over W).enabled = true)

/- The pinned readable form of EVT-023: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_023 : {E : Type} → (E → NetEventKind) → LogDecorator E → Prop :=
fun {E} kind D =>
  (∀ (W : StoreObs E) (th : LogLevel) (e : E),
      observed th (D.onAppend W th e) = observed th [LogEffect.log (eventLogLevel (kind e)) e, LogEffect.pass e]) ∧
    (∀ (W : StoreObs E) (h h' : List (StoreOp E)), (D.over W).read h h' = W.read h h') ∧
      ∀ (W : StoreObs E), (D.over W).enabled = true
-/
#guard_msgs in #print EVT_023

/-! ### The reference -/

/-- Java's guarded calls observe as the unguarded ones: the guard skips only calls at a level
the framework has disabled. -/
theorem guardedCalls_observed (th : LogLevel) (k : NetEventKind) (e : E) :
    observed th (guardedCalls NetEventKind.isWarnOrInfo th k e) =
      observed th [.log (eventLogLevel k) e, .pass e] := by
  cases th <;> cases k <;> rfl

/-- The reference logging decorator satisfies EVT-023 for every kind function: an append logs the
event at the level of its kind when that level is enabled and then passes it on, `events()` is
the wrapped store's, and it reports itself enabled around every store. -/
@[evidence holds EVT_023]
theorem EVT_023_reference {E : Type} (kind : E → NetEventKind) :
    EVT_023 kind (refLogStore kind) :=
  ⟨fun _ th e => guardedCalls_observed th (kind e) e, fun _ _ _ => rfl, fun _ => rfl⟩

/-! ### Consequences -/

/-- AC1: every failure kind (the set [EVT-030]'s `failures()` returns) is logged at WARN. -/
theorem eventLogLevel_failure (k : NetEventKind) (hk : k.isFailure = true) :
    eventLogLevel k = .warn := by
  cases k <;> simp_all [NetEventKind.isFailure, eventLogLevel]

/-- The test derivation on any decorator that meets EVT-023: the records the framework at `th`
writes for an executor's events are the events in order, each at the level of its kind, those at
a disabled level left out. -/
theorem evt023_logRecords {kind : E → NetEventKind} {D : LogDecorator E} (hD : EVT_023 kind D)
    (W : StoreObs E) (th : LogLevel) (tr : List E) :
    logRecords D W th tr =
      (tr.map fun e => (eventLogLevel (kind e), e)).filter fun r => r.1.loggableAt th := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    simp only [logRecords, List.flatMap_cons, hD.1 W th e] at ih ⊢
    rw [ih]
    cases h : (eventLogLevel (kind e)).loggableAt th <;> simp [observed, h]

/-- AC5: the wrapped store receives exactly the events appended to a decorator that meets
EVT-023, in order, whatever the threshold. -/
theorem evt023_passedOn {kind : E → NetEventKind} {D : LogDecorator E} (hD : EVT_023 kind D)
    (W : StoreObs E) (th : LogLevel) (tr : List E) : passedOn D W th tr = tr := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    simp only [passedOn, List.flatMap_cons, hD.1 W th e] at ih ⊢
    rw [ih]
    cases h : (eventLogLevel (kind e)).loggableAt th <;> simp [observed, h]

/-- AC6: an executor appends every event it emits to a decorator that meets EVT-023, whatever
store it wraps (the glossary's `storeSink`, [EVT-020] AC3), the noop store included. -/
theorem evt023_sink {kind : E → NetEventKind} {D : LogDecorator E} (hD : EVT_023 kind D)
    (W : StoreObs E) (tr : List E) : appended (storeSink (D.over W) tr) = tr :=
  storeSink_enabled (hD.2.2 W) tr

/-- A decorator that meets EVT-023 around a store that meets [EVT-021] returns every event an
executor emits, in emission order. -/
theorem evt023_over_mem {kind : E → NetEventKind} {D : LogDecorator E} (hD : EVT_023 kind D)
    {W : StoreObs E} (hW : EVT_021 W) (tr : List E) :
    (D.over W).read (storeSink (D.over W) tr) [] = tr := by
  simp only [storeSink, hD.2.2 W, if_true]
  rw [hD.2.1]
  exact evt021_appends hW tr

/-- A decorator that meets EVT-023 is not a noop store ([EVT-022]) around any store: it reports
itself enabled, as `EventStore.logging()` around the noop store does. -/
theorem evt023_not_noop {kind : E → NetEventKind} {D : LogDecorator E} (hD : EVT_023 kind D)
    (W : StoreObs E) : ¬ EVT_022 (D.over W) :=
  fun h => absurd ((hD.2.2 W).symm.trans h.2) (by decide)

/-- The reference decorator around the reference in-memory store is an in-memory store
([EVT-021]): `EventStore.logging(EventStore.inMemory())`. -/
theorem evt023_reference_mem (kind : E → NetEventKind) :
    EVT_021 ((refLogStore kind).over refMemStore) :=
  ⟨rfl, fun h e => retained_append_one h e, fun hc => absurd hc Bool.false_ne_true, rfl⟩

/-! ### Wrong decorators, one per load-bearing part -/

/-- The mutant reading of line 1 without the table: an append logs the event at some level
fixed by its kind, then passes it on; lines 2 and 3 kept. -/
def evt023_anyTable {E : Type} (kind : E → NetEventKind) (D : LogDecorator E) : Prop :=
  (∃ lv : NetEventKind → LogLevel, ∀ W th e,
    observed th (D.onAppend W th e) = observed th [.log (lv (kind e)) e, .pass e]) ∧
  (∀ W h h', (D.over W).read h h' = W.read h h') ∧
  (∀ W, (D.over W).enabled = true)

/-- The acceptance criteria as first written, with AC3 read first: the transition events,
`TransitionFailed`, `TransitionTimedOut` and `ActionTimedOut` among them, at DEBUG (clash
evt-c#3). -/
def transitionFirstLevel : NetEventKind → LogLevel
  | .executionStarted | .executionCompleted => .info
  | .transitionEnabled | .transitionClockRestarted | .transitionStarted | .transitionCompleted
  | .transitionFailed | .transitionTimedOut | .actionTimedOut => .debug
  | .tokenAdded | .tokenRemoved | .markingSnapshot | .logMessage => .trace

/-- A decorator with the transition-first table and no guard. -/
def evt023_transitionFirst {E : Type} (kind : E → NetEventKind) : LogDecorator E where
  onAppend _ _ e := [.log (transitionFirstLevel (kind e)) e, .pass e]
  over W := { enabled := true, hasClear := false, read := W.read }

/-- ✗ A decorator that logs the failure kinds at DEBUG (AC3 read literally) meets the reading
without the table and violates EVT-023 (line 1, the table): `TransitionFailed` is logged at
DEBUG, not WARN. -/
@[evidence mutant EVT_023]
theorem EVT_023_mutant_transitionFirst :
    evt023_anyTable id (evt023_transitionFirst id) ∧
      ¬ EVT_023 id (evt023_transitionFirst id) := by
  refine ⟨⟨⟨transitionFirstLevel, fun _ _ _ => rfl⟩, fun _ _ _ => rfl, fun _ => rfl⟩,
    fun h => ?_⟩
  have := h.1 refMemStore .trace .transitionFailed
  simp [evt023_transitionFirst, transitionFirstLevel, eventLogLevel, observed,
    LogLevel.loggableAt, LogLevel.rank] at this

/-- The mutant reading of line 1 without the order: an append makes the log call and the pass,
in either order; lines 2 and 3 kept. -/
def evt023_anyOrder {E : Type} (kind : E → NetEventKind) (D : LogDecorator E) : Prop :=
  (∀ W th e, (observed th (D.onAppend W th e)).Perm
    (observed th [.log (eventLogLevel (kind e)) e, .pass e])) ∧
  (∀ W h h', (D.over W).read h h' = W.read h h') ∧
  (∀ W, (D.over W).enabled = true)

/-- A decorator that passes the event to the wrapped store before logging it. -/
def evt023_passFirst {E : Type} (kind : E → NetEventKind) : LogDecorator E where
  onAppend _ _ e := [.pass e, .log (eventLogLevel (kind e)) e]
  over W := { enabled := true, hasClear := false, read := W.read }

/-- ✗ A decorator that passes the event on before logging it meets the reading without the order
and violates EVT-023 (line 1, AC5 "after logging"). -/
@[evidence mutant EVT_023]
theorem EVT_023_mutant_passFirst :
    evt023_anyOrder id (evt023_passFirst id) ∧ ¬ EVT_023 id (evt023_passFirst id) := by
  refine ⟨⟨fun _ th e => ?_, fun _ _ _ => rfl, fun _ => rfl⟩, fun h => ?_⟩
  · dsimp only [evt023_passFirst]
    cases th <;> cases e <;> decide
  · have := h.1 refMemStore .trace .tokenAdded
    simp [evt023_passFirst, observed, eventLogLevel, LogLevel.loggableAt, LogLevel.rank] at this

/-- The mutant reading of line 1 as AC1 to AC4 alone: an append logs the event at the level of
its kind when that level is enabled; lines 2 and 3 kept. -/
def evt023_logsOnly {E : Type} (kind : E → NetEventKind) (D : LogDecorator E) : Prop :=
  (∀ W th e, (eventLogLevel (kind e)).loggableAt th = true →
    LogEffect.log (eventLogLevel (kind e)) e ∈ D.onAppend W th e) ∧
  (∀ W h h', (D.over W).read h h' = W.read h h') ∧
  (∀ W, (D.over W).enabled = true)

/-- A decorator that logs each event and never passes it to the wrapped store. -/
def evt023_swallow {E : Type} (kind : E → NetEventKind) : LogDecorator E where
  onAppend _ _ e := [.log (eventLogLevel (kind e)) e]
  over W := { enabled := true, hasClear := false, read := W.read }

/-- ✗ A decorator that logs and swallows the event meets the logging reading and violates
EVT-023 (line 1, the pass to the wrapped store). -/
@[evidence mutant EVT_023]
theorem EVT_023_mutant_swallow :
    evt023_logsOnly id (evt023_swallow id) ∧ ¬ EVT_023 id (evt023_swallow id) := by
  refine ⟨⟨fun _ _ _ _ => List.mem_singleton_self _, fun _ _ _ => rfl, fun _ => rfl⟩,
    fun h => ?_⟩
  have := h.1 refMemStore .trace .tokenAdded
  simp [evt023_swallow, observed, eventLogLevel, LogLevel.loggableAt, LogLevel.rank] at this

/-- The mutant reading of line 1 without "once": the observed effects are only the log call and
the pass, the log call comes before the pass, and each happens at least once; lines 2 and 3
kept. -/
def evt023_noOnce {E : Type} (kind : E → NetEventKind) (D : LogDecorator E) : Prop :=
  (∀ W th e,
    (∀ x ∈ observed th (D.onAppend W th e),
      x ∈ observed th [.log (eventLogLevel (kind e)) e, .pass e]) ∧
    (observed th [.log (eventLogLevel (kind e)) e, .pass e]).Sublist
      (observed th (D.onAppend W th e))) ∧
  (∀ W h h', (D.over W).read h h' = W.read h h') ∧
  (∀ W, (D.over W).enabled = true)

/-- A decorator that logs each event twice, then passes it once. -/
def evt023_logTwice {E : Type} (kind : E → NetEventKind) : LogDecorator E where
  onAppend _ _ e :=
    [.log (eventLogLevel (kind e)) e, .log (eventLogLevel (kind e)) e, .pass e]
  over W := { enabled := true, hasClear := false, read := W.read }

/-- ✗ A decorator that logs twice before the pass meets the reading without "once" and violates
EVT-023 (line 1, "log the event once"): a `TokenAdded` with every level enabled gives two TRACE
records. -/
@[evidence mutant EVT_023]
theorem EVT_023_mutant_logTwice :
    evt023_noOnce id (evt023_logTwice id) ∧ ¬ EVT_023 id (evt023_logTwice id) := by
  refine ⟨⟨fun _ th e => ?_, fun _ _ _ => rfl, fun _ => rfl⟩, fun h => ?_⟩
  · dsimp only [evt023_logTwice]
    cases th <;> cases e <;> decide
  · have := h.1 refMemStore .trace .tokenAdded
    simp [evt023_logTwice, observed, eventLogLevel, LogLevel.loggableAt, LogLevel.rank] at this

/-- A decorator that logs each event once, then passes it twice. -/
def evt023_passTwice {E : Type} (kind : E → NetEventKind) : LogDecorator E where
  onAppend _ _ e := [.log (eventLogLevel (kind e)) e, .pass e, .pass e]
  over W := { enabled := true, hasClear := false, read := W.read }

/-- ✗ A decorator that passes the event twice meets the reading without "once" and violates
EVT-023 (line 1, "pass the event once"): the wrapped store would hold every event twice. -/
@[evidence mutant EVT_023]
theorem EVT_023_mutant_passTwice :
    evt023_noOnce id (evt023_passTwice id) ∧ ¬ EVT_023 id (evt023_passTwice id) := by
  refine ⟨⟨fun _ th e => ?_, fun _ _ _ => rfl, fun _ => rfl⟩, fun h => ?_⟩
  · dsimp only [evt023_passTwice]
    cases th <;> cases e <;> decide
  · have := h.1 refMemStore .trace .tokenAdded
    simp [evt023_passTwice, observed, eventLogLevel, LogLevel.loggableAt, LogLevel.rank] at this

/-- The mutant reading of line 1 judged with every level enabled only (threshold TRACE), as if
the framework had no configuration; lines 2 and 3 kept. -/
def evt023_allLoggable {E : Type} (kind : E → NetEventKind) (D : LogDecorator E) : Prop :=
  (∀ W e, observed .trace (D.onAppend W .trace e) =
    observed .trace [.log (eventLogLevel (kind e)) e, .pass e]) ∧
  (∀ W h h', (D.over W).read h h' = W.read h h') ∧
  (∀ W, (D.over W).enabled = true)

/-- Java's early-return guard with `ActionTimedOut` left out, as when a kind is added to the level
switch but not to the guard. -/
def slipGuard : NetEventKind → Bool
  | .executionStarted | .executionCompleted | .transitionFailed | .transitionTimedOut => true
  | _ => false

/-- The reference with the slipped guard. -/
def evt023_slipGuard {E : Type} (kind : E → NetEventKind) : LogDecorator E where
  onAppend _ th e := guardedCalls slipGuard th (kind e) e
  over W := { enabled := true, hasClear := false, read := W.read }

/-- ✗ A decorator whose early return forgets `ActionTimedOut` logs as Java does with every level
enabled and violates EVT-023 (line 1, the threshold and the WARN row of the table): with the
framework at INFO it writes no WARN record for an `ActionTimedOut`. -/
@[evidence mutant EVT_023]
theorem EVT_023_mutant_slipGuard :
    evt023_allLoggable id (evt023_slipGuard id) ∧ ¬ EVT_023 id (evt023_slipGuard id) := by
  refine ⟨⟨fun _ e => ?_, fun _ _ _ => rfl, fun _ => rfl⟩, fun h => ?_⟩
  · cases e <;> rfl
  · have := h.1 refMemStore .info .actionTimedOut
    simp [evt023_slipGuard, guardedCalls, slipGuard, observed, eventLogLevel,
      LogLevel.loggableAt, LogLevel.rank] at this

/-- The mutant reading of line 1 judged around the in-memory store only, not around every
wrapped store; lines 2 and 3 kept. -/
def evt023_aroundMem {E : Type} (kind : E → NetEventKind) (D : LogDecorator E) : Prop :=
  (∀ th e, observed th (D.onAppend refMemStore th e) =
    observed th [.log (eventLogLevel (kind e)) e, .pass e]) ∧
  (∀ W h h', (D.over W).read h h' = W.read h h') ∧
  (∀ W, (D.over W).enabled = true)

/-- A decorator whose `append` returns at once when the wrapped store is not enabled (a guard
copied from the executor's skip-when-disabled path); it still reports itself enabled. -/
def evt023_gatedOnWrapped {E : Type} (kind : E → NetEventKind) : LogDecorator E where
  onAppend W th e := if W.enabled then guardedCalls NetEventKind.isWarnOrInfo th (kind e) e else []
  over W := { enabled := true, hasClear := false, read := W.read }

/-- ✗ A decorator that logs and passes nothing around a store that is not enabled meets line 1
around the in-memory store and violates EVT-023 (line 1, "whatever store it wraps"): around the
noop store, `EventStore.logging()`, it logs nothing. -/
@[evidence mutant EVT_023]
theorem EVT_023_mutant_gatedOnWrapped :
    evt023_aroundMem id (evt023_gatedOnWrapped id) ∧
      ¬ EVT_023 id (evt023_gatedOnWrapped id) := by
  refine ⟨⟨fun th e => ?_, fun _ _ _ => rfl, fun _ => rfl⟩, fun h => ?_⟩
  · exact guardedCalls_observed th e e
  · have := h.1 refNoopStore .trace .executionStarted
    simp [evt023_gatedOnWrapped, refNoopStore, observed] at this

/-- The mutant reading without line 2: lines 1 and 3 only. -/
def evt023_noDelegateRead {E : Type} (kind : E → NetEventKind) (D : LogDecorator E) : Prop :=
  (∀ W th e, observed th (D.onAppend W th e) =
    observed th [.log (eventLogLevel (kind e)) e, .pass e]) ∧
  (∀ W, (D.over W).enabled = true)

/-- A decorator that keeps its own list of the events appended to it and answers `events()` from
that list, not from the wrapped store. -/
def evt023_ownList {E : Type} (kind : E → NetEventKind) : LogDecorator E where
  onAppend _ _ e := [.log (eventLogLevel (kind e)) e, .pass e]
  over _ := { enabled := true, hasClear := false, read := fun h _ => retained h }

/-- ✗ A decorator with its own list meets lines 1 and 3 and violates EVT-023 (line 2): around the
noop store, `events()` returns an appended event the wrapped store discarded. -/
@[evidence mutant EVT_023]
theorem EVT_023_mutant_ownList :
    evt023_noDelegateRead id (evt023_ownList id) ∧ ¬ EVT_023 id (evt023_ownList id) := by
  refine ⟨⟨fun _ _ _ => rfl, fun _ => rfl⟩, fun h => ?_⟩
  have := h.2.1 refNoopStore [.append .tokenAdded] []
  simp [evt023_ownList, refNoopStore, retained, stepOp] at this

/-- The mutant reading without line 3: lines 1 and 2 only. -/
def evt023_noEnabled {E : Type} (kind : E → NetEventKind) (D : LogDecorator E) : Prop :=
  (∀ W th e, observed th (D.onAppend W th e) =
    observed th [.log (eventLogLevel (kind e)) e, .pass e]) ∧
  (∀ W h h', (D.over W).read h h' = W.read h h')

/-- A decorator that reports the wrapped store's enabled flag, as one whose `isEnabled()` calls
the delegate's. -/
def evt023_delegateEnabled {E : Type} (kind : E → NetEventKind) : LogDecorator E where
  onAppend _ _ e := [.log (eventLogLevel (kind e)) e, .pass e]
  over W := { enabled := W.enabled, hasClear := false, read := W.read }

/-- ✗ A decorator that reports the wrapped store's flag meets lines 1 and 2 and violates EVT-023
(line 3): around the noop store (`EventStore.logging()`) it reports itself not enabled, so an
executor appends nothing to it and nothing is logged. -/
@[evidence mutant EVT_023]
theorem EVT_023_mutant_delegateEnabled :
    evt023_noEnabled id (evt023_delegateEnabled id) ∧
      ¬ EVT_023 id (evt023_delegateEnabled id) := by
  refine ⟨⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun h => ?_⟩
  have := h.2.2 refNoopStore
  simp [evt023_delegateEnabled, refNoopStore] at this

/-! ### Non-vacuity: the test derivation on the reference -/

/-- The thirteen kinds, in the order of Java's `NetEvent` declaration. -/
def allNetEventKinds : List NetEventKind :=
  [.executionStarted, .executionCompleted, .transitionEnabled, .transitionClockRestarted,
   .transitionStarted, .transitionCompleted, .transitionFailed, .transitionTimedOut,
   .actionTimedOut, .tokenAdded, .tokenRemoved, .markingSnapshot, .logMessage]

/-- The test derivation on the reference (Java's `shouldAppendAllThirteenEventTypesWithoutThrowing`
with the levels checked): the thirteen kinds, appended through an executor's sink to the
reference decorator around the in-memory store, give log records at the table's levels in order
with every level enabled, and only the WARN and INFO records with the framework at INFO; the
wrapped store receives the thirteen events, and `events()` returns them; around the noop store
the decorator still reports itself enabled. The transition-first table gives other records, so
line 1 is not true of every decorator. -/
@[evidence nonvacuous EVT_023]
theorem EVT_023_nonvacuous :
    logRecords (refLogStore id) refMemStore .trace allNetEventKinds =
      [(.info, .executionStarted), (.info, .executionCompleted),
       (.debug, .transitionEnabled), (.debug, .transitionClockRestarted),
       (.debug, .transitionStarted), (.debug, .transitionCompleted),
       (.warn, .transitionFailed), (.warn, .transitionTimedOut), (.warn, .actionTimedOut),
       (.trace, .tokenAdded), (.trace, .tokenRemoved), (.trace, .markingSnapshot),
       (.trace, .logMessage)] ∧
    logRecords (refLogStore id) refMemStore .info allNetEventKinds =
      [(.info, .executionStarted), (.info, .executionCompleted),
       (.warn, .transitionFailed), (.warn, .transitionTimedOut), (.warn, .actionTimedOut)] ∧
    passedOn (refLogStore id) refMemStore .info allNetEventKinds = allNetEventKinds ∧
    ((refLogStore id).over refMemStore).read
        (storeSink ((refLogStore id).over refMemStore) allNetEventKinds) [] = allNetEventKinds ∧
    ((refLogStore (E := NetEventKind) id).over refNoopStore).enabled = true ∧
    logRecords (evt023_transitionFirst id) refMemStore .trace allNetEventKinds ≠
      logRecords (refLogStore id) refMemStore .trace allNetEventKinds := by
  decide

end Libpetri.Spec
