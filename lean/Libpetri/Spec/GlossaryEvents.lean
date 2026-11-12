import Libpetri.Spec.Registry

set_option linter.missingDocs true

/-!
# Glossary: events (the event model, wave W7)

The vocabulary the event requirements use ([EVT-001] to [EVT-014] for the events an executor
emits, [EVT-020] to [EVT-032] for the stores, queries and replays that read them,
`spec/08-events-observability.md`). It holds the event values only and imports no executor, so
the store tier reads it without depending on the executor model.

* `NetEventKind`: the thirteen kinds of net event, and `NetEventKind.isFailure`, the one failure
  set ([EVT-023]'s WARN kinds and [EVT-030]'s `failures()`).
* `LogLevel`: the five levels a log message or a logging store uses ([EVT-013], [EVT-023]).
* `EventShape`: what every executor's events carry and what a query reads: the kind, the
  transition name, the place name ([EVT-030]).
* `NetEvent N T`: an event with the payload Java and TypeScript carry, over places `N` and tokens `T`
  (ruling D38 (a)). Rust and Python events carry less (no token unless the store captures
  tokens, no durations, no deadline or elapsed time); a requirement for every executor reads an
  event only through its kind, transition name and place (`NetEvent.kind`, `NetEvent.trans?`, `NetEvent.place?`),
  and a payload line is a companion block scoped to the executors whose events carry the field.
* Event-list terms read by several blocks: `removedAt`, `removedCount`, `addedAt`,
  `addedCount`, `kindCount`, `NetEvent.isLog`, `NetEvent.isOrch`.

What is not modelled: timestamps (every event carries one; the epoch clock is the CORE-011
slice), the execution ID and net name of the lifecycle events, the error message and type of a
failure, the logger name and throwable of a log message, the total duration of a run and the
budget of an action timeout (the reference executor records neither the run's start reading nor
the duration of a `Timeout` node).

The executor that emits these events is `EvExec` (`Reference/Events.lean`): a step of the
reference executor `RefExec` together with the events it appends.
-/

namespace Libpetri.Spec

/-! ## Kinds and levels -/

/-- The levels of a log message ([EVT-013]) and of the platform's logging framework a logging
store logs at ([EVT-023]; Java `System.Logger.Level`, the decorator never uses ERROR). -/
inductive LogLevel where
  /-- TRACE. -/
  | trace
  /-- DEBUG. -/
  | debug
  /-- INFO. -/
  | info
  /-- WARN (Java `Level.WARNING`). -/
  | warn
  /-- ERROR. -/
  | error
  deriving DecidableEq, Repr

/-- The severity of a level, least severe first (`System.Logger.Level` is ordered the same
way). -/
def LogLevel.rank : LogLevel → Nat
  | .trace => 0
  | .debug => 1
  | .info => 2
  | .warn => 3
  | .error => 4

/-- Whether the logging framework, configured at the threshold `th`, has the level `l` enabled:
`l` is `th` or more severe (`System.Logger.isLoggable`). -/
def LogLevel.loggableAt (l th : LogLevel) : Bool := decide (th.rank ≤ l.rank)

/-- **Glossary: Event kind** (proposed term). The thirteen kinds of net event ([EVT-002] to
[EVT-014]; Java's sealed `NetEvent`, the same thirteen variants in TypeScript, Rust and Python).
The one kind type of the event model: the executor events (`NetEvent.kind`), the logging store's level
table ([EVT-023]), the query helpers' event types ([EVT-030]) and the replay's recorded events
(`RecEvent.kind`, [EVT-032]) all read it. -/
inductive NetEventKind where
  /-- `ExecutionStarted` ([EVT-002]). -/
  | executionStarted
  /-- `ExecutionCompleted` ([EVT-003]). -/
  | executionCompleted
  /-- `TransitionEnabled` ([EVT-004]). -/
  | transitionEnabled
  /-- `TransitionClockRestarted` ([EVT-005]). -/
  | transitionClockRestarted
  /-- `TransitionStarted` ([EVT-006]). -/
  | transitionStarted
  /-- `TransitionCompleted` ([EVT-007]). -/
  | transitionCompleted
  /-- `TransitionFailed` ([EVT-008]). -/
  | transitionFailed
  /-- `TransitionTimedOut` ([EVT-009]). -/
  | transitionTimedOut
  /-- `ActionTimedOut` ([EVT-010]). -/
  | actionTimedOut
  /-- `TokenAdded` ([EVT-011]). -/
  | tokenAdded
  /-- `TokenRemoved` ([EVT-012]). -/
  | tokenRemoved
  /-- `MarkingSnapshot` ([EVT-014]). -/
  | markingSnapshot
  /-- `LogMessage` ([EVT-013]). -/
  | logMessage
  deriving DecidableEq, Repr

/-- **Glossary: Failure event** (proposed term). The failure kinds: `TransitionFailed`,
`TransitionTimedOut` and `ActionTimedOut`. The one failure set of the event model: the kinds the
logging store logs at WARN ([EVT-023]) and the events `failures()` returns ([EVT-030]); all four
runtimes test the same three kinds (`EventStore.java` `failures`, `net-event.ts`
`isFailureEvent`, `net_event.rs` `is_failure`). -/
def NetEventKind.isFailure : NetEventKind → Bool
  | .transitionFailed | .transitionTimedOut | .actionTimedOut => true
  | _ => false

/-- What a query reads of an event ([EVT-030]): its kind, the transition name it carries and the
place name it carries. In every runtime the eight transition kinds carry a transition name field
(LogMessage included), the two token kinds carry a place name, and the other kinds carry neither
(`rust/libpetri-event/src/net_event.rs` `transition_name` and `place_name`). An engine diagnostic
fills the name field with the empty name in all four runtimes (the initial-marking seam), and
with `null` in Java on an interrupted run; [EVT-030]'s line 1 holds the same whether the shape
reads the empty name as no name or not (`EVT_030_allows_emptySentinel`). -/
structure EventShape where
  /-- The event kind. -/
  type : NetEventKind
  /-- The transition name the event carries, if any. -/
  transition : Option String := none
  /-- The place name the event carries, if any. -/
  place : Option String := none
  deriving DecidableEq, Repr

/-! ## Events -/

/-- **Glossary: Event** (proposed term). One event an executor emits, with the payload Java and
TypeScript carry ([EVT-002] to [EVT-014], ruling D38 (a)), over place names `N` and tokens `T`;
transition names are strings, as in every runtime (ruling D10). An event is a value: it has no
identity and no field changes after it is built ([EVT-001]). Rust and Python carry the kind, the
transition name and the place name of every event, and a token only when the event store captures
tokens; the payload fields beyond the shape are read only by companion blocks scoped to the
executors that carry them. -/
inductive NetEvent (N T : Type) where
  /-- `ExecutionStarted` ([EVT-002]). -/
  | executionStarted
  /-- `ExecutionCompleted` ([EVT-003]); its total duration is not modelled (the executor state
  records no start reading). -/
  | executionCompleted
  /-- `TransitionEnabled` of transition `t` ([EVT-004]). -/
  | transitionEnabled (t : String)
  /-- `TransitionClockRestarted` of transition `t` ([EVT-005]). -/
  | transitionClockRestarted (t : String)
  /-- `TransitionStarted` of transition `t` with the tokens it removed, place by place
  ([EVT-006]). -/
  | transitionStarted (t : String) (removed : List (N × T))
  /-- `TransitionCompleted` of transition `t` with the tokens it produced and the time its action
  took, in firing-clock units ([EVT-007]). -/
  | transitionCompleted (t : String) (produced : List (N × T)) (dur : Nat)
  /-- `TransitionFailed` of transition `t` ([EVT-008]); message and exception type are not
  modelled. -/
  | transitionFailed (t : String)
  /-- `TransitionTimedOut` of transition `t`: its latest bound and its elapsed time when reaped
  ([EVT-009]). -/
  | transitionTimedOut (t : String) (deadline elapsed : Nat)
  /-- `ActionTimedOut` of transition `t` ([EVT-010]); the budget of the `Timeout` node is not
  modelled. -/
  | actionTimedOut (t : String)
  /-- `TokenAdded`: token `x` added to place `p` ([EVT-011]). -/
  | tokenAdded (p : N) (x : T)
  /-- `TokenRemoved`: token `x` removed from place `p` ([EVT-012]). -/
  | tokenRemoved (p : N) (x : T)
  /-- `MarkingSnapshot`: the places with their queues ([EVT-014]; the snapshot form of
  [CORE-073], `QSnap`). -/
  | markingSnapshot (m : List (N × List T))
  /-- `LogMessage` attributed to transition `t`, or to none ([EVT-013]). -/
  | logMessage (t : Option String) (level : LogLevel) (msg : String)
  deriving DecidableEq, Repr

namespace NetEvent

variable {N T : Type}

/-- The kind of an event. -/
def kind : NetEvent N T → NetEventKind
  | .executionStarted => .executionStarted
  | .executionCompleted => .executionCompleted
  | .transitionEnabled _ => .transitionEnabled
  | .transitionClockRestarted _ => .transitionClockRestarted
  | .transitionStarted .. => .transitionStarted
  | .transitionCompleted .. => .transitionCompleted
  | .transitionFailed _ => .transitionFailed
  | .transitionTimedOut .. => .transitionTimedOut
  | .actionTimedOut _ => .actionTimedOut
  | .tokenAdded .. => .tokenAdded
  | .tokenRemoved .. => .tokenRemoved
  | .markingSnapshot _ => .markingSnapshot
  | .logMessage .. => .logMessage

/-- The transition name an event carries: the seven transition kinds always, a log message when
it is attributed to one. -/
def trans? : NetEvent N T → Option String
  | .transitionEnabled t | .transitionClockRestarted t | .transitionStarted t _
  | .transitionCompleted t _ _ | .transitionFailed t | .transitionTimedOut t _ _
  | .actionTimedOut t => some t
  | .logMessage t _ _ => t
  | _ => none

/-- The place an event carries: `TokenAdded` and `TokenRemoved`. -/
def place? : NetEvent N T → Option N
  | .tokenAdded p _ | .tokenRemoved p _ => some p
  | _ => none

/-- The shape of an event, with place names given by `pn` ([EVT-030]): what every executor's
events carry and every query reads. -/
def toShape (pn : N → String) (e : NetEvent N T) : EventShape :=
  ⟨e.kind, e.trans?, e.place?.map pn⟩

/-- A log message ([EVT-013]). -/
def isLog (e : NetEvent N T) : Bool := e.kind == .logMessage

/-- **Glossary: Orchestrator event** (proposed term). An event the orchestrator loop emits: every
kind but `LogMessage` (an action's log) and `ActionTimedOut` (Java and TypeScript emit it from
the action's timer) ([EVT-003]). -/
def isOrch (e : NetEvent N T) : Bool :=
  e.kind != .logMessage && e.kind != .actionTimedOut

/-- The event is a `TokenRemoved` naming place `p`. It reads only the kind and the place of the
event (`removesFrom_iff`), so a line stated with it holds of every executor whose events carry
the place, whether or not they carry the token. -/
def removesFrom [DecidableEq N] (p : N) : NetEvent N T → Bool
  | .tokenRemoved q _ => decide (q = p)
  | _ => false

/-- The event is a `TokenAdded` naming place `p` (kind and place only). -/
def addsTo [DecidableEq N] (p : N) : NetEvent N T → Bool
  | .tokenAdded q _ => decide (q = p)
  | _ => false

/-- `removesFrom` reads the kind and the place of an event only. -/
theorem removesFrom_iff [DecidableEq N] (p : N) (e : NetEvent N T) :
    e.removesFrom p = true ↔ e.kind = .tokenRemoved ∧ e.place? = some p := by
  cases e <;> simp [removesFrom, kind, place?]

/-- `addsTo` reads the kind and the place of an event only. -/
theorem addsTo_iff [DecidableEq N] (p : N) (e : NetEvent N T) :
    e.addsTo p = true ↔ e.kind = .tokenAdded ∧ e.place? = some p := by
  cases e <;> simp [addsTo, kind, place?]

end NetEvent

/-! ## Event-list terms -/

section Lists

variable {N T : Type}

/-- The tokens of the `TokenRemoved` events of `evs` naming place `p`, in event order (the
payload [EVT-012] reads, where the event carries the token). -/
def removedAt [DecidableEq N] (evs : List (NetEvent N T)) (p : N) : List T :=
  evs.filterMap fun
    | .tokenRemoved q x => if q = p then some x else none
    | _ => none

/-- The number of `TokenRemoved` events of `evs` naming place `p` (kind and place only). -/
def removedCount [DecidableEq N] (evs : List (NetEvent N T)) (p : N) : Nat :=
  evs.countP (NetEvent.removesFrom p)

/-- The tokens of the `TokenAdded` events of `evs` naming place `p`, in event order. -/
def addedAt [DecidableEq N] (evs : List (NetEvent N T)) (p : N) : List T :=
  evs.filterMap fun
    | .tokenAdded q x => if q = p then some x else none
    | _ => none

/-- The number of `TokenAdded` events of `evs` naming place `p` (kind and place only). -/
def addedCount [DecidableEq N] (evs : List (NetEvent N T)) (p : N) : Nat :=
  evs.countP (NetEvent.addsTo p)

/-- The `TokenAdded` events of an emission, one per token, in emission order. -/
def addedEvs (e : List (N × T)) : List (NetEvent N T) := e.map fun x => .tokenAdded x.1 x.2

/-- The number of events of `evs` of kind `k`. -/
def kindCount (k : NetEventKind) (evs : List (NetEvent N T)) : Nat :=
  evs.countP fun e => e.kind == k

variable [DecidableEq N]

/-- The removed tokens of two event lists, one after the other. -/
theorem removedAt_append (a b : List (NetEvent N T)) (p : N) :
    removedAt (a ++ b) p = removedAt a p ++ removedAt b p := by
  simp [removedAt, List.filterMap_append]

/-- The removal counts of two event lists add up. -/
theorem removedCount_append (a b : List (NetEvent N T)) (p : N) :
    removedCount (a ++ b) p = removedCount a p + removedCount b p := by
  simp [removedCount, List.countP_append]

/-- The count of `TokenRemoved` events naming `p` is the number of tokens they carry: the count
form of a line is the token form with the tokens forgotten. -/
theorem removedCount_eq_length (evs : List (NetEvent N T)) (p : N) :
    removedCount evs p = (removedAt evs p).length := by
  induction evs with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | tokenRemoved q x =>
      by_cases h : q = p
      · simp [removedCount, removedAt, NetEvent.removesFrom, h] at ih ⊢; omega
      · simp [removedCount, removedAt, NetEvent.removesFrom, h] at ih ⊢; omega
    | _ => simpa [removedCount, removedAt, NetEvent.removesFrom] using ih

/-- An event list with no `TokenRemoved` event removes nothing from any place. -/
theorem removedAt_of_none (evs : List (NetEvent N T))
    (h : ∀ e ∈ evs, e.kind ≠ .tokenRemoved) (p : N) : removedAt evs p = [] := by
  rw [removedAt, List.filterMap_eq_nil_iff]
  intro e he
  cases e with
  | tokenRemoved q x => exact absurd rfl (h _ he)
  | _ => rfl

/-- The `TokenRemoved` events of the tokens `l` of place `q`, read at place `p`: `l` if `q = p`,
nothing otherwise. -/
theorem removedAt_map (l : List T) (q p : N) :
    removedAt (l.map (NetEvent.tokenRemoved q)) p = if q = p then l else [] := by
  induction l with
  | nil => simp [removedAt]
  | cons x xs ih =>
    by_cases h : q = p
    · simp only [removedAt, List.map_cons, List.filterMap_cons, h, if_true] at ih ⊢
      rw [ih]
    · simp only [removedAt, List.map_cons, List.filterMap_cons, h, if_false] at ih ⊢
      exact ih

/-- `TokenRemoved` events built place by place over a list of distinct places, read at `p`: the
tokens built for `p` if `p` is listed, nothing otherwise. -/
theorem removedAt_flatMap (f : N → List T) (ps : List N) (hn : ps.Nodup) (p : N) :
    removedAt (ps.flatMap fun q => (f q).map (NetEvent.tokenRemoved q)) p =
      if p ∈ ps then f p else [] := by
  induction ps with
  | nil => simp [removedAt]
  | cons q qs ih =>
    rw [List.flatMap_cons, removedAt_append, ih (List.nodup_cons.1 hn).2, removedAt_map]
    by_cases h : q = p
    · subst h; simp [(List.nodup_cons.1 hn).1]
    · have h' : p ≠ q := fun e => h e.symm
      simp [h, h']

end Lists

/-- An event is a value: a `TransitionStarted` event built with a list of removed tokens carries
exactly that list, so two such events are equal only when their lists are, and nothing done to
another list afterwards can reach it. For example, the event of transition `t` built with the
tokens `[(p, 1), (p, 2)]` differs from the one built with `[(p, 1)]`. -/
@[evidence cites "EVT-001" "All events are immutable value objects."]
theorem netEvent_value {N T : Type} (t : String) (xs ys : List (N × T)) :
    NetEvent.transitionStarted t xs = NetEvent.transitionStarted t ys ↔ xs = ys := by
  simp

end Libpetri.Spec
