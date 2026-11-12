import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryEvents

set_option linter.missingDocs true

/-!
# RefReplay: the replay cache of the debug protocol

The witness model of [EVT-032] (`spec/08-events-observability.md`, the marking replay cache that
the debug protocol's seek and step commands read): Rust `libpetri-debug::MarkingCache`, the
Python binding over it, Java `org.libpetri.debug.MarkingCache` and TypeScript `MarkingCache` in
`libpetri/debug`.

## The vocabulary (namespace `Libpetri.Spec`)

The replay reads a recorded event stream only: it never runs a net and never reads an executor.
What it takes from each event is its **replay view** (`REv N`): the token counts of a
`MarkingSnapshot`, the place of a `TokenAdded` or `TokenRemoved`, the transition of a
`TransitionEnabled` or `TransitionStarted`, and the transition of one of the four end events
(`TransitionCompleted`, `TransitionFailed`, `TransitionTimedOut`, `ActionTimedOut`). Every other
event (`ExecutionStarted`, `ExecutionCompleted`, `TransitionClockRestarted`, `LogMessage`) is
`other`. The event type `E` is a parameter and `view : E → REv N` its projection. The table
above is `recView` over `RecEvent N`, the thirteen recorded events by name with the part the
replay can read (a `MarkingSnapshot` as the list of places it carries, an unlisted place counting
zero). The executor event model (`NetEvent`, wave W7) defines the full event type; its view is
`recView` after the map that forgets what the replay does not read (`NetEvent.toRec`,
`Reference/EventsLink.lean`), and `RecEvent.kind` reads the event glossary's one kind type.

The **replayed state** (`RState N`) is what a `ComputedState` shows, compared by value: the
token count of every place (`cnt`), and the enabled and in-flight transition names as two sets
(`en`, `fl`, membership functions). Sets, not lists: Java builds the two lists from a `HashSet`,
so a cached read and a full replay can list the same names in different orders (clash evt-c#12,
ruling D83 (a)). Transition names are strings, as in every runtime ([TIME-010]).

`applyEv` is the effect of one event, `replay view es` the fold of `applyEv` over `es` from the
empty state (`RState.empty`). A **cache** (`Cache N`) holds the replayed states at the indexes
`iv, 2 iv, 3 iv, …` (the snapshot interval `iv` is 256 in every runtime); it is **coherent**
with a stream `es` when snapshot `k` is the replay of the first `(k + 1) * iv` events of `es`.
One call of `compute_at(events, index)` is observed as a `CacheCall`: it takes the cache's
content before the call, the stream and the index, and returns the cache's content after the
call together with the state it answers.

Every term also has a form over an arbitrary step function (`replayWith`, `CoherentWith`,
`CallReplaysWith`, `refCallWith`): the mutants of the replay rules in `Spec/Req/EVT_032.lean`
are the reference built over a wrong step.

## The reference (`refReplayCall`)

The reference call is the runtimes' algorithm: it first extends the cache by the snapshots the
index needs that the stream already has (`extendWith`; Rust `ensure_cached_up_to`), then answers
from the highest snapshot at or below the index by replaying the events between it and the
index, and from the start of the stream when there is no such snapshot (`readWith`). An index
past the end of the stream is clamped to the end (Rust, Python and TypeScript; Java's
`subList` throws, clash evt-c#9, ruling D83 (a)). The reference builds each new snapshot from
the start of the stream rather than from the previous snapshot; both give the same state
(`replayWith_take_split`), and which one a runtime does is not observable.

`refCall_replays` is the whole content: for a cache coherent with the stream, the call answers
the replay of the first `min index (length)` events and leaves a cache coherent with the stream.
`coherentWith_append` adds that a cache stays coherent when the stream grows at its end, which
is how the debug stream changes between two calls when nothing is evicted.
-/

namespace Libpetri.Spec

variable {N E : Type}

/-! ## Replay view and replayed state -/

/-- **Glossary: Replay view** (proposed term). What the replay cache takes from one recorded
event ([EVT-032]). The event type is a parameter; its projection onto this type is the table in
the module docstring. -/
inductive REv (N : Type) where
  /-- `MarkingSnapshot`: the token count of every place, as the snapshot carries it ([EVT-014];
  a place the snapshot does not list counts zero). -/
  | snapshot (m : N → Nat)
  /-- `TokenAdded` on place `p` ([EVT-011]). -/
  | added (p : N)
  /-- `TokenRemoved` from place `p` ([EVT-012]). -/
  | removed (p : N)
  /-- `TransitionEnabled` of transition `t` ([EVT-004]). -/
  | enabled (t : String)
  /-- `TransitionStarted` of transition `t` ([EVT-006]). -/
  | started (t : String)
  /-- One of the four end events of transition `t`: `TransitionCompleted` ([EVT-007]),
  `TransitionFailed` ([EVT-008]), `TransitionTimedOut` ([EVT-009]) or `ActionTimedOut`
  ([EVT-010]). -/
  | ended (t : String)
  /-- Every other event: `ExecutionStarted`, `ExecutionCompleted`, `TransitionClockRestarted`,
  `LogMessage`. -/
  | other

/-- **Glossary: Replayed state** (proposed term). The state a replay of recorded events gives,
compared by value ([EVT-032], `ComputedState`): the token count of each place, and the enabled
and in-flight transition names as sets (membership functions), so that two states with the same
names in another list order are equal (clash evt-c#12). -/
structure RState (N : Type) where
  /-- The token count of each place. -/
  cnt : N → Nat
  /-- The enabled transitions: a `TransitionEnabled` seen and no `TransitionStarted` since. -/
  en : String → Bool
  /-- The in-flight transitions: a `TransitionStarted` seen and no end event since. -/
  fl : String → Bool

/-- The empty state: no token anywhere, no transition enabled or in flight. -/
def RState.empty : RState N := ⟨fun _ => 0, fun _ => false, fun _ => false⟩

/-- `f` with the value at `a` set to `b`. -/
def setAt {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-- Two replayed states are equal when their counts and their two name sets agree pointwise. -/
theorem RState.ext' {s t : RState N} (hc : ∀ p, s.cnt p = t.cnt p) (he : ∀ n, s.en n = t.en n)
    (hf : ∀ n, s.fl n = t.fl n) : s = t := by
  cases s; cases t
  simp only [RState.mk.injEq]
  exact ⟨funext hc, funext he, funext hf⟩

/-- **Glossary: Replay step** (proposed term). The effect of one event on the replayed state
([EVT-032]; Rust `apply_events`, Java and TypeScript `applyEvents`):

* a `MarkingSnapshot` replaces the token count of every place by the count it carries;
* a `TokenAdded` adds one token to its place;
* a `TokenRemoved` removes one token from its place, and does nothing on a place with none;
* a `TransitionEnabled` adds its transition to the enabled set;
* a `TransitionStarted` moves its transition from the enabled set to the in-flight set;
* each of the four end events removes its transition from the in-flight set;
* every other event leaves the state as it is. -/
def applyEv [DecidableEq N] (s : RState N) : REv N → RState N
  | .snapshot m => { s with cnt := m }
  | .added p => { s with cnt := setAt s.cnt p (s.cnt p + 1) }
  | .removed p => { s with cnt := setAt s.cnt p (s.cnt p - 1) }
  | .enabled t => { s with en := setAt s.en t true }
  | .started t => { s with en := setAt s.en t false, fl := setAt s.fl t true }
  | .ended t => { s with fl := setAt s.fl t false }
  | .other => s

/-- The fold of a step function over the views of `es`, from the state `s`. -/
def replayWith (step : RState N → REv N → RState N) (view : E → REv N) (s : RState N)
    (es : List E) : RState N :=
  es.foldl (fun s e => step s (view e)) s

/-- **Glossary: Replay** (proposed term). The state the events `es` give, replayed one by one
from the empty state ([EVT-032]: a from-scratch replay). -/
def replay [DecidableEq N] (view : E → REv N) (es : List E) : RState N :=
  replayWith applyEv view RState.empty es

/-! ## The recorded events by name -/

/-- The thirteen recorded events by name ([EVT-002] to [EVT-014]), each with the part the replay
can read: the transition name of a transition event, the place of a token event, and the
`(place, count)` list of a `MarkingSnapshot` as the runtimes carry it, which need not list every
place. The executor event model of wave W7 keeps more of each event (timestamps, token values,
outputs, errors); its replay view is `recView` after the map that forgets those fields. -/
inductive RecEvent (N : Type) where
  /-- `ExecutionStarted` ([EVT-002]). -/
  | executionStarted
  /-- `ExecutionCompleted` ([EVT-003]). -/
  | executionCompleted
  /-- `TransitionEnabled` ([EVT-004]). -/
  | transitionEnabled (t : String)
  /-- `TransitionClockRestarted` ([EVT-005]). -/
  | transitionClockRestarted (t : String)
  /-- `TransitionStarted` ([EVT-006]). -/
  | transitionStarted (t : String)
  /-- `TransitionCompleted` ([EVT-007]). -/
  | transitionCompleted (t : String)
  /-- `TransitionFailed` ([EVT-008]). -/
  | transitionFailed (t : String)
  /-- `TransitionTimedOut` ([EVT-009]). -/
  | transitionTimedOut (t : String)
  /-- `ActionTimedOut` ([EVT-010]). -/
  | actionTimedOut (t : String)
  /-- `TokenAdded` ([EVT-011]). -/
  | tokenAdded (p : N)
  /-- `TokenRemoved` ([EVT-012]). -/
  | tokenRemoved (p : N)
  /-- `LogMessage` ([EVT-013]). -/
  | logMessage
  /-- `MarkingSnapshot` ([EVT-014]): the places it carries with their token counts. -/
  | markingSnapshot (l : List (N × Nat))

/-- The name of a recorded event, as the spec writes it. -/
def RecEvent.name : RecEvent N → String
  | .executionStarted => "ExecutionStarted"
  | .executionCompleted => "ExecutionCompleted"
  | .transitionEnabled _ => "TransitionEnabled"
  | .transitionClockRestarted _ => "TransitionClockRestarted"
  | .transitionStarted _ => "TransitionStarted"
  | .transitionCompleted _ => "TransitionCompleted"
  | .transitionFailed _ => "TransitionFailed"
  | .transitionTimedOut _ => "TransitionTimedOut"
  | .actionTimedOut _ => "ActionTimedOut"
  | .tokenAdded _ => "TokenAdded"
  | .tokenRemoved _ => "TokenRemoved"
  | .logMessage => "LogMessage"
  | .markingSnapshot _ => "MarkingSnapshot"

/-- The kind of a recorded event: the event glossary's one kind type (`NetEventKind`), which the
logging store's level table ([EVT-023]) and the query helpers ([EVT-030]) read too. -/
def RecEvent.kind : RecEvent N → NetEventKind
  | .executionStarted => .executionStarted
  | .executionCompleted => .executionCompleted
  | .transitionEnabled _ => .transitionEnabled
  | .transitionClockRestarted _ => .transitionClockRestarted
  | .transitionStarted _ => .transitionStarted
  | .transitionCompleted _ => .transitionCompleted
  | .transitionFailed _ => .transitionFailed
  | .transitionTimedOut _ => .transitionTimedOut
  | .actionTimedOut _ => .actionTimedOut
  | .tokenAdded _ => .tokenAdded
  | .tokenRemoved _ => .tokenRemoved
  | .logMessage => .logMessage
  | .markingSnapshot _ => .markingSnapshot

/-- Every event kind is the kind of a recorded event (over any non-empty set of places): the
recorded events name the same thirteen kinds. -/
theorem RecEvent.kind_surjective [Inhabited N] : ∀ k : NetEventKind, ∃ e : RecEvent N, e.kind = k
  | .executionStarted => ⟨.executionStarted, rfl⟩
  | .executionCompleted => ⟨.executionCompleted, rfl⟩
  | .transitionEnabled => ⟨.transitionEnabled "", rfl⟩
  | .transitionClockRestarted => ⟨.transitionClockRestarted "", rfl⟩
  | .transitionStarted => ⟨.transitionStarted "", rfl⟩
  | .transitionCompleted => ⟨.transitionCompleted "", rfl⟩
  | .transitionFailed => ⟨.transitionFailed "", rfl⟩
  | .transitionTimedOut => ⟨.transitionTimedOut "", rfl⟩
  | .actionTimedOut => ⟨.actionTimedOut "", rfl⟩
  | .tokenAdded => ⟨.tokenAdded default, rfl⟩
  | .tokenRemoved => ⟨.tokenRemoved default, rfl⟩
  | .markingSnapshot => ⟨.markingSnapshot [], rfl⟩
  | .logMessage => ⟨.logMessage, rfl⟩

/-- **The replay view of the recorded events** ([EVT-032], the third quoted sentence by name): a
`MarkingSnapshot` gives the count it carries for each place it lists and zero for every other
place (Rust `marking.clear()`, Java and TypeScript `marking.clear()` before the insert); the four
end events (`TransitionCompleted`, `TransitionFailed`, `TransitionTimedOut`, `ActionTimedOut`)
are `ended`; `ExecutionStarted`, `ExecutionCompleted`, `TransitionClockRestarted` and
`LogMessage` are `other`. -/
def recView [DecidableEq N] : RecEvent N → REv N
  | .markingSnapshot l => .snapshot (fun p => (l.lookup p).getD 0)
  | .tokenAdded p => .added p
  | .tokenRemoved p => .removed p
  | .transitionEnabled t => .enabled t
  | .transitionStarted t => .started t
  | .transitionCompleted t => .ended t
  | .transitionFailed t => .ended t
  | .transitionTimedOut t => .ended t
  | .actionTimedOut t => .ended t
  | .executionStarted => .other
  | .executionCompleted => .other
  | .transitionClockRestarted _ => .other
  | .logMessage => .other

/-! ## Cache and calls -/

/-- The content of a replay cache: the snapshot interval `iv` and the snapshots, snapshot `k`
standing for the event index `(k + 1) * iv` (Rust, Java and TypeScript `snapshots`). -/
structure Cache (N : Type) where
  /-- The snapshot interval (256 in every runtime). -/
  iv : Nat
  /-- The snapshots, oldest first. -/
  snaps : List (RState N)

/-- `c` is coherent with `es` for the step function `step`: every snapshot `k` stands for an
index inside `es` and is the replay of the first `(k + 1) * iv` events of `es`. -/
def Cache.CoherentWith (step : RState N → REv N → RState N) (view : E → REv N) (c : Cache N)
    (es : List E) : Prop :=
  ∀ k s, c.snaps[k]? = some s →
    (k + 1) * c.iv ≤ es.length ∧ s = replayWith step view RState.empty (es.take ((k + 1) * c.iv))

/-- **Glossary: Coherent cache** (proposed term). Every snapshot of `c` is the replay of the
events of `es` up to its index ([EVT-032]). A cache the runtime filled from earlier calls on the
same stream is coherent with it, and stays so when the stream grows at its end
(`coherentWith_append`); a stream that changed in any other way (another session, a debug store
that evicted its oldest events and so shifted every index) needs `invalidate()`, which empties
the cache (`coherent_nil`). -/
def Cache.Coherent [DecidableEq N] (view : E → REv N) (c : Cache N) (es : List E) : Prop :=
  c.CoherentWith applyEv view es

/-- One call of `compute_at(events, index)` on a replay cache: from the cache's content before
the call, the stream and the index, the cache's content after the call and the state answered. -/
abbrev CacheCall (N E : Type) := Cache N → List E → Nat → Cache N × RState N

/-- The two lines of [EVT-032] over the step function `step`: for a cache coherent with the
stream, a call answers the replay of the first `i` events and leaves a cache coherent with the
stream. `EVT_032 view call` is `CallReplaysWith applyEv view call`. -/
def CallReplaysWith (step : RState N → REv N → RState N) (view : E → REv N)
    (call : CacheCall N E) : Prop :=
  ∀ c es i, c.CoherentWith step view es →
    (call c es i).2 = replayWith step view RState.empty (es.take i) ∧
      (call c es i).1.CoherentWith step view es

/-! ## Lemmas on the replay and on coherence -/

/-- Replaying `es ++ es'` is replaying `es'` from the state `es` gives. -/
theorem replayWith_append (step : RState N → REv N → RState N) (view : E → REv N)
    (s : RState N) (es es' : List E) :
    replayWith step view s (es ++ es') = replayWith step view (replayWith step view s es) es' := by
  simp [replayWith, List.foldl_append]

/-- The replay of the first `j` events is the replay of the first `m ≤ j` events followed by the
replay of the events between `m` and `j`: a snapshot plus its delta. -/
theorem replayWith_take_split (step : RState N → REv N → RState N) (view : E → REv N)
    (es : List E) {m j : Nat} (h : m ≤ j) :
    replayWith step view RState.empty (es.take j) =
      replayWith step view (replayWith step view RState.empty (es.take m)) ((es.take j).drop m) := by
  rw [← replayWith_append]
  congr 1
  have : es.take m = (es.take j).take m := by rw [List.take_take, Nat.min_eq_left h]
  rw [this, List.take_append_drop]

/-- `take` at an index clamped to the length is `take` at the index. -/
theorem take_min_length {α : Type} (l : List α) (i : Nat) :
    l.take (min i l.length) = l.take i := by
  rcases Nat.le_total i l.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_length, List.take_of_length_le h]

/-- The empty cache (the one `invalidate()` leaves) is coherent with every stream. -/
theorem coherent_nil (step : RState N → REv N → RState N) (view : E → REv N) (iv : Nat)
    (es : List E) : (Cache.mk iv []).CoherentWith step view es := by
  intro k s hk
  simp at hk

/-- A cache coherent with a stream stays coherent when the stream grows at its end. -/
theorem coherentWith_append (step : RState N → REv N → RState N) (view : E → REv N)
    {c : Cache N} {es : List E} (hc : c.CoherentWith step view es) (more : List E) :
    c.CoherentWith step view (es ++ more) := by
  intro k s hk
  obtain ⟨hle, rfl⟩ := hc k s hk
  refine ⟨by simp; omega, ?_⟩
  rw [List.take_append_of_le_length hle]

/-! ## The reference call -/

/-- The snapshots `k, k + 1, …, k + n - 1` of `es`, each the replay of the events up to its
index. -/
def snapsFrom (step : RState N → REv N → RState N) (view : E → REv N) (iv : Nat) (es : List E)
    (k n : Nat) : List (RState N) :=
  (List.range' k n).map fun j => replayWith step view RState.empty (es.take ((j + 1) * iv))

/-- The cache after the extension step of a call at index `i` (Rust `ensure_cached_up_to`, Java
and TypeScript `ensureCachedUpTo`): the snapshots up to the index that the stream already
reaches are added, and the snapshots already there are kept. -/
def extendWith (step : RState N → REv N → RState N) (view : E → REv N) (c : Cache N)
    (es : List E) (i : Nat) : Cache N :=
  let want := min (i / c.iv) (es.length / c.iv)
  { c with snaps := c.snaps ++ snapsFrom step view c.iv es c.snaps.length (want - c.snaps.length) }

/-- The answer of a call at index `i` from the cache `c`: the index is clamped to the length of
the stream; the events between the highest snapshot at or below it and the index are replayed
from that snapshot, and all events up to the index from the empty state when there is no such
snapshot. -/
def readWith (step : RState N → REv N → RState N) (view : E → REv N) (c : Cache N) (es : List E)
    (i : Nat) : RState N :=
  let j := min i es.length
  match min (j / c.iv) c.snaps.length with
  | 0 => replayWith step view RState.empty (es.take j)
  | k + 1 =>
    match c.snaps[k]? with
    | none => replayWith step view RState.empty (es.take j)
    | some s => replayWith step view s ((es.take j).drop ((k + 1) * c.iv))

/-- The reference call over a step function: extend the cache, then read from it. -/
def refCallWith (step : RState N → REv N → RState N) (view : E → REv N) : CacheCall N E :=
  fun c es i =>
    let c' := extendWith step view c es i
    (c', readWith step view c' es i)

/-- **The reference replay cache** ([EVT-032]): the runtimes' `compute_at` over the replay step
`applyEv`. -/
def refReplayCall [DecidableEq N] (view : E → REv N) : CacheCall N E :=
  refCallWith applyEv view

#spec_witness refReplayCall

/-- The extension step keeps a cache coherent with the stream it reads. -/
theorem extendWith_coherent (step : RState N → REv N → RState N) (view : E → REv N)
    {c : Cache N} {es : List E} (hc : c.CoherentWith step view es) (i : Nat) :
    (extendWith step view c es i).CoherentWith step view es := by
  intro k s hk
  simp only [extendWith] at hk
  rcases Nat.lt_or_ge k c.snaps.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk
    exact hc k s hk
  · rw [List.getElem?_append_right hge] at hk
    simp only [snapsFrom, List.getElem?_map] at hk
    by_cases hn : k - c.snaps.length < min (i / c.iv) (es.length / c.iv) - c.snaps.length
    · rw [List.getElem?_range' hn] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      subst hk
      have hk' : c.snaps.length + 1 * (k - c.snaps.length) = k := by omega
      rw [hk']
      refine ⟨?_, rfl⟩
      have h1 : k + 1 ≤ es.length / c.iv := by
        have := Nat.min_le_right (i / c.iv) (es.length / c.iv)
        omega
      calc (k + 1) * c.iv ≤ es.length / c.iv * c.iv := Nat.mul_le_mul_right _ h1
        _ ≤ es.length := Nat.div_mul_le_self _ _
    · rw [List.getElem?_eq_none (by simp; omega)] at hk
      simp at hk

/-- The read answers the replay of the first `i` events from every cache whose snapshots at an
index no greater than the length of the stream are the replay up to their index: the read never
takes a snapshot above the clamped index, so a snapshot past the end is never read. -/
theorem readWith_replay_of (step : RState N → REv N → RState N) (view : E → REv N)
    {c : Cache N} {es : List E}
    (hc : ∀ k s, c.snaps[k]? = some s → (k + 1) * c.iv ≤ es.length →
      s = replayWith step view RState.empty (es.take ((k + 1) * c.iv)))
    (i : Nat) :
    readWith step view c es i = replayWith step view RState.empty (es.take i) := by
  simp only [readWith]
  generalize hj : min i es.length = j
  have hje : es.take i = es.take j := by rw [← hj, take_min_length]
  have hjl : j ≤ es.length := by rw [← hj]; exact Nat.min_le_right _ _
  rw [hje]
  generalize hslot : min (j / c.iv) c.snaps.length = slot
  cases slot with
  | zero => rfl
  | succ k =>
    cases hk : c.snaps[k]? with
    | none => simp only [hk]
    | some s =>
      simp only [hk]
      have hle : (k + 1) * c.iv ≤ j := by
        have : k + 1 ≤ j / c.iv := by rw [← hslot]; exact Nat.min_le_left _ _
        calc (k + 1) * c.iv ≤ (j / c.iv) * c.iv := Nat.mul_le_mul_right _ this
          _ ≤ j := Nat.div_mul_le_self _ _
      obtain rfl := hc k s hk (Nat.le_trans hle hjl)
      exact (replayWith_take_split step view es hle).symm

/-- The read answers the replay of the first `i` events from every cache coherent with the
stream: the snapshot plus the delta is the from-scratch replay, and an index past the end reads
the whole stream. -/
theorem readWith_replay (step : RState N → REv N → RState N) (view : E → REv N)
    {c : Cache N} {es : List E} (hc : c.CoherentWith step view es) (i : Nat) :
    readWith step view c es i = replayWith step view RState.empty (es.take i) :=
  readWith_replay_of step view (fun k s hk _ => (hc k s hk).2) i

/-- ✓ The reference call over any step function meets both lines over that step function. -/
theorem refCall_replays (step : RState N → REv N → RState N) (view : E → REv N) :
    CallReplaysWith step view (refCallWith step view) := by
  intro c es i hc
  have hc' := extendWith_coherent step view hc i
  exact ⟨readWith_replay step view hc' i, hc'⟩

/-! ## Facts about the replayed state -/

/-- The replay's enabled set is not the glossary's Enabled set ([EVT-032], clash evt-c#10,
ruling D83 (a): an over-approximation): after `T1` and `T2` are enabled and `T1` starts taking
the token both needed, no event removes `T2`, and the replay still lists it as enabled. -/
theorem replay_enabled_overapprox :
    (replay (N := Nat) id
      [.enabled "T1", .enabled "T2", .removed 0, .started "T1"]).en "T2" = true := by
  decide

/-- A replayed stream without a `MarkingSnapshot` counts only the tokens its `TokenAdded` events
add: a `TokenRemoved` of a token the stream never reported added does nothing (clash evt-c#11;
a Rust or Python stream reports no initial token). -/
theorem replay_no_initial :
    (replay (N := Nat) (E := REv Nat) id [.removed 0, .added 1]).cnt 0 = 0 ∧
    (replay (N := Nat) (E := REv Nat) id [.snapshot (fun p => if p = 0 then 1 else 0),
      .removed 0, .added 1]).cnt 1 = 1 := by
  decide

end Libpetri.Spec
