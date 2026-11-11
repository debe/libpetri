import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryStore
import Libpetri.Spec.Req.EVT_022

set_option linter.missingDocs true

/-!
# EVT-021: InMemoryEventStore (`spec/08-events-observability.md`)

The in-memory store keeps every event appended to it, in the order of the appends. The
requirement is a predicate over the observation of one store, `S : StoreObs E` (glossary
`GlossaryStore.lean`): what a call of `events()` returns after a history of appends and clears,
whether the store provides `clear()`, and whether it reports itself enabled. A call of
`events()` is not an operation of a history; the fifth quoted sentence (a call changes nothing a
later call returns) is the premise that makes that observation describe the store, worded as a
statement and not as a line, and the section "Calls of `events()`" states it as a remark on
histories that do contain calls.

The witness is the reference in-memory store `refMemStore`. Ruling D29 (a) fixes two of the
four acceptance criteria to what every runtime does: what a returned list shows after later
operations is not specified (TypeScript returns its live array), and `clear()` is required only
where the store provides it (the Rust store and the Python binding have none). The runtime
shapes meet the block (`EVT_021_allows_live`, `EVT_021_allows_detached`,
`EVT_021_allows_noClear`). Ruling D20 (clash evt-c#14) reads the body's "chronological order" as
append order.

The wrong stores are a store that starts with an event already in it, a store that orders by
timestamp, a store whose `clear()` does nothing and a store that keeps every event but reports
itself not enabled (one mutant per line), and the last-in-first-out store, the bounded debug
store and the noop store; a store whose `events()` drains it does not meet the premise of the
fifth quoted sentence (`evt021_drain_not_callFree`). Three consequences tie the block to the rest of the store tier: a
history of appends only is returned in full and in order (the test derivation), with `clear()`
the store returns exactly the retained events, and an executor's events all reach it in
emission order (`storeSink`, [EVT-020] AC3).
-/

namespace Libpetri.Spec

/-! ## EVT-021: InMemoryEventStore -/

requirement EVT_021
  id "EVT-021"
  title "InMemoryEventStore"
  kind F
  scope "the in-memory event store (Java EventStore.inMemory(), TypeScript InMemoryEventStore, Rust InMemoryEventStore, Python InMemoryEventStore)"
  source verbatim "spec/08-events-observability.md"
  quote "A new in-memory event store *shall* return no event from `events()`."
        "*When* an event is appended to the in-memory event store, a call of `events()` made right after the append *shall* return the events that a call made right before the append returns, with that event added at the end."
        "*Where* the in-memory event store provides `clear()`, a call of `events()` made right after `clear()` *shall* return no event."
        "The in-memory event store *shall* report itself as enabled, so that an executor appends every event it emits to it (see [EVT-020]): `isEnabled()` returns true in Java and TypeScript, the store type's `ENABLED` constant is true in Rust, and the Python binding's store is written through a Rust store whose `ENABLED` constant is true."
        "A call of `events()` changes nothing that a later call of `events()` returns, so the sentences above speak of what a call returns after the appends and clears made so far."
  reading "For every store S over any event type E:"
          "after the empty history, a call of events() returns the empty list;"
          "for every history h and event e, a call of events() after h followed by append e returns what a call after h returns, with e added at the end;"
          "if S provides clear(), then for every history h a call of events() after h followed by clear returns the empty list;"
          "S reports itself as enabled."
  assumes "The model is the observation of one store, S : StoreObs E (glossary: Event store): its enabled flag, whether it provides clear(), and read h h', the list a call of events() made after the history h shows once the further operations h' have run. Every line reads h' = [] only, the list as returned, so the block says nothing about what a returned list shows after later operations (ruling D29 (a)). The event type E is a parameter: the lines say nothing about what an event holds."
          "The fifth quoted sentence is the premise of that model, not a line, and the markdown words it as a statement of what the observation assumes and not as a shall, as EVT-020 words the storeSink sentence: a history holds appends and clears only, so read h [] can stand for every call of events() after h only when a call changes nothing a later call returns, and no store in this model can fail it. Section 'Calls of events()' states it on histories that contain calls (evt021_CallFree): on a call-free store that meets the block, every call returns the events appended since the last clear (evt021_calls_retained), the reference is call-free (evt021_ref_callFree), and a store whose events() drains it (a poll() loop over Java's ConcurrentLinkedQueue in place of List.copyOf) meets the block on its first calls but is not call-free (evt021_drain_accepted, evt021_drain_not_callFree). Every runtime is call-free: Java returns List.copyOf, TypeScript returns its array, Rust's events() takes the store by shared reference, and the Python binding builds a new list under its mutex."
          "The body sentence (the store retains all events, in order) and AC1 (events are stored in insertion order) are lines 1 and 2 and the first two quoted sentences: by induction they give that a history of appends only is returned in full and in append order (evt021_appends), and with clear() that events() returns exactly the events appended since the last clear (evt021_read_retained). The order is append order: the body's earlier wording 'chronological order' is reworded to it under ruling D20 (clash evt-c#14), because event timestamps need not rise along the appends, and every runtime keeps the order of the appends (a ConcurrentLinkedQueue in Java, a pushed array in TypeScript, a pushed Vec in Rust and in the Python binding). A store that orders its events by timestamp (evt021_chronoStore) violates line 2."
          "AC2 (thread-safe append, concurrent callers do not lose events) is kind Q: a history is one linear order of operations, so no line can show a lost concurrent append. It matters in Java, whose store appends lock-free to a ConcurrentLinkedQueue from the orchestrator, action and timeout threads (java/src/main/java/org/libpetri/event/EventStore.java:252-273); Rust's append takes the store mutably and the Python binding locks a mutex around it (rust/libpetri-py/src/events.rs), and TypeScript runs on one thread. What line 2 does show is that no append, concurrent or not, is lost once it has run."
          "AC3 (events() returns the events appended since the last clear(), in append order; what a returned list shows after later operations is not specified) is lines 1 and 2 for the events it returns, through evt021_read_retained and evt021_appends. What a returned list shows later is not a line: ruling D29 (a) leaves the copy unspecified, because TypeScript's store returns its own array, which grows on later appends (typescript/src/event/event-store.ts:58-60; clash evt-c#1), while Java returns List.copyOf, Rust lends a borrowed slice that the borrow checker keeps from changing while it is held, and Python builds a new list. The block accepts every such later view, not only a copy or a live view: EVT_021_allows_live shows the live-array store, and EVT_021_allows_detached a TypeScript store whose clear() replaces its array, so a list returned earlier stops following the store. The spec edit of this wave rewords AC3 from 'a snapshot copy (not a live reference)' to that ruling."
          "AC4 (clear() for test reuse) is line 3 and the third quoted sentence, under ruling D29 (a): clear() is required only where the store provides it, and the spec edit of this wave rewords AC4 to say so. hasClear is read off the store's class, not off the type a factory returns: it is true for TypeScript's InMemoryEventStore and for Java's package-private InMemoryEventStore, whose public clear() is callable from its own package although EventStore.inMemory() returns it as the EventStore interface (java/src/main/java/org/libpetri/event/EventStore.java:195, :252, :271), and false for Rust's and the Python binding's stores, which have none (rust/libpetri-event/src/event_store.rs:67-86; python/libpetri/_libpetri.pyi; clash evt-c#2). So a Java clear() that does nothing is the store EVT_021_mutant_ignoreClear rejects. EVT_021_allows_noClear shows the store without clear() meets the block. A history with a clear made on a store without clear() is not one a caller can make; line 2 quantifies over every history and covers it anyway, which every runtime meets."
          "Line 4 and the fourth quoted sentence are a new sentence derived from 'retains all events' and stated with that derivation: an executor appends to a store only when it reports itself enabled (the glossary's storeSink, EVT-020 AC3, 'isEnabled() controls whether the executor appends events to the store'), so a store that keeps every append but reports itself not enabled would retain none of a run's events. All runtimes meet it: Java's in-memory store keeps the interface default isEnabled() = true, TypeScript's returns true, Rust's sets ENABLED = true, and the executor writes the Python binding's store through a Rust store whose ENABLED is true (rust/libpetri-py/src/events.rs, RunStore). evt021_sink states the consequence: every event an executor emits reaches a store that meets the block, in emission order."
          "Scope: the line is on the in-memory store, not on every store that keeps events. The bounded debug stores evict their oldest events (EVT-024) and violate line 2 (EVT_021_forbids_bounded); the noop store (EVT-022) violates lines 2 and 4 (EVT_021_forbids_noop), so no one store meets both blocks (evt021_not_noop) and the consistency theorem gives each its own store variable. The query helpers the runtimes offer on the store (filter, transitionEvents, failures, and the Python filters, limit and offset) are EVT-030's; size(), isEmpty() and len() are not named by the spec and not modelled."
          "The test derivation (append 100 events; events() returns 100 in order) is EVT_021_nonvacuous on the reference, which also shows the last-in-first-out store returning the same appends reversed."
  signoff "pending"
  statement : ∀ {E : Type}, StoreObs E → Prop :=
    fun {E} S =>
      S.read [] [] = [] ∧
      (∀ (h : List (StoreOp E)) (e : E), S.read (h ++ [StoreOp.append e]) [] = S.read h [] ++ [e]) ∧
      (S.hasClear = true → ∀ (h : List (StoreOp E)), S.read (h ++ [StoreOp.clear]) [] = []) ∧
      S.enabled = true

/- The pinned readable form of EVT-021: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_021 : {E : Type} → StoreObs E → Prop :=
fun {E} S =>
  S.read [] [] = [] ∧
    (∀ (h : List (StoreOp E)) (e : E), S.read (h ++ [StoreOp.append e]) [] = S.read h [] ++ [e]) ∧
      (S.hasClear = true → ∀ (h : List (StoreOp E)), S.read (h ++ [StoreOp.clear]) [] = []) ∧ S.enabled = true
-/
#guard_msgs in #print EVT_021

/-! ### The reference -/

/-- The reference in-memory store satisfies EVT-021: it starts empty, adds each appended event at
the end, is empty after a clear and reports itself enabled. -/
@[evidence holds EVT_021]
theorem EVT_021_reference {E : Type} : EVT_021 (refMemStore (E := E)) :=
  ⟨rfl, fun h e => retained_append_one h e, fun _ h => retained_append_clear h, rfl⟩

/-! ### Consequences -/

/-- The test derivation on any store that meets EVT-021: after a history of appends only,
`events()` returns exactly those events, in append order. No `clear()` is needed. -/
theorem evt021_appends {E : Type} {S : StoreObs E} (hS : EVT_021 S) (es : List E) :
    S.read (es.map StoreOp.append) [] = es := by
  have key : ∀ (es : List E) (h₀ : List (StoreOp E)),
      S.read (h₀ ++ es.map StoreOp.append) [] = S.read h₀ [] ++ es := by
    intro es
    induction es with
    | nil => intro h₀; simp
    | cons e es ih =>
      intro h₀
      have := ih (h₀ ++ [StoreOp.append e])
      rw [hS.2.1] at this
      simpa using this
  simpa [hS.1] using key es []

/-- On a store that meets EVT-021 and provides `clear()`, `events()` returns exactly the
retained events: those appended since the last clear, in append order. -/
theorem evt021_read_retained {E : Type} {S : StoreObs E} (hS : EVT_021 S)
    (hc : S.hasClear = true) (h : List (StoreOp E)) : S.read h [] = retained h := by
  have step : ∀ (h₀ : List (StoreOp E)) (op : StoreOp E),
      S.read (h₀ ++ [op]) [] = stepOp (S.read h₀ []) op := by
    intro h₀ op
    cases op with
    | append e => exact hS.2.1 h₀ e
    | clear => exact hS.2.2.1 hc h₀
  have key : ∀ (h h₀ : List (StoreOp E)),
      S.read (h₀ ++ h) [] = h.foldl stepOp (S.read h₀ []) := by
    intro h
    induction h with
    | nil => intro h₀; simp
    | cons op h ih =>
      intro h₀
      have := ih (h₀ ++ [op])
      rw [step] at this
      simpa using this
  simpa [hS.1, retained] using key h []

/-- Every event an executor emits reaches a store that meets EVT-021, in emission order
([EVT-020] AC3, through the glossary's `storeSink`). -/
theorem evt021_sink {E : Type} {S : StoreObs E} (hS : EVT_021 S) (tr : List E) :
    S.read (storeSink S tr) [] = tr := by
  simp only [storeSink, hS.2.2.2]
  exact evt021_appends hS tr

/-- No one store meets both EVT-021 and EVT-022: the in-memory store shows an appended event and
reports itself enabled, the noop store does neither. So the consistency theorem gives each its
own store variable (design events.md, section 3). -/
theorem evt021_not_noop {E : Type} {S : StoreObs E} (hS : EVT_021 S) : ¬ EVT_022 S :=
  fun h => Bool.noConfusion (hS.2.2.2.symm.trans h.2)

/-! ### Wrong stores, one per line -/

/-- The mutant reading without line 1: lines 2, 3 and 4 only. -/
def evt021_noEmptyStart {E : Type} (S : StoreObs E) : Prop :=
  (∀ h e, S.read (h ++ [StoreOp.append e]) [] = S.read h [] ++ [e]) ∧
  (S.hasClear = true → ∀ h, S.read (h ++ [StoreOp.clear]) [] = []) ∧
  S.enabled = true

/-- A store that starts with an event already in it (as a store opened over an earlier run's
events would), adds each append at the end and is empty after a clear. -/
def evt021_seededStore : StoreObs Nat where
  enabled := true
  hasClear := true
  read h _ := h.foldl stepOp [0]

/-- ✗ A store that starts with an event in it meets lines 2 to 4 and violates EVT-021 (line 1):
a new store's `events()` returns that event. -/
@[evidence mutant EVT_021]
theorem EVT_021_mutant_seeded :
    evt021_noEmptyStart evt021_seededStore ∧ ¬ EVT_021 evt021_seededStore := by
  refine ⟨⟨fun h e => ?_, fun _ h => ?_, rfl⟩, fun h => ?_⟩
  · simp [evt021_seededStore, List.foldl_append, stepOp]
  · simp [evt021_seededStore, List.foldl_append, stepOp]
  · have := h.1
    simp [evt021_seededStore] at this

/-- The mutant reading without line 2: lines 1, 3 and 4 only. -/
def evt021_noAppendOrder {E : Type} (S : StoreObs E) : Prop :=
  S.read [] [] = [] ∧
  (S.hasClear = true → ∀ h, S.read (h ++ [StoreOp.clear]) [] = []) ∧
  S.enabled = true

/-- Insert a timestamp into a list sorted by timestamp, after every timestamp not above it. -/
def evt021_insertByTime (t : Nat) : List Nat → List Nat
  | [] => [t]
  | u :: us => if u ≤ t then u :: evt021_insertByTime t us else t :: u :: us

/-- Sort a list of timestamps, earliest first (insertion sort, stable). -/
def evt021_sortByTime : List Nat → List Nat
  | [] => []
  | t :: ts => evt021_insertByTime t (evt021_sortByTime ts)

/-- A store that returns its retained events sorted by timestamp, the event being its own
timestamp here: the body's "chronological order" read literally (clash evt-c#14). -/
def evt021_chronoStore : StoreObs Nat where
  enabled := true
  hasClear := true
  read h _ := evt021_sortByTime (retained h)

/-- ✗ A store that orders by timestamp meets lines 1, 3 and 4 and violates EVT-021 (line 2):
after the appends 2 then 1, `events()` returns `[1, 2]`, not the append order `[2, 1]`. -/
@[evidence mutant EVT_021]
theorem EVT_021_mutant_chrono :
    evt021_noAppendOrder evt021_chronoStore ∧ ¬ EVT_021 evt021_chronoStore := by
  refine ⟨⟨rfl, fun _ h => ?_, rfl⟩, fun h => ?_⟩
  · simp [evt021_chronoStore, retained_append_clear, evt021_sortByTime]
  · have := h.2.1 [.append 2] 1
    revert this
    decide

/-- The mutant reading without line 3: lines 1, 2 and 4 only. -/
def evt021_noClear {E : Type} (S : StoreObs E) : Prop :=
  S.read [] [] = [] ∧
  (∀ h e, S.read (h ++ [StoreOp.append e]) [] = S.read h [] ++ [e]) ∧
  S.enabled = true

/-- A store that provides `clear()` but whose `clear()` does nothing: it returns every event
ever appended (in Java, an `InMemoryEventStore.clear()` that lost its `events.clear()`; the
class provides `clear()`, so its `hasClear` is true). -/
def evt021_ignoreClearStore {E : Type} : StoreObs E where
  enabled := true
  hasClear := true
  read h _ := appended h

/-- ✗ A store whose `clear()` does nothing meets lines 1, 2 and 4 and violates EVT-021 (line 3):
after an append and a clear, `events()` still returns the event. -/
@[evidence mutant EVT_021]
theorem EVT_021_mutant_ignoreClear :
    evt021_noClear (evt021_ignoreClearStore (E := Nat)) ∧
      ¬ EVT_021 (evt021_ignoreClearStore (E := Nat)) := by
  refine ⟨⟨rfl, fun h e => ?_, rfl⟩, fun h => ?_⟩
  · simp [evt021_ignoreClearStore, appended]
  · have := h.2.2.1 rfl [.append 7]
    simp [evt021_ignoreClearStore, appended] at this

/-- The mutant reading without line 4: lines 1, 2 and 3 only. -/
def evt021_noEnabled {E : Type} (S : StoreObs E) : Prop :=
  S.read [] [] = [] ∧
  (∀ h e, S.read (h ++ [StoreOp.append e]) [] = S.read h [] ++ [e]) ∧
  (S.hasClear = true → ∀ h, S.read (h ++ [StoreOp.clear]) [] = [])

/-- A store that keeps every event appended to it, in order, and provides `clear()`, but reports
itself not enabled: an in-memory store whose only change is an `isEnabled()` that returns
false. -/
def evt021_disabledMemStore {E : Type} : StoreObs E where
  enabled := false
  hasClear := true
  read h _ := retained h

/-- ✗ A store that keeps its events but reports itself not enabled meets lines 1 to 3 and
violates EVT-021 (line 4): an executor appends nothing to it, so it retains none of a run's
events. -/
@[evidence mutant EVT_021]
theorem EVT_021_mutant_disabled :
    evt021_noEnabled (evt021_disabledMemStore (E := Nat)) ∧
      ¬ EVT_021 (evt021_disabledMemStore (E := Nat)) :=
  ⟨⟨rfl, fun h e => retained_append_one h e, fun _ h => retained_append_clear h⟩,
   fun h => Bool.noConfusion h.2.2.2⟩

/-- ✗ The last-in-first-out store violates EVT-021 (line 2): after the appends 1 then 2,
`events()` returns `[2, 1]`. -/
@[evidence forbids EVT_021]
theorem EVT_021_forbids_lifo : ¬ EVT_021 (newestFirstStore (E := Nat)) := by
  intro h
  have := h.2.1 [.append 1] 2
  simp [newestFirstStore, retained, stepOp] at this

/-- ✗ The bounded debug store of capacity 2 ([EVT-024]) is not an in-memory store (line 2): after
three appends it has evicted the oldest. -/
@[evidence forbids EVT_021]
theorem EVT_021_forbids_bounded : ¬ EVT_021 (refBoundedStore (E := Nat) 2) := by
  intro h
  have := h.2.1 [.append 1, .append 2] 3
  revert this
  decide

/-- ✗ The noop store ([EVT-022]) is not an in-memory store (lines 2 and 4). -/
@[evidence forbids EVT_021]
theorem EVT_021_forbids_noop : ¬ EVT_021 (refNoopStore (E := Nat)) :=
  fun h => evt021_not_noop h EVT_022_reference

/-! ### What the block allows (ruling D29 (a)) -/

/-- ✓ The live-array store meets EVT-021 (the copy is unspecified, ruling D29 (a)), and its
returned list does change: the list returned on a new store shows an event appended after the
call. -/
@[evidence allows EVT_021]
theorem EVT_021_allows_live :
    EVT_021 (liveMemStore (E := Nat)) ∧
      (liveMemStore (E := Nat)).read [] [.append 7] ≠
        (liveMemStore (E := Nat)).read [] [] := by
  refine ⟨⟨rfl, fun h e => ?_, fun _ h => ?_, rfl⟩, by decide⟩
  · simp [liveMemStore, retained_append_one]
  · simp [liveMemStore, retained_append_clear]

/-- The Rust in-memory store and the Python binding's: the reference store without `clear()`. -/
def evt021_noClearMemStore {E : Type} : StoreObs E where
  enabled := true
  hasClear := false
  read h _ := retained h

/-- ✓ The in-memory store without `clear()` meets EVT-021 (`clear()` where provided, ruling
D29 (a)). -/
@[evidence allows EVT_021]
theorem EVT_021_allows_noClear : EVT_021 (evt021_noClearMemStore (E := Nat)) ∧
    (evt021_noClearMemStore (E := Nat)).hasClear = false :=
  ⟨⟨rfl, fun h e => retained_append_one h e, fun hc => Bool.noConfusion hc, rfl⟩, rfl⟩

/-- A TypeScript in-memory store whose `clear()` replaces its array (`this._events = []`) rather
than emptying it: a list returned earlier follows the appends up to the next clear and then
stops following the store. -/
def evt021_detachedMemStore {E : Type} : StoreObs E where
  enabled := true
  hasClear := true
  read h h' := retained h ++ appended (h'.takeWhile fun
    | .clear => false
    | .append _ => true)

/-- ✓ The detached-array store meets EVT-021: what a returned list shows after later operations
is not specified (ruling D29 (a)), so a list that is neither a copy nor a live view of the store
is allowed. After a call on a new store followed by append 1, clear, append 2, the returned list
shows `[1]`: a copy shows `[]`, a live view `[2]`. -/
@[evidence allows EVT_021]
theorem EVT_021_allows_detached :
    EVT_021 (evt021_detachedMemStore (E := Nat)) ∧
      (evt021_detachedMemStore (E := Nat)).read [] [.append 1, .clear, .append 2] = [1] ∧
      (liveMemStore (E := Nat)).read [] [.append 1, .clear, .append 2] = [2] ∧
      (refMemStore (E := Nat)).read [] [.append 1, .clear, .append 2] = [] := by
  refine ⟨⟨rfl, fun h e => ?_, fun _ h => ?_, rfl⟩, by decide, by decide, by decide⟩
  · simp [evt021_detachedMemStore, appended, retained_append_one]
  · simp [evt021_detachedMemStore, appended, retained_append_clear]

/-! ### Calls of `events()` (the fifth quoted sentence)

A history of `StoreOp` holds appends and clears only, so the observation `read h []` stands for
every call of `events()` after `h` only on a store where a call changes nothing a later call
returns. Here the calls are made explicit: a store's behaviour is what a call of `events()`
returns after a history that may contain calls, and the store is call-free when that is what the
same call returns with the earlier calls left out. -/

/-- An operation on a store with the calls of `events()` made explicit. -/
inductive Evt021Op (E : Type) where
  /-- An append or a clear. -/
  | op (o : StoreOp E)
  /-- A call of `events()`. -/
  | call
  deriving DecidableEq

/-- The appends and clears of a history with calls, in order. -/
def evt021_ops {E : Type} (h : List (Evt021Op E)) : List (StoreOp E) :=
  h.filterMap fun
    | .op o => some o
    | .call => none

/-- A store's calls are free of effect: what a call of `events()` returns after a history with
calls is what it returns after the appends and clears of that history alone (the fifth quoted
sentence). `c h` is what a call made after `h` returns. -/
def evt021_CallFree {E : Type} (c : List (Evt021Op E) → List E) : Prop :=
  ∀ h, c h = c ((evt021_ops h).map .op)

/-- The observation (`StoreObs`) of a store given by what its calls return: `read h []` is the
call after the appends and clears `h`. -/
def evt021_project {E : Type} (en hc : Bool) (c : List (Evt021Op E) → List E) : StoreObs E where
  enabled := en
  hasClear := hc
  read h _ := c (h.map .op)

/-- Leaving the calls out of a history of appends and clears changes nothing. -/
theorem evt021_ops_map_op {E : Type} (h : List (StoreOp E)) :
    evt021_ops (h.map Evt021Op.op) = h := by
  induction h with
  | nil => rfl
  | cons o h ih => simpa [evt021_ops] using ih

/-- On a call-free store that provides `clear()` and whose observation meets EVT-021, every call
of `events()`, after any history with calls, returns the events appended since the last clear,
in append order. -/
theorem evt021_calls_retained {E : Type} {en : Bool} {c : List (Evt021Op E) → List E}
    (hf : evt021_CallFree c) (hS : EVT_021 (evt021_project en true c)) (h : List (Evt021Op E)) :
    c h = retained (evt021_ops h) := by
  rw [hf h]
  exact evt021_read_retained hS rfl (evt021_ops h)

/-- The reference in-memory store is call-free. -/
theorem evt021_ref_callFree {E : Type} :
    evt021_CallFree (fun h : List (Evt021Op E) => retained (evt021_ops h)) := by
  intro h
  simp only [evt021_ops_map_op]

/-- One operation on the queue of a store whose `events()` drains it: a call empties it. -/
def evt021_drainStep (q : List Nat) : Evt021Op Nat → List Nat
  | .op o => stepOp q o
  | .call => []

/-- What a call of `events()` returns on the draining store (a `poll()` loop over Java's
`ConcurrentLinkedQueue` in place of `List.copyOf`): the events appended since the last clear or
the last call. -/
def evt021_drainCall (h : List (Evt021Op Nat)) : List Nat := h.foldl evt021_drainStep []

/-- The draining store's observation meets EVT-021: a history of appends and clears holds no
call, so it shows only the first call after each history. -/
theorem evt021_drain_accepted : EVT_021 (evt021_project true true evt021_drainCall) := by
  refine ⟨rfl, fun h e => ?_, fun _ h => ?_, rfl⟩
  · simp [evt021_project, evt021_drainCall, List.foldl_append, evt021_drainStep, stepOp]
  · simp [evt021_project, evt021_drainCall, List.foldl_append, evt021_drainStep, stepOp]

/-- ✗ The draining store is not call-free (the fifth quoted sentence): after append 1, a first
call returns `[1]` and a second call `[]`. -/
theorem evt021_drain_not_callFree : ¬ evt021_CallFree evt021_drainCall := by
  intro hf
  have := hf [.op (.append 1), .call]
  revert this
  decide

/-! ### Non-vacuity: the test derivation on the reference -/

/-- The test derivation on the reference: after 100 appends, `events()` returns the 100 events in
append order; after an append, a clear and another append it returns the last event only; an
executor's events all reach it. The last-in-first-out store returns the same 100 appends
reversed, so line 2 is not true of every store. -/
@[evidence nonvacuous EVT_021]
theorem EVT_021_nonvacuous :
    (refMemStore (E := Nat)).read ((List.range 100).map StoreOp.append) [] = List.range 100 ∧
    (refMemStore (E := Nat)).read [.append 1, .clear, .append 2] [] = [2] ∧
    (refMemStore (E := Nat)).read (storeSink refMemStore [1, 2, 3]) [] = [1, 2, 3] ∧
    (newestFirstStore (E := Nat)).read ((List.range 100).map StoreOp.append) [] ≠
      List.range 100 := by
  refine ⟨retained_appends _, by decide, by decide, ?_⟩
  simp only [newestFirstStore, retained_appends]
  decide

end Libpetri.Spec
