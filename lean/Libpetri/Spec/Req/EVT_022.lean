import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryStore

set_option linter.missingDocs true

/-!
# EVT-022: NoopEventStore (`spec/08-events-observability.md`)

The noop store discards every event and reports itself not enabled. The requirement is a
predicate over the observation of one store, `S : StoreObs E` (glossary `GlossaryStore.lean`):
what a call of `events()` shows after a history of appends and clears, and whether the store
reports itself enabled.

The witness is the reference noop store `refNoopStore`, the shape of all three runtimes' noop
stores. The wrong stores are the logging decorator over the noop store (it discards every event
but reports itself enabled, as Java's `EventStore.logging()` does), a store that reports itself
not enabled but keeps its events, a store whose returned list is empty at the call but shows
later appends, and the in-memory store. Two consequences tie the block to the
rest of the store tier: an append to a store that meets it changes nothing a call of `events()`
shows (AC1), and an executor appends nothing to it (`storeSink`, [EVT-020] AC3).
-/

namespace Libpetri.Spec

/-! ## EVT-022: NoopEventStore -/

requirement EVT_022
  id "EVT-022"
  title "NoopEventStore"
  kind F
  scope "the noop event store (Java EventStore.noop(), TypeScript noopEventStore(), Rust NoopEventStore)"
  source verbatim "spec/08-events-observability.md"
  quote "The noop event store *shall* return no event from `events()`, whatever was appended to it, and the list it returns *shall* stay empty whatever is appended to it later."
        "*When* an event is appended to the noop event store, the store *shall* discard it."
        "The noop event store *shall* report itself as not enabled (`isEnabled()` returns false; in Rust, the store type's `ENABLED` constant is false)."
  reading "For every store S over any event type E:"
          "after every history h of appends and clears, a call of events() returns the empty list, and the list it returned still shows nothing after any further operations h';"
          "S reports itself as not enabled."
  assumes "The model is the observation of one store, S : StoreObs E (glossary: Event store): its enabled flag, whether it provides clear(), and read h h', the list a call of events() made after the history h shows once the further operations h' have run. The event type E is a parameter: the line says nothing about what an event holds. The first quoted sentence is line 1; its second half ('stays empty') is the quantifier over h', which all three runtimes meet with an immutable empty list (Java List.of(), a frozen empty array in TypeScript, the static empty slice in Rust)."
          "The second quoted sentence (AC1, append() is a no-op) is read as line 1: a store's append is observed only through events(), so an append that no later call of events() shows is discarded. evt022_append_noop states it as a consequence: removing an append from any history changes nothing a call of events() shows. size() and isEmpty(), which the runtimes also offer, are not named by the spec and not modelled."
          "AC2 (events() returns empty) is line 1. AC3 (isEnabled() returns false) is line 2 and the third quoted sentence; Rust has no isEnabled() method, and its noop store type sets the associated constant ENABLED to false, which the executor reads at compile time (impl EventStore for NoopEventStore in rust/libpetri-event/src/event_store.rs)."
          "AC4 (the executor does not allocate event objects when the noop store is used) and the body sentence 'When used, the executor skips event object creation entirely' are kind Q: allocation is not observable in a model of what a store shows, and PERF-010's benchmark is their test. They are false of both TypeScript executors and of the Java bitmap executor, which build event objects and test the enabled flag only when appending (clash perf#4); ruling D34 (a) rewords PERF-010 to what every runtime meets, and that rewording is not made yet: spec/10-performance.md (PERF-010) and EVT-022's body sentence and AC4 still say that no event object is created. The observable half, that an executor appends nothing to a store that reports itself not enabled, is EVT-020's AC3 and is not restated here: the glossary's storeSink decides it from the enabled flag, and evt022_sink shows it gives a store that meets this block nothing."
          "Clear: none of the three noop stores provides clear() (ruling D29 (a): clear() where provided), so a history with a clear is not one a caller can make; line 1 quantifies over every history and covers it anyway."
          "Scope: the line is on the noop store, not on every store that discards. Java's EventStore.logging() wraps the noop store in the logging decorator (EVT-023), which discards every event but reports itself enabled, so an executor builds and hands it every event; it is a different store and is the mutant evt022_discardEnabled here, not a runtime that fails the block. The debug-aware store over the noop store has the same shape in all three runtimes (enabled, events() empty) and is outside the line for the same reason."
          "Python has no noop store object: a run given no event store, or a store whose is_enabled is false, runs on Rust's NoopEventStore (rust/libpetri-py/src/events.rs, RunSink::Noop), so the Rust store covers it."
          "The test derivation is EVT_022_nonvacuous for its first half (a history of appends leaves events() empty while the in-memory store shows the same appends); its benchmark half is AC4's."
  signoff "2026-11-13 07379021855ffbc8 ai"
  statement : ∀ {E : Type}, StoreObs E → Prop :=
    fun S =>
      (∀ h h', S.read h h' = []) ∧
      S.enabled = false

/- The pinned readable form of EVT-022: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_022 : {E : Type} → StoreObs E → Prop :=
fun {E} S => (∀ (h h' : List (StoreOp E)), S.read h h' = []) ∧ S.enabled = false
-/
#guard_msgs in #print EVT_022

/-! ### The reference -/

/-- The reference noop store satisfies EVT-022: it returns the empty list from every call of
`events()`, after every history and for every later history, and reports itself not enabled. -/
@[evidence holds EVT_022]
theorem EVT_022_reference {E : Type} : EVT_022 (refNoopStore (E := E)) :=
  ⟨fun _ _ => rfl, rfl⟩

/-! ### Consequences -/

/-- AC1 on a store that meets EVT-022: an append anywhere in a history changes nothing a call of
`events()` shows, at the call or later. -/
theorem evt022_append_noop {E : Type} {S : StoreObs E} (hS : EVT_022 S)
    (h₀ h₁ h' : List (StoreOp E)) (e : E) :
    S.read (h₀ ++ StoreOp.append e :: h₁) h' = S.read (h₀ ++ h₁) h' := by
  rw [hS.1, hS.1]

/-- An executor appends nothing to a store that meets EVT-022 ([EVT-020] AC3, through the
glossary's `storeSink`), whatever events it emits. -/
theorem evt022_sink {E : Type} {S : StoreObs E} (hS : EVT_022 S) (tr : List E) :
    storeSink S tr = [] :=
  storeSink_disabled hS.2 tr

/-! ### Wrong stores, one per line -/

/-- The mutant reading without line 2 (line 1 alone): a store that discards, read as "events()
is always empty" without the enabled flag. -/
def Discards {E : Type} (S : StoreObs E) : Prop := ∀ h h', S.read h h' = []

/-- The logging decorator over the noop store (Java `EventStore.logging()` and
`LoggingEventStore` in `EventStore.java`): it hands every event to the noop store, so `events()` is
always empty, but it reports itself enabled. -/
def evt022_discardEnabled {E : Type} : StoreObs E where
  enabled := true
  hasClear := false
  read _ _ := []

/-- ✗ A store that discards every event but reports itself enabled meets the discarding reading
and violates EVT-022 (line 2): an executor would build and append every event to it. -/
@[evidence mutant EVT_022]
theorem EVT_022_mutant_discardEnabled :
    Discards (evt022_discardEnabled (E := Nat)) ∧ ¬ EVT_022 (evt022_discardEnabled (E := Nat)) :=
  ⟨fun _ _ => rfl, fun h => absurd h.2 (by decide)⟩

/-- The mutant reading without line 1 (line 2 alone): a store that reports itself not enabled,
read as the noop store without the empty `events()`. -/
def ReportsDisabled {E : Type} (S : StoreObs E) : Prop := S.enabled = false

/-- ✗ A store that reports itself not enabled but keeps its events meets the disabled reading
and violates EVT-022 (line 1): after one append, `events()` returns that event. -/
@[evidence mutant EVT_022]
theorem EVT_022_mutant_disabledMem :
    ReportsDisabled (disabledKeepStore (E := Nat)) ∧
      ¬ EVT_022 (disabledKeepStore (E := Nat)) := by
  refine ⟨rfl, fun h => ?_⟩
  have := h.1 [.append 7] []
  simp [disabledKeepStore, retained, stepOp] at this

/-- The mutant reading of line 1 without its second half: `events()` returns the empty list,
read at the call only (`h' = []`), with no promise about the returned list afterwards. -/
def ReturnsEmpty {E : Type} (S : StoreObs E) : Prop := (∀ h, S.read h [] = []) ∧ S.enabled = false

/-- A store that reports itself not enabled and returns an empty list from every call, but a
live one that later appends fill (a store that drains its buffer on each call of `events()`
and hands out the live new buffer, as TypeScript's in-memory store hands out its live array). -/
def evt022_liveEmpty {E : Type} : StoreObs E where
  enabled := false
  hasClear := false
  read _ h' := appended h'

/-- ✗ A store whose returned list is empty when returned but shows later appends meets the
at-the-call reading and violates EVT-022 (line 1, "stays empty"): an append after the call
shows up in the list the call returned. -/
@[evidence mutant EVT_022]
theorem EVT_022_mutant_liveEmpty :
    ReturnsEmpty (evt022_liveEmpty (E := Nat)) ∧ ¬ EVT_022 (evt022_liveEmpty (E := Nat)) := by
  refine ⟨⟨fun _ => rfl, rfl⟩, fun h => ?_⟩
  have := h.1 [] [.append 7]
  simp [evt022_liveEmpty, appended] at this

/-- ✗ The in-memory store is not a noop store (both lines): it shows what was appended and
reports itself enabled. -/
@[evidence forbids EVT_022]
theorem EVT_022_forbids_mem : ¬ EVT_022 (refMemStore (E := Nat)) := by
  intro h
  have := h.1 [.append 7] []
  simp [refMemStore, retained, stepOp] at this

/-! ### Non-vacuity: the test derivation on the reference -/

/-- The test derivation's first half on the reference: after three appends, a call of `events()`
on the noop store returns nothing, also once a fourth append has run, the store reports itself
not enabled and an executor appends nothing to it; the in-memory store shows the same three
appends, so line 1 is not true of every store. -/
@[evidence nonvacuous EVT_022]
theorem EVT_022_nonvacuous :
    (refNoopStore (E := Nat)).read [.append 1, .append 2, .append 3] [.append 4] = [] ∧
    (refNoopStore (E := Nat)).enabled = false ∧
    storeSink (refNoopStore (E := Nat)) [1, 2, 3] = [] ∧
    (refMemStore (E := Nat)).read [.append 1, .append 2, .append 3] [] = [1, 2, 3] := by
  decide

end Libpetri.Spec
