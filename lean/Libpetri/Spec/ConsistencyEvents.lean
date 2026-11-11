import Libpetri.Spec.GlossaryStore
import Libpetri.Spec.Req.EVT_020
import Libpetri.Spec.Req.EVT_021
import Libpetri.Spec.Req.EVT_022
import Libpetri.Spec.Req.EVT_023
import Libpetri.Spec.Req.EVT_024
import Libpetri.Spec.Req.EVT_025
import Libpetri.Spec.Req.EVT_030
import Libpetri.Spec.Req.EVT_031
import Libpetri.Spec.Req.EVT_032

set_option linter.missingDocs true

/-!
# Consistency of the event requirements (store part)

The target of this module is one theorem, `spec_consistent_events`, that extends the executor
theorem by the event blocks: the executor events of wave W7 on one event-emitting executor
(`RefEvents` over `RefExec`), and the store, query, replay and archive blocks of wave W6 on the
store witnesses of `GlossaryStore.lean` and the reference files of the store tier.

The store part gives **one store variable per store role**: the in-memory store ([EVT-021]),
the noop store ([EVT-022]), the logging decorator ([EVT-023]) and the bounded store ([EVT-024])
each get their own existential, instantiated by their own reference store. One shared store
variable would make the conjunction unsatisfiable: the in-memory store shows an appended event
and the noop store never does (design events.md, section 3; the evt-c spike's
`EVT_021_022_one_store_unsat`). What ties a store to an executor is the glossary's `storeSink`
([EVT-020] AC3), which decides from the store's enabled flag alone, so no agreement conjunct
between a store and the executor witness is needed beyond the enabled flag each store block
fixes. [EVT-020] is the interface every store meets, so it is a conjunct on each store variable
and on the logging decorator around the in-memory store.

Wave W6 adds, besides the stores: the query helpers of [EVT-030] and the logging decorator of
[EVT-023] over one event shape `sh`, whose failure set is the one both blocks read
(`failure_sets_agree`: [EVT-023]'s level table logs at WARN exactly the kinds [EVT-030]'s
`failures()` returns); the live subscriptions of the debug stores ([EVT-024] block B) and of the
Python binding ([EVT-031]), one subscription variable each, since the debug form subscribes
unbounded and [EVT-031] requires a capacity; the archive codec of [EVT-025]; and the replay
cache call of [EVT-032] over one replay view. Wave W7 adds the executor part, over the same
event type.

## Obligations of the W7 integrator

The store tier is written over an abstract event type, so three things here are bridges that W7
removes or ties down; none of them is meant to stay.

* **One kind type and one failure set.** The thirteen event kinds are enumerated three times:
  `NetEventKind` (with its `isFailure`) in EVT_023, `EventType` (with its own `isFailure`) in
  EVT_030, and `RecEvent` (the kinds with their payloads) in `Reference/Replay.lean`. This module
  bridges them (`EventType.toKind`, `failure_sets_agree`, `RecEvent.kind`). W7 keeps one kind
  type and one `isFailure` in its glossary of events, has EVT_023, EVT_030 and `RecEvent` read
  it, and deletes the bridges.
* **The event-model parameters.** The kind function `kind` of [EVT-023], the event shape `sh` of
  [EVT-030] (whose filters [EVT-031] also reads) and the replay view `view` of [EVT-032] are free
  parameters of their statements: a degenerate choice (every event of kind TokenAdded, every shape
  without names, a view that ignores every event) meets each block. Each block binds only with the
  event model's own function. W7 states `sh` as its events' shape function, `kind` as
  `(sh e).type.toKind` (as `joint_events_store_sketch` already does) and `view` as `recView` after
  the map that forgets the fields the replay does not read, and instantiates this theorem with
  them.
-/

namespace Libpetri.Spec

open Libpetri.Reference

/-- The event kind of [EVT-023]'s level table for an event type of [EVT-030]'s query helpers.
The two enumerations name the same thirteen kinds. -/
def EventType.toKind : EventType → NetEventKind
  | .executionStarted => .executionStarted
  | .executionCompleted => .executionCompleted
  | .transitionEnabled => .transitionEnabled
  | .transitionClockRestarted => .transitionClockRestarted
  | .transitionStarted => .transitionStarted
  | .transitionCompleted => .transitionCompleted
  | .transitionFailed => .transitionFailed
  | .transitionTimedOut => .transitionTimedOut
  | .actionTimedOut => .actionTimedOut
  | .tokenAdded => .tokenAdded
  | .tokenRemoved => .tokenRemoved
  | .logMessage => .logMessage
  | .markingSnapshot => .markingSnapshot

/-- `EventType.toKind` is one-to-one, so the two enumerations name the same kinds. -/
theorem EventType.toKind_injective : Function.Injective EventType.toKind := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

/-- One failure set: the kinds [EVT-023] logs at WARN are exactly the event types [EVT-030]'s
`failures()` returns (design events.md, section 3). -/
theorem failure_sets_agree (t : EventType) :
    (t.toKind.isFailure = t.isFailure) ∧ (eventLogLevel t.toKind = .warn ↔ t.isFailure = true) := by
  cases t <;> simp [EventType.toKind, NetEventKind.isFailure, EventType.isFailure, eventLogLevel]

/-- The kind of a recorded event of [EVT-032]'s replay, as [EVT-023]'s level table names it (a
bridge for the W7 integrator, see the module doc). -/
def RecEvent.kind {N : Type} : RecEvent N → NetEventKind
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

/-- Every kind of [EVT-023]'s table is the kind of a recorded event (over any non-empty set of
places), so the three enumerations name the same thirteen kinds. -/
theorem RecEvent.kind_surjective {N : Type} [Inhabited N] :
    ∀ k : NetEventKind, ∃ e : RecEvent N, e.kind = k := by
  intro k
  cases k
  · exact ⟨.executionStarted, rfl⟩
  · exact ⟨.executionCompleted, rfl⟩
  · exact ⟨.transitionEnabled "", rfl⟩
  · exact ⟨.transitionClockRestarted "", rfl⟩
  · exact ⟨.transitionStarted "", rfl⟩
  · exact ⟨.transitionCompleted "", rfl⟩
  · exact ⟨.transitionFailed "", rfl⟩
  · exact ⟨.transitionTimedOut "", rfl⟩
  · exact ⟨.actionTimedOut "", rfl⟩
  · exact ⟨.tokenAdded default, rfl⟩
  · exact ⟨.tokenRemoved default, rfl⟩
  · exact ⟨.markingSnapshot [], rfl⟩
  · exact ⟨.logMessage, rfl⟩

/-- ✓ The store-tier requirements of wave W6 hold together, one variable per store role: the
reference in-memory store (EVT-020, EVT-021) with the reference query helpers (EVT-030) and the
reference logging decorator (EVT-023) over one event shape, the decorator around the in-memory
store meeting EVT-020; the reference noop store (EVT-020, EVT-022); the reference bounded store
at the debug stores' default capacity (EVT-020, EVT-024); the reference debug subscriptions
(EVT-024 block B); the Python binding's subscriptions (EVT-031); the reference archive codec
(EVT-025); and the reference replay cache call (EVT-032). The store part of
`spec_consistent_events`. -/
@[evidence consistent EVT_020 EVT_021 EVT_022 EVT_023 EVT_024 EVT_024_B EVT_025 EVT_030 EVT_031
  EVT_032]
theorem joint_events_store_sketch {E D N : Type} [DecidableEq E] [DecidableEq N] [SameContent D]
    [SameContent E] (sh : E → EventShape) (view : E → REv N) :
    (∃ (Smem : StoreObs E) (H : QueryHelpers E) (L : LogDecorator E),
      EVT_020 Smem ∧ EVT_021 Smem ∧ EVT_030 sh H ∧
      EVT_023 (fun e => (sh e).type.toKind) L ∧ EVT_020 (L.over Smem)) ∧
    (∃ Snoop : StoreObs E, EVT_020 Snoop ∧ EVT_022 Snoop) ∧
    (∃ Sdbg : StoreObs E, EVT_020 Sdbg ∧ EVT_024 10000 Sdbg) ∧
    (∃ Udbg : SubSem E, EVT_024_B Udbg) ∧
    (∃ Upy : SubSem E, EVT_031 Upy) ∧
    (∃ C : ArchiveCodec D E, EVT_025 C) ∧
    (∃ call : CacheCall N E, EVT_032 view call) :=
  ⟨⟨refMemStore, refQueryHelpers sh, refLogStore _, EVT_020_reference, EVT_021_reference,
      EVT_030_reference sh, EVT_023_reference _, EVT_020_reference⟩,
    ⟨refNoopStore, EVT_020_noop, EVT_022_reference⟩,
    ⟨refBoundedStore 10000, EVT_020_bounded, EVT_024_default⟩,
    ⟨refDebugSub, EVT_024_B_reference⟩,
    ⟨evt031PySub, EVT_031_reference⟩,
    ⟨refArchive, EVT_025_reference⟩,
    ⟨refReplayCall view, EVT_032_reference view⟩⟩

end Libpetri.Spec
