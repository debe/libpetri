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
import Libpetri.Spec.Req.EVT_002
import Libpetri.Spec.Req.EVT_003
import Libpetri.Spec.Req.EVT_005
import Libpetri.Spec.Req.EVT_006
import Libpetri.Spec.Req.EVT_007
import Libpetri.Spec.Req.EVT_008
import Libpetri.Spec.Req.EVT_009
import Libpetri.Spec.Req.EVT_010
import Libpetri.Spec.Req.EVT_011
import Libpetri.Spec.Req.EVT_012
import Libpetri.Spec.Req.EVT_013
import Libpetri.Spec.Req.EVT_014
import Libpetri.Spec.Req.ENV_016_l1
import Libpetri.Spec.ConsistencyExec
import Libpetri.Reference.EventsLink

set_option linter.missingDocs true

/-!
# Consistency of the event requirements

The target of this module is one theorem, `joint_events_sketch`, that extends the executor
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

## One event model (done in the W7 tracer)

The store tier was written over an abstract event type, with three enumerations of the thirteen
kinds and two failure sets, bridged here. Wave W7 replaced the bridges by one model:

* **One kind type and one failure set.** `NetEventKind` and `NetEventKind.isFailure` live in the
  event glossary (`GlossaryEvents.lean`). [EVT-023]'s level table, [EVT-030]'s event types and
  failures, the replay's recorded events (`RecEvent.kind`, `Reference/Replay.lean`) and the
  executor events (`NetEvent.kind`) all read it; `NetEvent.toRec_kind` shows that the replay's
  view of an executor event keeps its kind. `failure_sets_agree` is what is left of the bridge:
  the kinds [EVT-023] logs at WARN are exactly the failure kinds [EVT-030]'s `failures()`
  returns.
* **The event-model parameters.** [EVT-023]'s kind function, [EVT-030]'s shape function (which
  [EVT-031]'s filters read too) and [EVT-032]'s replay view are parameters of their blocks, and a
  degenerate choice meets each block. `joint_events_sketch` instantiates the store part with the
  event model's own functions: the event type is `NetEvent N T`, the shape `NetEvent.toShape pn`
  (place names by `pn`), the kind `NetEvent.kind` (the shape's kind), and the replay view
  `NetEvent.replayView`, `recView` after the map that forgets what the replay does not read.

## The executor part

`joint_events_exec_sketch` is the executor part. It extends the executor theorem rather than
restating a weaker one: `ExecSpec V E X Q R` is the body of `spec_consistent_exec_sketch` (every
executor block of wave W5 on the one executor `E`, its links to the validator, the queue firing
and the timed step, and both coverage conditions), and `execSpec_sketch` checks by definitional
unfolding that it is exactly that theorem's body, so a conjunct added there and not here fails
the build. On top of it the executor with events `W` steps as `E` (`W.erase = E`, link E1) and
meets every executor event block of wave W7 (`EventsSpec`): the main blocks of EVT-002 to
EVT-013 and their Java and TypeScript payload companions, the action log `A` of EVT-013 with the
offer clause `Evt013CaptureCovers`, and the `awaitTermination` answer `Aw` of ENV-016 with the
offer clause `Env016AwaitCovers`. So the event blocks constrain the same executor every execution
block holds of; in particular "armed" in EVT-004 and EVT-005 and "reaped" in EVT-009 mean what
TIME-010, TIME-012 and TIME-013 say of `E`. The stand-alone companions over identifiers and
durations (EVT-002's execution ID and lifecycle ID blocks, EVT-003's duration block) are
conjuncts of their own. The witnesses are those of `spec_consistent_exec_sketch`,
`refEvExec polJT`, `refALog` and `refAwait`.

EVT-014 is stated over string place names, since its order is the code-point order of
[CORE-073]. The executor part therefore has a second conjunct over `String`: the same witnesses,
with the places of each snapshot listed ascending by name (`snapOf`, `evt014_snapOf_eq`), meet
`EventsSpec` and EVT-014 together. Over any other place type the order of a snapshot is that of
the names' `Ord`, which no block other than EVT-014 reads, so the generic conjunct picks any.

Two theorems sit beside it, one model each:

* `joint_events_covers_sketch` adds the coverage of the event kinds (design link E5,
  `EvCovers`), stated over `Nat` places and tokens as the coverage scenario is;
* `events_rust_scope` shows the Rust and Python emission (`refEvExec polRust`) meeting every main
  block (design link E6); the payload companions and EVT-014 are scoped to Java and TypeScript.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- One failure set: the kinds [EVT-023] logs at WARN are exactly the kinds [EVT-030]'s
`failures()` returns, the failure kinds of the event glossary. -/
theorem failure_sets_agree (k : NetEventKind) : eventLogLevel k = .warn ↔ k.isFailure = true := by
  cases k <;> simp [NetEventKind.isFailure, eventLogLevel]

/-- ✓ The store-tier requirements of wave W6 hold together, one variable per store role: the
reference in-memory store (EVT-020, EVT-021) with the reference query helpers (EVT-030) and the
reference logging decorator (EVT-023) over one event shape, the decorator around the in-memory
store meeting EVT-020; the reference noop store (EVT-020, EVT-022); the reference bounded store
at the debug stores' default capacity (EVT-020, EVT-024); the reference debug subscriptions
(EVT-024 block B); the Python binding's subscriptions (EVT-031); the reference archive codec
(EVT-025); and the reference replay cache call (EVT-032). The store part of
`joint_events_sketch`. -/
@[evidence consistent EVT_020 EVT_021 EVT_022 EVT_023 EVT_024 EVT_024_B EVT_025 EVT_030 EVT_031
  EVT_032]
theorem joint_events_store_sketch {E D N : Type} [DecidableEq E] [DecidableEq N] [SameContent D]
    [SameContent E] (sh : E → EventShape) (view : E → REv N) :
    (∃ (Smem : StoreObs E) (H : QueryHelpers E) (L : LogDecorator E),
      EVT_020 Smem ∧ EVT_021 Smem ∧ EVT_030 sh H ∧
      EVT_023 (fun e => (sh e).type) L ∧ EVT_020 (L.over Smem)) ∧
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

/-- Same content of two executor events, for the archive codec: equality (an event is a value,
[EVT-001]). -/
instance instSameContentNetEvent {N T : Type} : SameContent (NetEvent N T) :=
  SameContent.byEq _

/-- The body of `spec_consistent_exec_sketch`: every executor block of wave W5 on the one
executor `E`, with its validator `V`, expiry handling `X`, queue firing `Q` and timed step `R`,
the agreement links and both coverage conditions. -/
def ExecSpec {N T : Type} [DecidableEq N] (V : OutputValidator N) (E : XRel N T)
    (X : ExpiryRel N T) (Q : QFireRel N T) (R : TRel N) : Prop :=
  (EXEC_021 E ∧ IO_015 V ∧ ValidatedBy E V) ∧
  (EXEC_001 E ∧ EXEC_003 E ∧ EXEC_022 E ∧ EXEC_030 E ∧ EXEC_031 E ∧ EXEC_040 E ∧
    EXEC_041 E ∧ EXEC_042 E ∧ TIME_014 E) ∧
  (CONC_001 E ∧ CONC_002 E ∧ CONC_003 E ∧ CONC_010 E) ∧
  (ENV_002 E ∧ ENV_003 E ∧ ENV_004 E ∧ ENV_005 E ∧ ENV_006 E ∧ ENV_010 E ∧ ENV_011 E ∧
    ENV_013 E ∧ ENV_014 E ∧ ENV_015 E ∧ ENV_016 E X) ∧
  (EXEC_002_cycle E ∧ EXEC_010_cycle E ∧ EXEC_013_cycle E ∧ EXEC_020_cycle E ∧
    TIME_010_cycle E ∧ TIME_012_cycle E ∧ TIME_013_cycle E ∧ TIME_015_cycle E ∧
    CONC_005_cycle E) ∧
  (EXEC_010 Q ∧ EXEC_013 Q ∧ EXEC_020 Q ∧ QueueAgrees E Q) ∧
  (TIME_010 R ∧ TIME_012 R ∧ TIME_013 R ∧ TIME_015 R ∧ AtomicAgrees E R) ∧
  ExecCovers E ∧ ExecCoversW5 E X

/-- `ExecSpec` is the body of the executor theorem, checked by unfolding: if
`spec_consistent_exec_sketch` gains or loses a conjunct, this no longer type-checks. -/
theorem execSpec_sketch {N T : Type} [DecidableEq N] :
    ∃ (V : OutputValidator N) (E : XRel N T) (X : ExpiryRel N T) (Q : QFireRel N T) (R : TRel N),
      ExecSpec V E X Q R :=
  spec_consistent_exec_sketch

/-- The witnesses of the executor theorem meet its body. -/
theorem execSpec_ref {N T : Type} [DecidableEq N] :
    ExecSpec ioRefValidate (RefExec (N := N) (T := T)) refExpiry RefQFire RefTStep :=
  ⟨⟨EXEC_021_reference, IO_015_reference, refExec_validatedBy _⟩,
    ⟨EXEC_001_reference, EXEC_003_reference, EXEC_022_reference, EXEC_030_reference,
      EXEC_031_reference, EXEC_040_reference, EXEC_041_reference, EXEC_042_reference,
      TIME_014_reference⟩,
    ⟨CONC_001_reference, CONC_002_reference, CONC_003_reference, CONC_010_reference⟩,
    ⟨ENV_002_reference, ENV_003_reference, ENV_004_reference, ENV_005_reference,
      ENV_006_reference, ENV_010_reference, ENV_011_reference, ENV_013_reference,
      ENV_014_reference, ENV_015_reference, ENV_016_reference⟩,
    ⟨EXEC_002_cycle_reference, EXEC_010_cycle_reference, EXEC_013_cycle_reference,
      EXEC_020_cycle_reference, TIME_010_cycle_reference, TIME_012_cycle_reference,
      TIME_013_cycle_reference, TIME_015_cycle_reference, CONC_005_cycle_reference⟩,
    ⟨EXEC_010_reference, EXEC_013_reference, EXEC_020_reference, queueAgrees_ref⟩,
    ⟨TIME_010_reference, TIME_012_reference, TIME_013_reference, TIME_015_reference,
      atomicAgrees_ref⟩,
    refExec_covers, refExec_coversW5⟩

/-- The executor event blocks of wave W7 on one executor with events `W`, its action log `A`
([EVT-013]) and its `awaitTermination` answer `Aw` ([ENV-016]), with the offer clauses of the
last two. -/
def EventsSpec {N T : Type} [DecidableEq N] (W : EvExec N T) (A : ActionLogRel N T)
    (Aw : AwaitRel N T) : Prop :=
  EVT_002 W ∧ EVT_003 W ∧ EVT_004 W ∧ EVT_005 W ∧ EVT_006 W ∧ EVT_006_payload W ∧
    EVT_007 W ∧ EVT_007_payload W ∧ EVT_008 W ∧ EVT_009 W ∧ EVT_009_payload W ∧
    EVT_010 W ∧ EVT_011 W ∧ EVT_011_payload W ∧ EVT_012 W ∧ EVT_012_payload W ∧
    EVT_013 W A ∧ Evt013CaptureCovers A ∧ ENV_016_await W Aw ∧ Env016AwaitCovers Aw

/-- The reference executor with events, its action log and its await answer meet every executor
event block. -/
theorem eventsSpec_ref {N T : Type} [DecidableEq N] [Ord N] :
    EventsSpec (refEvExec (N := N) (T := T) polJT) refALog refAwait :=
  ⟨EVT_002_reference, EVT_003_reference, EVT_004_reference, EVT_005_reference,
    EVT_006_reference, EVT_006_payload_reference, EVT_007_reference,
    EVT_007_payload_reference, EVT_008_reference, EVT_009_reference,
    EVT_009_payload_reference, EVT_010_reference, EVT_011_reference,
    EVT_011_payload_reference, EVT_012_reference, EVT_012_payload_reference,
    EVT_013_reference, evt013_refALog_covers, ENV_016_await_reference,
    env016_await_ref_covers⟩

/-- ✓ The executor part of the event requirements: the one executor every execution block of
wave W5 holds of (with its validator, expiry handling, queue firing and timed step), and an
executor with events that steps exactly as it and meets every executor event block, with the
action log and the `awaitTermination` answer it offers; over string place names the same
executor also meets EVT-014; beside them, the execution IDs, the lifecycle IDs and the run
duration. For example, a run that fires one transition and quiesces emits `ExecutionStarted`
first and `ExecutionCompleted` last, once each, every token a start takes is reported by one
`TokenRemoved` event of its place, and with places declared as `b`, `c`, `a` the marking at the
start is reported as `a` then `b`. -/
@[evidence consistent EVT_002 EVT_003 EVT_004 EVT_005 EVT_006 EVT_006_payload EVT_007
  EVT_007_payload EVT_008 EVT_009 EVT_009_payload EVT_010 EVT_011 EVT_011_payload EVT_012
  EVT_012_payload EVT_013 EVT_014 ENV_016_await EVT_002_executionId EVT_002_lifecycleId
  EVT_003_duration]
theorem joint_events_exec_sketch {N T : Type} [DecidableEq N] :
    (∃ (V : OutputValidator N) (E : XRel N T) (X : ExpiryRel N T) (Q : QFireRel N T)
        (R : TRel N) (W : EvExec N T) (A : ActionLogRel N T) (Aw : AwaitRel N T),
      ExecSpec V E X Q R ∧ W.erase = E ∧ EventsSpec W A Aw) ∧
    (∃ (V : OutputValidator String) (E : XRel String T) (X : ExpiryRel String T)
        (Q : QFireRel String T) (R : TRel String) (W : EvExec String T)
        (A : ActionLogRel String T) (Aw : AwaitRel String T),
      ExecSpec V E X Q R ∧ W.erase = E ∧ EventsSpec W A Aw ∧ EVT_014 W) ∧
    (∃ ids, EVT_002_executionId ids) ∧ (∃ L, EVT_002_lifecycleId L) ∧
    (∃ d, EVT_003_duration d) := by
  letI : Ord N := ⟨fun _ _ => .eq⟩
  exact ⟨⟨ioRefValidate, RefExec, refExpiry, RefQFire, RefTStep, refEvExec polJT, refALog, refAwait,
      execSpec_ref, refEvExec_erase polJT, eventsSpec_ref⟩,
    ⟨ioRefValidate, RefExec, refExpiry, RefQFire, RefTStep, refEvExec polJT, refALog, refAwait,
      execSpec_ref, refEvExec_erase polJT, eventsSpec_ref, EVT_014_reference⟩,
    ⟨refExecutionId, EVT_002_executionId_reference⟩,
    ⟨refLifecycleIds, EVT_002_lifecycleId_reference⟩,
    ⟨refDurOf, EVT_003_duration_reference⟩⟩

/-- ✓ The executor part with the coverage of the event kinds (design link E5): over natural
numbers as places and tokens, the executor with events that meets every executor event block
also has a run whose trace holds an event of every kind the executor emits. For example, the
coverage run fires a delayed transition, lets an action budget expire and reaps a window
transition, so its trace holds `TransitionClockRestarted`, `ActionTimedOut` and
`TransitionTimedOut` beside the lifecycle events. -/
@[evidence consistent EVT_002 EVT_003 EVT_004 EVT_005 EVT_006 EVT_006_payload EVT_007
  EVT_007_payload EVT_008 EVT_009 EVT_009_payload EVT_010 EVT_011 EVT_011_payload EVT_012
  EVT_012_payload EVT_013 ENV_016_await]
theorem joint_events_covers_sketch :
    ∃ (V : OutputValidator Nat) (E : XRel Nat Nat) (X : ExpiryRel Nat Nat) (Q : QFireRel Nat Nat)
      (R : TRel Nat) (W : EvExec Nat Nat) (A : ActionLogRel Nat Nat) (Aw : AwaitRel Nat Nat),
      ExecSpec V E X Q R ∧ W.erase = E ∧ EventsSpec W A Aw ∧ EvCovers W :=
  ⟨ioRefValidate, RefExec, refExpiry, RefQFire, RefTStep, refEvExec polJT, refALog, refAwait,
    execSpec_ref, refEvExec_erase polJT, eventsSpec_ref, refEvCovers⟩

/-- ✓ The Rust and Python emission meets every main executor event block (design link E6): the
reference executor with events, emitting as Rust and Python do and with no captured action log,
meets them all. Its emission differs from the Java and TypeScript one only in the marking
snapshots, the `ActionTimedOut` events and the completion of a timeout outcome, which no main
block reads. For example, a run of it emits no `MarkingSnapshot` and still announces its start
and end once. -/
@[evidence consistent EVT_002 EVT_003 EVT_004 EVT_005 EVT_006 EVT_007 EVT_008 EVT_009 EVT_010
  EVT_011 EVT_012 EVT_013 ENV_016_await]
theorem events_rust_scope {N T : Type} [DecidableEq N] :
    ∃ (W : EvExec N T) (A : ActionLogRel N T) (Aw : AwaitRel N T) (_ : Ord N),
      W = refEvExec polRust ∧
      EVT_002 W ∧ EVT_003 W ∧ EVT_004 W ∧ EVT_005 W ∧ EVT_006 W ∧ EVT_007 W ∧ EVT_008 W ∧
      EVT_009 W ∧ EVT_010 W ∧ EVT_011 W ∧ EVT_012 W ∧ EVT_013 W A ∧ ENV_016_await W Aw :=
  letI : Ord N := ⟨fun _ _ => .eq⟩
  ⟨_, refNoALog, refAwait, inferInstance, rfl, EVT_002_rust, EVT_003_rust, EVT_004_rust, EVT_005_rust,
    EVT_006_rust, EVT_007_rust, EVT_008_rust, EVT_009_rust, EVT_010_rust, EVT_011_rust,
    EVT_012_rust, EVT_013_rust, ENV_016_await_rust⟩

/-- ✓ The event requirements hold together over one event model: the executor part above (over
string place names also with EVT-014), and
the store part with the event type of the executor events (`NetEvent N T`), its shape (place
names by `pn`), its kind and its replay view in place of the store tier's parameters. For
example, a `TokenRemoved` event of place `p` is shown by the in-memory store in append order, is
logged at TRACE by the logging store, matches a query for place `pn p`, and replays as one token
taken from `p`. -/
@[evidence consistent EVT_002 EVT_003 EVT_004 EVT_005 EVT_006 EVT_006_payload EVT_007
  EVT_007_payload EVT_008 EVT_009 EVT_009_payload EVT_010 EVT_011 EVT_011_payload EVT_012
  EVT_012_payload EVT_013 EVT_014 ENV_016_await EVT_020 EVT_021 EVT_022 EVT_023 EVT_024 EVT_024_B
  EVT_025 EVT_030 EVT_031 EVT_032]
theorem joint_events_sketch {N T : Type} [DecidableEq N] [DecidableEq T] (pn : N → String) :
    (∃ (V : OutputValidator N) (E : XRel N T) (X : ExpiryRel N T) (Q : QFireRel N T)
        (R : TRel N) (W : EvExec N T) (A : ActionLogRel N T) (Aw : AwaitRel N T),
      ExecSpec V E X Q R ∧ W.erase = E ∧ EventsSpec W A Aw) ∧
    (∃ (V : OutputValidator String) (E : XRel String T) (X : ExpiryRel String T)
        (Q : QFireRel String T) (R : TRel String) (W : EvExec String T)
        (A : ActionLogRel String T) (Aw : AwaitRel String T),
      ExecSpec V E X Q R ∧ W.erase = E ∧ EventsSpec W A Aw ∧ EVT_014 W) ∧
    (∃ (Smem : StoreObs (NetEvent N T)) (H : QueryHelpers (NetEvent N T))
        (L : LogDecorator (NetEvent N T)),
      EVT_020 Smem ∧ EVT_021 Smem ∧ EVT_030 (NetEvent.toShape pn) H ∧
      EVT_023 NetEvent.kind L ∧ EVT_020 (L.over Smem)) ∧
    (∃ Snoop : StoreObs (NetEvent N T), EVT_020 Snoop ∧ EVT_022 Snoop) ∧
    (∃ Sdbg : StoreObs (NetEvent N T), EVT_020 Sdbg ∧ EVT_024 10000 Sdbg) ∧
    (∃ Udbg : SubSem (NetEvent N T), EVT_024_B Udbg) ∧
    (∃ Upy : SubSem (NetEvent N T), EVT_031 Upy) ∧
    (∃ C : ArchiveCodec String (NetEvent N T), EVT_025 C) ∧
    (∃ call : CacheCall N (NetEvent N T), EVT_032 NetEvent.replayView call) :=
  ⟨joint_events_exec_sketch.1, (joint_events_exec_sketch (N := N)).2.1,
    joint_events_store_sketch (D := String) (NetEvent.toShape pn) NetEvent.replayView⟩

end Libpetri.Spec
