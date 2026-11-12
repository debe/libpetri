import Libpetri.Spec.GlossaryEvents
import Libpetri.Reference.Exec
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort
import Mathlib.Data.String.Basic

set_option linter.missingDocs true

/-!
# RefEvents: the events the reference executor emits (wave W7)

The witness model of the executor event requirements ([EVT-002] to [EVT-014],
`spec/08-events-observability.md`). It adds no behaviour to the reference executor: an event
executor is an executor step together with the events the step appends, and the reference is
`RefExec` with a **label homomorphism** `refEmitW` that reads only the step (its source state,
label and target state) and never recomputes a payload the label does not carry.

## The carrier (namespace `Libpetri.Spec`)

* `XEvRel N T`: an executor with events. `R C H s l evs s'` says that under configuration `C`,
  with the events `H` emitted so far (the history), the step labelled `l` leads from `s` to `s'`
  and appends the events `evs`. The history lets a line say "once per executor" (the diagnostics
  of [CORE-072] AC4 and [IO-016] AC4, which [EVT-013] reads); a line that does not need it
  quantifies over every history.
* `EvExec N T`: the boot events of a run (before its first step) and the step relation.
  `EvExec.erase` is the executor underneath: the consistency theorem requires it to be the
  executor the execution requirements hold of (`Reference/EventsLink.lean`, link E1).
* `EvStep`, `LRun`, `Trace`: a labelled run (each step with its states, label and events,
  the history threaded through), and the event trace of a run from the initial state.

A requirement block quantifies over an abstract `EvExec`; the reference is `refEvExec P`, and a
mutant is another emission over the same executor (`emitExec`), or any relation.

## The emission (namespace `Libpetri.Reference`)

Which label emits what (`refEmitW`); every label not listed emits nothing.

| label | events appended, in the reference's order |
|---|---|
| boot | `ExecutionStarted`, then [JT] the snapshot of the initial marking; no `TokenAdded` for it |
| `update` | `TransitionEnabled n` for each name off before and armed after; then `TransitionClockRestarted n` for each name restart pending before and armed after |
| `deadline ns` | `TransitionTimedOut n` per reaped name, with its latest bound and its elapsed time at the deadline reading |
| `start n` | `TokenRemoved` per token removed from the pass-visible marking (input arcs in declaration order, then reset arcs), then `TransitionStarted n` with the same tokens |
| `commit i` | `TokenAdded` per token of the emission, then `TransitionCompleted` |
| `fail i` | [Rust] `ActionTimedOut` when the failed outcome is a timeout outcome, then `TransitionFailed` |
| `tdeposit i` | [Rust] `ActionTimedOut`, then `TokenAdded` per token of the outcome, then [JT] `TransitionCompleted` |
| `expire i e` | [JT] `ActionTimedOut`, from the action's timer |
| `publish i` | `TokenAdded` per token of the batch |
| `inject k` | `TokenAdded` of the injected token |
| `finish c` | [JT] the snapshot of the marking, then `ExecutionCompleted` |

The places of a snapshot are listed ascending by name (`snapArrange`, under the names' `Ord`;
code-point order on strings, [CORE-073] and [EVT-014]).

The three points where the runtimes emit differently are the fields of `EvPol` (Rust and Python:
`polRust`; Java and TypeScript: `polJT`). A line for every executor holds of both; a payload
companion of Java and TypeScript holds of `polJT`.

Not emitted by the reference yet: the construction diagnostics (dead arcs, [CORE-037]; unknown
initial places, [CORE-072]), the multiplicity and unknown-place warnings of an admission
([IO-016], [CORE-072]) and an action's own log messages ([EVT-013]): the executor has no label
for an action's log, and the boot events are abstract in `EvExec`, so a block over `EvExec` does
not exclude them. The order of the `TransitionEnabled` and `TransitionClockRestarted` events of
one update, and of the `TokenRemoved` events across places, is the reference's (Rust's) choice;
no block fixes it.

**Restart pending** (`pendingS`): an armed status whose clock a start of another transition took
(the [TIME-012] restart flag, set from the live intermediate marking, ruling D7). The next update
that finds the name enabled re-stamps it and emits `TransitionClockRestarted`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference

variable {N T : Type}

/-! ## The carrier -/

/-- An executor with events: `R C H s l evs s'` says that under `C`, with the events `H`
emitted so far, the step labelled `l` leads from `s` to `s'` and appends `evs`. -/
abbrev XEvRel (N T : Type) :=
  Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → List (NetEvent N T) → XSt N T → Prop

/-- An executor with events: the events a run emits before its first step, from the
configuration and the initial marking, and the step relation. -/
structure EvExec (N T : Type) where
  /-- The boot events: what a run emits before its first step. -/
  boot : Cfg N T → QMarking N T → List (NetEvent N T)
  /-- The steps, with the events each appends. -/
  step : XEvRel N T

/-- The executor underneath an executor with events: its steps with the events forgotten. -/
def EvExec.erase (E : EvExec N T) : XRel N T := fun C s l s' => ∃ H evs, E.step C H s l evs s'

/-- One step of a labelled run: source state, label, the events appended, target state. -/
structure EvStep (N T : Type) where
  /-- The state before the step. -/
  src : XSt N T
  /-- The step's label. -/
  lbl : XLbl N T
  /-- The events the step appends. -/
  evs : List (NetEvent N T)
  /-- The state after the step. -/
  dst : XSt N T

/-- A labelled run of `E` under `C` from history `H` and state `s`: consecutive steps of `E`,
each given the events emitted before it. -/
def LRun (E : EvExec N T) (C : Cfg N T) : List (NetEvent N T) → XSt N T → List (EvStep N T) → Prop
  | _, _, [] => True
  | H, s, st :: rest => st.src = s ∧ E.step C H st.src st.lbl st.evs st.dst ∧
      LRun E C (H ++ st.evs) st.dst rest

/-- The events a labelled run appends, in emission order. -/
def EvStep.events (run : List (EvStep N T)) : List (NetEvent N T) := run.flatMap (·.evs)

/-- **The event trace of a run**: `tr` is what `E` emits on some labelled run from the initial
state of `M0` at reading `r0`: the boot events, then the events of each step. -/
def Trace (E : EvExec N T) (C : Cfg N T) (M0 : QMarking N T) (r0 : Nat) (tr : List (NetEvent N T)) :
    Prop :=
  ∃ run, LRun E C (E.boot C M0) (xinit M0 r0) run ∧ tr = E.boot C M0 ++ EvStep.events run

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri Libpetri.Spec Libpetri.Novel.Seam

variable {N T : Type}

/-! ## Where the runtimes emit differently -/

/-- The three emission points where the runtimes differ. -/
structure EvPol where
  /-- A `MarkingSnapshot` at the start of a run and before `ExecutionCompleted` ([EVT-014];
  Java and TypeScript; Rust and Python have no producer). -/
  snapshots             : Bool
  /-- `ActionTimedOut` from the action's timer, as an outside step (Java, TypeScript), rather
  than when the executor settles the timeout outcome (Rust, Python) ([EVT-010]). -/
  atoAtExpire           : Bool
  /-- `TransitionCompleted` also after a timeout outcome is deposited (Java, TypeScript)
  ([EVT-007]). -/
  completedAfterTimeout : Bool
  deriving DecidableEq, Repr

/-- Rust and Python. -/
def polRust : EvPol := ⟨false, false, false⟩

/-- Java and TypeScript. -/
def polJT : EvPol := ⟨true, true, true⟩

/-! ## The tokens a start removes -/

section Removed

variable [DecidableEq N]

/-- **Drained** (proposed term): the tokens a reset arc of `t` drains from `p`, firing from `M`:
what `p` still holds after input consumption, when `p` is a reset place of `t`. -/
def drained (M : QMarking N T) (t : Trans N) (p : N) : List T :=
  if p ∈ t.core.resets then qPostInput M t p else []

/-- Every token a firing of `t` from `M` removes from `p`: the consumed input tokens, oldest
first, then the drained tokens. Read tokens are not removed. -/
def qRemoved (M : QMarking N T) (t : Trans N) (p : N) : List T := qInputs M t p ++ drained M t p

/-- The tokens a firing of `t` from `M` removes, place by place in declaration order: each input
place's consumed tokens, then each reset place's drained tokens (the order of Java's and Rust's
consume, `BitmapNetExecutor.java` 1660-1733, `bitmap_backend.rs` 750-857; each list taken once
per place). -/
def removedListDecl (M : QMarking N T) (t : Trans N) : List (N × T) :=
  (inPlaces t).dedup.flatMap (fun p => (qInputs M t p).map (p, ·)) ++
    t.core.resets.dedup.flatMap (fun p => (drained M t p).map (p, ·))

/-- The `TokenRemoved` events of a firing of `t` from `M`, one per removed token, in the order
of `removedListDecl`. -/
def removedEvs (M : QMarking N T) (t : Trans N) : List (NetEvent N T) :=
  (removedListDecl M t).map fun x => .tokenRemoved x.1 x.2

/-- A place without an input arc of `t` gives up no consumed token. -/
theorem qInputs_of_not_mem {M : QMarking N T} {t : Trans N} {p : N} (h : p ∉ inPlaces t) :
    qInputs M t p = [] := by
  have hn : nspecAt t.core p = none := by
    unfold nspecAt
    rw [List.find?_eq_none]
    intro s hs he
    have : s.place = p := by simpa using he
    exact h (List.mem_map.mpr ⟨s, hs, this⟩)
  simp [qInputs, qTake, nconsumed, hn]

/-- Removal splits a queue: the removed tokens, then what the consume leaves. -/
theorem qRemoved_append_qConsume (M : QMarking N T) (t : Trans N) (p : N) :
    qRemoved M t p ++ qConsume M t p = M p := by
  by_cases hr : p ∈ t.core.resets
  · simp [qRemoved, drained, qConsume, hr, qInputs_append_qPostInput]
  · simp [qRemoved, drained, qConsume, hr, qInputs_append_qPostInput]

/-- The removal events, place by place: the input places' consumed tokens, then the reset
places' drained tokens. -/
theorem removedEvs_eq (M : QMarking N T) (t : Trans N) :
    removedEvs M t =
      (inPlaces t).dedup.flatMap (fun p => (qInputs M t p).map (NetEvent.tokenRemoved p)) ++
        t.core.resets.dedup.flatMap (fun p => (drained M t p).map (NetEvent.tokenRemoved p)) := by
  simp [removedEvs, removedListDecl, List.map_flatMap, Function.comp_def]

/-- The `TokenRemoved` events of a firing, read at `p`, are the tokens it removes from `p`. -/
theorem removedAt_removedEvs (M : QMarking N T) (t : Trans N) (p : N) :
    removedAt (removedEvs M t) p = qRemoved M t p := by
  rw [removedEvs_eq, removedAt_append, removedAt_flatMap _ _ (List.nodup_dedup _),
    removedAt_flatMap _ _ (List.nodup_dedup _)]
  unfold qRemoved
  congr 1
  · by_cases h : p ∈ inPlaces t
    · simp [List.mem_dedup, h]
    · simp [List.mem_dedup, h, qInputs_of_not_mem h]
  · by_cases h : p ∈ t.core.resets
    · simp [List.mem_dedup, h]
    · simp [List.mem_dedup, h, drained]

end Removed

/-! ## Statuses -/

/-- The status holds a clock. -/
def isArmedS : Status → Bool
  | .armed .. => true
  | _ => false

/-- **Glossary: Restart pending** (proposed term). Armed, with its clock taken by the start of
another transition whose live intermediate marking disabled it, and not disarmed since
([TIME-012], ruling D7). -/
def pendingS : Status → Bool
  | .armed _ true => true
  | _ => false

/-! ## The order of a snapshot -/

/-- **Snapshot order** (proposed term): the reference lists the places of a `MarkingSnapshot`
ascending by name under the names' `Ord` instance, as the snapshot form of [CORE-073] does
(`snapKeys`); on strings this is code-point order. `snapArrange L` lists the places of `L`, and
only those (`mem_snapArrange`), in that order. -/
def snapArrange {K : Type} [Ord K] (L : List K) : List K :=
  L.insertionSort fun a b => compare a b ≠ .gt

/-- Arranging keeps exactly the places of the list. -/
theorem mem_snapArrange {K : Type} [Ord K] (L : List K) (p : K) : p ∈ snapArrange L ↔ p ∈ L :=
  (List.perm_insertionSort _ L).mem_iff

/-! ## The reference emission -/

section Emission

variable [DecidableEq N] [Ord N]

/-- The places of the net with their queues in `M`: the declared places that hold a token, each
once, in the snapshot order of the place names (ruling R6 (a): declared places only). The payload
of a `MarkingSnapshot` in the reference. For names whose `Ord` agrees with a linear order it is the
canonical snapshot form of [CORE-073] (`refSnapshot`) of the declared places, ascending by name:
on string place names that is code-point order, which [EVT-014] asks for. -/
def snapOf (C : Cfg N T) (M : QMarking N T) : List (N × List T) :=
  ((snapArrange C.X.net.places).dedup.filter fun p => !(M p).isEmpty).map fun p => (p, M p)

/-- The transition names of the net, in declaration order. -/
def netNames (C : Cfg N T) : List String := C.X.net.transitions.map (·.core.name)

/-- The outcome of firing `f` is a timeout outcome. -/
def isTimeoutOut (f : Firing N T) : Bool :=
  match f.out with
  | some (.timedOut _) => true
  | _ => false

/-- **The reference emission**: the events the step from `s` labelled `l` to `s'` appends, under
the emission variant `P` (the table in the module docstring). The history `_H` is not read: the
reference emits no diagnostic yet. -/
def refEmitW (P : EvPol) (C : Cfg N T) (_H : List (NetEvent N T)) (s : XSt N T) (l : XLbl N T)
    (_s' : XSt N T) : List (NetEvent N T) :=
  match l with
  | .update =>
      (netNames C).filterMap (fun n =>
        if s.st n = .off && isArmedS (_s'.st n) then some (.transitionEnabled n) else none) ++
      (netNames C).filterMap (fun n =>
        if pendingS (s.st n) && isArmedS (_s'.st n) then some (.transitionClockRestarted n)
        else none)
  | .deadline ns =>
      ns.filterMap fun n => (findT C n).map fun u =>
        .transitionTimedOut n (C.X.timing u).latest ((viewAt s (max s.cyc s.now)).elapsed u)
  | .start n _ =>
      match s.order with
      | t :: _ => removedEvs (vis s) t ++ [.transitionStarted n (removedListDecl (vis s) t)]
      | [] => []
  | .commit i =>
      match s.fl.find? (·.id == i) with
      | some f =>
        match f.out with
        | some (.ok e) => addedEvs e ++ [.transitionCompleted f.t.core.name e (s.now - f.start)]
        | _ => []
      | none => []
  | .fail i =>
      match s.fl.find? (·.id == i) with
      | some f =>
        (if !P.atoAtExpire && isTimeoutOut f then [.actionTimedOut f.t.core.name] else []) ++
          [.transitionFailed f.t.core.name]
      | none => []
  | .tdeposit i =>
      match s.fl.find? (·.id == i) with
      | some f =>
        match f.out with
        | some (.timedOut e) =>
          (if P.atoAtExpire then [] else [.actionTimedOut f.t.core.name]) ++ addedEvs e ++
            (if P.completedAfterTimeout
             then [.transitionCompleted f.t.core.name e (s.now - f.start)] else [])
        | _ => []
      | none => []
  | .expire i _ =>
      if P.atoAtExpire then
        match s.fl.find? (·.id == i) with
        | some f => [.actionTimedOut f.t.core.name]
        | none => []
      else []
  | .publish _ =>
      match s.pq with
      | (_, b) :: _ => addedEvs b
      | [] => []
  | .inject _ =>
      match s.eq with
      | (_, p, x) :: _ => [.tokenAdded p x]
      | [] => []
  | .finish _ =>
      (if P.snapshots then [.markingSnapshot (snapOf C s.M)] else []) ++ [.executionCompleted]
  | _ => []

/-- The reference boot events: `ExecutionStarted`, then under `snapshots` the snapshot of the
initial marking. No `TokenAdded` for the initial marking (no runtime emits one). -/
def refBoot (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) : List (NetEvent N T) :=
  [.executionStarted] ++ (if P.snapshots then [.markingSnapshot (snapOf C M0)] else [])

end Emission

/-- The executor with events that steps as the reference executor and appends `emit`'s events:
the reference is one such executor, and so is every mutant that changes only what is emitted. -/
def emitExec (boot : Cfg N T → QMarking N T → List (NetEvent N T))
    (emit : Cfg N T → List (NetEvent N T) → XSt N T → XLbl N T → XSt N T → List (NetEvent N T))
    [DecidableEq N] : EvExec N T where
  boot := boot
  step := fun C H s l evs s' => xstep C s l = some s' ∧ evs = emit C H s l s'

/-- **The reference executor with events** under emission variant `P`: `RefExec` with
`refEmitW P`. -/
def refEvExec [DecidableEq N] [Ord N] (P : EvPol) : EvExec N T := emitExec (refBoot P) (refEmitW P)

/- The reference executor with events is the witness model of the event requirements' `holds`
theorems. -/
#spec_witness refEvExec

/-! ## Which label emits which kind -/

/-- The kinds a step labelled `l` may emit in the reference (the table of the module
docstring). -/
def lblKinds : XLbl N T → List NetEventKind
  | .update => [.transitionEnabled, .transitionClockRestarted]
  | .deadline _ => [.transitionTimedOut]
  | .start _ _ => [.tokenRemoved, .transitionStarted]
  | .commit _ => [.tokenAdded, .transitionCompleted]
  | .fail _ => [.actionTimedOut, .transitionFailed]
  | .tdeposit _ => [.actionTimedOut, .tokenAdded, .transitionCompleted]
  | .expire _ _ => [.actionTimedOut]
  | .publish _ => [.tokenAdded]
  | .inject _ => [.tokenAdded]
  | .finish _ => [.markingSnapshot, .executionCompleted]
  | _ => []

section Inversion

variable [DecidableEq N] [Ord N]

omit [DecidableEq N] [Ord N] in
/-- Every event of a list of `TokenAdded` events is a `TokenAdded`. -/
theorem kind_of_mem_addedEvs {e : NetEvent N T} {l : List (N × T)} (h : e ∈ addedEvs l) :
    e.kind = .tokenAdded := by
  simp only [addedEvs, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

omit [Ord N] in
/-- Every event of `removedEvs` is a `TokenRemoved`. -/
theorem kind_of_mem_removedEvs {e : NetEvent N T} {M : QMarking N T} {t : Trans N}
    (h : e ∈ removedEvs M t) : e.kind = .tokenRemoved := by
  simp only [removedEvs, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-- **Emission inversion**: every event the reference emits in a step labelled `l` has one of
the kinds `lblKinds l` lists. A block line "no other step emits kind `k`" follows from it with
no case split over the labels. -/
theorem refEmitW_kind (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    (l : XLbl N T) (s' : XSt N T) : ∀ e ∈ refEmitW P C H s l s', e.kind ∈ lblKinds l := by
  intro e he
  cases l with
  | update =>
    simp only [refEmitW, List.mem_append, List.mem_filterMap] at he
    rcases he with ⟨m, _, hm⟩ | ⟨m, _, hm⟩ <;> split at hm <;>
      simp only [Option.some.injEq, reduceCtorEq] at hm <;> subst hm <;> simp [lblKinds, NetEvent.kind]
  | deadline ns =>
    simp only [refEmitW, List.mem_filterMap] at he
    obtain ⟨m, _, hm⟩ := he
    cases hf : findT C m <;> simp only [hf, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hm
    subst hm; simp [lblKinds, NetEvent.kind]
  | start n sy =>
    simp only [refEmitW] at he
    split at he
    · rcases List.mem_append.1 he with h | h
      · simp [lblKinds, kind_of_mem_removedEvs h]
      · simp only [List.mem_singleton] at h; subst h; simp [lblKinds, NetEvent.kind]
    · cases he
  | commit i =>
    simp only [refEmitW] at he
    split at he
    · split at he
      · rcases List.mem_append.1 he with h | h
        · simp [lblKinds, kind_of_mem_addedEvs h]
        · simp only [List.mem_singleton] at h; subst h; simp [lblKinds, NetEvent.kind]
      · cases he
    · cases he
  | fail i =>
    simp only [refEmitW] at he
    split at he
    · rcases List.mem_append.1 he with h | h
      · split at h
        · simp only [List.mem_singleton] at h; subst h; simp [lblKinds, NetEvent.kind]
        · cases h
      · simp only [List.mem_singleton] at h; subst h; simp [lblKinds, NetEvent.kind]
    · cases he
  | tdeposit i =>
    simp only [refEmitW] at he
    split at he
    · split at he
      · rcases List.mem_append.1 he with h | h
        · rcases List.mem_append.1 h with h | h
          · split at h
            · cases h
            · simp only [List.mem_singleton] at h; subst h; simp [lblKinds, NetEvent.kind]
          · simp [lblKinds, kind_of_mem_addedEvs h]
        · split at h
          · simp only [List.mem_singleton] at h; subst h; simp [lblKinds, NetEvent.kind]
          · cases h
      · cases he
    · cases he
  | expire i e' =>
    simp only [refEmitW] at he
    split at he
    · split at he
      · simp only [List.mem_singleton] at he; subst he; simp [lblKinds, NetEvent.kind]
      · cases he
    · cases he
  | publish i =>
    simp only [refEmitW] at he
    split at he
    · simp [lblKinds, kind_of_mem_addedEvs he]
    · cases he
  | inject k =>
    simp only [refEmitW] at he
    split at he
    · simp only [List.mem_singleton] at he; subst he; simp [lblKinds, NetEvent.kind]
    · cases he
  | finish c =>
    simp only [refEmitW] at he
    rcases List.mem_append.1 he with h | h
    · split at h
      · simp only [List.mem_singleton] at h; subst h; simp [lblKinds, NetEvent.kind]
      · cases h
    · simp only [List.mem_singleton] at h; subst h; simp [lblKinds, NetEvent.kind]
  | _ => simp [refEmitW] at he

/-- Only a start emits `TokenRemoved` in the reference. -/
theorem refEmitW_noRemoved (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) (s : XSt N T)
    {l : XLbl N T} (hl : ∀ n sy, l ≠ .start n sy) (s' : XSt N T) :
    ∀ e ∈ refEmitW P C H s l s', e.kind ≠ .tokenRemoved := by
  intro e he hk
  have := refEmitW_kind P C H s l s' e he
  rw [hk] at this
  cases l with
  | start n sy => exact hl n sy rfl
  | _ => simp [lblKinds] at this

/-- **Boot inversion**: the reference boot emits `ExecutionStarted` and, under `snapshots`, a
`MarkingSnapshot`, and nothing else. -/
theorem refBoot_kind (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ refBoot P C M0, e.kind = .executionStarted ∨ e.kind = .markingSnapshot := by
  intro e he
  simp only [refBoot, List.mem_append, List.mem_singleton] at he
  rcases he with rfl | h
  · exact Or.inl rfl
  · split at h
    · simp only [List.mem_singleton] at h; subst h; exact Or.inr rfl
    · cases h

/-- The reference boot emits no `TokenRemoved`. -/
theorem refBoot_noRemoved (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) :
    ∀ e ∈ refBoot P C M0, e.kind ≠ .tokenRemoved := by
  intro e he hk
  rcases refBoot_kind P C M0 e he with h | h <;> rw [hk] at h <;> cases h

/-- The events of a start in the reference: the removal events of the head of the order from
the pass-visible marking, then `TransitionStarted` with the same tokens. -/
theorem refEmitW_start (P : EvPol) (C : Cfg N T) (H : List (NetEvent N T)) {s : XSt N T}
    {t : Trans N} {rest : List (Trans N)} (ho : s.order = t :: rest) (n : String) (sy : Bool)
    (s' : XSt N T) :
    refEmitW P C H s (.start n sy) s' =
      removedEvs (vis s) t ++ [.transitionStarted n (removedListDecl (vis s) t)] := by
  simp only [refEmitW, ho]

omit [DecidableEq N] [Ord N] in
/-- The pass-visible marking followed by the same-pass tail is the marking. -/
theorem vis_append_hid (s : XSt N T) (p : N) : vis s p ++ hid s p = s.M p :=
  List.take_append_drop _ _

omit [Ord N] in
/-- **What a start of the reference executor removes**: a start step takes the head `t` of the
pass's order, named as the label says, and for every place `p` the tokens it removes from the
pass-visible marking (`qRemoved (vis s) t p`), followed by the queue `p` holds after the step, are
the queue `p` held before it. The same-pass tail stays. -/
theorem xstep_start_qRemoved {C : Cfg N T} {s s' : XSt N T} {n : String} {sy : Bool}
    (h : xstep C s (.start n sy) = some s') :
    ∃ t rest, s.order = t :: rest ∧ t.core.name = n ∧
      ∀ p, qRemoved (vis s) t p ++ s'.M p = s.M p := by
  obtain ⟨t, rest, ho, -, -, -, hn, -, -, rfl⟩ := startStep_some h
  refine ⟨t, rest, ho, hn, fun p => ?_⟩
  simp only [liveAfter]
  rw [← List.append_assoc, qRemoved_append_qConsume, vis_append_hid]

/-- **The removal of a reference start, event by event**: the tokens of the `TokenRemoved`
events a reference start emits for `p`, followed by the queue `p` holds after the start, are
the queue `p` held before it. -/
theorem refStart_removedAt (P : EvPol) {C : Cfg N T} (H : List (NetEvent N T)) {s s' : XSt N T}
    {n : String} {sy : Bool} (h : xstep C s (.start n sy) = some s') (p : N) :
    removedAt (refEmitW P C H s (.start n sy) s') p ++ s'.M p = s.M p := by
  obtain ⟨t, rest, ho, -, hq⟩ := xstep_start_qRemoved h
  rw [refEmitW_start P C H ho, removedAt_append, removedAt_removedEvs]
  have h0 : removedAt ([.transitionStarted n (removedListDecl (vis s) t)] : List (NetEvent N T)) p =
    [] := rfl
  rw [h0, List.append_nil, hq]

end Inversion

/-! ## Decided runs -/

section Runs

variable [DecidableEq N] [Ord N]

/-- The labelled run of the reference with events from history `H` and state `s` along the
labels `ls`, if every label is a step. -/
def refRun (P : EvPol) (C : Cfg N T) :
    List (NetEvent N T) → XSt N T → List (XLbl N T) → Option (List (EvStep N T))
  | _, _, [] => some []
  | H, s, l :: ls => (xstep C s l).bind fun s' =>
      (refRun P C (H ++ refEmitW P C H s l s') s' ls).map (⟨s, l, refEmitW P C H s l s', s'⟩ :: ·)

/-- A run `refRun` builds is a labelled run of the reference with events. -/
theorem refRun_lrun (P : EvPol) (C : Cfg N T) :
    ∀ {H : List (NetEvent N T)} {s : XSt N T} {ls : List (XLbl N T)} {run : List (EvStep N T)},
      refRun P C H s ls = some run → LRun (refEvExec P) C H s run
  | H, s, [], run, h => by cases h; trivial
  | H, s, l :: ls, run, h => by
    simp only [refRun] at h
    cases hs : xstep C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases hr : refRun P C (H ++ refEmitW P C H s l s') s' ls with
      | none => simp [hr] at h
      | some run' =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, ⟨hs, rfl⟩, refRun_lrun P C hr⟩

/-- The event trace of the reference along the labels `ls` from the initial state of `M0` at
reading `r0`, if every label is a step. -/
def refTrace (P : EvPol) (C : Cfg N T) (M0 : QMarking N T) (r0 : Nat) (ls : List (XLbl N T)) :
    Option (List (NetEvent N T)) :=
  (refRun P C (refBoot P C M0) (xinit M0 r0) ls).map fun run =>
    refBoot P C M0 ++ EvStep.events run

/-- A trace `refTrace` computes is an event trace of the reference with events. -/
theorem refTrace_trace (P : EvPol) {C : Cfg N T} {M0 : QMarking N T} {r0 : Nat}
    {ls : List (XLbl N T)} {tr : List (NetEvent N T)} (h : refTrace P C M0 r0 ls = some tr) :
    Trace (refEvExec P) C M0 r0 tr := by
  unfold refTrace at h
  cases hr : refRun P C (refBoot P C M0) (xinit M0 r0) ls with
  | none => simp [hr] at h
  | some run =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    exact ⟨run, refRun_lrun P C hr, h.symm⟩

end Runs

end Libpetri.Reference
