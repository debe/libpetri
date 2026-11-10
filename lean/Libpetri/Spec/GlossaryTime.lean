import Libpetri.Reference.Timed
import Libpetri.Spec.Glossary
import Libpetri.Spec.Ears

set_option linter.missingDocs true

/-!
# Glossary: timing

The timing terms of `spec/glossary.md` (section "Timing"), as Lean definitions over the timed
reference step (`Libpetri/Reference/Timed.lean`). As in `Glossary.lean`, nothing here redefines
the step: each term is a readable name for a definition the reference already has
(`TSt.armed`, `TSt.elapsed`, `tExpired`, `mid`, `arcPlaces`, `writes`), and the bridge lemmas at
the end show that the two agree. Each docstring quotes its glossary entry.

A timing requirement is a predicate over an abstract timed step relation `R : TRel N`, so that
it can be checked against the reference (`RefTStep`) and against a mutant. Three conditions keep
such a predicate from holding of a relation that does nothing: `Covers` (every ready transition
can take every reference firing), `CoversReap` (every expired transition can be reaped) and
`CoversDelay` (the clock can always advance). `ProjectsTo` ties the firings of a timed relation
to an untimed one, and `FramesMarking` keeps the marking fixed across every other step.

Transitions are identified by name ([TIME-010], ruling D10): a stamp is kept per name, and
`InNet X u` says that `u` is the transition the net holds under `u`'s name.

Two frames are shared by the timing blocks TIME-002 to TIME-006, so that "its timing shall not
stop it from being ready" and "shall not reap" read the same in all of them: `StaysArmed` (no
step but the transition's own reap disarms it while it stays enabled) and `ClockFrame`
(`StaysArmed`, and no delay, no reap of another name and no firing of another name that leaves
it enabled throughout moves its stamp). Their policy-generic lemmas are at the end
(`staysArmed_of`, `clockFrame_of`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing maxDurationMs)

variable {N : Type}

/-! ## Timings and the clock -/

/-- **Glossary: Timing.** "The interval `[earliest, latest]` a transition's timing specification
gives: `Immediate`, `Deadline(by)`, `Delayed(after)`, `Window(earliest, latest)` or `Exact(at)`
[TIME-001]–[TIME-006]. `Immediate` and `Delayed` have no finite latest bound; their `latest()`
is the maximum duration."

The timing of `t` in the timed net `X` (`Novel.TimedScg.Timing`, milliseconds). -/
abbrev TimingOf (X : TimedNet N) (t : Trans N) : Timing := X.timing t

/-- **Glossary: Maximum duration.** "The finite stand-in for "no latest bound", about 100 years:
`MAX_DURATION_MS` = 3153600000000 ms, or `MAX_DURATION` in Java [TIME-001]. No valid timing has
an earliest bound above it, no valid `Deadline` has a `by` above it, and no valid `Window` has a
latest bound above it [TIME-001]." -/
abbrev MaxDuration : Nat := maxDurationMs

/-- **Glossary: Firing clock.** "The monotonic time source from which the executor stamps armed
transitions and computes elapsed time [TIME-010], [TIME-015]. Its readings never decrease and
may repeat [TIME-015]."

The current reading of the firing clock in state `s`. -/
abbrev ClockReading (s : TSt N) : Nat := s.now

/-- **Glossary: Deadline tolerance.** "The per-executor grace band added to a latest bound
before a transition is reaped: 5 ms by default, and `0` for strict enforcement [TIME-013]." -/
abbrev Tolerance (X : TimedNet N) : Nat := X.tol

/-! ## Arc places and writes -/

/-- **Glossary: Arc place.** "A place on which a transition has an input, read, inhibitor or
reset arc [CORE-030]–[CORE-034]. A place the transition only deposits into is not one of its arc
places." -/
def ArcPlace (u : Trans N) (p : N) : Prop :=
  p ∈ inPlaces u ∨ ReadArc u p ∨ InhibitorArc u p ∨ ResetArc u p

/-- **Glossary: Write.** "A firing writes a place when it consumes from it, deposits into it or
drains it through a reset arc. Draining a reset place that is already empty counts as a write.
An injected token writes the place it lands in [ENV-003]. Reading through a read arc and testing
through an inhibitor arc never write [TIME-013]."

`Writes t d p`: the firing of `t` with deposit `d` writes `p`. "Consumes from it" is read as "has
an input arc on it", as the runtimes mark every input place of a fired transition dirty. The
timed step of Phase 1 has no injection, so the injection clause is not modelled here. -/
def Writes (t : Trans N) (d : List N) (p : N) : Prop :=
  p ∈ inPlaces t ∨ ResetArc t p ∨ Produced d p

/-- **Glossary: Consume** and **Reset arc**, applied without a deposit: the intermediate
marking of a firing of `t` from `m` ([TIME-012]), "its inputs are consumed and its reset places
drained" and nothing deposited yet. -/
def Mid [DecidableEq N] (t : Trans N) (m : CountMarking N) : CountMarking N :=
  fun p => if ResetArc t p then 0 else m p - Consumes t m p

/-! ## Armed, elapsed, ready, expired, reaped -/

/-- **Glossary: Armed.** "A transition is armed when it is enabled and holds a clock: a stamp,
the firing-clock reading taken by the enablement update that most recently newly armed it
[TIME-010]. A transition is newly armed when it is enabled in the initial marking, when it is
enabled after a firing or an injected token that wrote one of its arc places while it was not
armed, and when its clock restarts [TIME-012]. A transition that is not enabled is not armed. Armed is not Enabled: a
reaped transition is enabled but not armed [TIME-013]." -/
def Armed (s : TSt N) (t : Trans N) : Prop :=
  Enabled t s.m ∧ (s.stamp t.core.name).isSome

instance (s : TSt N) (t : Trans N) : Decidable (Armed s t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Glossary: Elapsed time.** "The current reading of the firing clock minus an armed
transition's stamp [TIME-010]. Only an armed transition has one."

Defined for every transition; without a stamp it is 0. -/
def Elapsed (s : TSt N) (t : Trans N) : Nat :=
  ClockReading s - (s.stamp t.core.name).getD (ClockReading s)

/-- **Glossary: Reapable.** "A transition is reapable when its timing is `Deadline` or `Window`
[TIME-013]. `Exact`, `Immediate` and `Delayed` are not reapable, though `Exact` has a deadline
in the sense of `hasDeadline()` [TIME-001], [TIME-006]." -/
def Reapable (X : TimedNet N) (t : Trans N) : Prop := (TimingOf X t).reapable = true

instance (X : TimedNet N) (t : Trans N) : Decidable (Reapable X t) :=
  inferInstanceAs (Decidable (_ = true))

/-- **Glossary: Expired.** "A reapable transition is expired when it is armed and its elapsed
time is strictly greater than its latest bound plus the deadline tolerance [TIME-013]." -/
def Expired (X : TimedNet N) (s : TSt N) (t : Trans N) : Prop :=
  Reapable X t ∧ Armed s t ∧ (TimingOf X t).latest + Tolerance X < Elapsed s t

instance (X : TimedNet N) (s : TSt N) (t : Trans N) : Decidable (Expired X s t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Glossary: Ready.** "A transition is ready when it is armed, its elapsed time is at least
its earliest bound and it is not expired [TIME-010], [EXEC-002]." -/
def Ready (X : TimedNet N) (s : TSt N) (t : Trans N) : Prop :=
  Armed s t ∧ (TimingOf X t).earliest ≤ Elapsed s t ∧ ¬ Expired X s t

instance (X : TimedNet N) (s : TSt N) (t : Trans N) : Decidable (Ready X s t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Glossary: Reaped.** "To reap an expired transition is to disarm it in the deadline step
of a cycle without firing it, emitting `TransitionTimedOut` [TIME-013], [EXEC-001], [EVT-009].
A reaped transition keeps its tokens and stays enabled but not armed, and does not fire, until a
firing or an injected token writes one of its arc places; it is then newly armed if it is
enabled [TIME-013]."

The state reading: enabled at the marking and not armed. -/
def Reaped (s : TSt N) (t : Trans N) : Prop := Enabled t s.m ∧ ¬ Armed s t

instance (s : TSt N) (t : Trans N) : Decidable (Reaped s t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Identity by name -/

/-- `u` is the transition the net holds under `u`'s name (ruling D10: transitions are
identified by name). With pairwise distinct names (`NamesDistinct`) it is membership
(`inNet_iff_mem`). -/
def InNet (X : TimedNet N) (u : Trans N) : Prop :=
  X.net.transitions.find? (·.core.name == u.core.name) = some u

/-- The transitions of the net have pairwise distinct names ([TIME-010], the identity
assumption). -/
def NamesDistinct (X : TimedNet N) : Prop :=
  (X.net.transitions.map (·.core.name)).Nodup

/-! ## The initial state and unknown places -/

/-- **Glossary: Unknown place.** "A place the net does not declare: no transition of the net has
an arc on it or names it in its output spec. Its tokens are retained in the marking, inert,
since no arc can reference them [CORE-072]."

A net of the model is its list of transitions, and a place exists by use, so a place declared
through a builder but touched by no arc and named by no output spec is an unknown place here too. -/
def UnknownPlace (X : TimedNet N) (p : N) : Prop :=
  ∀ u ∈ X.net.transitions, ¬ ArcPlace u p ∧ ¬ OutputArc u p

/-- **Initialiser** ([CORE-072]): the state an executor starts from, given the timed net, the
initial marking and the first reading of the firing clock. -/
abbrev Init (N : Type) := TimedNet N → CountMarking N → Nat → TSt N

/-- **Initial arming** (glossary: Armed, "A transition is newly armed when it is enabled in the
initial marking"): in the state `I X m0 now0` every transition of the net is armed exactly when
it is enabled in `m0`, and an enabled one holds as its stamp the state's own clock reading, so
its elapsed time is 0 (`initArms_elapsed`) ([CORE-072], [TIME-010]). -/
def InitArms (I : Init N) : Prop :=
  ∀ X m0 now0 u, InNet X u →
    (Armed (I X m0 now0) u ↔ Enabled u m0) ∧
      (Enabled u m0 → (I X m0 now0).stamp u.core.name = some (ClockReading (I X m0 now0)))

/-! ## Timed step relations -/

/-- A timed step relation: `R X s l s'` says that in the timed net `X` the executor takes the
step `l` from state `s` to state `s'`. -/
abbrev TRel (N : Type) := TimedNet N → TSt N → TLbl N → TSt N → Prop

/-- Every firing step of `R` is a firing of `F`, from the step's marking to its successor's. -/
def ProjectsTo (R : TRel N) (F : FireRel N) : Prop :=
  ∀ X s t d s', R X s (.fire t d) s' → F t s.m d s'.m

/-- Only a firing changes the marking: a delay or a reap of `R` leaves it as it is. -/
def FramesMarking (R : TRel N) : Prop :=
  ∀ X s l s', R X s l s' → (∀ t d, l ≠ .fire t d) → s'.m = s.m

/-- Every ready transition of the net can take every reference firing it has: `R` has a firing
step with the same deposit and the same successor marking. -/
def Covers [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X s t d m', t ∈ X.net.transitions → Ready X s t → RefFire t s.m d m' →
    ∃ s', R X s (.fire t d) s' ∧ s'.m = m'

/-- Every expired transition of the net can be reaped. -/
def CoversReap (R : TRel N) : Prop :=
  ∀ X s t, t ∈ X.net.transitions → Expired X s t → ∃ s', R X s (.reap t) s'

/-- The firing clock can always advance, by any amount. -/
def CoversDelay (R : TRel N) : Prop :=
  ∀ X s δ, ∃ s', R X s (.delay δ) s' ∧ ClockReading s' = ClockReading s + δ

/-! ## Frames of a transition's clock -/

/-- No step other than the reap of `u` disarms `u` while `u` stays enabled: a step from a state in
which `u` is armed, to a state in which `u` is enabled, leaves it armed unless it is the reap of
`u`. Distinct names are assumed (ruling D10), since stamps are kept per name. A firing of `u`
itself is a step like any other: it leaves `u` armed when `u` is enabled after it. Without that,
a firing could leave its own transition enabled and unarmed, which is a reap ([TIME-012] line 3,
glossary: Reaped). -/
def StaysArmed (R : TRel N) (X : TimedNet N) (u : Trans N) : Prop :=
  ∀ l, NamesDistinct X → on (fun s s' => R X s l s'), shall (fun s s' =>
    Armed s u → Enabled u s'.m → l ≠ .reap u → Armed s' u)

/-- The clock frame of `u`: `StaysArmed`, and `u`'s stamp stays as it is across a delay, across
the reap of a transition of another name, and across a firing of a transition of another name
from a state in which `u` is armed, when `u` is enabled both in the intermediate marking of that
firing and after it ([TIME-012] line 2 specialised to `u`). These steps newly arm nothing, so
they keep the elapsed time of `u` growing with the clock. The clock itself advancing by a
delay's length is [TIME-015] line 2. -/
def ClockFrame [DecidableEq N] (R : TRel N) (X : TimedNet N) (u : Trans N) : Prop :=
  StaysArmed R X u ∧
  (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' =>
    s'.stamp u.core.name = s.stamp u.core.name)) ∧
  (∀ t, t.core.name ≠ u.core.name → on (fun s s' => R X s (.reap t) s'), shall (fun s s' =>
    s'.stamp u.core.name = s.stamp u.core.name)) ∧
  (∀ t d, t.core.name ≠ u.core.name → on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
    Armed s u → Enabled u (Mid t s.m) → Enabled u s'.m →
      s'.stamp u.core.name = s.stamp u.core.name))

/-! ## Bridge lemmas: the readable forms agree with the reference definitions -/

theorem armed_iff (s : TSt N) (t : Trans N) : Armed s t ↔ s.armed t = true := by
  simp [Armed, TSt.armed, Enabled]

theorem elapsed_eq (s : TSt N) (t : Trans N) : Elapsed s t = s.elapsed t := rfl

theorem expired_iff (X : TimedNet N) (s : TSt N) (t : Trans N) :
    Expired X s t ↔ tExpired X s t = true := by
  simp [Expired, tExpired, Reapable, armed_iff, elapsed_eq, and_assoc]

/-- `Ready` is what the reference step asks of a firing transition: armed, past `refPolicy`'s
gate, not expired. -/
theorem ready_iff [DecidableEq N] (X : TimedNet N) (s : TSt N) (t : Trans N) :
    Ready X s t ↔ s.armed t = true ∧ (refPolicy (N := N)).gate X s t = true ∧
      (refPolicy (N := N)).expired X s t = false := by
  simp [Ready, refPolicy, armed_iff, elapsed_eq, expired_iff]

theorem mid_eq [DecidableEq N] (t : Trans N) (m : CountMarking N) : Mid t m = mid t m := by
  funext p
  simp [Mid, mid, fireNC]

theorem arcPlace_iff (u : Trans N) (p : N) : ArcPlace u p ↔ p ∈ arcPlaces u := by
  simp [ArcPlace, arcPlaces, inPlaces, or_assoc, or_comm, or_left_comm]

theorem writes_iff [DecidableEq N] (t : Trans N) (d : List N) (p : N) :
    Writes t d p ↔ writes t d p = true := by
  simp [Writes, writes, inPlaces, or_assoc]

theorem writesArc_iff [DecidableEq N] (t : Trans N) (d : List N) (u : Trans N) :
    writesArc t d u = true ↔ ∃ p, ArcPlace u p ∧ Writes t d p := by
  simp [writesArc, arcPlace_iff, writes_iff]

theorem inNet_mem {X : TimedNet N} {u : Trans N} (h : InNet X u) : u ∈ X.net.transitions :=
  List.mem_of_find?_eq_some h

/-- Under distinct names, `InNet` is membership. -/
theorem inNet_iff_mem {X : TimedNet N} (hX : NamesDistinct X) (u : Trans N) :
    InNet X u ↔ u ∈ X.net.transitions := by
  refine ⟨inNet_mem, fun hu => ?_⟩
  unfold InNet
  obtain ⟨v, hv⟩ : ∃ v, X.net.transitions.find? (·.core.name == u.core.name) = some v := by
    cases h : X.net.transitions.find? (·.core.name == u.core.name) with
    | some v => exact ⟨v, rfl⟩
    | none => simp [List.find?_eq_none] at h; exact absurd rfl (h u hu)
  have hvm := List.mem_of_find?_eq_some hv
  have hvn : v.core.name = u.core.name := by simpa using List.find?_some hv
  rw [hv]
  congr 1
  exact (List.inj_on_of_nodup_map hX hvm hu hvn)

/-! ## The reference step meets the coverage conditions -/

/-- Inversion of a firing step, under any policy. -/
theorem refTStepW_fire_inv [DecidableEq N] {P : Policy N} {X : TimedNet N} {s s' : TSt N}
    {t : Trans N} {d : List N} (h : RefTStepW P X s (.fire t d) s') :
    t ∈ X.net.transitions ∧ RefFire t s.m d s'.m ∧ s.armed t = true ∧ P.gate X s t = true ∧
      P.expired X s t = false ∧
      s' = { m := s'.m, now := s.now, stamp := restampAll P X s t d s'.m } := by
  match h with
  | .fire _ _ _ _ _ ht hf ha hg hx => exact ⟨ht, hf, ha, hg, hx, rfl⟩

/-- Every stamp a firing leaves, under any policy, is the one the name held before, the fresh
reading, or none. -/
theorem restampAll_cases (P : Policy N) (X : TimedNet N) (s : TSt N) (t : Trans N)
    (d : List N) (m' : N → Nat) (n : String) :
    restampAll P X s t d m' n = s.stamp n ∨ restampAll P X s t d m' n = some (P.fresh s) ∨
      restampAll P X s t d m' n = none := by
  unfold restampAll
  cases hv : X.net.transitions.find? (·.core.name == n) with
  | none => exact .inr (.inr rfl)
  | some v =>
    have hn : v.core.name = n := by simpa using List.find?_some hv
    simp only [restampW, hn]
    split_ifs <;> simp

/-- The stamp a firing leaves on the net's transition `u` is `restampW` of `u`. -/
theorem restampAll_inNet {P : Policy N} {X : TimedNet N} {u : Trans N} (hu : InNet X u)
    (s : TSt N) (t : Trans N) (d : List N) (m' : N → Nat) :
    restampAll P X s t d m' u.core.name = restampW P X s t d m' u := by
  unfold restampAll
  rw [hu]

/-- Inversion of a reference firing step. -/
theorem refTStep_fire_inv [DecidableEq N] {X : TimedNet N} {s s' : TSt N} {t : Trans N}
    {d : List N} (h : RefTStep X s (.fire t d) s') :
    t ∈ X.net.transitions ∧ RefFire t s.m d s'.m ∧ Ready X s t ∧
      s' = { m := s'.m, now := s.now, stamp := restampAll refPolicy X s t d s'.m } := by
  obtain ⟨ht, hf, ha, hg, hx, he⟩ := refTStepW_fire_inv h
  exact ⟨ht, hf, (ready_iff X s t).2 ⟨ha, hg, hx⟩, he⟩

theorem refTStep_projectsTo [DecidableEq N] : ProjectsTo (RefTStep (N := N)) RefFire :=
  fun _ _ _ _ _ h => refTStep_projects h

theorem refTStep_framesMarking [DecidableEq N] : FramesMarking (RefTStep (N := N)) :=
  fun _ _ _ _ h hl => refTStepW_marking h hl

theorem refTStep_covers [DecidableEq N] : Covers (RefTStep (N := N)) := by
  intro X s t d m' ht hr hf
  obtain ⟨ha, hg, hx⟩ := (ready_iff X s t).1 hr
  exact ⟨_, RefTStepW.fire X s t d m' ht hf ha hg hx, rfl⟩

theorem refTStep_coversReap [DecidableEq N] : CoversReap (RefTStep (N := N)) :=
  fun X s t ht hx => ⟨_, RefTStepW.reap X s t ht ((expired_iff X s t).1 hx)⟩

theorem refTStep_coversDelay [DecidableEq N] : CoversDelay (RefTStep (N := N)) :=
  fun X s δ => ⟨_, RefTStepW.delay X s δ, rfl⟩

/-! ## The reference initialiser -/

/- The reference initialiser (`Reference.TSt.init`), registered as a witness model: the
initial marking as given, the first clock reading, and a stamp equal to that reading on every
transition of the net enabled in the initial marking. It is the start state of every `RefTStep`
run. -/
#spec_witness TSt.init

/-- The reference initialiser holds the initial marking, on every place, declared or not. -/
theorem init_marking (X : TimedNet N) (m0 : CountMarking N) (now0 : Nat) :
    (TSt.init X m0 now0).m = m0 := rfl

/-- The reference initialiser starts the firing clock at the given reading. -/
theorem init_clock (X : TimedNet N) (m0 : CountMarking N) (now0 : Nat) :
    ClockReading (TSt.init X m0 now0) = now0 := rfl

/-- The reference initialiser arms exactly the transitions of the net enabled in the initial
marking, each with the first reading as its stamp. -/
theorem initArms_init : InitArms (TSt.init (N := N)) := by
  intro X m0 now0 u hu
  have hf : X.net.transitions.find? (·.core.name == u.core.name) = some u := hu
  have hs : (TSt.init X m0 now0).stamp u.core.name =
      if enabledNA m0 u.core then some now0 else none := by
    simp only [TSt.init, hf]
  refine ⟨?_, fun he => ?_⟩
  · rw [Armed, hs]
    by_cases he : enabledNA m0 u.core = true
    · simp [he, Enabled, TSt.init]
    · simp [he, Enabled, TSt.init]
  · have he' : enabledNA m0 u.core = true := he
    rw [hs, if_pos he']
    rfl

/-- Under `InitArms`, a transition of the net enabled in the initial marking starts with elapsed
time 0. -/
theorem initArms_elapsed {I : Init N} (h : InitArms I) {X : TimedNet N} {m0 : CountMarking N}
    {now0 : Nat} {u : Trans N} (hu : InNet X u) (he : Enabled u m0) :
    Elapsed (I X m0 now0) u = 0 := by
  simp [Elapsed, (h X m0 now0 u hu).2 he]

/-- No transition of the net has an unknown place among its arc places. -/
theorem unknownPlace_not_arc {X : TimedNet N} {p : N} (h : UnknownPlace X p) {u : Trans N}
    (hu : u ∈ X.net.transitions) : ¬ ArcPlace u p :=
  (h u hu).1

/-- No transition of the net names an unknown place in its output spec. -/
theorem unknownPlace_not_output {X : TimedNet N} {p : N} (h : UnknownPlace X p) {u : Trans N}
    (hu : u ∈ X.net.transitions) : ¬ OutputArc u p :=
  (h u hu).2

/-! ## The frames, for any policy -/

section Frames

variable [DecidableEq N]

/-- Under any policy whose `rearm` is the spec's, the net's transition `u` stays armed across
every step but its own reap while it stays enabled: a delay keeps every stamp, the reap of
another transition keeps `u`'s (distinct names), and a firing, of `u` itself or of another
transition, keeps `u`'s stamp or re-arms `u` because it was armed. -/
theorem staysArmed_of {P : Policy N} (hr : P.rearm = refPolicy.rearm) {X : TimedNet N}
    {u : Trans N} (hu : InNet X u) : StaysArmed (RefTStepW P) X u := by
  intro l hd s s' h ha hen hl
  cases h with
  | delay => exact ha
  | reap t ht _ =>
    have htu : u.core.name ≠ t.core.name := fun e =>
      hl (by rw [List.inj_on_of_nodup_map hd ht (inNet_mem hu) e.symm])
    exact ⟨ha.1, by show (if u.core.name = t.core.name then (none : Option Nat) else
                      s.stamp u.core.name).isSome = true
                    rw [if_neg htu]; exact ha.2⟩
  | fire t d m' _ _ _ _ _ =>
    refine ⟨hen, ?_⟩
    show (restampAll P X s t d m' u.core.name).isSome = true
    rw [restampAll_inNet hu]
    unfold restampW
    split_ifs with h1 h2
    · exact ha.2
    · rfl
    · exfalso
      have hen' : enabledNA m' u.core = true := hen
      have ha' : s.armed u = true := (armed_iff s u).1 ha
      simp [hr, refPolicy, hen', ha'] at h2

/-- A delay, under any policy, keeps every stamp. -/
theorem frame_delay {P : Policy N} {X : TimedNet N} {s s' : TSt N} {δ : Nat}
    (h : RefTStepW P X s (.delay δ) s') (n : String) : s'.stamp n = s.stamp n := by
  cases h
  rfl

/-- A reap, under any policy, keeps the stamp of every other name. -/
theorem frame_reapOther {P : Policy N} {X : TimedNet N} {s s' : TSt N} {t : Trans N}
    (h : RefTStepW P X s (.reap t) s') {n : String} (hn : n ≠ t.core.name) :
    s'.stamp n = s.stamp n := by
  cases h with
  | reap _ _ _ =>
    show (if n = t.core.name then (none : Option Nat) else s.stamp n) = _
    rw [if_neg hn]

/-- Under any policy whose `keep` is the spec's, a firing of a transition of another name keeps
the stamp of the net's transition `u` when `u` is armed before it and enabled in its
intermediate marking and after it. -/
theorem frame_fireOther {P : Policy N} (hk : P.keep = refPolicy.keep) {X : TimedNet N}
    {u t : Trans N} {d : List N} (hu : InNet X u) (hne : t.core.name ≠ u.core.name) :
    on (fun s s' => RefTStepW P X s (.fire t d) s'),
      shall (fun s s' => Armed s u → Enabled u (Mid t s.m) → Enabled u s'.m →
        s'.stamp u.core.name = s.stamp u.core.name) := by
  intro s s' h ha hmid hen
  obtain ⟨-, -, -, -, -, he⟩ := refTStepW_fire_inv h
  have hmid' : enabledNA (mid t s.m) u.core = true := by rw [← mid_eq]; exact hmid
  have hkt : P.keep X s t d s'.m u = true := by
    rw [hk]
    simp only [refPolicy, Bool.and_eq_true]
    exact ⟨⟨⟨(armed_iff s u).1 ha, by simpa using Ne.symm hne⟩, hmid'⟩, hen⟩
  rw [he]
  show restampAll P X s t d s'.m u.core.name = _
  rw [restampAll_inNet hu]
  unfold restampW
  rw [if_pos hkt]

/-- **The clock frame for any policy** whose `keep` and `rearm` are the spec's (the expiry test
and the gate may be anything). -/
theorem clockFrame_of {P : Policy N} (hk : P.keep = refPolicy.keep)
    (hr : P.rearm = refPolicy.rearm) {X : TimedNet N} {u : Trans N} (hu : InNet X u) :
    ClockFrame (RefTStepW P) X u :=
  ⟨staysArmed_of hr hu, fun _ _ _ h => frame_delay h _,
    fun _ hn _ _ h => frame_reapOther h (Ne.symm hn), fun _ _ hn => frame_fireOther hk hu hn⟩

/-- The timed reference step meets the clock frame of every transition of the net. -/
theorem clockFrame_refTStep {X : TimedNet N} {u : Trans N} (hu : InNet X u) :
    ClockFrame (RefTStep (N := N)) X u :=
  clockFrame_of rfl rfl hu

/-- The policy that drops the clock of a transition its own firing leaves enabled: as the
spec's, except that a firing never re-arms the transition that fired. -/
def selfDropPolicy : Policy N :=
  { refPolicy with
    rearm := fun X s t d m' u => refPolicy.rearm X s t d m' u && u.core.name != t.core.name }

/-- ✗ The self-firing drop breaks `StaysArmed` (a reap hidden in a firing of the transition
itself): if the net's transition `u`, armed in `s`, fires there under the self-drop policy and is
enabled after it, it is left enabled and unarmed. -/
theorem selfDrop_not_staysArmed {X : TimedNet N} {u : Trans N} (hu : InNet X u)
    (hd : NamesDistinct X) {s : TSt N} {d : List N} {m' : N → Nat}
    (ha : Armed s u) (hf : RefFire u s.m d m') (hg : (refPolicy (N := N)).gate X s u = true)
    (hx : (refPolicy (N := N)).expired X s u = false) (hen : Enabled u m') :
    ¬ StaysArmed (RefTStepW selfDropPolicy) X u := by
  intro h
  have hs := RefTStepW.fire (P := selfDropPolicy) X s u d m' (inNet_mem hu) hf
    ((armed_iff s u).1 ha) hg hx
  have := (h _ hd _ _ hs ha hen (by simp)).2
  revert this
  show ¬ (restampAll selfDropPolicy X s u d m' u.core.name).isSome = true
  rw [restampAll_inNet hu]
  simp [restampW, selfDropPolicy, refPolicy]

end Frames

end Libpetri.Spec
