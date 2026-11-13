import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.TIME_010
import Libpetri.Spec.Text.CONC_005

set_option linter.missingDocs true

/-!
# CONC-005: Dirty set optimization (`spec/05-concurrency.md`)

The requirement is a predicate over an abstract timed step relation `R : TRel N` (glossary
`GlossaryTime.lean`), at the grain of the atomic Phase 1 step, like the TIME blocks. A
re-evaluation is seen through what it decides: whether the transition is armed. The evidence
theorems check the statement against the timed reference step (`RefTStep`), against a step that
re-evaluates every transition after every firing, a reverse index that holds input places only,
an enablement update that disarms a written transition that stays enabled, a firing that consumes
through a read arc, a step that drops the clock of every transition it does not re-evaluate, a
step that restarts the clock of every armed transition, and a reap that disarms the transitions
sharing an arc place with the reaped one; and against a mutant reading that leaves reaps out of
the frame of line 4.

Line 1 is TIME-010's line 1 without the stamp and with the fired transition's own exception;
line 2 is TIME-010's line 3 for an armed transition as well (deliberate overlap: CONC-005 is the
requirement that says "only"). Line 4 restates for every step what the clock frame of TIME-012
says about the steps that do not touch a transition's arc places.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CONC-005: Dirty set optimization -/

requirement CONC_005
  id "CONC-005"
  title "Dirty Set Optimization"
  kind B
  scope "all executors"
  source verbatim "spec/05-concurrency.md"
  covers CONC_005.s1, CONC_005.s2, CONC_005.s3
  reading "For every timed net X:"
          "a transition of the net that is not armed before a step and is armed after it was armed by a firing, either of a transition of its own name or one that writes one of its arc places;"
          "a firing that writes an arc place of the net's transition u leaves u armed if u is enabled after it, whether or not u was armed before it;"
          "a firing that writes none of u's arc places leaves u enabled after it exactly when u was enabled before it;"
          "a step that is not a firing of a transition of u's name, not a firing that writes one of u's arc places, and not the reap of a transition of u's name leaves the net's transition u, if it was armed before the step, armed after it with the stamp it held."
  assumes "A step relates two states of the executor (glossary: TSt), each holding a marking, the reading of the firing clock and a stamp per transition name; a step is a delay of the clock, a firing or a reap (TRel). Firings are atomic: the step that starts a firing completes it, so no transition is in flight. Arc place, Write, Enabled and Armed are the glossary terms (GlossaryTime.lean)."
          "The quoted sentences speak of the enablement check (glossary: Enablement check); a re-evaluation is a run of it, and the lines read its verdict as Enabled: for a transition that has no match specification the enablement check passes exactly when the transition is enabled (CONC-008, its fourth shall sentence), and the transitions of the model (Reference.Trans) carry no match specification, so every transition of the net is such a transition (ruling D30). The ν-match check of a transition with a match specification (NU-020) reads only the tokens of its correlated inputs, which are arc places, so line 3 holds of it as well; it is not encoded here."
          "A re-evaluation is read through what it decides. The enablement update that re-evaluates a transition leaves it armed when it is enabled and not armed when it is not enabled (TIME-010, TIME-011); a transition it does not re-evaluate keeps the state it had, its stamp included. The step relation shows a re-evaluation only through Armed and the stamp, so the lines speak of those: the runtimes' per-transition enabled flag is the glossary's Armed (a reaped transition has it cleared, rust/libpetri-runtime/src/bitmap_backend.rs enforce_deadlines). With reaping the skip is behaviour, not only cost (ruling D6, clash conc-a#6): re-evaluating a reaped transition none of whose arc places was written would arm it again (TIME-013 line 6, Libpetri.deadline_reap_dirty_diverges), which line 1 forbids (CONC_005_forbids_rearmAny)."
          "Line 2 is the first quoted sentence: every transition one of whose arc places the firing writes is re-evaluated, armed before or not, so it is armed after the firing exactly when it is enabled after it (Armed implies Enabled gives the other direction). An enablement update that disarms a written transition that stays enabled, by arming only the transitions that were not armed, breaks it (CONC_005_forbids_armedLost). The reverse index is complete: an arc place is an input, read, inhibitor or reset place (glossary: Arc place, ruling D6), and a reverse index that holds input places only misses a transition whose inhibitor place is drained (CONC_005_forbids_inputOnly). The stamp a re-evaluation gives a transition it arms, and whether a firing restarts the clock of a written transition that stays enabled, are TIME-010 and TIME-012."
          "Lines 1 and 4 are the second quoted sentence. Line 1 is its half for a transition that is not armed: only a firing that writes one of its arc places, or a firing of the transition itself, arms it; a delay or a reap arms nothing. Line 4 is its half for a transition that is armed: a step that does not re-evaluate it, which is every delay, every reap of another name and every firing of another name that writes none of its arc places, leaves it armed with its stamp. A reap that disarms the transitions sharing an arc place with the reaped one (CONC_005_forbids_reapDisarms), a firing that drops the clock of every transition it does not re-evaluate (CONC_005_forbids_dropClean) and one that restarts the clock of every armed transition (CONC_005_forbids_restartAll) break line 4. Line 4 states only the step from armed to armed: that such a step arms no transition that was not armed is line 1."
          "The exception 'or when the transition itself fires' is in lines 1 and 4 by name: the transition whose firing it is may be re-evaluated whatever its firing writes (Rust marks it dirty when its firing starts, bitmap_backend.rs post_fire; Java and TypeScript when its completion is processed, BitmapNetExecutor.java). That a transition does not fire from a state in which it is not armed is TIME-010 line 5, and what its own firing does to its clock is [TIME-012]; the reap of the transition itself is TIME-013."
          "Line 3 is the third quoted sentence, the section's 'only transitions affected by that place need re-evaluation' made a requirement: skipping a transition is correct only if a firing that writes none of its arc places leaves its enablement as it was. A write is the glossary's Write (ruling D6): consuming, depositing, and draining through a reset arc, a reset place that is already empty included; reading through a read arc and testing through an inhibitor arc never write. The section's 'tokens are added or removed from a place' is read as a write: an input arc counts even where nothing would be consumed, and draining an empty reset place counts although no token moves. Line 3 follows from the marking update of a firing ([CORE-022]); it excludes a step whose firing changes a place it does not write, for instance one that consumes the token of a read arc (CONC_005_forbids_readConsumes), under which skipping a transition would leave a stale enablement. Like the sentence, it has no exception: it speaks of the fired transition and of transitions outside the net too."
          "The third quoted sentence is stated per change of the marking (the consumption of a firing, the deposit of a firing, an injected token), because in all three runtimes an asynchronous action's deposit is made when its completion is processed, in a later cycle than its consumption, with other firings and injected tokens between. One step of R is an atomic firing: its consumption followed by its deposit with nothing between, and a place it writes is a place its consumption or its deposit writes (glossary: Write). So line 3 is the sentence applied to the two halves in turn; the interleaved case is the companion block CONC_005_cycle over the executor model (RefExec), named below."
          "Transitions are identified by name (ruling D10): a stamp is kept per name, and lines 1, 2 and 4 speak of the transition the net holds under the name (InNet)."
          "Injected tokens are not steps of the Phase 1 relation, which has no environment places, and the glossary's Writes leaves its injection clause out: the injection half of each quoted sentence is not encoded by this block. It is encoded with [ENV-003] over the executor model (RefExec) by the companion block CONC_005_cycle of this ID (lean/Libpetri/Spec/Req/CONC_005_cycle.lean; ruling D33 (a): a second block with the same ID). That companion also carries the consumption and the deposit of a firing as separate steps with other steps between, the enablement update of a cycle (which update performs a re-evaluation: the one of the cycle that takes the write in), and the fourth shall sentence of the markdown, the one on a reaped transition ([TIME-013]): its enablement check is not re-run while it is reaped, and only a firing or an injected token that writes one of its arc places ends its reaped state. This block does not quote that sentence. It carries the transition in flight as well: in Java and TypeScript an enablement update skips a transition whose firing is in flight although a firing wrote one of its arc places, and re-evaluates it when its completion is processed; whether a transition may start again while a firing of it is in flight is implementation-defined under ruling D8 (b), carried by the configuration (Cfg.reentrant)."
          "The evaluation of every transition at the start of a run, in the initial marking, is not a re-evaluation: it is the initial state (TSt.init, [TIME-010]); the runtimes mark every transition dirty once, when the marking is initialised."
          "The reverse index 'maps each place to the set of transitions that reference it': a transition references a place when the place is one of its arc places; a transition that only deposits into the place does not (glossary: Arc place, ruling D6, clash conc-a#7). The reverse index as a data structure is [CONC-007]; this block states its behaviour: complete (line 2), and sound because unwritten arc places keep their counts (line 3)."
          "The second paragraph (the dirty set is a bitmap, the executor sets the bits of the affected transitions, only dirty transitions are re-evaluated each cycle) is the representation of the quoted sentences (kind Q): no step relation observes a bit or a cycle. 'When a place changes' is read as a write."
          "AC1 (adding a token to place P only marks transitions connected to P as dirty): 'marks as dirty' is the representation of 'will be re-evaluated', and 'connected to P' is 'P is one of its arc places'; its behaviour is lines 1, 2 and 4, exercised by CONC_005_nonvacuous and CONC_005_nonvacuous_kept: a firing that deposits into place 0 arms the transition with an input arc on 0 and keeps an armed one armed, a firing that writes no place leaves the reaped transition reaped and an armed one armed with its stamp, and a reap leaves an armed competitor armed. AC2 (transitions not connected to P are not re-evaluated) is lines 1 and 4, with the mutants CONC_005_forbids_rearmAny, CONC_005_forbids_dropClean, CONC_005_forbids_restartAll and CONC_005_forbids_reapDisarms. AC3 (dirty bits are cleared after re-evaluation) is representation (kind Q) and is not encoded. The test derivation (50 transitions, exactly 3 re-evaluated) counts re-evaluations, a cost ([PERF-003]), and is not encoded."
  signoff "2026-11-13 1b18cd61a73e4270 ai"
  statement : ∀ {N : Type} [DecidableEq N], TRel N → Prop :=
    fun R => ∀ X : TimedNet _,
      (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => ¬ Armed s u →
          Armed s' u → ∃ t d, l = .fire t d ∧
            (t.core.name = u.core.name ∨ ∃ p, ArcPlace u p ∧ Writes t d p))) ∧
      (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun _ s' =>
          (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m → Armed s' u)) ∧
      (∀ t d u, on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
          (∀ p, ArcPlace u p → ¬ Writes t d p) → (Enabled u s'.m ↔ Enabled u s.m))) ∧
      (∀ l u, InNet X u →
          (∀ t d, l = .fire t d → u.core.name ≠ t.core.name ∧ ∀ p, ArcPlace u p → ¬ Writes t d p) →
          (∀ v, l = .reap v → v.core.name ≠ u.core.name) →
          on (fun s s' => R X s l s'), shall (fun s s' =>
            Armed s u → Armed s' u ∧ s'.stamp u.core.name = s.stamp u.core.name))

/- The pinned readable form of CONC-005: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_005 : {N : Type} → [DecidableEq N] → TRel N → Prop :=
fun {N} [DecidableEq N] R =>
  ∀ (X : TimedNet N),
    (∀ (l : TLbl N) (u : Reference.Trans N),
        InNet X u →
          on fun s s' => R X s l s', shall fun s s' =>
            ¬Armed s u →
              Armed s' u → ∃ t d, l = TLbl.fire t d ∧ (t.core.name = u.core.name ∨ ∃ p, ArcPlace u p ∧ Writes t d p)) ∧
      (∀ (t : Reference.Trans N) (d : List N) (u : Reference.Trans N),
          InNet X u →
            on fun s s' => R X s (TLbl.fire t d) s', shall fun x s' =>
              (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m → Armed s' u) ∧
        (∀ (t : Reference.Trans N) (d : List N) (u : Reference.Trans N),
            on fun s s' => R X s (TLbl.fire t d) s', shall fun s s' =>
              (∀ (p : N), ArcPlace u p → ¬Writes t d p) → (Enabled u s'.m ↔ Enabled u s.m)) ∧
          ∀ (l : TLbl N) (u : Reference.Trans N),
            InNet X u →
              (∀ (t : Reference.Trans N) (d : List N),
                  l = TLbl.fire t d → u.core.name ≠ t.core.name ∧ ∀ (p : N), ArcPlace u p → ¬Writes t d p) →
                (∀ (v : Reference.Trans N), l = TLbl.reap v → v.core.name ≠ u.core.name) →
                  on fun s s' => R X s l s', shall fun s s' =>
                    Armed s u → Armed s' u ∧ s'.stamp u.core.name = s.stamp u.core.name
-/
#guard_msgs in #print CONC_005

/-! ### Unwritten places and the frame of a firing -/

section Lines

variable {N : Type} [DecidableEq N]

/-- A place the firing of `t` with deposit `d` does not write keeps its count, whatever is
deposited elsewhere. -/
theorem conc005_fireNC_unwritten (m : N → Nat) (t : Trans N) (d : List N) (p : N)
    (h : ¬ Writes t d p) : fireNC m t.core (depProd d) p = m p := by
  simp only [Writes, inPlaces, Produced, not_or] at h
  obtain ⟨hi, hr, hd⟩ := h
  have hr' : p ∉ t.core.resets := hr
  have hn : nspecAt t.core p = none := by
    simp only [nspecAt, List.find?_eq_none, decide_eq_true_eq]
    intro s hs hp
    exact hi (List.mem_map.2 ⟨s, hs, hp⟩)
  simp [fireNC, hr', nconsumed, hn, depProd, List.count_eq_zero_of_not_mem hd]

omit [DecidableEq N] in
/-- Enablement reads arc places only: two markings that agree on every arc place of `u` agree
on whether `u` is enabled. -/
theorem conc005_enabledNA_congr_arc (u : Trans N) (m m' : N → Nat)
    (h : ∀ p, ArcPlace u p → m' p = m p) : enabledNA m' u.core = enabledNA m u.core := by
  unfold enabledNA
  have h1 : u.core.inputs.all (fun s => decide (s.card.required ≤ m' s.place))
      = u.core.inputs.all (fun s => decide (s.card.required ≤ m s.place)) :=
    all_congr_mem (fun s hs => by
      rw [h s.place (Or.inl (List.mem_map.2 ⟨s, hs, rfl⟩))])
  have h2 : u.core.inhibitors.all (fun p => m' p == 0) =
      u.core.inhibitors.all (fun p => m p == 0) :=
    all_congr_mem (fun p hp => by rw [h p (Or.inr (Or.inr (Or.inl hp)))])
  have h3 : u.core.reads.all (fun p => decide (1 ≤ m' p)) =
      u.core.reads.all (fun p => decide (1 ≤ m p)) :=
    all_congr_mem (fun p hp => by rw [h p (Or.inr (Or.inl hp))])
  rw [h1, h2, h3]

/-- Line 3 for any policy: a firing that writes none of `u`'s arc places leaves `u`'s
enablement as it was. -/
theorem conc005_frame {P : Policy N} {X : TimedNet N} {s s' : TSt N} {t : Trans N} {d : List N}
    (h : RefTStepW P X s (.fire t d) s') (u : Trans N)
    (hw : ∀ p, ArcPlace u p → ¬ Writes t d p) :
    enabledNA s'.m u.core = enabledNA s.m u.core := by
  obtain ⟨-, hf, -⟩ := refTStepW_fire_inv h
  have hm : s'.m = fireNC s.m t.core (depProd d) := hf.2.2
  exact conc005_enabledNA_congr_arc u s.m s'.m
    (fun p hp => by rw [hm]; exact conc005_fireNC_unwritten s.m t d p (hw p hp))

/-- The intermediate marking of a firing that writes none of `u`'s arc places enables `u`
exactly when the marking before it does. -/
theorem conc005_mid_frame (s : TSt N) (t : Trans N) (u : Trans N) (d : List N)
    (hw : ∀ p, ArcPlace u p → ¬ Writes t d p) :
    enabledNA (mid t s.m) u.core = enabledNA s.m u.core :=
  conc005_enabledNA_congr_arc u s.m (mid t s.m) (fun p hp => by
    have := conc005_fireNC_unwritten s.m t [] p (fun hx => hw p hp (by
      rcases hx with hx | hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact absurd hx (by simp [Produced])))
    have e : (depProd ([] : List N)) = fun _ => 0 := by funext x; simp [depProd]
    rw [e] at this
    simpa [mid] using this)

omit [DecidableEq N] in
/-- Under a policy whose `keep` asks for an armed transition, a firing leaves a stamp exactly
when it keeps or re-arms. -/
theorem conc005_restampW_isSome {P : Policy N}
    (hk : ∀ X s t d m' u, P.keep X s t d m' u = true → s.armed u = true)
    (X : TimedNet N) (s : TSt N) (t : Trans N) (d : List N) (m' : N → Nat) (u : Trans N) :
    (restampW P X s t d m' u).isSome = true ↔
      (P.keep X s t d m' u = true ∨ P.rearm X s t d m' u = true) := by
  unfold restampW
  by_cases h1 : P.keep X s t d m' u = true
  · have h := hk X s t d m' u h1
    simp only [TSt.armed, Bool.and_eq_true] at h
    simp [h1, h.2]
  · by_cases h2 : P.rearm X s t d m' u = true
    · simp [h1, h2]
    · simp [h1, h2]

end Lines

/-- The timed reference step satisfies CONC-005. Line 1 is TIME-010's line 1. Line 2 holds
because `refPolicy.rearm` arms every transition that is enabled after the firing and was armed or
had an arc place written, and `refPolicy.keep` keeps only a stamp there is. Line 3 is the marking
update of a firing, which changes written places only. Line 4 holds because a delay keeps every
stamp and the marking, a reap keeps the stamp of every other name and the marking, and
`refPolicy.keep` keeps the stamp of an armed transition of another name that the firing leaves
enabled in its intermediate marking and after it, which line 3 gives. -/
@[evidence holds CONC_005]
theorem CONC_005_reference {N : Type} [DecidableEq N] : CONC_005 (RefTStep (N := N)) := by
  intro X
  obtain ⟨h1, -, -, -, -⟩ := TIME_010_reference (N := N) X
  refine ⟨fun l u hu s s' h hna ha => ?_, fun t d u hu s s' h hw hen => ?_,
    fun t d u s s' h hw => ?_, fun l u hu hf hr s s' h ha => ?_⟩
  · obtain ⟨t, d, rfl, hw, -⟩ := h1 l u hu s s' h hna ha
    exact ⟨t, d, rfl, .inr hw⟩
  · obtain ⟨-, -, -, -, -, he⟩ := refTStepW_fire_inv h
    have hst : s'.stamp = restampAll refPolicy X s t d s'.m := congrArg TSt.stamp he
    refine ⟨hen, ?_⟩
    rw [hst, restampAll_inNet hu, conc005_restampW_isSome refPolicy_keep_armed]
    have hwa := (writesArc_iff t d u).2 hw
    have hen' : enabledNA s'.m u.core = true := hen
    exact .inr (by simp [refPolicy, hwa, hen'])
  · show enabledNA s'.m u.core = true ↔ enabledNA s.m u.core = true
    rw [conc005_frame h u hw]
  · have hen : Enabled u s'.m := by
      cases l with
      | delay δ => rw [refTStepW_marking h (fun _ _ e => by cases e)]; exact ha.1
      | reap v => rw [refTStepW_marking h (fun _ _ e => by cases e)]; exact ha.1
      | fire t d =>
        show enabledNA s'.m u.core = true
        rw [conc005_frame h u (hf t d rfl).2]; exact ha.1
    have hst : s'.stamp u.core.name = s.stamp u.core.name := by
      cases l with
      | delay δ => exact frame_delay h _
      | reap v => exact frame_reapOther h (fun e => hr v rfl e.symm)
      | fire t d =>
        obtain ⟨hne, hw⟩ := hf t d rfl
        have hmid : Enabled u (Mid t s.m) := by
          show enabledNA (Mid t s.m) u.core = true
          rw [mid_eq, conc005_mid_frame s t u d hw]; exact ha.1
        exact frame_fireOther rfl hu (Ne.symm hne) s s' h ha hmid hen
    exact ⟨⟨hen, by rw [hst]; exact ha.2⟩, hst⟩

/-! ### Examples: a transition inhibited by a drained place -/

/-- `u` is inhibited by place `0` and has no other arc. -/
def conc005_u : Trans Nat :=
  { core := { name := "u", inputs := [], inhibitors := [0], reads := [], resets := [] },
    out := none }

/-- `drain` consumes one token from place `0`. -/
def conc005_drain : Trans Nat :=
  { core := { name := "drain", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The net of the inhibitor example: `drain` and `u`, every transition `Immediate`. -/
def conc005_X : TimedNet Nat :=
  { net := { places := [0], transitions := [conc005_drain, conc005_u] },
    timing := fun _ => .immediate, tol := 0 }

theorem conc005_u_inX : InNet conc005_X conc005_u := rfl

/-- One token in place `0`: `drain` is armed since `0`, `u` is inhibited and holds no clock. -/
def conc005_s0 : TSt Nat :=
  { m := fun p => if p = 0 then 1 else 0, now := 0,
    stamp := fun n => if n = "drain" then some 0 else none }

/-- The state after `drain` fires from `conc005_s0` under policy `P`. -/
def conc005_after (P : Policy Nat) : TSt Nat :=
  { m := fireNC conc005_s0.m conc005_drain.core (depProd []), now := 0,
    stamp := restampAll P conc005_X conc005_s0 conc005_drain []
      (fireNC conc005_s0.m conc005_drain.core (depProd [])) }

/-- `drain` fires from `conc005_s0` under every policy whose gate and expiry are the spec's. -/
theorem conc005_drain_fires {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) :
    RefTStepW P conc005_X conc005_s0 (.fire conc005_drain []) (conc005_after P) := by
  refine RefTStepW.fire _ _ _ _ _ (by simp [conc005_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
    (by decide) ?_ ?_
  · rw [hg]; decide
  · rw [hx]; decide

/-! ### Examples: an armed transition across a write, a firing elsewhere, and a reap -/

/-- The source and `u` both armed, one token in place `0`, at `T = 20`; `u` armed since `10`,
every other name since `0`. -/
def conc005_sA : TSt Nat :=
  { m := fun p => if p = 0 then 1 else 0, now := 20,
    stamp := fun n => if n = "u" then some 10 else some 0 }

/-- The state after the source deposits into place `0` from `conc005_sA` under policy `P`. -/
def conc005_afterSrc (P : Policy Nat) : TSt Nat :=
  { m := fireNC conc005_sA.m time010_src.core (depProd [0]), now := 20,
    stamp := restampAll P time010_X conc005_sA time010_src [0]
      (fireNC conc005_sA.m time010_src.core (depProd [0])) }

/-- The state after `w` (which writes no place) fires from `conc005_sA`, in TIME-010's net
with `w`, under policy `P`. -/
def conc005_afterW (P : Policy Nat) : TSt Nat :=
  { m := fireNC conc005_sA.m time010_w.core (depProd []), now := 20,
    stamp := restampAll P time010_Y conc005_sA time010_w []
      (fireNC conc005_sA.m time010_w.core (depProd [])) }

/-- `a` has timing `Deadline(5)` and an input arc on place `0`. -/
def conc005_a : Trans Nat :=
  { core := { name := "a", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- `b` is `Immediate` with an input arc on place `0`: a competitor of `a`. -/
def conc005_b : Trans Nat :=
  { core := { name := "b", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The net of the reap example: `a` and `b`, tolerance 0. -/
def conc005_rX : TimedNet Nat :=
  { net := { places := [0], transitions := [conc005_a, conc005_b] },
    timing := fun t => if t.core.name = "a" then .deadline 5 else .immediate, tol := 0 }

theorem conc005_b_in : InNet conc005_rX conc005_b := rfl

/-- One token in place `0`, `T = 10`, `a` and `b` armed since `0`: `a` is expired. -/
def conc005_rs : TSt Nat :=
  { m := fun p => if p = 0 then 1 else 0, now := 10, stamp := fun _ => some 0 }

/-- The state the reference reap of `a` leaves. -/
def conc005_rsRef : TSt Nat :=
  { conc005_rs with stamp := fun n => if n = conc005_a.core.name then none else conc005_rs.stamp n }

/-- The reference reaps `a` from `conc005_rs`. -/
theorem conc005_reap_ref : RefTStep conc005_rX conc005_rs (.reap conc005_a) conc005_rsRef :=
  RefTStepW.reap _ _ _ (by simp [conc005_rX]) (by decide)

/-! ### Wrong models -/

/-- ✗ Re-evaluating every transition after every firing violates CONC-005 (line 1): from a state
in which `u` is reaped (enabled, no clock), `w` fires and writes no place, and the re-evaluation
of every transition arms `u` again. -/
@[evidence forbids CONC_005]
theorem CONC_005_forbids_rearmAny : ¬ CONC_005 (RefTStepW time010_rearmAnyPolicy) := fun h => by
  obtain ⟨t, d, e, hx⟩ := (h time010_Y).1 _ time010_u time010_u_inY _ _
    (time010_w_fires (P := time010_rearmAnyPolicy) rfl rfl) (by decide) (by decide)
  cases e
  rcases hx with hn | ⟨p, -, hw⟩
  · exact absurd hn (by decide)
  · simp [Writes, inPlaces, ResetArc, Produced, time010_w] at hw

/-- A reverse index that holds input places only: a firing arms an enabled transition that does
not keep its clock if it was armed or if the firing writes one of its input places. -/
def conc005_inputOnlyRearm (s : TSt Nat) (t : Trans Nat) (d : List Nat) (m' : Nat → Nat)
    (u : Trans Nat) : Bool :=
  enabledNA m' u.core && (s.armed u || (u.core.inputs.map (fun i => i.place)).any (writes t d))

/-- The policy whose reverse index holds input places only; everything else as the spec's. -/
def conc005_inputOnlyPolicy : Policy Nat :=
  { refPolicy with rearm := fun _ s t d m' u => conc005_inputOnlyRearm s t d m' u }

/-- ✗ A reverse index that holds input places only violates CONC-005 (line 2): `drain` empties
place `0`, the inhibitor place of `u`, and `u`, enabled after it, is not armed. -/
@[evidence forbids CONC_005]
theorem CONC_005_forbids_inputOnly : ¬ CONC_005 (RefTStepW conc005_inputOnlyPolicy) := fun h => by
  have := (h conc005_X).2.1 conc005_drain [] conc005_u conc005_u_inX _ _
    (conc005_drain_fires (P := conc005_inputOnlyPolicy) rfl rfl)
    ⟨0, by simp [ArcPlace, InhibitorArc, conc005_u],
      by simp [Writes, inPlaces, conc005_drain]⟩ (by decide)
  have hs : ((conc005_after conc005_inputOnlyPolicy).stamp conc005_u.core.name).isSome = false := by
    simp [conc005_after, restampAll, conc005_X, conc005_u, conc005_drain, restampW,
      conc005_inputOnlyPolicy, conc005_inputOnlyRearm, refPolicy, TSt.armed, conc005_s0,
      enabledNA]
  rw [this.2] at hs
  exact absurd hs (by decide)

/-- An enablement update that, for each transition one of whose arc places the firing writes,
clears its flag and sets it again only if it is enabled and was not armed ("arm the newly
enabled"): an armed, written transition is neither kept nor re-armed. Everything else as the
spec's. -/
def conc005_armedLostPolicy : Policy Nat :=
  { refPolicy with
    keep := fun X s t d m' u => refPolicy.keep X s t d m' u && !writesArc t d u
    rearm := fun _ s t d m' u => enabledNA m' u.core &&
      (writesArc t d u && !s.armed u || !writesArc t d u && s.armed u) }

/-- The source fires from `conc005_sA` under every policy whose gate and expiry are the
spec's. -/
theorem conc005_src_firesA {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) :
    RefTStepW P time010_X conc005_sA (.fire time010_src [0]) (conc005_afterSrc P) := by
  refine RefTStepW.fire _ _ _ _ _ (by simp [time010_X]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
    (by decide) ?_ ?_
  · rw [hg]; decide
  · rw [hx]; decide

/-- ✗ Disarming a written transition that stays enabled violates CONC-005 (line 2): `u` is armed,
the source deposits into its input place `0`, `u` is enabled after the firing and the mutant
leaves it unarmed, so it never fires until another write. -/
@[evidence forbids CONC_005]
theorem CONC_005_forbids_armedLost : ¬ CONC_005 (RefTStepW conc005_armedLostPolicy) := fun h => by
  have := (h time010_X).2.1 time010_src [0] time010_u time010_u_inX _ _
    (conc005_src_firesA (P := conc005_armedLostPolicy) rfl rfl)
    ⟨0, by simp [ArcPlace, inPlaces, time010_u], by simp [Writes, Produced]⟩ (by decide)
  exact absurd this (by decide)

/-- A step whose firing also takes the token of every read place of the fired transition (a
read arc treated as an input arc), and keeps the clock and the stamps. -/
def conc005_readConsumes : TRel Nat := fun _ s l s' =>
  match l with
  | .fire t d => s'.m = (fun p => if p ∈ t.core.reads then 0 else fireNC s.m t.core (depProd d) p) ∧
      s'.now = s.now ∧ s'.stamp = s.stamp
  | _ => False

/-- `reader` has a read arc on place `0` and no other arc. -/
def conc005_reader : Trans Nat :=
  { core := { name := "reader", inputs := [], inhibitors := [], reads := [0], resets := [] },
    out := none }

/-- ✗ A firing that consumes through a read arc violates CONC-005 (line 3): `reader` writes no
place, yet its firing empties place `0`, the input place of `time010_u`, which is enabled before
the firing and not after it. -/
@[evidence forbids CONC_005]
theorem CONC_005_forbids_readConsumes : ¬ CONC_005 conc005_readConsumes := fun h => by
  let s : TSt Nat := { m := fun p => if p = 0 then 1 else 0, now := 0, stamp := fun _ => none }
  let s' : TSt Nat :=
    { m := fun p => if p ∈ conc005_reader.core.reads then 0
        else fireNC s.m conc005_reader.core (depProd []) p, now := 0, stamp := fun _ => none }
  have hstep : conc005_readConsumes time010_X s (.fire conc005_reader []) s' := ⟨rfl, rfl, rfl⟩
  have hw : ∀ p, ArcPlace time010_u p → ¬ Writes conc005_reader [] p := fun p _ hp => by
    simp [Writes, inPlaces, ResetArc, Produced, conc005_reader] at hp
  have := (h time010_X).2.2.1 conc005_reader [] time010_u s s' hstep hw
  exact absurd (this.2 (by decide)) (by decide)

/-- The policy that keeps or re-arms only transitions whose arc places the firing writes: a
transition the firing does not re-evaluate loses its clock. -/
def conc005_dropCleanPolicy : Policy Nat :=
  { refPolicy with
    keep := fun X s t d m' u => refPolicy.keep X s t d m' u && writesArc t d u
    rearm := fun _ _ t d m' u => enabledNA m' u.core && writesArc t d u }

/-- `src` has no arc place at all: no firing writes one. -/
theorem conc005_src_unwritten (t : Trans Nat) (d : List Nat) :
    ∀ p, ArcPlace time010_src p → ¬ Writes t d p := fun p hp => by
  simp [ArcPlace, inPlaces, ReadArc, InhibitorArc, ResetArc, time010_src] at hp

/-- ✗ Dropping the clock of every transition that is not re-evaluated violates CONC-005
(line 4): from the reaped state of TIME-010's example, `w` fires and writes no place, and the
source, armed before and with no arc place at all, is not armed after it. -/
@[evidence forbids CONC_005]
theorem CONC_005_forbids_dropClean : ¬ CONC_005 (RefTStepW conc005_dropCleanPolicy) := fun h => by
  have := (h time010_Y).2.2.2 _ time010_src rfl
    (fun t d e => by cases e; exact ⟨by decide, conc005_src_unwritten _ _⟩)
    (fun _ e => by cases e) _ _
    (time010_w_fires (P := conc005_dropCleanPolicy) rfl rfl) (by decide)
  exact absurd this.1 (by decide)

/-- The policy that keeps no stamp: every firing restarts the clock of every transition it
leaves enabled and that was armed or had an arc place written. -/
def conc005_restartAllPolicy : Policy Nat := { refPolicy with keep := fun _ _ _ _ _ _ => false }

/-- `w` fires from `conc005_sA` under every policy whose gate and expiry are the spec's. -/
theorem conc005_w_firesA {P : Policy Nat} (hg : P.gate = refPolicy.gate)
    (hx : P.expired = refPolicy.expired) :
    RefTStepW P time010_Y conc005_sA (.fire time010_w []) (conc005_afterW P) := by
  refine RefTStepW.fire _ _ _ _ _ (by simp [time010_Y]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
    (by decide) ?_ ?_
  · rw [hg]; decide
  · rw [hx]; decide

/-- `w` writes none of `u`'s arc places. -/
theorem conc005_w_unwritten_u : ∀ p, ArcPlace time010_u p → ¬ Writes time010_w [] p :=
  fun p _ hp => by simp [Writes, inPlaces, ResetArc, Produced, time010_w] at hp

/-- ✗ Restarting the clock of every armed transition on every firing violates CONC-005
(line 4): `w` writes none of `u`'s arc places, yet `u`'s stamp moves from `10` to `20`, so
`u` (`Delayed(3)`), ready at `T = 20` before the firing, is not ready after it. -/
@[evidence forbids CONC_005]
theorem CONC_005_forbids_restartAll : ¬ CONC_005 (RefTStepW conc005_restartAllPolicy) :=
    fun h => by
  have := (h time010_Y).2.2.2 _ time010_u time010_u_inY
    (fun t d e => by cases e; exact ⟨by decide, conc005_w_unwritten_u⟩)
    (fun _ e => by cases e) _ _
    (conc005_w_firesA (P := conc005_restartAllPolicy) rfl rfl) (by decide)
  have h1 : (conc005_afterW conc005_restartAllPolicy).stamp "u" = some 20 := by decide
  have h2 : conc005_sA.stamp "u" = some 10 := by decide
  have h3 := this.2
  change (conc005_afterW conc005_restartAllPolicy).stamp "u" = conc005_sA.stamp "u" at h3
  rw [h1, h2] at h3
  exact absurd h3 (by decide)

/-- `t` and `v` share an arc place. -/
def conc005_shares {N : Type} [DecidableEq N] (t v : Trans N) : Bool :=
  (arcPlaces t).any (fun p => decide (p ∈ arcPlaces v))

/-- A step that is the reference on delays and firings, and whose reap of an expired transition
of the net clears its own stamp and the stamp of every transition of the net sharing an arc
place with it (as if the reap had written those places, re-arming none of them). -/
def conc005_reapSharedRel {N : Type} [DecidableEq N] : TRel N := fun X s l s' =>
  match l with
  | .delay δ => RefTStep X s (.delay δ) s'
  | .fire t d => RefTStep X s (.fire t d) s'
  | .reap t => t ∈ X.net.transitions ∧ tExpired X s t = true ∧
      s' = { s with stamp := fun n =>
        if (n == t.core.name ||
            X.net.transitions.any (fun v => v.core.name == n && conc005_shares t v))
        then none else s.stamp n }

/-- The state the mutant reap of `a` leaves. -/
def conc005_rsShared : TSt Nat :=
  { conc005_rs with stamp := fun n =>
      if (n == conc005_a.core.name ||
          conc005_rX.net.transitions.any (fun v => v.core.name == n && conc005_shares conc005_a v))
      then none else conc005_rs.stamp n }

/-- ✗ A reap that disarms the transitions sharing an arc place with the reaped one violates
CONC-005 (line 4): the reap of `a` writes no place, yet `b`, armed before and enabled after, is
left unarmed. -/
@[evidence forbids CONC_005]
theorem CONC_005_forbids_reapDisarms : ¬ CONC_005 (conc005_reapSharedRel (N := Nat)) :=
    fun h => by
  have hstep : conc005_reapSharedRel conc005_rX conc005_rs (.reap conc005_a) conc005_rsShared :=
    ⟨by simp [conc005_rX], by decide, rfl⟩
  have := (h conc005_rX).2.2.2 _ conc005_b conc005_b_in (fun _ _ e => by cases e)
    (fun v e => by cases e; decide) _ _ hstep (by decide)
  exact absurd this.1 (by decide)

/-! ### Mutant: no frame for a reap -/

/-- Mutant reading of CONC-005 under which "only when a firing or an injected token writes one
of its arc places" constrains firings alone: line 4 is asked of delays and firings, and a reap
of another transition may change whether a transition is armed. Lines 1 to 3 are as in
CONC-005. -/
def CONC_005_mutant_noReapFrame {N : Type} [DecidableEq N] (R : TRel N) : Prop :=
  ∀ X : TimedNet N,
    (∀ l u, InNet X u → on (fun s s' => R X s l s'), shall (fun s s' => ¬ Armed s u →
        Armed s' u → ∃ t d, l = .fire t d ∧
          (t.core.name = u.core.name ∨ ∃ p, ArcPlace u p ∧ Writes t d p))) ∧
    (∀ t d u, InNet X u → on (fun s s' => R X s (.fire t d) s'), shall (fun _ s' =>
        (∃ p, ArcPlace u p ∧ Writes t d p) → Enabled u s'.m → Armed s' u)) ∧
    (∀ t d u, on (fun s s' => R X s (.fire t d) s'), shall (fun s s' =>
        (∀ p, ArcPlace u p → ¬ Writes t d p) → (Enabled u s'.m ↔ Enabled u s.m))) ∧
    (∀ l u, InNet X u → (∀ v, l ≠ .reap v) →
        (∀ t d, l = .fire t d → u.core.name ≠ t.core.name ∧ ∀ p, ArcPlace u p → ¬ Writes t d p) →
        on (fun s s' => R X s l s'), shall (fun s s' =>
          Armed s u → Armed s' u ∧ s'.stamp u.core.name = s.stamp u.core.name))

/-- The reap that disarms the transitions sharing an arc place with the reaped one kills the
mutant: it is the reference on delays and firings and arms nothing on a reap, so it meets the
mutant reading, but CONC-005's line 4 keeps the competitor armed across the reap
(`CONC_005_forbids_reapDisarms`). -/
@[evidence mutant CONC_005]
theorem CONC_005_mutant_noReapFrame_killed :
    CONC_005_mutant_noReapFrame (conc005_reapSharedRel (N := Nat)) ∧
      ¬ CONC_005 (conc005_reapSharedRel (N := Nat)) := by
  refine ⟨fun X => ?_, CONC_005_forbids_reapDisarms⟩
  obtain ⟨r1, r2, r3, r4⟩ := CONC_005_reference (N := Nat) X
  refine ⟨fun l u hu s s' h hna ha => ?_, fun t d u hu s s' h => r2 t d u hu s s' h,
    fun t d u s s' h => r3 t d u s s' h, fun l u hu hnr hf s s' h => ?_⟩
  · cases l with
    | delay δ => exact r1 _ u hu s s' h hna ha
    | fire t d => exact r1 _ u hu s s' h hna ha
    | reap v =>
      obtain ⟨-, -, rfl⟩ := h
      exfalso
      apply hna
      obtain ⟨he, hs⟩ := ha
      refine ⟨he, ?_⟩
      simp only at hs
      split at hs
      · simp at hs
      · exact hs
  · cases l with
    | delay δ => exact r4 _ u hu hf (fun _ e => by cases e) s s' h
    | fire t d => exact r4 _ u hu hf (fun _ e => by cases e) s s' h
    | reap v => exact absurd rfl (hnr v)

/-! ### Every line exercised -/

/-- The source fires from TIME-010's reaped state under the reference step. -/
theorem conc005_src_fires : RefTStep time010_Y time010_r0 (.fire time010_src [0])
    (time010_rAfter refPolicy time010_src [0]) :=
  RefTStepW.fire _ _ _ _ _ (by simp [time010_Y]) ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩
    (by decide) (by decide) (by decide)

/-- Lines 1 to 4 are exercised by the reference step on transitions that are not armed. In
TIME-010's reaped state at `T = 20` (`u` enabled with no clock, the source and `w` armed), `w`
fires and writes none of the arc places of `u` or of the source: `u` stays enabled (line 3) and
unarmed (line 1), and the source stays armed (line 4). The source fires and deposits into place
`0`, the input place of `u`, and `u` is armed again (lines 1 and 2). In the inhibitor example,
`drain` empties place `0`, the inhibitor place of `u`, and `u`, enabled after it, is armed
(line 2). -/
@[evidence nonvacuous CONC_005]
theorem CONC_005_nonvacuous :
    RefTStep time010_Y time010_r0 (.fire time010_w []) (time010_rAfter refPolicy time010_w []) ∧
      (∀ p, ArcPlace time010_u p → ¬ Writes time010_w [] p) ∧
      Enabled time010_u time010_r0.m ∧
      Enabled time010_u (time010_rAfter refPolicy time010_w []).m ∧
      ¬ Armed time010_r0 time010_u ∧ ¬ Armed (time010_rAfter refPolicy time010_w []) time010_u ∧
      (∀ p, ArcPlace time010_src p → ¬ Writes time010_w [] p) ∧
      Armed time010_r0 time010_src ∧ Armed (time010_rAfter refPolicy time010_w []) time010_src ∧
      RefTStep time010_Y time010_r0 (.fire time010_src [0])
        (time010_rAfter refPolicy time010_src [0]) ∧
      ArcPlace time010_u 0 ∧ Writes time010_src [0] 0 ∧
      Armed (time010_rAfter refPolicy time010_src [0]) time010_u ∧
      RefTStep conc005_X conc005_s0 (.fire conc005_drain []) (conc005_after refPolicy) ∧
      InhibitorArc conc005_u 0 ∧ Writes conc005_drain [] 0 ∧
      ¬ Armed conc005_s0 conc005_u ∧ Armed (conc005_after refPolicy) conc005_u := by
  refine ⟨time010_w_fires rfl rfl, conc005_w_unwritten_u, by decide, by decide, by decide,
    by decide, conc005_src_unwritten _ _, by decide, by decide, conc005_src_fires, ?_, ?_,
    by decide, conc005_drain_fires rfl rfl, ?_, ?_, by decide, by decide⟩
  · simp [ArcPlace, inPlaces, time010_u]
  · simp [Writes, Produced]
  · simp [InhibitorArc, conc005_u]
  · simp [Writes, inPlaces, conc005_drain]

/-- Lines 2 and 4 are exercised by the reference step on transitions that are armed. From
`conc005_sA` (`u` armed since `10`, `T = 20`), the source deposits into place `0`, the input place
of `u`, and `u`, enabled after it, stays armed (line 2, the case `CONC_005_forbids_armedLost`
breaks). From the same state `w` fires and writes none of `u`'s arc places, and `u` stays armed
with stamp `10` (line 4, the case `CONC_005_forbids_restartAll` breaks). In the reap example the
reap of `a` leaves `b`, which shares place `0` with it, armed with its stamp (line 4 on a reap, the
case `CONC_005_forbids_reapDisarms` breaks). -/
@[evidence nonvacuous CONC_005]
theorem CONC_005_nonvacuous_kept :
    RefTStep time010_X conc005_sA (.fire time010_src [0]) (conc005_afterSrc refPolicy) ∧
      Armed conc005_sA time010_u ∧ ArcPlace time010_u 0 ∧ Writes time010_src [0] 0 ∧
      Armed (conc005_afterSrc refPolicy) time010_u ∧
      RefTStep time010_Y conc005_sA (.fire time010_w []) (conc005_afterW refPolicy) ∧
      (∀ p, ArcPlace time010_u p → ¬ Writes time010_w [] p) ∧
      Armed (conc005_afterW refPolicy) time010_u ∧
      (conc005_afterW refPolicy).stamp "u" = some 10 ∧ conc005_sA.stamp "u" = some 10 ∧
      RefTStep conc005_rX conc005_rs (.reap conc005_a) conc005_rsRef ∧
      conc005_shares conc005_a conc005_b = true ∧
      Armed conc005_rs conc005_b ∧ Armed conc005_rsRef conc005_b ∧
      conc005_rsRef.stamp "b" = conc005_rs.stamp "b" := by
  refine ⟨conc005_src_firesA rfl rfl, by decide, ?_, ?_, by decide, conc005_w_firesA rfl rfl,
    conc005_w_unwritten_u, by decide, by decide, by decide, conc005_reap_ref, by decide,
    by decide, by decide, by decide⟩
  · simp [ArcPlace, inPlaces, time010_u]
  · simp [Writes, Produced]

end Libpetri.Spec
