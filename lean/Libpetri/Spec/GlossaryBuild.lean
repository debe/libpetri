import Libpetri.Reference.Build
import Libpetri.Spec.GlossaryTime
import Libpetri.Spec.Req.TIME_001

set_option linter.missingDocs true

/-!
# Glossary: building transitions and nets

The joins between the structure model (`Reference/Build.lean`) and the models the existing blocks
are stated over. Nothing here defines building again: each term is a projection of a builder onto
a model an existing block already takes, and the lemmas show that the reference builders project
onto the existing witnesses.

* `projBuild` is the build check of a transition builder as the IO and EXEC-012 blocks take it
  (`Build : Trans N → Option String`); `projBuild_ref` shows that the reference transition
  builder projects onto `refBuild`, the `Build` of `spec_consistent_queue`.
* `TimingAgree` ties a transition builder to TIME-001's timing contract: on arcs that build, the
  builder accepts a given timing exactly when the contract's builder does, and a transition built
  without a timing has the contract's default. Without it a joint model would have two
  unconnected transition builders (TIME-001's `Q.build` and CORE-020's), which is how CORE-020's
  first line 4 contradicted TIME-001 unnoticed.
* `NetNamesDistinct` lifts the identity assumption of ruling D10 (`NamesDistinct`) to a built
  net; `toTimed_timing` shows that the timed view of a built net gives each transition its own
  definition's timing, and `built_timing_valid` that every timing a built net hands the timed step
  is valid.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

variable {N A : Type}

/-! ## The build check of a transition builder -/

/-- The build check of a transition builder `B`, as the existing blocks
take it (`Build : Trans N → Option String`, `none` = builds, `some msg` = fails with `msg`): build
the transition's arcs and output specification with no timing, priority or action given. -/
def projBuild (B : TBuilder N A) (t : Trans N) : Option String :=
  match B.build 0 ⟨t.core, t.out, none, none, none⟩ with
  | .error e => some e
  | .ok _ => none

/-- A build call of the reference transition builder fails with `e` exactly when the reference
build function fails with `e`. -/
theorem refTransBuild_error [DecidableEq N] [ToString N] {k : Nat} {i : TransIn N A} {e : String} :
    (refTransBuild (N := N) (A := A)).build k i = .error e ↔ refTransBuildRaw k i = .error e := by
  dsimp only [refTransBuild]
  split
  · rename_i z h
    constructor
    · intro c; cases c
    · intro c; rw [h] at c; cases c
  · rename_i e' h
    rw [h]
    exact ⟨fun c => by cases c; rfl, fun c => by cases c; rfl⟩

/-- **Agreement lemma.** The reference transition builder projects onto the reference builder
`refBuild`, the `Build` witness of `spec_consistent_queue`: its build check fails exactly when
`refBuild` does, with `refBuild`'s message. So every block stated over `Build` is about the same
builder as the blocks stated over the transition builder. -/
theorem projBuild_ref [DecidableEq N] [ToString N] :
    projBuild (refTransBuild (N := N) (A := A)) = refBuild := by
  funext t
  have hr : refBuild (TransIn.toTrans (⟨t.core, t.out, none, none, none⟩ : TransIn N A)) =
      refBuild t := rfl
  unfold projBuild
  cases hB : (refTransBuild (N := N) (A := A)).build 0 ⟨t.core, t.out, none, none, none⟩ with
  | error e =>
    have he := refTransBuild_error.1 hB
    unfold refTransBuildRaw at he
    rw [hr] at he
    cases hb : refBuild t with
    | none => rw [hb] at he; cases he
    | some e' => rw [hb] at he; cases he; rfl
  | ok x =>
    have hx := refTransBuildRaw_ok.1 (refTransBuild_ok.1 hB)
    exact ((refBuild_eq_none_iff t).2 hx.1).symm

/-! ## Agreement with TIME-001's timing contract -/

/-- **Timing agreement** of a transition builder `TB` with a timing contract `Q` ([TIME-001]):
(1) on an input whose arcs and output specification build, `TB` builds a given timing exactly
when `Q`'s transition builder does; (2) a transition `TB` builds without a timing has `Q`'s
default timing. -/
def TimingAgree [DecidableEq N] (TB : TBuilder N A) (Q : TimingContract) : Prop :=
  (∀ k (i : TransIn N A) tm, Builds i.toTrans → i.timing = some tm →
    ((∃ x, TB.build k i = .ok x) ↔ ∃ v, Q.build tm = .ok v)) ∧
  (∀ k (i : TransIn N A) x, TB.build k i = .ok x → i.timing = none →
    (TB.defOf x).timing = Q.defaultTiming)

/-- The reference transition builder agrees with TIME-001's reference contract. -/
theorem refTransBuild_timingAgree [DecidableEq N] [ToString N] :
    TimingAgree (refTransBuild (N := N) (A := A)) refTimingQ := by
  refine ⟨fun k i tm hb ht => ?_, fun k i x hx ht => ?_⟩
  · rw [refTransBuild_succeeds]
    show _ ↔ ∃ v, refTimingFactory tm = .ok v
    constructor
    · rintro ⟨-, hv⟩
      exact ⟨tm, refTimingFactory_ok.2 ⟨hv tm ht, rfl⟩⟩
    · rintro ⟨v, hv⟩
      refine ⟨hb, fun tm' ht' => ?_⟩
      rw [ht] at ht'
      cases ht'
      exact (refTimingFactory_ok.1 hv).1
  · show x.1.2.timing = Timing.immediate
    rw [refTransBuild_def hx]
    show i.timing.getD .immediate = .immediate
    rw [ht]; rfl

/-- The timing agreement does work in a joint model: with a contract that satisfies TIME-001, a
transition built without a timing has timing `Immediate`. CORE-020 alone does not state the
default (it cites TIME-001's last line), so a builder whose default is `Delayed(0)` meets CORE-020
and is rejected only here. -/
theorem timingAgree_default [DecidableEq N] {TB : TBuilder N A} {Q : TimingContract}
    (hQ : TIME_001 Q) (hag : TimingAgree TB Q) {k : Nat} {i : TransIn N A} {x : TB.I}
    (hx : TB.build k i = .ok x) (ht : i.timing = none) : (TB.defOf x).timing = .immediate :=
  (hag.2 k i x hx ht).trans hQ.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Built nets -/

/-- The transitions of a built net have pairwise distinct names: the identity assumption of
ruling D10 (`NamesDistinct`), on a built net. No builder checks it (ruling D23). -/
def NetNamesDistinct (b : BuiltNet N A) : Prop := (b.trans.map (·.core.name)).Nodup

/-- The firing view of a definition is reapable exactly when its timing is: the coherence
assumption of `TimedNet` holds by construction. -/
theorem toTrans_reapable (d : TransDef N A) : d.toTrans.reapable = d.timing.reapable := rfl

/-- The timed view of a built net has the transition names of the built net. -/
theorem toTimed_names (b : BuiltNet N A) (tol : Nat) :
    (b.toTimed tol).net.transitions.map (·.core.name) = b.trans.map (·.core.name) := by
  simp [BuiltNet.toTimed, BuiltNet.toNet, List.map_map, Function.comp_def, TransDef.toTrans]

/-- The D10 assumption on a built net is the D10 assumption on its timed view. -/
theorem netNamesDistinct_iff (b : BuiltNet N A) (tol : Nat) :
    NamesDistinct (b.toTimed tol) ↔ NetNamesDistinct b := by
  unfold NamesDistinct NetNamesDistinct
  rw [toTimed_names]

/-- In a list of definitions with pairwise distinct names, looking a member up by its name finds
it. -/
theorem find_name_of_nodup :
    ∀ (l : List (TransDef N A)) (d : TransDef N A), (l.map (·.core.name)).Nodup → d ∈ l →
      l.find? (·.core.name == d.core.name) = some d
  | [], _, _, h => absurd h List.not_mem_nil
  | e :: l, d, hn, hm => by
    rw [List.map_cons, List.nodup_cons] at hn
    by_cases he : e.core.name = d.core.name
    · have hed : e = d := by
        rcases List.mem_cons.1 hm with h | h
        · exact h.symm
        · exact absurd (he ▸ List.mem_map_of_mem (f := (·.core.name)) h) hn.1
      rw [List.find?_cons_of_pos (by simpa using he), hed]
    · have hd : d ∈ l := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd (h ▸ rfl) he
        · exact h
      rw [List.find?_cons_of_neg (by simpa using he)]
      exact find_name_of_nodup l d hn.2 hd

/-- Under the D10 assumption the timed view of a built net gives each of its transitions its own
definition's timing. -/
theorem toTimed_timing {b : BuiltNet N A} (hn : NetNamesDistinct b) (tol : Nat)
    {d : TransDef N A} (hd : d ∈ b.trans) : (b.toTimed tol).timing d.toTrans = d.timing := by
  show ((b.trans.find? (fun e : TransDef N A => e.core.name == d.core.name)).map
    (fun e : TransDef N A => e.timing)).getD Timing.immediate = d.timing
  rw [find_name_of_nodup b.trans d hn hd]
  rfl

/-- Every timing the timed view of a net built from the reference builders hands the timed step
is valid: it is the timing of a transition of the net, which the reference transition builder
checked, or `Immediate`. -/
theorem built_timing_valid [DecidableEq N] [ToString N]
    {inp : NetIn (refTransBuild (N := N) (A := A))} {b : BuiltNet N A}
    (h : refNetBuild inp = .ok b) (tol : Nat) (t : Trans N) :
    ((b.toTimed tol).timing t).Valid := by
  show (((b.trans.find? (fun e : TransDef N A => e.core.name == t.core.name)).map
    (fun e : TransDef N A => e.timing)).getD Timing.immediate).Valid
  cases hf : b.trans.find? (fun e : TransDef N A => e.core.name == t.core.name) with
  | none => exact trivial
  | some d => exact (refNetBuild_trans_ok h d (List.mem_of_find?_eq_some hf)).2

end Libpetri.Spec
