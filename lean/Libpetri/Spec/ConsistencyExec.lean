import Libpetri.Spec.Req.EXEC_021
import Libpetri.Spec.Req.IO_015

set_option linter.missingDocs true

/-!
# Consistency of the executor requirements (skeleton)

The target of this module is one theorem, `spec_consistent_exec`, that picks one witness for
every variable the execution, concurrency and environment blocks share with the Phase 1 blocks
and shows that every block holds of it: one output validator `V` (shared with IO-015), one ready
order (shared with EXEC-002), one timed step (shared with the TIME blocks) and one executor
`E`, tied to them by agreement conjuncts, so that the result is one model.

This file is the skeleton of wave W5. `spec_consistent_exec_sketch` fixes the shape with the
first executor block: the validator `V` of IO-015 and the executor `E` of EXEC-021 are
existentials of one statement, `ValidatedBy E V` says that `E` settles every admitted completion
as `V` decides, and `ExecCovers E` keeps the conjunction from holding of an executor that takes
no step (`exec_coverage_excludes_empty`). The witnesses are `ioRefValidate` and `RefExec`.
Coverage appears only here, never in a requirement block. Later blocks add their conjuncts, and
the agreement conjuncts `OrderAgrees`, `QueueAgrees` and `AtomicAgrees` join `E` to the ready
order, the queue firing and the timed step.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

section Witness

variable {N T : Type} [DecidableEq N]

/-- The reference executor settles every admitted completion as the configured validator
decides: `commit` when it accepts (and the relay check accepts), `fail` when it rejects. -/
theorem refExec_validatedBy (V : OutputValidator N) : ValidatedBy (RefExec (T := T)) V := by
  intro C hC s i f e ⟨hf, he, hc⟩ hr
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · have h : (commitStep refXPol C s i).isSome = true := by
      unfold commitStep
      rw [hf]
      simp only [he]
      rw [if_pos (by simp [hc, hC, hv, hr, refXPol])]
      rfl
    exact Option.isSome_iff_exists.mp h
  · have h : (failStep refXPol C s i).isSome = true := by
      unfold failStep
      simp [hf, hc, failCause, he, hC, hv, refXPol]
    exact Option.isSome_iff_exists.mp h

/-- The reference executor covers the wave 0 outside steps: the clock always advances, and every
open firing can return either way. -/
theorem refExec_covers : ExecCovers (RefExec (N := N) (T := T)) := by
  refine ⟨fun C s δ => ⟨_, rfl⟩, fun C s i f ok hf ho => ?_⟩
  have h : (retStep s i ok).isSome = true := by
    unfold retStep onOpen
    simp [hf, ho]
  exact Option.isSome_iff_exists.mp h

end Witness

/-- The empty executor fails the coverage condition: the clock cannot advance. -/
theorem exec_coverage_excludes_empty {N T : Type} :
    ¬ ExecCovers (fun (_ : Cfg N T) (_ : XSt N T) (_ : XLbl N T) (_ : XSt N T) => False) := by
  rintro ⟨h, -⟩
  let C : Cfg N T :=
    { X := { net := { places := [], transitions := [] }, timing := fun _ => .immediate, tol := 0 },
      prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
      validate := fun _ _ => true, relay := fun _ _ _ => true,
      timeoutOut := fun _ _ _ => false, res := 0 }
  let s : XSt N T :=
    { M := fun _ => [], now := 0, cyc := 0, st := fun _ => .off, fl := [], nextId := 0, cq := [],
      pq := [], eq := [], mode := Mode.open, phase := .completions, order := [],
      delta := fun _ => 0, started := false, parked := false }
  obtain ⟨_, h⟩ := h C s 0
  exact h

/-- ✓ EXEC-021 and IO-015 hold together: the reference validator and the reference executor
satisfy them, the executor settles admitted completions as that validator decides, and it takes
the outside steps of the coverage condition. The skeleton of `spec_consistent_exec`. -/
@[evidence consistent EXEC_021 IO_015]
theorem spec_consistent_exec_sketch {N T : Type} [DecidableEq N] :
    ∃ (V : OutputValidator N) (E : XRel N T),
      EXEC_021 E ∧ IO_015 V ∧ ValidatedBy E V ∧ ExecCovers E :=
  ⟨ioRefValidate, RefExec, EXEC_021_reference, IO_015_reference, refExec_validatedBy _,
    refExec_covers⟩

end Libpetri.Spec
