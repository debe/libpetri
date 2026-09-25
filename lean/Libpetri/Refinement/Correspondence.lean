/-
# Refinement: enablement correspondence

`canEnable_rel` — enablement agrees across `Rel` — split out of
`Refinement.lean`, which keeps the consume-phase correspondence lemmas.
-/
import Libpetri.Refinement.Model

namespace Libpetri

/-! ## Correspondence lemmas -/

/-- Enablement agrees across the relation. -/
theorem canEnable_rel {n : Nat} {st : PBState} {bb : BBState}
    (hrel : Rel n st bb) {t : Transition} (hb : PlacesInBounds t n) :
    canEnable st.ring t = bbCanEnable bb.marking t := by
  unfold canEnable bbCanEnable
  have hcnt : ∀ p, p < n → st.ring.cnt p = (bb.marking p).length := by
    intro p hp
    rw [← hrel.prj p hp, Pool.proj_length hrel.wf (by rw [hrel.np]; exact hp)]
  have hA : t.inputs.all (fun sp =>
        decide (0 < st.ring.cnt sp.place)
          && decide (sp.card.required ≤ st.ring.cnt sp.place))
      = t.inputs.all (fun sp =>
        decide (0 < (bb.marking sp.place).length)
          && decide (sp.card.required ≤ (bb.marking sp.place).length)) :=
    all_congr'' (fun sp hsp => by rw [hcnt sp.place (hb.inputs sp hsp)])
  have hB : t.reads.all (fun p => decide (0 < st.ring.cnt p))
      = t.reads.all (fun p => decide (0 < (bb.marking p).length)) :=
    all_congr'' (fun p hp => by rw [hcnt p (hb.reads p hp)])
  have hC : t.inhibitors.all (fun p => st.ring.cnt p == 0)
      = t.inhibitors.all (fun p => (bb.marking p).length == 0) :=
    all_congr'' (fun p hp => by rw [hcnt p (hb.inhibitors p hp)])
  rw [hA, hB, hC]
where
  all_congr'' {α : Type} {l : List α} {f g : α → Bool}
      (h : ∀ a ∈ l, f a = g a) : l.all f = l.all g := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.all_cons]
      rw [h a List.mem_cons_self,
        ih (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]

end Libpetri
