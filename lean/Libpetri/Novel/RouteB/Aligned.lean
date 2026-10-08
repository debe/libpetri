import Libpetri.Novel.RouteB.Sound
import Libpetri.Novel.RouteB.Classify

/-!
# Route B decides name alignment: `NameAligned` and `QuiescentNameAligned` ([NU-055], [NU-050], [VER-012])

`Sound.lean` composes the layers for every class predicate that reads only the key (`keyOf`:
the base and the `canonicalKey` of the name layer). This file instantiates that composition with
the first property that reads the **name layer** itself:

* `aligned p q S`: every token resident in `p` and every token resident in `q` carry one name
  (`∀ s t, resident p s → resident q t → s = t`). It is computable (bounded quantification over
  `List.range S.bound`, exact because `S.supp` puts every live symbol below the bound) and it
  compares names by equality only, so it is invariant under renaming and hence a function of
  the key (`aligned_key_inv`, via `canonicalKey_complete`).
* `NameAligned(p, q)` is the safety property `bad := fun S => !aligned p q S`;
  `QuiescentNameAligned(p, q)` the same predicate read at resting classes only (quiescence over
  the reapable set, [VER-002] / [TIME-013] as in `routeB_untimed_quiescence_sound`).

Results:
* `aligned_eq_true_iff`, `aligned_key_inv`.
* `aligned_view_iff`: on the view of a concrete marking, for coloured `p` and `q`, `aligned` is
  `∀ c ∈ m p, ∀ d ∈ m q, nameOf c = nameOf d`. Only the membership `p ∈ co`, `q ∈ co` is needed
  (`idx` returns the first position, and that position holds `p`), not `co.Nodup`.
* `resident_of_not_mem`, `aligned_uncoloured`, `aligned_uncoloured_right`: for `p ∉ co` or
  `q ∉ co` the predicate is constantly `true`.
  The name layer has no row for an uncoloured place, so a `Proven` would say nothing about it: a
  verifier must refuse such a query (answer `Unknown` with a reason), never answer `Proven`.
* **`routeB_untimed_nameAligned_sound`**, **`routeB_untimed_quiescentNameAligned_sound`**: the
  headlines, concluding the concrete statement on the executor's tokens. They instantiate
  `Sound.lean`'s `routeB_untimed_safety_sound_keyInv` and `routeB_untimed_quiescence_sound_keyInv`.

**Scope.** Exactly that of `Sound.lean`: the untimed, environment-free, atomic instance
`routeB untimedBase` (no timed executor simulation, gap R6). Premises stated as hypotheses:
`coloured_order` duplicate-free, every transition `InFragment` for its role, unguarded input
arcs, the coloured places initially empty, `p` and `q` coloured, and for the quiescence form
`PosKeys` and `ExecRests reap`. Premises built into `NuStepC` (contracts, the [NU-052] priority
premise, one global total name projection `nameOf`) are as in `Sound.lean`; the conclusion is
about names read through that `nameOf`, so it describes the runtime only when every key and
relay `KeyFn` agrees with it (`Exec.ProjCoherent`).

**Not covered.** `Violated` is sound for the graph only (a reachable class whose name layer is
misaligned), not for the executor: a consumer fires on any resident symbol in the graph and on
the FIFO head at run time, so a misaligned class may be unreachable for the executor. A truncated
build never yields `Proven` (`Decide.truncated_never_proven`). Route A and the name-blind SMT
encodings never read the name layer, so nothing here licenses them to answer `Proven` for this
property.
-/

namespace Libpetri.Novel.RouteB

open Libpetri
open Libpetri.Novel.CanonicalKey

section Aligned

variable {co : List PlaceId} {nameOf : Colour → ℕ} {net : List NuTrans} {role : NuTrans → Role}
  {conflict : Bool}

/-! ## The alignment predicate -/

/-- **`aligned p q S`**: every symbol resident in `p` equals every symbol resident in `q`.
Bounded by `S.bound`, above every live symbol (`S.supp`), so the check is exact. -/
def aligned {β : Type} (p q : PlaceId) (S : NState co β) : Bool :=
  (List.range S.bound).all fun s => (List.range S.bound).all fun t =>
    !(resident co p S.m s && resident co q S.m t) || s == t

theorem resident_lt {β : Type} {S : NState co β} {p : PlaceId} {s : ℕ}
    (h : resident co p S.m s = true) : s < S.bound :=
  lt_of_live S.supp (resident_live p S.m s h)

theorem aligned_eq_true_iff {β : Type} {p q : PlaceId} {S : NState co β} :
    aligned p q S = true ↔
      ∀ s t, resident co p S.m s = true → resident co q S.m t = true → s = t := by
  unfold aligned
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_iff_eq]
  constructor
  · intro h s t hs ht
    rcases h s (resident_lt hs) t (resident_lt ht) with (h | h) | h
    · rw [hs] at h; cases h
    · rw [ht] at h; cases h
    · exact h
  · intro h s _ t _
    by_cases hs : resident co p S.m s = true
    · by_cases ht : resident co q S.m t = true
      · exact Or.inr (h s t hs ht)
      · exact Or.inl (Or.inr (by simpa using ht))
    · exact Or.inl (Or.inl (by simpa using hs))

/-- Alignment of a name marking (no bound): the right side of `aligned_eq_true_iff`. -/
def AlignedM (p q : PlaceId) (M : NM co) : Prop :=
  ∀ s t, resident co p M s = true → resident co q M t = true → s = t

theorem alignedM_comp {p q : PlaceId} (M : NM co) (σ : Equiv.Perm ℕ) :
    AlignedM p q (M ∘ σ) ↔ AlignedM p q M := by
  unfold AlignedM
  have hr : ∀ (x : PlaceId) (u : ℕ), resident co x (M ∘ σ) u = resident co x M (σ u) :=
    fun x u => resident_inv x M σ u
  simp only [hr]
  constructor
  · intro h s t hs ht
    have := h (σ.symm s) (σ.symm t) (by simpa using hs) (by simpa using ht)
    simpa using congrArg σ this
  · intro h s t hs ht
    exact σ.injective (h _ _ hs ht)

/-- **`aligned` reads only the key**: it is invariant under renaming, and equal keys of name
layers with finite support are one renaming orbit (`canonicalKey_complete`). -/
theorem aligned_key_inv {β : Type} (p q : PlaceId) {a b : NState co β}
    (h : keyOf a = keyOf b) : aligned p q a = aligned p q b := by
  have hm : canonicalKey a.m = canonicalKey b.m := (Prod.mk.inj h).2
  obtain ⟨σ, hσ⟩ := canonicalKey_complete (liveSet_finite a.supp) (liveSet_finite b.supp) hm
  apply Bool.eq_iff_iff.mpr
  rw [aligned_eq_true_iff, aligned_eq_true_iff]
  change AlignedM p q a.m ↔ AlignedM p q b.m
  rw [hσ, alignedM_comp]

/-! ## On the executor's view -/

theorem idx_some_of_mem {p : PlaceId} (hp : p ∈ co) : ∃ i, idx co p = some i := by
  have : (idx co p).isSome = true := by
    rw [idx_isSome_eq_contains]; exact List.contains_iff_mem.mpr hp
  exact Option.isSome_iff_exists.mp this

/-- On the view of a concrete marking, a coloured place holds a symbol iff a token in it projects
to that name. -/
theorem resident_view_iff {p : PlaceId} (hp : p ∈ co) {m : CMarking} {s : ℕ} :
    resident co p (nameLayer co nameOf m) s = true ↔ ∃ c ∈ m p, nameOf c = s := by
  obtain ⟨i, hi⟩ := idx_some_of_mem hp
  have hget : co[i.1] = p := get_of_idx hi
  unfold resident cnt
  rw [hi]
  simp only [nameLayer, hget, bne_iff_ne, ne_eq, List.length_eq_zero_iff,
    List.filter_eq_nil_iff, beq_iff_eq, not_forall, not_not, exists_prop]

/-- **`aligned` on the executor's view is the concrete statement**, for coloured `p` and `q`:
every token in `p` and every token in `q` carry one name. -/
theorem aligned_view_iff {p q : PlaceId} (hp : p ∈ co) (hq : q ∈ co) {m : CMarking} :
    aligned p q (view co nameOf m) = true ↔ ∀ c ∈ m p, ∀ d ∈ m q, nameOf c = nameOf d := by
  rw [aligned_eq_true_iff]
  change (∀ s t, resident co p (nameLayer co nameOf m) s = true →
    resident co q (nameLayer co nameOf m) t = true → s = t) ↔ _
  simp only [resident_view_iff hp, resident_view_iff hq]
  constructor
  · intro h c hc d hd
    exact h _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
  · rintro h s t ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact h c hc d hd

/-- Nothing is resident in an uncoloured place: the name layer has no row for it. -/
theorem resident_of_not_mem {p : PlaceId} (hp : p ∉ co) (M : NM co) (s : ℕ) :
    resident co p M s = false := by
  have hnone : idx co p = none := by
    have : (idx co p).isSome = false := by
      rw [idx_isSome_eq_contains]; simpa using hp
    simpa using this
  unfold resident cnt
  rw [hnone]
  rfl

/-- **An uncoloured place makes `aligned` vacuous.** The name layer has no row for `p ∉ co`, so
nothing is resident there and `aligned p q S` holds of every class: a `Proven` would carry no
information about `p`. This is why the property must be refused (`Unknown` with a reason) for
an uncoloured place, never decided. -/
theorem aligned_uncoloured {β : Type} {p : PlaceId} (hp : p ∉ co) (q : PlaceId)
    (S : NState co β) : aligned p q S = true :=
  aligned_eq_true_iff.mpr fun s _ hs _ => by rw [resident_of_not_mem hp] at hs; cases hs

/-- The symmetric case: an uncoloured `q` makes `aligned` vacuous too. -/
theorem aligned_uncoloured_right {β : Type} (p : PlaceId) {q : PlaceId} (hq : q ∉ co)
    (S : NState co β) : aligned p q S = true :=
  aligned_eq_true_iff.mpr fun _ t _ ht => by rw [resident_of_not_mem hq] at ht; cases ht

/-! ## Headlines -/

/-- **`NameAligned(p, q)`: a Route B `Proven` holds for the untimed, environment-free
executor.** A complete build whose safety verdict for `!aligned p q` is
`Proven`: in every marking an untimed, injection-free executor run reaches, every token in `p`
and every token in `q` carry one name. `p` and `q` must be coloured (`aligned_uncoloured`). -/
theorem routeB_untimed_nameAligned_sound (hco : co.Nodup)
    (hfr : ∀ T ∈ net, InFragment co T (role T)) (hG : ∀ T ∈ net, GuardFree T.base)
    {p q : PlaceId} (hp : p ∈ co) (hq : q ∈ co)
    {maxClasses : ℕ} {cut : ℕ → Bool} {stopBad : NState co AMarking → Bool} {stopAt : Bool}
    {fuel : ℕ} {m0 : CMarking} (hempty : ∀ i : Fin co.length, m0 co[i.1] = [])
    (hP : Decide.verdict (routeB untimedBase net role conflict)
      (Decide.build (routeB untimedBase net role conflict) maxClasses cut stopBad stopAt fuel
        (initState co (alpha m0)))
      (.safety fun S => !aligned p q S) = .proven)
    {m : CMarking} (hR : Relation.ReflTransGen (NuStepC co nameOf net role conflict) m0 m) :
    ∀ c ∈ m p, ∀ d ∈ m q, nameOf c = nameOf d := by
  have h := routeB_untimed_safety_sound_keyInv hco hfr hG (bad := fun S => !aligned p q S)
    (fun a b hk => by rw [aligned_key_inv p q hk]) hempty hP hR
  exact (aligned_view_iff hp hq).mp (by simpa using h)

/-- **`QuiescentNameAligned(p, q)`: a Route B `Proven` holds for the untimed, environment-free
executor**, deadline reaping included ([TIME-013], [VER-002]). A
complete build whose quiescence verdict for `!aligned p q` over the reapable set `reap` is
`Proven`: in every marking an untimed, injection-free executor run reaches and rests at
(`ExecRests reap`), every token in `p` and every token in `q` carry one name. Needs `PosKeys`
beyond the safety premises; `p` and `q` must be coloured. -/
theorem routeB_untimed_quiescentNameAligned_sound (hco : co.Nodup)
    (hfr : ∀ T ∈ net, InFragment co T (role T)) (hpos : ∀ T ∈ net, PosKeys (role T))
    (hG : ∀ T ∈ net, GuardFree T.base) {p q : PlaceId} (hp : p ∈ co) (hq : q ∈ co)
    {reap : String → Bool} {maxClasses : ℕ} {cut : ℕ → Bool}
    {stopBad : NState co AMarking → Bool} {stopAt : Bool} {fuel : ℕ} {m0 : CMarking}
    (hempty : ∀ i : Fin co.length, m0 co[i.1] = [])
    (hP : Decide.verdict (routeB untimedBase net role conflict)
      (Decide.build (routeB untimedBase net role conflict) maxClasses cut stopBad stopAt fuel
        (initState co (alpha m0)))
      (.quiescence (fun S => !aligned p q S) reap) = .proven)
    {m : CMarking} (hR : Relation.ReflTransGen (NuStepC co nameOf net role conflict) m0 m)
    (hrest : ExecRests (co := co) (nameOf := nameOf) (net := net) reap m) :
    ∀ c ∈ m p, ∀ d ∈ m q, nameOf c = nameOf d := by
  have h := routeB_untimed_quiescence_sound_keyInv hco hfr hpos hG
    (bad := fun S => !aligned p q S) (fun a b hk => by rw [aligned_key_inv p q hk]) hempty hP
    hR hrest
  exact (aligned_view_iff hp hq).mp (by simpa using h)

end Aligned

end Libpetri.Novel.RouteB
