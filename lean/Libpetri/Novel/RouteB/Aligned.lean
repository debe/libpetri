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
* `alignedAll ps S`: `aligned p q S` for every `p` and `q` in `ps`, self pairs included, so the
  places of `ps` together hold at most one distinct name; a singleton `[p]` says `p` never holds
  two names.
* `NameAligned(ps)` is the safety property `bad := fun S => !alignedAll ps S` for the
  property's places `ps`; `QuiescentNameAligned(ps)` the same predicate read at resting classes
  only (quiescence over the reapable set, [VER-002] / [TIME-013] as in
  `routeB_untimed_quiescence_sound`).

Results:
* The pair form, the building block: `aligned_eq_true_iff`, `aligned_key_inv`,
  `aligned_view_iff` (on the view of a concrete marking, for coloured `p` and `q`, `aligned` is
  `∀ c ∈ m p, ∀ d ∈ m q, nameOf c = nameOf d`; it needs only the membership `p ∈ co`, `q ∈ co`,
  not `co.Nodup`, as `idx` returns the first position and that position holds `p`),
  `resident_of_not_mem`, `aligned_uncoloured`, `aligned_uncoloured_right` (for `p ∉ co` or
  `q ∉ co` the pair predicate is constantly `true`).
* The list form: `alignedAll_eq_true_iff`; `alignedAll_congr_mem` (only membership counts, so
  order and duplicates are free); `alignedAll_key_inv`; `alignedAll_view_iff` (all members
  coloured, no `Nodup` needed); `alignedAll_uncoloured` (`alignedAll ps` is `alignedAll` of the
  coloured members alone). The name layer has no row for an uncoloured place, so a `Proven`
  would say nothing about it: a verifier must refuse such a query (answer `Unknown` with a
  reason), never answer `Proven`.
* **`routeB_untimed_nameAligned_sound`**, **`routeB_untimed_quiescentNameAligned_sound`**: the
  headlines, concluding the concrete statement on the executor's tokens. They instantiate
  `Sound.lean`'s `routeB_untimed_safety_sound_keyInv` and `routeB_untimed_quiescence_sound_keyInv`.

**Scope.** Exactly that of `Sound.lean`: the untimed, environment-free, atomic instance
`routeB untimedBase` (no timed executor simulation, gap R6). Premises stated as hypotheses:
`coloured_order` duplicate-free, every transition `InFragment` for its role, unguarded input
arcs, the coloured places initially empty, every member of `ps` coloured, and for the
quiescence form `PosKeys` and `ExecRests reap`. Premises built into `NuStepC` (contracts, the
[NU-052] priority premise, one global total name projection `nameOf`) are as in `Sound.lean`;
the conclusion is about names read through that `nameOf`, so it describes the runtime only
when every key and relay `KeyFn` agrees with it (`Exec.ProjCoherent`).

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
information about `p` (lifted to lists by `alignedAll_uncoloured`). -/
theorem aligned_uncoloured {β : Type} {p : PlaceId} (hp : p ∉ co) (q : PlaceId)
    (S : NState co β) : aligned p q S = true :=
  aligned_eq_true_iff.mpr fun s _ hs _ => by rw [resident_of_not_mem hp] at hs; cases hs

/-- The symmetric case: an uncoloured `q` makes `aligned` vacuous too. -/
theorem aligned_uncoloured_right {β : Type} (p : PlaceId) {q : PlaceId} (hq : q ∉ co)
    (S : NState co β) : aligned p q S = true :=
  aligned_eq_true_iff.mpr fun _ t _ ht => by rw [resident_of_not_mem hq] at ht; cases ht

/-! ## Over a list of places: one name across all -/

/-- **`alignedAll ps S`**: every pair of places of `ps`, self pairs included, is `aligned`, so the
places of `ps` together hold at most one distinct name. A singleton `[p]` says that `p` never
holds two names. -/
def alignedAll {β : Type} (ps : List PlaceId) (S : NState co β) : Bool :=
  ps.all fun p => ps.all fun q => aligned p q S

theorem alignedAll_eq_true_iff {β : Type} {ps : List PlaceId} {S : NState co β} :
    alignedAll ps S = true ↔ ∀ p ∈ ps, ∀ q ∈ ps, aligned p q S = true := by
  simp only [alignedAll, List.all_eq_true]

/-- **Only membership counts**: order and duplicates of `ps` do not change `alignedAll`, so
deduplicating the list and fixing its order (for the description) are free. -/
theorem alignedAll_congr_mem {β : Type} {ps ps' : List PlaceId} (h : ∀ x, x ∈ ps ↔ x ∈ ps')
    (S : NState co β) : alignedAll ps S = alignedAll ps' S := by
  apply Bool.eq_iff_iff.mpr
  simp only [alignedAll_eq_true_iff, h]

/-- **`alignedAll` reads only the key**: each conjunct does (`aligned_key_inv`). -/
theorem alignedAll_key_inv {β : Type} (ps : List PlaceId) {a b : NState co β}
    (h : keyOf a = keyOf b) : alignedAll ps a = alignedAll ps b := by
  apply Bool.eq_iff_iff.mpr
  simp only [alignedAll_eq_true_iff, aligned_key_inv _ _ h]

/-- **`alignedAll` on the executor's view is the concrete statement**, for a list of coloured
places: all tokens in the places of `ps` carry one name. Neither `ps.Nodup` nor `co.Nodup` is
needed. -/
theorem alignedAll_view_iff {ps : List PlaceId} (hps : ∀ p ∈ ps, p ∈ co) {m : CMarking} :
    alignedAll ps (view co nameOf m) = true ↔
      ∀ p ∈ ps, ∀ q ∈ ps, ∀ c ∈ m p, ∀ d ∈ m q, nameOf c = nameOf d := by
  rw [alignedAll_eq_true_iff]
  constructor
  · intro h p hp q hq
    exact (aligned_view_iff (hps p hp) (hps q hq)).mp (h p hp q hq)
  · intro h p hp q hq
    exact (aligned_view_iff (hps p hp) (hps q hq)).mpr (h p hp q hq)

/-- **An uncoloured member contributes nothing.** Every row and column of a place outside `co`
is vacuous (`aligned_uncoloured`, `aligned_uncoloured_right`), so `alignedAll ps` is
`alignedAll` of the coloured members alone: a `Proven` would say nothing about an uncoloured
member (and with no coloured member it holds of every class). This is why the property must be
refused (`Unknown` with a reason) when any member is uncoloured, never decided. -/
theorem alignedAll_uncoloured {β : Type} (ps : List PlaceId) (S : NState co β) :
    alignedAll ps S = alignedAll (ps.filter fun p => co.contains p) S := by
  apply Bool.eq_iff_iff.mpr
  simp only [alignedAll_eq_true_iff, List.mem_filter, List.contains_iff_mem]
  constructor
  · intro h p hp q hq
    exact h p hp.1 q hq.1
  · intro h p hp q hq
    by_cases hpc : p ∈ co
    · by_cases hqc : q ∈ co
      · exact h p ⟨hp, by simpa using hpc⟩ q ⟨hq, by simpa using hqc⟩
      · exact aligned_uncoloured_right p hqc S
    · exact aligned_uncoloured hpc q S

/-! ## Headlines -/

/-- **`NameAligned(ps)`: a Route B `Proven` holds for the untimed, environment-free
executor.** A complete build whose safety verdict for `!alignedAll ps` is `Proven`: in every
marking an untimed, injection-free executor run reaches, all tokens in the places of `ps` carry
one name. Every member of `ps` must be coloured (`alignedAll_uncoloured`). -/
theorem routeB_untimed_nameAligned_sound (hco : co.Nodup)
    (hfr : ∀ T ∈ net, InFragment co T (role T)) (hG : ∀ T ∈ net, GuardFree T.base)
    {ps : List PlaceId} (hps : ∀ p ∈ ps, p ∈ co)
    {maxClasses : ℕ} {cut : ℕ → Bool} {stopBad : NState co AMarking → Bool} {stopAt : Bool}
    {fuel : ℕ} {m0 : CMarking} (hempty : ∀ i : Fin co.length, m0 co[i.1] = [])
    (hP : Decide.verdict (routeB untimedBase net role conflict)
      (Decide.build (routeB untimedBase net role conflict) maxClasses cut stopBad stopAt fuel
        (initState co (alpha m0)))
      (.safety fun S => !alignedAll ps S) = .proven)
    {m : CMarking} (hR : Relation.ReflTransGen (NuStepC co nameOf net role conflict) m0 m) :
    ∀ p ∈ ps, ∀ q ∈ ps, ∀ c ∈ m p, ∀ d ∈ m q, nameOf c = nameOf d := by
  have h := routeB_untimed_safety_sound_keyInv hco hfr hG (bad := fun S => !alignedAll ps S)
    (fun a b hk => by rw [alignedAll_key_inv ps hk]) hempty hP hR
  exact (alignedAll_view_iff hps).mp (by simpa using h)

/-- **`QuiescentNameAligned(ps)`: a Route B `Proven` holds for the untimed, environment-free
executor**, deadline reaping included ([TIME-013], [VER-002]). A complete build whose
quiescence verdict for `!alignedAll ps` over the reapable set `reap` is `Proven`: in every
marking an untimed, injection-free executor run reaches and rests at (`ExecRests reap`), all
tokens in the places of `ps` carry one name. Needs `PosKeys` beyond the safety premises; every
member of `ps` must be coloured. -/
theorem routeB_untimed_quiescentNameAligned_sound (hco : co.Nodup)
    (hfr : ∀ T ∈ net, InFragment co T (role T)) (hpos : ∀ T ∈ net, PosKeys (role T))
    (hG : ∀ T ∈ net, GuardFree T.base) {ps : List PlaceId} (hps : ∀ p ∈ ps, p ∈ co)
    {reap : String → Bool} {maxClasses : ℕ} {cut : ℕ → Bool}
    {stopBad : NState co AMarking → Bool} {stopAt : Bool} {fuel : ℕ} {m0 : CMarking}
    (hempty : ∀ i : Fin co.length, m0 co[i.1] = [])
    (hP : Decide.verdict (routeB untimedBase net role conflict)
      (Decide.build (routeB untimedBase net role conflict) maxClasses cut stopBad stopAt fuel
        (initState co (alpha m0)))
      (.quiescence (fun S => !alignedAll ps S) reap) = .proven)
    {m : CMarking} (hR : Relation.ReflTransGen (NuStepC co nameOf net role conflict) m0 m)
    (hrest : ExecRests (co := co) (nameOf := nameOf) (net := net) reap m) :
    ∀ p ∈ ps, ∀ q ∈ ps, ∀ c ∈ m p, ∀ d ∈ m q, nameOf c = nameOf d := by
  have h := routeB_untimed_quiescence_sound_keyInv hco hfr hpos hG
    (bad := fun S => !alignedAll ps S) (fun a b hk => by rw [alignedAll_key_inv ps hk]) hempty
    hP hR hrest
  exact (alignedAll_view_iff hps).mp (by simpa using h)

end Aligned

end Libpetri.Novel.RouteB
