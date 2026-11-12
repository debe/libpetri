import Libpetri.Reference.Nu
import Libpetri.Reference.Link
import Libpetri.Novel.RouteA.Shipped
import Libpetri.Novel.RouteA.Reaping
import Libpetri.Reference.NuMint

set_option linter.missingDocs true

/-!
# Bridge B2: a reference ν firing, read by name, is a Route A ν step

Route A ([NU-050], [NU-053]) proves its verdicts sound against its own ν semantics,
`Novel.RouteA.NuStep` over classified flat rows `CRow` (`Novel/RouteA/Model.lean`): a coloured
place holds the correlation names of its tokens, and a row moves names by its class (untouched,
mint, join, consume). This module ties that semantics to the reference ν firing `RefNuFire`
(`Reference/Nu.lean`), so the Route A soundness theorems speak of the reference executor.

* **The name view.** `nview nameOf M` reads a queue marking of stamped tokens as a coloured
  marking: every token becomes the name `nameOf` gives its value, in queue order. Its counts are
  the queue counts (`alpha_nview`).
* **The row of a firing.** `RowOf C t d r`: the row `r` is the flat row of `t`
  (`Link.toTransition`) with the deposit `d` of the firing, the plan accepted it (`ClassOK`), and
  its class fits the match (`ClassFits`): a join row belongs to a matched transition whose keys
  are exactly the row's coloured inputs and whose relay targets include the row's coloured
  outputs; every other row belongs to a transition without a match. This is what `build_plan`'s
  classification does (`classifyRowG`: a source row with a match is a join or refused).
* **The contracts** (kind A; the runtimes do not check them). `ProjCoherent`: every key and relay
  projection gives the name `nameOf` gives, on the tokens of its place. `NuContract`: a mint
  writes one fresh name into its coloured outputs (ruling NUA-9 (a), [NU-010]); a coloured
  consumer writes the name of the token it consumed ([NU-051]). A join needs no action contract:
  the relay check of [NU-054] and coherence give it.
* **B2.** `refNuFire_routeA_step`: under those, the name view of a `RefNuFire` firing is a
  `NuStep` of its row.
* **The headline run forms** read the contracts and the rows off the SOURCE rows `build_plan`
  receives, not off the plan it returns: a run (`RefNuRunA`) is a sequence of reference firings
  each of whose actions keeps the contract of the class `build_plan`'s rule gives its source row
  (`srcClass`), the spec's "while the declared mints and the coloured consumers keep their
  contracts"; every firing of the run has a source row (`SrcCovers`). `buildPlan_src`: the shipped
  plan carries a classified row for every source row. `refNuRunA_routeA_reach`: every marking such
  a run reaches reads, by name, as a Route A reachable marking. The soundness corollaries
  `refNuRunA_routeA_safety_sound_plan` and `refNuRunA_routeA_quiescence_sound_plan` (no reapable
  transition) are what [NU-050]'s Route A block uses.
* **The strong forms** `refNuReach_routeA_reach`, `refNu_routeA_safety_sound_plan` and the
  quiescence forms `refNu_routeA_quiescence_sound_reaping` (a `NuRests` marking) and
  `refNu_routeA_quiescence_sound_plan` re-base Route A's verdicts on every `RefNuReach` run, under
  `FiringsHaveRows`: every firing the reference offers from a reachable marking has a plan row
  whose contract it keeps. The reference leaves the emitted values free, so a mint that can fire
  twice has a firing that writes a stale name, and that premise fails on every such net: they are
  kept as the stronger, nearly vacuous variant (the reaping form has no run-form counterpart yet).
* `nuContract_mint_iff`: the mint contract here is `MintContract` of `Reference/NuMint.lean`, the
  contract [NU-010] justifies (ruling D78 (a)).

Out of scope here: the timed executor and the firing pass (RefExec with the ν kernel), the
computation of the coloured set and of the rows from the net (taken as given, as
`Novel/RouteA/Plan.lean` takes them), and tokens without a name on a keyed place (coherence
excludes them).
-/

namespace Libpetri.Reference.NuLinkA

open Libpetri Libpetri.Spec Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.ForwardDeposit
open Libpetri.Reference.Link (toTransition toInSpec specAt_toTransition alphaFireC_toTransition
  enabledC_toTransition guardNone_toTransition)

open Libpetri.Novel.RouteA (Name Cls CRow ClassOK ClassShape NoTestArcs NameEffect NuStep ReachNu
  NuDead NuRest Unguarded Enc ReachE Premises agg DeadER DeadE)

variable {V : Type}

/-! ## The name view -/

/-- **The name view** of a queue marking: every token is read as the name `nameOf` gives its
value, in queue order. -/
def nview (nameOf : V → Name) (M : QMarking PlaceId (Stamped V)) : CMarking :=
  fun p => (M p).map fun x => nameOf x.val

@[simp] theorem nview_apply (nameOf : V → Name) (M : QMarking PlaceId (Stamped V)) (p : PlaceId) :
    nview nameOf M p = (M p).map fun x => nameOf x.val := rfl

/-- The name view keeps every count. -/
theorem alpha_nview (nameOf : V → Name) (M : QMarking PlaceId (Stamped V)) :
    alpha (nview nameOf M) = qCount M := by
  funext p; simp [alpha, qCount]

/-! ## Rows, contracts -/

/-- **Projection coherence** (kind A): on every place the match of `t` keys or relays to, the
projection gives every token of `M` the name `nameOf` gives its value. -/
def ProjCoherent (nameOf : V → Name) (t : NuTrans PlaceId (KeyFn V Name))
    (M : QMarking PlaceId (Stamped V)) : Prop :=
  ∀ ms, t.mspec = some ms → ∀ k ∈ ms.keys ++ ms.relays, ∀ x ∈ M k.1, k.2 x.val = some (nameOf x.val)

/-- **The class fits the match**: a join row belongs to a matched transition whose keys are
exactly the row's coloured inputs and whose relay targets include the row's coloured outputs;
every other row belongs to a transition without a match. -/
def ClassFits (t : NuTrans PlaceId (KeyFn V Name)) (r : CRow) : Prop :=
  match r.cls with
  | .join ins rel => ∃ ms, t.mspec = some ms ∧ (∀ p, p ∈ ms.keyPlaces ↔ p ∈ ins) ∧
      ∀ p ∈ rel, p ∈ ms.relayPlaces
  | _ => t.mspec = none

/-- **`r` is the row of a firing of `t` with deposit `d`**: the flat row of `t`, the deposit's
counts, a row the plan accepted, and a class that fits the match. -/
structure RowOf (C : List PlaceId) (t : NuTrans PlaceId (KeyFn V Name)) (d : List PlaceId)
    (r : CRow) : Prop where
  /-- The row's transition is the flat transition of `t`. -/
  trans : r.t = toTransition t.base.core
  /-- The row deposits what the firing deposits. -/
  dep : ∀ p, r.d.count p = d.count p
  /-- The plan accepted the row. -/
  ok : ClassOK C r
  /-- The row's class fits the match of `t`. -/
  fits : ClassFits t r

/-- **The action contract of a row's class** (kind A): a mint writes one name that no coloured
place holds into every coloured place it writes (NUA-9 (a)); a coloured consumer writes the name
of the token it took; untouched and join rows need nothing. -/
def NuContract (C : List PlaceId) (nameOf : V → Name) (cls : Cls)
    (M : QMarking PlaceId (Stamped V)) (δ : QDelivered PlaceId (Stamped V))
    (e : List (PlaceId × Stamped V)) : Prop :=
  match cls with
  | .mint _ => ∃ v, (∀ q ∈ C, ∀ x ∈ M q, nameOf x.val ≠ v) ∧
      ∀ p ∈ C, ∀ x ∈ qEmittedTo e p, nameOf x.val = v
  | .consume inp _ => ∀ x ∈ δ.inputs inp, ∀ p ∈ C, ∀ y ∈ qEmittedTo e p, nameOf y.val = nameOf x.val
  | _ => True

/-! ## Lemmas on the queue operations -/

section Lemmas

theorem pre_toTransition (t : NTransition PlaceId) (p : PlaceId) :
    pre (toTransition t) p = match nspecAt t p with
      | none => 0
      | some s => s.card.required := by
  unfold pre; rw [specAt_toTransition]; cases nspecAt t p <;> rfl

theorem consumeAllAt_toTransition (t : NTransition PlaceId) (p : PlaceId) :
    consumeAllAt (toTransition t) p = match nspecAt t p with
      | none => false
      | some s => s.card.consumesAll := by
  unfold consumeAllAt; rw [specAt_toTransition]; cases nspecAt t p <;> rfl

/-- Off a draining arc, a firing takes `pre` tokens from a place. -/
theorem nconsumed_eq_pre {t : NTransition PlaceId} {p : PlaceId}
    (h : consumeAllAt (toTransition t) p = false) (m : PlaceId → Nat) :
    nconsumed m t p = pre (toTransition t) p := by
  rw [pre_toTransition]
  rw [consumeAllAt_toTransition] at h
  unfold nconsumed
  cases hs : nspecAt t p with
  | none => rfl
  | some s => rw [hs] at h; simp [h]

/-- A count-enabled transition has at least `pre p` tokens on every place. -/
theorem pre_le_of_enabled {m : PlaceId → Nat} {t : NTransition PlaceId}
    (h : enabledNA m t = true) (p : PlaceId) : pre (toTransition t) p ≤ m p := by
  rw [pre_toTransition]
  cases hs : nspecAt t p with
  | none => exact Nat.zero_le _
  | some s =>
    obtain ⟨hmem, hp⟩ := nspecAt_place hs
    unfold enabledNA at h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact hp ▸ h.1.1 s hmem

/-- The queue a place keeps after the consume, off a reset and a draining arc: the queue without
its first `pre` tokens. -/
theorem qConsume_eq_drop {M : QMarking PlaceId (Stamped V)} {t : Trans PlaceId} {p : PlaceId}
    (hr : (toTransition t.core).resets.contains p = false)
    (hc : consumeAllAt (toTransition t.core) p = false) :
    qConsume M t p = (M p).drop (pre (toTransition t.core) p) := by
  have hr' : p ∉ t.core.resets := by
    simpa [toTransition] using hr
  simp [qConsume, hr', qPostInput, qTake, nconsumed_eq_pre hc]

theorem qCount_nview_qAppend (nameOf : V → Name) (M : QMarking PlaceId (Stamped V))
    (e : List (PlaceId × Stamped V)) (p : PlaceId) :
    nview nameOf (qAppend M e) p =
      nview nameOf M p ++ (qEmittedTo e p).map fun x => nameOf x.val := by
  simp [qAppend_apply]

/-- `keyAt` finds a key of the match on the place. -/
theorem keyAt_some {ms : MatchSpec PlaceId (KeyFn V Name)} {p : PlaceId} {f : KeyFn V Name}
    (h : keyAt ms p = some f) : (p, f) ∈ ms.keys := by
  unfold keyAt at h
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h
  have hmem := List.mem_of_find?_eq_some hk
  have hp : k.1 = p := by simpa using List.find?_some hk
  obtain ⟨k1, k2⟩ := k
  simp only at hp
  subst hp
  exact hmem

/-- A place without a key in the match is not a key place. -/
theorem keyAt_none {ms : MatchSpec PlaceId (KeyFn V Name)} {p : PlaceId}
    (h : keyAt ms p = none) : p ∉ ms.keyPlaces := by
  unfold keyAt at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  intro hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
  exact h k hk (by simp)

/-- A key place has a key. -/
theorem keyAt_of_mem {ms : MatchSpec PlaceId (KeyFn V Name)} {p : PlaceId}
    (h : p ∈ ms.keyPlaces) : ∃ f, keyAt ms p = some f := by
  cases hk : keyAt ms p with
  | none => exact absurd h (keyAt_none hk)
  | some f => exact ⟨f, rfl⟩

/-- Under coherence, dropping the first token of name `n` is erasing `n` from the name view. -/
theorem map_dropNamed_one (nameOf : V → Name) (f : KeyFn V Name) (n : Name) :
    ∀ l : List (Stamped V), (∀ x ∈ l, f x.val = some (nameOf x.val)) →
      (dropNamed f n 1 l).map (fun x => nameOf x.val) = (l.map fun x => nameOf x.val).erase n
  | [], _ => by simp [dropNamed]
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have ih := map_dropNamed_one nameOf f n xs fun y hy => h y (List.mem_cons_of_mem x hy)
    by_cases hn : nameOf x.val = n
    · have : f x.val = some n := hx.trans (by rw [hn])
      simp [dropNamed, this, hn]
    · have : ¬ f x.val = some n := fun h' => hn (Option.some.inj (hx.symm.trans h'))
      simp only [dropNamed, this, if_false, List.map_cons]
      rw [ih, List.erase_cons_tail (by simpa using hn)]

/-- Under coherence, the tokens of name `n` on a keyed place are those whose name is `n`. -/
theorem named_length (nameOf : V → Name) (f : KeyFn V Name) (n : Name) (l : List (Stamped V))
    (h : ∀ x ∈ l, f x.val = some (nameOf x.val)) :
    (named f n l).length = (l.map fun x => nameOf x.val).count n := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ih := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [named, List.filter_cons, hx, Option.some.injEq, List.map_cons,
      List.count_cons] at ih ⊢
    by_cases hn : nameOf x.val = n
    · simp [hn, ih]
    · simp [hn, ih]

end Lemmas

/-! ## B2: one firing -/

section Step

/-- The deposit counts of a row equal the emission's. -/
theorem emitted_length {C : List PlaceId} {t : NuTrans PlaceId (KeyFn V Name)}
    {e : List (PlaceId × Stamped V)} {r : CRow} (hr : RowOf C t (e.map Prod.fst) r) (p : PlaceId) :
    (qEmittedTo e p).length = r.d.count p := by
  rw [qEmittedTo_length, hr.dep]

/-- The counts of a row's step are the reference count successor. -/
theorem alphaFireC_row {C : List PlaceId} {t : NuTrans PlaceId (KeyFn V Name)}
    {e : List (PlaceId × Stamped V)} {r : CRow} (hr : RowOf C t (e.map Prod.fst) r)
    (m : CMarking) :
    alphaFireC m r.t (fun p => r.d.count p) =
      fireNC (alpha m) t.base.core (depProd (e.map Prod.fst)) := by
  have : (fun p => r.d.count p) = fun p => (e.map Prod.fst).count p := funext hr.dep
  rw [this, hr.trans, alphaFireC_toTransition]

/-- A list of length one or zero whose names are all `v` reads as `[v]` or `[]`. -/
theorem map_eq_of_length {l : List (Stamped V)} {g : Stamped V → Name} {v : Name} {b : Bool}
    (hl : l.length = if b then 1 else 0) (hv : ∀ x ∈ l, g x = v) :
    l.map g = if b then [v] else [] := by
  cases b with
  | false => simp at hl; simp [hl]
  | true =>
    simp only [if_true] at hl ⊢
    match l, hl with
    | [x], _ => simp [hv x List.mem_cons_self]

theorem emitted_map {C : List PlaceId} {t : NuTrans PlaceId (KeyFn V Name)}
    {e : List (PlaceId × Stamped V)} {r : CRow} (hr : RowOf C t (e.map Prod.fst) r)
    {nameOf : V → Name} {p : PlaceId} {outs : List PlaceId} {v : Name}
    (hcnt : r.d.count p = if p ∈ outs then 1 else 0)
    (hv : ∀ x ∈ qEmittedTo e p, nameOf x.val = v) :
    (qEmittedTo e p).map (fun x => nameOf x.val) = if p ∈ outs then [v] else [] := by
  have := map_eq_of_length (b := decide (p ∈ outs)) (g := fun x => nameOf x.val)
    (by rw [emitted_length hr, hcnt]; simp) hv
  simpa using this

/-- **B2, one firing.** Under projection coherence before and after the firing and the action
contract of the row's class, the name view of a reference ν firing is a Route A ν step of the
firing's row. -/
theorem refNuFire_routeA_step {C : List PlaceId} {nameOf : V → Name}
    {t : NuTrans PlaceId (KeyFn V Name)} {r : CRow}
    {M M' : QMarking PlaceId (Stamped V)} {c : Option Name} {δ : QDelivered PlaceId (Stamped V)}
    {e : List (PlaceId × Stamped V)}
    (hf : RefNuFire t M c δ e M') (hr : RowOf C t (e.map Prod.fst) r)
    (hcoh : ProjCoherent nameOf t M) (hcoh' : ProjCoherent nameOf t M')
    (hcon : NuContract C nameOf r.cls M δ e) :
    NuStep C r (nview nameOf M) (nview nameOf M') := by
  have hok := hr.ok
  have harcs := hok.arcs
  have hshape := hok.shape
  have hfits := hr.fits
  -- the facts every class shares, for a firing without a match
  have plain : t.mspec = none →
      enabledNA (qCount M) t.base.core = true ∧ δ = qDelivered M t.base ∧
        M' = qFire M t.base e := by
    intro hm
    obtain ⟨-, hen, -, hδ, hM'⟩ := (refNuFire_restrictsTo t hm M c δ e M').1 hf
    exact ⟨hen, hδ, hM'⟩
  have hq : ∀ p ∈ C, qConsume M t.base p = (M p).drop (pre r.t p) := fun p hp => by
    rw [hr.trans] at harcs ⊢
    exact qConsume_eq_drop (harcs p hp).1 (harcs p hp).2.1
  unfold ClassFits at hfits
  unfold ClassShape at hshape
  unfold NuContract at hcon
  rcases hcls : r.cls with _ | outs | ⟨ins, rel⟩ | ⟨inp, outs⟩ <;>
    rw [hcls] at hfits hshape hcon
  -- untouched
  · obtain ⟨hen, -, rfl⟩ := plain hfits
    refine ⟨?_, ?_, ?_⟩
    · rw [hr.trans, enabledC_toTransition, alpha_nview]; exact hen
    · rw [alpha_nview, alphaFireC_row hr, alpha_nview, qCount_qFire]
    · show NameEffect C r.cls _ _
      rw [hcls]
      intro p hp
      have h0 := hshape p hp
      have he : qEmittedTo e p = [] := by
        rw [← List.length_eq_zero_iff, emitted_length hr, h0.2]
      simp [qFire, qAppend_apply, he, hq p hp, h0.1]
  -- mint
  · obtain ⟨hen, -, rfl⟩ := plain hfits
    obtain ⟨-, -, h0⟩ := hshape
    obtain ⟨v, hfresh, hv⟩ := hcon
    refine ⟨?_, ?_, ?_⟩
    · rw [hr.trans, enabledC_toTransition, alpha_nview]; exact hen
    · rw [alpha_nview, alphaFireC_row hr, alpha_nview, qCount_qFire]
    · show NameEffect C r.cls _ _
      rw [hcls]
      refine ⟨v, fun q hq' hmem => ?_, fun p hp => ?_⟩
      · obtain ⟨x, hx, hxv⟩ := List.mem_map.1 hmem
        exact hfresh q hq' x hx hxv
      · have hem := emitted_map hr (h0 p hp).2 (hv p hp)
        simp only [nview_apply, qFire, qAppend_apply, List.map_append, hq p hp, (h0 p hp).1,
          List.drop_zero, hem]
        split <;> simp
  -- join
  · obtain ⟨ms, hms, hkeys, hrel⟩ := hfits
    obtain ⟨-, hinC, -, h0⟩ := hshape
    obtain ⟨n, rfl, hsel, hen, -, hrok, -, rfl⟩ := (refNuFire_matched hms M c δ e M').1 hf
    have hsel' := (refSelect_eq_some_iff.1 hsel).1
    -- coherence on each key, at `M`
    have hkc : ∀ p f, keyAt ms p = some f → ∀ x ∈ M p, f x.val = some (nameOf x.val) :=
      fun p f hk x hx => hcoh ms hms (p, f) (List.mem_append_left _ (keyAt_some hk)) x hx
    -- a key place holds a token of the chosen name
    have hname : ∀ p ∈ ins, n ∈ nview nameOf M p := by
      intro p hp
      obtain ⟨f, hfk⟩ := keyAt_of_mem ((hkeys p).2 hp)
      have hpk := keyAt_some hfk
      unfold eligible at hsel'
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsel'
      have h1 := (hsel'.2 _ (List.mem_map.2 ⟨(p, f), hpk, rfl⟩)).1
      unfold stamps at h1
      simp only [List.length_map] at h1
      obtain ⟨y, hy⟩ := List.exists_mem_of_length_pos h1
      obtain ⟨hy1, hy2⟩ := List.mem_filter.1 hy
      obtain ⟨x, hx, hxy⟩ := List.mem_filterMap.1 hy1
      obtain ⟨n', hn', rfl⟩ := Option.map_eq_some_iff.1 hxy
      have : n' = n := by simpa using hy2
      subst this
      rw [hkc p f hfk x hx] at hn'
      exact List.mem_map.2 ⟨x, hx, Option.some.inj hn'⟩
    -- the consume, place by place
    have hcons : ∀ p, nuConsume ms t M n p =
        match keyAt ms p with
        | some f => dropNamed f n 1 (M p)
        | none => qConsume M t.base p := by
      intro p
      cases hk : keyAt ms p with
      | none => simp [nuConsume, nuPost, hk, qConsume]
      | some f =>
        have hpin : p ∈ ins := (hkeys p).1 (List.mem_map.2 ⟨(p, f), keyAt_some hk, rfl⟩)
        have hpC := hinC p hpin
        rw [hr.trans] at harcs h0
        have hres : p ∉ t.base.core.resets := by
          simpa [toTransition] using (harcs p hpC).1
        have hpre : pre (toTransition t.base.core) p = 1 := by
          have := (h0 p hpC).1; rwa [if_pos hpin] at this
        have hca := (harcs p hpC).2.1
        rw [pre_toTransition] at hpre
        rw [consumeAllAt_toTransition] at hca
        cases hs : nspecAt t.base.core p with
        | none => rw [hs] at hpre; cases hpre
        | some s =>
          rw [hs] at hpre hca
          simp only at hpre hca
          simp [nuConsume, nuPost, hres, hk, corrTake, hs, consumptionCount, hca, hpre]
    refine ⟨?_, ?_, ?_⟩
    · rw [hr.trans, enabledC_toTransition, alpha_nview]; exact hen
    · rw [alpha_nview, alphaFireC_row hr, alpha_nview]
      funext p
      simp only [qCount, qAppend_apply, List.length_append, qEmittedTo_length, fireNC, depProd,
        hcons p]
      cases hk : keyAt ms p with
      | none =>
        simp only
        by_cases hres : p ∈ t.base.core.resets
        · simp [qConsume, hres]
        · simp [qConsume, hres, qPostInput, qTake]
      | some f =>
        simp only
        have hpin : p ∈ ins := (hkeys p).1 (List.mem_map.2 ⟨(p, f), keyAt_some hk, rfl⟩)
        have hpC := hinC p hpin
        have harcs' := harcs
        rw [hr.trans] at harcs' h0
        have hres : p ∉ t.base.core.resets := by
          simpa [toTransition] using (harcs' p hpC).1
        have hpre : pre (toTransition t.base.core) p = 1 := by
          have := (h0 p hpC).1; rwa [if_pos hpin] at this
        rw [if_neg hres, nconsumed_eq_pre (harcs' p hpC).2.1, hpre]
        have hm := congrArg List.length (map_dropNamed_one nameOf f n (M p) (hkc p f hk))
        simp only [List.length_map] at hm
        rw [hm, List.length_erase_of_mem (show n ∈ (M p).map (fun x => nameOf x.val) from hname p hpin), List.length_map]
    · show NameEffect C r.cls _ _
      rw [hcls]
      refine ⟨n, hname, fun p hp => ?_⟩
      rw [qCount_nview_qAppend]
      have hv : ∀ x ∈ qEmittedTo e p, p ∈ rel → nameOf x.val = n := by
        intro x hx hpr
        obtain ⟨⟨p', g⟩, hg, hp'⟩ := List.mem_map.1 (hrel p hpr)
        simp only at hp'
        subst hp'
        have h1 := hrok _ hg x hx
        have h2 := hcoh' ms hms _ (List.mem_append_right _ hg) x
          (by rw [qAppend_apply]; exact List.mem_append_right _ hx)
        exact (Option.some.inj (h2.symm.trans h1))
      have hem : (qEmittedTo e p).map (fun x => nameOf x.val) = if p ∈ rel then [n] else [] := by
        by_cases hpr : p ∈ rel
        · exact emitted_map hr (outs := rel) (h0 p hp).2 (fun x hx => hv x hx hpr)
        · have hz : qEmittedTo e p = [] := by
            rw [← List.length_eq_zero_iff, emitted_length hr, (h0 p hp).2, if_neg hpr]
          simp [hz, hpr]
      rw [hem]
      congr 1
      by_cases hpin : p ∈ ins
      · obtain ⟨f, hk⟩ := keyAt_of_mem ((hkeys p).2 hpin)
        rw [if_pos hpin, nview_apply, hcons p, hk]
        exact map_dropNamed_one nameOf f n (M p) (hkc p f hk)
      · have hk : keyAt ms p = none := by
          cases hk : keyAt ms p with
          | none => rfl
          | some f => exact absurd ((hkeys p).1 (List.mem_map.2 ⟨(p, f), keyAt_some hk, rfl⟩)) hpin
        rw [if_neg hpin, nview_apply, hcons p, hk]
        simp only
        rw [hq p hp, (h0 p hp).1, if_neg hpin, List.drop_zero]
        rfl
  -- consume
  · obtain ⟨hen, rfl, rfl⟩ := plain hfits
    obtain ⟨hinp, -, h0⟩ := hshape
    have hpre : pre r.t inp = 1 := by have := (h0 inp hinp).1; rwa [if_pos rfl] at this
    have hle := pre_le_of_enabled hen inp
    rw [← hr.trans, hpre] at hle
    obtain ⟨x0, rest, hM⟩ : ∃ x0 rest, M inp = x0 :: rest := by
      cases h : M inp with
      | nil => simp [qCount, h] at hle
      | cons x0 rest => exact ⟨x0, rest, rfl⟩
    have hδ : x0 ∈ (qDelivered M t.base).inputs inp := by
      have hc : consumeAllAt (toTransition t.base.core) inp = false := by
        rw [← hr.trans]; exact (harcs inp hinp).2.1
      simp [qDelivered, qInputs, qTake, nconsumed_eq_pre hc, ← hr.trans, hpre, hM]
    refine ⟨?_, ?_, ?_⟩
    · rw [hr.trans, enabledC_toTransition, alpha_nview]; exact hen
    · rw [alpha_nview, alphaFireC_row hr, alpha_nview, qCount_qFire]
    · show NameEffect C r.cls _ _
      rw [hcls]
      refine ⟨nameOf x0.val, by simp [hM], fun p hp => ?_⟩
      have hem := emitted_map hr (h0 p hp).2 (hcon x0 hδ p hp)
      simp only [nview_apply, qFire, qAppend_apply, List.map_append, hq p hp, hem]
      congr 1
      by_cases hpi : p = inp
      · subst hpi
        rw [if_pos rfl, hpre, hM]
        simp
      · rw [if_neg hpi, (h0 p hp).1, if_neg hpi, List.drop_zero]

end Step

/-! ## B2 on runs, and the soundness of Route A against the reference -/

section Net

/-- **Every reference firing has its row**: from every marking the reference reaches, each firing
of a transition of `X` has a row of `rows` (`RowOf`) whose class's action contract it meets.
This is the premise of the strong forms; it fails on every net with a mint that can fire twice
(a firing that writes a stale name is a reference firing), so the headline forms use
`RefNuRunA` and `SrcCovers` instead. -/
def FiringsHaveRows (C : List PlaceId) (nameOf : V → Name) (X : List (NuTrans PlaceId (KeyFn V Name)))
    (rows : List CRow) (M0 : QMarking PlaceId (Stamped V)) : Prop :=
  ∀ M, RefNuReach X M0 M → ∀ t ∈ X, ∀ c δ e M', RefNuFire t M c δ e M' →
    ∃ r ∈ rows, RowOf C t (e.map Prod.fst) r ∧ NuContract C nameOf r.cls M δ e

/-- **Coherence along the run**: at every marking the reference reaches, the key and relay
projections of every transition of `X` agree with `nameOf`. -/
def CoherentRun (nameOf : V → Name) (X : List (NuTrans PlaceId (KeyFn V Name)))
    (M0 : QMarking PlaceId (Stamped V)) : Prop :=
  ∀ M, RefNuReach X M0 M → ∀ t ∈ X, ProjCoherent nameOf t M

/-- **B2 on runs.** Every marking the reference ν executor reaches reads, by name, as a marking
Route A's ν semantics reaches over the plan's rows. -/
theorem refNuReach_routeA_reach {C : List PlaceId} {nameOf : V → Name}
    {X : List (NuTrans PlaceId (KeyFn V Name))} {rows : List CRow}
    {M0 : QMarking PlaceId (Stamped V)}
    (hcoh : CoherentRun nameOf X M0) (hfit : FiringsHaveRows C nameOf X rows M0) :
    ∀ M, RefNuReach X M0 M → ReachNu C rows (nview nameOf M0) (nview nameOf M) := by
  intro M h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail M1 M2 hreach hstep ih =>
    obtain ⟨t, ht, c, δ, e, hf⟩ := hstep
    obtain ⟨r, hrm, hr, hcon⟩ := hfit M1 hreach t ht c δ e M2 hf
    exact Relation.ReflTransGen.tail ih ⟨r, hrm, refNuFire_routeA_step hf hr
      (hcoh M1 hreach t ht) (hcoh M2 (hreach.tail ⟨t, ht, c, δ, e, hf⟩) t ht) hcon⟩

/-- **Route A safety is sound for the reference executor.** If the shipped `build_plan` returns a
plan for the counts of `M0`, a `Proven` of the shipped name-coloured query rules out `Bad` at the
counts of every marking the reference ν executor reaches, under coherence and the action
contracts. Nothing is assumed about the simplex. -/
theorem refNu_routeA_safety_sound_plan {n : Nat} {C : List PlaceId} {ext : Bool}
    {ans : Option (Nat × Weight)} {src : List Novel.RouteA.SrcRow} {k : Nat}
    {rows : List CRow} {invs : List Weight}
    {nameOf : V → Name} {X : List (NuTrans PlaceId (KeyFn V Name))}
    {M0 : QMarking PlaceId (Stamped V)}
    (h : Novel.RouteA.buildPlan n C ext (qCount M0) ans src = some (k, rows))
    (hnd : C.Nodup) (hC : ∀ p ∈ C, p < n) (hG : ∀ s ∈ src, GuardFreeConsumeAll s.t)
    (hinv : ∀ y ∈ invs, ∀ s ∈ src,
      ZeroOnNonlinear y s.t n ∧ Novel.LinearBound.dotIncD y s.flat n = 0)
    {Bad : AMarking → Prop}
    (hproven : ∀ e, ReachE (Enc.shipped ⟨C, k, n, rows, invs, qCount M0⟩) e → ¬ Bad (agg C k e))
    (hcoh : CoherentRun nameOf X M0) (hfit : FiringsHaveRows C nameOf X rows M0) :
    ∀ M, RefNuReach X M0 M → ¬ Bad (qCount M) := by
  intro M hM
  rw [← alpha_nview nameOf M0] at h hproven
  rw [← alpha_nview nameOf M]
  exact Novel.RouteA.routeA_safety_sound_plan h hnd hC hG hinv hproven _
    (refNuReach_routeA_reach hcoh hfit M hM)

/-- The rows the reference reads as reapable: a row of a reapable transition of `X` whose class
fits it. -/
def reapRow (X : List (NuTrans PlaceId (KeyFn V Name))) (r : CRow) : Prop :=
  ∃ t ∈ X, r.t = toTransition t.base.core ∧ ClassFits t r ∧ t.base.reapable = true

/-- Every row of the plan comes from a transition of `X` whose match its class fits. -/
def RowsFrom (X : List (NuTrans PlaceId (KeyFn V Name))) (rows : List CRow) : Prop :=
  ∀ r ∈ rows, ∃ t ∈ X, r.t = toTransition t.base.core ∧ ClassFits t r

/-- A row is unguarded when it is the flat row of a reference transition. -/
theorem unguarded_of_rowsFrom {X : List (NuTrans PlaceId (KeyFn V Name))} {rows : List CRow}
    (h : RowsFrom X rows) : ∀ r ∈ rows, Unguarded r.t := by
  intro r hr
  obtain ⟨t, -, ht, -⟩ := h r hr
  rw [ht]
  exact guardNone_toTransition t.base.core

/-- A row's stamps hold a token's name when the projection names it. -/
theorem stamps_pos {l : List (Stamped V)} {f : KeyFn V Name} {v : Name}
    {x : Stamped V} (hx : x ∈ l) (hfx : f x.val = some v) :
    1 ≤ (stamps (l.filterMap fun x => (f x.val).map fun n => (n, x.stamp)) v).length := by
  unfold stamps
  rw [List.length_map]
  refine List.length_pos_of_mem (a := (v, x.stamp)) (List.mem_filter.2 ⟨?_, by simp⟩)
  exact List.mem_filterMap.2 ⟨x, hx, by simp [hfx]⟩

/-- **Enablement transfers back**: a row Route A ν-enables at the name view of `M` belongs to a
transition the reference ν-enables at `M`. -/
theorem nuEnabled_of_row {C : List PlaceId} {nameOf : V → Name}
    {t : NuTrans PlaceId (KeyFn V Name)} {r : CRow} {M : QMarking PlaceId (Stamped V)}
    (ht : r.t = toTransition t.base.core) (hok : ClassOK C r) (hfits : ClassFits t r)
    (hcoh : ProjCoherent nameOf t M)
    (hen : Novel.RouteA.NuEnabled (nview nameOf M) r) : Spec.NuEnabled t M := by
  obtain ⟨hc, hj⟩ := hen
  have hcount : Enabled t.base (qCount M) := by
    show enabledNA (qCount M) t.base.core = true
    rw [ht, enabledC_toTransition, alpha_nview] at hc
    exact hc
  refine ⟨hcount, fun ms hms => ?_⟩
  have hshape := hok.shape
  unfold ClassFits at hfits
  unfold ClassShape at hshape
  rcases hcls : r.cls with _ | outs | ⟨ins, rel⟩ | ⟨inp, outs⟩ <;>
    rw [hcls] at hfits hshape hj
  · rw [hfits] at hms; cases hms
  · rw [hfits] at hms; cases hms
  · obtain ⟨ms', hms', hkeys, -⟩ := hfits
    have hmseq : ms = ms' := by rw [hms'] at hms; exact (Option.some.inj hms).symm
    subst hmseq
    obtain ⟨hne, hinC, -, h0⟩ := hshape
    obtain ⟨v, hv⟩ := hj
    refine ⟨v, ?_⟩
    unfold eligible matchIn
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
      decide_eq_true_eq, List.mem_map]
    refine ⟨?_, ?_⟩
    · intro hnil
      rw [List.map_eq_nil_iff] at hnil
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil ins hne
      obtain ⟨k, hk, -⟩ := List.mem_map.1 ((hkeys p).2 hp)
      rw [hnil] at hk; exact List.not_mem_nil hk
    · rintro _ ⟨k, hk, rfl⟩
      have hpin : k.1 ∈ ins := (hkeys k.1).1 (List.mem_map.2 ⟨k, hk, rfl⟩)
      obtain ⟨x, hx, hxv⟩ := List.mem_map.1 (hv k.1 hpin)
      have hfx : k.2 x.val = some v :=
        (hcoh ms hms' k (List.mem_append_left _ hk) x hx).trans (by rw [hxv])
      have h1 := stamps_pos hx hfx
      refine ⟨h1, le_trans ?_ h1⟩
      unfold reqAt
      have hpre := (h0 k.1 (hinC k.1 hpin)).1
      rw [if_pos hpin, ht, pre_toTransition] at hpre
      cases hs : nspecAt t.base.core k.1 with
      | none => exact le_refl 1
      | some s => rw [hs] at hpre; exact le_of_eq hpre
  · rw [hfits] at hms; cases hms

/-- **A reference rest is a Route A rest**: where every ν-enabled transition of `X` is reapable,
every row of the plan is reapable (`reapRow`) or not ν-enabled at the name view. -/
theorem nuRest_of_nuRests {C : List PlaceId} {nameOf : V → Name}
    {X : List (NuTrans PlaceId (KeyFn V Name))} {rows : List CRow}
    {M : QMarking PlaceId (Stamped V)} (hsrc : RowsFrom X rows)
    (hok : ∀ r ∈ rows, ClassOK C r) (hcoh : ∀ t ∈ X, ProjCoherent nameOf t M)
    (hrest : NuRests X M) : NuRest (reapRow X) rows (nview nameOf M) := by
  intro r hr
  obtain ⟨t, ht, htr, hfits⟩ := hsrc r hr
  by_cases hen : Novel.RouteA.NuEnabled (nview nameOf M) r
  · exact Or.inl ⟨t, ht, htr, hfits,
      hrest t ht (nuEnabled_of_row htr (hok r hr) hfits (hcoh t ht) hen)⟩
  · exact Or.inr hen

/-- **Route A quiescence under reaping is sound for the reference executor.** A `Proven` of the
reaping-aware query (rows of reapable transitions skipped) rules out `Q` at the counts of every
marking the reference ν executor reaches and rests at. -/
theorem refNu_routeA_quiescence_sound_reaping {E : Enc} {nameOf : V → Name}
    {X : List (NuTrans PlaceId (KeyFn V Name))} {M0 : QMarking PlaceId (Stamped V)}
    (P : Premises E (nview nameOf M0)) (hd : ∀ r ∈ E.rows, InputsDistinctPlaces r.t)
    (hsrc : RowsFrom X E.rows) {Q : AMarking → Prop}
    (hproven : ∀ e, ReachE E e → ¬ (DeadER E (reapRow X) e ∧ Q (agg E.C E.k e)))
    (hcoh : CoherentRun nameOf X M0) (hfit : FiringsHaveRows E.C nameOf X E.rows M0) :
    ∀ M, RefNuReach X M0 M → ¬ (NuRests X M ∧ Q (qCount M)) := by
  intro M hM ⟨hrest, hq⟩
  refine Novel.RouteA.routeA_quiescence_sound_reaping P (unguarded_of_rowsFrom hsrc) hd hproven
    _ (refNuReach_routeA_reach hcoh hfit M hM) ⟨?_, by rwa [alpha_nview]⟩
  exact nuRest_of_nuRests hsrc P.classOK (hcoh M hM) hrest

/-- **Route A quiescence from the shipped `build_plan` is sound for the reference executor**, on
a net with no reapable transition: a `Proven` of the strict query rules out `Q` at the counts of
every marking the reference reaches and rests at. -/
theorem refNu_routeA_quiescence_sound_plan {n : Nat} {C : List PlaceId} {ext : Bool}
    {ans : Option (Nat × Weight)} {src : List Novel.RouteA.SrcRow} {k : Nat}
    {rows : List CRow} {invs : List Weight}
    {nameOf : V → Name} {X : List (NuTrans PlaceId (KeyFn V Name))}
    {M0 : QMarking PlaceId (Stamped V)}
    (h : Novel.RouteA.buildPlan n C ext (qCount M0) ans src = some (k, rows))
    (hnd : C.Nodup) (hC : ∀ p ∈ C, p < n) (hG : ∀ s ∈ src, GuardFreeConsumeAll s.t)
    (hinv : ∀ y ∈ invs, ∀ s ∈ src,
      ZeroOnNonlinear y s.t n ∧ Novel.LinearBound.dotIncD y s.flat n = 0)
    (hd : ∀ r ∈ rows, InputsDistinctPlaces r.t) (hsrc : RowsFrom X rows)
    (hok : ∀ r ∈ rows, ClassOK C r) (hnr : ∀ t ∈ X, t.base.reapable = false)
    {Q : AMarking → Prop}
    (hproven : ∀ e, ReachE (Enc.shipped ⟨C, k, n, rows, invs, qCount M0⟩) e →
      ¬ (DeadE (Enc.shipped ⟨C, k, n, rows, invs, qCount M0⟩) e ∧ Q (agg C k e)))
    (hcoh : CoherentRun nameOf X M0) (hfit : FiringsHaveRows C nameOf X rows M0) :
    ∀ M, RefNuReach X M0 M → ¬ (NuRests X M ∧ Q (qCount M)) := by
  intro M hM ⟨hrest, hq⟩
  rw [← alpha_nview nameOf M0] at h hproven
  have hdead : NuDead rows (nview nameOf M) := by
    intro r hr hen
    obtain ⟨t, ht, htr, hfits⟩ := hsrc r hr
    have := hrest t ht (nuEnabled_of_row htr (hok r hr) hfits (hcoh M hM t ht) hen)
    rw [hnr t ht] at this; cases this
  exact Novel.RouteA.routeA_quiescence_sound_plan h hnd hC hG hinv (unguarded_of_rowsFrom hsrc) hd
    hproven _ (refNuReach_routeA_reach hcoh hfit M hM) ⟨hdead, by rwa [alpha_nview]⟩

end Net

/-! ## B2 on contract-keeping runs, read off the source rows (the headline form)

The strong forms above ask, through `FiringsHaveRows`, the action contract of every firing the
reference offers from a reachable marking. The reference leaves the emitted values free, so a
mint that can fire twice has a firing that writes a stale name, and the premise fails on every
such net. They also read the contracts and the rows off the plan the planner returned, so a
planner that leaves a row out removes that row's firings from its own premises.

The headline forms below read both off the SOURCE rows `src` that `build_plan` receives, which the
planner does not choose: a run (`RefNuRunA`) is a sequence of reference firings each of whose
actions keeps the contract of the class `build_plan`'s rule gives its source row (`srcClass`),
and the rows premise (`SrcCovers`) asks every firing of the run for a source row. That the plan
carries a classified row for every source row is then a property of the shipped `build_plan`
(`buildPlan_src`), not a premise. -/

section SrcRuns

/-- The class `build_plan`'s classification rule gives a source row, with the shipped gates
(declared mints, timeout writes): `classifyRowG` under `shippedGate`. `none`: the row is refused
(and so is the whole plan). -/
def srcClass (C : List PlaceId) (ext : Bool) (s : Novel.RouteA.SrcRow) : Option Cls :=
  Novel.RouteA.classifyRowG C ext (Novel.RouteA.shippedGate C s).1
    (Novel.RouteA.shippedGate C s).2 s.ms s.t s.d

/-- **`s` is a source row of a firing of `t` with deposit `d`**: the flat row of `t`, the
deposit's counts, and a class (when the rule gives one) that fits the match of `t`. -/
structure SrcRowOf (C : List PlaceId) (ext : Bool) (t : NuTrans PlaceId (KeyFn V Name))
    (d : List PlaceId) (s : Novel.RouteA.SrcRow) : Prop where
  /-- The source row's transition is the flat transition of `t`. -/
  trans : s.t = toTransition t.base.core
  /-- The source row deposits what the firing deposits. -/
  dep : ∀ p, s.d.count p = d.count p
  /-- The class the rule gives the source row fits the match of `t`. -/
  fits : ∀ cls, srcClass C ext s = some cls → ClassFits t ⟨s.t, s.d, cls⟩

/-- **A contract-keeping reference run for Route A.** From `M0`, a sequence of reference ν
firings of transitions of `X`, each of whose actions keeps the contract of the class of every
source row of the firing (`NuContract`: a mint writes one name no coloured place holds into every
coloured place it writes; a coloured consumer writes the name it took). A source row the rule
refuses carries no contract. -/
def RefNuRunA (C : List PlaceId) (ext : Bool) (nameOf : V → Name)
    (X : List (NuTrans PlaceId (KeyFn V Name))) (src : List Novel.RouteA.SrcRow)
    (M0 : QMarking PlaceId (Stamped V)) : QMarking PlaceId (Stamped V) → Prop :=
  Relation.ReflTransGen (fun M M' => ∃ t ∈ X, ∃ c δ e, RefNuFire t M c δ e M' ∧
    ∀ s ∈ src, SrcRowOf C ext t (e.map Prod.fst) s →
      ∀ cls, srcClass C ext s = some cls → NuContract C nameOf cls M δ e) M0

/-- **Every firing of the run has a source row.** -/
def SrcCovers (C : List PlaceId) (ext : Bool) (nameOf : V → Name)
    (X : List (NuTrans PlaceId (KeyFn V Name))) (src : List Novel.RouteA.SrcRow)
    (M0 : QMarking PlaceId (Stamped V)) : Prop :=
  ∀ M, RefNuRunA C ext nameOf X src M0 M → ∀ t ∈ X, ∀ c δ e M', RefNuFire t M c δ e M' →
    ∃ s ∈ src, SrcRowOf C ext t (e.map Prod.fst) s

/-- Every source row comes from a transition of `X` whose match its class fits. -/
def SrcFrom (C : List PlaceId) (ext : Bool) (X : List (NuTrans PlaceId (KeyFn V Name)))
    (src : List Novel.RouteA.SrcRow) : Prop :=
  ∀ s ∈ src, ∃ t ∈ X, s.t = toTransition t.base.core ∧
    ∀ cls, srcClass C ext s = some cls → ClassFits t ⟨s.t, s.d, cls⟩

/-- A contract-keeping run is a reference ν run. -/
theorem RefNuRunA.refNuReach {C : List PlaceId} {ext : Bool} {nameOf : V → Name}
    {X : List (NuTrans PlaceId (KeyFn V Name))} {src : List Novel.RouteA.SrcRow}
    {M0 M : QMarking PlaceId (Stamped V)} (h : RefNuRunA C ext nameOf X src M0 M) :
    RefNuReach X M0 M := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨t, ht, c, δ, e, hf, -⟩ := hs
    exact ih.tail ⟨t, ht, c, δ, e, hf⟩

/-- Step 2 of `build_plan` keeps one classified row per source row, in both directions, each
with the class the rule gives. -/
theorem classifyAllG_src {C : List PlaceId} {ext : Bool} {g : Novel.RouteA.Gate} :
    ∀ {src : List Novel.RouteA.SrcRow} {rows : List CRow},
      Novel.RouteA.classifyAllG C ext g src = some rows →
      (∀ s ∈ src, ∃ r ∈ rows, r.t = s.t ∧ r.d = s.d ∧
        Novel.RouteA.classifyRowG C ext (g s).1 (g s).2 s.ms s.t s.d = some r.cls) ∧
      (∀ r ∈ rows, ∃ s ∈ src, r.t = s.t ∧ r.d = s.d ∧
        Novel.RouteA.classifyRowG C ext (g s).1 (g s).2 s.ms s.t s.d = some r.cls)
  | [], rows, h => by
    simp only [Novel.RouteA.classifyAllG, Option.some.injEq] at h
    subst h
    exact ⟨fun s hs => absurd hs List.not_mem_nil, fun r hr => absurd hr List.not_mem_nil⟩
  | s :: ss, rows, h => by
    simp only [Novel.RouteA.classifyAllG] at h
    split at h
    · rename_i cls rs hcls hrs
      cases h
      obtain ⟨h1, h2⟩ := classifyAllG_src hrs
      refine ⟨fun s' hs' => ?_, fun r hr => ?_⟩
      · rcases List.mem_cons.1 hs' with rfl | hs'
        · exact ⟨_, List.mem_cons_self, rfl, rfl, hcls⟩
        · obtain ⟨r, hr, hr'⟩ := h1 s' hs'
          exact ⟨r, List.mem_cons_of_mem _ hr, hr'⟩
      · rcases List.mem_cons.1 hr with rfl | hr
        · exact ⟨s, List.mem_cons_self, rfl, rfl, hcls⟩
        · obtain ⟨s', hs', hs''⟩ := h2 r hr
          exact ⟨s', List.mem_cons_of_mem _ hs', hs''⟩
    · exact absurd h (by simp)

/-- A plan `buildPlanG` returns is the classification of every source row. -/
theorem buildPlanG_classify {n : Nat} {C : List PlaceId} {ext : Bool} {g : Novel.RouteA.Gate}
    {a0 : AMarking} {slot : Option Nat} {src : List Novel.RouteA.SrcRow} {k : Nat}
    {rows : List CRow} (h : Novel.RouteA.buildPlanG n C ext g a0 slot src = some (k, rows)) :
    Novel.RouteA.classifyAllG C ext g src = some rows := by
  unfold Novel.RouteA.buildPlanG at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  rename_i rows' hrows'
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [hrows', h.2]

/-- **The shipped `build_plan` carries a classified row for every source row**, with the class
`srcClass` gives, and every row of its plan is one of those. -/
theorem buildPlan_src {n : Nat} {C : List PlaceId} {ext : Bool} {a0 : AMarking}
    {ans : Option (Nat × Weight)} {src : List Novel.RouteA.SrcRow} {k : Nat} {rows : List CRow}
    (h : Novel.RouteA.buildPlan n C ext a0 ans src = some (k, rows)) :
    (∀ s ∈ src, ∃ r ∈ rows, r.t = s.t ∧ r.d = s.d ∧ srcClass C ext s = some r.cls) ∧
      (∀ r ∈ rows, ∃ s ∈ src, r.t = s.t ∧ r.d = s.d ∧ srcClass C ext s = some r.cls) :=
  classifyAllG_src (buildPlanG_classify h)

/-- Rows that carry the class of a source row of `X` come from `X`. -/
theorem rowsFrom_of_src {C : List PlaceId} {ext : Bool}
    {X : List (NuTrans PlaceId (KeyFn V Name))} {src : List Novel.RouteA.SrcRow}
    {rows : List CRow} (hsrc : SrcFrom C ext X src)
    (hr : ∀ r ∈ rows, ∃ s ∈ src, r.t = s.t ∧ r.d = s.d ∧ srcClass C ext s = some r.cls) :
    RowsFrom X rows := by
  intro r hrm
  obtain ⟨s, hs, ht, -, hcls⟩ := hr r hrm
  obtain ⟨t, htX, hst, hfit⟩ := hsrc s hs
  exact ⟨t, htX, ht.trans hst, hfit r.cls hcls⟩

/-- **B2 on contract-keeping runs.** Given a plan that carries a classified row for every source
row, with the class the rule gives it, and rows the plan accepted, every marking a
contract-keeping reference run reaches reads, by name, as a marking Route A's ν semantics
reaches over the plan's rows, when every firing of the run has a source row and the projections
agree with `nameOf` along the run. -/
theorem refNuRunA_routeA_reach {C : List PlaceId} {ext : Bool} {nameOf : V → Name}
    {X : List (NuTrans PlaceId (KeyFn V Name))} {src : List Novel.RouteA.SrcRow}
    {rows : List CRow} {M0 : QMarking PlaceId (Stamped V)}
    (hplan : ∀ s ∈ src, ∃ r ∈ rows, r.t = s.t ∧ r.d = s.d ∧ srcClass C ext s = some r.cls)
    (hok : ∀ r ∈ rows, ClassOK C r)
    (hcov : SrcCovers C ext nameOf X src M0)
    (hcoh : ∀ M, RefNuRunA C ext nameOf X src M0 M → ∀ t ∈ X, ProjCoherent nameOf t M)
    {M : QMarking PlaceId (Stamped V)} (h : RefNuRunA C ext nameOf X src M0 M) :
    ReachNu C rows (nview nameOf M0) (nview nameOf M) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail M1 M2 hr hs ih =>
    obtain ⟨t, ht, c, δ, e, hf, hK⟩ := hs
    have hr2 : RefNuRunA C ext nameOf X src M0 M2 := hr.tail ⟨t, ht, c, δ, e, hf, hK⟩
    obtain ⟨s, hsm, hs⟩ := hcov M1 hr t ht c δ e M2 hf
    obtain ⟨r, hrm, hrt, hrd, hcls⟩ := hplan s hsm
    have hrow : RowOf C t (e.map Prod.fst) r :=
      ⟨hrt.trans hs.trans, fun p => by rw [hrd]; exact hs.dep p, hok r hrm,
        hs.fits r.cls hcls⟩
    exact ih.tail ⟨r, hrm, refNuFire_routeA_step hf hrow (hcoh M1 hr t ht)
      (hcoh M2 hr2 t ht) (hK s hsm hs r.cls hcls)⟩

/-- **Route A safety from the shipped `build_plan` is sound for the reference executor**, on
contract-keeping runs read off the source rows: a `Proven` of the shipped name-coloured query
rules out `Bad` at the counts of every marking such a run reaches. Nothing is assumed about the
simplex, nor about the plan beyond what `build_plan` returned. -/
theorem refNuRunA_routeA_safety_sound_plan {n : Nat} {C : List PlaceId} {ext : Bool}
    {ans : Option (Nat × Weight)} {src : List Novel.RouteA.SrcRow} {k : Nat}
    {rows : List CRow} {invs : List Weight}
    {nameOf : V → Name} {X : List (NuTrans PlaceId (KeyFn V Name))}
    {M0 : QMarking PlaceId (Stamped V)}
    (h : Novel.RouteA.buildPlan n C ext (qCount M0) ans src = some (k, rows))
    (hnd : C.Nodup) (hC : ∀ p ∈ C, p < n) (hG : ∀ s ∈ src, GuardFreeConsumeAll s.t)
    (hinv : ∀ y ∈ invs, ∀ s ∈ src,
      ZeroOnNonlinear y s.t n ∧ Novel.LinearBound.dotIncD y s.flat n = 0)
    (hcov : SrcCovers C ext nameOf X src M0)
    (hcoh : ∀ M, RefNuRunA C ext nameOf X src M0 M → ∀ t ∈ X, ProjCoherent nameOf t M)
    {Bad : AMarking → Prop}
    (hproven : ∀ e, ReachE (Enc.shipped ⟨C, k, n, rows, invs, qCount M0⟩) e → ¬ Bad (agg C k e)) :
    ∀ M, RefNuRunA C ext nameOf X src M0 M → ¬ Bad (qCount M) := by
  intro M hM
  have hplan := (buildPlan_src h).1
  rw [← alpha_nview nameOf M0] at h hproven
  have hok := (Novel.RouteA.buildPlan_premisesS h hnd hC hG hinv).classOK
  rw [← alpha_nview nameOf M]
  exact Novel.RouteA.routeA_safety_sound_plan h hnd hC hG hinv hproven _
    (refNuRunA_routeA_reach hplan hok hcov hcoh hM)

/-- **Route A quiescence from the shipped `build_plan` is sound for the reference executor**, on
contract-keeping runs read off the source rows and on a net with no reapable transition: a
`Proven` of the strict query rules out `Q` at the counts of every marking such a run reaches and
rests at. -/
theorem refNuRunA_routeA_quiescence_sound_plan {n : Nat} {C : List PlaceId} {ext : Bool}
    {ans : Option (Nat × Weight)} {src : List Novel.RouteA.SrcRow} {k : Nat}
    {rows : List CRow} {invs : List Weight}
    {nameOf : V → Name} {X : List (NuTrans PlaceId (KeyFn V Name))}
    {M0 : QMarking PlaceId (Stamped V)}
    (h : Novel.RouteA.buildPlan n C ext (qCount M0) ans src = some (k, rows))
    (hnd : C.Nodup) (hC : ∀ p ∈ C, p < n) (hG : ∀ s ∈ src, GuardFreeConsumeAll s.t)
    (hinv : ∀ y ∈ invs, ∀ s ∈ src,
      ZeroOnNonlinear y s.t n ∧ Novel.LinearBound.dotIncD y s.flat n = 0)
    (hcov : SrcCovers C ext nameOf X src M0)
    (hcoh : ∀ M, RefNuRunA C ext nameOf X src M0 M → ∀ t ∈ X, ProjCoherent nameOf t M)
    (hd : ∀ s ∈ src, InputsDistinctPlaces s.t) (hsrc : SrcFrom C ext X src)
    (hnr : ∀ t ∈ X, t.base.reapable = false)
    {Q : AMarking → Prop}
    (hproven : ∀ e, ReachE (Enc.shipped ⟨C, k, n, rows, invs, qCount M0⟩) e →
      ¬ (DeadE (Enc.shipped ⟨C, k, n, rows, invs, qCount M0⟩) e ∧ Q (agg C k e))) :
    ∀ M, RefNuRunA C ext nameOf X src M0 M → NuRests X M → ¬ Q (qCount M) := by
  intro M hM hrest hq
  obtain ⟨hplan, hback⟩ := buildPlan_src h
  have hfrom : RowsFrom X rows := rowsFrom_of_src hsrc hback
  have hdr : ∀ r ∈ rows, InputsDistinctPlaces r.t := by
    intro r hr
    obtain ⟨s, hs, ht, -⟩ := hback r hr
    rw [ht]
    exact hd s hs
  rw [← alpha_nview nameOf M0] at h hproven
  have hok := (Novel.RouteA.buildPlan_premisesS h hnd hC hG hinv).classOK
  have hdead : NuDead rows (nview nameOf M) := by
    intro r hr hen
    obtain ⟨t, ht, htr, hfits⟩ := hfrom r hr
    have := hrest t ht (nuEnabled_of_row htr (hok r hr) hfits (hcoh M hM t ht) hen)
    rw [hnr t ht] at this; cases this
  exact Novel.RouteA.routeA_quiescence_sound_plan h hnd hC hG hinv
    (unguarded_of_rowsFrom hfrom) hdr hproven _
    (refNuRunA_routeA_reach hplan hok hcov hcoh hM) ⟨hdead, by rwa [alpha_nview]⟩

/-- **The mint contract of [NU-010] is Route A's mint contract on the reference.** On a queue
marking `M` and an emission `e`, `NuContract` at a mint class is `MintContract` (ruling D78 (a),
`Reference/NuMint.lean`) with `holds p v`: the coloured place `p` holds a token named `v`, and
`wr p`: the names `e` writes into the coloured place `p`. -/
theorem nuContract_mint_iff (C : List PlaceId) (nameOf : V → Name) (outs : List PlaceId)
    (M : QMarking PlaceId (Stamped V)) (δ : QDelivered PlaceId (Stamped V))
    (e : List (PlaceId × Stamped V)) :
    NuContract C nameOf (.mint outs) M δ e ↔
      MintContract (fun p v => p ∈ C ∧ ∃ x ∈ M p, nameOf x.val = v)
        (fun p => if p ∈ C then (qEmittedTo e p).map (fun x => nameOf x.val) else []) := by
  constructor
  · rintro ⟨f, hf, hw⟩
    refine ⟨f, fun c ⟨hc, x, hx, hxf⟩ => hf c hc x hx hxf, fun c w hw' => ?_⟩
    simp only at hw'
    by_cases hc : c ∈ C
    · rw [if_pos hc] at hw'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hw'
      exact hw c hc y hy
    · rw [if_neg hc] at hw'
      exact absurd hw' List.not_mem_nil
  · rintro ⟨f, hf, hw⟩
    refine ⟨f, fun q hq x hx hxf => hf q ⟨hq, x, hx, hxf⟩, fun p hp x hx => ?_⟩
    apply hw p
    show nameOf x.val ∈ (if p ∈ C then _ else [])
    rw [if_pos hp]
    exact List.mem_map.2 ⟨x, hx, rfl⟩

end SrcRuns

/-! ## A worked example, and a name-blind join the bridge rejects -/

section Example

/-- The join of the worked example: one token from place 0 and one from place 1, joined by the
token's value as its name, the joined name relayed to place 2. -/
def exJoin : NuTrans PlaceId (KeyFn Nat Name) :=
  { base := { core := { name := "join", inputs := [⟨0, .one⟩, ⟨1, .one⟩], inhibitors := [],
                        reads := [], resets := [] },
              out := some (.place 2) },
    mspec := some { keys := [(0, some), (1, some)], relays := [(2, some)] } }

/-- The match of `exJoin`. -/
def exMs : MatchSpec PlaceId (KeyFn Nat Name) :=
  { keys := [(0, some), (1, some)], relays := [(2, some)] }

/-- Place 0 holds names 5 then 7, place 1 holds 7 then 5; the stamps make 5 the older name. -/
def exM : QMarking PlaceId (Stamped Nat) := fun p =>
  if p = 0 then [⟨5, 0⟩, ⟨7, 1⟩] else if p = 1 then [⟨7, 2⟩, ⟨5, 3⟩] else []

/-- The action relays name 5 to place 2. -/
def exE : List (PlaceId × Stamped Nat) := [(2, ⟨5, 4⟩)]

/-- What the reference leaves: the 5 of each key taken, the 5 relayed. -/
def exM' : QMarking PlaceId (Stamped Nat) := qAppend (nuConsume exMs exJoin exM 5) exE

/-- The row `build_plan` gives the join: coloured places 0, 1 and 2, a join of 0 and 1 relaying
to 2. -/
def exRow : CRow := ⟨toTransition exJoin.base.core, [2], .join [0, 1] [2]⟩

/-- The reference fires the join on name 5, the older of the two names both keys hold. -/
theorem ex_fire : RefNuFire exJoin exM (some 5) (nuDelivered exMs exJoin exM 5) exE exM' := by
  refine (refNuFire_matched (ms := exMs) rfl _ _ _ _ _).2
    ⟨5, rfl, ?_, ?_, ⟨.action 0, rfl⟩, ?_, rfl, rfl⟩
  · decide
  · decide
  · intro r hr x hx
    simp [exMs] at hr
    subst hr
    simp [exE, qEmittedTo] at hx
    subst hx; rfl

/-- The example's row is the row of the firing. -/
theorem ex_row : RowOf [0, 1, 2] exJoin (exE.map Prod.fst) exRow := by
  refine ⟨rfl, fun _ => rfl, ⟨?_, ?_⟩, ?_⟩
  · unfold NoTestArcs; decide
  · show _ ∧ _ ∧ _ ∧ _
    decide
  · exact ⟨exMs, rfl, fun p => by simp [MatchSpec.keyPlaces, exMs], by
      simp [MatchSpec.relayPlaces, exMs]⟩

/-- The example's keys name every token by its value. -/
theorem ex_coh (M : QMarking PlaceId (Stamped Nat)) : ProjCoherent id exJoin M := by
  intro ms hms k hk x hx
  simp [exJoin] at hms
  subst hms
  simp at hk
  rcases hk with rfl | rfl | rfl <;> rfl

/-- **The hypotheses of B2 hold together.** Places 0 and 1 hold names 5 then 7 and 7 then 5; the
reference joins on 5 and relays it to place 2. Read by name, the firing is a Route A join step of
its row: 5 leaves both keys, 7 stays, 5 arrives on place 2. -/
theorem ex_routeA_step : NuStep [0, 1, 2] exRow (nview id exM) (nview id exM') :=
  refNuFire_routeA_step ex_fire ex_row (ex_coh _) (ex_coh _) trivial

/-- The name view after the example's firing: 7 on each key, 5 relayed. -/
theorem ex_after : nview id exM' 0 = [7] ∧ nview id exM' 1 = [7] ∧ nview id exM' 2 = [5] := by
  decide

/-- **A name-blind join is no Route A step.** Firing the same join first in first out takes 5 from
place 0 and 7 from place 1, leaving 7 on place 0 and 5 on place 1. No single name left both keys,
so Route A's join does not describe it: the bridge needs the take by name. -/
theorem fifo_join_not_routeA_step :
    ¬ NuStep [0, 1, 2] exRow (nview id exM) (nview id (qFire exM exJoin.base exE)) := by
  rintro ⟨-, -, v, hv, heq⟩
  have h0 := heq 0 (by simp)
  have h1 := heq 1 (by simp)
  have hv0 := hv 0 (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, if_true, true_or,
    or_true] at h0 h1
  simp [nview, exM] at hv0
  rcases hv0 with rfl | rfl
  · revert h1; decide
  · revert h0; decide

end Example

end Libpetri.Reference.NuLinkA
