import Libpetri.Novel.RouteA.Model

/-!
# Route A for `k > 0`: the slot bound and the simulation

Headline results ([NU-050] Route A, [NU-053]):

* `colour_slots_suffice` — along every ν run, the number of distinct live names is at most
  `k`, for any `k ≥ y·M₀` with `y` a non-negative weighting of the flat rows that weights
  every coloured place at least one and does not increase along any row (`y·C ≤ 0`; a
  validated P-semiflow has `y·C = 0`). This is the soundness of `colour_slot_bound`'s
  argument: a live name holds a token in some coloured place, so
  `#live ≤ Σ_{coloured} M(p) ≤ y·M ≤ y·M₀ ≤ k`. The flat side is `Novel/ForwardDeposit.lean`'s
  Proposition 1 over deposit rows and `Novel/LinearBound.lean`'s `dot_le_initial_rows`.
* `coloured_simulates` — every ν-reachable marking is represented, under a colour assignment
  **injective on its live names**, by a state the encoding reaches. The injection is chosen
  along the run: a mint takes a colour no live name holds, which exists **because of**
  `colour_slots_suffice` applied to the marking *after* the mint.
* `routeA_safety_sound` — a reachability-safety `Proven` of the encoding (no reachable
  encoding state has a bad aggregate) holds of every ν-reachable marking.
* `routeA_quiescence_sound` — a quiescence `Proven` (no reachable encoding state is dead with
  a bad aggregate) holds too: a dead ν marking is represented by a state `DeadE` holds of.
  A join disabled for lack of a common name is disabled for every colour **because** the
  assignment is injective: two keys holding colour `c` hold the one live name of colour `c`.
  Untimed only: with a reapable transition (timing `Deadline` or `Window`,
  `reaping::is_reapable`) the executor rests at markings that are not ν-dead
  (`RouteA/Reaping.lean` has the reaping-aware version the shipped encoder implements, and the
  witness).

Premises (`Premises`), each named against the Rust:
* `classOK` — every row is as `build_plan` classified it;
* `guardFree` — P5 (no guard on a consume-all arc);
* `noSelfLoop`: **not checked by `build_plan`**; its failure was a wrong `Proven` of the old
  encoder (`Retrodict.lean`, `self_loop_consume_false_proven`). The shipped encoder nets the
  self-loop and needs no such premise (`Shipped.lean`, `premises_shipped`);
* `seed`, `empty` — the encoder's seed is `α(m₀)` (the seam, gap R3) and the coloured places
  start empty (checked by `build_plan`);
* `cover` — what `colour_slot_bound` returns (`Plan.lean`, `colourSlotBound_sound`);
* `laws` — each conjoined invariant passed `validate_invariants_exact` (H1 and `y·C = 0`,
  `Semiflow.lean`'s `ValidLaw` over deposit rows);
* the ν semantics itself carries P1–P4 (`Model.lean`), and `ReachNu` has no injection
  (`coloured_attempt` declines under injection; `Retrodict.lean`,
  `injection_breaks_closed_encoding`).
-/

namespace Libpetri.Novel.RouteA

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.LinearBound

/-! ## Counting names by colour -/

theorem cnt_nil (σ : Name → Nat) (c : Nat) : cnt σ c [] = 0 := rfl

theorem cnt_append (σ : Name → Nat) (c : Nat) (l₁ l₂ : List Name) :
    cnt σ c (l₁ ++ l₂) = cnt σ c l₁ + cnt σ c l₂ := List.countP_append

theorem cnt_single (σ : Name → Nat) (c : Nat) (v : Name) :
    cnt σ c [v] = if σ v = c then 1 else 0 := by
  unfold cnt
  by_cases h : σ v = c <;> simp [h]

theorem cnt_congr {σ σ' : Name → Nat} {c : Nat} :
    ∀ {l : List Name}, (∀ x ∈ l, σ x = σ' x) → cnt σ c l = cnt σ' c l
  | [], _ => rfl
  | x :: l, h => by
    have ih := cnt_congr (σ := σ) (σ' := σ') (c := c) (l := l)
      fun y hy => h y (List.mem_cons_of_mem x hy)
    unfold cnt at ih ⊢
    rw [List.countP_cons, List.countP_cons, h x List.mem_cons_self, ih]

theorem cnt_pos {σ : Name → Nat} {c : Nat} {l : List Name} {v : Name} (hv : v ∈ l)
    (hc : σ v = c) : 1 ≤ cnt σ c l :=
  List.countP_pos_iff.mpr ⟨v, hv, by simp [hc]⟩

theorem exists_of_cnt_pos {σ : Name → Nat} {c : Nat} {l : List Name} (h : 1 ≤ cnt σ c l) :
    ∃ x ∈ l, σ x = c := by
  obtain ⟨x, hx, hp⟩ := List.countP_pos_iff.mp h
  exact ⟨x, hx, by simpa using hp⟩

theorem cnt_zero_of {σ : Name → Nat} {c : Nat} {l : List Name} (h : ∀ x ∈ l, σ x ≠ c) :
    cnt σ c l = 0 :=
  List.countP_eq_zero.mpr fun x hx => by simpa using h x hx

/-- Removing one occurrence of a member removes one token of its colour. -/
theorem cnt_erase {σ : Name → Nat} {c : Nat} {l : List Name} {v : Name} (hv : v ∈ l) :
    cnt σ c (l.erase v) + (if σ v = c then 1 else 0) = cnt σ c l := by
  unfold cnt
  rw [List.countP_erase]
  by_cases h : σ v = c
  · have hpos := cnt_pos (σ := σ) hv h
    unfold cnt at hpos
    simp [hv, h]
    omega
  · simp [h]

/-- Summed over the `k` colours, the colour counts of a list whose colours are all below `k`
are its length: `Layout::aggregate` recovers the token count. -/
theorem sum_cnt {σ : Name → Nat} {k : Nat} :
    ∀ {l : List Name}, (∀ x ∈ l, σ x < k) → ∑ c ∈ Finset.range k, cnt σ c l = l.length
  | [], _ => by simp [cnt_nil]
  | x :: l, h => by
    have ih := sum_cnt (l := l) fun y hy => h y (List.mem_cons_of_mem x hy)
    have hx : σ x ∈ Finset.range k := Finset.mem_range.mpr (h x List.mem_cons_self)
    have hcons : ∀ c, cnt σ c (x :: l) = cnt σ c l + (if σ x = c then 1 else 0) := by
      intro c
      unfold cnt
      rw [List.countP_cons]
      by_cases hc : σ x = c <;> simp [hc]
    simp only [hcons, Finset.sum_add_distrib, ih, Finset.sum_ite_eq, hx, if_true,
      List.length_cons]

/-! ## Live names -/

theorem mem_live {C : List PlaceId} {m : CMarking} {x : Name} :
    x ∈ live C m ↔ ∃ p ∈ C, x ∈ m p := by
  unfold live
  exact List.mem_flatMap

/-- If every token of `m'` on a coloured place was in `m` there or is `v`, and `v` is live in
`m`, the live names of `m'` are live in `m`. -/
theorem live_sub {C : List PlaceId} {m m' : CMarking} {v : Name}
    (h : ∀ p ∈ C, ∀ x ∈ m' p, x ∈ m p ∨ x = v) (hv : v ∈ live C m) :
    ∀ x ∈ live C m', x ∈ live C m := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_live.mp hx
  rcases h p hp x hxp with h' | rfl
  · exact mem_live.mpr ⟨p, hp, h'⟩
  · exact hv

/-! ## The aggregates of a represented marking -/

/-- A represented marking has the encoding's aggregates as its token counts. -/
theorem agg_of_sim {C : List PlaceId} {k : Nat} {m : CMarking} {e : EState} {σ : Name → Nat}
    (h : Sim C k m e σ) : agg C k e = alpha m := by
  funext p
  unfold agg alpha
  by_cases hp : p ∈ C
  · rw [if_pos hp]
    rw [Finset.sum_congr rfl fun c _ => h.col p hp c]
    exact sum_cnt fun x hx => h.lt x (mem_live.mpr ⟨p, hp, hx⟩)
  · rw [if_neg hp]
    exact h.unc p hp

/-! ## The flat projection and the slot bound -/

/-- A ν run is a run of the flat rows (`StepCR`), hence (Proposition 1 over deposit rows) an
abstract run of the flat encoding. -/
theorem reachNu_flat {C : List PlaceId} {rows : List CRow} {m0 m : CMarking}
    (hG : ∀ r ∈ rows, GuardFreeConsumeAll r.t) (h : ReachNu C rows m0 m) :
    ReachAD (rows.map CRow.flat) (alpha m0) (alpha m) :=
  rows_reachability_simulated
    (fun tr htr => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp htr
      exact hG r hr)
    (Relation.ReflTransGen.lift id
      (fun _ _ hs => by
        obtain ⟨r, hr, hst⟩ := hs
        exact ⟨r.flat, List.mem_map.mpr ⟨r, hr, rfl⟩, hst.enabled, hst.counts⟩) m0 m h)

/-- Per-step conservation over a deposit row (the `fireAD` twin of `dot_fireA`): H1 and a
zero incidence column keep `y·M`. -/
theorem dot_fireAD_eq (y : Weight) {a : AMarking} {t : Transition} {d : Deposit} {n : Nat}
    (h1 : ZeroOnNonlinear y t n) (h2 : dotIncD y (t, d) n = 0) (hEn : enabledA a t = true) :
    dot y (fireAD a t d) n = dot y a n := by
  have hsplit : dot y (fireAD a t d) n = dot y a n + dotIncD y (t, d) n := by
    rw [dot_eq_isum, dot_eq_isum, dotIncD, ← isum_add]
    refine isum_congr fun p hp => ?_
    show y p * (fireAD a t d p : Int)
      = y p * (a p : Int) + y p * ((d.count p : Int) - (pre t p : Int))
    by_cases hR : t.resets.contains p = true
    · rw [h1 p hp (Or.inl hR)]
      simp
    · by_cases hCA : consumeAllAt t p = true
      · rw [h1 p hp (Or.inr hCA)]
        simp
      · have hfa : fireAD a t d p = a p - pre t p + d.count p := by
          unfold fireAD
          rw [if_neg hR, if_neg hCA]
        have hle := pre_le_of_enabledA hEn p
        rw [hfa, ← Int.mul_add]
        congr 1
        omega
  rw [hsplit, h2]
  omega

/-- A validated law (H1, `y·C = 0`) is conserved along every run of deposit rows: the lifted
invariant `encode_rule` conjoins is true of every flat-reachable marking. -/
theorem laws_conserved {rows : List (Transition × Deposit)} {a0 a : AMarking} {y : Weight}
    {n : Nat} (hl : ∀ tr ∈ rows, ZeroOnNonlinear y tr.1 n ∧ dotIncD y tr n = 0)
    (h : ReachAD rows a0 a) : dot y a n = dot y a0 n := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨tr, hmem, hen, rfl⟩ := hs
    exact (dot_fireAD_eq y (hl tr hmem).1 (hl tr hmem).2 hen).trans ih

/-- With `y ≥ 0` and `y ≥ 1` on the (duplicate-free, dense) coloured places, their token total
is below `y·M`. -/
theorem sum_le_dot {C : List PlaceId} {y : Weight} {a : AMarking} {n : Nat}
    (hnd : C.Nodup) (hCn : ∀ p ∈ C, p < n) (hpos : ∀ p, p < n → 0 ≤ y p)
    (hcov : ∀ p ∈ C, 1 ≤ y p) :
    (((C.map a).sum : Nat) : Int) ≤ dot y a n := by
  rw [← List.sum_toFinset _ hnd, dot_eq_isum, isum]
  push_cast
  calc ∑ p ∈ C.toFinset, (a p : Int) ≤ ∑ p ∈ C.toFinset, y p * (a p : Int) := by
        apply Finset.sum_le_sum
        intro p hp
        exact le_mul_of_one_le_left (Int.natCast_nonneg _) (hcov p (List.mem_toFinset.mp hp))
    _ ≤ ∑ p ∈ Finset.range n, y p * (a p : Int) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Finset.mem_range.mpr (hCn p (List.mem_toFinset.mp hp))
        · intro p hp _
          exact Int.mul_nonneg (hpos p (Finset.mem_range.mp hp)) (Int.natCast_nonneg _)

/-- **`colour_slots_suffice`.** Along every ν run, the distinct live names number at most `k`,
for `k ≥ y·M₀` and `y` a non-negative, non-increasing weighting that covers every coloured
place — the bound `colour_slot_bound` computes. -/
theorem colour_slots_suffice {C : List PlaceId} {rows : List CRow} {m0 m : CMarking}
    {y : Weight} {n k : Nat}
    (hG : ∀ r ∈ rows, GuardFreeConsumeAll r.t)
    (hnd : C.Nodup) (hCn : ∀ p ∈ C, p < n)
    (hpos : ∀ p, p < n → 0 ≤ y p) (hcov : ∀ p ∈ C, 1 ≤ y p)
    (hdec : ∀ r ∈ rows, dotIncD y r.flat n ≤ 0) (hk : dot y (alpha m0) n ≤ k)
    (h : ReachNu C rows m0 m) :
    (live C m).toFinset.card ≤ k := by
  have hflat := reachNu_flat hG h
  have hle : dot y (alpha m) n ≤ dot y (alpha m0) n :=
    dot_le_initial_rows (envs := []) hpos
      (fun tr htr => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp htr
        exact hdec r hr)
      (by simp) (reachAD_sub_inj hflat)
  have hsum := sum_le_dot (a := alpha m) hnd hCn hpos hcov
  have hlen : (live C m).length = (C.map (alpha m)).sum := by
    unfold live
    rw [List.length_flatMap]
    rfl
  have hcard := List.toFinset_card_le (live C m)
  omega

/-! ## One step of the simulation -/

/-- The uncoloured guards hold of a represented marking whose flat image enables the row. -/
theorem uGuard_of_sim {C : List PlaceId} {k : Nat} {m : CMarking} {e : EState}
    {σ : Name → Nat} {t : Transition} (harcs : NoTestArcs C t) (hsim : Sim C k m e σ)
    (hEn : enabledA (alpha m) t = true) : uGuard C e t := by
  have hEn' := hEn
  unfold enabledA at hEn'
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hEn'
  obtain ⟨⟨_, hinh⟩, hrd⟩ := hEn'
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [hsim.unc p hp]
    exact pre_le_of_enabledA hEn p
  · have hpC : p ∉ C := fun hc => (harcs p hc).2.2.1 hp
    rw [hsim.unc p hpC]
    exact hinh p hp
  · have hpC : p ∉ C := fun hc => (harcs p hc).2.2.2 hp
    rw [hsim.unc p hpC]
    exact hrd p hp

/-- `fireAD` at `p` reads only the column `p`. -/
theorem fireAD_congr_at {a b : AMarking} {t : Transition} {d : Deposit} {p : PlaceId}
    (h : a p = b p) : fireAD a t d p = fireAD b t d p := by
  unfold fireAD
  rw [h]

/-- The join rule under the colour of the consumed name keeps colour counting exact: the
`Class::Join` update (and the `Class::Consume` one without a self-loop) against the ν
threading effect. -/
theorem thread_col {C : List PlaceId} {σ : Name → Nat} {m m' : CMarking}
    {s : PlaceId → Nat → Nat} {ins rel : List PlaceId} {v : Name}
    (hcol : ∀ p ∈ C, ∀ c, s p c = cnt σ c (m p)) (hv : ∀ p ∈ ins, v ∈ m p)
    (hm' : ∀ p ∈ C, m' p = (if p ∈ ins then (m p).erase v else m p) ++
      (if p ∈ rel then [v] else [])) :
    ∀ p ∈ C, ∀ c, sJoin ins rel (σ v) s p c = cnt σ c (m' p) := by
  intro p hp c
  rw [hm' p hp, cnt_append]
  unfold sJoin
  rw [hcol p hp c]
  by_cases hi : p ∈ ins
  · have he := cnt_erase (σ := σ) (c := c) (hv p hi)
    by_cases hr : p ∈ rel
    · by_cases hc : c = σ v
      · subst hc
        simp only [hi, hr, if_true, cnt_single, not_true_eq_false, and_false,
          if_false] at he ⊢
        omega
      · have hc' : ¬ σ v = c := fun h => hc h.symm
        simp only [hi, hr, if_true, cnt_single, hc, hc', if_false] at he ⊢
        omega
    · by_cases hc : c = σ v
      · subst hc
        simp only [hi, hr, if_true, if_false, not_false_eq_true, and_self,
          cnt_nil] at he ⊢
        omega
      · have hc' : ¬ σ v = c := fun h => hc h.symm
        simp only [hi, hr, if_true, if_false, hc, hc', cnt_nil] at he ⊢
        omega
  · by_cases hr : p ∈ rel
    · by_cases hc : c = σ v
      · subst hc
        simp [hi, hr, cnt_single]
      · have hc' : ¬ σ v = c := fun h => hc h.symm
        simp [hi, hr, hc, hc', cnt_single]
    · by_cases hc : c = σ v
      · subst hc
        simp [hi, hr, cnt_nil]
      · simp [hi, hr, hc, cnt_nil]

/-- Without a self-loop the shipped `Class::Consume` update is the join update over the single
key: the write order cannot matter. -/
theorem sConsume_eq_sJoin {inp : PlaceId} {outs : List PlaceId} {c : Nat}
    {s : PlaceId → Nat → Nat} (h : inp ∉ outs) :
    sConsume inp outs c s = sJoin [inp] outs c s := by
  funext p c'
  unfold sConsume sJoin
  by_cases hc : c' = c
  · by_cases ho : p ∈ outs
    · have hpi : p ≠ inp := fun e => h (e ▸ ho)
      simp [hc, ho, hpi]
    · by_cases hpi : p = inp
      · subst hpi
        simp [hc, h]
      · simp [hc, ho, hpi]
  · simp [hc]

/-- **One step of the simulation.** A represented ν marking's firing is matched by one rule of
the encoding, with the colour assignment extended by the minted name's colour. The two facts
that need the whole run — the slot bound and the laws at the successor — are hypotheses. -/
theorem sim_step {E : Enc} {r : CRow} {m m' : CMarking} {e : EState} {σ : Name → Nat}
    (hok : ClassOK E.C r) (hnsl : ConsumeNoSelfLoop r.cls) (hG : GuardFreeConsumeAll r.t)
    (hs : NuStep E.C r m m') (hsim : Sim E.C E.k m e σ)
    (hslots : (live E.C m').toFinset.card ≤ E.k)
    (hinv : ∀ y ∈ E.invs, dot y (alpha m') E.n = dot y E.a0 E.n) :
    ∃ e' σ', EStep E r e e' ∧ Sim E.C E.k m' e' σ' := by
  obtain ⟨hEnA, hFire⟩ := prop1_step_deposit m r.t r.d hG hs.enabled
  have hcount : alpha m' = fireAD (alpha m) r.t r.d := hs.counts.trans hFire
  have hguard : uGuard E.C e r.t := uGuard_of_sim hok.arcs hsim hEnA
  have hunc' : ∀ p, p ∉ E.C → uFire E.C e r.t r.d p = (m' p).length := by
    intro p hp
    have h1 : (m' p).length = alpha m' p := rfl
    rw [h1, hcount]
    simp only [uFire, if_neg hp]
    exact fireAD_congr_at (hsim.unc p hp)
  suffices H : ∃ (s' : PlaceId → Nat → Nat) (σ' : Name → Nat),
      ColourStep E.C E.k r.cls e.s s' ∧ (∀ p ∈ E.C, ∀ c, s' p c = cnt σ' c (m' p)) ∧
      (∀ x ∈ live E.C m', ∀ x' ∈ live E.C m', σ' x = σ' x' → x = x') ∧
      (∀ x ∈ live E.C m', σ' x < E.k) by
    obtain ⟨s', σ', hcs, hcol, hinj, hlt⟩ := H
    have hsim' : Sim E.C E.k m' ⟨uFire E.C e r.t r.d, s'⟩ σ' := ⟨hunc', hcol, hinj, hlt⟩
    refine ⟨⟨uFire E.C e r.t r.d, s'⟩, σ', ⟨hguard, rfl, hcs, ?_⟩, hsim'⟩
    intro y hy
    rw [agg_of_sim hsim']
    exact hinv y hy
  obtain ⟨t, d, cls⟩ := r
  cases cls with
  | untouched =>
    have hm' : ∀ p ∈ E.C, m' p = m p := hs.names
    have hlive : ∀ x, x ∈ live E.C m' ↔ x ∈ live E.C m := by
      intro x
      simp only [mem_live]
      constructor
      · rintro ⟨p, hp, hx⟩
        exact ⟨p, hp, hm' p hp ▸ hx⟩
      · rintro ⟨p, hp, hx⟩
        exact ⟨p, hp, (hm' p hp).symm ▸ hx⟩
    refine ⟨e.s, σ, rfl, fun p hp c => ?_, fun x hx x' hx' h => ?_, fun x hx => ?_⟩
    · rw [hm' p hp]
      exact hsim.col p hp c
    · exact hsim.inj x ((hlive x).mp hx) x' ((hlive x').mp hx') h
    · exact hsim.lt x ((hlive x).mp hx)
  | mint outs =>
    obtain ⟨hne, houtC, _⟩ := hok.shape
    obtain ⟨v, hfresh, hm'⟩ := hs.names
    have hvnot : v ∉ live E.C m := fun hv => by
      obtain ⟨q, hq, hvq⟩ := mem_live.mp hv
      exact hfresh q hq hvq
    have hsub : ∀ p ∈ E.C, ∀ x ∈ m p, x ∈ m' p := by
      intro p hp x hx
      rw [hm' p hp]
      split
      · exact List.mem_append_left _ hx
      · exact hx
    have hlive' : ∀ x ∈ live E.C m', x ∈ live E.C m ∨ x = v := by
      intro x hx
      obtain ⟨p, hp, hxp⟩ := mem_live.mp hx
      rw [hm' p hp] at hxp
      split at hxp
      · rcases List.mem_append.mp hxp with h | h
        · exact Or.inl (mem_live.mpr ⟨p, hp, h⟩)
        · exact Or.inr (List.mem_singleton.mp h)
      · exact Or.inl (mem_live.mpr ⟨p, hp, hxp⟩)
    obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil outs hne
    have hvlive' : v ∈ live E.C m' := by
      refine mem_live.mpr ⟨o, houtC o ho, ?_⟩
      rw [hm' o (houtC o ho), if_pos ho]
      exact List.mem_append_right _ List.mem_cons_self
    -- The slot bound after the mint leaves a colour no live name holds.
    have hcardL : (live E.C m).toFinset.card + 1 ≤ E.k := by
      have hins : insert v (live E.C m).toFinset ⊆ (live E.C m').toFinset := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact List.mem_toFinset.mpr hvlive'
        · obtain ⟨p, hp, hxp⟩ := mem_live.mp (List.mem_toFinset.mp hx)
          exact List.mem_toFinset.mpr (mem_live.mpr ⟨p, hp, hsub p hp x hxp⟩)
      have h1 := Finset.card_le_card hins
      rw [Finset.card_insert_of_notMem (fun h => hvnot (List.mem_toFinset.mp h))] at h1
      omega
    have himg : ((live E.C m).toFinset.image σ).card < (Finset.range E.k).card := by
      rw [Finset.card_range]
      exact lt_of_le_of_lt Finset.card_image_le (by omega)
    obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card himg
    have hck : c < E.k := Finset.mem_range.mp hc
    have hnot : ∀ x ∈ live E.C m, σ x ≠ c := fun x hx hσ =>
      hcn (Finset.mem_image.mpr ⟨x, List.mem_toFinset.mpr hx, hσ⟩)
    have hfree : ∀ q ∈ E.C, e.s q c = 0 := by
      intro q hq
      rw [hsim.col q hq]
      exact cnt_zero_of fun x hx => hnot x (mem_live.mpr ⟨q, hq, hx⟩)
    let σ' : Name → Nat := fun x => if x = v then c else σ x
    have hσ'old : ∀ x ∈ live E.C m, σ' x = σ x := fun x hx => by
      have : x ≠ v := fun h => hvnot (h ▸ hx)
      simp [σ', this]
    refine ⟨sMint outs c e.s, σ', ⟨c, hck, hfree, rfl⟩, fun p hp c' => ?_,
      fun x hx x' hx' h => ?_, fun x hx => ?_⟩
    · have hcg : cnt σ' c' (m p) = cnt σ c' (m p) :=
        cnt_congr fun x hx => hσ'old x (mem_live.mpr ⟨p, hp, hx⟩)
      rw [hm' p hp]
      unfold sMint
      rw [hsim.col p hp c']
      by_cases ho : p ∈ outs
      · rw [if_pos ho, cnt_append, hcg, cnt_single]
        have hv' : σ' v = c := by simp [σ']
        rw [hv']
        by_cases hcc : c' = c
        · subst hcc
          simp [ho]
        · have : ¬ c = c' := fun h => hcc h.symm
          simp [hcc, this]
      · rw [if_neg ho, hcg]
        simp [ho]
    · rcases hlive' x hx with hxo | rfl <;> rcases hlive' x' hx' with hxo' | rfl
      · rw [hσ'old x hxo, hσ'old x' hxo'] at h
        exact hsim.inj x hxo x' hxo' h
      · exfalso
        rw [hσ'old x hxo] at h
        have : σ' x' = c := by simp [σ']
        exact hnot x hxo (h.trans this)
      · exfalso
        rw [hσ'old x' hxo'] at h
        have : σ' x = c := by simp [σ']
        exact hnot x' hxo' (h.symm.trans this)
      · rfl
    · rcases hlive' x hx with hxo | rfl
      · rw [hσ'old x hxo]
        exact hsim.lt x hxo
      · simp [σ', hck]
  | join ins rel =>
    obtain ⟨hne, hinC, _, _⟩ := hok.shape
    obtain ⟨v, hv, hm'⟩ := hs.names
    obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil ins hne
    have hvlive : v ∈ live E.C m := mem_live.mpr ⟨p0, hinC p0 hp0, hv p0 hp0⟩
    have hlive' : ∀ x ∈ live E.C m', x ∈ live E.C m := by
      refine live_sub (fun p hp x hx => ?_) hvlive
      rw [hm' p hp] at hx
      rcases List.mem_append.mp hx with h | h
      · split at h
        · exact Or.inl (List.mem_of_mem_erase h)
        · exact Or.inl h
      · split at h
        · exact Or.inr (List.mem_singleton.mp h)
        · exact absurd h (List.not_mem_nil)
    refine ⟨sJoin ins rel (σ v) e.s, σ, ⟨σ v, hsim.lt v hvlive, fun p hp => ?_, rfl⟩,
      thread_col hsim.col hv hm', fun x hx x' hx' h => hsim.inj x (hlive' x hx) x'
        (hlive' x' hx') h, fun x hx => hsim.lt x (hlive' x hx)⟩
    rw [hsim.col p (hinC p hp)]
    exact cnt_pos (hv p hp) rfl
  | consume inp outs =>
    have hnsl' : inp ∉ outs := hnsl
    obtain ⟨hinpC, _, _⟩ := hok.shape
    obtain ⟨v, hv, hm'⟩ := hs.names
    have hvlive : v ∈ live E.C m := mem_live.mpr ⟨inp, hinpC, hv⟩
    have hm'' : ∀ p ∈ E.C, m' p = (if p ∈ [inp] then (m p).erase v else m p) ++
        (if p ∈ outs then [v] else []) := by
      intro p hp
      rw [hm' p hp]
      simp only [List.mem_singleton]
    have hlive' : ∀ x ∈ live E.C m', x ∈ live E.C m := by
      refine live_sub (fun p hp x hx => ?_) hvlive
      rw [hm'' p hp] at hx
      rcases List.mem_append.mp hx with h | h
      · split at h
        · exact Or.inl (List.mem_of_mem_erase h)
        · exact Or.inl h
      · split at h
        · exact Or.inr (List.mem_singleton.mp h)
        · exact absurd h (List.not_mem_nil)
    refine ⟨sConsume inp outs (σ v) e.s, σ, ⟨σ v, hsim.lt v hvlive, ?_, rfl⟩, ?_,
      fun x hx x' hx' h => hsim.inj x (hlive' x hx) x' (hlive' x' hx') h,
      fun x hx => hsim.lt x (hlive' x hx)⟩
    · rw [hsim.col inp hinpC]
      exact cnt_pos hv rfl
    · rw [sConsume_eq_sJoin hnsl']
      exact thread_col hsim.col (fun p hp => by
        rw [List.mem_singleton] at hp
        exact hp ▸ hv) hm''

/-! ## The simulation over runs -/

/-- What the encoding call is given, and what the ν run assumes (see the module header). -/
structure Premises (E : Enc) (m0 : CMarking) : Prop where
  nodup : E.C.Nodup
  below : ∀ p ∈ E.C, p < E.n
  classOK : ∀ r ∈ E.rows, ClassOK E.C r
  guardFree : ∀ r ∈ E.rows, GuardFreeConsumeAll r.t
  noSelfLoop : ∀ r ∈ E.rows, ConsumeNoSelfLoop r.cls
  seed : E.a0 = alpha m0
  empty : ∀ p ∈ E.C, m0 p = []
  cover : ∃ y : Weight, (∀ p, p < E.n → 0 ≤ y p) ∧ (∀ p ∈ E.C, 1 ≤ y p) ∧
    (∀ r ∈ E.rows, dotIncD y r.flat E.n ≤ 0) ∧ dot y E.a0 E.n ≤ E.k
  laws : ∀ y ∈ E.invs, ∀ r ∈ E.rows, ZeroOnNonlinear y r.t E.n ∧ dotIncD y r.flat E.n = 0

/-- The seed represents the initial marking. -/
theorem sim_init {E : Enc} {m0 : CMarking} (P : Premises E m0) :
    Sim E.C E.k m0 (e0 E) (fun _ => 0) := by
  have hlive : ∀ x, x ∉ live E.C m0 := fun x hx => by
    obtain ⟨p, hp, hxp⟩ := mem_live.mp hx
    rw [P.empty p hp] at hxp
    exact List.not_mem_nil hxp
  refine ⟨fun p hp => ?_, fun p hp c => ?_, fun x hx => absurd hx (hlive x),
    fun x hx => absurd hx (hlive x)⟩
  · show (if p ∈ E.C then 0 else E.a0 p) = _
    rw [if_neg hp, P.seed]
    rfl
  · show 0 = _
    rw [P.empty p hp]
    rfl

/-- **`coloured_simulates`.** Every ν-reachable marking is represented — token counts on the
uncoloured columns, name counts per colour on the coloured ones, under a colour assignment
injective on its live names — by a state the name-coloured CHC system reaches. -/
theorem coloured_simulates {E : Enc} {m0 : CMarking} (P : Premises E m0) {m : CMarking}
    (h : ReachNu E.C E.rows m0 m) : ∃ e σ, ReachE E e ∧ Sim E.C E.k m e σ := by
  obtain ⟨y, hpos, hcov, hdec, hk⟩ := P.cover
  induction h with
  | refl => exact ⟨e0 E, fun _ => 0, Relation.ReflTransGen.refl, sim_init P⟩
  | @tail m1 m2 hr hs ih =>
    obtain ⟨e, σ, he, hsim⟩ := ih
    obtain ⟨r, hrm, hstep⟩ := hs
    have hr' : ReachNu E.C E.rows m0 m2 := Relation.ReflTransGen.tail hr ⟨r, hrm, hstep⟩
    have hslots := colour_slots_suffice P.guardFree P.nodup P.below hpos hcov hdec
      (P.seed ▸ hk) hr'
    have hinv : ∀ y ∈ E.invs, dot y (alpha m2) E.n = dot y E.a0 E.n := fun y hy => by
      rw [P.seed]
      exact laws_conserved
        (fun tr htr => by
          obtain ⟨r', hr'', rfl⟩ := List.mem_map.mp htr
          exact P.laws y hy r' hr'')
        (reachNu_flat P.guardFree hr')
    obtain ⟨e', σ', hE, hsim'⟩ := sim_step (P.classOK r hrm) (P.noSelfLoop r hrm)
      (P.guardFree r hrm) hstep hsim hslots hinv
    exact ⟨e', σ', Relation.ReflTransGen.tail he ⟨r, hrm, hE⟩, hsim'⟩

/-- The represented state carries the ν marking's token counts as its aggregates — what every
property arm of `encode_violation` reads (`lay.aggregate`). -/
theorem coloured_simulates_agg {E : Enc} {m0 : CMarking} (P : Premises E m0) {m : CMarking}
    (h : ReachNu E.C E.rows m0 m) : ∃ e, ReachE E e ∧ agg E.C E.k e = alpha m := by
  obtain ⟨e, σ, he, hsim⟩ := coloured_simulates P h
  exact ⟨e, he, agg_of_sim hsim⟩

/-- **Reachability safety.** A `Proven` of the name-coloured query — no reachable state whose
aggregates are bad — holds of every ν-reachable marking. -/
theorem routeA_safety_sound {E : Enc} {m0 : CMarking} (P : Premises E m0)
    {Bad : AMarking → Prop} (hproven : ∀ e, ReachE E e → ¬ Bad (agg E.C E.k e)) :
    ∀ m, ReachNu E.C E.rows m0 m → ¬ Bad (alpha m) := by
  intro m h hbad
  obtain ⟨e, he, hagg⟩ := coloured_simulates_agg P h
  exact hproven e he (hagg ▸ hbad)

/-! ## Quiescence -/

/-- Unguarded, the concrete enablement is the abstract one of the counts. -/
theorem enabledC_of_enabledA {m : CMarking} {t : Transition} (hu : Unguarded t)
    (h : enabledA (alpha m) t = true) : enabledC m t = true := by
  unfold enabledA at h
  unfold enabledC
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢
  obtain ⟨⟨hin, hinh⟩, hrd⟩ := h
  refine ⟨⟨fun s hs => ?_, fun p hp => hinh p hp⟩, fun p hp => hrd p hp⟩
  have hmc : matchCount m s = (m s.place).length := by
    unfold matchCount
    rw [hu s hs]
  rw [hmc]
  exact hin s hs

/-- A row whose counts disable it is disabled in the encoding: for an uncoloured reason, or —
when the missing token is on a key or on a consumer's input — for every colour. -/
theorem disabled_of_not_enabledC {C : List PlaceId} {k : Nat} {m : CMarking} {e : EState}
    {σ : Name → Nat} {r : CRow} (hok : ClassOK C r) (hu : Unguarded r.t)
    (hd : InputsDistinctPlaces r.t) (hsim : Sim C k m e σ) (hn : enabledC m r.t = false) :
    uDisabled C e r.t ∨ colDisabled C k r.cls e.s := by
  have hA : ¬ enabledA (alpha m) r.t = true := fun h => by
    rw [enabledC_of_enabledA hu h] at hn
    exact Bool.noConfusion hn
  by_cases hin : ∀ s ∈ r.t.inputs, s.card.required ≤ alpha m s.place
  · by_cases hinh : ∀ p ∈ r.t.inhibitors, alpha m p = 0
    · by_cases hrd : ∀ p ∈ r.t.reads, 1 ≤ alpha m p
      · exfalso
        apply hA
        unfold enabledA
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨⟨hin, hinh⟩, hrd⟩
      · push Not at hrd
        obtain ⟨p, hp, hlt⟩ := hrd
        have hpC : p ∉ C := fun hc => (hok.arcs p hc).2.2.2 hp
        left
        right
        right
        exact ⟨p, hp, by rw [hsim.unc p hpC]; exact hlt⟩
    · push Not at hinh
      obtain ⟨p, hp, hne⟩ := hinh
      have hpC : p ∉ C := fun hc => (hok.arcs p hc).2.2.1 hp
      left
      right
      left
      exact ⟨p, hp, by rw [hsim.unc p hpC]; exact Nat.pos_of_ne_zero hne⟩
  · push Not at hin
    obtain ⟨s, hs, hlt⟩ := hin
    have hpre : pre r.t s.place = s.card.required := by
      unfold pre
      rw [hd s hs]
    by_cases hpC : s.place ∈ C
    · have hshape := hok.shape
      obtain ⟨t, d, cls⟩ := r
      cases cls with
      | untouched =>
        have := (hshape s.place hpC).1
        omega
      | mint outs =>
        have := (hshape.2.2 s.place hpC).1
        omega
      | join ins rel =>
        right
        have h0 := (hshape.2.2.2 s.place hpC).1
        by_cases hi : s.place ∈ ins
        · rw [if_pos hi] at h0
          have hempty : m s.place = [] := by
            have : alpha m s.place = 0 := by omega
            exact List.eq_nil_of_length_eq_zero this
          intro c _
          exact ⟨s.place, hi, by rw [hsim.col s.place hpC, hempty]; rfl⟩
        · rw [if_neg hi] at h0
          omega
      | consume inp outs =>
        right
        have h0 := (hshape.2.2 s.place hpC).1
        by_cases hi : s.place = inp
        · rw [if_pos hi] at h0
          have hempty : m s.place = [] := by
            have : alpha m s.place = 0 := by omega
            exact List.eq_nil_of_length_eq_zero this
          intro c _
          show e.s inp c = 0
          rw [← hi, hsim.col s.place hpC, hempty]
          rfl
        · rw [if_neg hi] at h0
          omega
    · left
      left
      exact ⟨s.place, hpC, by rw [hsim.unc s.place hpC, hpre]; exact hlt⟩

/-- **A dead ν marking is represented by a dead encoding state.** The join case is where the
injectivity of the colour assignment is used. -/
theorem dead_transfer {E : Enc} {m : CMarking} {e : EState} {σ : Name → Nat}
    (hok : ∀ r ∈ E.rows, ClassOK E.C r) (hu : ∀ r ∈ E.rows, Unguarded r.t)
    (hd : ∀ r ∈ E.rows, InputsDistinctPlaces r.t) (hsim : Sim E.C E.k m e σ)
    (hdead : NuDead E.rows m) : DeadE E e := by
  intro r hr
  cases hen : enabledC m r.t with
  | false => exact disabled_of_not_enabledC (hok r hr) (hu r hr) (hd r hr) hsim hen
  | true =>
    have hne := hdead r hr
    have hshape := (hok r hr).shape
    obtain ⟨t, d, cls⟩ := r
    cases cls with
    | untouched => exact absurd ⟨hen, trivial⟩ hne
    | mint outs => exact absurd ⟨hen, trivial⟩ hne
    | consume inp outs => exact absurd ⟨hen, trivial⟩ hne
    | join ins rel =>
      right
      intro c _
      by_contra hall
      push Not at hall
      apply hne
      refine ⟨hen, ?_⟩
      obtain ⟨hne', hinC, _, _⟩ := hshape
      obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil ins hne'
      have hpos : ∀ p ∈ ins, 1 ≤ cnt σ c (m p) := fun p hp => by
        rw [← hsim.col p (hinC p hp)]
        exact Nat.one_le_iff_ne_zero.mpr (hall p hp)
      obtain ⟨x0, hx0, hσ0⟩ := exists_of_cnt_pos (hpos p0 hp0)
      refine ⟨x0, fun p hp => ?_⟩
      obtain ⟨x, hx, hσ⟩ := exists_of_cnt_pos (hpos p hp)
      have heq := hsim.inj x (mem_live.mpr ⟨p, hinC p hp, hx⟩) x0
        (mem_live.mpr ⟨p0, hinC p0 hp0, hx0⟩) (hσ.trans hσ0.symm)
      exact heq ▸ hx

/-- **Quiescence, untimed.** A `Proven` of a quiescence query — no reachable state that is dead
(`encode_coloured_quiescent`) with bad aggregates (the stranded / sink / pending / count clause
the property conjoins) — holds of every ν-reachable marking: none is dead with bad counts.

This is a statement about **ν-dead** markings only, for the strict `DeadE` (what
`encode_coloured_quiescent` emits under `assume_no_reaping`). It gives **no guarantee for timed
executions of a net with a reapable transition** (timing `Deadline` or `Window`,
`reaping::is_reapable`; `Exact` is never reaped): the executor reaps such a transition and comes
to rest at a marking where it is still enabled, which is not ν-dead, so this theorem does not
reach it (`Novel/ReapingVsUntimed.lean`; for Route A, `RouteA/Reaping.lean`,
`ReapW.reaping_breaks_routeA_quiescence`). The timed statements are
`routeA_quiescence_sound_reaping`, for the reaping-aware predicate `DeadER`, and
`routeA_reap_aware_sound`, for the shipped predicate `DeadERs` against the executor model of
`Novel/ReapAware.lean`. -/
theorem routeA_quiescence_sound {E : Enc} {m0 : CMarking} (P : Premises E m0)
    (hu : ∀ r ∈ E.rows, Unguarded r.t) (hd : ∀ r ∈ E.rows, InputsDistinctPlaces r.t)
    {Q : AMarking → Prop}
    (hproven : ∀ e, ReachE E e → ¬ (DeadE E e ∧ Q (agg E.C E.k e))) :
    ∀ m, ReachNu E.C E.rows m0 m → ¬ (NuDead E.rows m ∧ Q (alpha m)) := by
  intro m h ⟨hdead, hq⟩
  obtain ⟨e, σ, he, hsim⟩ := coloured_simulates P h
  exact hproven e he ⟨dead_transfer P.classOK hu hd hsim hdead, (agg_of_sim hsim) ▸ hq⟩

end Libpetri.Novel.RouteA
