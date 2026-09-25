/-
# The state equation with firing counters ([VER-016])

With `EncodeOptions::state_equation` the CHC state is `(M, n)`, one counter per
flat transition after the places (`encode_net`, `smt_encoder.rs:134-161`). The
init fact has `n = 0`. Rule `k` sets `n'_k = n_k + 1`, copies the other
counters and conjoins `n' ≥ 0` (`counter_conditions`). An injection rule copies
every counter (`encode_injection_rule`). After the P-invariants, each
transition-rule body conjoins one row per non-injected place
(`state_equation_conditions`): `m'_p = M0_p + Σ_k C[p][k]·n'_k`, or `≤` where a
consume-all or reset arc clears `p` (`nonlinear_places`; [VER-016] AC2).

* `rows_hold`: every row holds on every reachable augmented state. A linear arm
  moves both sides by `C[p][k]`. A clearing arm yields `post ≤ m − pre + post`,
  because its guard needs `m ≥ pre`.
* `state_equation_reach_eq`: conjoining the rows and every gate-validated law
  into the transition rules removes no augmented state.
* `counters_erase` / `counters_exist`: the counters are bookkeeping, so the
  option neither adds nor loses a marking of `ReachAInj`.
* `equality_row_is_unsound_on_a_clearing_place`: the reason AC2 weakens the
  row to `≤` instead of keeping `=`.

Out of scope: the certificate check over `(M, n)` ([VER-016] AC3), the
`Bounded k` injection guard and legacy `env_bounds` caps (both only restrict
steps, so `rows_hold` still applies), and script byte-identity.
-/
import Libpetri.Semiflow

namespace Libpetri

/-- Firing counters by flat-transition index: the `n_k` that follow the places
in `Reachable`. `Nat`-valued, so the emitted `n' ≥ 0` holds by construction. -/
abbrev Counters := Nat → Nat

/-- `n'` of rule `k` (`counter_conditions`, `smt_encoder.rs:254-267`):
`n'_k = n_k + 1`, every other counter copied. -/
def bump (n : Counters) (k : Nat) : Counters :=
  fun j => if j = k then n j + 1 else n j

/-- `C[p][k] = post − pre` of flat transition `k`, `0` past the end: the
coefficient `state_equation_conditions` reads off `ft.post[p] - ft.pre[p]`
(`smt_encoder.rs:294-308`). -/
def incAt (net : FlatNet) (k : Nat) (p : PlaceId) : Int :=
  match net[k]? with
  | some ft => (post ft.2 p : Int) - (pre ft.1 p : Int)
  | none => 0

/-- `M0_p + Σ_k C[p][k]·n_k` over the transition indices. The encoder omits
zero terms, which does not change the sum. -/
def rowRhs (net : FlatNet) (a0 : AMarking) (n : Counters) (p : PlaceId) : Int :=
  (a0 p : Int) + isum (fun k => incAt net k p * (n k : Int)) net.length

/-- Some flat transition clears `p` with a reset or consume-all arc
(`nonlinear_places`, `p_invariant.rs:229-245`). -/
def cleared (net : FlatNet) (p : PlaceId) : Bool :=
  net.any fun ft => ft.1.resets.contains p || consumeAllAt ft.1 p

/-- The row `state_equation_conditions` emits for `p`
(`smt_encoder.rs:269-319`): `≤` on a cleared place, `=` elsewhere. -/
def Row (net : FlatNet) (a0 a : AMarking) (n : Counters) (p : PlaceId) : Prop :=
  if cleared net p = true then (a p : Int) ≤ rowRhs net a0 n p
  else (a p : Int) = rowRhs net a0 n p

/-- One step of `ReachCnt` on an augmented state `(M, n)`: flat transition `k`
fires and bumps its counter, or an environment place receives a token. -/
def StepCntRel (net : FlatNet) (envs : List PlaceId) (s s' : AMarking × Counters) : Prop :=
  (∃ k ft, net[k]? = some ft ∧ enabledA s.1 ft.1 = true ∧
      s' = (fireA s.1 ft.1 ft.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- `ReachAInj` over augmented states `(M, n)`: the least fixpoint of the
options-on rules without their strengthening conjuncts. -/
def ReachCnt (net : FlatNet) (envs : List PlaceId) (a0 : AMarking) :
    AMarking → Counters → Prop :=
  fun a n => Relation.ReflTransGen (StepCntRel net envs) (a0, fun _ => 0) (a, n)

theorem ReachCnt.init {net envs a0} : ReachCnt net envs a0 a0 (fun _ => 0) :=
  Relation.ReflTransGen.refl

theorem ReachCnt.step {net envs a0 a n} {k : Nat} {ft : FlatTransition}
    (h : ReachCnt net envs a0 a n) (hk : net[k]? = some ft) (hen : enabledA a ft.1 = true) :
    ReachCnt net envs a0 (fireA a ft.1 ft.2) (bump n k) :=
  Relation.ReflTransGen.tail h (Or.inl ⟨k, ft, hk, hen, rfl⟩)

theorem ReachCnt.inject {net envs a0 a n} {p : PlaceId}
    (h : ReachCnt net envs a0 a n) (hp : p ∈ envs) :
    ReachCnt net envs a0 (fun q => if q == p then a q + 1 else a q) n :=
  Relation.ReflTransGen.tail h (Or.inr ⟨p, hp, rfl⟩)

/-- Induction over `ReachCnt` with the cases of the former inductive. -/
@[elab_as_elim, induction_eliminator]
theorem ReachCnt.rec' {net envs a0}
    {motive : (a : AMarking) → (n : Counters) → ReachCnt net envs a0 a n → Prop}
    (init : motive a0 (fun _ => 0) ReachCnt.init)
    (step : ∀ {a n k ft} (hr : ReachCnt net envs a0 a n) (hk : net[k]? = some ft)
      (hen : enabledA a ft.1 = true),
      motive a n hr → motive (fireA a ft.1 ft.2) (bump n k) (ReachCnt.step hr hk hen))
    (inject : ∀ {a n p} (hr : ReachCnt net envs a0 a n) (hp : p ∈ envs), motive a n hr →
      motive (fun q => if q == p then a q + 1 else a q) n (ReachCnt.inject hr hp))
    {a : AMarking} {n : Counters} (h : ReachCnt net envs a0 a n) : motive a n h := by
  suffices ∀ s (h : Relation.ReflTransGen (StepCntRel net envs) (a0, fun _ => 0) s),
      motive s.1 s.2 h from this (a, n) h
  intro s h
  induction h with
  | refl => exact init
  | tail hr hs ih =>
    rcases hs with ⟨k, ft, hk, hen, rfl⟩ | ⟨p, hp, rfl⟩
    · exact step hr hk hen ih
    · exact inject hr hp ih

/-- One step of `ReachCntStr`: a firing whose successor keeps every law of `ys`
and every non-injected row below `w`, or an unconstrained injection. -/
def StepCntStrRel (net : FlatNet) (envs : List PlaceId) (ys : List Weight) (w : Nat)
    (a0 : AMarking) (s s' : AMarking × Counters) : Prop :=
  (∃ k ft, net[k]? = some ft ∧ enabledA s.1 ft.1 = true ∧
      (∀ y ∈ ys, dot y (fireA s.1 ft.1 ft.2) w = dot y a0 w) ∧
      (∀ p, p < w → p ∉ envs → Row net a0 (fireA s.1 ft.1 ft.2) (bump s.2 k) p) ∧
      s' = (fireA s.1 ft.1 ft.2, bump s.2 k))
  ∨ ∃ p ∈ envs, s' = (fun q => if q == p then s.1 q + 1 else s.1 q, s.2)

/-- The shipped options-on rules (`encode_net`, `smt_encoder.rs:151-173`):
every transition rule conjoins each law of `ys` and the row of every
non-injected place below `w` over `(M', n')`; injection rules conjoin
neither. -/
def ReachCntStr (net : FlatNet) (envs : List PlaceId) (ys : List Weight)
    (w : Nat) (a0 : AMarking) : AMarking → Counters → Prop :=
  fun a n => Relation.ReflTransGen (StepCntStrRel net envs ys w a0) (a0, fun _ => 0) (a, n)

theorem ReachCntStr.init {net envs ys w a0} : ReachCntStr net envs ys w a0 a0 (fun _ => 0) :=
  Relation.ReflTransGen.refl

theorem ReachCntStr.step {net envs ys w a0 a n} {k : Nat} {ft : FlatTransition}
    (h : ReachCntStr net envs ys w a0 a n) (hk : net[k]? = some ft)
    (hen : enabledA a ft.1 = true)
    (hc : ∀ y ∈ ys, dot y (fireA a ft.1 ft.2) w = dot y a0 w)
    (hrow : ∀ p, p < w → p ∉ envs → Row net a0 (fireA a ft.1 ft.2) (bump n k) p) :
    ReachCntStr net envs ys w a0 (fireA a ft.1 ft.2) (bump n k) :=
  Relation.ReflTransGen.tail h (Or.inl ⟨k, ft, hk, hen, hc, hrow, rfl⟩)

theorem ReachCntStr.inject {net envs ys w a0 a n} {p : PlaceId}
    (h : ReachCntStr net envs ys w a0 a n) (hp : p ∈ envs) :
    ReachCntStr net envs ys w a0 (fun q => if q == p then a q + 1 else a q) n :=
  Relation.ReflTransGen.tail h (Or.inr ⟨p, hp, rfl⟩)

/-- Induction over `ReachCntStr` with the cases of the former inductive. -/
@[elab_as_elim, induction_eliminator]
theorem ReachCntStr.rec' {net envs ys w a0}
    {motive : (a : AMarking) → (n : Counters) → ReachCntStr net envs ys w a0 a n → Prop}
    (init : motive a0 (fun _ => 0) ReachCntStr.init)
    (step : ∀ {a n k ft} (hr : ReachCntStr net envs ys w a0 a n) (hk : net[k]? = some ft)
      (hen : enabledA a ft.1 = true)
      (hc : ∀ y ∈ ys, dot y (fireA a ft.1 ft.2) w = dot y a0 w)
      (hrow : ∀ p, p < w → p ∉ envs → Row net a0 (fireA a ft.1 ft.2) (bump n k) p),
      motive a n hr →
      motive (fireA a ft.1 ft.2) (bump n k) (ReachCntStr.step hr hk hen hc hrow))
    (inject : ∀ {a n p} (hr : ReachCntStr net envs ys w a0 a n) (hp : p ∈ envs),
      motive a n hr →
      motive (fun q => if q == p then a q + 1 else a q) n (ReachCntStr.inject hr hp))
    {a : AMarking} {n : Counters} (h : ReachCntStr net envs ys w a0 a n) : motive a n h := by
  suffices ∀ s (h : Relation.ReflTransGen (StepCntStrRel net envs ys w a0) (a0, fun _ => 0) s),
      motive s.1 s.2 h from this (a, n) h
  intro s h
  induction h with
  | refl => exact init
  | tail hr hs ih =>
    rcases hs with ⟨k, ft, hk, hen, hc, hrow, rfl⟩ | ⟨p, hp, rfl⟩
    · exact step hr hk hen hc hrow ih
    · exact inject hr hp ih

/-! ## The counters are bookkeeping -/

theorem counters_erase {net : FlatNet} {envs : List PlaceId} {a0 a : AMarking}
    {n : Counters} (h : ReachCnt net envs a0 a n) : ReachAInj net envs a0 a := by
  induction h with
  | init => exact ReachAInj.init
  | step _ hk hen ih => exact ReachAInj.step ih (List.mem_of_getElem? hk) hen
  | inject _ hp ih => exact ReachAInj.inject ih hp

theorem counters_exist {net : FlatNet} {envs : List PlaceId} {a0 a : AMarking}
    (h : ReachAInj net envs a0 a) : ∃ n, ReachCnt net envs a0 a n := by
  induction h with
  | init => exact ⟨_, ReachCnt.init⟩
  | step _ hmem hen ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
    exact ⟨_, ReachCnt.step hn hk hen⟩
  | inject _ hp ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨_, ReachCnt.inject hn hp⟩

/-! ## Every row holds on the reachable set -/

theorem rowRhs_zero (net : FlatNet) (a0 : AMarking) (p : PlaceId) :
    rowRhs net a0 (fun _ => 0) p = a0 p := by
  have : ∀ m, isum (fun k => incAt net k p * ((0 : Nat) : Int)) m = 0 := fun m => by
    simp [isum]
  unfold rowRhs
  rw [this]
  omega

/-- Firing `k` adds exactly column `k` to the counted sum. -/
theorem isum_bump (c : Nat → Int) (n : Counters) {k : Nat} :
    ∀ {m}, k < m →
      isum (fun j => c j * (bump n k j : Int)) m
        = isum (fun j => c j * (n j : Int)) m + c k
  | 0, h => absurd h (Nat.not_lt_zero k)
  | m + 1, h => by
    rw [isum_succ, isum_succ]
    by_cases hkm : k = m
    · subst hkm
      have hframe : isum (fun j => c j * (bump n k j : Int)) k
          = isum (fun j => c j * (n j : Int)) k :=
        isum_congr fun j hj => by
          simp [bump, Nat.ne_of_lt hj]
      rw [hframe]
      simp only [bump, ite_true, Int.natCast_add, Int.mul_add, Int.natCast_one, Int.mul_one]
      omega
    · rw [isum_bump c n (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hkm)]
      simp only [bump, if_neg (Ne.symm hkm)]
      omega

theorem rowRhs_bump {net : FlatNet} {a0 : AMarking} {n : Counters} {k : Nat}
    {ft : FlatTransition} (hk : net[k]? = some ft) (p : PlaceId) :
    rowRhs net a0 (bump n k) p
      = rowRhs net a0 n p + ((post ft.2 p : Int) - (pre ft.1 p : Int)) := by
  have hlt : k < net.length := (List.getElem?_eq_some_iff.mp hk).1
  have hc : incAt net k p = (post ft.2 p : Int) - (pre ft.1 p : Int) := by
    unfold incAt
    rw [hk]
  unfold rowRhs
  rw [isum_bump _ n hlt, hc]
  omega

/-- One firing preserves the row: the linear arm moves both sides by
`C[p][k]`; a clearing arm leaves `post`, at most `m − pre + post`. -/
theorem row_fire {net : FlatNet} {a0 a : AMarking} {n : Counters} {k : Nat}
    {ft : FlatTransition} (hk : net[k]? = some ft) (hen : enabledA a ft.1 = true)
    {p : PlaceId} (hrow : Row net a0 a n p) :
    Row net a0 (fireA a ft.1 ft.2) (bump n k) p := by
  have hle := pre_le_of_enabledA hen p
  unfold Row at hrow ⊢
  rw [rowRhs_bump hk p]
  by_cases hcl : cleared net p = true
  · rw [if_pos hcl] at hrow ⊢
    unfold fireA
    split
    · omega
    · split <;> omega
  · rw [if_neg hcl] at hrow ⊢
    have hmem := List.mem_of_getElem? hk
    have hlin : ¬ (ft.1.resets.contains p || consumeAllAt ft.1 p) = true :=
      fun h => hcl (List.any_eq_true.mpr ⟨ft, hmem, h⟩)
    simp only [Bool.or_eq_true, not_or] at hlin
    have hfa : fireA a ft.1 ft.2 p = a p - pre ft.1 p + post ft.2 p := by
      unfold fireA
      rw [if_neg hlin.1, if_neg hlin.2]
    rw [hfa]
    omega

/-- **The state equation is invariant** ([VER-016] AC2): on every reachable
augmented state, every non-injected place satisfies its row. -/
theorem rows_hold {net : FlatNet} {envs : List PlaceId} {a0 a : AMarking}
    {n : Counters} (h : ReachCnt net envs a0 a n) :
    ∀ p, p ∉ envs → Row net a0 a n p := by
  induction h with
  | init =>
    intro p _
    unfold Row
    rw [rowRhs_zero]
    split <;> omega
  | step _ hk hen ih => exact fun p hp => row_fire hk hen (ih p hp)
  | @inject a1 n1 q _ hq ih =>
    intro p hp
    have hpq : (p == q) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun h => hp (h ▸ hq)
    have := ih p hp
    unfold Row at this ⊢
    simp only [hpq]
    exact this

/-- **Conjoining the state equation is sound** ([VER-016]): with every law of
`ys` gate-validated (H1, H2, H3′), the options-on strengthened rules reach
exactly the augmented states the plain ones do. Pure strengthening: no
successor is removed, so no `Violated` can turn into `Proven`. -/
theorem state_equation_reach_eq {net : FlatNet} {envs : List PlaceId}
    {ys : List Weight} {w : Nat} {a0 : AMarking}
    (hv : ∀ y ∈ ys, ValidLawInj net envs w y) :
    ∀ a n, ReachCnt net envs a0 a n ↔ ReachCntStr net envs ys w a0 a n := by
  intro a n
  constructor
  · intro h
    induction h with
    | init => exact ReachCntStr.init
    | @step a1 n1 k ft hr hk hen ih =>
      have hmem := List.mem_of_getElem? hk
      refine ReachCntStr.step ih hk hen (fun y hy => ?_)
        (fun p _ hp => rows_hold (ReachCnt.step hr hk hen) p hp)
      exact (dot_fireA y ((hv y hy).h1 ft hmem) ((hv y hy).h2 ft hmem) hen).trans
        (invariant_strengthening_sound_inj (hv y hy).h1 (hv y hy).h2 (hv y hy).h3
          (counters_erase hr))
    | inject _ hp ih => exact ReachCntStr.inject ih hp
  · intro h
    induction h with
    | init => exact ReachCnt.init
    | step _ hk hen _ _ ih => exact ReachCnt.step ih hk hen
    | inject _ hp ih => exact ReachCnt.inject ih hp

/-! ## Why a clearing place gets `≤`, not `=` -/

/-- On `netAll` (`Strengthening.lean`), `drain_all` clears place `0`, which
holds two tokens, with an `In::All` of `pre = 1`. After one firing the place is
empty while the linear count says `2 − 1 = 1`. The state is reachable and
satisfies `≤`, but an `=` row would prune it. -/
theorem equality_row_is_unsound_on_a_clearing_place :
    ReachCnt netAll [] a0All (fireA a0All tAll [1]) (bump (fun _ => 0) 0)
    ∧ cleared netAll 0 = true
    ∧ ((fireA a0All tAll [1] 0 : Nat) : Int)
        ≠ rowRhs netAll a0All (bump (fun _ => 0) 0) 0
    ∧ Row netAll a0All (fireA a0All tAll [1]) (bump (fun _ => 0) 0) 0 :=
  have hr : ReachCnt netAll [] a0All (fireA a0All tAll [1]) (bump (fun _ => 0) 0) :=
    ReachCnt.step (k := 0) (ft := (tAll, [1])) ReachCnt.init rfl (by decide)
  ⟨hr, by decide, by decide, rows_hold hr 0 (by simp)⟩

end Libpetri
