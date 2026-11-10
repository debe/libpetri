import Libpetri.Novel.FiringBound.Ranking

/-!
# The bounded model check is exact ([VER-019], [VER-025])

`encode_bounded_run` as a constraint system over integer assignments, `decode_bounded_run`
(`decodeRust`), and exactness: a model at depth `d` exists iff some run of at most `d` steps
reaches a violating marking. See `Libpetri/Novel/FiringBound.lean`.

A step is a flat transition firing or, since [VER-025], an environment-injection step
([VER-006]). `BmcModelEnv` is the script with `J` injections: selector `T + j` injects into the
place of injection `j`, the idle selector is `T + J`. `BmcModel` is the injection-free script of
[VER-019] (`J = 0`, byte-identical), and `bmcModelEnv_nil` shows it is `BmcModelEnv` at the
empty injection list; every [VER-019] theorem below is the `J = 0` case of its `Env` form.
-/

namespace Libpetri.Novel.FiringBound

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.LinearBound

/-! ## The bounded run: the constraint system of `encode_bounded_run` -/

/-- `clears`: a consume-all input or a reset arc empties the place. -/
def clears (tr : Row) (p : PlaceId) : Bool :=
  consumeAllAt tr.1 p || tr.1.resets.contains p

/-- `column`: the flat `post − pre` at `p`, exact. -/
def column (tr : Row) (p : PlaceId) : Int :=
  (tr.2.count p : Int) - (pre tr.1 p : Int)

/-- A row touches `p` when it clears it or its column there is nonzero. -/
def touches (tr : Row) (p : PlaceId) : Bool :=
  clears tr p || column tr p != 0

/-- The rows touching `p`, in net order; the Rust reverses the list before nesting. -/
def touching (rows : List Row) (p : PlaceId) : List Nat :=
  (List.range rows.length).filter fun t =>
    match rows[t]? with
    | some tr => touches tr p
    | none => false

/-- The arm of row `t` at `p` over the previous value `v`: `post[p]` when the row clears `p`,
`v + column` otherwise (`shifted`). -/
def nextVal (rows : List Row) (v : Int) (p : PlaceId) (t : Nat) : Int :=
  match rows[t]? with
  | some tr => if clears tr p = true then (tr.2.count p : Int) else v + column tr p
  | none => v

/-- The `ite` chain for one place and step: over the touching rows reversed,
`value ← (ite (= s t) next value)`, starting from the previous value. -/
def chain (sel : Int) (touch : List Nat) (br : Nat → Int) (base : Int) : Int :=
  touch.reverse.foldl (fun (v : Int) (t : Nat) => if sel = (t : Int) then br t else v) base

/-- `guard_conditions` over an integer marking: `m ≥ pre[p]` where `pre[p] > 0`, inhibited
places empty, read places marked. -/
def guardI (n : Nat) (t : Transition) (m : PlaceId → Int) : Prop :=
  (∀ p, p < n → 0 < pre t p → (pre t p : Int) ≤ m p) ∧
    (∀ p ∈ t.inhibitors, m p = 0) ∧ (∀ p ∈ t.reads, 1 ≤ m p)

/-- The integer marking at step `i`: the literal `M0` at step 0, the variable `m{i}_{p}` after,
and the initial count for a place past the net (which has no variable). -/
def mAt (n : Nat) (a0 : AMarking) (M : Nat → PlaceId → Int) (i : Nat) (p : PlaceId) : Int :=
  if i = 0 ∨ n ≤ p then (a0 p : Int) else M i p

/-- **The injection-free script `encode_bounded_run` emits at depth `d`** ([VER-019], no
injection: `J = 0`), as constraints over the selectors `s` and the marking variables `M` (P4).
With no injection the post-caps are empty. `BmcModelEnv` is the general script;
`bmcModelEnv_nil` shows the two agree at `J = 0`. -/
structure BmcModel (rows : List Row) (n : Nat) (a0 : AMarking)
    (badI : (PlaceId → Int) → Prop) (d : Nat) (s : Nat → Int) (M : Nat → PlaceId → Int) :
    Prop where
  /-- `(and (>= s_i 0) (<= s_i T))`. -/
  sel_range : ∀ i, i < d → 0 ≤ s i ∧ s i ≤ rows.length
  /-- `(=> (= s_i T) (= s_{i+1} T))`. -/
  idle_final : ∀ i, i + 1 < d → s i = rows.length → s (i + 1) = rows.length
  /-- `(=> (= s_i t) guard_t(m_i))` for every row `t`. -/
  guard : ∀ i, i < d → ∀ t (ht : t < rows.length), s i = t → guardI n rows[t].1 (mAt n a0 M i)
  /-- `(= m_{i+1,p} chain)` for every place of the net. -/
  update : ∀ i, i < d → ∀ p, p < n →
    mAt n a0 M (i + 1) p =
      chain (s i) (touching rows p) (nextVal rows (mAt n a0 M i p) p) (mAt n a0 M i p)
  /-- `(assert bad(m_d))`. -/
  bad : badI (mAt n a0 M d)

/-- The script is satisfiable. -/
def BmcSat (rows : List Row) (n : Nat) (a0 : AMarking) (badI : (PlaceId → Int) → Prop)
    (d : Nat) : Prop :=
  ∃ s M, BmcModel rows n a0 badI d s M

/-- P2: every place the row mentions is a place of the flat net. -/
structure RowIn (n : Nat) (tr : Row) : Prop where
  inputs : ∀ s ∈ tr.1.inputs, s.place < n
  resets : ∀ p ∈ tr.1.resets, p < n
  deposit : ∀ p ∈ tr.2, p < n
  inhibitors : ∀ p ∈ tr.1.inhibitors, p < n
  reads : ∀ p ∈ tr.1.reads, p < n

/-- The shape premises of this section: P1 and P2 on every row. -/
def WellFormedRows (n : Nat) (rows : List Row) : Prop :=
  ∀ tr ∈ rows, RowIn n tr ∧ InputsDistinctPlaces tr.1

/-- P5: the integer violation agrees with the natural one on every marking. -/
def BadAgrees (badI : (PlaceId → Int) → Prop) (bad : AMarking → Prop) : Prop :=
  ∀ a : AMarking, badI (fun p => (a p : Int)) ↔ bad a

/-! ## Environment injection steps ([VER-025]) -/

/-- An environment injection as `resolve_env_injection` gives it ([VER-006]): the injected
place's flat index and its bound, `none` when unbounded (`AlwaysAvailable`), `some k` under
`Bounded(k)`. The list is `J` long; injection `j` has selector `T + j`. In `bounded_run.rs` the
selectors number `injection_steps(env_inject)`, the list with an index past the net dropped; under
P2 (`InjsIn`) it drops nothing, so injection `j` is selector `T + j` in the script, the decode and
the replay alike. -/
abbrev Inj := PlaceId × Option Nat

/-- The injection guard (`injection_conditions`, the bounded-run line
`(=> (= s_i T+j) (< m_i_pid bound))`, and `abstract_replay::inject_a`'s refusal at
`m[pid] ≥ bound`, which `StepRelation::step` takes): always when unbounded, `m < k` under bound
`k`. `inject_a` also refuses a place past the marking, which P2 (`InjsIn`) rules out. -/
def injOk (j : Inj) (a : AMarking) : Bool :=
  match j.2 with
  | none => true
  | some k => decide (a j.1 < k)

/-- One token into `p`, every other place copied (`m'_p = m_p + 1`; `inject_a`'s
`next[pid] += 1`, and the bounded run's injection arm `(+ <current> 1)`). The same function as
`EnvSemantics.injA`. -/
def injAt (a : AMarking) (p : PlaceId) : AMarking := fun q => if q == p then a q + 1 else a q

/-- One post-cap: a bounded injection's place holds at most its bound. -/
def capOk (a : AMarking) (j : Inj) : Bool :=
  match j.2 with
  | none => true
  | some k => decide (a j.1 ≤ k)

/-- `within_env_bounds` over `environment_caps`: every bounded injection's place holds at most
its bound. Empty, so always true, without a bounded injection. -/
def capsOk (injs : List Inj) (a : AMarking) : Bool :=
  injs.all (capOk a)

/-- **One step by index, `StepRelation::step`** (`bounded_run.rs`; [VER-025] contract section 5),
the one place a step is taken: `replay_run` and the trim's `violating_prefix` (`trimStep`,
`Witness.lean`) both step through it. `StepRelation::of` resolves the post-caps
(`environment_caps`) and the injections (`injection_steps`) once. An index `t < T` fires row `t`
when it is enabled (`enabled_a`, `fire_a`) and its successor passes the post-caps
(`within_env_bounds`); an index `T + j` injects into injection `j`'s place when the guard allows
it (`inject_a`), with no post-cap check (the CHC injection rule has none); any other index
fails. -/
def stepIdx (rows : List Row) (injs : List Inj) (a : AMarking) (t : Nat) : Option AMarking :=
  match rows[t]? with
  | some tr =>
    if enabledA a tr.1 = true ∧ capsOk injs (fireAD a tr.1 tr.2) = true then
      some (fireAD a tr.1 tr.2)
    else none
  | none =>
    match injs[t - rows.length]? with
    | some j => if injOk j a = true then some (injAt a j.1) else none
    | none => none

/-- **`replay_run` without the final property check**: the steps named by index in order, each
taken by `StepRelation::step` (`stepIdx`), `none` at the first one it refuses. With no injection
it is `replay` (`replayEnv_nil`). -/
def replayEnv (rows : List Row) (injs : List Inj) : AMarking → List Nat → Option AMarking
  | a, [] => some a
  | a, t :: ts => (stepIdx rows injs a t).bind fun b => replayEnv rows injs b ts

/-- **The step relation of the open system the witness phase searches**: a row step whose
successor passes the post-caps, or an allowed injection. `stepEnv_injsOf` (`Witness.lean`)
shows it is `EnvSemantics.StepAE`, the unstrengthened CHC rules of `encode_net`, at the
injection list the verifier builds. -/
def StepEnv (rows : List Row) (injs : List Inj) (a a' : AMarking) : Prop :=
  (StepAD rows a a' ∧ capsOk injs a' = true) ∨ ∃ j ∈ injs, injOk j a = true ∧ a' = injAt a j.1

/-- Reachability under `StepEnv`. -/
def ReachEnv (rows : List Row) (injs : List Inj) (a0 : AMarking) : AMarking → Prop :=
  Relation.ReflTransGen (StepEnv rows injs) a0

/-- The injections into `p`, as selectors `T + j`, in injection order. -/
def injTouching (T : Nat) (injs : List Inj) (p : PlaceId) : List Nat :=
  ((List.range injs.length).filter fun j => decide ((injs[j]?.map Prod.fst) = some p)).map
    (T + ·)

/-- The touching selectors of `p` with injections (contract section 4, step 5): the touching
rows in net order, then `T + j` for each injection `j` into `p`. The Rust reverses the list
before nesting, as without injections. -/
def touchingEnv (rows : List Row) (injs : List Inj) (p : PlaceId) : List Nat :=
  touching rows p ++ injTouching rows.length injs p

/-- The arm of selector `t` at `p`: a row's arm (`nextVal`) for `t < T`, the injection arm
`(+ <current> 1)` (`shifted(current, 1)`) otherwise. -/
def nextValEnv (rows : List Row) (v : Int) (p : PlaceId) (t : Nat) : Int :=
  if t < rows.length then nextVal rows v p t else v + 1

/-- **The script `encode_bounded_run` emits at depth `d` with the injections `injs`**
([VER-025] contract section 4), as constraints over the selectors `s` and the marking variables
`M` (P4). Per step: the selector range `[0, T + J]`, idle (`T + J`) only at the end, the guard
of a selected row, the guard of a selected bounded injection, the `ite` chain of every place,
and the post-cap of every bounded injection on the next marking; the violation at the last
marking. The post-caps keep `environment_caps`' filter to places of the net. -/
structure BmcModelEnv (rows : List Row) (injs : List Inj) (n : Nat) (a0 : AMarking)
    (badI : (PlaceId → Int) → Prop) (d : Nat) (s : Nat → Int) (M : Nat → PlaceId → Int) :
    Prop where
  /-- `(and (>= s_i 0) (<= s_i T+J))`. -/
  sel_range : ∀ i, i < d → 0 ≤ s i ∧ s i ≤ ((rows.length + injs.length : Nat) : Int)
  /-- `(=> (= s_i T+J) (= s_{i+1} T+J))`. -/
  idle_final : ∀ i, i + 1 < d → s i = ((rows.length + injs.length : Nat) : Int) →
    s (i + 1) = ((rows.length + injs.length : Nat) : Int)
  /-- `(=> (= s_i t) guard_t(m_i))` for every row `t`. -/
  guard : ∀ i, i < d → ∀ t (ht : t < rows.length), s i = t → guardI n rows[t].1 (mAt n a0 M i)
  /-- `(=> (= s_i T+j) (< m_i_pid bound))` for every bounded injection `j`. -/
  inj_guard : ∀ i, i < d → ∀ j (hj : j < injs.length) k, injs[j].2 = some k →
    s i = ((rows.length + j : Nat) : Int) → mAt n a0 M i injs[j].1 < k
  /-- `(= m_{i+1,p} chain)` for every place of the net, over the rows and injections. -/
  update : ∀ i, i < d → ∀ p, p < n →
    mAt n a0 M (i + 1) p =
      chain (s i) (touchingEnv rows injs p) (nextValEnv rows (mAt n a0 M i p) p) (mAt n a0 M i p)
  /-- `(<= m_{i+1,pid} bound)` for every bounded injection into a place of the net. -/
  caps : ∀ i, i < d → ∀ j ∈ injs, ∀ k, j.2 = some k → j.1 < n → mAt n a0 M (i + 1) j.1 ≤ k
  /-- `(assert bad(m_d))`. -/
  bad : badI (mAt n a0 M d)

/-- The script with injections is satisfiable. -/
def BmcSatEnv (rows : List Row) (injs : List Inj) (n : Nat) (a0 : AMarking)
    (badI : (PlaceId → Int) → Prop) (d : Nat) : Prop :=
  ∃ s M, BmcModelEnv rows injs n a0 badI d s M

/-- P2 for injections: every injected place is a place of the flat net (`resolve_env_injection`
keeps only names the flat index has). -/
def InjsIn (n : Nat) (injs : List Inj) : Prop :=
  ∀ j ∈ injs, j.1 < n

/-- P9: no place is injected twice. `env_injection` iterates a set of place names and
`place_index` is injective, so the resolved places are distinct; `environment_caps` collects
the caps into a map keyed by place, which is the conjunction of every cap under this premise. -/
def InjsDistinct (injs : List Inj) : Prop :=
  (injs.map Prod.fst).Nodup

/-! ### The `ite` chain -/

theorem chain_cons (sel : Int) (t : Nat) (ts : List Nat) (br : Nat → Int) (base : Int) :
    chain sel (t :: ts) br base = if sel = (t : Int) then br t else chain sel ts br base := by
  unfold chain
  rw [List.foldl_reverse, List.foldl_reverse, List.foldr_cons]

/-- The selected row's arm, when it touches the place. -/
theorem chain_hit {sel : Int} {touch : List Nat} {br : Nat → Int} {base : Int} {t : Nat}
    (ht : t ∈ touch) (hs : sel = t) : chain sel touch br base = br t := by
  induction touch with
  | nil => exact absurd ht (by simp)
  | cons u us ih =>
    rw [chain_cons]
    by_cases hu : sel = (u : Int)
    · rw [if_pos hu]
      have : u = t := by rw [hs] at hu; exact_mod_cast hu.symm
      rw [this]
    · rw [if_neg hu]
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact absurd hs hu
      · exact ih ht'

/-- The previous value, when no touching row is selected. -/
theorem chain_miss {sel : Int} {touch : List Nat} {br : Nat → Int} {base : Int}
    (h : ∀ t ∈ touch, sel ≠ (t : Int)) : chain sel touch br base = base := by
  induction touch with
  | nil => rfl
  | cons u us ih =>
    rw [chain_cons, if_neg (h u List.mem_cons_self)]
    exact ih fun t ht => h t (List.mem_cons_of_mem u ht)

/-- Selectors past the list's end that are never selected do not change the chain. -/
theorem chain_append_miss {sel : Int} {xs ys : List Nat} {br : Nat → Int} {base : Int}
    (h : ∀ t ∈ ys, sel ≠ (t : Int)) : chain sel (xs ++ ys) br base = chain sel xs br base := by
  induction xs with
  | nil => exact chain_miss h
  | cons u us ih => rw [List.cons_append, chain_cons, chain_cons, ih]

/-- The chain reads the arms of its own selectors only. -/
theorem chain_congr {sel : Int} {touch : List Nat} {br br' : Nat → Int} {base : Int}
    (h : ∀ t ∈ touch, br t = br' t) : chain sel touch br base = chain sel touch br' base := by
  induction touch with
  | nil => rfl
  | cons u us ih =>
    rw [chain_cons, chain_cons, h u List.mem_cons_self,
      ih fun t ht => h t (List.mem_cons_of_mem u ht)]

theorem mem_touching {rows : List Row} {p : PlaceId} {t : Nat} :
    t ∈ touching rows p ↔ ∃ tr, rows[t]? = some tr ∧ touches tr p = true := by
  unfold touching
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hlt, hm⟩
    cases h : rows[t]? with
    | none => rw [h] at hm; exact absurd hm (by simp)
    | some tr => rw [h] at hm; exact ⟨tr, rfl, hm⟩
  · rintro ⟨tr, h, hm⟩
    exact ⟨(List.getElem?_eq_some_iff.mp h).1, by rw [h]; exact hm⟩

theorem touching_lt {rows : List Row} {p : PlaceId} {t : Nat} (ht : t ∈ touching rows p) :
    t < rows.length := by
  obtain ⟨tr, h, -⟩ := mem_touching.mp ht
  exact (List.getElem?_eq_some_iff.mp h).1

theorem mem_injTouching {T : Nat} {injs : List Inj} {p : PlaceId} {x : Nat} :
    x ∈ injTouching T injs p ↔
      ∃ j, j < injs.length ∧ (injs[j]?.map Prod.fst) = some p ∧ x = T + j := by
  unfold injTouching
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨j, ⟨hj, hp⟩, rfl⟩; exact ⟨j, hj, hp, rfl⟩
  · rintro ⟨j, hj, hp, rfl⟩; exact ⟨j, ⟨hj, hp⟩, rfl⟩

theorem touchingEnv_bounds {rows : List Row} {injs : List Inj} {p : PlaceId} {t : Nat}
    (ht : t ∈ touchingEnv rows injs p) : t < rows.length + injs.length := by
  rcases List.mem_append.mp ht with h | h
  · have := touching_lt h; omega
  · obtain ⟨j, hj, -, rfl⟩ := mem_injTouching.mp h; omega

/-- An idle step (`s_i = T`) leaves every place at its previous value. -/
theorem chain_idle (rows : List Row) (p : PlaceId) (br : Nat → Int) (base : Int) :
    chain (rows.length : Int) (touching rows p) br base = base := by
  apply chain_miss
  intro t ht heq
  have hlt := touching_lt ht
  have : rows.length = t := by exact_mod_cast heq
  omega

/-- An idle step with injections (`s_i = T + J`) leaves every place at its previous value. -/
theorem chain_idle_env (rows : List Row) (injs : List Inj) (p : PlaceId) (br : Nat → Int)
    (base : Int) :
    chain ((rows.length + injs.length : Nat) : Int) (touchingEnv rows injs p) br base = base := by
  apply chain_miss
  intro t ht heq
  have hlt := touchingEnv_bounds ht
  have : rows.length + injs.length = t := by exact_mod_cast heq
  omega

/-- **The chain computes `fireAD`**: with row `t` selected and enabled at `a`, each place's
chain over `a`'s count is the count `fireAD` leaves there. -/
theorem chain_step {rows : List Row} {t : Nat} {tr : Row} (ht : rows[t]? = some tr)
    {a : AMarking} (hen : enabledA a tr.1 = true) (p : PlaceId) :
    chain (t : Int) (touching rows p) (nextVal rows (a p : Int) p) (a p : Int) =
      ((fireAD a tr.1 tr.2 p : Nat) : Int) := by
  have hle : pre tr.1 p ≤ a p := pre_le_of_enabledA hen p
  by_cases hT : touches tr p = true
  · rw [chain_hit (mem_touching.mpr ⟨tr, ht, hT⟩) rfl]
    unfold nextVal fireAD
    rw [ht]
    simp only
    by_cases hR : tr.1.resets.contains p = true
    · have hc : clears tr p = true := by simp only [clears, hR, Bool.or_true]
      rw [if_pos hc, if_pos hR]
    · rw [if_neg hR]
      by_cases hCA : consumeAllAt tr.1 p = true
      · have hc : clears tr p = true := by simp only [clears, hCA, Bool.true_or]
        rw [if_pos hc, if_pos hCA]
      · have hc : ¬ clears tr p = true := by
          simp only [clears, Bool.or_eq_true, not_or]; exact ⟨hCA, hR⟩
        rw [if_neg hc, if_neg hCA]
        unfold column
        push_cast [hle]
        omega
  · rw [chain_miss]
    · have hc : clears tr p = false := by
        unfold touches at hT; simp only [Bool.or_eq_true, not_or] at hT
        simpa using hT.1
      have hcol : column tr p = 0 := by
        unfold touches at hT; simp only [Bool.or_eq_true, not_or, bne_iff_ne, ne_eq,
          Decidable.not_not] at hT
        exact hT.2
      unfold clears at hc
      simp only [Bool.or_eq_false_iff] at hc
      unfold fireAD
      rw [if_neg (by rw [hc.2]; exact Bool.false_ne_true),
        if_neg (by rw [hc.1]; exact Bool.false_ne_true)]
      unfold column at hcol
      push_cast [hle]
      omega
    · intro u hu heq
      have : u = t := by exact_mod_cast heq.symm
      subst this
      obtain ⟨tr', h', hT'⟩ := mem_touching.mp hu
      rw [ht] at h'
      cases h'
      exact hT hT'

/-- The chain with injections computes `fireAD` on a row step: no injection selector is the
row's, and the row arms are `nextVal`'s. -/
theorem chain_step_env {rows : List Row} {injs : List Inj} {t : Nat} {tr : Row}
    (ht : rows[t]? = some tr) {a : AMarking} (hen : enabledA a tr.1 = true) (p : PlaceId) :
    chain (t : Int) (touchingEnv rows injs p) (nextValEnv rows (a p : Int) p) (a p : Int) =
      ((fireAD a tr.1 tr.2 p : Nat) : Int) := by
  have htl : t < rows.length := (List.getElem?_eq_some_iff.mp ht).1
  unfold touchingEnv
  rw [chain_append_miss]
  · rw [chain_congr (br' := nextVal rows (a p : Int) p)]
    · exact chain_step ht hen p
    · intro u hu
      unfold nextValEnv
      rw [if_pos (touching_lt hu)]
  · intro u hu heq
    obtain ⟨j, -, -, rfl⟩ := mem_injTouching.mp hu
    have : t = rows.length + j := by exact_mod_cast heq
    omega

/-- **The chain computes an injection**: with injection `j` selected (`s = T + j`), the place it
injects into gains one token and every other place keeps its value. -/
theorem chain_inject_env {rows : List Row} {injs : List Inj} {j : Nat} {jj : Inj}
    (hj : injs[j]? = some jj) (p : PlaceId) (v : Int) :
    chain ((rows.length + j : Nat) : Int) (touchingEnv rows injs p) (nextValEnv rows v p) v =
      if p = jj.1 then v + 1 else v := by
  have hjl : j < injs.length := (List.getElem?_eq_some_iff.mp hj).1
  by_cases hp : p = jj.1
  · rw [if_pos hp]
    have hmem : rows.length + j ∈ touchingEnv rows injs p := by
      unfold touchingEnv
      refine List.mem_append_right _ (mem_injTouching.mpr ⟨j, hjl, ?_, rfl⟩)
      rw [hj, hp]; rfl
    rw [chain_hit hmem rfl]
    unfold nextValEnv
    rw [if_neg (by omega)]
  · rw [if_neg hp]
    apply chain_miss
    intro u hu heq
    have hu' : rows.length + j = u := by exact_mod_cast heq
    rcases List.mem_append.mp hu with h | h
    · have := touching_lt h; omega
    · obtain ⟨j', -, hp', rfl⟩ := mem_injTouching.mp h
      have : j = j' := by omega
      subst this
      rw [hj] at hp'
      exact hp (Option.some.inj hp').symm

/-! ### The guard is enablement -/

/-- **`guard_conditions` is `enabledA`** on a natural marking, under P1 and P2. The same
equivalence makes `enabled_a` (the replay's guard over the flat vectors) `enabledA` (P7). -/
theorem guardI_iff_enabledA {n : Nat} {tr : Row} (hin : RowIn n tr)
    (hd : InputsDistinctPlaces tr.1) (a : AMarking) :
    guardI n tr.1 (fun p => (a p : Int)) ↔ enabledA a tr.1 = true := by
  unfold guardI enabledA
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨hIn, hInh, hRd⟩
    refine ⟨⟨fun s hs => ?_, fun p hp => by exact_mod_cast hInh p hp⟩,
      fun p hp => by exact_mod_cast hRd p hp⟩
    have hpre : pre tr.1 s.place = s.card.required := by
      unfold pre; rw [hd s hs]
    by_cases h0 : s.card.required = 0
    · omega
    · have := hIn s.place (hin.inputs s hs) (by omega)
      rw [hpre] at this
      exact_mod_cast this
  · rintro ⟨⟨hIn, hInh⟩, hRd⟩
    have hen : enabledA a tr.1 = true := by
      unfold enabledA
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨hIn, hInh⟩, hRd⟩
    refine ⟨fun p _ _ => by exact_mod_cast pre_le_of_enabledA hen p,
      fun p hp => by exact_mod_cast hInh p hp, fun p hp => by exact_mod_cast hRd p hp⟩

/-! ### Places past the net -/

/-- A row leaves every place past the net where it was. -/
theorem fireAD_frame {n : Nat} {tr : Row} (hin : RowIn n tr) (a : AMarking) {p : PlaceId}
    (hp : n ≤ p) : fireAD a tr.1 tr.2 p = a p := by
  have hR : tr.1.resets.contains p = false := by
    cases h : tr.1.resets.contains p with
    | false => rfl
    | true =>
      exact absurd (Nat.lt_of_lt_of_le (hin.resets p (by simpa using h)) hp) (Nat.lt_irrefl _)
  have hspec : specAt tr.1 p = none := by
    cases h : specAt tr.1 p with
    | none => rfl
    | some s =>
      obtain ⟨hmem, hplace⟩ := specAt_sound h
      have hlt := hin.inputs s hmem
      rw [hplace] at hlt
      exact absurd (Nat.lt_of_lt_of_le hlt hp) (Nat.lt_irrefl _)
  have hCA : consumeAllAt tr.1 p = false := by unfold consumeAllAt; rw [hspec]
  have hpre : pre tr.1 p = 0 := by unfold pre; rw [hspec]
  have hcnt : tr.2.count p = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro hm
    exact absurd (Nat.lt_of_lt_of_le (hin.deposit p hm) hp) (Nat.lt_irrefl _)
  unfold fireAD
  rw [if_neg (by rw [hR]; exact Bool.false_ne_true), if_neg (by rw [hCA]; exact Bool.false_ne_true),
    hpre, hcnt]
  omega

/-- A replay leaves every place past the net where it was. -/
theorem replay_frame {n : Nat} {rows : List Row} (hWF : WellFormedRows n rows) :
    ∀ {a b : AMarking} {ts : List Nat}, replay rows a ts = some b → ∀ p, n ≤ p → b p = a p
  | a, b, [], h, p, _ => by simp only [replay, Option.some.injEq] at h; rw [h]
  | a, b, t :: ts, h, p, hp => by
    simp only [replay] at h
    cases ht : rows[t]? with
    | none => rw [ht] at h; exact absurd h (by simp)
    | some tr =>
      rw [ht] at h
      simp only at h
      split at h
      · rw [replay_frame hWF h p hp]
        exact fireAD_frame (hWF tr (List.mem_of_getElem? ht)).1 a hp
      · exact absurd h (by simp)

/-! ### `replay_run` with injection steps -/

/-- A step `stepIdx` accepts at a row index is that row's enabled firing, within the caps. -/
theorem stepIdx_row {rows : List Row} {injs : List Inj} {a b : AMarking} {t : Nat} {tr : Row}
    (ht : rows[t]? = some tr) (h : stepIdx rows injs a t = some b) :
    enabledA a tr.1 = true ∧ capsOk injs (fireAD a tr.1 tr.2) = true ∧
      b = fireAD a tr.1 tr.2 := by
  unfold stepIdx at h
  rw [ht] at h
  simp only at h
  split at h
  · rename_i hc; exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- A step `stepIdx` accepts at index `T + j` is injection `j`, allowed by its guard. -/
theorem stepIdx_inj {rows : List Row} {injs : List Inj} {a b : AMarking} {j : Nat} {jj : Inj}
    (hj : injs[j]? = some jj) (h : stepIdx rows injs a (rows.length + j) = some b) :
    injOk jj a = true ∧ b = injAt a jj.1 := by
  unfold stepIdx at h
  rw [List.getElem?_eq_none (by omega), Nat.add_sub_cancel_left, hj] at h
  simp only at h
  split at h
  · rename_i hc; exact ⟨hc, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- `stepIdx` accepts only indices in `[0, T + J)`. -/
theorem stepIdx_lt {rows : List Row} {injs : List Inj} {a b : AMarking} {t : Nat}
    (h : stepIdx rows injs a t = some b) : t < rows.length + injs.length := by
  unfold stepIdx at h
  cases ht : rows[t]? with
  | some tr => have := (List.getElem?_eq_some_iff.mp ht).1; omega
  | none =>
    rw [ht] at h
    simp only at h
    have hge : rows.length ≤ t := List.getElem?_eq_none_iff.mp ht
    cases hj : injs[t - rows.length]? with
    | none => rw [hj] at h; exact absurd h (by simp)
    | some jj =>
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega

/-- An accepted step is a `StepEnv` step. -/
theorem stepIdx_sound {rows : List Row} {injs : List Inj} {a b : AMarking} {t : Nat}
    (h : stepIdx rows injs a t = some b) : StepEnv rows injs a b := by
  cases ht : rows[t]? with
  | some tr =>
    obtain ⟨hen, hcap, rfl⟩ := stepIdx_row ht h
    exact Or.inl ⟨⟨tr, List.mem_of_getElem? ht, hen, rfl⟩, hcap⟩
  | none =>
    have hge : rows.length ≤ t := List.getElem?_eq_none_iff.mp ht
    obtain ⟨j, rfl⟩ : ∃ j, t = rows.length + j := ⟨t - rows.length, by omega⟩
    have hlt := stepIdx_lt h
    have hj : injs[j]? = some injs[j] := List.getElem?_eq_getElem (by omega)
    obtain ⟨hok, rfl⟩ := stepIdx_inj hj h
    exact Or.inr ⟨injs[j], List.getElem_mem (by omega), hok, rfl⟩

/-- Every `StepEnv` step is accepted at some index. -/
theorem stepEnv_stepIdx {rows : List Row} {injs : List Inj} {a b : AMarking}
    (h : StepEnv rows injs a b) : ∃ t, stepIdx rows injs a t = some b := by
  rcases h with ⟨⟨tr, hmem, hen, rfl⟩, hcap⟩ | ⟨jj, hmem, hok, rfl⟩
  · obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp hmem
    refine ⟨t, ?_⟩
    unfold stepIdx
    rw [ht]
    simp [hen, hcap]
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
    refine ⟨rows.length + j, ?_⟩
    unfold stepIdx
    rw [List.getElem?_eq_none (by omega), Nat.add_sub_cancel_left, hj]
    simp [hok]

theorem replayEnv_append (rows : List Row) (injs : List Inj) :
    ∀ (a : AMarking) (xs ys : List Nat),
      replayEnv rows injs a (xs ++ ys) =
        (replayEnv rows injs a xs).bind fun b => replayEnv rows injs b ys
  | a, [], ys => rfl
  | a, t :: xs, ys => by
    simp only [List.cons_append, replayEnv, Option.bind_assoc]
    congr 1
    funext b
    exact replayEnv_append rows injs b xs ys

theorem replayEnv_singleton (rows : List Row) (injs : List Inj) (a : AMarking) (t : Nat) :
    replayEnv rows injs a [t] = stepIdx rows injs a t := by
  simp only [replayEnv]
  cases stepIdx rows injs a t <;> rfl

/-- One step at the end of a replay. -/
theorem replayEnv_snoc {rows : List Row} {injs : List Inj} {a b c : AMarking} {ts : List Nat}
    {t : Nat} (h : replayEnv rows injs a ts = some b) (hs : stepIdx rows injs b t = some c) :
    replayEnv rows injs a (ts ++ [t]) = some c := by
  rw [replayEnv_append, h]
  simp only [Option.bind_some]
  rw [replayEnv_singleton, hs]

/-- **A replayed run is a run** of `StepEnv`. -/
@[evidence cites "VER-025" "a run the replay accepts, firings and injection steps by index, is a run of the step relation StepEnv: an enabled row whose successor passes the post-caps, or an injection while its guard holds; model of replay_run"]
theorem replayEnv_sound {rows : List Row} {injs : List Inj} :
    ∀ {a b : AMarking} {ts : List Nat}, replayEnv rows injs a ts = some b →
      ReachEnv rows injs a b
  | a, b, [], h => by
    simp only [replayEnv, Option.some.injEq] at h
    subst h; exact Relation.ReflTransGen.refl
  | a, b, t :: ts, h => by
    simp only [replayEnv] at h
    cases hs : stepIdx rows injs a t with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some c =>
      rw [hs] at h
      exact Relation.ReflTransGen.head (stepIdx_sound hs) (replayEnv_sound h)

/-- Every index a successful replay takes is a step index, `< T + J`. -/
theorem replayEnv_lt {rows : List Row} {injs : List Inj} :
    ∀ {a b : AMarking} {ts : List Nat}, replayEnv rows injs a ts = some b →
      ∀ t ∈ ts, t < rows.length + injs.length
  | _, _, [], _ => by simp
  | a, b, t :: ts, h => by
    simp only [replayEnv] at h
    cases hs : stepIdx rows injs a t with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some c =>
      rw [hs] at h
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact stepIdx_lt hs
      · exact replayEnv_lt h u hu

/-- **Every run of `StepEnv` is a replay** of some index list. -/
theorem reachEnv_replay {rows : List Row} {injs : List Inj} {a0 a : AMarking}
    (h : ReachEnv rows injs a0 a) : ∃ ts, replayEnv rows injs a0 ts = some a := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | tail _ hs ih =>
    obtain ⟨ts, hts⟩ := ih
    obtain ⟨t, ht⟩ := stepEnv_stepIdx hs
    exact ⟨ts ++ [t], replayEnv_snoc hts ht⟩

/-- **With no injection the replay is `replay`** ([VER-019]'s `replay_run`). -/
theorem replayEnv_nil (rows : List Row) : replayEnv rows [] = replay rows := by
  funext a ts
  induction ts generalizing a with
  | nil => rfl
  | cons t ts ih =>
    simp only [replayEnv, replay, stepIdx]
    cases rows[t]? with
    | none => rfl
    | some tr =>
      simp only [capsOk, List.all_nil, and_true]
      split
      · exact ih _
      · rfl

/-- A step leaves every place past the net where it was. -/
theorem stepIdx_frame {n : Nat} {rows : List Row} {injs : List Inj} (hWF : WellFormedRows n rows)
    (hIn : InjsIn n injs) {a b : AMarking} {t : Nat} (h : stepIdx rows injs a t = some b)
    {p : PlaceId} (hp : n ≤ p) : b p = a p := by
  rcases stepIdx_sound h with ⟨⟨tr, hmem, -, rfl⟩, -⟩ | ⟨jj, hmem, -, rfl⟩
  · exact fireAD_frame (hWF tr hmem).1 a hp
  · have hlt : jj.1 < n := hIn jj hmem
    have : p ≠ jj.1 := fun h => by
      rw [h] at hp; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hp)
    simp [injAt, this]

/-- A replay with injections leaves every place past the net where it was. -/
theorem replayEnv_frame {n : Nat} {rows : List Row} {injs : List Inj}
    (hWF : WellFormedRows n rows) (hIn : InjsIn n injs) :
    ∀ {a b : AMarking} {ts : List Nat}, replayEnv rows injs a ts = some b →
      ∀ p, n ≤ p → b p = a p
  | a, b, [], h, p, _ => by simp only [replayEnv, Option.some.injEq] at h; rw [h]
  | a, b, t :: ts, h, p, hp => by
    simp only [replayEnv] at h
    cases hs : stepIdx rows injs a t with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some c =>
      rw [hs] at h
      rw [replayEnv_frame hWF hIn h p hp]
      exact stepIdx_frame hWF hIn hs hp

/-- Under P9 every step keeps the post-caps: a row step checks them, and an allowed injection
raises its own place to at most its bound. -/
theorem stepIdx_caps {rows : List Row} {injs : List Inj} (hD : InjsDistinct injs)
    {a b : AMarking} {t : Nat} (hc : capsOk injs a = true) (h : stepIdx rows injs a t = some b) :
    capsOk injs b = true := by
  rcases stepIdx_sound h with ⟨-, hcap⟩ | ⟨jj, hmem, hok, rfl⟩
  · exact hcap
  · unfold capsOk at hc ⊢
    rw [List.all_eq_true] at hc ⊢
    intro jj' hmem'
    have hc' := hc jj' hmem'
    by_cases hp : jj'.1 = jj.1
    · have heq : jj' = jj := List.inj_on_of_nodup_map hD hmem' hmem hp
      subst heq
      unfold capOk injOk at *
      cases hk : jj'.2 with
      | none => rfl
      | some k =>
        rw [hk] at hok
        simp only [decide_eq_true_eq] at hok ⊢
        simp only [injAt, beq_self_eq_true, if_true]
        omega
    · unfold capOk at hc' ⊢
      have : injAt a jj.1 jj'.1 = a jj'.1 := by simp [injAt, hp]
      rw [this]
      exact hc'

/-! ### Decoding the selectors -/

/-- `index_below(T)`: a selector names a row iff it lies in `[0, T)`. With injections the
decode is called with `T + J` (contract section 5), so a selector in `[T, T + J)` decodes as an
injection step. -/
def decodeSel (T : Nat) (v : Int) : Option Nat :=
  if 0 ≤ v ∧ v < T then some v.toNat else none

/-- `map_while`. -/
def takeSome : List (Option Nat) → List Nat
  | [] => []
  | none :: _ => []
  | some x :: xs => x :: takeSome xs

/-- `decode_bounded_run` as written: the selectors of steps `0 … d−1`, read up to the first
idle one. Its `stepCount` is `T` without injection and `T + J` with them; the body does not
change. -/
def decodeRust (T : Nat) (s : Nat → Int) (d : Nat) : List Nat :=
  takeSome ((List.range d).map fun i => decodeSel T (s i))

/-- The same, one step at a time: step `i` is appended while every earlier step was a firing. -/
def decode (T : Nat) (s : Nat → Int) : Nat → List Nat
  | 0 => []
  | i + 1 =>
    if (decode T s i).length = i then
      match decodeSel T (s i) with
      | some t => decode T s i ++ [t]
      | none => decode T s i
    else decode T s i

theorem takeSome_length_le : ∀ xs : List (Option Nat), (takeSome xs).length ≤ xs.length
  | [] => le_refl _
  | none :: _ => Nat.zero_le _
  | some _ :: xs => by simp only [takeSome, List.length_cons]; have := takeSome_length_le xs; omega

theorem takeSome_snoc : ∀ (xs : List (Option Nat)) (x : Option Nat),
    takeSome (xs ++ [x]) =
      if (takeSome xs).length = xs.length then takeSome xs ++ x.toList else takeSome xs
  | [], none => rfl
  | [], some _ => rfl
  | none :: xs, x => by
    simp only [List.cons_append, takeSome, List.length_nil, List.length_cons]
    rw [if_neg (by omega)]
  | some y :: xs, x => by
    simp only [List.cons_append, takeSome, List.length_cons, Nat.add_right_cancel_iff]
    rw [takeSome_snoc xs x]
    split <;> simp

/-- **`decode_bounded_run` is `decode`.** -/
theorem decodeRust_eq_decode (T : Nat) (s : Nat → Int) : ∀ d, decodeRust T s d = decode T s d
  | 0 => rfl
  | d + 1 => by
    unfold decodeRust
    rw [List.range_succ, List.map_append, List.map_singleton, takeSome_snoc]
    have ih := decodeRust_eq_decode T s d
    unfold decodeRust at ih
    rw [ih, List.length_map, List.length_range, decode]
    split
    · cases decodeSel T (s d) <;> simp
    · rfl

theorem decode_length_le (T : Nat) (s : Nat → Int) : ∀ d, (decode T s d).length ≤ d
  | 0 => le_refl _
  | i + 1 => by
    have ih := decode_length_le T s i
    unfold decode
    split
    · split <;> simp <;> omega
    · omega

/-! ### Soundness of the encoding: a model is a replayable run -/

/-- **A model's decoded selectors replay** (with injection steps) to the marking of its last
step. -/
theorem bmcEnv_model_replays {rows : List Row} {injs : List Inj} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {d : Nat} {s : Nat → Int} {M : Nat → PlaceId → Int}
    (hWF : WellFormedRows n rows) (hIn : InjsIn n injs)
    (hm : BmcModelEnv rows injs n a0 badI d s M) :
    ∃ a, replayEnv rows injs a0 (decode (rows.length + injs.length) s d) = some a ∧
      ∀ p, mAt n a0 M d p = a p := by
  let TJ := rows.length + injs.length
  suffices h : ∀ i, i ≤ d → ∃ a, replayEnv rows injs a0 (decode TJ s i) = some a ∧
      (∀ p, mAt n a0 M i p = a p) ∧
      ((decode TJ s i).length = i ∨ (0 < i ∧ s (i - 1) = (TJ : Int))) by
    obtain ⟨a, h1, h2, -⟩ := h d (le_refl d)
    exact ⟨a, h1, h2⟩
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨a0, rfl, fun p => by simp [mAt], Or.inl rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨a, hrep, hmk, hlen⟩ := ih (by omega)
    have hid : i < d := by omega
    -- the frame: places past the net keep their initial count, in `mAt` and in `a`
    have hfr : ∀ p, n ≤ p → mAt n a0 M (i + 1) p = a p := by
      intro p hp
      have h1 : mAt n a0 M (i + 1) p = a0 p := by simp [mAt, hp]
      have h2 : mAt n a0 M i p = a0 p := by simp [mAt, hp]
      rw [h1, ← h2, hmk p]
    -- an idle step
    have idle : s i = (TJ : Int) → ∀ p, mAt n a0 M (i + 1) p = a p := by
      intro hs p
      by_cases hp : p < n
      · rw [hm.update i hid p hp, hs, chain_idle_env, hmk p]
      · exact hfr p (Nat.le_of_not_lt hp)
    have hmk' : mAt n a0 M i = fun p => (a p : Int) := funext hmk
    by_cases hL : (decode TJ s i).length = i
    · cases hsel : decodeSel TJ (s i) with
      | none =>
        have hs : s i = (TJ : Int) := by
          have hr := hm.sel_range i hid
          unfold decodeSel at hsel
          split at hsel
          · exact absurd hsel (by simp)
          · rename_i hn; omega
        refine ⟨a, ?_, idle hs, Or.inr ⟨by omega, by simpa using hs⟩⟩
        simp only [decode, hL, if_true, hsel]
        exact hrep
      | some t =>
        have hst : s i = t ∧ t < TJ := by
          unfold decodeSel at hsel
          split at hsel
          · rename_i hc
            have := Option.some.inj hsel
            subst this
            exact ⟨(Int.toNat_of_nonneg hc.1).symm, by omega⟩
          · exact absurd hsel (by simp)
        obtain ⟨hs, htl⟩ := hst
        have hdec : decode TJ s (i + 1) = decode TJ s i ++ [t] := by
          simp only [decode, hL, if_true, hsel]
        by_cases hT : t < rows.length
        · -- a row step
          have htr : rows[t]? = some rows[t] := List.getElem?_eq_getElem hT
          have hmem : rows[t] ∈ rows := List.getElem_mem hT
          have hg := hm.guard i hid t hT hs
          rw [hmk'] at hg
          have hen := (guardI_iff_enabledA (hWF _ hmem).1 (hWF _ hmem).2 a).mp hg
          have hnext : ∀ p, mAt n a0 M (i + 1) p = fireAD a rows[t].1 rows[t].2 p := by
            intro p
            by_cases hp : p < n
            · rw [hm.update i hid p hp, hs, hmk p]
              exact chain_step_env htr hen p
            · rw [hfr p (Nat.le_of_not_lt hp)]
              rw [fireAD_frame (hWF _ hmem).1 a (Nat.le_of_not_lt hp)]
          have hcap : capsOk injs (fireAD a rows[t].1 rows[t].2) = true := by
            unfold capsOk
            rw [List.all_eq_true]
            intro jj hjj
            unfold capOk
            cases hk : jj.2 with
            | none => rfl
            | some k =>
              have := hm.caps i hid jj hjj k hk (hIn jj hjj)
              rw [hnext] at this
              simp only [decide_eq_true_eq]
              exact_mod_cast this
          have hstep : stepIdx rows injs a t = some (fireAD a rows[t].1 rows[t].2) := by
            unfold stepIdx
            rw [htr]
            simp [hen, hcap]
          refine ⟨fireAD a rows[t].1 rows[t].2, ?_, hnext, Or.inl ?_⟩
          · rw [hdec]; exact replayEnv_snoc hrep hstep
          · rw [hdec, List.length_append, hL]; rfl
        · -- an injection step
          obtain ⟨j, rfl⟩ : ∃ j, t = rows.length + j := ⟨t - rows.length, by omega⟩
          have hjl : j < injs.length := by
            have : rows.length + j < rows.length + injs.length := htl
            omega
          have hj : injs[j]? = some injs[j] := List.getElem?_eq_getElem hjl
          have hok : injOk injs[j] a = true := by
            unfold injOk
            cases hk : injs[j].2 with
            | none => rfl
            | some k =>
              have := hm.inj_guard i hid j hjl k hk hs
              rw [hmk] at this
              simp only [decide_eq_true_eq]
              exact_mod_cast this
          have hstep : stepIdx rows injs a (rows.length + j) = some (injAt a injs[j].1) := by
            unfold stepIdx
            rw [List.getElem?_eq_none (by omega), Nat.add_sub_cancel_left, hj]
            simp [hok]
          have hnext : ∀ p, mAt n a0 M (i + 1) p = injAt a injs[j].1 p := by
            intro p
            by_cases hp : p < n
            · rw [hm.update i hid p hp, hs, chain_inject_env hj p, hmk p]
              unfold injAt
              by_cases hpj : p = injs[j].1
              · rw [if_pos hpj, if_pos (by simp [hpj])]; push_cast; rfl
              · rw [if_neg hpj, if_neg (by simp [hpj])]
            · rw [hfr p (Nat.le_of_not_lt hp)]
              have : p ≠ injs[j].1 := fun h => by
                have hlt : injs[j].1 < n := hIn injs[j] (List.getElem_mem hjl)
                rw [← h] at hlt; exact hp hlt
              simp [injAt, this]
          refine ⟨injAt a injs[j].1, ?_, hnext, Or.inl ?_⟩
          · rw [hdec]; exact replayEnv_snoc hrep hstep
          · rw [hdec, List.length_append, hL]; rfl
    · obtain ⟨hpos, hprev⟩ := hlen.resolve_left hL
      have hs : s i = (TJ : Int) := by
        have := hm.idle_final (i - 1) (by omega) hprev
        rwa [Nat.sub_add_cancel (by omega)] at this
      refine ⟨a, ?_, idle hs, Or.inr ⟨by omega, by simpa using hs⟩⟩
      simp only [decode, hL, if_false]
      exact hrep

/-! ### Completeness of the encoding: a run is a model -/

/-- The marking after the first `i` steps of a run with injections. -/
def stAtEnv (rows : List Row) (injs : List Inj) (a0 : AMarking) (ts : List Nat) (i : Nat) :
    AMarking :=
  (replayEnv rows injs a0 (ts.take i)).getD a0

theorem replayEnv_take {rows : List Row} {injs : List Inj} {a0 a : AMarking} {ts : List Nat}
    (h : replayEnv rows injs a0 ts = some a) (i : Nat) :
    replayEnv rows injs a0 (ts.take i) = some (stAtEnv rows injs a0 ts i) := by
  have hsplit := replayEnv_append rows injs a0 (ts.take i) (ts.drop i)
  rw [List.take_append_drop, h] at hsplit
  unfold stAtEnv
  cases hti : replayEnv rows injs a0 (ts.take i) with
  | none => rw [hti] at hsplit; exact absurd hsplit (by simp)
  | some b => rfl

/-- **A run of at most `d` steps (firings and injections) to a violating marking is a model of
the depth-`d` script**: its steps as selectors, idle after, and its markings as the variables.
The post-caps need P9 and a seed within the caps, which `bounded_premise_violation` checks
before any route ([VER-006] AC3, `EnvSemantics/Premise.lean`). -/
theorem bmcEnv_of_run {rows : List Row} {injs : List Inj} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} {d : Nat}
    (hWF : WellFormedRows n rows) (hIn : InjsIn n injs) (hD : InjsDistinct injs)
    (hBad : BadAgrees badI bad) (hcap0 : capsOk injs a0 = true)
    {ts : List Nat} {a : AMarking} (hlen : ts.length ≤ d)
    (hrep : replayEnv rows injs a0 ts = some a) (hbad : bad a) :
    BmcSatEnv rows injs n a0 badI d := by
  classical
  let T := rows.length
  let TJ := rows.length + injs.length
  let st := stAtEnv rows injs a0 ts
  let s : Nat → Int := fun i => if h : i < ts.length then (ts[i] : Int) else (TJ : Int)
  let M : Nat → PlaceId → Int := fun i p => (st i p : Int)
  have hlt := replayEnv_lt hrep
  have hst0 : st 0 = a0 := by simp [st, stAtEnv, replayEnv]
  have hmk : ∀ i p, mAt n a0 M i p = (st i p : Int) := by
    intro i p
    unfold mAt
    split
    · rename_i hc
      rcases hc with h0 | hp
      · subst h0; rw [hst0]
      · have := replayEnv_frame hWF hIn (replayEnv_take hrep i) p hp
        simp only [st]
        rw [this]
    · rfl
  have hmk' : ∀ i, mAt n a0 M i = fun p => (st i p : Int) := fun i => funext (hmk i)
  -- step `i < |ts|` takes `ts[i]` from `st i` to `st (i+1)`
  have hstep : ∀ i (hi : i < ts.length), stepIdx rows injs (st i) ts[i] = some (st (i + 1)) := by
    intro i hi
    have h1 := replayEnv_take hrep (i + 1)
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, replayEnv_append,
      replayEnv_take hrep i] at h1
    simp only [Option.bind_some] at h1
    rw [replayEnv_singleton] at h1
    exact h1
  have hidle : ∀ i, ts.length ≤ i → st (i + 1) = st i := by
    intro i hi
    simp only [st, stAtEnv]
    rw [List.take_of_length_le (by omega), List.take_of_length_le hi]
  have hcaps : ∀ i, capsOk injs (st i) = true := by
    intro i
    induction i with
    | zero => rw [hst0]; exact hcap0
    | succ i ih =>
      by_cases hi : i < ts.length
      · exact stepIdx_caps hD ih (hstep i hi)
      · rw [hidle i (by omega)]; exact ih
  have hsT : ∀ i, ts.length ≤ i → s i = (TJ : Int) := by
    intro i hi; simp only [s, dif_neg (show ¬ i < ts.length by omega)]
  have hsLt : ∀ i (hi : i < ts.length), s i = (ts[i] : Int) := by
    intro i hi; simp only [s, dif_pos hi]
  refine ⟨s, M, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- sel_range
    intro i _
    by_cases hi : i < ts.length
    · rw [hsLt i hi]
      have := hlt ts[i] (List.getElem_mem hi)
      constructor <;> omega
    · rw [hsT i (by omega)]; omega
  · -- idle_final
    intro i _ hs
    have hi : ts.length ≤ i := by
      by_contra hc
      rw [hsLt i (by omega)] at hs
      have := hlt ts[i] (List.getElem_mem (by omega))
      omega
    exact hsT (i + 1) (by omega)
  · -- guard
    intro i _ t ht hs
    have hi : i < ts.length := by
      by_contra hc
      rw [hsT i (by omega)] at hs
      omega
    rw [hsLt i hi] at hs
    have htt : ts[i] = t := by exact_mod_cast hs
    have h1 := hstep i hi
    rw [htt] at h1
    obtain ⟨hen, -, -⟩ := stepIdx_row (List.getElem?_eq_getElem ht) h1
    rw [hmk' i]
    have hmem : rows[t] ∈ rows := List.getElem_mem ht
    exact (guardI_iff_enabledA (hWF _ hmem).1 (hWF _ hmem).2 _).mpr hen
  · -- inj_guard
    intro i _ j hj k hk hs
    have hi : i < ts.length := by
      by_contra hc
      rw [hsT i (by omega)] at hs
      have : rows.length + injs.length = rows.length + j := by exact_mod_cast hs
      omega
    rw [hsLt i hi] at hs
    have htt : ts[i] = rows.length + j := by exact_mod_cast hs
    have h1 := hstep i hi
    rw [htt] at h1
    obtain ⟨hok, -⟩ := stepIdx_inj (List.getElem?_eq_getElem hj) h1
    unfold injOk at hok
    rw [hk] at hok
    simp only [decide_eq_true_eq] at hok
    rw [hmk i]
    exact_mod_cast hok
  · -- update
    intro i _ p _
    rw [hmk (i + 1) p, hmk i p]
    by_cases hi : i < ts.length
    · have h1 := hstep i hi
      rw [hsLt i hi]
      by_cases hT : ts[i] < rows.length
      · have htr : rows[ts[i]]? = some rows[ts[i]] := List.getElem?_eq_getElem hT
        obtain ⟨hen, -, hnext⟩ := stepIdx_row htr h1
        rw [hnext]
        exact (chain_step_env htr hen p).symm
      · obtain ⟨j, hj⟩ : ∃ j, ts[i] = rows.length + j := ⟨ts[i] - rows.length, by omega⟩
        have hjl : j < injs.length := by
          have := hlt ts[i] (List.getElem_mem hi); omega
        have hjj : injs[j]? = some injs[j] := List.getElem?_eq_getElem hjl
        rw [hj] at h1 ⊢
        obtain ⟨-, hnext⟩ := stepIdx_inj hjj h1
        rw [chain_inject_env hjj p, hnext]
        unfold injAt
        by_cases hpj : p = injs[j].1
        · rw [if_pos hpj, if_pos (by simp [hpj])]; push_cast; rfl
        · rw [if_neg hpj, if_neg (by simp [hpj])]
    · rw [hsT i (by omega), chain_idle_env, hidle i (by omega)]
  · -- caps
    intro i _ jj hjj k hk _
    rw [hmk (i + 1)]
    have := hcaps (i + 1)
    unfold capsOk at this
    rw [List.all_eq_true] at this
    have hc := this jj hjj
    unfold capOk at hc
    rw [hk] at hc
    simp only [decide_eq_true_eq] at hc
    exact_mod_cast hc
  · -- bad
    rw [hmk' d]
    have : st d = a := by
      have h1 := replayEnv_take hrep d
      rw [List.take_of_length_le hlen, hrep] at h1
      exact (Option.some.inj h1).symm
    rw [this]
    exact (hBad a).mpr hbad

/-! ### Exactness -/

/-- **`bmcEnv_complete`: the depth-`d` script with injections has a model iff some run of at most
`d` steps (firings and injections) reaches a violating marking.** The direction from a model to
a run needs P1, P2 only; the converse needs P9 and the capped seed as well. -/
@[evidence cites "VER-025" "exactness of the script with injection steps: the depth-d constraint system has a model iff some run of at most d firings and injections replays to a violating marking (P1, P2, P5, P9, seed within the caps; the SMT-LIB text is P4); backs the status line 'no run of at most D steps reaches a violation'"]
theorem bmcEnv_complete {rows : List Row} {injs : List Inj} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} (d : Nat)
    (hWF : WellFormedRows n rows) (hIn : InjsIn n injs) (hD : InjsDistinct injs)
    (hBad : BadAgrees badI bad) (hcap0 : capsOk injs a0 = true) :
    BmcSatEnv rows injs n a0 badI d ↔
      ∃ ts a, ts.length ≤ d ∧ replayEnv rows injs a0 ts = some a ∧ bad a := by
  constructor
  · rintro ⟨s, M, hm⟩
    obtain ⟨a, hrep, hmk⟩ := bmcEnv_model_replays hWF hIn hm
    refine ⟨_, a, decode_length_le _ s d, hrep, ?_⟩
    have := hm.bad
    rw [show mAt n a0 M d = fun p => (a p : Int) from funext hmk] at this
    exact (hBad a).mp this
  · rintro ⟨ts, a, hlen, hrep, hbad⟩
    exact bmcEnv_of_run hWF hIn hD hBad hcap0 hlen hrep hbad

/-- **The `sat` path with injections**: a model's decoded run (`decode_bounded_run` at
`stepCount = T + J`) replays under the exact semantics (`replay_run`) to a violating marking, so
a `sat` answer is never turned away by the replay. -/
@[evidence cites "VER-025" "a model of the depth-d script decodes, at stepCount T + J (selectors in [T, T + J) are injection steps), to a run that replays under the exact step relation to a violating marking: a truthful sat is never turned away by the replay"]
theorem bmcEnv_sat_replays {rows : List Row} {injs : List Inj} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} {d : Nat} {s : Nat → Int}
    {M : Nat → PlaceId → Int} (hWF : WellFormedRows n rows) (hIn : InjsIn n injs)
    (hBad : BadAgrees badI bad) (hm : BmcModelEnv rows injs n a0 badI d s M) :
    ∃ a, replayEnv rows injs a0 (decodeRust (rows.length + injs.length) s d) = some a ∧
      bad a := by
  obtain ⟨a, hrep, hmk⟩ := bmcEnv_model_replays hWF hIn hm
  refine ⟨a, by rw [decodeRust_eq_decode]; exact hrep, ?_⟩
  have := hm.bad
  rw [show mAt n a0 M d = fun p => (a p : Int) from funext hmk] at this
  exact (hBad a).mp this

/-! ### No injection: the [VER-019] script -/

/-- **At the empty injection list the script is the [VER-019] one**: the selector range, the idle
selector, the guards and the chains are `BmcModel`'s, and there is no injection guard or cap. -/
@[evidence cites "VER-025" "with J = 0 the constraint system of the witness script is the bounded run of VER-019 (constraint level; the byte identity of the text is the golden parity tests)"]
theorem bmcModelEnv_nil {rows : List Row} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {d : Nat} {s : Nat → Int} {M : Nat → PlaceId → Int} :
    BmcModelEnv rows [] n a0 badI d s M ↔ BmcModel rows n a0 badI d s M := by
  have hT : ∀ p, touchingEnv rows [] p = touching rows p := by
    intro p; simp [touchingEnv, injTouching]
  have hC : ∀ (sel : Int) (p : PlaceId) (v : Int),
      chain sel (touchingEnv rows [] p) (nextValEnv rows v p) v =
        chain sel (touching rows p) (nextVal rows v p) v := by
    intro sel p v
    rw [hT]
    apply chain_congr
    intro t ht
    unfold nextValEnv
    rw [if_pos (touching_lt ht)]
  constructor
  · intro hm
    refine ⟨fun i hi => ?_, fun i hi hs => ?_, hm.guard, fun i hi p hp => ?_, hm.bad⟩
    · simpa using hm.sel_range i hi
    · simpa using hm.idle_final i hi (by simpa using hs)
    · rw [hm.update i hi p hp, hC]
  · intro hm
    refine ⟨fun i hi => ?_, fun i hi hs => ?_, hm.guard, fun i _ j hj => ?_,
      fun i hi p hp => ?_, fun i _ jj hjj => ?_, hm.bad⟩
    · simpa using hm.sel_range i hi
    · simpa using hm.idle_final i hi (by simpa using hs)
    · exact absurd hj (by simp)
    · rw [hm.update i hi p hp, hC]
    · exact absurd hjj (by simp)

theorem bmcSatEnv_nil {rows : List Row} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {d : Nat} :
    BmcSatEnv rows [] n a0 badI d ↔ BmcSat rows n a0 badI d := by
  unfold BmcSatEnv BmcSat
  simp only [bmcModelEnv_nil]

theorem injsIn_nil (n : Nat) : InjsIn n [] := by simp [InjsIn]

theorem injsDistinct_nil : InjsDistinct [] := by simp [InjsDistinct]

/-- **A model's decoded selectors replay** to the marking of its last step. -/
theorem bmc_model_replays {rows : List Row} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {d : Nat} {s : Nat → Int} {M : Nat → PlaceId → Int}
    (hWF : WellFormedRows n rows) (hm : BmcModel rows n a0 badI d s M) :
    ∃ a, replay rows a0 (decode rows.length s d) = some a ∧ ∀ p, mAt n a0 M d p = a p := by
  have := bmcEnv_model_replays hWF (injsIn_nil n) (bmcModelEnv_nil.mpr hm)
  simpa [replayEnv_nil] using this

/-- **A run of at most `d` firings to a violating marking is a model of the depth-`d` script**:
its firings as selectors, idle after, and its markings as the variables. -/
theorem bmc_of_run {rows : List Row} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} {d : Nat}
    (hWF : WellFormedRows n rows) (hBad : BadAgrees badI bad)
    {ts : List Nat} {a : AMarking} (hlen : ts.length ≤ d) (hrep : replay rows a0 ts = some a)
    (hbad : bad a) : BmcSat rows n a0 badI d := by
  rw [← replayEnv_nil] at hrep
  exact bmcSatEnv_nil.mp
    (bmcEnv_of_run hWF (injsIn_nil n) injsDistinct_nil hBad rfl hlen hrep hbad)

/-- **`bmc_complete`: the depth-`d` script has a model iff some run of at most `d` firings
reaches a violating marking.** The `J = 0` case of `bmcEnv_complete`. -/
@[evidence cites "VER-019" "the depth-d bounded run has a model iff some run of at most d firings reaches a violating marking; proved as the J = 0 case of the VER-025 script with injection steps"]
theorem bmc_complete {rows : List Row} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} (d : Nat)
    (hWF : WellFormedRows n rows) (hBad : BadAgrees badI bad) :
    BmcSat rows n a0 badI d ↔
      ∃ ts a, ts.length ≤ d ∧ replay rows a0 ts = some a ∧ bad a := by
  rw [← bmcSatEnv_nil, bmcEnv_complete d hWF (injsIn_nil n) injsDistinct_nil hBad rfl,
    replayEnv_nil]

/-- **The `sat` path**: a model's decoded run (`decode_bounded_run`) replays under the exact
semantics (`replay_run`) to a violating marking, so a `sat` answer is never turned away by the
replay. -/
@[evidence cites "VER-019" "a model of the depth-d bounded run decodes to a run that replays under the exact semantics to a violating marking; the J = 0 case of the VER-025 decode"]
theorem bmc_sat_replays {rows : List Row} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} {d : Nat} {s : Nat → Int}
    {M : Nat → PlaceId → Int} (hWF : WellFormedRows n rows) (hBad : BadAgrees badI bad)
    (hm : BmcModel rows n a0 badI d s M) :
    ∃ a, replay rows a0 (decodeRust rows.length s d) = some a ∧ bad a := by
  have := bmcEnv_sat_replays hWF (injsIn_nil n) hBad (bmcModelEnv_nil.mpr hm)
  simpa [replayEnv_nil] using this

/-- **At the firing bound the script is exact for reachability**: with a ranking the check
accepts, `d ≥ K` has a model iff some `ReachAD`-reachable marking violates. -/
theorem bmc_exact_at_bound {rows : List Row} {n : Nat} {a0 : AMarking} {r : Weight} {K : Int}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} {d : Nat}
    (hWF : WellFormedRows n rows) (hBad : BadAgrees badI bad)
    (hK : checkRankingExact n rows a0 r = some K) (hd : K ≤ d) :
    BmcSat rows n a0 badI d ↔ ∃ a, ReachAD rows a0 a ∧ bad a := by
  obtain ⟨hr, rfl⟩ := checkRankingExact_sound hK
  rw [bmc_complete d hWF hBad]
  constructor
  · rintro ⟨ts, a, -, hrep, hbad⟩
    exact ⟨a, replay_sound hrep, hbad⟩
  · rintro ⟨a, hreach, hbad⟩
    obtain ⟨ts, hrep⟩ := reachAD_replay hreach
    have := ranking_bounds_length hr hrep
    exact ⟨ts, a, by omega, hrep, hbad⟩

end Libpetri.Novel.FiringBound
