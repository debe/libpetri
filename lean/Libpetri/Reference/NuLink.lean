import Libpetri.Reference.Nu
import Libpetri.Reference.Link
import Libpetri.Novel.RouteB.Sim
import Libpetri.Reference.NuMint

set_option linter.missingDocs true

/-!
# Bridge B1: a reference ν firing is a Route B executor step

`Novel/RouteB/Sim.lean` proves Route B sound against `NuStepC`, its own model of one untimed
executor ν firing (count effect, name effect, contracts). This module shows that the reference
ν firing `RefNuFire` (`Reference/Nu.lean`) is such a step, so the Route B results speak of the
reference executor ([NU-050] soundness, nu.md section 1.5).

* **Translation.** At `N := PlaceId`, `V := Colour`, `Nm := ℕ`, a ν transition becomes a Route B
  transition (`toNuTransB`): the structural core of `Link.toTransition`, the branch outcomes of
  its output spec as Route B rows (`outRows`), the keyed places of its match and its relay
  targets. A queue marking is read without stamps (`vals`).
* **Premises** (`B1Shape`, `NuProj`, `NuContract`).
  - Shape, true of every transition that builds and that the Route B classifier accepts as a join:
    the input places are distinct ([CORE-030] AC3), every correlated input takes a fixed count
    (`One` or `Exactly`, `FixedCard` of `Exec.lean`), and every correlated input is a coloured
    place.
  - `NuProj` is the projection premise (`ProjCoherent` of `Exec.lean`, read on the reference's
    per-key projections): every key and relay projection of the transition gives every token in
    its place the name `nameOf` gives it.
  - `NuContract` is the action contract of the role (`Exec.Contract`, read on the delivered and
    emitted tokens): a mint writes one fresh name to every coloured output; a consumer writes to a
    coloured output only a name it received from a coloured input.
* **Results.**
  - `refNuFire_names_step`: every reference ν firing of a transition of `X`, under the premises,
    is a `NuStepC` step of the translated net, with `conflict := false` (the priority pass is
    RefExec's, not the atomic step's).
  - The headline run forms, over contract-keeping runs (`RefNuRunB`: every firing's action keeps
    its role's contract, the spec's "while the declared mints and the coloured consumers keep
    their contracts"): `refNuRunB_names_reach` (such a run is a run of `NuStepC` steps) and
    `refNuRunB_routeB` (with `InFragment` of the translated net and an initial marking whose
    coloured places are empty, every marking such a run reaches has the key of a class the
    Route B exploration reaches, `exec_reach_simulated`). [NU-050]'s Route B block reads its runs
    this way.
  - The strong forms `refNuReach_names_reach` and `refNuReach_routeB` ask the contract of every
    firing the reference offers from a reachable marking. The reference leaves the emitted values
    free, so a mint that can fire twice has a firing that writes a stale name, and their premise
    fails on every such net: they are kept as the stronger, nearly vacuous variant.
  - `nuContract_mint_iff`: the mint contract here is `MintContract` of `Reference/NuMint.lean`,
    the contract [NU-010] justifies (ruling D78 (a)).

A correlated input with an `All` or `AtLeast` arc is outside the bridge: the reference takes every
token of the chosen name there, `NuStepC`'s count effect takes the whole place (Route B accepts only
`One` and `Exactly` keys, so its soundness theorems never meet the case).
-/

namespace Libpetri.Reference.NuLink

open Libpetri Libpetri.Spec Libpetri.Reference Libpetri.Reference.Link
open Libpetri.Novel.Seam Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.RouteB (Role nameLayer cnt idx isKey keyReq Selectable SpecTakes rmvList
  ExecNames Contract NuStepC)

/-! ## Translation -/

/-- A queue marking without the stamps: the coloured marking Route B's executor model reads. -/
def vals (M : QMarking PlaceId (Stamped Colour)) : CMarking := fun p => (M p).map Stamped.val

/-- Whether the input arc on `p` drains (`All` / `AtLeast`); `false` without an arc. -/
def drainsAt (t : NTransition PlaceId) (p : PlaceId) : Bool :=
  match nspecAt t p with
  | some s => s.card.consumesAll
  | none => false

/-- The fixed count the input arc on `p` takes (its required count); `0` without an arc. -/
def fixedAt (t : NTransition PlaceId) (p : PlaceId) : Nat :=
  match nspecAt t p with
  | some s => s.card.required
  | none => 0

/-- The row of a timeout `forward src dst`: a drained forward when the arc on `src` drains, else
`dst` once per token the arc takes (`fixedRows` puts fixed forwards in the fixed part). -/
def fwdRow (t : NTransition PlaceId) (src dst : PlaceId) : Novel.RouteB.Row :=
  if drainsAt t src then { fixed := [], drains := [(dst, src)] }
  else { fixed := List.replicate (fixedAt t src) dst }

/-- Two rows deposited together (an `And` node). -/
def rowCross (a b : Novel.RouteB.Row) : Novel.RouteB.Row :=
  { fixed := a.fixed ++ b.fixed, drains := a.drains ++ b.drains }

/-- The rows of a timeout child, clause for clause `Out.timeoutDeposits`. -/
def tRows (t : NTransition PlaceId) : Out PlaceId → List Novel.RouteB.Row
  | .place p => [{ fixed := [p] }]
  | .forward src dst => [fwdRow t src dst]
  | .and l r => (tRows t l).flatMap fun x => (tRows t r).map (rowCross x)
  | .xor l r => tRows t l ++ tRows t r
  | .timeout c => tRows t c

/-- The branch outcomes of a transition as Route B rows (`expand_transition`): one row per action
branch, then the rows of the timeout child; one empty row without an output spec. -/
def outRows (t : Trans PlaceId) : List Novel.RouteB.Row :=
  match t.out with
  | none => [{ fixed := [] }]
  | some o =>
    o.branches.map (fun b => { fixed := b }) ++ ((o.findTimeout.map (tRows t.core)).getD [])

/-- **A ν transition as Route B reads it**: the structural core, the rows of its output spec, the
keyed places of its match (`none` without a match) and its relay targets. -/
def toNuTransB (t : NuTrans PlaceId (KeyFn Colour ℕ)) : Novel.RouteB.NuTrans where
  base := toTransition t.base.core
  rows := outRows t.base
  keys := t.mspec.map MatchSpec.keyPlaces
  relays := (t.mspec.map MatchSpec.relayPlaces).getD []

/-! ## Premises -/

/-- The match of a transition, the empty one without a match: no key, no relay. -/
def msOf (t : NuTrans PlaceId (KeyFn Colour ℕ)) : MatchSpec PlaceId (KeyFn Colour ℕ) :=
  t.mspec.getD { keys := [] }

/-- **The shape B1 needs**, true of a built transition the Route B classifier accepts: distinct
input places ([CORE-030] AC3), every correlated input with a fixed count (`One` / `Exactly`), and
every correlated input a coloured place of `co`. -/
structure B1Shape (co : List PlaceId) (t : NuTrans PlaceId (KeyFn Colour ℕ)) : Prop where
  /-- At most one input arc per place. -/
  distinct : Spec.InputsDistinct t.base
  /-- No correlated input drains. -/
  keysFixed : ∀ p ∈ (msOf t).keyPlaces, drainsAt t.base.core p = false
  /-- Every correlated input is coloured. -/
  keysColoured : ∀ p ∈ (msOf t).keyPlaces, p ∈ co

/-- **The projection premise** at a marking (`Exec.ProjCoherent`, per key): every key and relay
projection of the match gives each token of its place the name `nameOf` gives it. -/
def NuProj (nameOf : Colour → ℕ) (t : NuTrans PlaceId (KeyFn Colour ℕ))
    (M : QMarking PlaceId (Stamped Colour)) : Prop :=
  ∀ k ∈ (msOf t).keys ++ (msOf t).relays, ∀ x ∈ M k.1, k.2 x.val = some (nameOf x.val)

/-- **The action contract of a role** (`Exec.Contract`), on what the firing delivered (`δ`) and
emitted (`e`): a mint writes one name to every coloured output, a name no coloured place of `M`
holds; a consumer writes to a coloured output only the name of a token it received from a
coloured input. Joins and ordinary transitions carry no contract. -/
def NuContract (co : List PlaceId) (nameOf : Colour → ℕ) (r : Role)
    (t : NuTrans PlaceId (KeyFn Colour ℕ)) (M : QMarking PlaceId (Stamped Colour))
    (δ : QDelivered PlaceId (Stamped Colour)) (e : List (PlaceId × Stamped Colour)) : Prop :=
  match r with
  | .mint => ∃ f, (∀ p ∈ co, ∀ x ∈ M p, nameOf x.val ≠ f) ∧ ∀ x ∈ e, x.1 ∈ co → nameOf x.2.val = f
  | .consume _ => ∀ x ∈ e, x.1 ∈ co → ∃ s ∈ t.base.core.inputs, s.place ∈ co ∧
      ∃ y ∈ δ.inputs s.place, nameOf y.val = nameOf x.2.val
  | .ordinary => True
  | .join _ _ => True

/-! ## The rows: every offered deposit is a row's resolved deposit -/

section Rows

/-- A row deposited with another resolves to the two resolved deposits, up to order. -/
theorem resolve_rowCross (k : PlaceId → ℕ) (a b : Novel.RouteB.Row) :
    ((rowCross a b).resolve k).Perm (a.resolve k ++ b.resolve k) := by
  refine List.perm_iff_count.2 fun x => ?_
  simp only [Novel.RouteB.Row.resolve, rowCross, List.flatMap_append, List.count_append]
  omega

/-- On a place whose arc does not drain, the reference's consumed count is the fixed count. -/
theorem nconsumed_of_not_drains {t : NTransition PlaceId} {p : PlaceId} (m : PlaceId → ℕ)
    (h : drainsAt t p = false) : nconsumed m t p = fixedAt t p := by
  unfold nconsumed fixedAt
  unfold drainsAt at h
  cases hs : nspecAt t p with
  | none => rfl
  | some s => rw [hs] at h; simp [h]

/-- Every deposit a timeout child offers is, up to order, the resolved deposit of one of its
rows, resolved at the counts the firing consumed. -/
theorem tRows_perm (t : NTransition PlaceId) (m : PlaceId → ℕ) : ∀ (c : Out PlaceId),
    ∀ d ∈ c.timeoutDeposits (nconsumed m t), ∃ r ∈ tRows t c, (r.resolve (nconsumed m t)).Perm d
  | .place p => by
    intro d hd
    simp only [Out.timeoutDeposits, List.mem_singleton] at hd
    subst hd
    exact ⟨_, List.mem_singleton_self _, by simp [Novel.RouteB.Row.resolve]⟩
  | .forward src dst => by
    intro d hd
    simp only [Out.timeoutDeposits, List.mem_singleton] at hd
    subst hd
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    unfold fwdRow
    cases h : drainsAt t src
    · simp [Novel.RouteB.Row.resolve, nconsumed_of_not_drains m h]
    · simp [Novel.RouteB.Row.resolve]
  | .and l r => by
    intro d hd
    simp only [Out.timeoutDeposits, cross, List.mem_flatMap, List.mem_map] at hd
    obtain ⟨x, hx, y, hy, rfl⟩ := hd
    obtain ⟨rx, hrx, px⟩ := tRows_perm t m l x hx
    obtain ⟨ry, hry, py⟩ := tRows_perm t m r y hy
    refine ⟨rowCross rx ry, ?_, (resolve_rowCross _ rx ry).trans (px.append py)⟩
    simp only [tRows, List.mem_flatMap, List.mem_map]
    exact ⟨rx, hrx, ry, hry, rfl⟩
  | .xor l r => by
    intro d hd
    simp only [Out.timeoutDeposits, List.mem_append] at hd
    rcases hd with hd | hd
    · obtain ⟨x, hx, px⟩ := tRows_perm t m l d hd
      exact ⟨x, by simp [tRows, hx], px⟩
    · obtain ⟨x, hx, px⟩ := tRows_perm t m r d hd
      exact ⟨x, by simp [tRows, hx], px⟩
  | .timeout c => by
    intro d hd
    exact tRows_perm t m c d hd

/-- **Every offered deposit is a row**: a deposit the output spec offers at the consumed counts
is, up to order, the resolved deposit of one of the transition's Route B rows. -/
theorem deposit_mem_outRows (t : Trans PlaceId) (m : PlaceId → ℕ) {ch : Choice}
    {d : List PlaceId} (h : deposit (nconsumed m t.core) t.out ch = some d) :
    ∃ r ∈ outRows t, (r.resolve (nconsumed m t.core)).Perm d := by
  unfold outRows
  cases ho : t.out with
  | none =>
    rw [ho] at h
    cases ch with
    | action i =>
      cases i with
      | zero =>
        simp only [deposit, Option.some.injEq] at h
        subst h
        exact ⟨_, List.mem_singleton_self _, by simp [Novel.RouteB.Row.resolve]⟩
      | succ i => simp [deposit] at h
    | timedOut j => simp [deposit] at h
  | some o =>
    rw [ho] at h
    cases ch with
    | action i =>
      simp only [deposit] at h
      refine ⟨{ fixed := d }, List.mem_append_left _ (List.mem_map.2 ⟨d,
        List.mem_of_getElem? h, rfl⟩), by simp [Novel.RouteB.Row.resolve]⟩
    | timedOut j =>
      simp only [deposit] at h
      cases hc : o.findTimeout with
      | none => rw [hc] at h; cases h
      | some c =>
        rw [hc] at h
        simp only [Option.bind_some] at h
        obtain ⟨r, hr, pr⟩ := tRows_perm t.core m c d (List.mem_of_getElem? h)
        exact ⟨r, List.mem_append_right _ (by simpa [hc] using hr), pr⟩

end Rows

/-! ## Names, places and queues -/

section Names

/-- The names of a list of tokens under `nameOf`, in order. -/
def nm (nameOf : Colour → ℕ) (l : List (Stamped Colour)) : List ℕ := l.map fun x => nameOf x.val

variable {nameOf : Colour → ℕ}

theorem nm_append (l l' : List (Stamped Colour)) :
    nm nameOf (l ++ l') = nm nameOf l ++ nm nameOf l' :=
  List.map_append

/-- Route B's name layer of the stamp-free marking counts the names of the queue. -/
theorem nameLayer_vals (co : List PlaceId) (M : QMarking PlaceId (Stamped Colour)) (u : ℕ)
    (i : Fin co.length) : nameLayer co nameOf (vals M) u i = (nm nameOf (M co[i.1])).count u := by
  simp only [nameLayer, vals, nm, List.count_eq_length_filter, List.filter_map, List.length_map]
  rfl

theorem idx_of_mem {co : List PlaceId} {p : PlaceId} (h : p ∈ co) :
    ∃ i, idx co p = some i := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  refine Option.isSome_iff_exists.1 ?_
  unfold idx
  rw [List.find?_isSome]
  exact ⟨⟨j, hj⟩, List.mem_finRange _, by simp⟩

theorem idx_of_not_mem {co : List PlaceId} {p : PlaceId} (h : p ∉ co) : idx co p = none := by
  unfold idx
  rw [List.find?_eq_none]
  intro i _ he
  exact h (by simpa using (beq_iff_eq.1 he) ▸ List.getElem_mem i.isLt)

/-- On a coloured place, Route B's per-place name count is the count of the name in the queue. -/
theorem cnt_vals_mem {co : List PlaceId} {p : PlaceId} (h : p ∈ co)
    (M : QMarking PlaceId (Stamped Colour)) (u : ℕ) :
    cnt co (nameLayer co nameOf (vals M)) u p = (nm nameOf (M p)).count u := by
  obtain ⟨i, hi⟩ := idx_of_mem h
  unfold cnt
  simp only [hi]
  rw [nameLayer_vals, Novel.RouteB.get_of_idx hi]

theorem cnt_vals_not_mem {co : List PlaceId} {p : PlaceId} (h : p ∉ co)
    (M : QMarking PlaceId (Stamped Colour)) (u : ℕ) :
    cnt co (nameLayer co nameOf (vals M)) u p = 0 := by
  unfold cnt; rw [idx_of_not_mem h]

/-- Taking the first `k` tokens of a name and keeping the rest loses no token. -/
theorem take_dropNamed_perm (f : KeyFn Colour ℕ) (n : ℕ) : ∀ (k : ℕ) (l : List (Stamped Colour)),
    ((named f n l).take k ++ dropNamed f n k l).Perm l
  | 0, l => by simp [dropNamed]
  | _ + 1, [] => by simp [dropNamed, named]
  | k + 1, x :: xs => by
    by_cases h : f x.val = some n
    · have ih := take_dropNamed_perm f n k xs
      simp only [named] at ih ⊢
      simp only [dropNamed, h, if_true, List.filter_cons, decide_true, List.take_succ_cons,
        List.cons_append]
      exact ih.cons x
    · have ih := take_dropNamed_perm f n (k + 1) xs
      simp only [named] at ih ⊢
      simp only [dropNamed, h, if_false, List.filter_cons, decide_false]
      simp only [Bool.false_eq_true, if_false]
      exact List.perm_middle.trans (ih.cons x)

/-- Under the projection premise, the tokens of a name are the tokens `nameOf` names so. -/
theorem named_eq_filter {f : KeyFn Colour ℕ} {l : List (Stamped Colour)}
    (h : ∀ x ∈ l, f x.val = some (nameOf x.val)) (n : ℕ) :
    named f n l = l.filter fun x => decide (nameOf x.val = n) := by
  unfold named
  refine List.filter_congr fun x hx => ?_
  rw [h x hx]; simp

theorem named_length_eq_count {f : KeyFn Colour ℕ} {l : List (Stamped Colour)}
    (h : ∀ x ∈ l, f x.val = some (nameOf x.val)) (n : ℕ) :
    (named f n l).length = (nm nameOf l).count n := by
  rw [named_eq_filter h, nm, List.count_eq_length_filter, List.filter_map, List.length_map]
  congr 1

theorem name_of_mem_named {f : KeyFn Colour ℕ} {l : List (Stamped Colour)}
    (h : ∀ x ∈ l, f x.val = some (nameOf x.val)) {n : ℕ} {x : Stamped Colour}
    (hx : x ∈ named f n l) : nameOf x.val = n := by
  rw [named_eq_filter h] at hx
  simpa using (List.mem_filter.1 hx).2

/-- The selection input's stamps of a name on a correlated input are one per token of the name. -/
theorem stamps_length (f : KeyFn Colour ℕ) (n : ℕ) : ∀ l : List (Stamped Colour),
    (stamps (l.filterMap fun x => (f x.val).map fun n' => (n', x.stamp)) n).length =
      (named f n l).length
  | [] => rfl
  | x :: xs => by
    have ih := stamps_length f n xs
    unfold stamps named at ih ⊢
    cases h : f x.val with
    | none => simp [h, ih]
    | some m =>
      by_cases hm : m = n
      · subst hm; simp [h, ih]
      · simp [h, hm, ih]

end Names

section Keys
variable {K : Type}

theorem keyAt_some {ms : MatchSpec PlaceId K} {p : PlaceId} {f : K} (h : keyAt ms p = some f) :
    (p, f) ∈ ms.keys := by
  unfold keyAt at h
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h
  have := List.find?_some hk
  have hp : k.1 = p := by simpa using this
  rw [← hp]
  exact List.mem_of_find?_eq_some hk

theorem keyAt_none_iff {ms : MatchSpec PlaceId K} {p : PlaceId} :
    keyAt ms p = none ↔ p ∉ ms.keyPlaces := by
  unfold keyAt MatchSpec.keyPlaces
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  simp only [decide_eq_true_eq, List.mem_map, not_exists, not_and, Prod.forall]

end Keys

/-! ## The firing, place by place -/

section Fire

variable {nameOf : Colour → ℕ} {t : NuTrans PlaceId (KeyFn Colour ℕ)}
  {M : QMarking PlaceId (Stamped Colour)} {n : ℕ}

theorem qCount_eq_alpha (M : QMarking PlaceId (Stamped Colour)) : qCount M = alpha (vals M) := by
  funext p; simp [qCount, alpha, vals]

/-- With distinct input places, the arc on the place of an input arc is that arc. -/
theorem nspecAt_of_mem {tc : NTransition PlaceId} (hd : (tc.inputs.map (·.place)).Nodup) :
    ∀ {s}, s ∈ tc.inputs → nspecAt tc s.place = some s := by
  intro s hs
  unfold nspecAt
  obtain ⟨tc_name, ins, inh, rds, rst⟩ := tc
  simp only at hd hs ⊢
  induction ins with
  | nil => cases hs
  | cons a rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hd
    rcases List.mem_cons.1 hs with rfl | hs'
    · simp
    · have hne : a.place ≠ s.place := fun he => hd.1 ⟨s, hs', he.symm⟩
      simp only [List.find?_cons, hne, decide_false]
      exact ih hd.2 hs'

/-- An input arc's required count is at most its place's count at an enabled marking. -/
theorem required_le_of_enabled {tc : NTransition PlaceId} {m : PlaceId → ℕ}
    (hen : enabledNA m tc = true) {s : NInSpec PlaceId} (hs : s ∈ tc.inputs) :
    s.card.required ≤ m s.place := by
  unfold enabledNA at hen
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hen
  exact hen.1.1 s hs

/-- With every correlated input fixed, the correlated takes are the reference's consumed counts. -/
theorem corrTake_eq (hfix : ∀ p ∈ (msOf t).keyPlaces, drainsAt t.base.core p = false) :
    corrTake (msOf t) t M n = nconsumed (alpha (vals M)) t.base.core := by
  funext p
  unfold corrTake
  cases hk : keyAt (msOf t) p with
  | none => simp [qTake, qCount_eq_alpha]
  | some f =>
    have hp : p ∈ (msOf t).keyPlaces := by
      by_contra h; rw [keyAt_none_iff.2 h] at hk; cases hk
    have hd := hfix p hp
    unfold drainsAt at hd
    simp only [nconsumed]
    cases hs : nspecAt t.base.core p with
    | none => rfl
    | some s => rw [hs] at hd; simp [consumptionCount, hd]

/-- Delivered and kept tokens of a place together are the place's tokens. -/
theorem nuInputs_append_nuPost (ms : MatchSpec PlaceId (KeyFn Colour ℕ)) (p : PlaceId) :
    (nuInputs ms t M n p ++ nuPost ms t M n p).Perm (M p) := by
  unfold nuInputs nuPost
  cases keyAt ms p with
  | some f => exact take_dropNamed_perm f n _ _
  | none => exact List.Perm.of_eq (qInputs_append_qPostInput M t.base p)

/-- Every correlated input holds at least its required count of tokens of the name: what an
eligible name gives the firing. -/
def Elig (t : NuTrans PlaceId (KeyFn Colour ℕ)) (M : QMarking PlaceId (Stamped Colour)) (n : ℕ) :
    Prop :=
  ∀ k ∈ (msOf t).keys, reqAt t.base k.1 ≤ (named k.2 n (M k.1)).length

/-- The required count of the arc on the place of an input arc is that arc's. -/
theorem reqAt_of_nspecAt {p : PlaceId} {s : NInSpec PlaceId} (hs : nspecAt t.base.core p = some s) :
    reqAt t.base p = s.card.required := by
  unfold reqAt; rw [hs]

/-- **The firing takes from each place what the reference count firing consumes.** -/
theorem nuInputs_length (hfix : ∀ p ∈ (msOf t).keyPlaces, drainsAt t.base.core p = false)
    (hen : enabledNA (qCount M) t.base.core = true) (hel : Elig t M n) (p : PlaceId) :
    (nuInputs (msOf t) t M n p).length = nconsumed (alpha (vals M)) t.base.core p := by
  have hc := congrFun (corrTake_eq (M := M) (n := n) hfix) p
  unfold nuInputs
  cases hk : keyAt (msOf t) p with
  | some f =>
    simp only [List.length_take]
    rw [hc]
    apply min_eq_left
    have hp : p ∈ (msOf t).keyPlaces := by
      by_contra h; rw [keyAt_none_iff.2 h] at hk; cases hk
    have hd := hfix p hp
    unfold drainsAt at hd
    unfold nconsumed
    cases hs : nspecAt t.base.core p with
    | none => exact Nat.zero_le _
    | some s =>
      rw [hs] at hd
      simp only [hd, Bool.false_eq_true, if_false]
      have := hel (p, f) (keyAt_some hk)
      rwa [reqAt_of_nspecAt hs] at this
  | none =>
    simp only [qInputs, List.length_take, qTake]
    rw [qCount_eq_alpha]
    apply min_eq_left
    unfold nconsumed
    cases hs : nspecAt t.base.core p with
    | none => exact Nat.zero_le _
    | some s =>
      have hsp := nspecAt_place hs
      by_cases hc : s.card.consumesAll = true
      · simp [hc, alpha, vals]
      · have := required_le_of_enabled hen hsp.1
        rw [hsp.2] at this
        simpa [hc, qCount, alpha, vals] using this

/-- A place without an input arc gives the action nothing. -/
theorem nuInputs_of_none {p : PlaceId} (h : nspecAt t.base.core p = none) :
    nuInputs (msOf t) t M n p = [] := by
  unfold nuInputs corrTake
  cases keyAt (msOf t) p <;> simp [h, qInputs, qTake, nconsumed]

/-- Kept tokens of a name: the tokens of the name minus the delivered ones. -/
theorem count_nuPost (ms : MatchSpec PlaceId (KeyFn Colour ℕ)) (p : PlaceId) (u : ℕ) :
    (nm nameOf (nuPost ms t M n p)).count u =
      (nm nameOf (M p)).count u - (nm nameOf (nuInputs ms t M n p)).count u := by
  have h := ((nuInputs_append_nuPost (t := t) (M := M) (n := n) ms p).map
    (fun x : Stamped Colour => nameOf x.val)).count_eq u
  simp only [List.map_append, List.count_append] at h
  simp only [nm]
  omega

theorem count_nuInputs_le (ms : MatchSpec PlaceId (KeyFn Colour ℕ)) (p : PlaceId) (u : ℕ) :
    (nm nameOf (nuInputs ms t M n p)).count u ≤ (nm nameOf (M p)).count u := by
  have h := ((nuInputs_append_nuPost (t := t) (M := M) (n := n) ms p).map
    (fun x : Stamped Colour => nameOf x.val)).count_eq u
  simp only [List.map_append, List.count_append] at h
  simp only [nm]
  omega

theorem length_nuPost (ms : MatchSpec PlaceId (KeyFn Colour ℕ)) (p : PlaceId) :
    (nuPost ms t M n p).length = (M p).length - (nuInputs ms t M n p).length := by
  have h := (nuInputs_append_nuPost (t := t) (M := M) (n := n) ms p).length_eq
  simp only [List.length_append] at h
  omega

end Fire

/-! ## The Route B reading of a translated transition -/

section Reading

variable {t : NuTrans PlaceId (KeyFn Colour ℕ)}

theorem isKey_toNuTransB (p : PlaceId) :
    isKey (toNuTransB t) p = true ↔ p ∈ (msOf t).keyPlaces := by
  unfold isKey toNuTransB msOf
  cases t.mspec <;> simp [MatchSpec.keyPlaces]

theorem keyReq_toNuTransB (p : PlaceId) : keyReq (toNuTransB t) p = reqAt t.base p := by
  unfold keyReq reqAt toNuTransB nspecAt
  simp only [toTransition, List.find?_map]
  have : ((fun s : InSpec => s.place == p) ∘ toInSpec) =
      fun s : NInSpec PlaceId => decide (s.place = p) := by
    funext s; by_cases h : s.place = p <;> simp [toInSpec, h]
  rw [this]
  cases t.base.core.inputs.find? (fun s => decide (s.place = p)) with
  | none => rfl
  | some s => cases h : s.card <;> simp [toInSpec, h, Card.required]

theorem inputs_toNuTransB : (toNuTransB t).base.inputs = t.base.core.inputs.map toInSpec := rfl

theorem resets_toNuTransB : (toNuTransB t).base.resets = t.base.core.resets := rfl

/-- What Route B's `rmvList` reads of input arcs on distinct places: the names one arc on the
place removes, or nothing. -/
theorem rmvList_map (g : InSpec → List ℕ) (p : PlaceId) (u : ℕ) : ∀ ss : List InSpec,
    (ss.map (·.place)).Nodup →
      (∃ s ∈ ss, s.place = p ∧ rmvList ss (ss.map g) p u = (g s).count u) ∨
        ((∀ s ∈ ss, s.place ≠ p) ∧ rmvList ss (ss.map g) p u = 0)
  | [], _ => Or.inr ⟨by simp, by simp [rmvList]⟩
  | s :: ss, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have ih := rmvList_map g p u ss hnd.2
    simp only [List.map_cons, rmvList]
    by_cases hs : s.place = p
    · rcases ih with ⟨s', hs', hp', -⟩ | ⟨-, h0⟩
      · exact absurd ⟨s', hs', hp'.trans hs.symm⟩ hnd.1
      · exact Or.inl ⟨s, List.mem_cons_self, hs, by simp [hs, h0]⟩
    · rcases ih with ⟨s', hs', hp', h'⟩ | ⟨hall, h0⟩
      · exact Or.inl ⟨s', List.mem_cons_of_mem _ hs', hp', by simp [hs, h']⟩
      · refine Or.inr ⟨fun x hx => ?_, by simp [hs, h0]⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hs
        · exact hall x hx

theorem mem_zip_map {α β : Type} (g : α → β) {s : α} : ∀ {ss : List α}, s ∈ ss →
    (s, g s) ∈ ss.zip (ss.map g)
  | a :: as, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]
      exact Or.inr (mem_zip_map g h)

end Reading

/-! ## The name effect -/

section NameEffect

variable {co : List PlaceId} {nameOf : Colour → ℕ} {t : NuTrans PlaceId (KeyFn Colour ℕ)}
  {M : QMarking PlaceId (Stamped Colour)} {n : ℕ}

/-- The names one input arc removes, as Route B's `ExecNames` lists them: on a coloured place the
names of the tokens the firing delivers from it; on an uncoloured place, which Route B does not
track, nothing for a draining arc and placeholder names for a fixed one. -/
def specNames (co : List PlaceId) (nameOf : Colour → ℕ) (t : NuTrans PlaceId (KeyFn Colour ℕ))
    (M : QMarking PlaceId (Stamped Colour)) (n : ℕ) (s : InSpec) : List ℕ :=
  if s.place ∈ co then nm nameOf (nuInputs (msOf t) t M n s.place)
  else if s.card.consumesAll then [] else List.replicate s.card.required 0

/-- The names the firing writes to each coloured place, in emission order. -/
def emitNames (co : List PlaceId) (nameOf : Colour → ℕ) (e : List (PlaceId × Stamped Colour)) :
    Fin co.length → List ℕ :=
  fun i => nm nameOf (qEmittedTo e co[i.1])

/-- **Every input arc removes what Route B's `SpecTakes` says**: the required count of the chosen
name on a correlated input, the whole place on a draining arc, the required count elsewhere. -/
theorem specTakes_of (hsh : B1Shape co t) (hen : enabledNA (qCount M) t.base.core = true)
    (hel : Elig t M n) (hproj : NuProj nameOf t M) {s0 : NInSpec PlaceId}
    (hs0 : s0 ∈ t.base.core.inputs) :
    SpecTakes co (toNuTransB t) (nameLayer co nameOf (vals M)) n (toInSpec s0)
      (specNames co nameOf t M n (toInSpec s0)) := by
  have hns : nspecAt t.base.core s0.place = some s0 := nspecAt_of_mem hsh.distinct hs0
  have hreq : s0.card.required ≤ (M s0.place).length := required_le_of_enabled hen hs0
  unfold SpecTakes specNames
  simp only [toInSpec]
  by_cases hk : s0.place ∈ (msOf t).keyPlaces
  · rw [if_pos ((isKey_toNuTransB _).2 hk)]
    have hcol := hsh.keysColoured _ hk
    have hfx := hsh.keysFixed _ hk
    unfold drainsAt at hfx
    rw [hns] at hfx
    simp only at hfx
    rw [if_neg (by simp [hfx]), if_pos hcol]
    obtain ⟨f, hf⟩ : ∃ f, keyAt (msOf t) s0.place = some f :=
      Option.ne_none_iff_exists'.1 (fun h => keyAt_none_iff.1 h hk)
    have hkf := keyAt_some hf
    have hpr : ∀ x ∈ M s0.place, f x.val = some (nameOf x.val) :=
      hproj _ (List.mem_append_left _ hkf)
    have hc := congrFun (corrTake_eq (M := M) (n := n) hsh.keysFixed) s0.place
    unfold nuInputs
    rw [hf, hc]
    simp only [nconsumed, hns, hfx, Bool.false_eq_true, if_false]
    have hle : s0.card.required ≤ (named f n (M s0.place)).length := by
      have := hel _ hkf
      rwa [reqAt_of_nspecAt hns] at this
    refine List.eq_replicate_iff.2 ⟨by simp [nm, List.length_take, hle], fun b hb => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact name_of_mem_named hpr (List.mem_of_mem_take hx)
  · rw [if_neg (fun h => hk ((isKey_toNuTransB _).1 h))]
    have hkn : keyAt (msOf t) s0.place = none := keyAt_none_iff.2 hk
    by_cases hcol : s0.place ∈ co
    · rw [if_pos hcol]
      unfold nuInputs
      rw [hkn]
      simp only [qInputs, qTake, nconsumed, hns]
      by_cases hc : s0.card.consumesAll = true
      · simp only [hc, if_true]
        intro u
        rw [cnt_vals_mem hcol, List.take_of_length_le (by simp [qCount])]
      · simp only [hc, Bool.false_eq_true, if_false]
        simp [nm, List.length_take, hreq]
    · rw [if_neg hcol]
      by_cases hc : s0.card.consumesAll = true
      · simp only [hc, if_true]
        intro u
        rw [cnt_vals_not_mem hcol]; rfl
      · simp [hc]

theorem inputs_places_nodup (hsh : B1Shape co t) :
    ((toNuTransB t).base.inputs.map (·.place)).Nodup := by
  have h := hsh.distinct
  unfold Spec.InputsDistinct inPlaces at h
  simpa [inputs_toNuTransB, List.map_map, Function.comp_def, toInSpec] using h

theorem mem_of_mem_qEmittedTo {e : List (PlaceId × Stamped Colour)} {p : PlaceId}
    {x : Stamped Colour} (hx : x ∈ qEmittedTo e p) : (p, x) ∈ e := by
  unfold qEmittedTo at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hy, hp⟩ := List.mem_filter.1 hy
  have : y.1 = p := by simpa using hp
  rw [← this]
  exact hy

/-- **The name effect**: a firing that takes `nuInputs` (with the shape, the eligibility of the
chosen name, the projection premise and the role's contract) changes Route B's name layer as
`ExecNames` says. -/
theorem execNames_of (r : Role) {e : List (PlaceId × Stamped Colour)}
    {M' : QMarking PlaceId (Stamped Colour)} (hsh : B1Shape co t)
    (hen : enabledNA (qCount M) t.base.core = true) (hel : Elig t M n)
    (hproj : NuProj nameOf t M) (hproj' : NuProj nameOf t M')
    (hsel : (toNuTransB t).keys.isSome = true →
      Selectable co (toNuTransB t) (nameLayer co nameOf (vals M)) n)
    (hrel : ∀ ms, t.mspec = some ms → RelayOk ms n e)
    (hK : NuContract co nameOf r t M (nuDelivered (msOf t) t M n) e)
    (hM' : M' = qAppend (nuConsume (msOf t) t M n) e)
    {d : List PlaceId} (hd : ∀ p, d.count p = (e.map Prod.fst).count p) :
    ExecNames co (toNuTransB t) d (nameLayer co nameOf (vals M)) (nameLayer co nameOf (vals M'))
      (Contract co r (toNuTransB t) (nameLayer co nameOf (vals M))) := by
  have hnd := inputs_places_nodup hsh
  refine ⟨n, (toNuTransB t).base.inputs.map (specNames co nameOf t M n), emitNames co nameOf e,
    hsel, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- every input arc removes what `SpecTakes` says
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro s hs
    rw [inputs_toNuTransB] at hs
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs
    exact specTakes_of hsh hen hel hproj hs0
  · -- the removed names are present
    intro i u
    rcases rmvList_map (specNames co nameOf t M n) co[i.1] u _ hnd with ⟨s, -, hp, h⟩ | ⟨-, h0⟩
    · rw [h, nameLayer_vals]
      unfold specNames
      rw [if_pos (hp ▸ List.getElem_mem i.isLt), hp]
      exact count_nuInputs_le _ _ _
    · rw [h0]; exact Nat.zero_le _
  · -- one written name per deposited token
    intro i
    simp [emitNames, nm, qEmittedTo_length, hd]
  · -- a relay target receives only the chosen name
    intro hks i hi w hw
    cases hm : t.mspec with
    | none => simp [toNuTransB, hm] at hks
    | some ms =>
      have hmo : msOf t = ms := by simp [msOf, hm]
      simp only [toNuTransB, hm, Option.map_some, Option.getD_some, MatchSpec.relayPlaces,
        List.mem_map] at hi
      obtain ⟨rr, hrr, hrr1⟩ := hi
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
      have h1 := hrel ms hm rr hrr x (hrr1 ▸ hx)
      have hxM : x ∈ M' rr.1 := by
        rw [hM', qAppend_apply, hrr1]; exact List.mem_append_right _ hx
      have h2 := hproj' rr (by rw [hmo]; exact List.mem_append_right _ hrr) x hxM
      rw [h1] at h2
      exact (Option.some.inj h2).symm
  · -- the role's contract
    cases r with
    | mint =>
      obtain ⟨f, hfresh, hall⟩ := hK
      refine ⟨f, fun i => ?_, fun i w hw => ?_⟩
      · rw [nameLayer_vals, List.count_eq_zero]
        intro hf
        obtain ⟨x, hx, hxf⟩ := List.mem_map.1 hf
        exact hfresh _ (List.getElem_mem i.isLt) x hx hxf
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
        exact hall _ (mem_of_mem_qEmittedTo hx) (List.getElem_mem i.isLt)
    | consume inp =>
      intro i w hw
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
      obtain ⟨s0, hs0, hcol, z, hz, hzx⟩ :=
        hK _ (mem_of_mem_qEmittedTo hx) (List.getElem_mem i.isLt)
      refine ⟨(toInSpec s0, specNames co nameOf t M n (toInSpec s0)),
        mem_zip_map _ (List.mem_map_of_mem hs0), ?_, ?_⟩
      · obtain ⟨j, hj⟩ := idx_of_mem hcol
        simp [toInSpec, hj]
      · simp only [specNames, toInSpec, if_pos hcol]
        exact List.mem_map.2 ⟨z, hz, hzx⟩
    | ordinary => trivial
    | join _ _ => trivial
  · -- the name layer after the firing
    funext u i
    subst hM'
    rw [nameLayer_vals, qAppend_apply, nm_append, List.count_append]
    simp only [resets_toNuTransB, emitNames]
    by_cases hr : co[i.1] ∈ t.base.core.resets
    · simp [nuConsume, hr, nm]
    · have hc : (t.base.core.resets.contains co[i.1]) = false := by simpa using hr
      rw [hc]
      simp only [Bool.false_eq_true, if_false, nuConsume, hr, if_false]
      rw [count_nuPost, nameLayer_vals]
      rcases rmvList_map (specNames co nameOf t M n) co[i.1] u _ hnd with ⟨s, -, hp, h⟩ |
        ⟨hall, h0⟩
      · rw [h]
        unfold specNames
        rw [if_pos (hp ▸ List.getElem_mem i.isLt), hp]
      · rw [h0]
        have hnone : nspecAt t.base.core co[i.1] = none := by
          unfold nspecAt
          rw [List.find?_eq_none]
          intro s hs he
          have := hall (toInSpec s) (by rw [inputs_toNuTransB]; exact List.mem_map_of_mem hs)
          exact this (by simpa [toInSpec] using he)
        rw [nuInputs_of_none hnone]
        simp [nm]

end NameEffect

/-! ## B1: a reference ν firing is a Route B executor step -/

section Bridge

variable {co : List PlaceId} {nameOf : Colour → ℕ} {t : NuTrans PlaceId (KeyFn Colour ℕ)}
  {M : QMarking PlaceId (Stamped Colour)} {n : ℕ}

/-- **One firing, as the reference's equations describe it**, is a `NuStepC` step: enabled on the
counts, an emission the output spec offers under the correlated takes, the name effect of
`execNames_of`. The matched and the match-free firing both reduce to this. -/
theorem nuFire_names_step (role : Novel.RouteB.NuTrans → Role)
    {X : List (NuTrans PlaceId (KeyFn Colour ℕ))} (ht : t ∈ X) (hsh : B1Shape co t)
    {e : List (PlaceId × Stamped Colour)} {M' : QMarking PlaceId (Stamped Colour)}
    (hen : enabledNA (qCount M) t.base.core = true)
    (hdep : ∃ ch, deposit (corrTake (msOf t) t M n) t.base.out ch = some (e.map Prod.fst))
    (hel : Elig t M n) (hproj : NuProj nameOf t M) (hproj' : NuProj nameOf t M')
    (hsel : (toNuTransB t).keys.isSome = true →
      Selectable co (toNuTransB t) (nameLayer co nameOf (vals M)) n)
    (hrel : ∀ ms, t.mspec = some ms → RelayOk ms n e)
    (hK : NuContract co nameOf (role (toNuTransB t)) t M (nuDelivered (msOf t) t M n) e)
    (hM' : M' = qAppend (nuConsume (msOf t) t M n) e) :
    NuStepC co nameOf (X.map toNuTransB) role false (vals M) (vals M') := by
  rw [corrTake_eq hsh.keysFixed] at hdep
  obtain ⟨ch, hch⟩ := hdep
  obtain ⟨r, hr, hperm⟩ := deposit_mem_outRows t.base (alpha (vals M)) hch
  have hk : consumedAt (vals M) (toNuTransB t).base = nconsumed (alpha (vals M)) t.base.core :=
    funext (consumedAt_toTransition _ _)
  refine ⟨toNuTransB t, List.mem_map_of_mem ht, r, hr, ?_, ?_, ?_, fun h => absurd h (by simp)⟩
  · show enabledC (vals M) (toTransition t.base.core) = true
    rw [enabledC_toTransition, ← qCount_eq_alpha]
    exact hen
  · rw [hk]
    show alpha (vals M') = alphaFireC (vals M) (toTransition t.base.core) _
    rw [alphaFireC_toTransition]
    funext p
    have hc := hperm.count_eq p
    simp only [fireNC, depProd]
    subst hM'
    simp only [alpha, vals, List.length_map, qAppend_apply, List.length_append, qEmittedTo_length]
    rw [hc]
    by_cases hres : p ∈ t.base.core.resets
    · simp [nuConsume, hres]
    · simp only [nuConsume, hres, if_false]
      rw [length_nuPost, nuInputs_length hsh.keysFixed hen hel]
  · rw [hk]
    exact execNames_of _ hsh hen hel hproj hproj' hsel hrel hK hM' (fun p => hperm.count_eq p)

/-- The eligibility of a name, read on the queues: the match has a key, and every correlated
input holds at least one token of the name and at least its required count. -/
theorem elig_of_eligible {ms : MatchSpec PlaceId (KeyFn Colour ℕ)}
    (h : eligible (matchIn ms t M) n = true) :
    ms.keys ≠ [] ∧ ∀ k ∈ ms.keys, 1 ≤ (named k.2 n (M k.1)).length ∧
      reqAt t.base k.1 ≤ (named k.2 n (M k.1)).length := by
  unfold eligible matchIn at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq,
    List.isEmpty_eq_false_iff, List.mem_map] at h
  refine ⟨fun he => by simp [he] at h, fun k hk => ?_⟩
  have := h.2 _ ⟨k, hk, rfl⟩
  simp only [stamps_length] at this
  exact this

/-- On a matched transition with the shape and the projection premise, Route B's executor
accepts the chosen name (`Selectable`). -/
theorem selectable_of_eligible {ms : MatchSpec PlaceId (KeyFn Colour ℕ)} (hm : t.mspec = some ms)
    (hsh : B1Shape co t) (hproj : NuProj nameOf t M) (h : eligible (matchIn ms t M) n = true) :
    Selectable co (toNuTransB t) (nameLayer co nameOf (vals M)) n := by
  have hmo : msOf t = ms := by simp [msOf, hm]
  obtain ⟨hne, hall⟩ := elig_of_eligible h
  intro ks hks
  simp only [toNuTransB, hm, Option.map_some, Option.some.injEq] at hks
  subst hks
  refine ⟨by simpa [MatchSpec.keyPlaces] using hne, fun p hp => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
  have hcol := hsh.keysColoured k.1 (by rw [hmo]; exact hp)
  have hpr := hproj k (by rw [hmo]; exact List.mem_append_left _ hk)
  rw [cnt_vals_mem hcol, ← named_length_eq_count hpr, keyReq_toNuTransB]
  exact hall k hk

theorem keyAt_msOf_of_none (hm : t.mspec = none) (p : PlaceId) : keyAt (msOf t) p = none := by
  simp [msOf, hm, keyAt]

/-- **B1, one firing.** Every reference ν firing of a transition of `X` (with or without a match)
is a `NuStepC` step of the translated net, given the transition's shape, the projection premise
before and after, and the role's action contract on what was delivered and emitted. -/
theorem refNuFire_names_step (role : Novel.RouteB.NuTrans → Role)
    {X : List (NuTrans PlaceId (KeyFn Colour ℕ))} (ht : t ∈ X) (hsh : B1Shape co t)
    {c : Option ℕ} {δ : QDelivered PlaceId (Stamped Colour)} {e : List (PlaceId × Stamped Colour)}
    {M' : QMarking PlaceId (Stamped Colour)} (hf : RefNuFire t M c δ e M')
    (hproj : NuProj nameOf t M) (hproj' : NuProj nameOf t M')
    (hK : NuContract co nameOf (role (toNuTransB t)) t M δ e) :
    NuStepC co nameOf (X.map toNuTransB) role false (vals M) (vals M') := by
  cases hm : t.mspec with
  | none =>
    obtain ⟨-, hen, ⟨ch, hch⟩, rfl, rfl⟩ := (refNuFire_restrictsTo t hm M c δ e M').1 hf
    have hct : corrTake (msOf t) t M 0 = nconsumed (qCount M) t.base.core := by
      funext p; simp [corrTake, keyAt_msOf_of_none hm, qTake]
    have hcons : nuConsume (msOf t) t M 0 = qConsume M t.base := by
      funext p; simp [nuConsume, nuPost, keyAt_msOf_of_none hm, qConsume]
    have hdel : nuDelivered (msOf t) t M 0 = qDelivered M t.base := by
      have hin : nuInputs (msOf t) t M 0 = qInputs M t.base := by
        funext p; simp [nuInputs, keyAt_msOf_of_none hm]
      have hpost : nuPost (msOf t) t M 0 = qPostInput M t.base := by
        funext p; simp [nuPost, keyAt_msOf_of_none hm]
      simp [nuDelivered, qDelivered, qReads, hin, hpost]
    refine nuFire_names_step (n := 0) role ht hsh hen ⟨ch, by rw [hct]; exact hch⟩
      (fun k hk => by simp [msOf, hm] at hk) hproj hproj'
      (fun h => by simp [toNuTransB, hm] at h) (fun ms h => by rw [hm] at h; cases h)
      (by rw [hdel]; exact hK) (by rw [hcons]; rfl)
  | some ms =>
    obtain ⟨n, rfl, hs, hen, hdep, hrel, rfl, rfl⟩ := (refNuFire_matched hm M c δ e M').1 hf
    have hmo : msOf t = ms := by simp [msOf, hm]
    have hsel := (refSelect_eq_some_iff.1 hs).1
    refine nuFire_names_step (n := n) role ht hsh hen (by rw [hmo]; exact hdep)
      (fun k hk => ((elig_of_eligible hsel).2 k (hmo ▸ hk)).2) hproj hproj'
      (fun _ => selectable_of_eligible hm hsh hproj hsel)
      (fun ms' h => by rw [hm] at h; cases h; exact hrel) (by rw [hmo]; exact hK) (by rw [hmo])

/-- **B1, runs, the strong form.** A reference ν run of `X` whose every firing meets the
projection premise and its role's contract is a run of `NuStepC` steps of the translated net.

The premise `hok` asks the contract of EVERY firing the reference offers from a reachable marking,
including firings whose action writes a stale name. The reference leaves the emitted values free,
so once a coloured place holds a name, a mint that can fire again has a firing that writes that
name, and `hok` fails: on every net in which a mint can fire twice this form says nothing
(`NU_050`'s `nu050_hok_fails`). The headline form is `refNuRunB_names_reach`, over the runs whose
firings keep their contracts (`RefNuRunB`). -/
theorem refNuReach_names_reach (role : Novel.RouteB.NuTrans → Role)
    {X : List (NuTrans PlaceId (KeyFn Colour ℕ))} (hsh : ∀ t ∈ X, B1Shape co t)
    {M0 M : QMarking PlaceId (Stamped Colour)}
    (hok : ∀ M₁ M₂, RefNuReach X M0 M₁ → ∀ t ∈ X, ∀ c δ e, RefNuFire t M₁ c δ e M₂ →
      NuProj nameOf t M₁ ∧ NuProj nameOf t M₂ ∧ NuContract co nameOf (role (toNuTransB t)) t M₁ δ e)
    (h : RefNuReach X M0 M) :
    Relation.ReflTransGen (NuStepC co nameOf (X.map toNuTransB) role false) (vals M0) (vals M) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hr hs ih =>
    obtain ⟨t, ht, c, δ, e, hf⟩ := hs
    obtain ⟨hp, hp', hK⟩ := hok _ _ hr t ht c δ e hf
    exact ih.tail (refNuFire_names_step role ht (hsh t ht) hf hp hp' hK)

/-- Every translated transition is guard-free (inputs carry no guard since [IO-006]): the `hG`
premise of Route B's soundness theorems. -/
theorem guardFree_toNuTransB (X : List (NuTrans PlaceId (KeyFn Colour ℕ))) :
    ∀ T ∈ X.map toNuTransB, Novel.RouteB.GuardFree T.base := by
  intro T hT
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hT
  exact guardNone_toTransition t.base.core

/-- **B1 with Route B, the strong form.** On a translated net in Route B's fragment, from a class
with the key of the initial marking, every marking a reference ν run reaches (every firing
meeting the projection premise and its contract) has the key of a class the Route B exploration
reaches. Its premise `hok` is the one of `refNuReach_names_reach`, which no net with a mint that
can fire twice meets; the headline form is `refNuRunB_routeB`. -/
theorem refNuReach_routeB (role : Novel.RouteB.NuTrans → Role)
    {X : List (NuTrans PlaceId (KeyFn Colour ℕ))} (hco : co.Nodup)
    (hfr : ∀ T ∈ X.map toNuTransB, Novel.RouteB.InFragment co T (role T))
    (hsh : ∀ t ∈ X, B1Shape co t) {M0 M : QMarking PlaceId (Stamped Colour)}
    {S0 : Novel.RouteB.NState co AMarking}
    (h0 : Novel.RouteB.keyOf S0 = Novel.RouteB.keyOf (Novel.RouteB.view co nameOf (vals M0)))
    (hok : ∀ M₁ M₂, RefNuReach X M0 M₁ → ∀ t ∈ X, ∀ c δ e, RefNuFire t M₁ c δ e M₂ →
      NuProj nameOf t M₁ ∧ NuProj nameOf t M₂ ∧ NuContract co nameOf (role (toNuTransB t)) t M₁ δ e)
    (h : RefNuReach X M0 M) :
    ∃ S, Explorer.Reach (Novel.RouteB.routeB Novel.RouteB.untimedBase (X.map toNuTransB) role false)
        S0 S ∧
      Novel.RouteB.keyOf S = Novel.RouteB.keyOf (Novel.RouteB.view co nameOf (vals M)) := by
  exact Novel.RouteB.exec_reach_simulated hco hfr (guardFree_toNuTransB X) h0
    (refNuReach_names_reach role hsh hok h)

end Bridge

/-! ## B1 on contract-keeping runs (the headline form) -/

section Runs

/-- **A contract-keeping reference run for Route B.** From `M0`, a sequence of reference ν
firings (`RefNuFire`) of transitions of `X`, each of whose actions keeps the contract of the role
Route B gives its transition (`NuContract`: a mint writes one name no coloured place holds into
every coloured output; a coloured consumer writes only a name it received from a coloured
input). A firing whose action breaks its contract is not a step of such a run. -/
def RefNuRunB (co : List PlaceId) (nameOf : Colour → ℕ) (role : Novel.RouteB.NuTrans → Role)
    (X : List (NuTrans PlaceId (KeyFn Colour ℕ))) (M0 : QMarking PlaceId (Stamped Colour)) :
    QMarking PlaceId (Stamped Colour) → Prop :=
  Relation.ReflTransGen (fun M M' => ∃ t ∈ X, ∃ c δ e, RefNuFire t M c δ e M' ∧
    NuContract co nameOf (role (toNuTransB t)) t M δ e) M0

/-- A contract-keeping run is a reference ν run. -/
theorem RefNuRunB.refNuReach {co : List PlaceId} {nameOf : Colour → ℕ}
    {role : Novel.RouteB.NuTrans → Role} {X : List (NuTrans PlaceId (KeyFn Colour ℕ))}
    {M0 M : QMarking PlaceId (Stamped Colour)} (h : RefNuRunB co nameOf role X M0 M) :
    RefNuReach X M0 M := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨t, ht, c, δ, e, hf, -⟩ := hs
    exact ih.tail ⟨t, ht, c, δ, e, hf⟩

/-- **B1 on contract-keeping runs.** Every marking a contract-keeping reference run reaches,
read without stamps, is reached by a run of Route B's executor model `NuStepC` on the translated
net, given the shape of every transition and the projection premise at every marking the run
reaches. -/
theorem refNuRunB_names_reach {co : List PlaceId} {nameOf : Colour → ℕ}
    {role : Novel.RouteB.NuTrans → Role} {X : List (NuTrans PlaceId (KeyFn Colour ℕ))}
    {M0 : QMarking PlaceId (Stamped Colour)}
    (hsh : ∀ t ∈ X, B1Shape co t)
    (hproj : ∀ M, RefNuRunB co nameOf role X M0 M → ∀ t ∈ X, NuProj nameOf t M)
    {M : QMarking PlaceId (Stamped Colour)} (h : RefNuRunB co nameOf role X M0 M) :
    Relation.ReflTransGen (NuStepC co nameOf (X.map toNuTransB) role false) (vals M0) (vals M) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail M1 M2 hr hs ih =>
    obtain ⟨t, ht, c, δ, e, hf, hK⟩ := hs
    have hr2 : RefNuRunB co nameOf role X M0 M2 := hr.tail ⟨t, ht, c, δ, e, hf, hK⟩
    exact ih.tail (refNuFire_names_step role ht (hsh t ht) hf (hproj M1 hr t ht)
      (hproj M2 hr2 t ht) hK)

/-- **B1 with Route B on contract-keeping runs.** On a translated net in Route B's fragment, from
a class with the key of the initial marking, every marking a contract-keeping reference run
reaches has the key of a class the Route B exploration reaches. -/
theorem refNuRunB_routeB {co : List PlaceId} {nameOf : Colour → ℕ}
    (role : Novel.RouteB.NuTrans → Role)
    {X : List (NuTrans PlaceId (KeyFn Colour ℕ))} (hco : co.Nodup)
    (hfr : ∀ T ∈ X.map toNuTransB, Novel.RouteB.InFragment co T (role T))
    (hsh : ∀ t ∈ X, B1Shape co t) {M0 M : QMarking PlaceId (Stamped Colour)}
    {S0 : Novel.RouteB.NState co AMarking}
    (h0 : Novel.RouteB.keyOf S0 = Novel.RouteB.keyOf (Novel.RouteB.view co nameOf (vals M0)))
    (hproj : ∀ M, RefNuRunB co nameOf role X M0 M → ∀ t ∈ X, NuProj nameOf t M)
    (h : RefNuRunB co nameOf role X M0 M) :
    ∃ S, Explorer.Reach (Novel.RouteB.routeB Novel.RouteB.untimedBase (X.map toNuTransB) role false)
        S0 S ∧
      Novel.RouteB.keyOf S = Novel.RouteB.keyOf (Novel.RouteB.view co nameOf (vals M)) :=
  Novel.RouteB.exec_reach_simulated hco hfr (guardFree_toNuTransB X) h0
    (refNuRunB_names_reach hsh hproj h)

/-- **The mint contract of [NU-010] is Route B's mint contract on the reference.** On a queue
marking `M` and an emission `e`, `NuContract` at the mint role is `MintContract` (ruling D78 (a),
`Reference/NuMint.lean`) with `holds p v`: the coloured place `p` holds a token named `v`, and
`wr p`: the names `e` writes into the coloured place `p`. -/
theorem nuContract_mint_iff (co : List PlaceId) (nameOf : Colour → ℕ)
    (t : NuTrans PlaceId (KeyFn Colour ℕ)) (M : QMarking PlaceId (Stamped Colour))
    (δ : QDelivered PlaceId (Stamped Colour)) (e : List (PlaceId × Stamped Colour)) :
    NuContract co nameOf .mint t M δ e ↔
      MintContract (fun p v => p ∈ co ∧ ∃ x ∈ M p, nameOf x.val = v)
        (fun p => if p ∈ co then (qEmittedTo e p).map (fun x => nameOf x.val) else []) := by
  constructor
  · rintro ⟨f, hf, hw⟩
    refine ⟨f, fun c ⟨hc, x, hx, hxf⟩ => hf c hc x hx hxf, fun c w hw' => ?_⟩
    simp only at hw'
    by_cases hc : c ∈ co
    · rw [if_pos hc] at hw'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hw'
      simp only [qEmittedTo, List.mem_map, List.mem_filter, decide_eq_true_eq] at hy
      obtain ⟨z, ⟨hz, hzc⟩, rfl⟩ := hy
      exact hw z hz (hzc ▸ hc)
    · rw [if_neg hc] at hw'
      exact absurd hw' List.not_mem_nil
  · rintro ⟨f, hf, hw⟩
    refine ⟨f, fun p hp x hx hxf => hf p ⟨hp, x, hx, hxf⟩, fun x hx hxc => ?_⟩
    apply hw x.1
    show nameOf x.2.val ∈ (if x.1 ∈ co then _ else [])
    rw [if_pos hxc]
    exact List.mem_map.2 ⟨x.2, List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, by simp⟩, rfl⟩, rfl⟩

end Runs

/-! ## A worked example: the premises are met -/

section Example

/-- The key of the example: a token's name is its value. -/
def exKey : KeyFn Colour ℕ := some

/-- The example join: one token from place 0 and one from place 1, joined on the name, writes one
token to place 2. -/
def exJoin : NuTrans PlaceId (KeyFn Colour ℕ) where
  base :=
    { core :=
        { name := "join", inputs := [⟨0, .one⟩, ⟨1, .one⟩], inhibitors := [], reads := [],
          resets := [] }
      out := some (.place 2) }
  mspec := some { keys := [(0, exKey), (1, exKey)] }

/-- The example marking: place 0 holds a token named 7 (stamp 0) and one named 5 (stamp 2);
place 1 holds a token named 5 (stamp 1). -/
def exM : QMarking PlaceId (Stamped Colour) := fun p =>
  if p = 0 then [⟨7, 0⟩, ⟨5, 2⟩] else if p = 1 then [⟨5, 1⟩] else []

theorem exJoin_shape : B1Shape [0, 1] exJoin :=
  ⟨by decide, by simp [msOf, exJoin, MatchSpec.keyPlaces, drainsAt, nspecAt, Card.consumesAll],
    by simp [msOf, exJoin, MatchSpec.keyPlaces]⟩

theorem exJoin_proj (M : QMarking PlaceId (Stamped Colour)) : NuProj id exJoin M := by
  intro k hk x _
  simp only [msOf, exJoin, Option.getD_some, List.append_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hk
  rcases hk with rfl | rfl <;> rfl

/-- **Worked example.** Place 0 holds tokens named 7 and 5, place 1 a token named 5. The join
fires on name 5, the only name both places hold, and writes one token to place 2. Its reference
firing, read without stamps, is a step of Route B's executor model: the bridge's premises (shape,
projection, contract) all hold here, so the bridge is not vacuous. -/
theorem exJoin_names_step : ∃ δ M', RefNuFire exJoin exM (some 5) δ [(2, ⟨0, 3⟩)] M' ∧
    NuStepC [0, 1] id ([exJoin].map toNuTransB) (fun _ => .ordinary) false (vals exM)
      (vals M') := by
  obtain ⟨δ, M', hf⟩ := refNuFire_covers exJoin { keys := [(0, exKey), (1, exKey)] } rfl exM 5
    (refSelect_eq_some_iff.1 (by decide)) (by decide) [(2, ⟨0, 3⟩)]
    ⟨.action 0, rfl⟩ (by simp [RelayOk])
  exact ⟨δ, M', hf, refNuFire_names_step _ List.mem_cons_self exJoin_shape hf (exJoin_proj _)
    (exJoin_proj _) trivial⟩

/-- The example join with a draining (`All`) correlated input on place 0. -/
def exJoinAll : NuTrans PlaceId (KeyFn Colour ℕ) where
  base :=
    { core :=
        { name := "join", inputs := [⟨0, .all⟩, ⟨1, .one⟩], inhibitors := [], reads := [],
          resets := [] }
      out := some (.place 2) }
  mspec := some { keys := [(0, exKey), (1, exKey)] }

/-- **Why correlated inputs must take a fixed count.** With an `All` arc on place 0, the join on
name 5 takes only the token named 5 from place 0 and leaves the token named 7 there. Route B's
executor model would empty place 0, so this reference firing is not one of its steps: the
`keysFixed` premise of `B1Shape` cannot be dropped. -/
theorem exJoinAll_not_step : ∃ δ M', RefNuFire exJoinAll exM (some 5) δ [(2, ⟨0, 3⟩)] M' ∧
    ¬ NuStepC [0, 1] id ([exJoinAll].map toNuTransB) (fun _ => .ordinary) false (vals exM)
      (vals M') := by
  obtain ⟨δ, M', hf⟩ := refNuFire_covers exJoinAll { keys := [(0, exKey), (1, exKey)] } rfl exM 5
    (refSelect_eq_some_iff.1 (by decide)) (by decide) [(2, ⟨0, 3⟩)]
    ⟨.action 0, rfl⟩ (by simp [RelayOk])
  refine ⟨δ, M', hf, ?_⟩
  obtain ⟨n, hn, -, -, -, -, -, hM'⟩ := (refNuFire_matched rfl exM _ δ _ M').1 hf
  cases hn
  rintro ⟨T, hT, r, hr, -, heff, -⟩
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hT
  subst hT
  have h0 := congrFun heff 0
  have hr' : r = { fixed := [2] } := by
    simpa [toNuTransB, outRows, exJoinAll, Out.branches, Out.findTimeout] using hr
  subst hr' hM'
  revert h0
  decide

end Example

end Libpetri.Reference.NuLink
