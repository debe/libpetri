import Libpetri.Novel.RouteB.Sim
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# `classify`: the fragment Route B admits, and why the off-key rule is needed ([NU-051] AC7)

Model of `name_fragment.rs::classify` for one transition, given the coloured set (`coloured`, the
union of every match key, plus under EXTENDED the declared carriers and every relay target) and
the mode. The rules, in the Rust's order:

1. (all transitions, `classify` step 1b) no reset / read / inhibitor arc on a coloured place —
   `arcsOk`;
2. a branch outcome depositing into a coloured place at any count but one rejects the net,
   a drained forward (`Deposit::Drained`) into a coloured place included;
3. a matched transition is a `Join` when it writes a coloured place only as a declared relay
   target (EXTENDED; none under BASE), consumes **no coloured place off-key** (the rule
   `4d7a9d9` added; `offKey = false` models the code before it), and every key's first input
   spec is `One` / `Exactly`; its `coloured_in` lists one `(place, count)` per key. The Rust sorts
   it by place name; the model keeps key order. The order is not irrelevant: the removal
   `name_successors` drives is order-independent (`foldl_remove_apply`), but `joinEnab`, like
   `enabling_symbols`, seeds its candidates from the head of `coloured_in` (`symbols_in` of the
   first place, so the head key is asked for presence) and asks every other key only for
   `count ≥ required`. With every count at least one the head test is implied and the order
   drops out (`joinEnab_perm_of_pos`); with a zero-count key it does not
   (`zeroKey_order_matters`). The step direction never depends on it (a `Selectable` name is
   present in every key place), so only the quiescence half, through `PosKeys`, sees it;
4. a non-matched transition consuming a coloured place is rejected under BASE, and under EXTENDED
   is a `Consume` when it has exactly one coloured input spec, at count one;
5. else `Mint` when some branch writes a coloured place, else `Ordinary`.

`classifyT` is the rule set before the contract fixes. The shipped function adds the declared
mints and the timeout-write rules; it is `classifyS` (section "`classify` as shipped" at the end
of this file), which only refuses more (`classifyS_sub`).

Results:
* `classifyT_join_offKey`: with the shipped rule, an accepted join consumes coloured places only
  through its keys — the off-key clause of `InFragment`.
* **`classifyT_inFragment`**: whatever role `classify` assigns, the transition meets
  `InFragment` for it, given that the coloured set is `coloured_order`, every key is coloured (by
  construction of the coloured set), and the two join conditions `classify` does not check:
  distinct keys and at most one input spec per key place (`hone`). The builders discharge both
  (`BuilderOK`, `classifyS_inFragment`): `MatchSpecBuilder::build` and `TransitionBuilder::build`
  panic on a place keyed twice, and `TransitionBuilder::build` on two input arcs on one place,
  [CORE-030] AC3, so no transition `classify` sees violates them. The empty key list and a
  zero-count key need no premise for the step: `Selectable` models `select_match_name`, which
  returns `None` without keys and needs the name present in every key place.
* **`offKey_rule_is_necessary`** (retrodiction of `4d7a9d9`): a join `J : A, B, C → OUT` keyed on
  `A`, `B` that also takes `C` (another join's key) through a plain input. Before the fix
  `classify` accepted it as `join [(A,1),(B,1)] []`; with the fix it is rejected. From a name
  layer with `s` in `A` and `B` and `u` in `C`, the executor's firing on `s` also takes `u` off
  `C` (FIFO), and **no** `name_successors` output of the pre-fix role has that successor's key:
  every one keeps `C` occupied. The graph keeps a symbol the base marking has lost.
* `dupKey_breaks_simulation` (fixed: `MatchSpecBuilder::build` and `TransitionBuilder::build`
  now panic on it, `dupKey_refused`): a match spec that names one place twice passed `classify`
  and `MatchSpec::build`; its `coloured_in` is `[(A,1),(A,1)]`, the Rust
  `remove`s the matched symbol twice while the runtime consumes one token per input spec, and no
  graph successor has the executor's key. The distinct-keys clause of `InFragment` is
  load-bearing, and the builder now discharges it (`BuilderOK.keysNodup`).
* `copyingMint_breaks_simulation`: a `Mint` whose action writes a live name (the stock `fork()`
  copies its input) has an executor successor no graph successor matches, so the `Mint` contract
  is load-bearing too. The shipped `classify` refuses an undeclared writer (`copyingMint_refused`),
  so the contract is now a premise the net declares ([NU-010]), still not checked at run time.
* `zeroKey_breaks_quiescence` (fixed: `TransitionBuilder::build` now panics on an input that
  requires zero tokens, `zeroKey_refused`): a key spec `In::Exactly { count: 0 }` passed
  `classify`. When that key is not the head of `coloured_in` (in the Rust: not the name-least
  key), `enabling_symbols` asks only `count ≥ 0` of its place, while `select_match_name` still
  needs the name present. A class whose executor marking is quiescent has a successor, so the
  quiescence premise `PosKeys` (every key consumes at least one token) is load-bearing.
  `PosKeys` is sufficient, not exact: a zero-count key at the head is still asked for presence
  (`zeroKey_order_matters`), so the Rust is exposed only when a zero-count key sorts after
  another key. The model states the stronger premise because its `coloured_in` is in key order,
  not name order.
* `joinEnab_perm_of_pos`, `zeroKey_order_matters`: under `PosKeys` the order of `coloured_in` is
  irrelevant to `joinEnab`; without it, it decides which zero-count key is asked for presence.
-/

namespace Libpetri.Novel.RouteB

open Libpetri
open Libpetri.Novel.CanonicalKey
open Libpetri.Novel.ForwardDeposit

section Classify

/-- `FragmentMode`. -/
inductive Mode where
  | base
  | extended
  deriving DecidableEq

variable (col : PlaceId → Bool)

/-- Rule 1 (`classify` step 1b), per transition. -/
def arcsOk (T : NuTrans) : Bool :=
  !(T.base.resets.any col || T.base.reads.any col || T.base.inhibitors.any col)

/-- `required` for a key: `One` → 1, `Exactly n` → n, anything else rejects. -/
def keyCount (T : NuTrans) (p : PlaceId) : Option (PlaceId × ℕ) :=
  match T.base.inputs.find? (fun s => s.place == p) with
  | some s => match s.card with
    | .one => some (p, 1)
    | .exactly c => some (p, c)
    | _ => none
  | none => none

/-- The role `classify` assigns one transition, or `none` (the net falls back). `offKey` selects
the off-key rule of `4d7a9d9`. Rule 2 rejects a fixed deposit into a coloured place at any count
but one and any drained forward into a coloured place (a `Deposit::Drained` is never
`Deposit::Tokens(1)`). -/
def classifyT (mode : Mode) (offKey : Bool) (T : NuTrans) : Option Role :=
  let colIns := T.base.inputs.filter fun s => col s.place
  if !(arcsOk col T) then none
  else if T.rows.any (fun r => r.fixed.any (fun p => col p && r.fixed.count p != 1)
      || r.drains.any fun x => col x.1) then none
  else match T.keys with
  | some ks =>
    let relayTo := if mode = .extended then T.relays else []
    if T.rows.any (fun r => r.places.any fun p => col p && !relayTo.contains p) then none
    else if offKey && colIns.any (fun s => !ks.contains s.place) then none
    else (ks.mapM (keyCount T)).map fun cin => Role.join cin relayTo
  | none =>
    if !colIns.isEmpty then
      match mode, colIns with
      | .extended, [s] =>
        match s.card with
        | .one => some (Role.consume s.place)
        | .exactly 1 => some (Role.consume s.place)
        | _ => none
      | _, _ => none
    else if T.rows.any (fun r => r.places.any col) then some Role.mint
    else some Role.ordinary

variable {col}

/-- **The off-key clause.** With the shipped rule an accepted join consumes a coloured place only
through one of its keys. -/
theorem classifyT_join_offKey {mode : Mode} {T : NuTrans} {cin : List (PlaceId × ℕ)}
    {rel : List PlaceId} (h : classifyT col mode true T = some (Role.join cin rel)) :
    ∃ ks, T.keys = some ks ∧ ∀ s ∈ T.base.inputs, col s.place = true → s.place ∈ ks := by
  cases hk : T.keys with
  | none =>
    exfalso
    unfold classifyT at h
    rw [hk] at h
    simp only at h
    split_ifs at h
    all_goals first
      | cases h
      | (split at h <;> first | cases h | (split at h <;> cases h))
  | some ks =>
    refine ⟨ks, rfl, fun s hs hc => ?_⟩
    by_contra hnot
    have hany : ((T.base.inputs.filter fun s => col s.place).any
        fun s => !ks.contains s.place) = true := by
      rw [List.any_eq_true]
      exact ⟨s, List.mem_filter.mpr ⟨hs, hc⟩, by simpa [List.contains_iff_mem] using hnot⟩
    unfold classifyT at h
    rw [hk] at h
    simp only [hany, Bool.true_and] at h
    split_ifs at h

theorem mapM_keyCount {T : NuTrans} :
    ∀ {ks : List PlaceId} {cin : List (PlaceId × ℕ)}, ks.mapM (keyCount T) = some cin →
      List.Forall₂ (fun p pr => keyCount T p = some pr) ks cin
  | [], cin, h => by
    simp only [List.mapM_nil] at h
    cases h
    exact List.Forall₂.nil
  | p :: ks, cin, h => by
    simp only [List.mapM_cons] at h
    cases hp : keyCount T p with
    | none => rw [hp] at h; cases h
    | some pr =>
      rw [hp] at h
      cases hr : ks.mapM (keyCount T) with
      | none => rw [hr] at h; cases h
      | some rest =>
        rw [hr] at h
        cases h
        exact List.Forall₂.cons hp (mapM_keyCount hr)

theorem keyCount_spec {T : NuTrans} {p : PlaceId} {pr : PlaceId × ℕ}
    (h : keyCount T p = some pr) :
    pr.1 = p ∧ ∃ s, T.base.inputs.find? (fun s => s.place == p) = some s ∧ FixedCard s pr.2 := by
  unfold keyCount at h
  split at h
  · rename_i s hs
    split at h <;> cases h
    · rename_i hc; exact ⟨rfl, s, hs, Or.inl ⟨hc, rfl⟩⟩
    · rename_i c hc; exact ⟨rfl, s, hs, Or.inr hc⟩
  · cases h

theorem forall2_fst {T : NuTrans} :
    ∀ {ks : List PlaceId} {cin : List (PlaceId × ℕ)},
      List.Forall₂ (fun p pr => keyCount T p = some pr) ks cin → cin.map Prod.fst = ks
  | [], [], List.Forall₂.nil => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h hr => by
    rw [List.map_cons, (keyCount_spec h).1, forall2_fst hr]

theorem forall2_mem {T : NuTrans} :
    ∀ {ks : List PlaceId} {cin : List (PlaceId × ℕ)},
      List.Forall₂ (fun p pr => keyCount T p = some pr) ks cin →
        ∀ pr ∈ cin, keyCount T pr.1 = some pr
  | [], [], List.Forall₂.nil, _, h => absurd h List.not_mem_nil
  | _ :: _, _ :: _, List.Forall₂.cons h hr, pr, hpr => by
    rcases List.mem_cons.mp hpr with rfl | hpr
    · rw [(keyCount_spec h).1]; exact h
    · exact forall2_mem hr pr hpr

theorem filter_singleton_of_find {l : List InSpec} {P : InSpec → Bool} {s : InSpec}
    (hf : l.find? P = some s) (hle : (l.filter P).length ≤ 1) : l.filter P = [s] := by
  rw [← List.head?_filter] at hf
  cases hl : l.filter P with
  | nil => rw [hl] at hf; cases hf
  | cons a rest =>
    rw [hl] at hf hle
    cases hf
    cases rest with
    | nil => rfl
    | cons _ _ => simp at hle

theorem idx_none_of_col {co : List PlaceId} (hcol : ∀ p, col p = (idx co p).isSome)
    {p : PlaceId} (h : col p = false) : idx co p = none := by
  rw [hcol] at h
  exact Option.not_isSome_iff_eq_none.mp (by simp [h])

/-- **`classify` establishes `InFragment`.** Whatever role the shipped `classify` assigns, the
transition meets the fragment conditions for it, given: the coloured set is `coloured_order`
(`hcol`); every key is coloured (`hkc`: `classify` puts every match key in the coloured set by
construction, step 1); and the two join conditions `classify` does not check, distinct keys
(`hnd`, `dupKey_breaks_simulation`) and at most one input spec per key place (`hone`;
`classify` reads the first). Both are discharged before `classify` runs: `TransitionBuilder::build`
panics on a place keyed twice (`match_spec.rs::duplicate_key`, [NU-020]) and on two input arcs on
one place ([CORE-030] AC3), and every transition of a net passes through it
(`classifyS_inFragment`). -/
theorem classifyT_inFragment {co : List PlaceId} (hcol : ∀ p, col p = (idx co p).isSome)
    {mode : Mode} {T : NuTrans} {r : Role} (h : classifyT col mode true T = some r)
    (hkc : ∀ ks, T.keys = some ks → ∀ p ∈ ks, col p = true)
    (hnd : ∀ ks, T.keys = some ks → ks.Nodup)
    (hone : ∀ ks, T.keys = some ks → ∀ p ∈ ks,
      (T.base.inputs.filter fun s => s.place == p).length ≤ 1) :
    InFragment co T r := by
  have h0 := h
  unfold classifyT at h
  simp only at h
  by_cases h1 : (!(arcsOk col T)) = true
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : T.rows.any (fun r => r.fixed.any (fun p => col p && r.fixed.count p != 1)
      || r.drains.any fun x => col x.1) = true
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  have hcom : Common co T := by
    have ha : arcsOk col T = true := by simpa using h1
    have hrow : ∀ r ∈ T.rows, (r.fixed.any (fun p => col p && r.fixed.count p != 1)
        || r.drains.any fun x => col x.1) = false := by
      intro r hr
      cases hc : (r.fixed.any (fun p => col p && r.fixed.count p != 1)
        || r.drains.any fun x => col x.1)
      · rfl
      · exact absurd (List.any_eq_true.mpr ⟨r, hr, hc⟩) h2
    refine ⟨fun p hp => idx_none_of_col hcol ?_, fun r hr p hp hc => ?_, fun r hr x hx =>
      idx_none_of_col hcol ?_⟩
    · cases hcp : col p
      · rfl
      · have : T.base.resets.any col = true := List.any_eq_true.mpr ⟨p, hp, hcp⟩
        simp [arcsOk, this] at ha
    · by_contra hne
      have hany : r.fixed.any (fun p => col p && r.fixed.count p != 1) = true :=
        List.any_eq_true.mpr ⟨p, hp, by simp [hcol, hc, hne]⟩
      have := hrow r hr
      simp [hany] at this
    · cases hcx : col x.1
      · rfl
      · have hany : r.drains.any (fun x => col x.1) = true := List.any_eq_true.mpr ⟨x, hx, hcx⟩
        have := hrow r hr
        simp [hany] at this
  cases hk : T.keys with
  | some ks =>
    rw [hk] at h
    simp only at h
    generalize hrel : (if mode = .extended then T.relays else []) = rel at h
    split_ifs at h with h3 h4
    obtain ⟨cin, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    have hF := mapM_keyCount hm
    have hfst := forall2_fst hF
    obtain ⟨ks', hks', hoff⟩ := classifyT_join_offKey h0
    rw [hk] at hks'
    cases hks'
    refine ⟨hcom, ks, hk, fun p => by rw [hfst], by rw [hfst]; exact hnd ks hk, ?_, ?_, ?_, ?_⟩
    · intro pr hpr
      have hkp := forall2_mem hF pr hpr
      obtain ⟨-, s, hfs, hfc⟩ := keyCount_spec hkp
      have hmem : pr.1 ∈ ks := by rw [← hfst]; exact List.mem_map_of_mem hpr
      refine ⟨by rw [← hcol]; exact hkc ks hk _ hmem, s,
        filter_singleton_of_find hfs (hone ks hk _ hmem), hfc⟩
    · intro s hs hc
      exact hoff s hs (by rw [hcol]; exact hc)
    · intro r hr p hp hc
      by_contra hn
      apply h3
      refine List.any_eq_true.mpr ⟨r, hr, List.any_eq_true.mpr ⟨p, hp, ?_⟩⟩
      rw [Bool.and_eq_true, hcol, Bool.not_eq_true']
      refine ⟨hc, ?_⟩
      cases hcn : rel.contains p
      · rfl
      · exact absurd (List.contains_iff_mem.mp hcn) hn
    · intro p hp
      rw [← hrel] at hp
      split at hp
      · exact hp
      · exact absurd hp List.not_mem_nil
  | none =>
    rw [hk] at h
    simp only at h
    have hcolf : (fun s : InSpec => col s.place) = fun s => (idx co s.place).isSome :=
      funext fun s => hcol s.place
    have hnoin : (T.base.inputs.filter fun s => col s.place).isEmpty = true →
        ∀ s ∈ T.base.inputs, idx co s.place = none := by
      intro he s hs
      refine idx_none_of_col hcol ?_
      cases hc : col s.place
      · rfl
      · have : s ∈ T.base.inputs.filter fun s => col s.place := List.mem_filter.mpr ⟨hs, hc⟩
        rw [List.isEmpty_iff] at he
        rw [he] at this
        exact absurd this List.not_mem_nil
    split_ifs at h with h3 h4
    · split at h
      · rename_i s hs
        split at h <;> cases h
        · rename_i hc
          exact ⟨hcom, hk, s, by rw [← hcolf]; exact hs, rfl, Or.inl ⟨hc, rfl⟩⟩
        · rename_i hc
          exact ⟨hcom, hk, s, by rw [← hcolf]; exact hs, rfl, Or.inr hc⟩
      · cases h
    · cases h
      exact ⟨hcom, hk, hnoin (by simpa using h3)⟩
    · cases h
      refine ⟨hcom, hk, hnoin (by simpa using h3), fun r hr p hp => idx_none_of_col hcol ?_⟩
      cases hcp : col p
      · rfl
      · exact absurd (List.any_eq_true.mpr ⟨r, hr, List.any_eq_true.mpr ⟨p, hp, hcp⟩⟩) h4

end Classify

/-! ## The off-key witness -/

section OffKey

/-- Places: `A = 0`, `B = 1`, `C = 2` (coloured, in that order), `OUT = 3`. -/
def coW : List PlaceId := [0, 1, 2]

def colW (p : PlaceId) : Bool := coW.contains p

def inOne (p : PlaceId) : InSpec := { place := p, card := .one, guard := none }

/-- `J : A, B, C → OUT`, keyed on `A`, `B`; `C` (another join's key) consumed off-key. -/
def tJ : NuTrans where
  base := { name := "J", inputs := [inOne 0, inOne 1, inOne 2], inhibitors := [], reads := [],
            resets := [] }
  rows := [⟨[3], []⟩]
  keys := some [0, 1]
  relays := []

/-- Before `4d7a9d9` `classify` accepted `J` as a plain join; since, it rejects it. -/
theorem classify_offKey_before_after :
    classifyT colW .base false tJ = some (Role.join [(0, 1), (1, 1)] []) ∧
    classifyT colW .base true tJ = none := by
  constructor <;> rfl

/-- The name layer: `s = 0` in `A` and `B`, `u = 1` in `C`. -/
def mW : NM coW := fun u i =>
  if i.1 = 0 ∧ u = 0 then 1 else if i.1 = 1 ∧ u = 0 then 1 else if i.1 = 2 ∧ u = 1 then 1 else 0

/-- The executor's successor: `J` fires on `s`, and the FIFO head of `C` is `u`: all empty. -/
def mW' : NM coW := fun _ _ => 0

theorem mW_supp : Supp mW 2 := by
  intro s hs i
  unfold mW
  have h0 : s ≠ 0 := by omega
  have h1 : s ≠ 1 := by omega
  simp [h0, h1]

/-- The firing is an executor step: `s` is selectable, `A` and `B` give `s`, `C` gives `u`. -/
theorem offKey_exec :
    ExecNames coW tJ [3] mW mW' (Contract coW (Role.join [(0, 1), (1, 1)] []) tJ mW) := by
  refine ⟨0, [[0], [0], [1]], fun _ => [], ?_, ?_, ?_, ?_, ?_, trivial, ?_⟩
  · intro _ ks hks
    cases hks
    refine ⟨by simp, fun p hp => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨by decide, by decide⟩
  · refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)) <;>
      simp [SpecTakes, isKey, tJ, inOne, Card.consumesAll, Card.required]
  · intro i u
    fin_cases i <;> simp [rmvList, mW, inOne, tJ, coW, List.count_singleton] <;>
      (try split_ifs) <;> omega
  · intro i
    fin_cases i <;> decide
  · intro _ i hi
    simp [tJ] at hi
  · funext u i
    fin_cases i <;> simp [rmvList, mW, mW', inOne, tJ, coW, List.count_singleton] <;>
      (try split_ifs) <;> omega

/-- A place's occupancy is determined by the key. -/
theorem occupied_of_key {co : List PlaceId} {M N : NM co} (hM : (liveSet M).Finite)
    (hN : (liveSet N).Finite) (h : canonicalKey M = canonicalKey N) (i : Fin co.length) :
    (∃ s, M s i ≠ 0) ↔ (∃ s, N s i ≠ 0) := by
  obtain ⟨σ, hσ⟩ := canonicalKey_complete hM hN h
  subst hσ
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨σ.symm s, by simpa using hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨σ s, hs⟩

/-- **Retrodiction of `4d7a9d9`: the off-key rule is necessary.** The pre-fix role's
`name_successors` keep `u` in `C`; the executor's successor has `C` empty; no graph successor has
its key. -/
theorem offKey_rule_is_necessary :
    classifyT colW .base false tJ = some (Role.join [(0, 1), (1, 1)] []) ∧
    classifyT colW .base true tJ = none ∧
    ExecNames coW tJ [3] mW mW' (Contract coW (Role.join [(0, 1), (1, 1)] []) tJ mW) ∧
    ∀ c, 2 ≤ c → ∀ M'' ∈ nameSuccs coW (Role.join [(0, 1), (1, 1)] []) mW [3] 2 c,
      canonicalKey M'' ≠ canonicalKey mW' := by
  refine ⟨classify_offKey_before_after.1, classify_offKey_before_after.2, offKey_exec, ?_⟩
  intro c _ M'' hM'' hkey
  simp only [nameSuccs, List.mem_map] at hM''
  obtain ⟨s, hs, rfl⟩ := hM''
  obtain ⟨hs2, hen⟩ := mem_dsig_range hs
  have hs0 : s = 0 := by
    interval_cases s
    · rfl
    · exact absurd hen (by decide)
  subst hs0
  have hsupp : Supp (joinStep coW [(0, 1), (1, 1)] (relOut [3] []) 0 mW) 2 :=
    supp_of_local (joinStep_local _ _) mW_supp (by decide) (Nat.le_refl _)
  obtain ⟨t, ht⟩ := (occupied_of_key (liveSet_finite hsupp)
    (liveSet_finite (M := mW') (B := 0) (fun _ _ _ => rfl)) hkey ⟨2, by decide⟩).mp
    ⟨1, by decide⟩
  exact ht rfl

end OffKey

/-! ## Duplicate match keys (fixed: the builders refuse them, `dupKey_refused`) -/

section DupKey

/-- One coloured place `A = 0`; `OUT = 1`. -/
def coD : List PlaceId := [0]

/-- `J : A → OUT` with `MatchSpec` keys `[A, A]` (accepted by `MatchSpec::build`: two keys). -/
def tD : NuTrans where
  base := { name := "J", inputs := [inOne 0], inhibitors := [], reads := [], resets := [] }
  rows := [⟨[1], []⟩]
  keys := some [0, 0]
  relays := []

/-- `classify` accepts it, with `coloured_in = [(A,1),(A,1)]`, in both modes. -/
theorem classify_dupKey :
    classifyT (fun p => coD.contains p) .base true tD = some (Role.join [(0, 1), (0, 1)] []) ∧
    classifyT (fun p => coD.contains p) .extended true tD = some (Role.join [(0, 1), (0, 1)] []) := by
  constructor <;> rfl

/-- Two tokens of `s = 0` in `A`. -/
def mD : NM coD := fun u _ => if u = 0 then 2 else 0

/-- The executor consumes one token of the matched name per input spec: one left. -/
def mD' : NM coD := fun u _ => if u = 0 then 1 else 0

theorem dupKey_exec :
    ExecNames coD tD [1] mD mD' (Contract coD (Role.join [(0, 1), (0, 1)] []) tD mD) := by
  refine ⟨0, [[0]], fun _ => [], ?_, ?_, ?_, ?_, ?_, trivial, ?_⟩
  · intro _ ks hks
    cases hks
    refine ⟨by simp, fun p hp => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false, or_self] at hp
    subst hp
    exact ⟨by decide, by decide⟩
  · exact List.Forall₂.cons (by simp [SpecTakes, isKey, tD, inOne, Card.consumesAll,
      Card.required]) List.Forall₂.nil
  · intro i u
    fin_cases i
    simp [rmvList, mD, inOne, coD, tD, List.count_singleton]
    split_ifs <;> omega
  · intro i; fin_cases i; decide
  · intro _ i hi; simp [tD] at hi
  · funext u i
    fin_cases i
    simp [rmvList, mD, mD', inOne, coD, tD, List.count_singleton]
    split_ifs <;> omega

theorem mD_supp : Supp mD 1 := by
  intro s hs i
  unfold mD
  simp [show s ≠ 0 by omega]

/-- **Duplicate keys break the simulation**: the graph removes `s` twice (`remove` per key), the
executor once (per input spec); no graph successor has the executor's key. -/
theorem dupKey_breaks_simulation :
    classifyT (fun p => coD.contains p) .extended true tD = some (Role.join [(0, 1), (0, 1)] []) ∧
    ExecNames coD tD [1] mD mD' (Contract coD (Role.join [(0, 1), (0, 1)] []) tD mD) ∧
    ∀ c, 1 ≤ c → ∀ M'' ∈ nameSuccs coD (Role.join [(0, 1), (0, 1)] []) mD [1] 1 c,
      canonicalKey M'' ≠ canonicalKey mD' := by
  refine ⟨classify_dupKey.2, dupKey_exec, ?_⟩
  intro c _ M'' hM'' hkey
  simp only [nameSuccs, List.mem_map] at hM''
  obtain ⟨s, hs, rfl⟩ := hM''
  have hs0 : s < 1 := (mem_dsig_range hs).1
  have hs0' : s = 0 := by omega
  subst hs0'
  have hsupp : Supp (joinStep coD [(0, 1), (0, 1)] (relOut [1] []) 0 mD) 1 :=
    supp_of_local (joinStep_local _ _) mD_supp (by decide) (Nat.le_refl _)
  have hsupp' : Supp mD' 1 := by
    intro s hs i; unfold mD'; simp [show s ≠ 0 by omega]
  obtain ⟨t, ht⟩ := (occupied_of_key (liveSet_finite hsupp) (liveSet_finite hsupp') hkey
    ⟨0, by decide⟩).mpr ⟨0, by decide⟩
  have ht1 : t < 1 := lt_of_live hsupp ⟨_, ht⟩
  have ht0 : t = 0 := by omega
  subst ht0
  exact ht (by decide)

end DupKey

/-! ## A `Mint` that does not mint (refused unless declared, `copyingMint_refused`) -/

section CopyingMint

/-- Coloured `A = 0`, `B = 1`; uncoloured source `S = 2`. -/
def coM : List PlaceId := [0, 1]

/-- `mB : S → B`, no coloured input: `classify` calls it a `Mint`. -/
def tM : NuTrans where
  base := { name := "mB", inputs := [inOne 2], inhibitors := [], reads := [], resets := [] }
  rows := [⟨[1], []⟩]
  keys := none
  relays := []

theorem classify_mint : classifyT (fun p => coM.contains p) .base true tM = some Role.mint := rfl

/-- `s = 0` already in `A`. -/
def mM : NM coM := fun u i => if u = 0 ∧ i.1 = 0 then 1 else 0

/-- The action copies the correlation id it read (`fork()`), which is `s`: `s` is now in `B` too. -/
def mM' : NM coM := fun u _ => if u = 0 then 1 else 0

/-- The runtime rules hold (no contract): the write is one token into `B`, named `s`. -/
theorem copyingMint_exec :
    ExecNames coM tM [1] mM mM' (fun _ _ _ => True) := by
  refine ⟨0, [[7]], fun i => if i.1 = 1 then [0] else [], fun h => by simp [tM] at h, ?_, ?_, ?_,
    fun h => by simp [tM] at h, trivial, ?_⟩
  · exact List.Forall₂.cons (by simp [SpecTakes, isKey, tM, inOne, Card.consumesAll,
      Card.required]) List.Forall₂.nil
  · intro i u
    fin_cases i <;> simp [rmvList, inOne, coM, tM]
  · intro i; fin_cases i <;> decide
  · funext u i
    fin_cases i
    · simp [rmvList, mM, mM', inOne, coM, tM]
    · simp [rmvList, mM, mM', inOne, coM, tM, List.count_singleton]
      split_ifs <;> omega

/-- **The `Mint` contract is load-bearing**: the executor's successor has one symbol in both `A`
and `B`; every graph successor (a fresh symbol in `B`) has none. -/
theorem copyingMint_breaks_simulation :
    classifyT (fun p => coM.contains p) .base true tM = some Role.mint ∧
    ExecNames coM tM [1] mM mM' (fun _ _ _ => True) ∧
    ∀ c, 1 ≤ c → ∀ M'' ∈ nameSuccs coM Role.mint mM [1] 1 c,
      canonicalKey M'' ≠ canonicalKey mM' := by
  refine ⟨classify_mint, copyingMint_exec, ?_⟩
  intro c hc M'' hM'' hkey
  simp only [nameSuccs, List.mem_singleton] at hM''
  subst hM''
  have hmM : Supp mM 1 := by
    intro s hs i; unfold mM; simp [show s ≠ 0 by omega]
  have hS1 : Supp (mintStep coM (colOut coM [1]) c mM) (c + 1) :=
    supp_of_local (mintStep_local _) hmM (by omega) (by omega)
  have hS2 : Supp mM' 1 := by
    intro s hs i; unfold mM'; simp [show s ≠ 0 by omega]
  obtain ⟨σ, hσ⟩ := canonicalKey_complete (liveSet_finite hS1) (liveSet_finite hS2) hkey
  have hL : colOut coM [1] = [1] := by decide
  have hval : ∀ x (i : Fin coM.length), mintStep coM (colOut coM [1]) c mM x i =
      mM x i + if x = c ∧ coM[i.1] ∈ [1] then 1 else 0 := fun x i => by
    unfold mintStep; rw [hL]; exact foldl_add_apply (by decide) c [1] (by decide) mM x i
  have h0 : mM' 0 ⟨0, by decide⟩ = 1 := rfl
  have h1 : mM' 0 ⟨1, by decide⟩ = 1 := rfl
  rw [hσ] at h0 h1
  simp only [Function.comp] at h0 h1
  rw [hval] at h0 h1
  by_cases hs0 : σ 0 = 0
  · rw [hs0] at h0 h1
    have hc0 : (0 : ℕ) ≠ c := by omega
    simp [mM, coM, hc0] at h1
  · simp [mM, coM, hs0] at h0

end CopyingMint

/-! ## A zero-count key (fixed: the builder refuses it, `zeroKey_refused`) -/

section ZeroKey

theorem idx_isSome_eq_contains (co : List PlaceId) (p : PlaceId) :
    (idx co p).isSome = co.contains p := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  unfold idx
  rw [List.find?_isSome]
  constructor
  · rintro ⟨i, -, hi⟩
    simp only [beq_iff_eq] at hi
    rw [← hi]
    exact List.getElem_mem i.isLt
  · intro hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    exact ⟨⟨i, hi⟩, List.mem_finRange _, by simp⟩

/-- Coloured `A = 0`, `B = 1`; `OUT = 2`. -/
def coZ : List PlaceId := [0, 1]

def inZero (p : PlaceId) : InSpec := { place := p, card := .exactly 0, guard := none }

/-- `J : A, B → OUT` keyed on `A`, `B`, where `B`'s input spec is `In::Exactly { count: 0 }`
(a public enum variant; only the `exactly()` helper asserts `count ≥ 1`). -/
def tZ : NuTrans where
  base := { name := "J", inputs := [inOne 0, inZero 1], inhibitors := [], reads := [],
            resets := [] }
  rows := [⟨[2], []⟩]
  keys := some [0, 1]
  relays := []

def roleZ (_ : NuTrans) : Role := .join [(0, 1), (1, 0)] []

/-- `classify` accepts it: `coloured_in = [(A,1),(B,0)]`. -/
theorem classify_zeroKey :
    classifyT (fun p => coZ.contains p) .extended true tZ = some (roleZ tZ) := by
  decide

/-- Name `0` in `A`; `B` empty. -/
def mZ : CMarking := fun p => if p = 0 then [0] else []

theorem cnt_mZ_B (n : ℕ) : cnt coZ (nameLayer coZ id mZ) n 1 = 0 := by
  unfold cnt
  rw [show idx coZ 1 = some ⟨1, by decide⟩ from by decide]
  simp [nameLayer, mZ, coZ]

/-- With every key count at least one, `joinEnab` is "every key place holds the required count":
the presence test on the head of `cin` follows from the head's own count. -/
theorem joinEnab_eq_all_of_pos {co : List PlaceId} {cin : List (PlaceId × ℕ)} (hne : cin ≠ [])
    (hpos : ∀ pr ∈ cin, 1 ≤ pr.2) (M : NM co) (s : ℕ) :
    joinEnab co cin M s = cin.all fun pr => decide (pr.2 ≤ cnt co M s pr.1) := by
  cases cin with
  | nil => exact absurd rfl hne
  | cons p0 rest =>
    obtain ⟨p, r⟩ := p0
    simp only [joinEnab]
    by_cases hall : ((p, r) :: rest).all (fun pr => decide (pr.2 ≤ cnt co M s pr.1)) = true
    · rw [hall]
      have h1 := List.all_eq_true.mp hall (p, r) List.mem_cons_self
      have h2 := hpos (p, r) List.mem_cons_self
      simp only [decide_eq_true_eq] at h1 h2
      simp only [Bool.and_true, bne_iff_ne, ne_eq]
      omega
    · rw [Bool.not_eq_true] at hall
      rw [hall, Bool.and_false]

/-- **Key order is irrelevant under `PosKeys`**: `joinEnab` reads `cin` only as a set when every
key consumes at least one token, so the model's key order and the Rust's name-sorted
`coloured_in` give the same enabling symbols. -/
theorem joinEnab_perm_of_pos {co : List PlaceId} {cin cin' : List (PlaceId × ℕ)}
    (hp : cin.Perm cin') (hpos : ∀ pr ∈ cin, 1 ≤ pr.2) (M : NM co) (s : ℕ) :
    joinEnab co cin M s = joinEnab co cin' M s := by
  cases cin with
  | nil => rw [hp.nil_eq]
  | cons pr rest =>
    have hne' : cin' ≠ [] := fun h => by
      rw [h] at hp
      exact List.cons_ne_nil _ _ (List.Perm.eq_nil hp)
    rw [joinEnab_eq_all_of_pos (List.cons_ne_nil _ _) hpos,
      joinEnab_eq_all_of_pos hne' (fun q hq => hpos q (hp.mem_iff.mpr hq))]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    exact ⟨fun h q hq => h q (hp.mem_iff.mpr hq), fun h q hq => h q (hp.mem_iff.mp hq)⟩

/-- **Key order matters without `PosKeys`.** `joinEnab`, like `enabling_symbols`, draws its
candidates from the head of `cin` (`symbols_in(first_place)`) and asks the other keys only for
`count ≥ required`. On the same layer (name `0` in `A`, `B` empty) the zero-count key on `B`
admits name `0` when `B` is second and rejects it when `B` is first. The Rust sorts
`coloured_in` by place name, so which zero-count key escapes the presence test is decided by
place names. -/
theorem zeroKey_order_matters :
    joinEnab coZ [(0, 1), (1, 0)] (nameLayer coZ id mZ) 0 = true ∧
    joinEnab coZ [(1, 0), (0, 1)] (nameLayer coZ id mZ) 0 = false := by
  decide

/-- **A zero-count key breaks the quiescence half.** `classify` accepts `J` and every fragment
premise holds (`classifyT_inFragment`), but the key spec on `B` consumes zero tokens. With a
name in `A` and `B` empty the executor is quiescent (`select_match_name` needs the name present
in every key place), while `enabling_symbols`, seeded from the head `A` of `coloured_in`, asks
only `count ≥ 0` of `B` and the class has a successor. `B` sorts after `A` by name too, so the
Rust's `coloured_in` has the same order (the repro before the builder fix); with the zero-count key at the head
the presence test would still apply to it (`zeroKey_order_matters`). So a `DeadlockFree` `Proven` can miss the executor's deadlock; under `Conflict` the
same `will_fire` over-approximation can also prune a lower-priority firing the executor makes.
`PosKeys` is the premise that rules this out. -/
theorem zeroKey_breaks_quiescence :
    classifyT (fun p => coZ.contains p) .extended true tZ = some (roleZ tZ) ∧
    InFragment coZ tZ (roleZ tZ) ∧ ¬ PosKeys (roleZ tZ) ∧
    ExecQuiescent (co := coZ) (nameOf := id) (net := [tZ]) mZ ∧
    (succ untimedBase [tZ] roleZ false (view coZ id mZ).bound (view coZ id mZ)).isEmpty = false := by
  refine ⟨classify_zeroKey, ?_, ?_, ?_, by decide⟩
  · refine classifyT_inFragment (fun p => (idx_isSome_eq_contains coZ p).symm) classify_zeroKey
      ?_ ?_ ?_ <;> intro ks hks <;> cases hks
    · intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> rfl
    · decide
    · intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> decide
  · intro h
    have := h _ _ rfl (1, 0) (by simp)
    omega
  · intro T hT hen
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT
    subst hT
    obtain ⟨n, hn⟩ := hen.2 [0, 1] rfl
    have := ((hn [0, 1] rfl).2 1 (by simp)).1
    rw [cnt_mZ_B] at this
    omega

end ZeroKey


/-! ## `classify` as shipped: declared mints, timeout writes, and the builders' checks

The shipped `classify` (`name_fragment.rs`) takes a fourth argument, `mints`, the declared
mint transitions (`declared_mints`: named by the caller, or consuming a declared budget place,
[NU-010]), and reads `branch_outcomes::timeout_writes`, what the executor itself writes on
timeout (`TimeoutWrite::Unit`, a unit token, or `TimeoutWrite::Forward(from)`, a copy of what it
took from `from`). On top of `classifyT` with the off-key rule:

* a transition `classifyT` calls a `Mint` stays one only when it is declared and its timeout
  writes no coloured place (`classifyS_mint`); otherwise the net is refused;
* a `Consume` (EXTENDED) stays one only when each of its coloured timeout writes forwards the
  coloured input it consumes (`classifyS_consume`);
* a `Join` stays one only when each of its coloured timeout writes forwards one of its match keys
  (`classifyS_join`). Its coloured writes are relay targets, whose deposits the executor checks
  ([NU-054]): a unit token or a forward of another input fails the firing, which deposits nothing,
  while the relay step would add the matched name.

The `Mint` contract of `NuStepC` is therefore a declared premise: `classifyS` never reads an
undeclared writer as a mint (`classifyS_undeclared`), so the copying `fork()` of
`copyingMint_breaks_simulation` is refused unless the net declares it (`copyingMint_refused`);
what a declared mint's action writes stays unchecked, which the report states ("Mint contract
(NU-010) assumed for ..."). A timeout deposit is never fresh, never a name the consumer did not
take, and never a relay token without the matched name, so the contracts are never assumed of
what the executor writes on timeout.

The builders now reject two shapes `classifyT` accepts (`BuilderOK`): `MatchSpecBuilder::build`
and `TransitionBuilder::build` panic on a place keyed twice (`match_spec.rs::duplicate_key`,
[NU-020]), and `TransitionBuilder::build` on an input that requires zero tokens ([IO-002],
[IO-004]) and, as before, on two input specs on one place ([CORE-030] AC3). So the distinct-keys
condition and `PosKeys`, which the theorems take as hypotheses, hold of every transition the
Rust can build (`classifyS_inFragment`, `builderOK_posKeys`), and the witnesses `tD`
(`dupKey_breaks_simulation`) and `tZ` (`zeroKey_breaks_quiescence`) cannot be built
(`dupKey_refused`, `zeroKey_refused`).
-/

section Shipped

/-- `branch_outcomes::TimeoutWrite`. -/
inductive TW where
  | unit
  | forward (src : PlaceId)
  deriving DecidableEq

variable (col : PlaceId → Bool)

/-- `classify` as shipped for one transition: `declared` is `mints.contains(t.name())`, `tw` is
`timeout_writes(t)`. -/
def classifyS (mode : Mode) (declared : Bool) (tw : List (PlaceId × TW)) (T : NuTrans) :
    Option Role :=
  match classifyT col mode true T with
  | some Role.mint =>
    if declared && tw.all (fun w => !col w.1) then some Role.mint else none
  | some (Role.consume p) =>
    if tw.all (fun w => !col w.1 || w.2 == TW.forward p) then some (Role.consume p) else none
  | some (Role.join cin rel) =>
    if tw.all (fun w => !col w.1 || cin.any (fun k => w.2 == TW.forward k.1))
    then some (Role.join cin rel) else none
  | r => r

variable {col}

/-- The shipped rules only refuse more: what `classifyS` accepts, `classifyT` accepts with the
same role. -/
theorem classifyS_sub {mode : Mode} {declared : Bool} {tw : List (PlaceId × TW)} {T : NuTrans}
    {r : Role} (h : classifyS col mode declared tw T = some r) :
    classifyT col mode true T = some r := by
  unfold classifyS at h
  split at h
  · rename_i h1
    split_ifs at h
    cases h
    exact h1
  · rename_i p h1
    split_ifs at h
    cases h
    exact h1
  · rename_i cin rel h1
    split_ifs at h
    cases h
    exact h1
  · exact h

/-- **A mint is declared and writes no coloured place on timeout.** -/
theorem classifyS_mint {mode : Mode} {declared : Bool} {tw : List (PlaceId × TW)} {T : NuTrans}
    (h : classifyS col mode declared tw T = some Role.mint) :
    declared = true ∧ ∀ w ∈ tw, col w.1 = false := by
  have h1 := classifyS_sub h
  unfold classifyS at h
  rw [h1] at h
  simp only at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hc
  exact ⟨hc.1, hc.2⟩

/-- **An undeclared transition is never a mint.** -/
theorem classifyS_undeclared {mode : Mode} {tw : List (PlaceId × TW)} {T : NuTrans} :
    classifyS col mode false tw T ≠ some Role.mint := fun h => by
  have := (classifyS_mint h).1
  exact Bool.false_ne_true this

/-- **A consumer's coloured timeout writes forward its consumed input.** -/
theorem classifyS_consume {mode : Mode} {declared : Bool} {tw : List (PlaceId × TW)}
    {T : NuTrans} {p : PlaceId} (h : classifyS col mode declared tw T = some (Role.consume p)) :
    ∀ w ∈ tw, col w.1 = true → w.2 = TW.forward p := by
  have h1 := classifyS_sub h
  unfold classifyS at h
  rw [h1] at h
  simp only at h
  split_ifs at h with hc
  intro w hw hcw
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
  rcases hc w hw with h' | h'
  · rw [hcw] at h'; exact absurd h' (by simp)
  · exact h'

/-- **A join's coloured timeout writes forward one of its match keys.** The executor checks
every relay deposit ([NU-054]) and fails the firing on a unit token or another input's name, so
this is the one timeout write the relay step describes. -/
theorem classifyS_join {mode : Mode} {declared : Bool} {tw : List (PlaceId × TW)}
    {T : NuTrans} {cin : List (PlaceId × ℕ)} {rel : List PlaceId}
    (h : classifyS col mode declared tw T = some (Role.join cin rel)) :
    ∀ w ∈ tw, col w.1 = true → ∃ k ∈ cin, w.2 = TW.forward k.1 := by
  have h1 := classifyS_sub h
  unfold classifyS at h
  rw [h1] at h
  simp only at h
  split_ifs at h with hc
  intro w hw hcw
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
    beq_iff_eq] at hc
  rcases hc w hw with h' | h'
  · rw [hcw] at h'; exact absurd h' (by simp)
  · exact h'

/-- What the Rust builders assert of every transition they return. -/
structure BuilderOK (T : NuTrans) : Prop where
  /-- `duplicate_key`: no place keyed twice ([NU-020]). -/
  keysNodup : ∀ ks, T.keys = some ks → ks.Nodup
  /-- No input requires zero tokens ([IO-002], [IO-004]). -/
  posInputs : ∀ s ∈ T.base.inputs, 1 ≤ s.card.required
  /-- At most one input spec per place ([CORE-030] AC3). -/
  onePerPlace : ∀ p, (T.base.inputs.filter fun s => s.place == p).length ≤ 1

/-- **`classifyS` puts a buildable transition in the fragment** with no join condition left to
assume: distinct keys and one spec per key place are the builders' checks. -/
theorem classifyS_inFragment {co : List PlaceId} (hcol : ∀ p, col p = (idx co p).isSome)
    {mode : Mode} {declared : Bool} {tw : List (PlaceId × TW)} {T : NuTrans} {r : Role}
    (h : classifyS col mode declared tw T = some r) (hB : BuilderOK T)
    (hkc : ∀ ks, T.keys = some ks → ∀ p ∈ ks, col p = true) : InFragment co T r :=
  classifyT_inFragment hcol (classifyS_sub h) hkc hB.keysNodup fun _ _ p _ => hB.onePerPlace p

/-- **`PosKeys` holds of every buildable join** in the fragment. -/
theorem builderOK_posKeys {co : List PlaceId} {T : NuTrans} {r : Role} (hB : BuilderOK T)
    (h : InFragment co T r) : PosKeys r := by
  intro cin rel hr pr hpr
  subst hr
  obtain ⟨-, -, -, -, -, hcin, -⟩ := h
  obtain ⟨-, s, hs, hfc⟩ := hcin pr hpr
  have hmem : s ∈ T.base.inputs := (List.mem_filter.mp (hs ▸ List.mem_singleton_self s)).1
  have hreq := hB.posInputs s hmem
  rcases hfc with ⟨-, h1⟩ | h2
  · omega
  · rw [h2] at hreq
    exact hreq

/-- **The duplicate-key witness cannot be built** (`match_spec.rs::duplicate_key`). -/
theorem dupKey_refused : ¬ BuilderOK tD := fun h => by
  have := h.keysNodup [0, 0] rfl
  simp at this

/-- **The zero-count witness cannot be built** (`TransitionBuilder::build`). -/
theorem zeroKey_refused : ¬ BuilderOK tZ := fun h => by
  have := h.posInputs (inZero 1) (by simp [tZ])
  simp [inZero, Card.required] at this

/-- **The copying mint is refused unless declared.** `classifyT` calls `tM` a `Mint`; the shipped
`classify` refuses it without the declaration, whatever it writes on timeout. -/
theorem copyingMint_refused (tw : List (PlaceId × TW)) :
    classifyS (fun p => coM.contains p) .base false tw tM = none := by
  unfold classifyS
  rw [classify_mint]
  simp

end Shipped

end Libpetri.Novel.RouteB
