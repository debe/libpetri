import Libpetri.Novel.RouteA.Simulate

/-!
# Route A: `build_plan` and `colour_slot_bound`

A model of the two functions of `name_coloured_encoder.rs` that decide whether Route A runs and
with how many colour slots, and the proof that whatever they return discharges the plan
premises of `Simulate.lean`:

* `colourSlotBound` — `colour_slot_bound`: the tightest `y·M₀` over the non-negative laws that
  weight every coloured place `≥ 1`; otherwise the sum of the zero-constant laws and of every
  positive-constant law that touches a coloured place the zero-constant ones left uncovered,
  if that covers every coloured place; otherwise `None`. `colourSlotBound_sound`: the result
  is `y·M₀` for a non-negative weighting `y` that covers every coloured place and annihilates
  every flat row — the `cover` premise.
* `classifyRow` — the classification branch of `build_plan` for one flat row, and
  `classifyRow_ok`: an accepted row has the incidence its class promises (`ClassOK`).
* `buildPlan`, `buildPlan_premises`: the whole function, and the `Premises` of
  `coloured_simulates` from its `Some`, given the facts about the inputs that `build_plan`
  receives rather than checks (the validated laws, the seed, guard-freeness) — and
  `ConsumeNoSelfLoop`, which it **neither receives nor checks**.

What is not modelled: the coloured set's computation from names (the match keys, the declared
carriers and relay targets are resolved through `place_index`); `C` is taken as given, sorted
and duplicate-free as `(0..p).filter(..)` makes it. The `source` mapping of flat rows back to
transitions is taken as given (`SrcRow.ms`), with the Rust's defensive length check.
-/

namespace Libpetri.Novel.RouteA

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.LinearBound

/-! ## `colour_slot_bound` -/

/-- A `PInvariant` as `colour_slot_bound` reads it: its weights and its `constant`. -/
structure Law where
  y : Weight
  c : Int

/-- `is_semiflow`: every weight of the (length `place_count`) vector is non-negative. -/
def isSemi (n : Nat) (l : Law) : Bool := (List.range n).all fun p => decide (0 ≤ l.y p)

/-- Every coloured place has weight at least one. -/
def coversAll (C : List PlaceId) (l : Law) : Bool := C.all fun p => decide (1 ≤ l.y p)

/-- `colour_slot_bound` (`name_coloured_encoder.rs`). `c as usize` is `Int.toNat`; the
constant of a validated semi-positive law is `y·M₀ ≥ 0`, so nothing is truncated. -/
def colourSlotBound (n : Nat) (C : List PlaceId) (laws : List Law) : Option Nat :=
  let semis := laws.filter (isSemi n)
  match ((semis.filter (coversAll C)).map Law.c).min? with
  | some c => some c.toNat
  | none =>
    let free := semis.filter fun l => l.c == 0
    let freeCov : PlaceId → Bool := fun p => free.any fun l => decide (1 ≤ l.y p)
    let sel := semis.filter fun l =>
      l.c != 0 && C.any fun p => !freeCov p && decide (1 ≤ l.y p)
    if C.all (fun p => freeCov p || sel.any fun l => decide (1 ≤ l.y p)) then
      some ((sel.map Law.c).sum).toNat
    else none

/-- What `validate_invariants_exact` establishes of every law it lets through: the exact
`y·C = 0` against the flat rows (integer posts) and `constant = y·M₀`. -/
structure LawValid (rows : List (Transition × Deposit)) (n : Nat) (a0 : AMarking) (l : Law) :
    Prop where
  col : ∀ tr ∈ rows, dotIncD l.y tr n = 0
  const : l.c = dot l.y a0 n

/-- The pointwise sum of a list of weight vectors (the sum of semiflows the Rust adds up). -/
def wsum (S : List Law) : Weight := fun p => (S.map fun l => l.y p).sum

theorem isum_wsum (S : List Law) (g : PlaceId → Int) (n : Nat) :
    isum (fun p => wsum S p * g p) n = (S.map fun l => isum (fun p => l.y p * g p) n).sum := by
  induction S with
  | nil => simp [wsum, isum]
  | cons l S ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih, ← isum_add]
    refine isum_congr fun p _ => ?_
    simp [wsum, add_mul]

theorem dot_wsum (S : List Law) (a : AMarking) (n : Nat) :
    dot (wsum S) a n = (S.map fun l => dot l.y a n).sum := by
  rw [dot_eq_isum, isum_wsum]
  congr 1
  exact List.map_congr_left fun l _ => (dot_eq_isum l.y a n).symm

theorem dotIncD_wsum (S : List Law) (tr : Transition × Deposit) (n : Nat) :
    dotIncD (wsum S) tr n = (S.map fun l => dotIncD l.y tr n).sum := by
  unfold dotIncD
  exact isum_wsum S _ n

theorem dot_nonneg_of {y : Weight} {a : AMarking} {n : Nat} (hy : ∀ p, p < n → 0 ≤ y p) :
    0 ≤ dot y a n := by
  rw [dot_eq_isum]
  exact Finset.sum_nonneg fun p hp =>
    Int.mul_nonneg (hy p (Finset.mem_range.mp hp)) (Int.natCast_nonneg _)

theorem isSemi_spec {n : Nat} {l : Law} (h : isSemi n l = true) : ∀ p, p < n → 0 ≤ l.y p := by
  intro p hp
  unfold isSemi at h
  rw [List.all_eq_true] at h
  simpa using h p (List.mem_range.mpr hp)

theorem list_sum_eq_zero {S : List Law} {f : Law → Int} (h : ∀ l ∈ S, f l = 0) :
    (S.map f).sum = 0 := by
  induction S with
  | nil => rfl
  | cons l S ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h l List.mem_cons_self, ih fun l' hl' => h l' (List.mem_cons_of_mem l hl')]
    rfl

/-- **`colour_slot_bound` is sound.** Whatever it returns is `y·M₀` for a weighting that is
non-negative, weights every coloured place at least one, and annihilates every flat row — the
`cover` premise of `coloured_simulates` (with `y·C = 0 ≤ 0`). -/
theorem colourSlotBound_sound {n : Nat} {C : List PlaceId} {laws : List Law}
    {rows : List (Transition × Deposit)} {a0 : AMarking} {k : Nat}
    (hC : ∀ p ∈ C, p < n) (hv : ∀ l ∈ laws, LawValid rows n a0 l) (h : colourSlotBound n C laws = some k) :
    ∃ y : Weight, (∀ p, p < n → 0 ≤ y p) ∧ (∀ p ∈ C, 1 ≤ y p) ∧
      (∀ tr ∈ rows, dotIncD y tr n = 0) ∧ dot y a0 n = k := by
  unfold colourSlotBound at h
  simp only at h
  split at h
  · rename_i c hmin
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.min?_mem hmin)
    obtain ⟨hl1, hcov⟩ := List.mem_filter.mp hl
    obtain ⟨hlaw, hsemi⟩ := List.mem_filter.mp hl1
    have hpos := isSemi_spec hsemi
    have hc : l.c = dot l.y a0 n := (hv l hlaw).const
    have hc0 : 0 ≤ l.c := hc ▸ dot_nonneg_of hpos
    refine ⟨l.y, hpos, fun p hp => ?_, (hv l hlaw).col, ?_⟩
    · unfold coversAll at hcov
      rw [List.all_eq_true] at hcov
      simpa using hcov p hp
    · cases h
      rw [← hc]
      omega
  · split at h
    · rename_i hall
      cases h
      set free := (laws.filter (isSemi n)).filter fun l => l.c == 0
      set sel := (laws.filter (isSemi n)).filter fun l =>
        l.c != 0 && C.any fun p =>
          !(free.any fun l => decide (1 ≤ l.y p)) && decide (1 ≤ l.y p)
      have hsemiS : ∀ l ∈ free ++ sel, l ∈ laws ∧ isSemi n l = true := by
        intro l hl
        rcases List.mem_append.mp hl with h' | h'
        · exact List.mem_filter.mp (List.mem_filter.mp h').1
        · exact List.mem_filter.mp (List.mem_filter.mp h').1
      have hposS : ∀ l ∈ free ++ sel, ∀ p, p < n → 0 ≤ l.y p :=
        fun l hl => isSemi_spec (hsemiS l hl).2
      refine ⟨wsum (free ++ sel), fun p hp => ?_, fun p hp => ?_, fun tr htr => ?_, ?_⟩
      · exact List.sum_nonneg fun x hx => by
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
          exact hposS l hl p hp
      · have hpn := hC p hp
        rw [List.all_eq_true] at hall
        have hex := hall p hp
        simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at hex
        obtain ⟨l, hl, h1⟩ : ∃ l ∈ free ++ sel, 1 ≤ l.y p := by
          rcases hex with ⟨l, hl, h1⟩ | ⟨l, hl, h1⟩
          · exact ⟨l, List.mem_append_left _ hl, h1⟩
          · exact ⟨l, List.mem_append_right _ hl, h1⟩
        have hle := List.single_le_sum (l := (free ++ sel).map fun l => l.y p)
          (fun x hx => by
            obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hx
            exact hposS l' hl' p hpn)
          (l.y p) (List.mem_map.mpr ⟨l, hl, rfl⟩)
        exact le_trans h1 hle
      · rw [dotIncD_wsum]
        exact list_sum_eq_zero fun l hl => (hv l (hsemiS l hl).1).col tr htr
      · rw [dot_wsum]
        have hfree : (free.map fun l => dot l.y a0 n).sum = 0 :=
          list_sum_eq_zero fun l hl => by
            have := (List.mem_filter.mp hl).2
            rw [← (hv l (List.mem_filter.mp (List.mem_filter.mp hl).1).1).const]
            simpa using this
        have hsel : (sel.map fun l => dot l.y a0 n) = sel.map Law.c :=
          List.map_congr_left fun l hl =>
            ((hv l (List.mem_filter.mp (List.mem_filter.mp hl).1).1).const).symm
        have hnn : 0 ≤ (sel.map Law.c).sum := List.sum_nonneg fun x hx => by
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
          have hl' := List.mem_filter.mp (List.mem_filter.mp hl).1
          rw [(hv l hl'.1).const]
          exact dot_nonneg_of (isSemi_spec hl'.2)
        rw [List.map_append, List.sum_append, hfree, hsel]
        omega
    · exact absurd h (by simp)

/-! ## The classification branch of `build_plan` -/

/-- What `build_plan` reads from a flat row's source transition: `match_spec()`'s key places and
(EXTENDED) relay targets, resolved to flat indices. -/
structure MatchInfo where
  keys : List PlaceId
  relays : List PlaceId

/-- The classification of one flat row (`build_plan`, step 2): `coloured_in` / `coloured_out`
are the coloured places with `pre > 0` / `post > 0`, read off the row's own incidence. The two
contract gates are parameters: `mintOk` decides whether a row with coloured outputs and no
coloured input may be a `Mint`, `consOk i` whether a consumer of `i` may be a `Consume`. The
shipped `build_plan` and the one before the NU-010 fix differ only in them (`classifyRow`,
`classifyRowS`). -/
def classifyRowG (C : List PlaceId) (ext : Bool) (mintOk : Bool) (consOk : PlaceId → Bool)
    (ms : Option MatchInfo) (t : Transition) (d : Deposit) : Option Cls :=
  let cin := C.filter fun p => decide (0 < pre t p)
  let cout := C.filter fun p => decide (0 < d.count p)
  match ms with
  | some mi =>
    if cin = [] then none
    else if cout.any (fun p => !ext || !mi.relays.contains p || d.count p != 1) then none
    else if cin.any (fun p => !mi.keys.contains p) then none
    else if cin.any (fun p => pre t p != 1) then none
    else some (.join cin cout)
  | none =>
    if cin ≠ [] then
      if !ext then none
      else
        match cin with
        | [i] =>
          if pre t i != 1 then none
          else if cout.any (fun p => d.count p != 1) then none
          else if !consOk i then none
          else some (.consume i cout)
        | _ => none
    else if cout ≠ [] then
      if cout.any (fun p => d.count p != 1) then none
      else if !mintOk then none
      else some (.mint cout)
    else some .untouched

/-- The row classification before the NU-010 fix: a row with coloured outputs and no coloured
input is a `Mint` as soon as it consumes a budget token, and every consumer is kept. -/
def classifyRow (C : List PlaceId) (ext : Bool) (budget : List PlaceId) (ms : Option MatchInfo)
    (t : Transition) (d : Deposit) : Option Cls :=
  classifyRowG C ext (decide (1 ≤ (budget.map (pre t)).sum)) (fun _ => true) ms t d

theorem mem_cin {C : List PlaceId} {f : PlaceId → Nat} {p : PlaceId} :
    p ∈ C.filter (fun q => decide (0 < f q)) ↔ p ∈ C ∧ 0 < f p := by
  simp [List.mem_filter]

/-- An accepted row has the coloured incidence its class promises, whatever the gates. -/
theorem classifyRowG_ok {C : List PlaceId} {ext : Bool} {mintOk : Bool}
    {consOk : PlaceId → Bool} {ms : Option MatchInfo} {t : Transition} {d : Deposit} {cls : Cls}
    (h : classifyRowG C ext mintOk consOk ms t d = some cls) : ClassShape C ⟨t, d, cls⟩ := by
  have hin0 : ∀ p ∈ C, p ∉ C.filter (fun q => decide (0 < pre t q)) → pre t p = 0 :=
    fun p hp hn => by
      by_contra hne
      exact hn (mem_cin.mpr ⟨hp, Nat.pos_of_ne_zero hne⟩)
  have hout0 : ∀ p ∈ C, p ∉ C.filter (fun q => decide (0 < d.count q)) → d.count p = 0 :=
    fun p hp hn => by
      by_contra hne
      exact hn (mem_cin.mpr ⟨hp, Nat.pos_of_ne_zero hne⟩)
  unfold classifyRowG at h
  cases ms with
  | some mi =>
    simp only at h
    split at h
    · exact absurd h (by simp)
    rename_i hne
    split at h
    · exact absurd h (by simp)
    rename_i hout
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    rename_i hpre
    cases h
    simp only [List.any_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, not_exists, not_and,
      not_or, Bool.not_eq_true', Bool.not_eq_false] at hout hpre
    refine ⟨hne, fun p hp => (mem_cin.mp hp).1, fun p hp => (mem_cin.mp hp).1,
      fun p hp => ⟨?_, ?_⟩⟩
    · by_cases hi : p ∈ C.filter (fun q => decide (0 < pre t q))
      · rw [if_pos hi]
        exact Classical.byContradiction (hpre p hi)
      · rw [if_neg hi]
        exact hin0 p hp hi
    · by_cases ho : p ∈ C.filter (fun q => decide (0 < d.count q))
      · rw [if_pos ho]
        exact Classical.byContradiction (hout p ho).2
      · rw [if_neg ho]
        exact hout0 p hp ho
  | none =>
    simp only at h
    split at h
    · rename_i hne
      split at h
      · exact absurd h (by simp)
      split at h
      · rename_i i hi
        split at h
        · exact absurd h (by simp)
        rename_i hpi
        split at h
        · exact absurd h (by simp)
        rename_i hout
        split at h
        · exact absurd h (by simp)
        cases h
        simp only [List.any_eq_true, bne_iff_ne, ne_eq, not_exists, not_and, not_not]
          at hout hpi
        have hiC : i ∈ C := (mem_cin.mp (hi ▸ List.mem_singleton_self i)).1
        refine ⟨hiC, fun p hp => (mem_cin.mp hp).1, fun p hp => ⟨?_, ?_⟩⟩
        · by_cases hpe : p = i
          · subst hpe
            rw [if_pos rfl]
            exact hpi
          · rw [if_neg hpe]
            refine hin0 p hp fun hm => hpe ?_
            rw [hi] at hm
            exact List.mem_singleton.mp hm
        · by_cases ho : p ∈ C.filter (fun q => decide (0 < d.count q))
          · rw [if_pos ho]
            exact hout p ho
          · rw [if_neg ho]
            exact hout0 p hp ho
      · exact absurd h (by simp)
    · rename_i hne
      simp only [ne_eq, not_not] at hne
      split at h
      · rename_i hcne
        split at h
        · exact absurd h (by simp)
        rename_i hout
        split at h
        · exact absurd h (by simp)
        cases h
        simp only [List.any_eq_true, bne_iff_ne, ne_eq, not_exists, not_and, not_not] at hout
        refine ⟨hcne, fun p hp => (mem_cin.mp hp).1, fun p hp => ⟨?_, ?_⟩⟩
        · exact hin0 p hp (by rw [hne]; exact List.not_mem_nil)
        · by_cases ho : p ∈ C.filter (fun q => decide (0 < d.count q))
          · rw [if_pos ho]
            exact hout p ho
          · rw [if_neg ho]
            exact hout0 p hp ho
      · rename_i hcne
        simp only [ne_eq, not_not] at hcne
        cases h
        intro p hp
        exact ⟨hin0 p hp (by rw [hne]; exact List.not_mem_nil),
          hout0 p hp (by rw [hcne]; exact List.not_mem_nil)⟩

/-! ## `build_plan` -/

/-- The refusal of any reset, consume-all, inhibitor or read arc on a coloured place. -/
def arcsOK (C : List PlaceId) (t : Transition) : Bool :=
  C.all fun p => !t.resets.contains p && !consumeAllAt t p && !t.inhibitors.contains p &&
    !t.reads.contains p

theorem arcsOK_spec {C : List PlaceId} {t : Transition} (h : arcsOK C t = true) :
    NoTestArcs C t := by
  intro p hp
  unfold arcsOK at h
  rw [List.all_eq_true] at h
  have := h p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  refine ⟨h1, h2, fun hm => ?_, fun hm => ?_⟩
  · have : t.inhibitors.contains p = true := List.contains_iff_mem.mpr hm
    rw [this] at h3
    exact Bool.noConfusion h3
  · have : t.reads.contains p = true := List.contains_iff_mem.mpr hm
    rw [this] at h4
    exact Bool.noConfusion h4

/-- A flat row as `build_plan` receives it: the flat transition and its source's match
information (`source[i].match_spec()`). -/
structure SrcRow where
  t : Transition
  d : Deposit
  ms : Option MatchInfo
  /-- `mints.contains(t.name())`: the source transition is a declared mint ([NU-010]). -/
  declared : Bool
  /-- `branch_outcomes::timeout_writes` of the source transition: each place its timeout writes,
  with `some from` for a `TimeoutWrite::Forward(from)` and `none` for a `TimeoutWrite::Unit`. -/
  tw : List (PlaceId × Option PlaceId)

def SrcRow.flat (s : SrcRow) : Transition × Deposit := (s.t, s.d)

/-- The gates of a classification rule, per source row: may it be a `Mint`, and may it consume
a given coloured place as a `Consume`. -/
abbrev Gate := SrcRow → Bool × (PlaceId → Bool)

/-- Step 2 over all rows; any refusal refuses the plan. -/
def classifyAllG (C : List PlaceId) (ext : Bool) (g : Gate) :
    List SrcRow → Option (List CRow)
  | [] => some []
  | s :: ss =>
    match classifyRowG C ext (g s).1 (g s).2 s.ms s.t s.d, classifyAllG C ext g ss with
    | some cls, some rows => some (⟨s.t, s.d, cls⟩ :: rows)
    | _, _ => none

/-- The gates before the NU-010 fix: a mint needs one budget token, a consumer nothing. -/
def budgetGate (budget : List PlaceId) : Gate :=
  fun s => (decide (1 ≤ (budget.map (pre s.t)).sum), fun _ => true)

/-- The shipped gates (`build_plan`): a `Mint` must be declared and its timeout must write no
coloured place; a `Consume` of `i` must forward `i` in every coloured timeout write. The Rust
also refuses a `Join` whose coloured timeout write is not a forward of one of its match keys
([NU-054]); that refusal is not modelled here and only makes the shipped plan refuse more. -/
def shippedGate (C : List PlaceId) : Gate :=
  fun s => (s.declared && s.tw.all (fun w => !C.contains w.1),
    fun i => s.tw.all fun w => !C.contains w.1 || w.2 == some i)

theorem classifyAll_spec {C : List PlaceId} {ext : Bool} {g : Gate} :
    ∀ {src : List SrcRow} {rows : List CRow}, classifyAllG C ext g src = some rows →
      rows.map CRow.flat = src.map SrcRow.flat ∧
        ∀ r ∈ rows, ∃ s ∈ src, r.t = s.t ∧ r.d = s.d ∧ ClassShape C r
  | [], rows, h => by
    simp only [classifyAllG, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun r hr => absurd hr List.not_mem_nil⟩
  | s :: ss, rows, h => by
    simp only [classifyAllG] at h
    split at h
    · rename_i cls rs hcls hrs
      cases h
      obtain ⟨hmap, hall⟩ := classifyAll_spec hrs
      refine ⟨by simp [hmap, CRow.flat, SrcRow.flat], fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨s, List.mem_cons_self, rfl, rfl, classifyRowG_ok hcls⟩
      · obtain ⟨s', hs', h1, h2, h3⟩ := hall r hr
        exact ⟨s', List.mem_cons_of_mem s hs', h1, h2, h3⟩
    · exact absurd h (by simp)

/-- `build_plan` (`name_coloured_encoder.rs`), from the coloured set on, with the gates `g`. -/
def buildPlanG (n : Nat) (C : List PlaceId) (ext : Bool) (g : Gate) (a0 : AMarking)
    (laws : List Law) (src : List SrcRow) : Option (Nat × List CRow) :=
  if C = [] then none
  else if C.any (fun p => a0 p != 0) then none
  else
    match colourSlotBound n C laws with
    | none => none
    | some k =>
      if k = 0 ∧ C.length = n then none
      else if src.any (fun s => !arcsOK C s.t) then none
      else (classifyAllG C ext g src).map fun rows => (k, rows)

/-- **`build_plan` as shipped**: the gates of `shippedGate` (declared mints, timeout writes). -/
def buildPlan (n : Nat) (C : List PlaceId) (ext : Bool) (a0 : AMarking) (laws : List Law)
    (src : List SrcRow) : Option (Nat × List CRow) :=
  buildPlanG n C ext (shippedGate C) a0 laws src

/-- `build_plan` before the NU-010 fix: a budget token made a mint (`budgetGate`). -/
def buildPlanBudget (n : Nat) (C : List PlaceId) (ext : Bool) (budget : List PlaceId)
    (a0 : AMarking) (laws : List Law) (src : List SrcRow) : Option (Nat × List CRow) :=
  buildPlanG n C ext (budgetGate budget) a0 laws src

/-- `Premises` without `noSelfLoop`: what a plan `build_plan` returns and the verifier's other
checks establish. The shipped encoder needs nothing more (`RouteA/Shipped.lean`,
`premises_shipped`). -/
structure PremisesS (E : Enc) (m0 : CMarking) : Prop where
  nodup : E.C.Nodup
  below : ∀ p ∈ E.C, p < E.n
  classOK : ∀ r ∈ E.rows, ClassOK E.C r
  guardFree : ∀ r ∈ E.rows, GuardFreeConsumeAll r.t
  seed : E.a0 = alpha m0
  empty : ∀ p ∈ E.C, m0 p = []
  cover : ∃ y : Weight, (∀ p, p < E.n → 0 ≤ y p) ∧ (∀ p ∈ E.C, 1 ≤ y p) ∧
    (∀ r ∈ E.rows, dotIncD y r.flat E.n ≤ 0) ∧ dot y E.a0 E.n ≤ E.k
  laws : ∀ y ∈ E.invs, ∀ r ∈ E.rows, ZeroOnNonlinear y r.t E.n ∧ dotIncD y r.flat E.n = 0

theorem PremisesS.withNoSelfLoop {E : Enc} {m0 : CMarking} (P : PremisesS E m0)
    (h : ∀ r ∈ E.rows, ConsumeNoSelfLoop r.cls) : Premises E m0 :=
  ⟨P.nodup, P.below, P.classOK, P.guardFree, h, P.seed, P.empty, P.cover, P.laws⟩

/-- **A plan `build_plan` returns discharges the plan premises of `coloured_simulates`** but
`ConsumeNoSelfLoop`, for any gates, given what the verifier hands it and does not re-check
here: the semiflows passed the exact gate (`LawValid`), the conjoined invariants passed it with
H1, the seed is `α(m₀)`, and no guard sits on a consume-all arc. -/
theorem buildPlanG_premisesS {n : Nat} {C : List PlaceId} {ext : Bool} {g : Gate}
    {laws : List Law} {src : List SrcRow} {k : Nat} {rows : List CRow} {m0 : CMarking}
    {invs : List Weight}
    (h : buildPlanG n C ext g (alpha m0) laws src = some (k, rows))
    (hnd : C.Nodup) (hC : ∀ p ∈ C, p < n)
    (hv : ∀ l ∈ laws, LawValid (src.map SrcRow.flat) n (alpha m0) l)
    (hG : ∀ s ∈ src, GuardFreeConsumeAll s.t)
    (hinv : ∀ y ∈ invs, ∀ s ∈ src, ZeroOnNonlinear y s.t n ∧ dotIncD y s.flat n = 0) :
    PremisesS ⟨C, k, n, rows, invs, alpha m0⟩ m0 := by
  unfold buildPlanG at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  rename_i hempty
  split at h
  · exact absurd h (by simp)
  rename_i k' hk
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  rename_i harcs
  obtain ⟨rows', hrows', hkr⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at hkr
  obtain ⟨rfl, rfl⟩ := hkr
  obtain ⟨hmap, hall⟩ := classifyAll_spec hrows'
  simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and, Bool.not_eq_false]
    at harcs hempty
  have hsrc : ∀ r ∈ rows', ∃ s ∈ src, r.t = s.t ∧ r.d = s.d ∧ ClassShape C r := hall
  have hflat : ∀ r ∈ rows', r.flat ∈ src.map SrcRow.flat := fun r hr =>
    hmap ▸ List.mem_map.mpr ⟨r, hr, rfl⟩
  obtain ⟨y, hpos, hcov, hcol, hdot⟩ := colourSlotBound_sound hC hv hk
  refine ⟨hnd, hC, fun r hr => ?_, fun r hr => ?_, rfl, fun p hp => ?_,
    ⟨y, hpos, hcov, fun r hr => ?_, le_of_eq hdot⟩, fun y' hy' r hr => ?_⟩
  · obtain ⟨s, hs, ht, _, hsh⟩ := hsrc r hr
    exact ⟨ht ▸ arcsOK_spec (by simpa using harcs s hs), hsh⟩
  · obtain ⟨s, hs, ht, _, _⟩ := hsrc r hr
    exact ht ▸ hG s hs
  · have := hempty p hp
    simp only [bne_iff_ne, ne_eq, not_not] at this
    exact List.eq_nil_of_length_eq_zero this
  · exact le_of_eq (hcol r.flat (hflat r hr))
  · obtain ⟨s, hs, ht, hd, _⟩ := hsrc r hr
    have hrf : r.flat = s.flat := by simp [CRow.flat, SrcRow.flat, ht, hd]
    rw [hrf, ht]
    exact hinv y' hy' s hs

/-- `buildPlanG_premisesS` with `ConsumeNoSelfLoop` as a hypothesis: the premises of
`coloured_simulates`, whose encoder is the one before the self-loop fix. -/
theorem buildPlanG_premises {n : Nat} {C : List PlaceId} {ext : Bool} {g : Gate}
    {laws : List Law} {src : List SrcRow} {k : Nat} {rows : List CRow} {m0 : CMarking}
    {invs : List Weight}
    (h : buildPlanG n C ext g (alpha m0) laws src = some (k, rows))
    (hnd : C.Nodup) (hC : ∀ p ∈ C, p < n)
    (hv : ∀ l ∈ laws, LawValid (src.map SrcRow.flat) n (alpha m0) l)
    (hG : ∀ s ∈ src, GuardFreeConsumeAll s.t)
    (hinv : ∀ y ∈ invs, ∀ s ∈ src, ZeroOnNonlinear y s.t n ∧ dotIncD y s.flat n = 0)
    (hnsl : ∀ r ∈ rows, ConsumeNoSelfLoop r.cls) :
    Premises ⟨C, k, n, rows, invs, alpha m0⟩ m0 :=
  (buildPlanG_premisesS h hnd hC hv hG hinv).withNoSelfLoop hnsl

/-- `buildPlanG_premises` for the shipped `build_plan`. -/
theorem buildPlan_premises {n : Nat} {C : List PlaceId} {ext : Bool}
    {laws : List Law} {src : List SrcRow} {k : Nat} {rows : List CRow} {m0 : CMarking}
    {invs : List Weight}
    (h : buildPlan n C ext (alpha m0) laws src = some (k, rows))
    (hnd : C.Nodup) (hC : ∀ p ∈ C, p < n)
    (hv : ∀ l ∈ laws, LawValid (src.map SrcRow.flat) n (alpha m0) l)
    (hG : ∀ s ∈ src, GuardFreeConsumeAll s.t)
    (hinv : ∀ y ∈ invs, ∀ s ∈ src, ZeroOnNonlinear y s.t n ∧ dotIncD y s.flat n = 0)
    (hnsl : ∀ r ∈ rows, ConsumeNoSelfLoop r.cls) :
    Premises ⟨C, k, n, rows, invs, alpha m0⟩ m0 :=
  buildPlanG_premises h hnd hC hv hG hinv hnsl

/-- `buildPlanG_premises` for the `build_plan` before the NU-010 fix. -/
theorem buildPlanBudget_premises {n : Nat} {C : List PlaceId} {ext : Bool}
    {budget : List PlaceId} {laws : List Law} {src : List SrcRow} {k : Nat} {rows : List CRow}
    {m0 : CMarking} {invs : List Weight}
    (h : buildPlanBudget n C ext budget (alpha m0) laws src = some (k, rows))
    (hnd : C.Nodup) (hC : ∀ p ∈ C, p < n)
    (hv : ∀ l ∈ laws, LawValid (src.map SrcRow.flat) n (alpha m0) l)
    (hG : ∀ s ∈ src, GuardFreeConsumeAll s.t)
    (hinv : ∀ y ∈ invs, ∀ s ∈ src, ZeroOnNonlinear y s.t n ∧ dotIncD y s.flat n = 0)
    (hnsl : ∀ r ∈ rows, ConsumeNoSelfLoop r.cls) :
    Premises ⟨C, k, n, rows, invs, alpha m0⟩ m0 :=
  buildPlanG_premises h hnd hC hv hG hinv hnsl

/-! ## The shipped gates -/

set_option linter.unnecessarySeqFocus false in
/-- A `Mint` passed the mint gate. -/
theorem classifyRowG_mint_gate {C : List PlaceId} {ext mintOk : Bool} {consOk : PlaceId → Bool}
    {ms : Option MatchInfo} {t : Transition} {d : Deposit} {outs : List PlaceId}
    (h : classifyRowG C ext mintOk consOk ms t d = some (.mint outs)) : mintOk = true := by
  unfold classifyRowG at h
  cases ms <;> simp only at h <;> split_ifs at h <;> (try split at h) <;>
    (try split_ifs at h) <;> (try cases h) <;> simp_all

set_option linter.unnecessarySeqFocus false in
/-- A `Consume` of `i` passed the consume gate for `i`. -/
theorem classifyRowG_consume_gate {C : List PlaceId} {ext mintOk : Bool}
    {consOk : PlaceId → Bool} {ms : Option MatchInfo} {t : Transition} {d : Deposit}
    {i : PlaceId} {outs : List PlaceId}
    (h : classifyRowG C ext mintOk consOk ms t d = some (.consume i outs)) : consOk i = true := by
  unfold classifyRowG at h
  cases ms <;> simp only at h <;> split_ifs at h <;> (try split at h) <;>
    (try split_ifs at h) <;> (try cases h) <;> simp_all

/-- **A shipped `Mint` row is declared and its timeout writes no coloured place** (NU-010). -/
theorem shipped_mint {C : List PlaceId} {ext : Bool} {s : SrcRow} {outs : List PlaceId}
    (h : classifyRowG C ext (shippedGate C s).1 (shippedGate C s).2 s.ms s.t s.d =
      some (.mint outs)) :
    s.declared = true ∧ ∀ w ∈ s.tw, w.1 ∉ C := by
  have := classifyRowG_mint_gate h
  simp only [shippedGate, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at this
  refine ⟨this.1, fun w hw hC => ?_⟩
  have h2 := this.2 w hw
  simp [hC] at h2

/-- **A shipped `Consume` row forwards its input in every coloured timeout write** (NU-051). -/
theorem shipped_consume {C : List PlaceId} {ext : Bool} {s : SrcRow} {i : PlaceId}
    {outs : List PlaceId}
    (h : classifyRowG C ext (shippedGate C s).1 (shippedGate C s).2 s.ms s.t s.d =
      some (.consume i outs)) :
    ∀ w ∈ s.tw, w.1 ∈ C → w.2 = some i := by
  have := classifyRowG_consume_gate h
  simp only [shippedGate, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at this
  intro w hw hC
  rcases this w hw with h1 | h1
  · simp [hC] at h1
  · exact h1

end Libpetri.Novel.RouteA
