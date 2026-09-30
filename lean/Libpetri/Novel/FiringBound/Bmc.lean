import Libpetri.Novel.FiringBound.Ranking

/-!
# The bounded model check is exact ([VER-019])

`encode_bounded_run` as a constraint system over integer assignments (`BmcModel`),
`decode_bounded_run` (`decodeRust`), and `bmc_complete`: a model at depth `d` exists iff some run
of at most `d` firings reaches a violating marking. See `Libpetri/Novel/FiringBound.lean`.
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

/-- **The script `encode_bounded_run` emits at depth `d`, as constraints** over the selectors
`s` and the marking variables `M` (P4). The environment post-caps are empty (P6). -/
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

/-- An idle step (`s_i = T`) leaves every place at its previous value. -/
theorem chain_idle (rows : List Row) (p : PlaceId) (br : Nat → Int) (base : Int) :
    chain (rows.length : Int) (touching rows p) br base = base := by
  apply chain_miss
  intro t ht heq
  obtain ⟨tr, h, -⟩ := mem_touching.mp ht
  have hlt := (List.getElem?_eq_some_iff.mp h).1
  have : rows.length = t := by exact_mod_cast heq
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

/-! ### Decoding the selectors -/

/-- `index_below(T)`: a selector names a row iff it lies in `[0, T)`. -/
def decodeSel (T : Nat) (v : Int) : Option Nat :=
  if 0 ≤ v ∧ v < T then some v.toNat else none

/-- `map_while`. -/
def takeSome : List (Option Nat) → List Nat
  | [] => []
  | none :: _ => []
  | some x :: xs => x :: takeSome xs

/-- `decode_bounded_run` as written: the selectors of steps `0 … d−1`, read up to the first
idle one. -/
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

/-- **A model's decoded selectors replay** to the marking of its last step. -/
theorem bmc_model_replays {rows : List Row} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {d : Nat} {s : Nat → Int} {M : Nat → PlaceId → Int}
    (hWF : WellFormedRows n rows) (hm : BmcModel rows n a0 badI d s M) :
    ∃ a, replay rows a0 (decode rows.length s d) = some a ∧ ∀ p, mAt n a0 M d p = a p := by
  suffices h : ∀ i, i ≤ d → ∃ a, replay rows a0 (decode rows.length s i) = some a ∧
      (∀ p, mAt n a0 M i p = a p) ∧
      ((decode rows.length s i).length = i ∨ (0 < i ∧ s (i - 1) = rows.length)) by
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
    have idle : s i = rows.length →
        ∀ p, mAt n a0 M (i + 1) p = a p := by
      intro hs p
      by_cases hp : p < n
      · rw [hm.update i hid p hp, hs, chain_idle, hmk p]
      · exact hfr p (Nat.le_of_not_lt hp)
    by_cases hL : (decode rows.length s i).length = i
    · cases hsel : decodeSel rows.length (s i) with
      | none =>
        have hs : s i = rows.length := by
          have hr := hm.sel_range i hid
          unfold decodeSel at hsel
          split at hsel
          · exact absurd hsel (by simp)
          · rename_i hn; omega
        refine ⟨a, ?_, idle hs, Or.inr ⟨by omega, by simpa using hs⟩⟩
        simp only [decode, hL, if_true, hsel]
        exact hrep
      | some t =>
        have hst : s i = t ∧ t < rows.length := by
          unfold decodeSel at hsel
          split at hsel
          · rename_i hc
            have := Option.some.inj hsel
            subst this
            exact ⟨(Int.toNat_of_nonneg hc.1).symm, by omega⟩
          · exact absurd hsel (by simp)
        obtain ⟨hs, htl⟩ := hst
        have htr : rows[t]? = some rows[t] := List.getElem?_eq_getElem htl
        have hmem : rows[t] ∈ rows := List.getElem_mem htl
        have hg := hm.guard i hid t htl hs
        have hmk' : mAt n a0 M i = fun p => (a p : Int) := funext hmk
        rw [hmk'] at hg
        have hen := (guardI_iff_enabledA (hWF _ hmem).1 (hWF _ hmem).2 a).mp hg
        refine ⟨fireAD a rows[t].1 rows[t].2, ?_, fun p => ?_, Or.inl ?_⟩
        · simp only [decode, hL, if_true, hsel]
          exact replay_snoc hrep htr hen
        · by_cases hp : p < n
          · rw [hm.update i hid p hp, hs, hmk p]
            exact chain_step htr hen p
          · rw [hfr p (Nat.le_of_not_lt hp)]
            rw [fireAD_frame (hWF _ hmem).1 a (Nat.le_of_not_lt hp)]
        · simp [decode, hL, hsel]
    · obtain ⟨hpos, hprev⟩ := hlen.resolve_left hL
      have hs : s i = rows.length := by
        have := hm.idle_final (i - 1) (by omega) hprev
        rwa [Nat.sub_add_cancel (by omega)] at this
      refine ⟨a, ?_, idle hs, Or.inr ⟨by omega, by simpa using hs⟩⟩
      simp only [decode, hL, if_false]
      exact hrep

/-! ### Completeness of the encoding: a run is a model -/

/-- The marking after the first `i` firings of a run. -/
def stAt (rows : List Row) (a0 : AMarking) (ts : List Nat) (i : Nat) : AMarking :=
  (replay rows a0 (ts.take i)).getD a0

theorem replay_take {rows : List Row} {a0 a : AMarking} {ts : List Nat}
    (h : replay rows a0 ts = some a) (i : Nat) :
    replay rows a0 (ts.take i) = some (stAt rows a0 ts i) := by
  have hsplit := replay_append rows a0 (ts.take i) (ts.drop i)
  rw [List.take_append_drop, h] at hsplit
  unfold stAt
  cases hti : replay rows a0 (ts.take i) with
  | none => rw [hti] at hsplit; exact absurd hsplit (by simp)
  | some b => rfl

/-- **A run of at most `d` firings to a violating marking is a model of the depth-`d` script**:
its firings as selectors, idle after, and its markings as the variables. -/
theorem bmc_of_run {rows : List Row} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} {d : Nat}
    (hWF : WellFormedRows n rows) (hBad : BadAgrees badI bad)
    {ts : List Nat} {a : AMarking} (hlen : ts.length ≤ d) (hrep : replay rows a0 ts = some a)
    (hbad : bad a) : BmcSat rows n a0 badI d := by
  classical
  let T := rows.length
  let s : Nat → Int := fun i => if h : i < ts.length then (ts[i] : Int) else (T : Int)
  let M : Nat → PlaceId → Int := fun i p => (stAt rows a0 ts i p : Int)
  have hlt := replay_lt hrep
  have hst0 : stAt rows a0 ts 0 = a0 := by simp [stAt, replay]
  have hmk : ∀ i p, mAt n a0 M i p = (stAt rows a0 ts i p : Int) := by
    intro i p
    unfold mAt
    split
    · rename_i hc
      rcases hc with h0 | hp
      · subst h0; rw [hst0]
      · rw [replay_frame hWF (replay_take hrep i) p hp]
    · rfl
  have hmk' : ∀ i, mAt n a0 M i = fun p => (stAt rows a0 ts i p : Int) := fun i => funext (hmk i)
  -- the step `i < |ts|` fires `ts[i]` from `stAt i` to `stAt (i+1)`
  have hfire : ∀ i (hi : i < ts.length), ∃ tr, rows[ts[i]]? = some tr ∧
      enabledA (stAt rows a0 ts i) tr.1 = true ∧
      stAt rows a0 ts (i + 1) = fireAD (stAt rows a0 ts i) tr.1 tr.2 := by
    intro i hi
    have h1 := replay_take hrep (i + 1)
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, replay_append,
      replay_take hrep i] at h1
    simp only [Option.bind_some, replay] at h1
    cases htr : rows[ts[i]]? with
    | none => rw [htr] at h1; exact absurd h1 (by simp)
    | some tr =>
      rw [htr] at h1
      simp only at h1
      split at h1
      · rename_i hen
        exact ⟨tr, rfl, hen, (Option.some.inj h1).symm⟩
      · exact absurd h1 (by simp)
  have hidle : ∀ i, ts.length ≤ i → stAt rows a0 ts (i + 1) = stAt rows a0 ts i := by
    intro i hi
    unfold stAt
    rw [List.take_of_length_le (by omega), List.take_of_length_le hi]
  have hsT : ∀ i, ts.length ≤ i → s i = T := by
    intro i hi; simp only [s, dif_neg (show ¬ i < ts.length by omega)]
  have hsLt : ∀ i (hi : i < ts.length), s i = (ts[i] : Int) := by
    intro i hi; simp only [s, dif_pos hi]
  refine ⟨s, M, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i _
    by_cases hi : i < ts.length
    · rw [hsLt i hi]
      have := hlt ts[i] (List.getElem_mem hi)
      constructor <;> omega
    · rw [hsT i (by omega)]; omega
  · intro i _ hs
    have hi : ts.length ≤ i := by
      by_contra hc
      rw [hsLt i (by omega)] at hs
      have := hlt ts[i] (List.getElem_mem (by omega))
      omega
    exact hsT (i + 1) (by omega)
  · intro i _ t ht hs
    have hi : i < ts.length := by
      by_contra hc
      rw [hsT i (by omega)] at hs
      omega
    rw [hsLt i hi] at hs
    have htt : ts[i] = t := by exact_mod_cast hs
    obtain ⟨tr, htr, hen, -⟩ := hfire i hi
    rw [htt, List.getElem?_eq_getElem ht] at htr
    cases htr
    rw [hmk' i]
    have hmem : rows[t] ∈ rows := List.getElem_mem ht
    exact (guardI_iff_enabledA (hWF _ hmem).1 (hWF _ hmem).2 _).mpr hen
  · intro i _ p _
    rw [hmk (i + 1) p, hmk i p]
    by_cases hi : i < ts.length
    · obtain ⟨tr, htr, hen, hnext⟩ := hfire i hi
      rw [hsLt i hi, hnext]
      exact (chain_step htr hen p).symm
    · rw [hsT i (by omega), chain_idle, hidle i (by omega)]
  · rw [hmk' d]
    have : stAt rows a0 ts d = a := by
      have h1 := replay_take hrep d
      rw [List.take_of_length_le hlen, hrep] at h1
      exact (Option.some.inj h1).symm
    rw [this]
    exact (hBad a).mpr hbad

/-! ### Exactness -/

/-- **`bmc_complete`: the depth-`d` script has a model iff some run of at most `d` firings
reaches a violating marking.** -/
theorem bmc_complete {rows : List Row} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} (d : Nat)
    (hWF : WellFormedRows n rows) (hBad : BadAgrees badI bad) :
    BmcSat rows n a0 badI d ↔
      ∃ ts a, ts.length ≤ d ∧ replay rows a0 ts = some a ∧ bad a := by
  constructor
  · rintro ⟨s, M, hm⟩
    obtain ⟨a, hrep, hmk⟩ := bmc_model_replays hWF hm
    refine ⟨_, a, decode_length_le _ s d, hrep, ?_⟩
    have := hm.bad
    rw [show mAt n a0 M d = fun p => (a p : Int) from funext hmk] at this
    exact (hBad a).mp this
  · rintro ⟨ts, a, hlen, hrep, hbad⟩
    exact bmc_of_run hWF hBad hlen hrep hbad

/-- **The `sat` path**: a model's decoded run (`decode_bounded_run`) replays under the exact
semantics (`replay_run`) to a violating marking, so a `sat` answer is never turned away by the
replay. -/
theorem bmc_sat_replays {rows : List Row} {n : Nat} {a0 : AMarking}
    {badI : (PlaceId → Int) → Prop} {bad : AMarking → Prop} {d : Nat} {s : Nat → Int}
    {M : Nat → PlaceId → Int} (hWF : WellFormedRows n rows) (hBad : BadAgrees badI bad)
    (hm : BmcModel rows n a0 badI d s M) :
    ∃ a, replay rows a0 (decodeRust rows.length s d) = some a ∧ bad a := by
  obtain ⟨a, hrep, hmk⟩ := bmc_model_replays hWF hm
  refine ⟨a, by rw [decodeRust_eq_decode]; exact hrep, ?_⟩
  have := hm.bad
  rw [show mAt n a0 M d = fun p => (a p : Int) from funext hmk] at this
  exact (hBad a).mp this

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
