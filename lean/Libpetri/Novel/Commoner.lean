import Libpetri.Soundness

/-!
# Siphons, traps and Commoner's theorem ([VER-020])

Model of the structural deadlock pre-check: `structural_check`, `find_minimal_siphons` and
`find_maximal_trap_in` (`rust/libpetri-verification/src/structural_check.rs:17-132`), and the
early `Proven` built on it (`smt_verifier.rs:892-905`, guarded by `commoner_applies`,
`smt_verifier.rs:2699-2707`). The semantics is the CHC relation `ReachA` over flat transitions
(`Soundness.lean`), one entry per XOR branch, as `flatten` produces them.

* `Consumes t p` is `pre[p] > 0`: `flatten` sums `required_count` over the input arcs on `p`,
  and the sum is positive iff one of them requires a token.
* `Siphon`: every flat transition that outputs into `S` consumes from `S`.
  `Trap`: every flat transition that consumes from `T` outputs into `T`. These are the
  properties the Rust fixpoints test (`structural_check.rs:47-61`, `:102-117`).
* `Ordinary` is `commoner_applies`: no read, inhibitor or reset arc, no consume-all input, and
  every input arc requires at most one token. The Rust guard bounds the per-place *sum* by one,
  which implies the per-arc bound used here.

Results:
* `siphon_stays_empty` (any arcs): once a siphon is empty it stays empty on every
  `ReachA`-reachable marking.
* `trap_stays_marked`: a trap no reset or consume-all arc touches stays marked once marked.
* `commoner` (AC2): in an ordinary net whose input places lie below `n`, if every nonempty
  siphon below `n` contains a trap that is marked initially, then no reachable marking is dead.
  At a dead marking the unmarked places form a siphon; its marked trap would have to be both
  marked and unmarked.
* `ordinary_is_necessary` (AC3): `t: exactly(2, a) → a` from `{a:1}`, the spec's second
  witness. It satisfies the full siphon/trap condition, marked trap included, yet it is dead
  initially, so dropping the arc-weight bound breaks the theorem.
* `marked_trap_is_necessary`: the ordinary cycle `t1: a → b`, `t2: b → a` from the empty
  marking. Every nonempty siphon contains a nonempty trap, which is exactly what
  `structural_check` asks: it returns `NoPotentialDeadlock` when each minimal siphon's maximal
  trap is nonempty and never reads the initial marking. Yet the net is dead initially.
  Commoner needs a *marked* trap, so the early structural `Proven` is only sound once that
  check is added. The default VER-017 enumeration decides small untimed nets before this phase
  runs, so by our reading of `smt_verifier.rs:769-905` the gap is reachable for timed nets,
  truncated enumerations and `enumeration_max_classes = 0`. That reading has not been
  confirmed against a running verifier.

Out of scope: the fixpoint loops themselves (that `find_minimal_siphons` returns siphons and
that a siphon with no source transition closes correctly, that the contraction of
`find_maximal_trap_in` returns a trap, and that checking minimal siphons suffices), the
50-place `Inconclusive` cut-off, timing, environment places, sink places and ν-matching (all
excluded by the same guard).
-/

namespace Libpetri.Novel.Commoner

open Libpetri

/-- `pre[p] > 0` of the flattened transition: some input arc on `p` requires a token. -/
def Consumes (t : Transition) (p : PlaceId) : Prop :=
  ∃ s ∈ t.inputs, s.place = p ∧ 0 < s.card.required

/-- Every flat transition that outputs into `S` consumes from `S`. -/
def Siphon (net : FlatNet) (S : PlaceId → Prop) : Prop :=
  ∀ ft ∈ net, (∃ p, S p ∧ ft.2.contains p = true) → ∃ q, S q ∧ Consumes ft.1 q

/-- Every flat transition that consumes from `T` outputs into `T`. -/
def Trap (net : FlatNet) (T : PlaceId → Prop) : Prop :=
  ∀ ft ∈ net, (∃ p, T p ∧ Consumes ft.1 p) → ∃ q, T q ∧ ft.2.contains q = true

/-- An enabled transition finds a token on every place it consumes from. -/
theorem consumes_marked {a : AMarking} {t : Transition} {q : PlaceId}
    (hen : enabledA a t = true) (hc : Consumes t q) : 0 < a q := by
  obtain ⟨s, hs, rfl, hreq⟩ := hc
  unfold enabledA at hen
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hen
  exact Nat.lt_of_lt_of_le hreq (hen.1.1 s hs)

/-! ## Siphons stay empty, traps stay marked -/

/-- **An empty siphon stays empty** on every reachable marking, whatever arcs the net has. -/
theorem siphon_stays_empty {net : FlatNet} {S : PlaceId → Prop} (hS : Siphon net S)
    {a0 a : AMarking} (h0 : ∀ p, S p → a0 p = 0) (hr : ReachA net a0 a) :
    ∀ p, S p → a p = 0 := by
  induction hr with
  | init => exact h0
  | @step a1 ft _ hmem hen ih =>
    intro p hp
    have hpost : ft.2.contains p = false := by
      cases hc : ft.2.contains p with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨q, hq, hcons⟩ := hS ft hmem ⟨p, hp, hc⟩
        have hpos := consumes_marked hen hcons
        rw [ih q hq] at hpos
        exact Nat.lt_irrefl 0 hpos
    unfold fireA post
    rw [hpost]
    simp only [Bool.false_eq_true, if_false]
    rw [ih p hp]
    split
    · rfl
    · split
      · rfl
      · simp

/-- **A marked trap stays marked**, provided no reset or consume-all arc touches it. -/
theorem trap_stays_marked {net : FlatNet} {T : PlaceId → Prop} (hT : Trap net T)
    (hnd : ∀ ft ∈ net, ∀ p, T p →
      ft.1.resets.contains p = false ∧ consumeAllAt ft.1 p = false)
    {a0 a : AMarking} (h0 : ∃ p, T p ∧ 0 < a0 p) (hr : ReachA net a0 a) :
    ∃ p, T p ∧ 0 < a p := by
  induction hr with
  | init => exact h0
  | @step a1 ft _ hmem hen ih =>
    obtain ⟨p, hp, hpos⟩ := ih
    by_cases hc : ∃ q, T q ∧ Consumes ft.1 q
    · obtain ⟨q, hq, hout⟩ := hT ft hmem hc
      refine ⟨q, hq, ?_⟩
      unfold fireA post
      rw [hout]
      simp only [if_true]
      split
      · omega
      · split <;> omega
    · refine ⟨p, hp, ?_⟩
      have hpre : pre ft.1 p = 0 := by
        unfold pre
        cases hs : specAt ft.1 p with
        | none => rfl
        | some s =>
          obtain ⟨hsm, hpl⟩ := specAt_sound hs
          show s.card.required = 0
          cases hreq : s.card.required with
          | zero => rfl
          | succ k => exact absurd ⟨p, hp, s, hsm, hpl, by omega⟩ hc
      obtain ⟨hr1, hc1⟩ := hnd ft hmem p hp
      unfold fireA
      rw [hr1, hc1]
      simp only [Bool.false_eq_true, if_false]
      rw [hpre]
      omega

/-! ## Commoner's theorem for ordinary nets -/

/-- `commoner_applies` (`smt_verifier.rs:2699-2707`). -/
def Ordinary (net : FlatNet) : Prop :=
  ∀ ft ∈ net, ft.1.inhibitors = [] ∧ ft.1.reads = [] ∧ ft.1.resets = [] ∧
    ∀ s ∈ ft.1.inputs, s.card.consumesAll = false ∧ s.card.required ≤ 1

/-- Every input arc sits on a place below `n` (the dense index of `flatten`). -/
def InputsBelow (net : FlatNet) (n : Nat) : Prop :=
  ∀ ft ∈ net, ∀ s ∈ ft.1.inputs, s.place < n

/-- No transition of the net is enabled. -/
def Dead (net : FlatNet) (a : AMarking) : Prop :=
  ∀ ft ∈ net, enabledA a ft.1 = false

/-- Commoner's condition: every nonempty siphon below `n` contains an initially marked trap. -/
def CommonerCond (net : FlatNet) (n : Nat) (a0 : AMarking) : Prop :=
  ∀ S : PlaceId → Prop, (∀ p, S p → p < n) → (∃ p, S p) → Siphon net S →
    ∃ T : PlaceId → Prop, (∀ p, T p → S p) ∧ Trap net T ∧ ∃ p, T p ∧ 0 < a0 p

theorem ordinary_no_drain {net : FlatNet} (h : Ordinary net) :
    ∀ ft ∈ net, ∀ p, ft.1.resets.contains p = false ∧ consumeAllAt ft.1 p = false := by
  intro ft hmem p
  obtain ⟨_, _, hres, hin⟩ := h ft hmem
  refine ⟨by rw [hres]; rfl, ?_⟩
  unfold consumeAllAt
  cases hs : specAt ft.1 p with
  | none => rfl
  | some s => exact (hin s (specAt_sound hs).1).1

/-- At a dead marking of an ordinary net, every transition consumes from an unmarked place. -/
theorem dead_consumes_unmarked {net : FlatNet} {n : Nat} {a : AMarking} (hord : Ordinary net)
    (hbelow : InputsBelow net n) (hdead : Dead net a) :
    ∀ ft ∈ net, ∃ q, (q < n ∧ a q = 0) ∧ Consumes ft.1 q := by
  intro ft hmem
  obtain ⟨hinh, hrd, _, hin⟩ := hord ft hmem
  have hen := hdead ft hmem
  unfold enabledA at hen
  rw [hinh, hrd] at hen
  simp only [List.all_nil, Bool.and_true, List.all_eq_false, decide_eq_true_eq] at hen
  obtain ⟨s, hs, hlt⟩ := hen
  have hreq := (hin s hs).2
  refine ⟨s.place, ⟨hbelow ft hmem s hs, by omega⟩, s, hs, rfl, by omega⟩

/-- **Commoner's theorem** (deadlock-freedom direction, [VER-020] AC2). In an ordinary net,
if every nonempty siphon contains an initially marked trap, then no reachable marking is dead. -/
theorem commoner {net : FlatNet} {n : Nat} {a0 : AMarking} (hne : net ≠ [])
    (hord : Ordinary net) (hbelow : InputsBelow net n) (hcond : CommonerCond net n a0)
    {a : AMarking} (hr : ReachA net a0 a) : ¬ Dead net a := by
  intro hdead
  have hcons := dead_consumes_unmarked hord hbelow hdead
  have hsiph : Siphon net (fun p => p < n ∧ a p = 0) :=
    fun ft hmem _ => hcons ft hmem
  obtain ⟨ft, hft⟩ := List.exists_mem_of_ne_nil net hne
  obtain ⟨q, hq, _⟩ := hcons ft hft
  obtain ⟨T, hTS, hT, hmark⟩ := hcond _ (fun _ h => h.1) ⟨q, hq⟩ hsiph
  obtain ⟨p, hp, hpos⟩ := trap_stays_marked hT
    (fun ft hmem p _ => ordinary_no_drain hord ft hmem p) hmark hr
  rw [(hTS p hp).2] at hpos
  exact Nat.lt_irrefl 0 hpos

/-! ## The hypotheses are necessary -/

/-- `t: exactly(2, a) → a`. -/
def tEx : Transition :=
  { name := "t", inputs := [⟨0, .exactly 2, none⟩], inhibitors := [], reads := [], resets := [] }

def netEx : FlatNet := [(tEx, [0])]

def a0Ex : AMarking := fun p => if p = 0 then 1 else 0

/-- **Ordinarity is necessary** ([VER-020] AC3, the spec's second witness). The net satisfies
Commoner's condition with an initially marked trap and is dead at `{a:1}`. -/
theorem ordinary_is_necessary :
    CommonerCond netEx 1 a0Ex ∧ InputsBelow netEx 1 ∧ Dead netEx a0Ex := by
  refine ⟨?_, ?_, ?_⟩
  · intro S hS hne _
    obtain ⟨p, hp⟩ := hne
    have hp0 : p = 0 := Nat.lt_one_iff.mp (hS p hp)
    subst hp0
    refine ⟨S, fun _ h => h, ?_, 0, hp, by decide⟩
    intro ft hmem _
    simp only [netEx, List.mem_singleton] at hmem
    subst hmem
    exact ⟨0, hp, rfl⟩
  · intro ft hmem s hs
    simp only [netEx, List.mem_singleton] at hmem
    subst hmem
    simp only [tEx, List.mem_singleton] at hs
    subst hs
    decide
  · intro ft hmem
    simp only [netEx, List.mem_singleton] at hmem
    subst hmem
    rfl

/-- `t1: one(a) → b`. -/
def tAB : Transition :=
  { name := "t1", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- `t2: one(b) → a`. -/
def tBA : Transition :=
  { name := "t2", inputs := [⟨1, .one, none⟩], inhibitors := [], reads := [], resets := [] }

def netCyc : FlatNet := [(tAB, [1]), (tBA, [0])]

theorem consumes_tAB {q : PlaceId} (h : Consumes tAB q) : q = 0 := by
  obtain ⟨s, hs, hq, _⟩ := h
  simp only [tAB, List.mem_singleton] at hs
  subst hs
  exact hq.symm

theorem consumes_tBA {q : PlaceId} (h : Consumes tBA q) : q = 1 := by
  obtain ⟨s, hs, hq, _⟩ := h
  simp only [tBA, List.mem_singleton] at hs
  subst hs
  exact hq.symm

/-- **The marked-trap requirement is necessary.** The ordinary cycle passes the check
`structural_check` performs, since every nonempty siphon contains a nonempty trap, yet it is
dead at the empty marking. -/
theorem marked_trap_is_necessary :
    Ordinary netCyc ∧
    (∀ S : PlaceId → Prop, (∃ p, S p) → Siphon netCyc S →
      ∃ T : PlaceId → Prop, (∀ p, T p → S p) ∧ Trap netCyc T ∧ ∃ p, T p) ∧
    Dead netCyc (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ft hmem
    simp only [netCyc, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · refine ⟨rfl, rfl, rfl, fun s hs => ?_⟩
      simp only [tAB, List.mem_singleton] at hs
      subst hs
      decide
    · refine ⟨rfl, rfl, rfl, fun s hs => ?_⟩
      simp only [tBA, List.mem_singleton] at hs
      subst hs
      decide
  · intro S hne hsiph
    obtain ⟨p, hp⟩ := hne
    have m1 : (tAB, [1]) ∈ netCyc := by simp [netCyc]
    have m2 : (tBA, [0]) ∈ netCyc := by simp [netCyc]
    -- a siphon containing `a` contains `b` and conversely
    have h01 : S 0 → S 1 := fun h0 => by
      obtain ⟨q, hq, hc⟩ := hsiph _ m2 ⟨0, h0, rfl⟩
      rwa [consumes_tBA hc] at hq
    have h10 : S 1 → S 0 := fun h1 => by
      obtain ⟨q, hq, hc⟩ := hsiph _ m1 ⟨1, h1, rfl⟩
      rwa [consumes_tAB hc] at hq
    refine ⟨S, fun _ h => h, ?_, p, hp⟩
    intro ft hmem hcons
    obtain ⟨q, hq, hc⟩ := hcons
    simp only [netCyc, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [consumes_tAB hc] at hq
      exact ⟨1, h01 hq, rfl⟩
    · rw [consumes_tBA hc] at hq
      exact ⟨0, h10 hq, rfl⟩
  · intro ft hmem
    simp only [netCyc, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rfl

end Libpetri.Novel.Commoner
