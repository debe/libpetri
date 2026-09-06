/-
# Proposition 1 — the abstraction is an over-approximation

`theory/verification-preserving-neural-substitution.typ` Proposition 1:
`α(R(N)) ⊆ R(N̂)`. Every false-`Proven` bug in the project's history is a
violation of this statement for the shipped encoder.

The theorem below is proved under two side conditions the encoder does **not**
check, `GuardFreeConsumeAll` and `UnitOutput`. `guard_hypothesis_is_necessary`
and `unit_output_hypothesis_is_necessary` exhibit concrete nets showing neither
can be dropped — so each is a real gap in the shipped verifier, not proof
bureaucracy.
-/
import Libpetri.Basic

namespace Libpetri

/-! ## A flat transition is a transition together with one XOR branch

`net_flattener.rs:98-115` emits one `FlatTransition` per branch of the output
tree, all sharing the same `pre`. The branch is exactly the set of places that
receive one token. -/
abbrev FlatTransition := Transition × List PlaceId

/-- A net, post-flattening. -/
abbrev FlatNet := List FlatTransition

/-- Both side conditions, over a whole net. -/
def WellFormed (net : FlatNet) : Prop :=
  ∀ ft ∈ net, InputsDistinctPlaces ft.1 ∧ GuardFreeConsumeAll ft.1

/-! ## Helper lemmas -/

private theorem len_filter_le {α : Type} (g : α → Bool) :
    ∀ l : List α, (l.filter g).length ≤ l.length
  | [] => by simp
  | x :: xs => by
    simp only [List.filter]
    cases hg : g x with
    | true => simpa using len_filter_le g xs
    | false => exact Nat.le_trans (len_filter_le g xs) (Nat.le_succ _)

/-- A guard can only ever hide tokens, never invent them. -/
theorem matchCount_le (m : CMarking) (s : InSpec) :
    matchCount m s ≤ (m s.place).length := by
  unfold matchCount
  cases s.guard with
  | none => exact Nat.le_refl _
  | some g => exact len_filter_le g _

/-- `specAt` really does return a spec belonging to the transition, sitting on
the place asked for. -/
theorem specAt_sound {t : Transition} {p : PlaceId} {s : InSpec}
    (h : specAt t p = some s) : s ∈ t.inputs ∧ s.place = p := by
  unfold specAt at h
  exact ⟨List.mem_of_find?_eq_some h, by
    have := List.find?_some h
    simpa using this⟩

/-! ## The simulation lemma

This is the whole content of Proposition 1: one concrete firing is matched by
one abstract firing of the corresponding flat transition. -/

theorem prop1_step
    (m : CMarking) (t : Transition) (prod : PlaceId → Nat) (br : List PlaceId)
    (hGuard : GuardFreeConsumeAll t)
    (hProd : UnitOutput prod br)
    (hEn : enabledC m t = true) :
    enabledA (alpha m) t = true ∧ alphaFireC m t prod = fireA (alpha m) t br := by
  constructor
  · -- Enablement transfers because `matchCount ≤ length`: the abstract guard is
    -- strictly weaker, which is the safe direction.
    unfold enabledC at hEn
    unfold enabledA
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hEn ⊢
    obtain ⟨⟨hIn, hInh⟩, hRd⟩ := hEn
    refine ⟨⟨fun s hs => ?_, fun p hp => ?_⟩, fun p hp => ?_⟩
    · exact Nat.le_trans (hIn s hs) (matchCount_le m s)
    · exact hInh p hp
    · exact hRd p hp
  · -- Effect transfers place by place.
    funext p
    unfold alphaFireC fireA
    by_cases hR : t.resets.contains p = true
    · simp only [hR, if_pos]
      exact hProd p
    · simp only [hR, if_neg, Bool.not_eq_true] at *
      by_cases hCA : consumeAllAt t p = true
      · -- Consume-all place. The encoder claims the place is emptied; that is
        -- only true when the arc is unguarded, which `hGuard` supplies.
        simp only [hCA, if_pos]
        unfold consumedAt
        unfold consumeAllAt at hCA
        cases hs : specAt t p with
        | none => rw [hs] at hCA; simp at hCA
        | some s =>
          rw [hs] at hCA
          obtain ⟨hmem, hplace⟩ := specAt_sound hs
          have hg : s.guard = none := hGuard s hmem hCA
          have hall : consumeCount m s = (m p).length := by
            simp [consumeCount, hCA, matchCount, hg, hplace]
          show ((m p).length - consumeCount m s) + prod p = post br p
          rw [hall, Nat.sub_self, Nat.zero_add]
          exact hProd p
      · -- Ordinary place: `m'_p = m_p - pre[p] + post[p]`.
        simp only [hCA, if_neg, Bool.not_eq_true]
        unfold consumedAt pre alpha
        cases hs : specAt t p with
        | none =>
          show ((m p).length - 0) + prod p = ((m p).length - 0) + post br p
          rw [hProd p]
        | some s =>
          have hCA' : s.card.consumesAll = false := by
            unfold consumeAllAt at hCA
            rw [hs] at hCA
            simpa using hCA
          show ((m p).length - consumeCount m s) + prod p
             = ((m p).length - s.card.required) + post br p
          rw [show consumeCount m s = s.card.required by
                simp [consumeCount, hCA'], hProd p]

/-! ## Proposition 1 over reachability

`StepC` specifies a concrete firing at the granularity `α` observes: it is
enabled, and its effect on token counts is `alphaFireC`. That is exactly what
`consume_for_firing` + `produce_token` establish. -/

structure StepC (m : CMarking) (ft : FlatTransition)
    (prod : PlaceId → Nat) (m' : CMarking) : Prop where
  enabled : enabledC m ft.1 = true
  unit    : UnitOutput prod ft.2
  effect  : alpha m' = alphaFireC m ft.1 prod

/-- Concrete reachability `R(N)`. -/
inductive ReachC (net : FlatNet) (m0 : CMarking) : CMarking → Prop
  | init : ReachC net m0 m0
  | step {m m' ft prod} :
      ReachC net m0 m → ft ∈ net → StepC m ft prod m' → ReachC net m0 m'

/-- Abstract reachability `R(N̂)` — the least fixpoint of the CHC rules
(`smt_encoder.rs:66` seeds it with `M₀`, `:70-73` adds one rule per flat
transition). -/
inductive ReachA (net : FlatNet) (a0 : AMarking) : AMarking → Prop
  | init : ReachA net a0 a0
  | step {a ft} :
      ReachA net a0 a → ft ∈ net → enabledA a ft.1 = true →
      ReachA net a0 (fireA a ft.1 ft.2)

/-- **Proposition 1.** `α(R(N)) ⊆ R(N̂)`. -/
theorem proposition_one
    {net : FlatNet} {m0 m : CMarking}
    (hWF : WellFormed net) (h : ReachC net m0 m) :
    ReachA net (alpha m0) (alpha m) := by
  induction h with
  | init => exact ReachA.init
  | step hr hmem hstep ih =>
    rename_i m1 m2 ft prod
    obtain ⟨_, hGuard⟩ := hWF ft hmem
    obtain ⟨hEn, hUnit, hEff⟩ := hstep
    obtain ⟨hEnA, hFire⟩ := prop1_step m1 ft.1 prod ft.2 hGuard hUnit hEn
    rw [hEff, hFire]
    exact ReachA.step ih hmem hEnA

/-!
## Necessity of the two side conditions

Each counterexample is a complete net plus a reachable concrete marking whose
`α`-image the abstract relation cannot produce. Both are decided by `decide`,
so they are checked, not asserted.
-/

section Counterexamples

/-- A guard that accepts only colour `1`. -/
def guardIsOne : Guard := fun c => c == 1

/-- `t` drains place 0 with a *guarded* `In::All`, producing nothing. -/
def tGuardedAll : Transition :=
  { name := "drain"
  , inputs := [{ place := 0, card := .all, guard := some guardIsOne }]
  , inhibitors := [], reads := [], resets := [] }

/-- Place 0 holds one matching token (`1`) and one non-matching token (`2`). -/
def mGuarded : CMarking := fun p => if p == 0 then [1, 2] else []

theorem guarded_all_is_enabled : enabledC mGuarded tGuardedAll = true := by decide

/-- **Finding 1 — now discharged by deleting guards from the implementations.**

The executor consumed only the guard-matching token, so place 0 still held one
token after the firing. The encoder emits `m'_0 = post[0] = 0` for every
`consume_all` place (`smt_encoder.rs:165-167`), because `net_flattener.rs` never
inspects the guard. The abstract successor is therefore *smaller* than the
concrete one — an under-approximation, which is precisely how a
`PlaceBound(p₀, 0)` query gets a false `Proven`.

This theorem is retained as the evidence that motivated removing input guards
(`IO-006`, tombstoned 2026-02, finally carried through in Rust and TypeScript).
No net that can be built today reaches this state, so `GuardFreeConsumeAll` is
now vacuous — but the obligation it names is real, and would return the moment a
per-token predicate is reintroduced without teaching the flattener about it. -/
theorem guard_hypothesis_is_necessary :
    alphaFireC mGuarded tGuardedAll (fun _ => 0) 0 = 1
    ∧ fireA (alpha mGuarded) tGuardedAll [] 0 = 0 := by
  constructor <;> decide

/-- `t` moves one token from place 0 to place 1. -/
def tSimple : Transition :=
  { name := "move"
  , inputs := [{ place := 0, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def mSimple : CMarking := fun p => if p == 0 then [7] else []

/-- An action that writes *two* tokens to its single output place. -/
def prodDouble : PlaceId → Nat := fun p => if p == 1 then 2 else 0

/-- **Finding 2.** `validate_out_spec` (`executor_core/output.rs:41`) compares
place SETS and never token counts, so this action is accepted: the produced set
is `{p₁}`, which is exactly what `Out::Place(p₁)` claims. (The [IO-015]
exact-explanation rewrite tightened WHICH place sets conform — a claim must now
equal the produced set — but the two tokens this action writes to place 1 remain
invisible to it, so the finding stands unchanged.) The encoder fixes the gain at one token per
branch place (`net_flattener.rs:85-88`). Again the concrete successor escapes
the abstract relation. -/
theorem unit_output_hypothesis_is_necessary :
    alphaFireC mSimple tSimple prodDouble 1 = 2
    ∧ fireA (alpha mSimple) tSimple [1] 1 = 1 := by
  constructor <;> decide

end Counterexamples

end Libpetri
