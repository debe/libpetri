/-
# Retrodiction: environment places and the frozen reachable set (VER-006)

Commit `98b9297` fixed a false `Proven`: environment places were never injected
into the CHC encoding, so the reachable set froze at `M₀` and every safety bound
held vacuously. `smt_encoder.rs:75-83` now emits, per injectable env place,

    Reachable(M') :- Reachable(M) [AND m_p < bound] AND m'_p = m_p + 1
                     AND (for q != p) m'_q = m_q

The net below is the smallest witness: one environment place feeding one
transition. Without the injection rule nothing is ever enabled, so
`PlaceBound(p₁, 0)` is proved; with it, `p₁` provably reaches 1.
-/
import Libpetri.Soundness

namespace Libpetri

def envPlace : PlaceId := 0
def outPlace : PlaceId := 1

/-- Consumes one token from the environment place, produces one downstream. -/
def tConsume : Transition :=
  { name := "consume"
  , inputs := [{ place := envPlace, card := .one, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

def netEnv : FlatNet := [(tConsume, [outPlace])]

/-- `M₀` — empty. Tokens arrive only via `inject()`. -/
def m0A : AMarking := fun _ => 0

/-! ## Pre-fix: the reachable set is frozen at `M₀` -/

/-- With no injection rule, `R(N̂) = {M₀}`. -/
theorem envless_reach_is_trivial {a : AMarking} (h : ReachA netEnv m0A a) : a = m0A := by
  induction h with
  | init => rfl
  | @step a1 ft _hr hmem hen ih =>
    exfalso
    have hft : ft = (tConsume, [outPlace]) := by simpa [netEnv] using hmem
    subst hft
    rw [ih] at hen
    exact absurd hen (by decide)

/-- Consequently `PlaceBound(p₁, 0)` is "proved" — vacuously. This is the
false `Proven` of `98b9297`. -/
theorem false_proven_without_injection :
    ∀ a, ReachA netEnv m0A a → a outPlace = 0 := by
  intro a h
  rw [envless_reach_is_trivial h]
  rfl

/-! ## Post-fix: injection restores the missing steps -/

/-- `R(N̂)` with the environment-injection rule of `smt_encoder.rs:81-83`.
`AlwaysAvailable` (unbounded) is modelled; the `Bounded k` variant adds the
`m_p < bound` guard. -/
inductive ReachAInj (net : FlatNet) (envs : List PlaceId) (a0 : AMarking) : AMarking → Prop
  | init : ReachAInj net envs a0 a0
  | step {a ft} :
      ReachAInj net envs a0 a → ft ∈ net → enabledA a ft.1 = true →
      ReachAInj net envs a0 (fireA a ft.1 ft.2)
  | inject {a p} :
      ReachAInj net envs a0 a → p ∈ envs →
      ReachAInj net envs a0 (fun q => if q == p then a q + 1 else a q)

/-- `M₀` after one injection into the environment place. -/
def aInjected : AMarking := fun q => if q == envPlace then m0A q + 1 else m0A q

/-- **Retrodiction of `98b9297`.** With injection encoded, the bound proved
above is violated: `p₁` reaches one token. The concrete executor can always
do this — `inject()` is the whole point of an environment place — so the
pre-fix `Proven` was unsound, not merely imprecise. -/
theorem injection_reaches_violation :
    ∃ a, ReachAInj netEnv [envPlace] m0A a ∧ a outPlace = 1 := by
  have hinj : ReachAInj netEnv [envPlace] m0A aInjected :=
    ReachAInj.inject (p := envPlace) ReachAInj.init (by simp)
  refine ⟨fireA aInjected tConsume [outPlace], ?_, by decide⟩
  exact ReachAInj.step (ft := (tConsume, [outPlace])) hinj (by simp [netEnv]) (by decide)

end Libpetri
