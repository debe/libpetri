/-
# Retrodiction: environment places and the frozen reachable set (VER-006)

Commit `98b9297` fixed a false `Proven`: environment places were never injected
into the CHC encoding, so the reachable set froze at `M₀` and every safety bound
held vacuously. `encode_net` (the body of `encode`, `smt_encoder.rs:175-184`)
now emits, per injectable env place,

    Reachable(M') :- Reachable(M) [AND m_p < bound] AND m'_p = m_p + 1
                     AND (for q != p) m'_q = m_q

(the options-off form; with `EncodeOptions::state_equation` ([VER-016]) the
rule also copies every firing counter, modelled in `StateEquation.lean`).

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

/-- One step of `R(N̂)` with injection: a net transition fires, or one token
is injected into an environment place. -/
def StepAInjRel (net : FlatNet) (envs : List PlaceId) (a a' : AMarking) : Prop :=
  StepARel net a a' ∨ ∃ p ∈ envs, a' = fun q => if q == p then a q + 1 else a q

/-- `R(N̂)` with the environment-injection rule (`encode_injection_rule`,
`smt_encoder.rs:532-560`, one per injectable place from `encode_net`'s loop at
`:182-184`; the conjuncts are `injection_conditions`, `:446-467`).
`AlwaysAvailable` (unbounded) is modelled; the `Bounded k` variant adds the
`m_p < bound` guard. -/
def ReachAInj (net : FlatNet) (envs : List PlaceId) (a0 : AMarking) : AMarking → Prop :=
  Relation.ReflTransGen (StepAInjRel net envs) a0

theorem ReachAInj.init {net : FlatNet} {envs : List PlaceId} {a0 : AMarking} :
    ReachAInj net envs a0 a0 :=
  Relation.ReflTransGen.refl

theorem ReachAInj.step {net : FlatNet} {envs : List PlaceId} {a0 a : AMarking}
    {ft : FlatTransition} (h : ReachAInj net envs a0 a) (hmem : ft ∈ net)
    (hen : enabledA a ft.1 = true) : ReachAInj net envs a0 (fireA a ft.1 ft.2) :=
  Relation.ReflTransGen.tail h (Or.inl ⟨ft, hmem, hen, rfl⟩)

theorem ReachAInj.inject {net : FlatNet} {envs : List PlaceId} {a0 a : AMarking}
    {p : PlaceId} (h : ReachAInj net envs a0 a) (hp : p ∈ envs) :
    ReachAInj net envs a0 (fun q => if q == p then a q + 1 else a q) :=
  Relation.ReflTransGen.tail h (Or.inr ⟨p, hp, rfl⟩)

/-- Induction over `ReachAInj` with the cases of the former inductive. -/
@[elab_as_elim, induction_eliminator]
theorem ReachAInj.rec' {net : FlatNet} {envs : List PlaceId} {a0 : AMarking}
    {motive : (a : AMarking) → ReachAInj net envs a0 a → Prop}
    (init : motive a0 ReachAInj.init)
    (step : ∀ {a ft} (hr : ReachAInj net envs a0 a) (hmem : ft ∈ net)
      (hen : enabledA a ft.1 = true),
      motive a hr → motive (fireA a ft.1 ft.2) (ReachAInj.step hr hmem hen))
    (inject : ∀ {a p} (hr : ReachAInj net envs a0 a) (hp : p ∈ envs),
      motive a hr →
      motive (fun q => if q == p then a q + 1 else a q) (ReachAInj.inject hr hp))
    {a : AMarking} (h : ReachAInj net envs a0 a) : motive a h := by
  induction h with
  | refl => exact init
  | tail hr hst ih =>
    rcases hst with ⟨ft, hmem, hen, rfl⟩ | ⟨p, hp, rfl⟩
    · exact step hr hmem hen ih
    · exact inject hr hp ih

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
