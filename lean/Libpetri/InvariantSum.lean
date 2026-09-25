/-
# Weight vectors and the weighted sums the encoder emits

`Weight`, `isum`, `dot` and `dotInc`, split out of `Strengthening.lean`, which
proves P-invariant strengthening sound over them.
-/
import Libpetri.Soundness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Mul

namespace Libpetri

/-!
## Weight vectors and the emitted sums

`PInvariant` (`p_invariant.rs:9-13`) carries `weights: Vec<i64>` over the
dense place index plus a `support` that `validate_invariants_exact` pins to
exactly the nonzero weights (`p_invariant.rs:288-299`). A weight vector is
modelled total over `PlaceId` with its support below `place_count` — a plain
function rather than a `Finsupp`, so concrete vectors stay definable by `if`;
sums run over the first `n` places (`Finset.range n`, `dotProduct` over
`Fin n`), which is the sum `invariant_conditions` emits
(`smt_encoder.rs:406-429`), since the dense index of `flatten`
(`net_flattener.rs:31-40`) keeps every place id below `place_count`.
-/

/-- A P-invariant weight vector `y`: one integer weight per dense place index
(`PInvariant.weights`, `p_invariant.rs:9-13`). -/
abbrev Weight := PlaceId → Int

/-- The support of `y` lies below `n` — what `PInvariant.support ⊆
[0, place_count)` means for a total function. -/
def SupportBelow (n : Nat) (y : Weight) : Prop :=
  ∀ p, n ≤ p → y p = 0

/-- `Σ_{p < n} f p` over the dense place index. -/
def isum (f : PlaceId → Int) (n : Nat) : Int :=
  ∑ p ∈ Finset.range n, f p

/-- The weighted token sum `y·M` over the first `n` places — the equality the
encoder conjoins on the successor variables `m'_i` (`invariant_conditions`,
`smt_encoder.rs:406-429`). -/
def dot (y : Weight) (m : AMarking) (n : Nat) : Int :=
  dotProduct (fun i : Fin n => y i) (fun i : Fin n => (m i : Int))

/-- `y·(post − pre)` over the first `n` places: `y` applied to one flat
transition's **incidence column exactly as the shipped matrix builds it** —
`C[t][p] = post − pre` with `pre = required_count`
(`incidence_matrix.rs:45-51` from `net_flattener.rs:50-54`; TS
`incidence-matrix.ts` from `net-flattener.ts`). `dotInc y ft n = 0` is
therefore *verbatim* the condition `validate_invariants_exact` re-validates in
exact arithmetic (`p_invariant.rs:313-331`; TS `p-invariant-computer.ts`).
Note what the column does **not** say: nothing about `consume_all` or
`reset_places` — that omission is H1 below. -/
def dotInc (y : Weight) (ft : FlatTransition) (n : Nat) : Int :=
  isum (fun p => y p * ((post ft.2 p : Int) - (pre ft.1 p : Int))) n

theorem isum_succ (f : PlaceId → Int) (n : Nat) : isum f (n + 1) = isum f n + f n :=
  Finset.sum_range_succ f n

/-- `dot` is the `isum` of the pointwise products. -/
theorem dot_eq_isum (y : Weight) (m : AMarking) (n : Nat) :
    dot y m n = isum (fun p => y p * (m p : Int)) n :=
  Fin.sum_univ_eq_sum_range (fun p => y p * (m p : Int)) n

theorem isum_congr {f g : PlaceId → Int} :
    ∀ {n : Nat}, (∀ p, p < n → f p = g p) → isum f n = isum g n :=
  fun h => Finset.sum_congr rfl fun p hp => h p (Finset.mem_range.mp hp)

theorem isum_add (f g : PlaceId → Int) :
    ∀ n, isum (fun p => f p + g p) n = isum f n + isum g n :=
  fun _ => Finset.sum_add_distrib

/-- A weight vector supported below `n` sums identically under any wider
truncation — the encoder's support-indexed sum (`invariant_conditions`,
`smt_encoder.rs:414-418`, iterates `inv.support` only) loses nothing against
the full `y·M`. -/
theorem dot_stable_of_support_below {y : Weight} {n : Nat}
    (hy : SupportBelow n y) (m : AMarking) :
    ∀ k, dot y m (n + k) = dot y m n
  | 0 => rfl
  | k + 1 => by
    rw [dot_eq_isum, ← Nat.add_assoc, isum_succ, ← dot_eq_isum,
      dot_stable_of_support_below hy m k, hy (n + k) (Nat.le_add_right n k)]
    omega

/-- Two-place evaluation of `dot`, for the concrete witnesses below. -/
theorem dot_two (y : Weight) (m : AMarking) :
    dot y m 2 = y 0 * (m 0 : Int) + y 1 * (m 1 : Int) :=
  Fin.sum_univ_two (fun i : Fin 2 => y i * (m i : Int))

end Libpetri
