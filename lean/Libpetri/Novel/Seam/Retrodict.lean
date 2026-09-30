import Libpetri.Novel.Seam.Sound

/-!
# Retrodiction: the stray-token `Proven` ([CORE-072], [VER-002])

The defect fixed by the inert-place rewrite (`e058472` Rust, `972e0a1` Java, `6924817` TS):
the caller's initial marking puts a token on a place `a` the net never declares. The executor
keeps it ([CORE-072]: inert), so the initial marking is already quiescent with a stranded token:
`DeadlockFree` is violated at step zero, and the enumeration route, which reads the named
`MarkingState`, said so. The CHC route flattened the declared places `{c, d}` only, seeded the
restriction (all zero), and its `Bad` ranged over `c` and `d`: `Proven`.

Every decision below is by `decide`, on string place names.

* `stray_token_not_covered`: the pre-fix index does not cover the marking.
* `prefix_seed_drops_stray`, `prefix_routes_disagree`: the encoded seed is empty, so the CHC
  route and the enumeration route start from different markings (analysis cause 1d).
* `covers_is_necessary`: every premise of `deadlock_proven_sound` holds of the pre-fix pipeline
  except `Covers`, and its conclusion fails: the wrong `Proven`, reproduced.
* `postfix_catches_stray`: on the inert net's index the seed itself is `Bad`, so no inductive
  invariant can certify the net.
-/

namespace Libpetri.Novel.Seam.StrayToken

open Libpetri Libpetri.Novel.Seam

/-- `c → d`, one token. -/
def tMove : NTransition String :=
  { name := "move", inputs := [{ place := "c", card := .one }], inhibitors := [], reads := []
  , resets := [] }

/-- The net declares `c` and `d` only. -/
def netStray : NNet String := { places := ["c", "d"], transitions := [(tMove, ["d"])] }

/-- The caller's `MarkingState`: one token on the undeclared `a`. -/
def m0Stray : NMarking String := ⟨[("a", 1)], by decide, by decide⟩

/-- The executor's initial marking. -/
def M0Stray : NCMarking String := fun n => if n = "a" then [0] else []

/-- Pre-fix: `flatten(net)`. -/
abbrev ixPre : PlaceIndex String := flatIndex netStray.places

/-- Post-fix: `flatten(inert_places_net(net, m0))`. -/
abbrev ixPost : PlaceIndex String := flatIndex (inertNet netStray m0Stray).places

theorem netStray_arcsDeclared : ArcsDeclared netStray := by
  intro ft hft n hn
  simp only [netStray, List.mem_singleton] at hft
  subst hft
  revert n; decide

theorem netStray_inputsDistinct : InputsDistinct netStray := by
  intro ft hft
  simp only [netStray, List.mem_singleton] at hft
  subst hft
  decide

theorem seeds : SeedsFrom M0Stray m0Stray := by
  funext n
  by_cases h : n = "a"
  · subst h; decide
  · simp [alphaN, M0Stray, h, NMarking.count, m0Stray, Ne.symm h]

/-- **The pre-fix index does not cover the caller's marking.** -/
theorem stray_token_not_covered : ¬ Covers ixPre m0Stray.count := by
  intro h
  exact absurd (h "a" (by decide)) (by decide)

/-- The pre-fix seed is the empty marking: the stray token has no variable. -/
theorem prefix_seed_drops_stray : encodeM0 ixPre m0Stray = fun _ => 0 := by
  funext i
  rw [encodeM0_eq_restrict]
  unfold restrict
  cases h : ixPre.name? i with
  | none => rfl
  | some n =>
    have hn : n ∈ netStray.places := mem_flatIndex.mp (ixPre.mem_of_name? h)
    simp only [netStray, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl <;> decide

/-- **The routes read different seeds** (analysis cause 1d): read back by name, the CHC seed is not
the marking the enumeration starts from. -/
theorem prefix_routes_disagree : lift ixPre (encodeM0 ixPre m0Stray) ≠ m0Stray.count := by
  intro h
  have := congrFun h "a"
  revert this
  decide

/-- The pre-fix CHC system's reachable set is the empty marking alone: `move` needs a token on
`c`. -/
theorem prefix_invariant :
    InductiveInv (flatNet ixPre netStray) (encodeM0 ixPre m0Stray) (fun a => a = fun _ => 0) := by
  refine ⟨prefix_seed_drops_stray, fun a b ha hs => ?_⟩
  obtain ⟨ft, hft, hen, -⟩ := hs
  subst ha
  simp only [flatNet, netStray, List.map_cons, List.map_nil, List.mem_singleton] at hft
  subst hft
  exact absurd hen (by decide)

/-- The pre-fix `Bad` is false on that marking: `Proven`. -/
theorem prefix_proves :
    ∀ a, a = (fun _ => 0) → ¬ deadlockBad (flatNet ixPre netStray) ixPre [] [] a = true := by
  rintro a rfl
  decide

/-- The executor's initial marking is a deadlock that strands the token on `a`. -/
theorem stray_deadlocks : NDeadlock netStray [] [] (alphaN M0Stray) := by
  refine ⟨fun ft hft => ?_, "a", by decide, ?_⟩
  · simp only [netStray, List.mem_singleton] at hft
    subst hft
    decide
  · simp [Resting, IsMarker]

/-- **`Covers` is necessary.** Every premise of `deadlock_proven_sound` other than `Covers` holds
of the pre-fix pipeline, yet the executor's initial marking (reachable in zero steps) violates
`DeadlockFree`: the CHC route's `Proven` was wrong, and exactly the `Covers` premise is what
fails. -/
theorem covers_is_necessary :
    ArcsIn ixPre netStray ∧ InputsDistinct netStray ∧ SeedsFrom M0Stray m0Stray ∧
    InductiveInv (flatNet ixPre netStray) (encodeM0 ixPre m0Stray) (fun a => a = fun _ => 0) ∧
    (∀ a, a = (fun _ => 0) → ¬ deadlockBad (flatNet ixPre netStray) ixPre [] [] a = true) ∧
    ReachNC netStray M0Stray M0Stray ∧ NDeadlock netStray [] [] (alphaN M0Stray) ∧
    ¬ Covers ixPre m0Stray.count :=
  ⟨arcsIn_flatIndex netStray_arcsDeclared, netStray_inputsDistinct, seeds, prefix_invariant,
    prefix_proves, Relation.ReflTransGen.refl, stray_deadlocks, stray_token_not_covered⟩

/-- Post-fix, the index covers the marking (`inert_covers`). -/
theorem postfix_covers : Covers ixPost m0Stray.count := inert_covers netStray m0Stray

/-- Post-fix, both routes start from the caller's marking. -/
theorem postfix_routes_agree : lift ixPost (encodeM0 ixPost m0Stray) = m0Stray.count :=
  (routes_same_seed postfix_covers).2

/-- **Post-fix, the seed itself is `Bad`**: the inert place `a` has an index and strands. (In the
model's unsorted index `a` is number `2`; the Rust's sorted `flatten` numbers it `0`. The
verdict does not depend on which.) -/
theorem postfix_catches_stray :
    deadlockBad (flatNet ixPost netStray) ixPost [] [] (encodeM0 ixPost m0Stray) = true := by
  decide

/-- Hence no inductive invariant certifies the net post-fix: the CHC route answers `Violated`,
as the enumeration route always did. -/
theorem postfix_no_certificate :
    ¬ ∃ Inv, InductiveInv (flatNet ixPost netStray) (encodeM0 ixPost m0Stray) Inv ∧
      ∀ a, Inv a → ¬ deadlockBad (flatNet ixPost netStray) ixPost [] [] a = true := by
  rintro ⟨Inv, hInv, hSafe⟩
  exact hSafe _ hInv.init postfix_catches_stray

end Libpetri.Novel.Seam.StrayToken
