/-
# Fixture for the `proofgraph` extractor test

A tiny module with a known dependency shape. `scripts/test_proofgraph_extractor.sh`
extracts it (`--root ProofGraphFixture --prefix PGFixture`) and diffs the result
against `graph/test/fixture.expected.json`. Never imported by `Libpetri`.
-/

namespace PGFixture

/-- An inductive with two constructors. -/
inductive Colour where
  | red
  | green

/-- The bottom of the diamond. Uses core `Nat` and `HAdd.hAdd` (externals). -/
def d (n : Nat) : Nat := n + 1

/-- Left side of the diamond. -/
def b (n : Nat) : Nat := d n

/-- Right side of the diamond. -/
def c (n : Nat) : Nat := d (d n)

/-- The top of the diamond: uses `b` and `c`, both of which use `d`. -/
def a (n : Nat) : Nat := b n + c n

/-- Defined by `match`: elaborates through the auxiliary `isRed.match_1`. -/
def isRed : Colour → Bool
  | .red => true
  | .green => false

/-- Structural recursion over a list: `count.match_1`, `brecOn` and the
equation lemmas are auxiliaries. -/
def count : List Colour → Nat
  | [] => 0
  | x :: xs => (if isRed x then 1 else 0) + count xs

/-- Proved by `split` on the unfolded `match`, which uses the nested auxiliary
`isRed.match_1.splitter`. -/
theorem isRed_spec (x : Colour) (h : isRed x = true) : x = .red := by
  unfold isRed at h
  split at h
  · rfl
  · cases h

/-- Proved through the equation lemmas `count.eq_2` and `isRed.eq_1`. -/
theorem count_red (xs : List Colour) : count (.red :: xs) = 1 + count xs := by
  simp [count, isRed]

/-- Proved by rewriting with `count`'s equation lemma, so the proof term uses
the auxiliary `count.eq_1` directly. -/
theorem count_nil : count [] = 0 := by rw [count]

/-- A private declaration. -/
private def secret : Nat := d 0

/-- Uses the private `secret`. -/
theorem secret_eq : secret = 1 := rfl

/-- Uses `Classical.em`, so its axioms include `Classical.choice`. -/
theorem em_colour (x : Colour) : x = .red ∨ ¬ x = .red := Classical.em _

/-! Mutual well-founded recursion: the compiler generates auxiliaries that
reference each other (`isEven._mutual`, `_unary`, `match_`, `eq_`), an
auxiliary cycle the contraction must traverse completely. -/

mutual
/-- Even, by mutual recursion with `isOdd`. -/
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
termination_by n => n
/-- Odd, by mutual recursion with `isEven`. -/
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
termination_by n => n
end

mutual
/-- Structural mutual recursion (no `termination_by`). -/
def evenS : Nat → Bool
  | 0 => true
  | n + 1 => oddS n
/-- Structural mutual recursion, the other half. -/
def oddS : Nat → Bool
  | 0 => false
  | n + 1 => evenS n
end

/-- Uses both structural mutual definitions. -/
theorem evenS_two : evenS 2 = true := rfl

/-- Uses both mutual definitions through their equation lemmas. -/
theorem isEven_two : isEven 2 = true := by
  rw [isEven, isOdd, isEven]

/-- Well-founded recursion with `termination_by` (`WellFounded.fix`,
`halvings._unfold`). -/
def halvings (n : Nat) : Nat :=
  if n < 2 then 0 else 1 + halvings (n / 2)
termination_by n
decreasing_by omega

/-- Uses `halvings` through its unfolding equation. -/
theorem halvings_one : halvings 1 = 0 := by
  rw [halvings]
  rfl

/-- A structure with a default field (`Point.y._default`), a constructor
`Point.mk` and projections `Point.x`, `Point.y`. -/
structure Point where
  x : Nat
  y : Nat := x

/-- Built with the default for `y`. -/
def origin : Point := { x := 0 }

/-- Uses the projection `Point.y`. -/
theorem origin_y : origin.y = 0 := rfl

end PGFixture
