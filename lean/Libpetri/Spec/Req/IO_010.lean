import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.IO_010

set_option linter.missingDocs true

/-!
# IO-010: Output place (leaf) (`spec/02-input-output-specs.md`)

A predicate over an abstract firing relation `F : FireRel N`, checked against the reference
semantics (`Reference.Fires`, as `RefFire`), against concrete firing relations that break it, and
against one mutant reading per clause.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## IO-010: Output place (leaf) -/

requirement IO_010
  id "IO-010"
  title "Output place (leaf)"
  kind B
  scope "executors with output validation enabled (the default)"
  source verbatim "spec/02-input-output-specs.md"
  covers IO_010.s1, IO_010.s2, IO_010.s3, IO_010.s4, IO_010.s5
  reading "For every transition t whose output spec is the leaf Place(p), and every deposit d:"
          "every firing of t that deposits d puts at least one token in p;"
          "every firing of t that deposits d puts no token in any place other than p;"
          "every firing of t that deposits d, from m to m', leaves p holding at least what p kept (nothing if t has a reset arc on p, else m p minus what t consumed from p) plus what d put in p."
  assumes "The firing relation F is that of an executor with output validation enabled, the default (CONC-026). An executor with the CONC-026 skip enabled deposits whatever the action wrote, its Place leaf included, so it may write nothing; CONC-026 lifts IO-010 for it, and the evidence below shows that such an executor's firing relation (io010_skipFire) does not satisfy IO-010 (IO_010_forbids_skip), which is why the scope is stated."
          "A transition whose output spec is the leaf Place(p) passes every build-time check of its output spec (IO-011 to IO-014: one place, no Timeout, no ForwardInput, one output branch), so the statement ranges over transitions that build; no well-formedness hypothesis is needed."
          "A firing is read as one step from a marking to a marking that deposits the tokens of one outcome (glossary: Fire, Deposit); timing and priority play no part. A completion that fails, by an action exception or by IO-015 validation, deposits no outcome and is not a firing here."
          "The statement covers a transition whose whole output spec is the leaf. A Place leaf inside And, Xor or Timeout contributes its claim {place} to an output branch (IO-015); what that branch must receive is the subject of IO-011, IO-012, IO-013 and IO-015, not of this block."
          "'One or more tokens' is read on the deposit (glossary: Produced set): p is in the produced set. How many tokens beyond one is not constrained: an output branch is a set of places, and several tokens into p conform (IO-015, IO-016 AC4, CORE-036); the reference semantics deposits exactly one (IO-016). Deposits are compared per place (Deposits d p, Produced d p), never by list order (CORE-036)."
          "The second clause (nothing outside p) reads 'a single output place' together with IO-015's exact-explanation rule: the produced set of a firing of a Place(p) spec is exactly {p}."
          "AC1 (output spec declares a single place) is structural and holds by construction: the leaf names one place, outPlaces (Place p) = [p] (checked by example below); the statement's hypothesis selects exactly these transitions."
          "AC2 (produced tokens appear in the place) is the first clause on the deposit and the third clause on the marking. The third clause is a lower bound: it rules out a lost write (the firing reports [p] but leaves p as it was) and a misrouted write (the token lands in another place), also when p already holds tokens. The exact count of p (no extra tokens) is [CORE-030]'s on an input place, [CORE-034]'s on a reset place and [CORE-035]'s third line on every other place; tokens appearing in other places are [CORE-035]'s."
          "'The tokens place kept' is the glossary's effect of a firing on one place: a reset place keeps none [CORE-034], an input place keeps its count minus the consumption count [CORE-030], [IO-007], any other place keeps its count. Inhibitor and read arcs consume nothing [CORE-031], [CORE-032]."
  signoff "2026-11-13 43da83ca0e74b3ef ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t p, OutputSpec t = some (.place p) → ∀ d,
      (on (fun m m' => F t m d m'), shall (fun _ _ => Produced d p)) ∧
      (on (fun m m' => F t m d m'), shall (fun _ _ => ∀ q, Produced d q → q = p)) ∧
      (on (fun m m' => F t m d m'), shall (fun m m' =>
        (if ResetArc t p then 0 else TokenCount m p - Consumes t m p) + Deposits d p ≤
          TokenCount m' p))

/- The pinned readable form of IO-010: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_010 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N) (p : N),
    OutputSpec t = some (Out.place p) →
      ∀ (d : List N),
        (on fun m m' => F t m d m', shall fun x x_1 => Produced d p) ∧
          (on fun m m' => F t m d m', shall fun x x_1 => ∀ (q : N), Produced d q → q = p) ∧
            on fun m m' => F t m d m', shall fun m m' =>
              (if ResetArc t p then 0 else TokenCount m p - Consumes t m p) + Deposits d p ≤ TokenCount m' p
-/
#guard_msgs in #print IO_010

/-- AC1: the leaf `Place(p)` names the single place `p`. -/
example {N : Type} (p : N) : outPlaces (Out.place p) = [p] := rfl

/-- The only deposit the reference semantics offers for the leaf `Place(p)` is the one token in
`p`: its one action branch is `[p]`, and it has no `Timeout` node. -/
theorem deposit_place_leaf {N : Type} (c : N → Nat) (p : N) (ch : Novel.ForwardDeposit.Choice)
    (d : List N) (h : deposit c (some (Out.place p)) ch = some d) : d = [p] := by
  cases ch with
  | action i =>
    cases i with
    | zero => simpa [deposit, Out.branches] using h.symm
    | succ i => simp [deposit, Out.branches] at h
  | timedOut j => simp [deposit, Out.findTimeout] at h

/-- The reference semantics satisfies IO-010: a firing of a transition whose output spec is
`Place(p)` deposits `[p]` (`deposit_place_leaf`), one token in `p` and nothing elsewhere, and
`Seam.fireNC` adds that token to what `p` kept (`refFire_apply`). -/
@[evidence holds IO_010]
theorem IO_010_reference {N : Type} [DecidableEq N] : IO_010 (RefFire (N := N)) := by
  intro t p ht d
  have hd : ∀ m m', RefFire t m d m' → d = [p] := by
    rintro m m' ⟨-, ⟨ch, hch⟩, -⟩
    have ht' : t.out = some (.place p) := ht
    rw [ht'] at hch
    exact deposit_place_leaf _ p ch d hch
  refine ⟨fun m m' h => ?_, fun m m' h q hq => ?_, fun m m' h => ?_⟩
  · rw [hd m m' h]; exact List.mem_singleton_self p
  · rw [hd m m' h] at hq; exact List.mem_singleton.mp hq
  · show _ ≤ m' p
    rw [refFire_apply h p]
    split <;> simp_all

/-! ### Examples over a one-place net -/

/-- The transition of the examples: no arcs in, output spec the leaf `Place(0)`. -/
def io010_t : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.place 0) }

/-- The marking of the examples in which every place is empty. -/
def io010_empty : Nat → Nat := fun _ => 0

/-- The marking after `io010_t` fires from the empty marking: one token in place `0`. -/
def io010_after : Nat → Nat := fun n => if n = 0 then 1 else 0

/-- A firing relation that deposits nothing: every transition may fire from every marking,
leaving it as it is. -/
def io010_idleFire : FireRel Nat := fun _ m d m' => d = [] ∧ m' = m

/-- A firing relation that writes the leaf's place and spills one token into the next place: a
transition whose output spec is `Place(p)` deposits `[p, p + 1]` and adds the deposit to the
marking. -/
def io010_spillFire : FireRel Nat :=
  fun t m d m' => ∃ p, t.out = some (.place p) ∧ d = [p, p + 1] ∧
    m' = fun q => m q + Deposits d q

/-- The marking of the examples in which place `0` holds two tokens and every other place none. -/
def io010_two : Nat → Nat := fun n => if n = 0 then 2 else 0

/-- A firing relation that loses the write: a transition whose output spec is `Place(p)` reports
the deposit `[p]` but leaves the marking as it was. -/
def io010_lostFire : FireRel Nat :=
  fun t m d m' => ∃ p, t.out = some (.place p) ∧ d = [p] ∧ m' = m

/-- A firing relation that misroutes the write: a transition whose output spec is `Place(p)`
reports the deposit `[p]`, but the token lands in place `p + 1`. -/
def io010_misrouteFire : FireRel Nat :=
  fun t m d m' => ∃ p, t.out = some (.place p) ∧ d = [p] ∧
    m' = fun q => if q = p + 1 then m q + 1 else m q

/-- ✗ A firing that deposits nothing violates IO-010 (first clause): `io010_t` fires from the
empty marking with an empty deposit, so place `0` receives no token. -/
@[evidence forbids IO_010]
theorem IO_010_forbids_idle : ¬ IO_010 io010_idleFire := by
  intro h
  have := (h io010_t 0 rfl []).1 io010_empty io010_empty ⟨rfl, rfl⟩
  exact absurd this (by decide)

/-- ✗ A firing that writes a second place violates IO-010 (second clause): `io010_t` deposits
`[0, 1]`, and place `1` is not its leaf's place. -/
@[evidence forbids IO_010]
theorem IO_010_forbids_spill : ¬ IO_010 io010_spillFire := by
  intro h
  have := (h io010_t 0 rfl [0, 1]).2.1 io010_empty (fun q => io010_empty q + Deposits [0, 1] q)
    ⟨0, rfl, rfl, rfl⟩ 1 (by decide)
  exact absurd this (by decide)

/-- ✗ A lost write violates IO-010 (third clause), also when the leaf's place already holds
tokens: `io010_t` reports `[0]` from the marking with one token in place `0` and leaves it there,
so place `0` holds 1 token where it must hold at least 1 + 1. -/
@[evidence forbids IO_010]
theorem IO_010_forbids_lost : ¬ IO_010 io010_lostFire := by
  intro h
  have := (h io010_t 0 rfl [0]).2.2 io010_after io010_after ⟨0, rfl, rfl, rfl⟩
  exact absurd this (by decide)

/-- ✗ A misrouted write violates IO-010 (third clause), also when the leaf's place already holds
tokens: `io010_t` reports `[0]` from the marking with two tokens in place `0`, but the token lands
in place `1`, so place `0` holds 2 tokens where it must hold at least 2 + 1. -/
@[evidence forbids IO_010]
theorem IO_010_forbids_misroute : ¬ IO_010 io010_misrouteFire := by
  intro h
  have := (h io010_t 0 rfl [0]).2.2 io010_two
    (fun q => if q = 0 + 1 then io010_two q + 1 else io010_two q) ⟨0, rfl, rfl, rfl⟩
  exact absurd this (by decide)

/-- A firing relation that writes the leaf's place twice: a transition whose output spec is
`Place(p)` deposits `[p, p]` and adds the deposit to the marking. -/
def io010_multiFire : FireRel Nat :=
  fun t m d m' => ∃ p, t.out = some (.place p) ∧ d = [p, p] ∧
    m' = fun q => m q + Deposits d q

/-- ✓ Several tokens into the leaf's place conform (an output branch is a set of places, IO-015,
IO-016 AC4, CORE-036): a firing that deposits `[p, p]` satisfies every clause of IO-010. -/
@[evidence allows IO_010]
theorem IO_010_allows_multi : IO_010 io010_multiFire := by
  intro t p ht d
  refine ⟨?_, ?_, ?_⟩ <;> rintro m m' ⟨p', hp', rfl, hm'⟩ <;>
  · have : p' = p := by
      have h2 : (some (Out.place p') : Option (Out Nat)) = some (Out.place p) := hp'.symm.trans ht
      cases h2; rfl
    subst this
    first
    | exact List.mem_cons_self ..
    | intro q hq; simp at hq; exact hq
    | subst hm'
      show _ ≤ m p' + Deposits [p', p'] p'
      simp only [TokenCount]
      split <;> omega

/-- The firing relation of an executor with the CONC-026 validation skip enabled, on a `Place(p)`
leaf: the action may write any number of tokens into `p`, none included (CORE-063 still confines
the write to the declared output `p`), and the executor deposits that write unvalidated. -/
def io010_skipFire : FireRel Nat :=
  fun t m d m' => ∃ p k, t.out = some (.place p) ∧ d = List.replicate k p ∧
    m' = fun q => m q + Deposits d q

/-- ✗ The skip executor is outside IO-010's scope (CONC-026): its firing relation lets
`io010_t` fire from the empty marking with the empty write, so the first clause fails. This is why
IO-010 is scoped to executors with output validation enabled. -/
@[evidence forbids IO_010]
theorem IO_010_forbids_skip : ¬ IO_010 io010_skipFire := by
  intro h
  have := (h io010_t 0 rfl []).1 io010_empty (fun q => io010_empty q + Deposits [] q)
    ⟨0, 0, rfl, rfl, rfl⟩
  exact absurd this (by decide)

/-- Mutant reading of IO-010 that drops the first clause: the leaf's firing writes nowhere but
its place, but need not write there at all. -/
def IO_010_mutant_dropProduces {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ (t : Trans N) (p : N), OutputSpec t = some (.place p) → ∀ d : List N,
    (on (fun m m' => F t m d m'), shall (fun _ _ => ∀ q, Produced d q → q = p)) ∧
    (on (fun m m' => F t m d m'), shall (fun m m' =>
      (if ResetArc t p then 0 else TokenCount m p - Consumes t m p) + Deposits d p ≤
        TokenCount m' p))

/-- The idle firing kills the first mutant: an empty deposit writes nowhere else, so the mutant
holds, but it does not put a token in the leaf's place, so IO-010 does not. -/
@[evidence mutant IO_010]
theorem IO_010_mutant_dropProduces_killed :
    IO_010_mutant_dropProduces io010_idleFire ∧ ¬ IO_010 io010_idleFire := by
  refine ⟨?_, IO_010_forbids_idle⟩
  intro t p _ d
  refine ⟨?_, ?_⟩
  · rintro m m' ⟨rfl, -⟩ q hq
    simp [Produced] at hq
  · rintro m m' ⟨rfl, rfl⟩
    have : Deposits ([] : List Nat) p = 0 := rfl
    simp only [TokenCount]
    split <;> omega

/-- Mutant reading of IO-010 that drops the second clause: the leaf's firing puts a token in its
place, but may also write other places. -/
def IO_010_mutant_dropOnly {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ (t : Trans N) (p : N), OutputSpec t = some (.place p) → ∀ d : List N,
    (on (fun m m' => F t m d m'), shall (fun _ _ => Produced d p)) ∧
    (on (fun m m' => F t m d m'), shall (fun m m' =>
      (if ResetArc t p then 0 else TokenCount m p - Consumes t m p) + Deposits d p ≤
        TokenCount m' p))

/-- The spilling firing kills the second mutant: it always writes the leaf's place, so the
mutant holds, but it also writes the next place, so IO-010 does not. -/
@[evidence mutant IO_010]
theorem IO_010_mutant_dropOnly_killed :
    IO_010_mutant_dropOnly io010_spillFire ∧ ¬ IO_010 io010_spillFire := by
  refine ⟨?_, IO_010_forbids_spill⟩
  intro t p ht d
  refine ⟨?_, ?_⟩ <;> rintro m m' ⟨p', hp', rfl, hm'⟩ <;>
  · have : p' = p := by
      have h2 : (some (Out.place p') : Option (Out Nat)) = some (Out.place p) := hp'.symm.trans ht
      cases h2; rfl
    subst this
    first
    | exact List.mem_cons_self ..
    | subst hm'
      show _ ≤ m p' + Deposits [p', p' + 1] p'
      have : Deposits [p', p' + 1] p' = 1 := by simp [Deposits, depProd]
      simp only [TokenCount]
      split <;> omega

/-- Mutant reading of IO-010 that drops the third clause: the leaf's firing reports a token in
its place and nowhere else, but the marking it leaves need not hold that token. -/
def IO_010_mutant_dropMarking {N : Type} (F : FireRel N) : Prop :=
  ∀ (t : Trans N) (p : N), OutputSpec t = some (.place p) → ∀ d : List N,
    (on (fun m m' => F t m d m'), shall (fun _ _ => Produced d p)) ∧
    (on (fun m m' => F t m d m'), shall (fun _ _ => ∀ q, Produced d q → q = p))

/-- The lost write kills the third mutant: it reports the deposit `[p]`, so the mutant holds,
but it leaves the marking unchanged, so IO-010 does not. -/
@[evidence mutant IO_010]
theorem IO_010_mutant_dropMarking_killed :
    IO_010_mutant_dropMarking io010_lostFire ∧ ¬ IO_010 io010_lostFire := by
  refine ⟨?_, IO_010_forbids_lost⟩
  intro t p ht d
  refine ⟨?_, ?_⟩ <;> rintro m m' ⟨p', hp', rfl, -⟩ <;>
  · have : p' = p := by
      have h2 : (some (Out.place p') : Option (Out Nat)) = some (Out.place p) := hp'.symm.trans ht
      cases h2; rfl
    subst this
    first
    | exact List.mem_singleton_self _
    | exact fun q hq => List.mem_singleton.mp hq

/-- All three clauses of IO-010 are exercised by the reference semantics: `io010_t` has the
leaf `Place(0)` as its output spec, it fires from the empty marking depositing `[0]` (so the
clauses' trigger happens and place `0` receives a token), the deposit names place `0` only, and
the marking it leaves holds that token in place `0` (the conclusions are checked on a real
firing, not vacuously). -/
@[evidence nonvacuous IO_010]
theorem IO_010_nonvacuous :
    OutputSpec io010_t = some (.place 0) ∧
      RefFire io010_t io010_empty [0] io010_after ∧
      Produced [0] 0 ∧ (∀ q, Produced [0] q → q = 0) ∧
      TokenCount io010_empty 0 + Deposits [0] 0 ≤ TokenCount io010_after 0 := by
  refine ⟨rfl, ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩, by decide, fun q hq => List.mem_singleton.mp hq,
    by decide⟩
  funext n
  by_cases h : n = 0
  · subst h; simp [fireNC, depProd, nconsumed, nspecAt, io010_t, io010_empty, io010_after]
  · simp [fireNC, depProd, nconsumed, nspecAt, io010_t, io010_empty, io010_after, h,
      Ne.symm h]

end Libpetri.Spec
