import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.CORE_034

set_option linter.missingDocs true

/-!
# CORE-034: Reset arc (`spec/01-core-model.md`)

A predicate over an abstract firing relation `F : FireRel N`, checked against the reference
semantics (`RefFire`), against concrete firing relations that break it, and against one mutant
reading per clause.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-- `t` with every reset arc on `p` removed, and nothing else changed: the transition a reset
arc on `p` that played no part in whether `t` can fire would leave behind. (Local to CORE-034;
the counterpart of `withoutInhibitor`.) -/
def withoutReset [DecidableEq N] (t : Trans N) (p : N) : Trans N :=
  { t with core := { t.core with resets := t.core.resets.filter (· ≠ p) } }

/-! ## CORE-034: Reset arc -/

requirement CORE_034
  id "CORE-034"
  title "Reset arc"
  kind B
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  covers CORE_034.s1, CORE_034.s2, CORE_034.s3, CORE_034.s4
  reading "For every transition t and every reset place p of t, writing t∖p for t without its reset arcs on p:"
          "every firing of t that deposits d leaves p with exactly as many tokens as d puts in p, whatever p held before;"
          "every firing of t∖p from a marking m that deposits d is matched by a firing of t from m whose deposit puts the same number of tokens in every place (a reset arc removes no deposit, and t fires wherever t∖p does);"
          "every firing of t from m that deposits d is matched by a firing of t∖p from m whose deposit puts the same number of tokens in every place and that leaves every place other than p with the same token count (a reset arc adds no deposit, t∖p fires wherever t does, and the arc changes no other place)."
  assumes "A firing is read as one step from a marking to a marking (glossary: Fire); timing and priority play no part. 'Can fire' is read as 'some firing exists', to any target marking: removing a reset arc changes where a firing leads, so the second sentence compares the existence of a firing, not its target. It is the existence half of the second and third lines taken together (`CORE_034_canFire`), so it has no line of its own."
          "Deposits are compared per place (CORE-036): two deposits that put the same number of tokens in every place are the same deposit, whatever their order (`SamePerPlace`)."
          "AC1 (fires even if the reset place is empty) is the second line at a marking with p empty: the reset arc on p adds no condition, so t fires there whenever t∖p does. The text does not claim t fires with its other arcs unsatisfied."
          "AC2 (all tokens removed on firing) is the first line. A reset place that is also an output place keeps what the firing deposited there (glossary: Deposit); a reset place that is also an input place ends with the deposit too, whatever was consumed from it."
          "AC3 (no token requirement, no contribution to enablement) is the second and third lines at every marking, empty or marked."
          "AC4 (same deposits with and without the reset arc, compared per place; a reset arc on an output place neither adds nor removes an outcome) is the second line (no outcome removed) and the third line (no outcome added)."
          "The third line is also the frame of a reset arc: it rules out a reset that also empties a place the transition has no arc to, and a reset whose removed tokens feed a Forward or timeout deposit (they are not consumed; IO-013/IO-014 forward only consumed tokens). It compares against the same transition without the arc rather than spelling out the whole marking change; the effect of the other arcs is CORE-030, CORE-031, CORE-032 and IO-013's subject."
          "The comparison is over firing relations, not over which output specs build: a transition and the same transition without its reset arcs have the same output spec, so the build-time checks of IO-011 to IO-014 accept both or neither."
          "Token counts only: which tokens are removed, and EXEC-003 AC5 (a reset later in the same firing pass leaves same-pass deposits in place) are below this granularity; that refinement is EXEC-003's subject, not this block's."
  signoff "2026-11-13 93e6155b06c813c7 ai"
  statement : ∀ {N : Type} [DecidableEq N], FireRel N → Prop :=
    fun F => ∀ t p, ResetArc t p →
      (∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = Deposits d p)) ∧
      (∀ d, on (fun m m'' => F (withoutReset t p) m d m''), shall (fun m _ =>
        ∃ d' m', F t m d' m' ∧ SamePerPlace d d')) ∧
      (∀ d, on (fun m m' => F t m d m'), shall (fun m m' =>
        ∃ d' m'', F (withoutReset t p) m d' m'' ∧ SamePerPlace d d' ∧
          ∀ q, q ≠ p → TokenCount m' q = TokenCount m'' q))

/- The pinned readable form of CORE-034: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_034 : {N : Type} → [DecidableEq N] → FireRel N → Prop :=
fun {N} [DecidableEq N] F =>
  ∀ (t : Reference.Trans N) (p : N),
    ResetArc t p →
      (∀ (d : List N), on fun m m' => F t m d m', shall fun x m' => TokenCount m' p = Deposits d p) ∧
        (∀ (d : List N),
            on fun m m'' => F (withoutReset t p) m d m'', shall fun m x => ∃ d' m', F t m d' m' ∧ SamePerPlace d d') ∧
          ∀ (d : List N),
            on fun m m' => F t m d m', shall fun m m' =>
              ∃ d' m'',
                F (withoutReset t p) m d' m'' ∧
                  SamePerPlace d d' ∧ ∀ (q : N), q ≠ p → TokenCount m' q = TokenCount m'' q
-/
#guard_msgs in #print CORE_034

/-- The reference semantics satisfies CORE-034: `Seam.fireNC` sets a reset place to the deposit
count (`refFire_apply`), neither `Seam.enabledNA` nor the deposit (`Seam.nconsumed`) reads
the reset arcs, so a firing of `t` and of `t` without its reset arcs on `p` exist at the same
markings with the same deposits, and `Seam.fireNC` reads the reset arcs only at the reset place
itself. -/
@[evidence holds CORE_034, evidence cites "EXEC-013" "AC1 and AC2 on token counts: a firing leaves a reset place holding exactly its deposit (all tokens removed), and a reset arc never affects whether its transition can fire, so an unmarked reset place is no error; the queue-level drain is EXEC_013_reference"]
theorem CORE_034_reference {N : Type} [DecidableEq N] : CORE_034 (RefFire (N := N)) := by
  intro t p hp
  refine ⟨fun d m m' h => ?_, fun d m m'' h => ?_, fun d m m' h => ?_⟩
  · simp [refFire_apply h p, hp]
  · obtain ⟨hen, hd, -⟩ := h
    exact ⟨d, _, ⟨hen, hd, rfl⟩, fun _ => rfl⟩
  · obtain ⟨hen, hd, rfl⟩ := h
    refine ⟨d, _, ⟨hen, hd, rfl⟩, fun _ => rfl, fun q hq => ?_⟩
    simp [fireNC, withoutReset, nconsumed, nspecAt, hq]

/-- The second sentence of CORE-034 follows from the statement: under any firing relation that
satisfies CORE-034, a transition with a reset arc on `p` can fire from exactly the markings
from which it can fire without that arc. -/
theorem CORE_034_canFire {N : Type} [DecidableEq N] {F : FireRel N} (h : CORE_034 F)
    (t : Trans N) (p : N) (hp : ResetArc t p) (m : N → Nat) :
    (∃ m', Fire F t m m') ↔ (∃ m', Fire F (withoutReset t p) m m') := by
  constructor
  · rintro ⟨m', d, hf⟩
    obtain ⟨d', m'', hf', -⟩ := (h t p hp).2.2 d m m' hf
    exact ⟨m'', d', hf'⟩
  · rintro ⟨m'', d, hf⟩
    obtain ⟨d', m', hf', -⟩ := (h t p hp).2.1 d m m'' hf
    exact ⟨m', d', hf'⟩

/-! ### Examples over a small net -/

/-- The main transition of the examples: no inputs, one reset arc on place `0`, no output
spec. -/
def core034_t : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [0] },
    out := none }

/-- A transition whose reset place is also its output place: reset arc on place `0`, output
spec `Place 0`. -/
def core034_tOut : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [0] },
    out := some (.place 0) }

/-- A transition that forwards from its reset place: reset arc on place `0`, no input arc on
it, output spec `Timeout (Forward 0 1)`. -/
def core034_tFwd : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [0] },
    out := some (.timeout (.forward 0 1)) }

/-- The AC4 transition: reset arc on place `0`, output spec `Xor(Place 0, Place 1)`, so the
reset place is one of its output places. -/
def core034_tXor : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [0] },
    out := some (.xor (.place 0) (.place 1)) }

/-- A transition with a reset arc on place `0` and output spec `Xor(Place 1, Place 2)`: two
deposits, neither in its reset place. -/
def core034_tXor12 : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [0] },
    out := some (.xor (.place 1) (.place 2)) }

/-- The marking of the examples in which every place holds three tokens. -/
def core034_full : Nat → Nat := fun _ => 3

/-- The marking after `core034_t` fires from `core034_full`: place `0` emptied, the rest
untouched. -/
def core034_after : Nat → Nat := fun n => if n = 0 then 0 else 3

/-- The marking after `core034_tOut` fires from `core034_full`: place `0` holds only the
token the firing deposited, the rest untouched. -/
def core034_afterOut : Nat → Nat := fun n => if n = 0 then 1 else 3

/-- The marking after `core034_tXor` fires from `core034_full` and deposits in place `1`:
place `0` emptied, place `1` one token more. -/
def core034_afterXor1 : Nat → Nat := fun n => if n = 0 then 0 else if n = 1 then 4 else 3

/-- The marking after `core034_tXor` without its reset arc fires from `core034_full` and
deposits in place `0`. -/
def core034_afterNoReset0 : Nat → Nat := fun n => if n = 0 then 4 else 3

/-- The marking of the examples in which every place is empty. -/
def core034_empty : Nat → Nat := fun _ => 0

/-- The firing that changes nothing: every transition may fire from every marking, depositing
nothing and leaving the marking as it is. -/
def core034_idleFire : FireRel Nat := fun _ m d m' => d = [] ∧ m' = m

/-- ✗ A reset arc that removes nothing violates CORE-034 (first clause): under the idle firing
`core034_t` fires from `core034_full`, deposits nothing, and place `0` keeps its three
tokens. -/
@[evidence forbids CORE_034]
theorem CORE_034_forbids_keepsTokens : ¬ CORE_034 core034_idleFire := by
  intro h
  have := (h core034_t 0 (by decide)).1 [] core034_full core034_full ⟨rfl, rfl⟩
  exact absurd this (by decide)

/-- A firing relation in which the reset is applied after the deposit: a reference firing,
then every reset place set to zero, wiping what the same firing deposited there. -/
def core034_resetAfterDepositFire : FireRel Nat := fun t m d m' =>
  ∃ m'', RefFire t m d m'' ∧ m' = fun n => if n ∈ t.core.resets then 0 else m'' n

/-- ✗ A reset that also removes the firing's own deposit violates CORE-034 (first clause):
`core034_tOut` deposits one token in its reset place `0` and must end holding it, not zero. -/
@[evidence forbids CORE_034]
theorem CORE_034_forbids_resetAfterDeposit : ¬ CORE_034 core034_resetAfterDepositFire := by
  intro h
  have := (h core034_tOut 0 (by decide)).1 [0] core034_empty _
    ⟨_, ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩, rfl⟩
  revert this; decide

/-- A firing relation in which a reset arc requires its place to be marked: a reference firing,
allowed only when every reset place is marked. -/
def core034_resetNeedsTokenFire : FireRel Nat :=
  fun t m d m' => (∀ q ∈ t.core.resets, Marked m q) ∧ RefFire t m d m'

/-- ✗ A reset arc with a token requirement violates CORE-034 (second clause): without its reset
arc `core034_t` fires from the empty marking, with it no firing matches. -/
@[evidence forbids CORE_034]
theorem CORE_034_forbids_resetNeedsToken : ¬ CORE_034 core034_resetNeedsTokenFire := by
  intro h
  have hfire : core034_resetNeedsTokenFire (withoutReset core034_t 0)
      core034_empty [] core034_empty :=
    ⟨by decide, by decide, ⟨.action 0, rfl⟩, by funext n; simp [fireNC, depProd, nconsumed,
      nspecAt, withoutReset, core034_t, core034_empty]⟩
  obtain ⟨_, _, ⟨hne, -⟩, -⟩ := (h core034_t 0 (by decide)).2.1 [] _ _ hfire
  exact absurd (hne 0 (by decide)) (by decide)

/-- A firing relation in which a reset arc pins its transition to its first output branch: a
reference firing, and a transition with a reset arc may only deposit the first branch of its
output spec. The reset arc removes deposit choices, but never whether the transition fires. -/
def core034_firstBranchFire : FireRel Nat := fun t m d m' =>
  RefFire t m d m' ∧ (t.core.resets ≠ [] → deposit (nconsumed m t.core) t.out (.action 0) = some d)

/-- ✗ A reset arc that removes a deposit violates CORE-034 (second clause): without its reset
arc `core034_tXor12` deposits in place `2`, with it only in place `1`. -/
@[evidence forbids CORE_034]
theorem CORE_034_forbids_firstBranch : ¬ CORE_034 core034_firstBranchFire := by
  intro h
  have hfire : core034_firstBranchFire (withoutReset core034_tXor12 0) core034_full [2]
      (fireNC core034_full (withoutReset core034_tXor12 0).core (depProd [2])) :=
    ⟨⟨by decide, ⟨.action 1, rfl⟩, rfl⟩, fun hne => (hne (by decide)).elim⟩
  obtain ⟨d', _, ⟨-, h0⟩, hs⟩ := (h core034_tXor12 0 (by decide)).2.1 _ _ _ hfire
  have hd : some [1] = some d' := h0 (by decide)
  cases hd
  exact absurd (hs 2) (by decide)

/-- A firing relation whose reset loop runs one place too far: a reference firing, then every
place `n + 1` with `n` a reset place (and not itself a reset place) emptied as well. -/
def core034_resetsNeighbourFire : FireRel Nat := fun t m d m' =>
  ∃ m'', RefFire t m d m'' ∧
    m' = fun n => if n ∉ t.core.resets ∧ n ≠ 0 ∧ n - 1 ∈ t.core.resets then 0 else m'' n

/-- `core034_t` (reset on place `0` only) fires from `core034_full` under the neighbour-emptying
firing and leaves place `1`, which it has no arc to, with no tokens. -/
theorem core034_resetsNeighbour_wrong :
    ∃ m', core034_resetsNeighbourFire core034_t core034_full [] m' ∧ m' 1 = 0 :=
  ⟨_, ⟨_, ⟨by decide, ⟨.action 0, rfl⟩, rfl⟩, rfl⟩, by decide⟩

/-- ✗ A reset that also empties a place the transition has no arc to violates CORE-034 (third
clause): without its reset arc `core034_t` leaves place `1` at three tokens, with it place `1`
ends at zero. -/
@[evidence forbids CORE_034]
theorem CORE_034_forbids_resetsNeighbour : ¬ CORE_034 core034_resetsNeighbourFire := by
  intro h
  obtain ⟨m', hm, h1⟩ := core034_resetsNeighbour_wrong
  obtain ⟨d', m'', ⟨_, hr, rfl⟩, -, hq⟩ := (h core034_t 0 (by decide)).2.2 _ _ _ hm
  have := hq 1 (by decide)
  rw [TokenCount, h1] at this
  obtain ⟨-, ⟨ch, hch⟩, rfl⟩ := hr
  have hd' : d' = [] := by
    cases ch with
    | action i =>
      rcases i with _ | i <;> simp [deposit, withoutReset, core034_t] at hch
      exact hch
    | timedOut j => simp [deposit, withoutReset, core034_t] at hch
  subst hd'
  revert this; decide

/-- A firing relation in which the tokens a reset removes count as consumed: a forward or
timeout forward from a reset place moves them all. -/
def core034_resetForwardsFire : FireRel Nat := fun t m d m' =>
  enabledNA m t.core = true ∧
    (∃ ch, deposit (fun n => if n ∈ t.core.resets then m n else nconsumed m t.core n) t.out ch
      = some d) ∧
    m' = fireNC m t.core (depProd d)

/-- ✗ A reset whose removed tokens feed a forward violates CORE-034 (third clause): on timeout
`core034_tFwd` forwards the three tokens its reset removed from place `0` into place `1`, a
deposit no firing of `core034_tFwd` without its reset arc makes, in any order (it consumed
nothing from `0`). -/
@[evidence forbids CORE_034]
theorem CORE_034_forbids_resetForwards : ¬ CORE_034 core034_resetForwardsFire := by
  intro h
  have hf : core034_resetForwardsFire core034_tFwd core034_full [1, 1, 1]
      (fireNC core034_full core034_tFwd.core (depProd [1, 1, 1])) :=
    ⟨by decide, ⟨.timedOut 0, by decide⟩, rfl⟩
  obtain ⟨d', _, ⟨-, ⟨ch, hch⟩, -⟩, hs, -⟩ := (h core034_tFwd 0 (by decide)).2.2 _ _ _ hf
  have h1 := hs 1
  cases ch with
  | action i =>
    rcases i with _ | i <;>
      simp [deposit, Out.branches, withoutReset, core034_tFwd] at hch
    subst hch; revert h1; decide
  | timedOut j =>
    rcases j with _ | j <;>
      simp [deposit, Out.findTimeout, Out.timeoutDeposits, withoutReset, core034_tFwd,
        nconsumed, nspecAt] at hch
    subst hch; revert h1; decide

/-- Mutant reading of CORE-034 that drops the first clause: a reset arc neither adds nor removes
a deposit and changes nothing but its own place, but need not empty it. -/
def CORE_034_mutant_dropEmpties {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, ResetArc t p →
    (∀ d, on (fun m m'' => F (withoutReset t p) m d m''), shall (fun m _ =>
      ∃ d' m', F t m d' m' ∧ SamePerPlace d d')) ∧
    (∀ d, on (fun m m' => F t m d m'), shall (fun m m' =>
      ∃ d' m'', F (withoutReset t p) m d' m'' ∧ SamePerPlace d d' ∧
        ∀ q, q ≠ p → TokenCount m' q = TokenCount m'' q))

/-- The idle firing kills the first mutant: it satisfies the mutant (every transition fires from
every marking, whatever its arcs, deposits nothing and changes nothing) but not CORE-034 (place
`0` keeps its tokens). -/
@[evidence mutant CORE_034]
theorem CORE_034_mutant_dropEmpties_killed :
    CORE_034_mutant_dropEmpties core034_idleFire ∧ ¬ CORE_034 core034_idleFire := by
  refine ⟨?_, CORE_034_forbids_keepsTokens⟩
  intro t p _
  refine ⟨?_, ?_⟩
  · rintro d m m' ⟨rfl, rfl⟩
    exact ⟨[], _, ⟨rfl, rfl⟩, fun _ => rfl⟩
  · rintro d m m' ⟨rfl, rfl⟩
    exact ⟨[], _, ⟨rfl, rfl⟩, fun _ => rfl, fun _ _ => rfl⟩

/-- Mutant reading of CORE-034 that drops the second clause (the converse direction): a reset arc
empties its place, adds no deposit and touches nothing else, but may remove a deposit. -/
def CORE_034_mutant_dropRemoves {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, ResetArc t p →
    (∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = Deposits d p)) ∧
    (∀ d, on (fun m m' => F t m d m'), shall (fun m m' =>
      ∃ d' m'', F (withoutReset t p) m d' m'' ∧ SamePerPlace d d' ∧
        ∀ q, q ≠ p → TokenCount m' q = TokenCount m'' q))

/-- The first-branch firing kills the second mutant: its firings are reference firings, so they
empty every reset place and are matched by the firing without the arc (the mutant holds; a
deposit of the first branch stays one when a reset arc is dropped, because the deposit does not
read the reset arcs), but `core034_tXor12` cannot deposit in place `2` although it can without
its reset arc (CORE-034 fails). -/
@[evidence mutant CORE_034]
theorem CORE_034_mutant_dropRemoves_killed :
    CORE_034_mutant_dropRemoves core034_firstBranchFire ∧
      ¬ CORE_034 core034_firstBranchFire := by
  refine ⟨?_, CORE_034_forbids_firstBranch⟩
  intro t p hp
  refine ⟨fun d m m' h => (CORE_034_reference t p hp).1 d m m' h.1, fun d m m' h => ?_⟩
  obtain ⟨⟨hen, hd, rfl⟩, h0⟩ := h
  refine ⟨d, _, ⟨⟨hen, hd, rfl⟩, fun hne => h0 ?_⟩, fun _ => rfl, fun q hq => ?_⟩
  · intro ht; apply hne; simp [withoutReset, ht]
  · simp [fireNC, withoutReset, nconsumed, nspecAt, hq]

/-- Mutant reading of CORE-034 that drops the third clause: a reset arc empties its place and
removes no deposit, but may add one or act on other places too. -/
def CORE_034_mutant_dropFrame {N : Type} [DecidableEq N] (F : FireRel N) : Prop :=
  ∀ t p, ResetArc t p →
    (∀ d, on (fun m m' => F t m d m'), shall (fun _ m' => TokenCount m' p = Deposits d p)) ∧
    (∀ d, on (fun m m'' => F (withoutReset t p) m d m''), shall (fun m _ =>
      ∃ d' m', F t m d' m' ∧ SamePerPlace d d'))

/-- The neighbour-emptying firing kills the third mutant: the reset place itself ends with the
deposit and every firing without the arc is matched by one with it (the mutant holds), but
place `1` is emptied by a reset on place `0` (CORE-034 fails). -/
@[evidence mutant CORE_034]
theorem CORE_034_mutant_dropFrame_killed :
    CORE_034_mutant_dropFrame core034_resetsNeighbourFire ∧
      ¬ CORE_034 core034_resetsNeighbourFire := by
  refine ⟨?_, CORE_034_forbids_resetsNeighbour⟩
  intro t p hp
  refine ⟨fun d m m' h => ?_, fun d m m'' h => ?_⟩
  · obtain ⟨_, hr, rfl⟩ := h
    have hp' : p ∈ t.core.resets := hp
    show (if _ then _ else _) = _
    rw [if_neg (by simp [hp']), refFire_apply hr p, if_pos hp]
  · obtain ⟨_, ⟨hen, hd, -⟩, -⟩ := h
    exact ⟨d, _, ⟨_, ⟨hen, hd, rfl⟩, rfl⟩, fun _ => rfl⟩

/-- All three clauses of CORE-034 are exercised by the reference semantics: `core034_t` has a
reset arc on place `0`; from `core034_full` it fires and empties place `0` (first clause, three
tokens removed, none deposited), where without its reset arc place `0` would keep them, while
every other place ends the same with and without the arc (third clause); it fires from the empty
marking, as it does without its reset arc (second clause, reset place unmarked);
`core034_tOut`, whose reset place is also its output place, ends with place `0` holding the one
token it deposited there (first clause with a nonzero deposit); and `core034_tXor` (AC4), with
the reset arc on one of its two output places, deposits in place `0` or in place `1` exactly as
it does without the arc, and after depositing in place `0` holds that token alone there. -/
@[evidence nonvacuous CORE_034]
theorem CORE_034_nonvacuous :
    ResetArc core034_t 0 ∧
      RefFire core034_t core034_full [] core034_after ∧ core034_after 0 = 0 ∧
      RefFire (withoutReset core034_t 0) core034_full [] core034_full ∧
      (∀ q, q ≠ 0 → core034_after q = core034_full q) ∧
      Fire RefFire core034_t core034_empty core034_empty ∧
      Fire RefFire (withoutReset core034_t 0) core034_empty core034_empty ∧
      RefFire core034_tOut core034_full [0] core034_afterOut ∧ core034_afterOut 0 = 1 ∧
      ResetArc core034_tXor 0 ∧
      RefFire core034_tXor core034_full [0] core034_afterOut ∧
      RefFire core034_tXor core034_full [1] core034_afterXor1 ∧
      RefFire (withoutReset core034_tXor 0) core034_full [0] core034_afterNoReset0 ∧
      RefFire (withoutReset core034_tXor 0) core034_full [1]
        (fun n => if n = 1 then 4 else 3) := by
  refine ⟨by decide, ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩, rfl, ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩,
    fun q hq => by simp [core034_after, core034_full, hq],
    ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩, ⟨[], by decide, ⟨.action 0, rfl⟩, ?_⟩,
    ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩, rfl, by decide,
    ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩, ⟨by decide, ⟨.action 1, rfl⟩, ?_⟩,
    ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩, ⟨by decide, ⟨.action 1, rfl⟩, ?_⟩⟩
  · funext n; by_cases h : n = 0 <;>
      simp [fireNC, depProd, nconsumed, nspecAt, core034_t, core034_full, core034_after, h]
  · funext n; simp [fireNC, depProd, nconsumed, nspecAt, withoutReset, core034_t, core034_full]
  · funext n; simp [fireNC, depProd, nconsumed, nspecAt, core034_t, core034_empty]
  · funext n; simp [fireNC, depProd, nconsumed, nspecAt, withoutReset, core034_t,
      core034_empty]
  · funext n; by_cases h : n = 0
    · simp [fireNC, depProd, core034_tOut, core034_afterOut, h]
    · simp [fireNC, depProd, nconsumed, nspecAt, core034_tOut, core034_full, core034_afterOut, h,
        Ne.symm h]
  · funext n; by_cases h : n = 0
    · simp [fireNC, depProd, core034_tXor, core034_afterOut, h]
    · simp [fireNC, depProd, nconsumed, nspecAt, core034_tXor, core034_full, core034_afterOut, h,
        Ne.symm h]
  · funext n; by_cases h : n = 0
    · simp [fireNC, depProd, core034_tXor, core034_afterXor1, h]
    · by_cases h1 : n = 1
      · subst h1; simp [fireNC, depProd, nconsumed, nspecAt, core034_tXor, core034_full,
          core034_afterXor1]
      · simp [fireNC, depProd, nconsumed, nspecAt, core034_tXor, core034_full, core034_afterXor1,
          h, h1, Ne.symm h1]
  · funext n; by_cases h : n = 0
    · subst h; simp [fireNC, depProd, nconsumed, nspecAt, withoutReset, core034_tXor,
        core034_full, core034_afterNoReset0]
    · simp [fireNC, depProd, nconsumed, nspecAt, withoutReset, core034_tXor, core034_full,
        core034_afterNoReset0, h, Ne.symm h]
  · funext n; by_cases h : n = 1
    · subst h; simp [fireNC, depProd, nconsumed, nspecAt, withoutReset, core034_tXor,
        core034_full]
    · simp [fireNC, depProd, nconsumed, nspecAt, withoutReset, core034_tXor, core034_full,
        h, Ne.symm h]

end Libpetri.Spec
