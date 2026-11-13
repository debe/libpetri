import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.GlossaryQueue
import Libpetri.Spec.Req.EXEC_010
import Libpetri.Spec.Req.EXEC_020
import Libpetri.Spec.Text.CORE_013

set_option linter.missingDocs true

/-!
# CORE-013: Token FIFO ordering (`spec/01-core-model.md`)

The requirement is a predicate over an abstract queue firing relation `Q : QFireRel N T`
(glossary `GlossaryQueue.lean`): `Q t M δ e M'` says that `t` fires from the queue marking `M`,
delivers `δ` to its action, the action emits `e`, and the firing leaves `M'`. It says how one
firing changes the queue of a place: a place that is neither an input place nor a reset place
keeps its whole queue and gains the emitted tokens at the tail, and an input place hands its
action some of its first tokens, in queue order, and (unless it is also a reset place) loses
exactly those and gains the emitted tokens at the tail.

The block is derived: `core013_of_EXEC` proves it of every relation that satisfies [EXEC-010]
and [EXEC-020], so the holds theorem is those two blocks' holds theorems composed, and every
relation it forbids is forbidden by one of them too. The evidence checks it against the
reference queue firing (`RefQFire`), against an executor that deposits at the head of the queue
(`exec020_prependFire`), one that delivers newest first (`exec010_revSel`), one that keeps every
place sorted by token timestamp (`core013_stampSel`, the "oldest is the smallest created_at"
reading of clash K8), one whose read arcs pop the head of a read place (`core013_readPopFire`),
and against three mutant readings: a stack (LIFO), a bag that keeps the right tokens in any
order, and a reading that lets every place that is not a reset place lose some of its first
tokens.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## CORE-013: Token FIFO ordering -/

requirement CORE_013
  id "CORE-013"
  title "Token FIFO Ordering"
  kind B
  scope "all executors"
  source verbatim "spec/01-core-model.md"
  covers CORE_013.s1, CORE_013.s2, CORE_013.s3, CORE_013.s4
  reading "For every queue firing relation Q:"
          "for every firing of a transition t and every place p that is neither an input place nor a reset place of t: the queue p holds after the firing is the queue it held before the firing, followed by the tokens the action emitted to p, in emission order;"
          "for every firing of a transition t and every input place p of t: there is a number k such that the tokens delivered to the action from p are the first k tokens of p's queue before the firing, in queue order, and, if p is not a reset place of t, the queue p holds after the firing is the queue it held before without those k tokens, followed by the tokens the action emitted to p, in emission order."
  assumes "A firing relates a queue marking before it to the queue marking after it, with what it delivered to the action and the emissions of the action (glossary: Queue order, QueueMarking, Delivered, QFireRel, Emitted to). 'Oldest' is read as the glossary's Queue order defines it: the oldest token is the head of the place, the one added first (OldestFirst, Head). It is not the token with the smallest timestamp (created_at): a token can carry a stamp older than a token added before it (a host-supplied stamp, CORE-011; a restore, CORE-073), and an executor that keeps each place sorted by stamp is forbidden (CORE_013_forbids_stampOrder). The rewording of the word 'oldest' in NU-020 that clash K8 proposes is approved by ruling D20 (a); this block does not rely on it."
          "The firing is atomic, as one step of Q is: both shall sentences are scoped to a firing with nothing else changing the marking between its consumption and its deposit. In all three runtimes an asynchronous action's outputs are deposited when its completion is processed, in a later cycle than the consumption (Java BitmapNetExecutor fireTransition and its completion handler; Rust and TypeScript alike), and other firings and injected tokens can change the place in between: if t, asynchronous, deposits into p while a synchronous u consumes p's head before t completes, p does not end holding its whole queue from before t's firing. The same order for interleaved firings (each firing takes the head when it starts and appends at the tail when it completes) is stated locally by EXEC-010 and EXEC-020; over the executor cycle it is the companion of the executor model (RefExec, W5)."
          "Correlated inputs (ruling D16, clash K7): the second shall sentence excludes a correlated input of a ν-net match specification, as EXEC-010 does. The first needs no exclusion: every place a match names is a declared input (NU-020), and the first sentence speaks only of places that are not input places. The transitions of the model (Reference.Trans) carry no match specification, so every input place is one that is not a correlated input, and line 2 quantifies over every input place. How a correlated input consumes is NU-020's, not encoded here; this block makes no claim about it. The model's scope is what keeps correlated inputs out of line 2 today, and the holds theorem is the check that it still does: if the model gains match specifications and the reference consumes a correlated input by name, line 2 fails at a correlated input whose matched tokens are not the head of its queue, CORE_013_reference (through EXEC_010_reference) can no longer be proved, and the exclusion must then be written into line 2."
          "The prose sentence on the oldest token carries the same exception in its own words (ruling D30, which extends D16 to the count-level sentences of CORE-013, CORE-022, IO-001 and IO-003 to IO-005), so the section's normative sentences agree on correlated inputs."
          "Line 1 is the first shall sentence and the prose sentence 'Tokens within a place are stored in FIFO (first-in, first-out) order.', as far as one firing can show it: a place the firing neither consumes from nor resets keeps every token it held, in queue order, and gains tokens only at the tail, in the order the action produced them. That such a place loses nothing is also EXEC-020's second line and CORE-035's count line; line 1 states it so that the first shall sentence cannot be read as letting a firing take head tokens from a read, inhibitor, output or untouched place. Input places are line 2's. A reset place is left out: it ends the firing holding exactly what was deposited there (CORE-034, EXEC-013). Line 1 kills an executor that deposits at the head of the queue (CORE_013_forbids_headDeposit), an executor whose read arcs pop the head of a read place (CORE_013_forbids_readPop), a bag reading that keeps the right tokens in any order (CORE_013_mutant_bag_killed), and the weaker reading that lets every place that is not a reset place lose some of its first tokens (CORE_013_mutant_headLoss_killed)."
          "Line 2 is the second shall sentence and the prose sentence 'The oldest token is consumed first when a transition fires, except on a correlated input of a match specification ([NU-020]).': the action receives the first tokens of each input place, in queue order, and on an input place that is not a reset place the place keeps the rest of its queue, followed by the emitted tokens in emission order, since the same k fixes the delivery and the removal. How many tokens leave (k) is the consumption count of the input arc (EXEC-010, IO-007, CORE-030), not repeated here. On an input place that is also a reset place only the delivery half applies; the place is drained (CORE-034). Line 2 says nothing about what is delivered from a place that is not an input place, as EXEC-010 and EXEC_013.lean leave it open; an action that receives tokens from such a place is ruled out by CORE-060 AC4 (CORE_060 line 4) and CORE-063 (CORE_063). Delivering the oldest tokens newest first is killed by line 2 (CORE_013_forbids_reversed), and so is a stack reading (CORE_013_mutant_lifo_killed)."
          "The block is derived: core013_of_EXEC proves it of every relation that satisfies EXEC-010 and EXEC-020 (line 1 is EXEC-020's first two lines on a place that is neither an input nor a reset place), so it adds no constraint of its own at the grain of one firing, and its holds theorem is EXEC_010_reference and EXEC_020_reference composed. It is kept as a block because CORE-013 is the requirement the other IDs cite for queue order (EXEC-010, CORE-073, MOD-021)."
          "Order across the phases of the executor (tokens injected through an environment place, the initial marking, tokens deposited earlier in the same firing pass, and a restore, CORE-073 AC6) needs the executor model (RefExec, wave W5) and is deferred to it. Tokens an action published before it completed (IO-015) are not modelled: the action emits only at the end of the atomic firing (ruling D17)."
          "AC1 (tokens A, B, C added in order, consuming one yields A) and AC2 (consuming again yields B) are checked on the reference by CORE_013_nonvacuous, with tokens 10, 11, 12 for A, B, C added one after another to place 0 of the empty marking (and 40 to place 2): the first firing of a One input on place 0 delivers 10 and leaves 11, 12 on place 0 and 40, 30 on the output place 2; the second delivers 11 and leaves 12. The statement gives only the consuming half of the two criteria, and only up to the count: under it alone a firing may deliver any prefix of the queue, and that a One input takes exactly one token is EXEC-010's count line (with IO-007 and CORE-030). The adding half (a token added outside a firing goes at the tail, so A, B, C added in order are held as A, B, C) is CORE-070's add line, which rejects a store that adds at the head; CORE_013_nonvacuous builds its marking with the reference add (qAppend) and does not test it. Adding through an environment place or a restore, across the executor's phases, is RefExec's (W5)."
          "The test derivation (add three tokens, remove them one at a time, check FIFO order) is the same check as AC1 and AC2. Adding a token outside a firing is CORE-070's add line, and removing one outside a firing is CORE-070's removeFirst (removeFirst_fst: it returns the head); CORE_070_nonvacuous runs the adds and a removal on the reference."
  signoff "2026-11-13 cd1eca5bb95e9b90 ai"
  statement : ∀ {N T : Type} [DecidableEq N], QFireRel N T → Prop :=
    fun Q =>
      (∀ t δ e p, p ∉ inPlaces t → ¬ ResetArc t p →
        on (fun M M' => Q t M δ e M'), shall (fun M M' =>
          M' p = M p ++ EmittedTo e p)) ∧
      (∀ t δ e p, p ∈ inPlaces t →
        on (fun M M' => Q t M δ e M'), shall (fun M M' =>
          ∃ k, δ.inputs p = OldestFirst M p k ∧
            (¬ ResetArc t p → M' p = (M p).drop k ++ EmittedTo e p)))

/- The pinned readable form of CORE-013: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CORE_013 : {N T : Type} → [DecidableEq N] → QFireRel N T → Prop :=
fun {N T} [DecidableEq N] Q =>
  (∀ (t : Reference.Trans N) (δ : Delivered N T) (e : List (N × T)),
      ∀ p ∉ inPlaces t, ¬ResetArc t p → on fun M M' => Q t M δ e M', shall fun M M' => M' p = M p ++ EmittedTo e p) ∧
    ∀ (t : Reference.Trans N) (δ : Delivered N T) (e : List (N × T)),
      ∀ p ∈ inPlaces t,
        on fun M M' => Q t M δ e M', shall fun M M' =>
          ∃ k, δ.inputs p = OldestFirst M p k ∧ (¬ResetArc t p → M' p = List.drop k (M p) ++ EmittedTo e p)
-/
#guard_msgs in #print CORE_013

/-! ### Derived from EXEC-010 and EXEC-020 -/

/-- On an input place that is not a reset place, EXEC-010 and EXEC-020 together fix the queue
after the firing: the queue before it without its `Consumes` oldest tokens, then the emitted
tokens in emission order. EXEC-010 gives the kept tokens as a prefix and the content up to
order; EXEC-020 gives the emitted tokens as the tail. -/
theorem core013_input_queue {N T : Type} [DecidableEq N] {Q : QFireRel N T}
    (h10 : EXEC_010 Q) (h20 : EXEC_020 Q) {t : Trans N} {M M' : QueueMarking N T}
    {δ : Delivered N T} {e : List (N × T)} (hq : Q t M δ e M') {p : N}
    (hp : p ∈ inPlaces t) (hr : ¬ ResetArc t p) :
    M' p = (M p).drop (Consumes t (Counts M) p) ++ EmittedTo e p := by
  obtain ⟨base, happ, -, -⟩ := h20 t M δ e M' hq
  have hM' : M' p = base p ++ EmittedTo e p := happ p
  obtain ⟨hpre, hperm⟩ := h10.1 t δ e p hp hr M M' hq
  have hlen : ((M p).drop (Consumes t (Counts M) p)).length = (base p).length := by
    have := hperm.length_eq
    rw [hM'] at this
    simp only [List.length_append] at this
    omega
  have hpre' : (M p).drop (Consumes t (Counts M) p) <+: base p ++ EmittedTo e p := hM' ▸ hpre
  have hb : (M p).drop (Consumes t (Counts M) p) <+: base p :=
    List.prefix_of_prefix_length_le hpre' (List.prefix_append _ _) (Nat.le_of_eq hlen)
  rw [hM', hb.eq_of_length hlen]

/-- CORE-013 is a consequence of EXEC-010 and EXEC-020, for every queue firing relation: the
block adds no constraint of its own at the grain of one firing. -/
theorem core013_of_EXEC {N T : Type} [DecidableEq N] {Q : QFireRel N T}
    (h10 : EXEC_010 Q) (h20 : EXEC_020 Q) : CORE_013 Q := by
  refine ⟨fun t δ e p hi hr M M' hq => ?_, fun t δ e p hp M M' hq => ?_⟩
  · obtain ⟨base, happ, hkeep, -⟩ := h20 t M δ e M' hq
    rw [← hkeep p hi hr]
    exact happ p
  · exact ⟨_, h10.2.1 t δ e p hp M M' hq, fun hr => core013_input_queue h10 h20 hq hp hr⟩

/-! ### The reference -/

/-- The reference queue firing satisfies CORE-013: it satisfies EXEC-010 and EXEC-020
(`EXEC_010_reference`, `EXEC_020_reference`), and CORE-013 follows from them
(`core013_of_EXEC`). -/
@[evidence holds CORE_013]
theorem CORE_013_reference {N T : Type} [DecidableEq N] :
    CORE_013 (RefQFire (N := N) (T := T)) :=
  core013_of_EXEC EXEC_010_reference EXEC_020_reference

/-! ### Examples (AC1 and AC2) -/

/-- One `One` input on place 0, output place 2; no read, inhibitor or reset arc. -/
def core013T : Trans Nat :=
  { core := { name := "take", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 2) }

/-- The empty marking with the tokens 10, 11 and 12 added to place 0 one after another (A, B,
C of AC1), and 40 to place 2. -/
def core013M0 : QueueMarking Nat Nat := qAppend qEmpty [(0, 10), (2, 40), (0, 11), (0, 12)]

/-- The marking the first firing of `core013T` leaves, its action emitting 30 to place 2. -/
def core013M1 : QueueMarking Nat Nat := qFire core013M0 core013T [(2, 30)]

/-- Both lines of CORE-013 are exercised by the reference, and AC1 and AC2 hold. Place 0 is an
input place that is not a reset place, so both lines apply to it; place 2 is neither an input
nor a reset place, so line 1 applies to it. AC1: the first firing from `core013M0` delivers
`[10]` (A) and leaves `[11, 12]` on place 0, and `[40, 30]` on place 2 (the emitted token behind
the one already there). AC2: the second firing, from what the first left, delivers `[11]` (B)
and leaves `[12]`. -/
@[evidence nonvacuous CORE_013]
theorem CORE_013_nonvacuous :
    (core013M0 0 = [10, 11, 12] ∧ 0 ∈ inPlaces core013T ∧ ¬ ResetArc core013T 0 ∧
      2 ∉ inPlaces core013T ∧ ¬ ResetArc core013T 2) ∧
    (∃ δ M', RefQFire core013T core013M0 δ [(2, 30)] M' ∧
      δ.inputs 0 = [10] ∧ M' 0 = [11, 12] ∧ M' 2 = [40, 30]) ∧
    (∃ δ M', RefQFire core013T core013M1 δ [(2, 30)] M' ∧
      δ.inputs 0 = [11] ∧ M' 0 = [12]) := by
  refine ⟨by decide, ?_, ?_⟩
  · exact ⟨qDelivered core013M0 core013T, core013M1,
      ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, by decide, by decide, by decide⟩
  · exact ⟨qDelivered core013M1 core013T, qFire core013M1 core013T [(2, 30)],
      ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩, by decide, by decide⟩

/-! ### Relations that break it -/

/-- ✗ Depositing at the head of the queue violates CORE-013 (line 1): firing `qexT .one` from
`exec020M` with 30 emitted to place 2, which already holds 40, leaves `[30, 40]` there, where
line 1 requires `[40, 30]`. -/
@[evidence forbids CORE_013]
theorem CORE_013_forbids_headDeposit :
    ¬ CORE_013 (exec020_prependFire (N := Nat) (T := Nat)) := by
  intro h
  have hk := h.1 (qexT .one) _ [(2, 30)] 2 (by decide) (by decide) exec020M _
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have hl : EmittedTo [((2 : Nat), (30 : Nat))] 2 ++ qConsume exec020M (qexT .one) 2 = [30, 40] := by
    decide
  have he : EmittedTo [((2 : Nat), (30 : Nat))] 2 = [30] := by decide
  have h2 : exec020M 2 = [40] := by decide
  beta_reduce at hk
  rw [hl, he, h2] at hk
  exact exec020_ne_prepended _ hk

/-- ✗ Delivering the oldest tokens newest first violates CORE-013 (line 2): `Exactly(2)` from
`[10, 11, 12]` delivers `[11, 10]`, which is no prefix of the queue. -/
@[evidence forbids CORE_013]
theorem CORE_013_forbids_reversed :
    ¬ CORE_013 (exec010_by (N := Nat) (T := Nat) exec010_revSel) := by
  intro h
  obtain ⟨k, hk, -⟩ := h.2 (qexT (.exactly 2)) _ exec010_e 0 (by decide) _ _
    (exec010_by_fires exec010_revSel (.exactly 2) (by decide))
  have h1 : (exec010_delivered exec010_revSel qexM (qexT (.exactly 2))).inputs 0 = [11, 10] := by
    decide
  have h2 : qexM 0 = [10, 11, 12] := by decide
  rw [h1, OldestFirst, h2] at hk
  match k, hk with
  | 0, h => simp at h
  | 1, h => simp at h
  | 2, h => simp at h
  | k + 3, h => simp at h

/-- "Oldest" read as "smallest timestamp" (clash K8): with each token standing for its own
`created_at`, the place is kept sorted by stamp, and a firing takes the `k` smallest stamps. -/
def core013_stampSel (l : List Nat) (k : Nat) : List Nat × List Nat :=
  let s := l.insertionSort (· ≤ ·)
  (s.take k, s.drop k)

/-- `qexM` with place 0 holding 12, 10, 11 in queue order: the token added first carries the
newest stamp (a host-supplied stamp, CORE-011, or a restore, CORE-073). -/
def core013StampM : QueueMarking Nat Nat :=
  fun p => if p = 0 then [12, 10, 11] else if p = 1 then [20, 21] else []

/-- ✗ An executor that keeps every place sorted by token timestamp violates CORE-013 (line 2):
`One` from the queue `[12, 10, 11]` delivers `[10]`, the smallest stamp, where the spec requires
the head `12`. -/
@[evidence forbids CORE_013]
theorem CORE_013_forbids_stampOrder :
    ¬ CORE_013 (exec010_by (N := Nat) (T := Nat) core013_stampSel) := by
  intro h
  obtain ⟨k, hk, -⟩ := h.2 (qexT .one) _ exec010_e 0 (by decide) core013StampM _
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have h1 : (exec010_delivered core013_stampSel core013StampM (qexT .one)).inputs 0 = [10] := by
    decide
  have h2 : core013StampM 0 = [12, 10, 11] := by decide
  rw [h1, OldestFirst, h2] at hk
  match k, hk with
  | 0, h => simp at h
  | k + 1, h => simp at h

/-- One `One` input on place 0, a read arc (no reset) on place 1, output place 2. -/
def core013ReadT : Trans Nat :=
  { core := { name := "peek", inputs := [⟨0, .one⟩], inhibitors := [], reads := [1], resets := [] },
    out := some (.place 2) }

/-- The consume of an executor whose read opcode pops the head of a read place that is not an
input place, where it should only peek; every other place is consumed as the reference does. -/
def core013_readPop {N T : Type} [DecidableEq N] (M : QueueMarking N T) (t : Trans N) :
    QueueMarking N T :=
  fun p => if p ∈ t.core.reads ∧ p ∉ inPlaces t then (qConsume M t p).drop 1 else qConsume M t p

/-- **Mutant executor: a read arc that pops.** It delivers and deposits as the reference does,
but its consume is `core013_readPop`. -/
def core013_readPopFire {N T : Type} [DecidableEq N] : QFireRel N T := fun t M δ e M' =>
  Enabled t (Counts M) ∧
    (∃ ch, deposit (Consumes t (Counts M)) (OutputSpec t) ch = some (e.map Prod.fst)) ∧
    δ = qDelivered M t ∧ M' = qAppend (core013_readPop M t) e

/-- ✗ A read arc that pops the head of its place violates CORE-013 (line 1): firing
`core013ReadT` from `qexM`, whose read place 1 holds `[20, 21]`, leaves `[21]` there, where
line 1 requires `[20, 21]` (nothing is emitted to place 1). -/
@[evidence forbids CORE_013]
theorem CORE_013_forbids_readPop :
    ¬ CORE_013 (core013_readPopFire (N := Nat) (T := Nat)) := by
  intro h
  have hk := h.1 core013ReadT _ [(2, 30)] 1 (by decide) (by decide) qexM _
    ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  revert hk
  decide

/-! ### Mutant: any place may lose head tokens -/

/-- Mutant reading of the first shall sentence that lets every place that is not a reset place
end the firing holding the last tokens of its queue (all, some or none of them), followed by the
emitted tokens: input places are as in CORE-013, but a read, inhibitor, output or untouched
place may lose some of its first tokens. -/
def CORE_013_mutant_headLoss {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  (∀ t δ e p, ¬ ResetArc t p →
    on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      ∃ k, M' p = (M p).drop k ++ EmittedTo e p)) ∧
  (∀ t δ e p, p ∈ inPlaces t →
    on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      ∃ k, δ.inputs p = OldestFirst M p k ∧
        (¬ ResetArc t p → M' p = (M p).drop k ++ EmittedTo e p)))

/-- The read-pop executor satisfies the head-loss reading at every type, but not CORE-013
(`CORE_013_forbids_readPop`). -/
@[evidence mutant CORE_013]
theorem CORE_013_mutant_headLoss_killed :
    CORE_013_mutant_headLoss (core013_readPopFire (N := Nat) (T := Nat)) ∧
      ¬ CORE_013 (core013_readPopFire (N := Nat) (T := Nat)) := by
  refine ⟨⟨fun t δ e p hr M M' h => ?_, fun t δ e p hp M M' h => ?_⟩,
    CORE_013_forbids_readPop⟩
  · obtain ⟨-, -, -, rfl⟩ := h
    have hr' : p ∉ t.core.resets := hr
    show ∃ k, qAppend (core013_readPop M t) e p = (M p).drop k ++ qEmittedTo e p
    rw [qAppend_apply]
    by_cases hc : p ∈ t.core.reads ∧ p ∉ inPlaces t
    · refine ⟨qTake M t p + 1, ?_⟩
      simp only [core013_readPop, hc, not_false_eq_true, and_self, if_true, qConsume, hr',
        if_false, qPostInput, List.drop_drop]
    · refine ⟨qTake M t p, ?_⟩
      simp only [core013_readPop, hc, if_false, qConsume, hr', qPostInput]
  · obtain ⟨-, -, rfl, rfl⟩ := h
    refine ⟨qTake M t p, rfl, fun hr => ?_⟩
    have hr' : p ∉ t.core.resets := hr
    have hc : ¬ (p ∈ t.core.reads ∧ p ∉ inPlaces t) := fun h => h.2 hp
    show qAppend (core013_readPop M t) e p = (M p).drop (qTake M t p) ++ qEmittedTo e p
    rw [qAppend_apply]
    simp only [core013_readPop, hc, if_false, qConsume, hr', qPostInput]

/-! ### Mutant: a stack -/

/-- Mutant reading of CORE-013 as a stack (LIFO): on an input place that is not a reset place
and receives no emission, the action receives the newest tokens and the place keeps the oldest
ones. -/
def CORE_013_mutant_lifo {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  ∀ t δ e p, p ∈ inPlaces t → ¬ ResetArc t p → EmittedTo e p = [] →
    on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      ∃ k, δ.inputs p = (M p).drop k ∧ M' p = (M p).take k)

/-- The LIFO executor (`exec010_lifoSel`) satisfies the stack reading but not CORE-013: `One`
from `[10, 11, 12]` delivers `[12]`, which is no prefix of the queue (line 2). -/
@[evidence mutant CORE_013]
theorem CORE_013_mutant_lifo_killed :
    CORE_013_mutant_lifo (exec010_by (N := Nat) (T := Nat) exec010_lifoSel) ∧
      ¬ CORE_013 (exec010_by (N := Nat) (T := Nat) exec010_lifoSel) := by
  refine ⟨fun t δ e p _ hr he M M' h => ?_, fun h => ?_⟩
  · refine ⟨(M p).length - Consumes t (Counts M) p, ?_, ?_⟩
    · rw [exec010_by_inputs h p]; rfl
    · rw [exec010_by_kept h hr he]; rfl
  · obtain ⟨k, hk, -⟩ := h.2 (qexT .one) _ exec010_e 0 (by decide) _ _
      (exec010_by_fires exec010_lifoSel .one (by decide))
    have h1 : (exec010_delivered exec010_lifoSel qexM (qexT .one)).inputs 0 = [12] := by decide
    have h2 : qexM 0 = [10, 11, 12] := by decide
    rw [h1, OldestFirst, h2] at hk
    match k, hk with
    | 0, h => simp at h
    | k + 1, h => simp at h

/-! ### Mutant: a bag -/

/-- Mutant reading of CORE-013 that keeps the right tokens but not their order: a place that is
neither an input nor a reset place ends the firing holding its queue and the emitted tokens, in
some order, and an input place hands its action its first `k` tokens and, unless it is a reset
place, ends holding the rest of its queue and the emitted tokens, in some order. It is what
"stored in FIFO order" would say if it only fixed which tokens leave, not where new ones go. -/
def CORE_013_mutant_bag {N T : Type} [DecidableEq N] (Q : QFireRel N T) : Prop :=
  (∀ t δ e p, p ∉ inPlaces t → ¬ ResetArc t p →
    on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      List.Perm (M' p) (M p ++ EmittedTo e p))) ∧
  (∀ t δ e p, p ∈ inPlaces t →
    on (fun M M' => Q t M δ e M'), shall (fun M M' =>
      ∃ k, δ.inputs p = OldestFirst M p k ∧
        (¬ ResetArc t p → List.Perm (M' p) ((M p).drop k ++ EmittedTo e p))))

/-- The head-deposit executor keeps the right tokens, so the bag reading holds of it at every
type; CORE-013 does not (`CORE_013_forbids_headDeposit`). -/
@[evidence mutant CORE_013]
theorem CORE_013_mutant_bag_killed :
    CORE_013_mutant_bag (exec020_prependFire (N := Nat) (T := Nat)) ∧
      ¬ CORE_013 (exec020_prependFire (N := Nat) (T := Nat)) := by
  refine ⟨⟨fun t δ e p hi hr M M' h => ?_, fun t δ e p hp M M' h => ?_⟩,
    CORE_013_forbids_headDeposit⟩
  · obtain ⟨_, _, _, rfl⟩ := h
    show List.Perm (EmittedTo e p ++ qConsume M t p) (M p ++ EmittedTo e p)
    rw [exec020_qConsume_untouched M hi hr]
    exact List.perm_append_comm
  · obtain ⟨_, _, rfl, rfl⟩ := h
    refine ⟨Consumes t (Counts M) p, rfl, fun hr => ?_⟩
    have hr' : p ∉ t.core.resets := hr
    simp only [qConsume, hr', if_false, qPostInput]
    exact List.perm_append_comm

end Libpetri.Spec
