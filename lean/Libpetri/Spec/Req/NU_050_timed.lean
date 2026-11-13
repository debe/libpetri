import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Nu
import Libpetri.Spec.Req.TIME_012_nu
import Libpetri.Novel.TimedScg.Retrodict
import Libpetri.Spec.Text.NU_050

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# NU-050, the timed lines of Route B (`spec/12-nu-nets.md`)

The fourth block of NU-050, beside `NU_050_prefix`, `NU_050_soundB` and `NU_050_soundA` in
`NU_050.lean`: on a timed net, Route B gives a matched join a clock only while one name is
present in every correlated input, and the clock-restart rule of [TIME-012] reads the name layer.
The lines speak of every transition of the net: for a transition without a match, enabled
([NU-020]) is enabled on the counts, so the lines are the clock rules of [TIME-012] on Route B.

The block is a predicate over an abstract timed ν step relation `R : RBTRel N V Nm`, the timed
semantics the classes of the Route B graph stand for: a state holds a queue marking of stamped
tokens, the reading of the clock and a stamp per transition name (`none`: no clock); a step is a
delay or a firing that names the fired ν transition, its chosen name and its emission. The
reference `RefRouteBT` is the semantics of the name-gated successor `compute_successor_gated`
(`state_class_graph.rs`) with `name_enabled` as both gates (`name_state_class_graph.rs`): Merlin's
strong urgency (time may pass only while no clocked transition overruns its latest bound), a
transition holds a clock only while it is ν-enabled ([NU-020]), a clock survives a firing only
when its transition is ν-enabled before, in the intermediate marking and after, and every other
transition ν-enabled after the firing gets a fresh clock. The firing itself is the reference ν
firing `RefNuFire`. The latest-bound relaxation for a late executor ([TIME-013]) is the same
semantics on the relaxed net (`Timing.relaxLate`), so the lines, stated for every timed ν net,
hold with and without it.

The DBM zones of the graph, its name-symbol quotient and the [NU-052] prune are not in the
model: the shipped gated successor is gap R6 of `Novel/RouteB/Sound.lean`, and the model-level
witness of the old count-gated graph is `Novel.TimedScg.name_disabled_join_escapes`, cited here.

The net, state, label, relation, intermediate marking and in-net vocabulary is the executor-side
vocabulary of the ν-join clause of [TIME-012] (`TIME_012_nu.lean`): `RBTNet`, `RBTSt`, `RBTLbl`,
`RBTRel`, `rbtMid` and `RBTInNet` abbreviate `NuTimedNet`, `NuTSt`, `NuTLbl`, `NuTRel`, `NuMid` and
`NuInNet`, so the Route B relation and the executor relation have one type and differ only in
their witnesses. The Route B relation adds strong urgency, which the executor does not have (it
reaps instead, [TIME-013]).

Wrong models, at least one per line: the count-gated clock of the graph before the fix
(`countPol`, line 1) and a clock gated on the names alone (`sharedPol`, line 1); a restart judged
on the counts of the intermediate marking (`countMidPol`, line 2) or on its names alone
(`midSharedPol`, line 2); a restart on every take from a correlated input (`takePol`, line 3, the
literal old wording, clash nu-b#10); a join that is never given a fresh clock when it comes to
share a name (`noArmPol`, line 4); a fired join that keeps its own clock (`firedKeepPol`, line 5);
clocks that never age, restamped at every step (`agelessRel`, line 6); and a firing that ignores
the earliest bound (`untimedRel`, line 7).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Novel.TimedScg (Timing)

/-! ## Vocabulary -/

section Vocab

variable {N V Nm : Type}

/-- A timed ν net as Route B reads it: the executor-side timed ν net of [TIME-012]
(`NuTimedNet`), its transitions, each possibly matched, and the timing of each transition
([TIME-001]). A relaxed net ([TIME-013]) is a net whose timings went through `Timing.relaxLate`. -/
abbrev RBTNet (N V Nm : Type) := NuTimedNet N V Nm

/-- A state of Route B's timed semantics: the executor-side state `NuTSt`, the queue marking of
stamped tokens, the reading of the clock and the stamp per transition name (`none`: the
transition holds no clock). -/
abbrev RBTSt (N V : Type) := NuTSt N V

/-- A step of Route B's timed semantics: the executor-side label `NuTLbl`, time passing by `δ` or
`t` firing with chosen name `c` (`none` without a match) and emission `e`. -/
abbrev RBTLbl (N V Nm : Type) := NuTLbl N V Nm

/-- A timed ν step relation of Route B: `R X s l s'`, of the same type as the executor-side
relation `NuTRel`; the two differ only in their witnesses. -/
abbrev RBTRel (N V Nm : Type) := NuTRel N V Nm

/-- `u` holds a clock in `s`: its name has a stamp. -/
def RBTClock (s : RBTSt N V) (u : NuTrans N (KeyFn V Nm)) : Prop :=
  (s.stamp u.base.core.name).isSome = true

instance (s : RBTSt N V) (u : NuTrans N (KeyFn V Nm)) : Decidable (RBTClock s u) :=
  inferInstanceAs (Decidable (_ = true))

/-- `u` is the net's transition of its name (`NuInNet`). -/
abbrev RBTInNet (X : RBTNet N V Nm) (u : NuTrans N (KeyFn V Nm)) : Prop := NuInNet X u

/-- The net's transition named `n`, if any. -/
def rbtLookup (X : RBTNet N V Nm) (n : String) : Option (NuTrans N (KeyFn V Nm)) :=
  X.trans.find? (·.base.core.name == n)

/-- The elapsed time of `u`: the clock reading minus its stamp (0 without a stamp). -/
def rbtElapsed (s : RBTSt N V) (u : NuTrans N (KeyFn V Nm)) : Nat :=
  s.now - (s.stamp u.base.core.name).getD s.now

variable [DecidableEq N] [LinearOrder Nm]

/-- **A name is shared** by the correlated inputs of `u` in `M`: some name is present in every
correlated input at the count its arc requires (`eligible`, [NU-020]). Every transition without
a match shares one vacuously. -/
def NuShared (u : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) : Prop :=
  ∀ ms, u.mspec = some ms → ∃ n, eligible (matchIn ms u M) n = true

/-- **The intermediate marking of a ν firing** ([TIME-012] read by names), the executor-side
`NuMid`: a matched transition takes the first tokens of its chosen name from each correlated input
(`nuConsume`, which also drains the reset places); any other transition takes the queue heads
(`qConsume`). -/
abbrev rbtMid (t : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) (c : Option Nm) :
    QMarking N (Stamped V) :=
  NuMid t M c

/-- Enabled on the token counts, as a test. -/
def rbtCountB (u : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) : Bool :=
  enabledNA (qCount M) u.base.core

/-- A shared name, as a test: the candidates of [NU-022] (the eligible names) are not empty. -/
def rbtSharedB (u : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) : Bool :=
  match u.mspec with
  | none => true
  | some ms => !(cands (matchIn ms u M)).isEmpty

/-- ν enablement ([NU-020]), as a test. -/
def rbtEnB (u : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) : Bool :=
  rbtCountB u M && rbtSharedB u M

theorem rbtSharedB_iff (u : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) :
    rbtSharedB u M = true ↔ NuShared u M := by
  unfold rbtSharedB NuShared
  cases h : u.mspec with
  | none => simp
  | some ms =>
    simp only [Bool.not_eq_true', Option.some.injEq, forall_eq']
    constructor
    · intro hc
      cases hl : cands (matchIn ms u M) with
      | nil => rw [hl] at hc; simp at hc
      | cons n _ => exact ⟨n, mem_cands.1 (by rw [hl]; exact List.mem_cons_self ..)⟩
    · rintro ⟨n, hn⟩
      have hm := mem_cands.2 hn
      cases hl : cands (matchIn ms u M) with
      | nil => rw [hl] at hm; exact absurd hm List.not_mem_nil
      | cons _ _ => rfl

theorem rbtEnB_iff (u : NuTrans N (KeyFn V Nm)) (M : QMarking N (Stamped V)) :
    rbtEnB u M = true ↔ NuEnabled u M := by
  simp only [rbtEnB, Bool.and_eq_true, rbtSharedB_iff, rbtCountB, NuEnabled, NuShared, Enabled]

theorem rbtEnB_false_of_not_shared {u : NuTrans N (KeyFn V Nm)} {M : QMarking N (Stamped V)}
    (h : ¬ NuShared u M) : rbtEnB u M = false := by
  cases hb : rbtEnB u M with
  | false => rfl
  | true =>
    simp only [rbtEnB, Bool.and_eq_true] at hb
    exact absurd ((rbtSharedB_iff u M).1 hb.2) h

theorem rbtEnB_false_of_not_enabled {u : NuTrans N (KeyFn V Nm)} {M : QMarking N (Stamped V)}
    (h : ¬ NuEnabled u M) : rbtEnB u M = false := by
  cases hb : rbtEnB u M with
  | false => rfl
  | true => exact absurd ((rbtEnB_iff u M).1 hb) h

end Vocab

/-! ## The block -/

requirement NU_050_timed
  id "NU-050"
  title "Exact Verification of Matched Transitions: a join's clock on a timed net"
  kind T
  scope "every verifier that offers the Route B name-partition graph (MAY) on a timed net; the timed semantics its classes stand for"
  source verbatim "spec/12-nu-nets.md"
  covers NU_050.s7, NU_050.s8, NU_050.s9, NU_050.s10, NU_050.s11, NU_050.s12, NU_050.s13, NU_050.s6
  reading "For every timed ν net X (the relaxed net of TIME-013 included) and every transition u that is the net's transition of its name, matched or not:"
          "every step after which u is not ν-enabled leaves u without a stamp;"
          "a firing of t, named differently from u, from a state in which u holds a stamp and is not ν-enabled in the intermediate marking of t (with t's chosen name), after which u is ν-enabled, leaves u stamped with the clock reading after the firing;"
          "a firing of t, named differently from u, from a state in which u holds a stamp and is ν-enabled, after which u is ν-enabled, and in whose intermediate marking u is ν-enabled, leaves u's stamp as it was;"
          "a firing from a state in which u holds no stamp, after which u is ν-enabled, leaves u stamped with the clock reading after the firing;"
          "a firing of a transition named as u, after which u is ν-enabled, leaves u stamped with the clock reading after the firing;"
          "a delay by δ keeps the marking, advances the clock reading by δ and, when u is ν-enabled, keeps u's stamp;"
          "a firing of u starts from a state in which u holds a stamp and its elapsed time is at least u's earliest bound, and keeps the clock reading."
  assumes "The model is the timed semantics the classes of the Route B graph stand for (RBTRel): a state holds the queue marking of stamped tokens, the clock reading and a stamp per transition name, none for no clock; a step is a delay or an atomic firing naming the fired ν transition, its chosen name and its emission. A class of the graph stands for the states with its marking, its name layer and clock values in its firing domain; the zones (DBM), the name-symbol quotient and the canonical key are not modelled (gap R6 of Novel/RouteB/Sound.lean: the gated successor compute_successor_gated is the shipped code, its Lean model is open). Names are the values the key projections read (NU-001), not abstract symbols; that the quotient keeps the gate is Novel.RouteB.nameEnabled_comp. The witness RefRouteBT is that semantics: strong urgency on delays (a delay may not take a clocked, ν-enabled transition past its latest bound), clocks only on ν-enabled transitions, a clock kept across a firing only when its transition is ν-enabled before, in the intermediate marking and after and is not named as the fired one, and a fresh clock for every other transition ν-enabled after the firing, which is compute_successor_gated with is_enabled and name_enabled as the gates (state_class_graph.rs, name_state_class_graph.rs). A firing of the model is a reference ν firing RefNuFire (the selected name, FIFO takes elsewhere); the graph's free choice of a shared name and of a consumer's resident name (clash nu-b#3) are VER-012's, and every line is stated for the label's own chosen name and intermediate marking. Time is in whole milliseconds, as the executor's clock (TSt.now)."
          "'Enabled with an eligible name' in the quoted sentences is NuEnabled ([NU-020], [NU-022]): enabled on the counts and some name eligible, which for a transition without a match is enabled on the counts. 'No name present in every correlated input at the count its arc requires' is ¬NuShared, one way of not being ν-enabled; a matched join whose names are shared but whose counts fail (an empty non-correlated input, a marked inhibitor) is not enabled with an eligible name either, so it holds no clock (line 1) and a clock judged in such an intermediate marking restarts (line 2). 'Another transition' is a transition with a different name, as compute_successor_gated tells the fired transition apart. The intermediate marking is rbtMid: the correlated takes of the chosen name and the drained reset places for a matched transition, the queue consume otherwise, as TIME_012_nu's NuMid on the executor side. Line 1 is the first quoted sentence. Line 2 is the second: its fresh clock is line 2 and its taking away, when the firing leaves j not enabled, is line 1. Line 3 is the third, line 4 the fourth. Line 5 is the fifth, again with the taking away carried by line 1. Line 6 is the sixth, line 7 the seventh. A clock that held a stamp before a firing and is enabled after it is fixed by lines 2, 3 and 5; one that held none by line 4; one not enabled after by line 1; so every firing fixes every stamp."
          "The lines speak of every transition of the net, matched or not. For a transition without a match they are the clock rules of TIME-012 read on Route B's relation; they are stated here because the TIME_012 block constrains the executor relation, not RBTRel, and the graph-side persistence rule of VER-010 (Novel/TimedScg/Run.lean) speaks of the un-named graph."
          "The body's 'a firing after which no name is present in every correlated input restarts the join's clock' is read on the intermediate marking (line 2), as compute_successor_gated judges it (the intermediate name layer as the gate between) and the executor does (TIME_012_nu, flag_clock_restarts on the live marking): a deposit only adds tokens, so a firing after which no name is shared left none shared in its intermediate marking either, and line 2 then restarts the clock (or, with line 1, leaves none); line 2 also restarts a clock when the firing takes the shared name out and puts it back. The lines speak of steps; the initial class is not gated in the shipped graph (initial_state_class), which is harmless because Route B starts with every coloured place empty (refusal step 7 of NU-055), so no join is enabled on its counts there."
          "The eighth quoted sentence is the quantification over every timed ν net: the relaxed net of TIME-013 (Timing.relaxLate, the graph built by reaping::relax_late when the caller does not assume an on-time executor) is one, so the lines hold of it too; NU_050_timed_ac3 runs one net both ways."
          "The body sentences 'On a timed net Route B gives a matched join a clock only while one name-symbol is present in every correlated input, because the executor enables the join only then ([NU-020]).' and 'The clock-restart rule of [TIME-012] reads the name layer too: a firing after which no name is present in every correlated input restarts the join's clock, even when the inputs still hold tokens, and a join whose inputs come to share a name starts a fresh clock then.' are restated by the EARS sentences (lines 1 to 5). The executor half ('because the executor enables the join only then') is NU-020's: every firing of RefRouteBT is a RefNuFire firing from a marking at which its transition is ν-enabled (nu050t_fire_executor), and the executor's own clock rule is the TIME_012_nu block. The sentence 'A join whose inputs hold tokens but share no name has no clock, so its latest bound constrains no other firing.' says what the semantics offers, so it is a coverage predicate (RBTCovers: time may pass while every clocked, ν-enabled transition stays within its latest bound, and every clocked, ν-enabled transition past its earliest bound fires), not a line; RefRouteBT meets it (NU_050_timed_covers_reference) and the empty relation, which meets every line, does not (nu050t_coverage_excludes_empty). Strong urgency itself (a delay never takes a clocked transition past its latest bound) is not a line here: it is the timed semantics of VER-010, which Route B carries unchanged."
          "AC3 is NU_050_timed_ac3: on the AC3 net, on time and with the relaxation, the join never holds a clock and the watchdog marks BAD at 10 ms, so a sound Route B reports unreachable(BAD) violated; under the count-gated clock of the graph before the fix the join holds a clock with latest bound 5 and time cannot pass to 10 ms (nu050t_countClock_ac3), the graph-level witness of which is Novel.TimedScg.name_disabled_join_escapes (cited as nu050t_old_graph_escapes). For any relation meeting the lines and RBTCovers the same run exists: the join holds no clock (line 1), the watchdog's clock starts at 0 ms and is kept (lines 3, 4 and 6), RBTCovers offers the 10 ms delay and the watchdog's firing. AC4 is NU_050_timed_ac4: the join is count-enabled from 1 ms, first shares a name at 5 ms, gets its clock then, cannot fire at 14 ms and can at 15 ms; under the count-gated clock it fires at 11 ms (nu050t_countClock_ac4). That the join cannot fire before 15 ms holds of every relation meeting the lines, not only of the reference: nu050t_ac4_of_statement (a 9 ms delay keeps the stamp 5 by line 6, and line 7 refuses the firing at 14 ms). Both ACs are run against the shipped Route B by fixture tests (kind Q), since its timed successor is gap R6."
          "Modelled injection, environment places and the deadline reaps of the executor ([TIME-013]) are not steps of the relation: Route B reads environment places as VER-006 AC8 says, and accounts for a late executor by the relaxed net instead of reaps."
  signoff "2026-11-13 8521730a656ca00b ai"
  statement : ∀ {N V Nm : Type} [DecidableEq N] [LinearOrder Nm], RBTRel N V Nm → Prop :=
    fun R => ∀ (X : RBTNet _ _ _) (u : NuTrans _ (KeyFn _ _)), RBTInNet X u →
      (∀ l, on (fun s s' => R X s l s'), shall (fun _ s' => ¬ NuEnabled u s'.M →
          s'.stamp u.base.core.name = none)) ∧
      (∀ t c e, u.base.core.name ≠ t.base.core.name →
          on (fun s s' => R X s (.fire t c e) s'), shall (fun s s' => RBTClock s u →
            ¬ NuEnabled u (rbtMid t s.M c) → NuEnabled u s'.M →
              s'.stamp u.base.core.name = some s'.now)) ∧
      (∀ t c e, u.base.core.name ≠ t.base.core.name →
          on (fun s s' => R X s (.fire t c e) s'), shall (fun s s' => RBTClock s u →
            NuEnabled u s.M → NuEnabled u (rbtMid t s.M c) → NuEnabled u s'.M →
              s'.stamp u.base.core.name = s.stamp u.base.core.name)) ∧
      (∀ t c e, on (fun s s' => R X s (.fire t c e) s'), shall (fun s s' => ¬ RBTClock s u →
          NuEnabled u s'.M → s'.stamp u.base.core.name = some s'.now)) ∧
      (∀ t c e, u.base.core.name = t.base.core.name →
          on (fun s s' => R X s (.fire t c e) s'), shall (fun _ s' => NuEnabled u s'.M →
            s'.stamp u.base.core.name = some s'.now)) ∧
      (∀ δ, on (fun s s' => R X s (.delay δ) s'), shall (fun s s' => s'.M = s.M ∧
          s'.now = s.now + δ ∧ (NuEnabled u s.M →
            s'.stamp u.base.core.name = s.stamp u.base.core.name))) ∧
      (∀ c e, on (fun s s' => R X s (.fire u c e) s'), shall (fun s s' => RBTClock s u ∧
          (X.timing u.base).earliest ≤ rbtElapsed s u ∧ s'.now = s.now))

/- The pinned readable form of NU_050_timed: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_050_timed : {N V Nm : Type} → [DecidableEq N] → [LinearOrder Nm] → RBTRel N V Nm → Prop :=
fun {N V Nm} [DecidableEq N] [LinearOrder Nm] R =>
  ∀ (X : RBTNet N V Nm) (u : NuTrans N (KeyFn V Nm)),
    RBTInNet X u →
      (∀ (l : NuTLbl N V Nm),
          on fun s s' => R X s l s', shall fun x s' => ¬NuEnabled u s'.M → s'.stamp u.base.core.name = none) ∧
        (∀ (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (e : List (N × Stamped V)),
            u.base.core.name ≠ t.base.core.name →
              on fun s s' => R X s (NuTLbl.fire t c e) s', shall fun s s' =>
                RBTClock s u →
                  ¬NuEnabled u (rbtMid t s.M c) → NuEnabled u s'.M → s'.stamp u.base.core.name = some s'.now) ∧
          (∀ (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (e : List (N × Stamped V)),
              u.base.core.name ≠ t.base.core.name →
                on fun s s' => R X s (NuTLbl.fire t c e) s', shall fun s s' =>
                  RBTClock s u →
                    NuEnabled u s.M →
                      NuEnabled u (rbtMid t s.M c) →
                        NuEnabled u s'.M → s'.stamp u.base.core.name = s.stamp u.base.core.name) ∧
            (∀ (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (e : List (N × Stamped V)),
                on fun s s' => R X s (NuTLbl.fire t c e) s', shall fun s s' =>
                  ¬RBTClock s u → NuEnabled u s'.M → s'.stamp u.base.core.name = some s'.now) ∧
              (∀ (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (e : List (N × Stamped V)),
                  u.base.core.name = t.base.core.name →
                    on fun s s' => R X s (NuTLbl.fire t c e) s', shall fun x s' =>
                      NuEnabled u s'.M → s'.stamp u.base.core.name = some s'.now) ∧
                (∀ (δ : ℕ),
                    on fun s s' => R X s (NuTLbl.delay δ) s', shall fun s s' =>
                      s'.M = s.M ∧
                        s'.now = s.now + δ ∧ (NuEnabled u s.M → s'.stamp u.base.core.name = s.stamp u.base.core.name)) ∧
                  ∀ (c : Option Nm) (e : List (N × Stamped V)),
                    on fun s s' => R X s (NuTLbl.fire u c e) s', shall fun s s' =>
                      RBTClock s u ∧ (X.timing u.base).earliest ≤ rbtElapsed s u ∧ s'.now = s.now
-/
#guard_msgs in #print NU_050_timed

/-! ## The semantics, with its timing decisions as a policy -/

section Ref

variable {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]

/-- The timing decisions of the Route B timed semantics. `clockEn u M`: `u` may hold a clock at
`M`. `midEn u M`: the test a kept clock passes in the intermediate marking. `keepX t u`: a further
condition for `u` to keep its clock when `t` fires; the spec's is that `u` is not named as `t`.
`rearm s u`: `u`, not keeping its clock and allowed one after the firing, gets a fresh one. -/
structure RBTPol (N V Nm : Type) where
  /-- `u` may hold a clock at the marking. -/
  clockEn : NuTrans N (KeyFn V Nm) → QMarking N (Stamped V) → Bool
  /-- The test in the intermediate marking for keeping a clock. -/
  midEn   : NuTrans N (KeyFn V Nm) → QMarking N (Stamped V) → Bool
  /-- A further keep condition: the fired transition, the judged one. -/
  keepX   : NuTrans N (KeyFn V Nm) → NuTrans N (KeyFn V Nm) → Bool
  /-- A transition that does not keep its clock gets a fresh one. -/
  rearm   : RBTSt N V → NuTrans N (KeyFn V Nm) → Bool

/-- `u` keeps its stamp when `t` fires with chosen name `c` from `s` to the marking `M'`. -/
def rbtKeep (P : RBTPol N V Nm) (s : RBTSt N V) (t : NuTrans N (KeyFn V Nm)) (c : Option Nm)
    (M' : QMarking N (Stamped V)) (u : NuTrans N (KeyFn V Nm)) : Bool :=
  (s.stamp u.base.core.name).isSome && P.clockEn u s.M && P.midEn u (rbtMid t s.M c) &&
    P.clockEn u M' && P.keepX t u

/-- The stamps after a firing: a kept stamp stays; otherwise a transition allowed a clock after
the firing gets the current reading when `rearm` says so; otherwise none. -/
def rbtRestamp (P : RBTPol N V Nm) (X : RBTNet N V Nm) (s : RBTSt N V)
    (t : NuTrans N (KeyFn V Nm)) (c : Option Nm) (M' : QMarking N (Stamped V)) :
    String → Option Nat := fun n =>
  match rbtLookup X n with
  | some u =>
    if rbtKeep P s t c M' u then s.stamp n
    else if P.clockEn u M' && P.rearm s u then some s.now else none
  | none => none

/-- The stamps after a delay: a transition not allowed a clock at the marking holds none. -/
def rbtClean (P : RBTPol N V Nm) (X : RBTNet N V Nm) (s : RBTSt N V) : String → Option Nat :=
  fun n => match rbtLookup X n with
    | some u => if P.clockEn u s.M then s.stamp n else none
    | none => none

/-- The initial state from marking `M` at reading `now`: every transition allowed a clock at `M`
is stamped `now`. -/
def rbtInit (P : RBTPol N V Nm) (X : RBTNet N V Nm) (M : QMarking N (Stamped V)) (now : Nat) :
    RBTSt N V :=
  ⟨M, now, fun n => match rbtLookup X n with
    | some u => if P.clockEn u M then some now else none
    | none => none⟩

/-- `u` is clocked: allowed a clock at the marking, and holding one. -/
def rbtArmed (P : RBTPol N V Nm) (s : RBTSt N V) (u : NuTrans N (KeyFn V Nm)) : Bool :=
  P.clockEn u s.M && (s.stamp u.base.core.name).isSome

/-- **The Route B timed step under policy `P`.** Time passes by `δ` only while no clocked
transition of the net overruns its latest bound (strong urgency); a clocked transition of the net
past its earliest bound fires as the reference ν firing says, and the stamps are recomputed. -/
inductive RBTStepW (P : RBTPol N V Nm) :
    RBTNet N V Nm → RBTSt N V → RBTLbl N V Nm → RBTSt N V → Prop
  /-- Time passes; the marking stays; a transition not allowed a clock loses its stamp. -/
  | delay (X : RBTNet N V Nm) (s : RBTSt N V) (δ : Nat)
      (hurg : ∀ u ∈ X.trans, rbtArmed P s u = true →
        rbtElapsed s u + δ ≤ (X.timing u.base).latest) :
      RBTStepW P X s (.delay δ) { M := s.M, now := s.now + δ, stamp := rbtClean P X s }
  /-- A clocked transition of the net past its earliest bound fires. -/
  | fire (X : RBTNet N V Nm) (s : RBTSt N V) (t : NuTrans N (KeyFn V Nm)) (c : Option Nm)
      (δ : QDelivered N (Stamped V)) (e : List (N × Stamped V)) (M' : QMarking N (Stamped V))
      (ht : t ∈ X.trans) (hf : RefNuFire t s.M c δ e M') (ha : rbtArmed P s t = true)
      (hg : (X.timing t.base).earliest ≤ rbtElapsed s t) :
      RBTStepW P X s (.fire t c e) { M := M', now := s.now, stamp := rbtRestamp P X s t c M' }

/-- The spec's policy: a clock only while ν-enabled, kept only while ν-enabled in the
intermediate marking and only by a transition not named as the fired one, a fresh clock for
every transition ν-enabled after a firing that did not keep one. -/
def refRBTPol : RBTPol N V Nm :=
  ⟨rbtEnB, rbtEnB, fun t u => u.base.core.name != t.base.core.name, fun _ _ => true⟩

/-- **Route B's timed semantics** (witness model): the step under the spec's policy. -/
def RefRouteBT : RBTRel N V Nm := RBTStepW refRBTPol

omit [DecidableEq N] [LinearOrder Nm] in
theorem rbtLookup_of_inNet {X : RBTNet N V Nm} {u : NuTrans N (KeyFn V Nm)}
    (hu : RBTInNet X u) : rbtLookup X u.base.core.name = some u := hu

/-- The stamp a net's transition holds after a firing. -/
theorem rbtRestamp_inNet {P : RBTPol N V Nm} {X : RBTNet N V Nm} {u : NuTrans N (KeyFn V Nm)}
    (hu : RBTInNet X u) (s : RBTSt N V) (t : NuTrans N (KeyFn V Nm)) (c : Option Nm)
    (M' : QMarking N (Stamped V)) :
    rbtRestamp P X s t c M' u.base.core.name =
      if rbtKeep P s t c M' u then s.stamp u.base.core.name
      else if P.clockEn u M' && P.rearm s u then some s.now else none := by
  unfold rbtRestamp
  rw [rbtLookup_of_inNet hu]

omit [DecidableEq N] [LinearOrder Nm] in
/-- The stamp a net's transition holds after a delay. -/
theorem rbtClean_inNet {P : RBTPol N V Nm} {X : RBTNet N V Nm} {u : NuTrans N (KeyFn V Nm)}
    (hu : RBTInNet X u) (s : RBTSt N V) :
    rbtClean P X s u.base.core.name = if P.clockEn u s.M then s.stamp u.base.core.name else none := by
  unfold rbtClean
  rw [rbtLookup_of_inNet hu]

/-- A firing step, inverted. -/
theorem rbtStepW_fire_inv {P : RBTPol N V Nm} {X : RBTNet N V Nm} {s s' : RBTSt N V}
    {t : NuTrans N (KeyFn V Nm)} {c : Option Nm} {e : List (N × Stamped V)}
    (h : RBTStepW P X s (.fire t c e) s') :
    t ∈ X.trans ∧ (∃ δ, RefNuFire t s.M c δ e s'.M) ∧ rbtArmed P s t = true ∧
      (X.timing t.base).earliest ≤ rbtElapsed s t ∧ s'.now = s.now ∧
      s'.stamp = rbtRestamp P X s t c s'.M := by
  cases h
  exact ⟨by assumption, ⟨_, by assumption⟩, by assumption, by assumption, rfl, rfl⟩

/-- A delay step, inverted. -/
theorem rbtStepW_delay_inv {P : RBTPol N V Nm} {X : RBTNet N V Nm} {s s' : RBTSt N V} {δ : Nat}
    (h : RBTStepW P X s (.delay δ) s') :
    s'.M = s.M ∧ s'.now = s.now + δ ∧ s'.stamp = rbtClean P X s := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

end Ref

#spec_witness RefRouteBT

/-- Route B's timed semantics keeps the seven lines. Take a join whose inputs A and B both hold
name 1. A step after which the join is not enabled leaves it without a clock, because a clock is
only kept or given to an enabled transition. When another transition fires and the join is not
enabled in the intermediate marking, it cannot keep its clock, so it gets the current reading if
it is enabled after the firing. A join that is enabled before, in the intermediate marking and
after keeps its stamp. A join without a clock that is enabled after a firing gets the current
reading, and so does the join itself after it fires. Time passing keeps the marking and the
stamps and moves the clock on, and the join fires only once its clock has run its earliest
bound. -/
@[evidence holds NU_050_timed]
theorem NU_050_timed_reference {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    NU_050_timed (RefRouteBT (N := N) (V := V) (Nm := Nm)) := by
  intro X u hu
  have post : ∀ (s s' : RBTSt N V) (t : NuTrans N (KeyFn V Nm)) (c : Option Nm),
      s'.now = s.now → s'.stamp = rbtRestamp refRBTPol X s t c s'.M →
      rbtKeep refRBTPol s t c s'.M u = false → NuEnabled u s'.M →
      s'.stamp u.base.core.name = some s'.now := by
    intro s s' t c hnow hst hk hen
    rw [hst, rbtRestamp_inNet hu, hk, hnow]
    simp [refRBTPol, (rbtEnB_iff u s'.M).2 hen]
  refine ⟨fun l s s' h hns => ?_, fun t c e hne s s' h hc hmid haft => ?_,
    fun t c e hne s s' h hc hen hmid haft => ?_, fun t c e s s' h hc haft => ?_,
    fun t c e heq s s' h haft => ?_, fun δ s s' h => ?_, fun c e s s' h => ?_⟩
  · have hf := rbtEnB_false_of_not_enabled hns
    cases h with
    | delay δ _ =>
      show rbtClean refRBTPol X s u.base.core.name = none
      rw [rbtClean_inNet hu]
      simp [refRBTPol, hf]
    | fire t c δ e M' _ _ _ _ =>
      show rbtRestamp refRBTPol X s t c M' u.base.core.name = none
      rw [rbtRestamp_inNet hu]
      simp [rbtKeep, refRBTPol, hf]
  · obtain ⟨-, -, -, -, hnow, hst⟩ := rbtStepW_fire_inv h
    have hm := rbtEnB_false_of_not_enabled hmid
    exact post s s' t c hnow hst (by simp [rbtKeep, refRBTPol, hm]) haft
  · obtain ⟨-, -, -, -, -, hst⟩ := rbtStepW_fire_inv h
    have hk : rbtKeep refRBTPol s t c s'.M u = true := by
      simp only [RBTClock] at hc
      simp [rbtKeep, refRBTPol, hc, (rbtEnB_iff u s.M).2 hen, (rbtEnB_iff _ _).2 hmid,
        (rbtEnB_iff u s'.M).2 haft, hne]
    rw [hst, rbtRestamp_inNet hu, if_pos hk]
  · obtain ⟨-, -, -, -, hnow, hst⟩ := rbtStepW_fire_inv h
    simp only [RBTClock, Bool.not_eq_true, Option.isSome_eq_false_iff] at hc
    exact post s s' t c hnow hst (by simp [rbtKeep, hc]) haft
  · obtain ⟨-, -, -, -, hnow, hst⟩ := rbtStepW_fire_inv h
    exact post s s' t c hnow hst (by simp [rbtKeep, refRBTPol, heq]) haft
  · obtain ⟨hM, hnow, hst⟩ := rbtStepW_delay_inv h
    refine ⟨hM, hnow, fun hen => ?_⟩
    rw [hst, rbtClean_inNet hu]
    simp [refRBTPol, (rbtEnB_iff u s.M).2 hen]
  · obtain ⟨-, -, ha, hg, hnow, -⟩ := rbtStepW_fire_inv h
    simp only [rbtArmed, refRBTPol, Bool.and_eq_true] at ha
    exact ⟨ha.2, hg, hnow⟩

/-! ## What the semantics offers -/

section Covers

variable {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]

/-- **What Route B's timed semantics offers** (the coverage predicate, not a line): time may
pass by `δ` whenever every clocked, ν-enabled transition of the net stays within its latest bound,
so the latest bound of a join that holds no clock constrains nothing; and every clocked,
ν-enabled transition of the net past its earliest bound fires with every emission the reference
ν firing offers. -/
def RBTCovers (R : RBTRel N V Nm) : Prop :=
  (∀ X s δ, (∀ u ∈ X.trans, NuEnabled u s.M → RBTClock s u →
      rbtElapsed s u + δ ≤ (X.timing u.base).latest) →
    ∃ s', R X s (.delay δ) s' ∧ s'.M = s.M ∧ s'.now = s.now + δ) ∧
  (∀ X s t c δ e M', t ∈ X.trans → RefNuFire t s.M c δ e M' → RBTClock s t →
    (X.timing t.base).earliest ≤ rbtElapsed s t →
    ∃ s', R X s (.fire t c e) s' ∧ s'.M = M' ∧ s'.now = s.now)

end Covers

/-- Route B's timed semantics offers what the coverage predicate asks. A delay is refused only
by a transition that holds a clock and is ν-enabled, so a join whose inputs share no name never
holds time back; and a clocked transition past its earliest bound fires, because a reference ν
firing is ν-enabled at its marking. -/
@[evidence cites "NU-050" "A join whose inputs hold tokens but share no name has no clock, so its latest bound constrains no other firing."]
theorem NU_050_timed_covers_reference {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    RBTCovers (RefRouteBT (N := N) (V := V) (Nm := Nm)) := by
  refine ⟨fun X s δ h => ⟨_, RBTStepW.delay X s δ (fun u hu ha => ?_), rfl, rfl⟩,
    fun X s t c δ e M' ht hf hc hg => ⟨_, RBTStepW.fire X s t c δ e M' ht hf ?_ hg, rfl, rfl⟩⟩
  · simp only [rbtArmed, refRBTPol, Bool.and_eq_true] at ha
    exact h u hu ((rbtEnB_iff u s.M).1 ha.1) ha.2
  · simp only [rbtArmed, refRBTPol, Bool.and_eq_true]
    exact ⟨(rbtEnB_iff t s.M).2 (refNuFire_nuEnabled hf), hc⟩

/-- The relation with no step keeps every line (each line speaks of steps only) but offers
nothing: on the net with no transition, time may not even pass. So the coverage predicate is
what rules it out, as `NuCovers` does for the ν firing blocks. -/
theorem nu050t_coverage_excludes_empty :
    NU_050_timed (fun _ _ _ _ => False : RBTRel Nat Nat Nat) ∧
      ¬ RBTCovers (fun _ _ _ _ => False : RBTRel Nat Nat Nat) := by
  refine ⟨fun _ _ _ => ⟨fun _ _ _ h => h.elim, fun _ _ _ _ _ _ h => h.elim,
    fun _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ h => h.elim,
    fun _ _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩, fun h => ?_⟩
  obtain ⟨_, hs, -⟩ := h.1 ⟨[], fun _ => .immediate⟩ ⟨fun _ => [], 0, fun _ => none⟩ 0
    (fun _ hu => absurd hu List.not_mem_nil)
  exact hs

/-- Every firing of Route B's timed semantics is a firing of the reference ν executor, from a
marking at which the fired transition is ν-enabled: a join fires only on a name present in
every correlated input, which is why the semantics gives it a clock only then. -/
@[evidence cites "NU-050" "On a timed net Route B gives a matched join a clock only while one name-symbol is present in every correlated input, because the executor enables the join only then ([NU-020])."]
theorem nu050t_fire_executor {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]
    {X : RBTNet N V Nm} {s s' : RBTSt N V} {t : NuTrans N (KeyFn V Nm)} {c : Option Nm}
    {e : List (N × Stamped V)} (h : RefRouteBT X s (.fire t c e) s') :
    (∃ δ, RefNuFire t s.M c δ e s'.M) ∧ NuEnabled t s.M := by
  obtain ⟨-, ⟨δ, hf⟩, -⟩ := rbtStepW_fire_inv h
  exact ⟨⟨δ, hf⟩, refNuFire_nuEnabled hf⟩

/-- The graph-level witness of the old behaviour: in the count-based state-class graph, a join
that is count-enabled but never name-enabled keeps a clock and its deadline, and that clock
excludes a run the executor makes (it marks `b` at 10 ms; no class of the graph does). -/
@[evidence cites "NU-050" "A join whose inputs hold tokens but share no name has no clock, so its latest bound constrains no other firing."]
theorem nu050t_old_graph_escapes :
    (∃ s, Relation.ReflTransGen
        (Novel.TimedScg.BlockedStep Novel.TimedScg.netRP fun i => i == 0)
        (Novel.TimedScg.s0 Novel.TimedScg.m0RP) s ∧ s.m 2 = 1) ∧
      ∃ C0, Novel.TimedScg.initCls Novel.TimedScg.netRP (fun _ => none) 0
          Novel.TimedScg.m0RP = some C0 ∧
        ∀ C, Relation.ReflTransGen (Novel.TimedScg.Edge Novel.TimedScg.netRP (fun _ => none) 0)
          C0 C → C.m 2 = 0 :=
  Novel.TimedScg.name_disabled_join_escapes le_rfl (by norm_num)

/-! ## Examples: places, names and timings in `Nat` -/

section Examples

/-- A token with value (and name) `v`, created at `s`. -/
def nu050t_tok (v : Nat) (s : Int) : Stamped Nat := ⟨v, s⟩

/-- The key used throughout: a token's name is its value. -/
def nu050t_key : KeyFn Nat Nat := some

/-- A transition without a match: one token from `i`, one token to `o`. -/
def nu050t_plain (n : String) (i o : Nat) : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := n, inputs := [⟨i, .one⟩], inhibitors := [], reads := [],
                        resets := [] }, out := some (.place o) } }

/-- A join of `a` and `b`, one token each, correlated on both by `nu050t_key`, with output `o`
(none: no output spec). -/
def nu050t_join (a b : Nat) (o : Option Nat) : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "join", inputs := [⟨a, .one⟩, ⟨b, .one⟩], inhibitors := [],
                        reads := [], resets := [] }, out := o.map Out.place }
    mspec := some { keys := [(a, nu050t_key), (b, nu050t_key)] } }

/-- A firing of a transition without a match is a reference ν firing with no chosen name. -/
theorem nu050t_plainFire {t : NuTrans Nat (KeyFn Nat Nat)} (h : t.mspec = none)
    {M : QMarking Nat (Stamped Nat)} {e : List (Nat × Stamped Nat)}
    (hq : RefQFire t.base M (qDelivered M t.base) e (qFire M t.base e)) :
    RefNuFire t M none (qDelivered M t.base) e (qFire M t.base e) := by
  unfold RefNuFire; rw [h]; exact ⟨rfl, hq⟩

/-- The count-gated policy: the graph before the fix, whose clocks and keep test read the counts
only (`compute_successor` without gates). -/
def nu050t_countPol : RBTPol Nat Nat Nat :=
  { refRBTPol with clockEn := rbtCountB, midEn := rbtCountB }

/-- A restart judged on the counts of the intermediate marking. -/
def nu050t_countMidPol : RBTPol Nat Nat Nat := { refRBTPol with midEn := rbtCountB }

/-- A restart on every take from a correlated input: the join keeps its clock only when the
fired transition has no input arc on a place the join correlates (the literal reading "a firing
that takes the bound name out of a correlated input restarts the join's clock"). -/
def nu050t_takePol : RBTPol Nat Nat Nat :=
  { refRBTPol with keepX := fun t u => (u.base.core.name != t.base.core.name) &&
      t.base.core.inputs.all fun a => !((u.mspec.map MatchSpec.keyPlaces).getD []).contains a.place }

/-- No fresh clock for a transition that held none: only a clock that was taken away restarts. -/
def nu050t_noArmPol : RBTPol Nat Nat Nat :=
  { refRBTPol with rearm := fun s u => (s.stamp u.base.core.name).isSome }

/-- A clock gated on the names alone: a matched join holds a clock while its correlated inputs
share a name, whatever its counts (`name_enabled` without `is_enabled`). -/
def nu050t_sharedPol : RBTPol Nat Nat Nat := { refRBTPol with clockEn := rbtSharedB }

/-- A kept clock judged on the names alone in the intermediate marking: the count test there is
dropped (`enabled_between` without `is_enabled(t, &intermediate)`). -/
def nu050t_midSharedPol : RBTPol Nat Nat Nat := { refRBTPol with midEn := rbtSharedB }

/-- A fired transition that keeps its own clock: the keep test does not exclude the fired one. -/
def nu050t_firedKeepPol : RBTPol Nat Nat Nat := { refRBTPol with keepX := fun _ _ => true }

/-- Clocks that never age: every step of Route B's timed semantics, followed by a restamp of
every clock with the current reading. -/
def nu050t_agelessRel : RBTRel Nat Nat Nat := fun X s l s' =>
  ∃ s'', RefRouteBT X s l s'' ∧ s' = { s'' with stamp := fun n => (s''.stamp n).map fun _ => s''.now }

/-- Firing without the earliest bound: Route B's timed semantics on the net with every timing
made `immediate`, so a clocked, enabled transition fires at once. -/
def nu050t_untimedRel : RBTRel Nat Nat Nat := fun X s l s' =>
  RefRouteBT { X with timing := fun _ => .immediate } s l s'

/-! ### AC3: a join that never shares a name does not hold the watchdog back -/

/-- `forkA : sA (0) → A (2)`. -/
def nu050t_forkA : NuTrans Nat (KeyFn Nat Nat) := nu050t_plain "forkA" 0 2
/-- `forkB : sB (1) → B (3)`. -/
def nu050t_forkB : NuTrans Nat (KeyFn Nat Nat) := nu050t_plain "forkB" 1 3
/-- `join : A (2) + B (3) → merged (4)`, correlated on both inputs. -/
def nu050t_join3 : NuTrans Nat (KeyFn Nat Nat) := nu050t_join 2 3 (some 4)
/-- `watchdog : W (5) → BAD (6)`. -/
def nu050t_watch : NuTrans Nat (KeyFn Nat Nat) := nu050t_plain "watchdog" 5 6

/-- The AC3 net with the join's timing `tj`: the forks `immediate`, the watchdog `delayed(10)`. -/
def nu050t_X3 (tj : Timing) : RBTNet Nat Nat Nat :=
  { trans := [nu050t_forkA, nu050t_forkB, nu050t_join3, nu050t_watch],
    timing := fun t => if t.core.name = "join" then tj
      else if t.core.name = "watchdog" then .delayed 10 else .immediate }

/-- The join's timing on time, `window(0, 5)`. -/
def nu050t_onTime : Timing := .window 0 5
/-- The join's timing on the relaxed net of [TIME-013]. -/
def nu050t_late : Timing := Timing.relaxLate true (.window 0 5)

/-- The initial marking: one token on `sA`, `sB` and `W`. -/
def nu050t_M0 : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 ∨ p = 1 ∨ p = 5 then [nu050t_tok 0 0] else []

/-- forkA's emission: name `1` into A. -/
def nu050t_eA : List (Nat × Stamped Nat) := [(2, nu050t_tok 1 0)]
/-- forkB's emission: name `2` into B. -/
def nu050t_eB : List (Nat × Stamped Nat) := [(3, nu050t_tok 2 0)]
/-- The watchdog's emission: a token on BAD. -/
def nu050t_eW : List (Nat × Stamped Nat) := [(6, nu050t_tok 0 10)]

/-- The run's states under policy `P`: start, after forkA, after forkB, after 10 ms. -/
def nu050t_r0 (P : RBTPol Nat Nat Nat) (tj : Timing) : RBTSt Nat Nat :=
  rbtInit P (nu050t_X3 tj) nu050t_M0 0
/-- After forkA. -/
def nu050t_r1 (P : RBTPol Nat Nat Nat) (tj : Timing) : RBTSt Nat Nat :=
  ⟨qFire (nu050t_r0 P tj).M nu050t_forkA.base nu050t_eA, 0,
    rbtRestamp P (nu050t_X3 tj) (nu050t_r0 P tj) nu050t_forkA none
      (qFire (nu050t_r0 P tj).M nu050t_forkA.base nu050t_eA)⟩
/-- After forkB. -/
def nu050t_r2 (P : RBTPol Nat Nat Nat) (tj : Timing) : RBTSt Nat Nat :=
  ⟨qFire (nu050t_r1 P tj).M nu050t_forkB.base nu050t_eB, 0,
    rbtRestamp P (nu050t_X3 tj) (nu050t_r1 P tj) nu050t_forkB none
      (qFire (nu050t_r1 P tj).M nu050t_forkB.base nu050t_eB)⟩
/-- After 10 ms. -/
def nu050t_r3 (P : RBTPol Nat Nat Nat) (tj : Timing) : RBTSt Nat Nat :=
  ⟨(nu050t_r2 P tj).M, 10, rbtClean P (nu050t_X3 tj) (nu050t_r2 P tj)⟩
/-- After the watchdog. -/
def nu050t_r4 (P : RBTPol Nat Nat Nat) (tj : Timing) : RBTSt Nat Nat :=
  ⟨qFire (nu050t_r3 P tj).M nu050t_watch.base nu050t_eW, 10,
    rbtRestamp P (nu050t_X3 tj) (nu050t_r3 P tj) nu050t_watch none
      (qFire (nu050t_r3 P tj).M nu050t_watch.base nu050t_eW)⟩

theorem nu050t_join3_inNet (tj : Timing) : RBTInNet (nu050t_X3 tj) nu050t_join3 := rfl

/-- The AC3 run under the reference, for either timing of the join. -/
theorem nu050t_ac3_run (tj : Timing) (htj : tj = nu050t_onTime ∨ tj = nu050t_late) :
    RefRouteBT (nu050t_X3 tj) (nu050t_r0 refRBTPol tj) (.fire nu050t_forkA none nu050t_eA)
        (nu050t_r1 refRBTPol tj) ∧
      RefRouteBT (nu050t_X3 tj) (nu050t_r1 refRBTPol tj) (.fire nu050t_forkB none nu050t_eB)
        (nu050t_r2 refRBTPol tj) ∧
      RefRouteBT (nu050t_X3 tj) (nu050t_r2 refRBTPol tj) (.delay 10) (nu050t_r3 refRBTPol tj) ∧
      RefRouteBT (nu050t_X3 tj) (nu050t_r3 refRBTPol tj) (.fire nu050t_watch none nu050t_eW)
        (nu050t_r4 refRBTPol tj) := by
  rcases htj with rfl | rfl <;>
  refine ⟨RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_X3])
      (nu050t_plainFire rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩) (by decide) (by decide),
    RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_X3])
      (nu050t_plainFire rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩) (by decide) (by decide),
    RBTStepW.delay _ _ _ (fun u hu ha => ?_),
    RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_X3])
      (nu050t_plainFire rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩) (by decide)
      (by decide)⟩ <;>
  · simp only [nu050t_X3, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> revert ha <;> decide

/-- ✓ Worked example (AC3). Two forks put name 1 into A and name 2 into B, so the join's inputs
hold tokens but share no name; it has `window(0, 5)`, and a watchdog with `delayed(10)` marks
BAD. In Route B's timed semantics the join never gets a clock: time passes to 10 ms and the
watchdog marks BAD. The same run goes through on the relaxed net, where the join's timing is
`immediate`. So a sound Route B reports `unreachable(BAD)` violated, on time and late. -/
@[evidence nonvacuous NU_050_timed]
theorem NU_050_timed_ac3 :
    (∀ tj ∈ [nu050t_onTime, nu050t_late],
      RefRouteBT (nu050t_X3 tj) (nu050t_r0 refRBTPol tj) (.fire nu050t_forkA none nu050t_eA)
          (nu050t_r1 refRBTPol tj) ∧
        RefRouteBT (nu050t_X3 tj) (nu050t_r1 refRBTPol tj) (.fire nu050t_forkB none nu050t_eB)
          (nu050t_r2 refRBTPol tj) ∧
        RefRouteBT (nu050t_X3 tj) (nu050t_r2 refRBTPol tj) (.delay 10)
          (nu050t_r3 refRBTPol tj) ∧
        RefRouteBT (nu050t_X3 tj) (nu050t_r3 refRBTPol tj) (.fire nu050t_watch none nu050t_eW)
          (nu050t_r4 refRBTPol tj) ∧
        (nu050t_r4 refRBTPol tj).M 6 ≠ [] ∧
        (nu050t_r2 refRBTPol tj).stamp "join" = none ∧
        qCount (nu050t_r2 refRBTPol tj).M 2 = 1 ∧ qCount (nu050t_r2 refRBTPol tj).M 3 = 1 ∧
        ¬ NuShared nu050t_join3 (nu050t_r2 refRBTPol tj).M) ∧
      nu050t_late = .immediate := by
  refine ⟨fun tj htj => ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htj
  rcases htj with rfl | rfl
  · obtain ⟨h1, h2, h3, h4⟩ := nu050t_ac3_run nu050t_onTime (.inl rfl)
    refine ⟨h1, h2, h3, h4, by decide, by decide, by decide, by decide, fun h => ?_⟩
    have := (rbtSharedB_iff _ _).2 h
    revert this; decide
  · obtain ⟨h1, h2, h3, h4⟩ := nu050t_ac3_run nu050t_late (.inr rfl)
    refine ⟨h1, h2, h3, h4, by decide, by decide, by decide, by decide, fun h => ?_⟩
    have := (rbtSharedB_iff _ _).2 h
    revert this; decide

/-- Under the count-gated clock of the graph before the fix, on time, the join gets a clock at
0 ms as soon as both its inputs hold a token, although they share no name, and its latest bound
5 then refuses the 10 ms the watchdog needs: the deadline of a join that never fires holds the
watchdog back, so that graph would prove `unreachable(BAD)`. -/
theorem nu050t_countClock_ac3 :
    RBTStepW nu050t_countPol (nu050t_X3 nu050t_onTime) (nu050t_r1 nu050t_countPol nu050t_onTime)
        (.fire nu050t_forkB none nu050t_eB) (nu050t_r2 nu050t_countPol nu050t_onTime) ∧
      (nu050t_r2 nu050t_countPol nu050t_onTime).stamp "join" = some 0 ∧
      ∀ s', ¬ RBTStepW nu050t_countPol (nu050t_X3 nu050t_onTime)
        (nu050t_r2 nu050t_countPol nu050t_onTime) (.delay 10) s' := by
  refine ⟨RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_X3])
      (nu050t_plainFire rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩) (by decide)
      (by simp [nu050t_X3, nu050t_forkB, nu050t_plain, Timing.earliest]), by decide,
    fun s' h => ?_⟩
  cases h with
  | delay _ hurg =>
    have := hurg nu050t_join3 (by simp [nu050t_X3]) (by decide)
    revert this; decide

/-- ✗ The count-gated clock violates NU-050 (line 1): forkB's firing leaves name 1 in A and
name 2 in B, so the join's inputs hold tokens but share no name, and the count-gated semantics
gives the join a clock there. -/
@[evidence forbids NU_050_timed]
theorem NU_050_timed_forbids_countClock : ¬ NU_050_timed (RBTStepW nu050t_countPol) := by
  intro h
  have h1 := (h (nu050t_X3 nu050t_onTime) nu050t_join3 (nu050t_join3_inNet _)).1
    (.fire nu050t_forkB none nu050t_eB) _ _ nu050t_countClock_ac3.1 (fun hs => by
      have := (rbtEnB_iff _ _).2 hs
      revert this; decide)
  revert h1
  decide

/-! ### AC4: a join's clock starts when its inputs first share a name -/

/-- `join : A (0) + B (1) → out (3)`, correlated on both inputs. -/
def nu050t_join4 : NuTrans Nat (KeyFn Nat Nat) := nu050t_join 0 1 (some 3)
/-- `mv : S (2) → B (1)`, which carries a token of name 1 into B. -/
def nu050t_mv : NuTrans Nat (KeyFn Nat Nat) := nu050t_plain "mv" 2 1

/-- The AC4 net: the join `delayed(10)`, `mv` `delayed(4)`. -/
def nu050t_X4 : RBTNet Nat Nat Nat :=
  { trans := [nu050t_join4, nu050t_mv],
    timing := fun t => if t.core.name = "join" then .delayed 10 else .delayed 4 }

/-- At 1 ms: A holds name 1, B holds name 2, S holds name 1. -/
def nu050t_M4 : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu050t_tok 1 1] else if p = 1 then [nu050t_tok 2 1]
  else if p = 2 then [nu050t_tok 1 1] else []

/-- mv's emission: name 1 into B. -/
def nu050t_eM : List (Nat × Stamped Nat) := [(1, nu050t_tok 1 1)]
/-- The join's emission when it fires at 15 ms. -/
def nu050t_eJ : List (Nat × Stamped Nat) := [(3, nu050t_tok 1 15)]

/-- The AC4 states under policy `P`: at 1 ms, at 5 ms, after mv, and `d` ms after mv. -/
def nu050t_a0 (P : RBTPol Nat Nat Nat) : RBTSt Nat Nat := rbtInit P nu050t_X4 nu050t_M4 1
/-- At 5 ms. -/
def nu050t_a1 (P : RBTPol Nat Nat Nat) : RBTSt Nat Nat :=
  ⟨nu050t_M4, 5, rbtClean P nu050t_X4 (nu050t_a0 P)⟩
/-- After mv, at 5 ms. -/
def nu050t_a2 (P : RBTPol Nat Nat Nat) : RBTSt Nat Nat :=
  ⟨qFire nu050t_M4 nu050t_mv.base nu050t_eM, 5,
    rbtRestamp P nu050t_X4 (nu050t_a1 P) nu050t_mv none (qFire nu050t_M4 nu050t_mv.base nu050t_eM)⟩
/-- `d` ms after mv. -/
def nu050t_a3 (P : RBTPol Nat Nat Nat) (d : Nat) : RBTSt Nat Nat :=
  ⟨(nu050t_a2 P).M, 5 + d, rbtClean P nu050t_X4 (nu050t_a2 P)⟩

/-- The steps to the state `d` ms after mv, under the reference, for `d` = 9 and 10. -/
theorem nu050t_ac4_run (d : Nat) (hd : d = 9 ∨ d = 10) :
    RefRouteBT nu050t_X4 (nu050t_a0 refRBTPol) (.delay 4) (nu050t_a1 refRBTPol) ∧
      RefRouteBT nu050t_X4 (nu050t_a1 refRBTPol) (.fire nu050t_mv none nu050t_eM)
        (nu050t_a2 refRBTPol) ∧
      RefRouteBT nu050t_X4 (nu050t_a2 refRBTPol) (.delay d) (nu050t_a3 refRBTPol d) := by
  rcases hd with rfl | rfl <;>
  refine ⟨RBTStepW.delay _ _ _ (fun u hu ha => ?_),
    RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_X4])
      (nu050t_plainFire rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩) (by decide) (by decide),
    RBTStepW.delay _ _ _ (fun u hu ha => ?_)⟩ <;>
  · simp only [nu050t_X4, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> revert ha <;> decide

/-- ✓ Worked example (AC4). The join has `delayed(10)`. From 1 ms its inputs hold a token each
(A name 1, B name 2), so it is enabled on the counts but shares no name and has no clock. At
5 ms `mv` carries a token of name 1 into B, the inputs share name 1, and the join gets its clock
then. 9 ms later (14 ms) it cannot fire; 10 ms later (15 ms) it can. -/
@[evidence nonvacuous NU_050_timed]
theorem NU_050_timed_ac4 :
    RefRouteBT nu050t_X4 (nu050t_a0 refRBTPol) (.delay 4) (nu050t_a1 refRBTPol) ∧
      RefRouteBT nu050t_X4 (nu050t_a1 refRBTPol) (.fire nu050t_mv none nu050t_eM)
        (nu050t_a2 refRBTPol) ∧
      (nu050t_a1 refRBTPol).stamp "join" = none ∧
      rbtCountB nu050t_join4 (nu050t_a0 refRBTPol).M = true ∧
      (nu050t_a2 refRBTPol).stamp "join" = some 5 ∧
      RefRouteBT nu050t_X4 (nu050t_a2 refRBTPol) (.delay 9) (nu050t_a3 refRBTPol 9) ∧
      (∀ c e s', ¬ RefRouteBT nu050t_X4 (nu050t_a3 refRBTPol 9) (.fire nu050t_join4 c e) s') ∧
      RefRouteBT nu050t_X4 (nu050t_a2 refRBTPol) (.delay 10) (nu050t_a3 refRBTPol 10) ∧
      ∃ s', RefRouteBT nu050t_X4 (nu050t_a3 refRBTPol 10) (.fire nu050t_join4 (some 1) nu050t_eJ)
        s' := by
  obtain ⟨h1, h2, h9⟩ := nu050t_ac4_run 9 (.inl rfl)
  obtain ⟨-, -, h10⟩ := nu050t_ac4_run 10 (.inr rfl)
  refine ⟨h1, h2, by decide, by decide, by decide, h9, fun c e s' h => ?_, h10, ⟨_,
    RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_X4])
      ((refNuFire_matched rfl _ _ _ _ _).2 ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
        fun r hr => by simp at hr, rfl, rfl⟩) (by decide) (by decide)⟩⟩
  obtain ⟨-, -, -, hg, -⟩ := rbtStepW_fire_inv h
  revert hg
  decide

/-- Under the count-gated clock the AC4 join is clocked from 1 ms, when its inputs first hold
a token each, keeps that clock through mv's firing, and fires at 11 ms, 4 ms before AC4 allows. -/
theorem nu050t_countClock_ac4 :
    (nu050t_a2 nu050t_countPol).stamp "join" = some 1 ∧
      ∃ s', RBTStepW nu050t_countPol nu050t_X4 (nu050t_a3 nu050t_countPol 6)
        (.fire nu050t_join4 (some 1) nu050t_eJ) s' :=
  ⟨by decide, ⟨_, RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_X4])
      ((refNuFire_matched rfl _ _ _ _ _).2 ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
        fun r hr => by simp at hr, rfl, rfl⟩) (by decide) (by decide)⟩⟩

/-- ✗ A join that is never given a fresh clock when it comes to share a name violates NU-050
(line 4): in AC4, `mv` leaves the join enabled on name 1 and the join held no clock before, but
this policy leaves it without one. -/
@[evidence forbids NU_050_timed]
theorem NU_050_timed_forbids_noArm : ¬ NU_050_timed (RBTStepW nu050t_noArmPol) := by
  intro h
  have hstep : RBTStepW nu050t_noArmPol nu050t_X4 (nu050t_a1 nu050t_noArmPol)
      (.fire nu050t_mv none nu050t_eM) (nu050t_a2 nu050t_noArmPol) :=
    RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_X4])
      (nu050t_plainFire rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩) (by decide) (by decide)
  have h4 := (h nu050t_X4 nu050t_join4 rfl).2.2.2.1 nu050t_mv none nu050t_eM _ _ hstep
    (by decide) ((rbtEnB_iff _ _).1 (by decide))
  revert h4
  decide

/-! ### A restart when the bound name leaves, and a kept clock when another name stays -/

/-- `cyc : A (0) → A (0)`: takes A's head and puts a token back. -/
def nu050t_cyc : NuTrans Nat (KeyFn Nat Nat) := nu050t_plain "cyc" 0 0
/-- `take : A (0) → C (2)`: takes A's head. -/
def nu050t_take : NuTrans Nat (KeyFn Nat Nat) := nu050t_plain "take" 0 2
/-- `join : A (0) + B (1)`, correlated on both, no output spec. -/
def nu050t_joinR : NuTrans Nat (KeyFn Nat Nat) := nu050t_join 0 1 none

/-- The net of `joinR` and a transition `t`, all `immediate`. -/
def nu050t_XR (t : NuTrans Nat (KeyFn Nat Nat)) : RBTNet Nat Nat Nat :=
  { trans := [nu050t_joinR, t], timing := fun _ => .immediate }

/-- A state at 7 ms with the join and `t` stamped 2 and the marking `M`. -/
def nu050t_q (t : NuTrans Nat (KeyFn Nat Nat)) (M : QMarking Nat (Stamped Nat)) :
    RBTSt Nat Nat :=
  ⟨M, 7, fun n => if n = "join" ∨ n = t.base.core.name then some 2 else none⟩

/-- Restart marking: A holds names 1 and 3, B holds name 1. -/
def nu050t_MR : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu050t_tok 1 0, nu050t_tok 3 1] else if p = 1 then [nu050t_tok 1 0] else []
/-- Keep marking: A and B each hold names 1 and 2. -/
def nu050t_MK : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 ∨ p = 1 then [nu050t_tok 1 0, nu050t_tok 2 1] else []

/-- cyc's emission: name 1 back into A. -/
def nu050t_eC : List (Nat × Stamped Nat) := [(0, nu050t_tok 1 0)]
/-- take's emission: a token into C. -/
def nu050t_eT : List (Nat × Stamped Nat) := [(2, nu050t_tok 1 0)]

/-- The state after `t` fires from `nu050t_q t M` with emission `e`, under policy `P`. -/
def nu050t_qAfter (P : RBTPol Nat Nat Nat) (t : NuTrans Nat (KeyFn Nat Nat))
    (M : QMarking Nat (Stamped Nat)) (e : List (Nat × Stamped Nat)) : RBTSt Nat Nat :=
  ⟨qFire M t.base e, 7, rbtRestamp P (nu050t_XR t) (nu050t_q t M) t none (qFire M t.base e)⟩

/-- The firing of `t` from `nu050t_q t M`, under any policy that clocks by ν enablement or by
the counts. -/
theorem nu050t_qStep (P : RBTPol Nat Nat Nat) (t : NuTrans Nat (KeyFn Nat Nat))
    (M : QMarking Nat (Stamped Nat)) (e : List (Nat × Stamped Nat)) (hm : t.mspec = none)
    (hq : RefQFire t.base M (qDelivered M t.base) e (qFire M t.base e))
    (ha : rbtArmed P (nu050t_q t M) t = true) :
    RBTStepW P (nu050t_XR t) (nu050t_q t M) (.fire t none e) (nu050t_qAfter P t M e) :=
  RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_XR]) (nu050t_plainFire hm hq) ha
    (by simp [nu050t_XR, Timing.earliest])

/-- ✓ Worked example (lines 2 and 3). The join's inputs are A = [1, 3] and B = [1], so it
shares name 1 and holds a clock from 2 ms. At 7 ms `cyc` takes name 1 out of A and puts it back:
in the intermediate marking A = [3] and B = [1] still hold tokens but share no name, so the join
restarts its clock at 7 ms. With A = B = [1, 2] instead, `take` removes name 1 from A, but name 2
stays in both inputs, so the join keeps its clock from 2 ms. -/
@[evidence nonvacuous NU_050_timed]
theorem NU_050_timed_restart_keep :
    RefRouteBT (nu050t_XR nu050t_cyc) (nu050t_q nu050t_cyc nu050t_MR) (.fire nu050t_cyc none nu050t_eC)
        (nu050t_qAfter refRBTPol nu050t_cyc nu050t_MR nu050t_eC) ∧
      qCount (rbtMid nu050t_cyc nu050t_MR none) 0 = 1 ∧
      qCount (rbtMid nu050t_cyc nu050t_MR none) 1 = 1 ∧
      ¬ NuShared nu050t_joinR (rbtMid nu050t_cyc nu050t_MR none) ∧
      (nu050t_qAfter refRBTPol nu050t_cyc nu050t_MR nu050t_eC).stamp "join" = some 7 ∧
      RefRouteBT (nu050t_XR nu050t_take) (nu050t_q nu050t_take nu050t_MK)
        (.fire nu050t_take none nu050t_eT) (nu050t_qAfter refRBTPol nu050t_take nu050t_MK nu050t_eT) ∧
      NuEnabled nu050t_joinR (rbtMid nu050t_take nu050t_MK none) ∧
      (nu050t_qAfter refRBTPol nu050t_take nu050t_MK nu050t_eT).stamp "join" = some 2 := by
  refine ⟨nu050t_qStep _ nu050t_cyc nu050t_MR nu050t_eC rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩ (by decide),
    by decide, by decide, fun h => ?_, by decide,
    nu050t_qStep _ nu050t_take nu050t_MK nu050t_eT rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩ (by decide),
    (rbtEnB_iff _ _).1 (by decide), by decide⟩
  have := (rbtSharedB_iff _ _).2 h
  revert this; decide

/-- ✗ A restart judged on the counts of the intermediate marking violates NU-050 (line 2): when
`cyc` takes name 1 out of A and puts it back, A = [3] and B = [1] still hold a token each, so the
counts keep the join enabled and this policy keeps its clock from 2 ms, where no shared name is
left and the clock must restart at 7 ms. -/
@[evidence forbids NU_050_timed]
theorem NU_050_timed_forbids_countMid : ¬ NU_050_timed (RBTStepW nu050t_countMidPol) := by
  intro h
  have h2a := (h (nu050t_XR nu050t_cyc) nu050t_joinR rfl).2.1 nu050t_cyc none nu050t_eC
    (by decide) _ _
    (nu050t_qStep _ nu050t_cyc nu050t_MR nu050t_eC rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩ (by decide)) (by decide)
    (fun hs => by
      have := (rbtEnB_iff _ _).2 hs
      revert this; decide) ((rbtEnB_iff _ _).1 (by decide))
  revert h2a
  decide

/-- ✗ A restart on every take from a correlated input violates NU-050 (line 3): `take` removes
name 1 from A, but name 2 stays in both inputs, so the join is enabled before, in the
intermediate marking and after, and must keep its clock from 2 ms; this policy restarts it at
7 ms. -/
@[evidence forbids NU_050_timed]
theorem NU_050_timed_forbids_restartOnTake : ¬ NU_050_timed (RBTStepW nu050t_takePol) := by
  intro h
  have h3 := (h (nu050t_XR nu050t_take) nu050t_joinR rfl).2.2.1 nu050t_take none nu050t_eT
    (by decide) _ _
    (nu050t_qStep _ nu050t_take nu050t_MK nu050t_eT rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩ (by decide)) (by decide)
    ((rbtEnB_iff _ _).1 (by decide)) ((rbtEnB_iff _ _).1 (by decide))
    ((rbtEnB_iff _ _).1 (by decide))
  revert h3
  decide

/-! ### A permit input: names shared, counts not -/

/-- `join : A (0) + B (1) + P (2)`, correlated on A and B only: P is a plain input, a permit. -/
def nu050t_joinP : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "join", inputs := [⟨0, .one⟩, ⟨1, .one⟩, ⟨2, .one⟩],
                        inhibitors := [], reads := [], resets := [] }, out := none }
    mspec := some { keys := [(0, nu050t_key), (1, nu050t_key)] } }

/-- `cycP : P (2) → P (2)`: takes the permit and puts one back. -/
def nu050t_cycP : NuTrans Nat (KeyFn Nat Nat) := nu050t_plain "cycP" 2 2
/-- `takeP : P (2) → C (6)`: takes the permit. -/
def nu050t_takeP : NuTrans Nat (KeyFn Nat Nat) := nu050t_plain "takeP" 2 6

/-- The net of `joinP` and a transition `t`, all `immediate`. -/
def nu050t_XP (t : NuTrans Nat (KeyFn Nat Nat)) : RBTNet Nat Nat Nat :=
  { trans := [nu050t_joinP, t], timing := fun _ => .immediate }

/-- A and B hold name 1, P holds a permit. -/
def nu050t_MP : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 ∨ p = 1 then [nu050t_tok 1 0] else if p = 2 then [nu050t_tok 0 0] else []

/-- cycP's emission: a permit back into P. -/
def nu050t_eP : List (Nat × Stamped Nat) := [(2, nu050t_tok 0 0)]
/-- takeP's emission: a token into C. -/
def nu050t_eTP : List (Nat × Stamped Nat) := [(6, nu050t_tok 0 0)]

/-- The state after `t` fires from `nu050t_q t nu050t_MP` with emission `e`, under policy `P`. -/
def nu050t_qAfterP (P : RBTPol Nat Nat Nat) (t : NuTrans Nat (KeyFn Nat Nat))
    (e : List (Nat × Stamped Nat)) : RBTSt Nat Nat :=
  ⟨qFire nu050t_MP t.base e, 7,
    rbtRestamp P (nu050t_XP t) (nu050t_q t nu050t_MP) t none (qFire nu050t_MP t.base e)⟩

/-- The firing of `t` from `nu050t_q t nu050t_MP`. -/
theorem nu050t_qStepP (P : RBTPol Nat Nat Nat) (t : NuTrans Nat (KeyFn Nat Nat))
    (e : List (Nat × Stamped Nat)) (hm : t.mspec = none)
    (hq : RefQFire t.base nu050t_MP (qDelivered nu050t_MP t.base) e (qFire nu050t_MP t.base e))
    (ha : rbtArmed P (nu050t_q t nu050t_MP) t = true) :
    RBTStepW P (nu050t_XP t) (nu050t_q t nu050t_MP) (.fire t none e) (nu050t_qAfterP P t e) :=
  RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_XP]) (nu050t_plainFire hm hq) ha
    (by simp [nu050t_XP, Timing.earliest])

/-! ### The fired join itself -/

/-- The marking after `joinR` fires on name 1 from A = B = [1, 2]: A = B = [2]. -/
def nu050t_MK' : QMarking Nat (Stamped Nat) :=
  match nu050t_joinR.mspec with
  | some ms => qAppend (nuConsume ms nu050t_joinR nu050t_MK 1) []
  | none => nu050t_MK

/-- `joinR` fires on name 1 from A = B = [1, 2], with no emission. -/
theorem nu050t_fireK : RefNuFire nu050t_joinR nu050t_MK (some 1)
    (nuDelivered { keys := [(0, nu050t_key), (1, nu050t_key)] } nu050t_joinR nu050t_MK 1) []
    nu050t_MK' :=
  (refNuFire_matched rfl _ _ _ _ _).2 ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
    fun r hr => by simp at hr, rfl, rfl⟩

/-- The state after `joinR` fires on name 1, under policy `P`. -/
def nu050t_kAfter (P : RBTPol Nat Nat Nat) : RBTSt Nat Nat :=
  ⟨nu050t_MK', 7, rbtRestamp P (nu050t_XR nu050t_take) (nu050t_q nu050t_take nu050t_MK)
    nu050t_joinR (some 1) nu050t_MK'⟩

/-- The firing of `joinR` on name 1, under any policy that clocks by ν enablement. -/
theorem nu050t_kStep (P : RBTPol Nat Nat Nat)
    (ha : rbtArmed P (nu050t_q nu050t_take nu050t_MK) nu050t_joinR = true) :
    RBTStepW P (nu050t_XR nu050t_take) (nu050t_q nu050t_take nu050t_MK)
      (.fire nu050t_joinR (some 1) []) (nu050t_kAfter P) :=
  RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_XR]) nu050t_fireK ha
    (by simp [nu050t_XR, Timing.earliest])

/-- ✓ Worked example (lines 1, 2 and 5). The join takes A and B by name and a permit from P.
A and B hold name 1, P holds a permit, and the join holds a clock from 2 ms. At 7 ms `cycP`
takes the permit and puts one back: in between, the names are still shared but P is empty, so
the join is not enabled there and its clock restarts at 7 ms. If `takeP` takes the permit for
good, the names stay shared but the join is not enabled, so it holds no clock at all. Last, a
join whose inputs A and B hold names 1 and 2 fires on name 1 at 7 ms; name 2 is still shared, so
the join is enabled again and its clock starts afresh at 7 ms. -/
@[evidence nonvacuous NU_050_timed]
theorem NU_050_timed_permit_fired :
    RefRouteBT (nu050t_XP nu050t_cycP) (nu050t_q nu050t_cycP nu050t_MP)
        (.fire nu050t_cycP none nu050t_eP) (nu050t_qAfterP refRBTPol nu050t_cycP nu050t_eP) ∧
      NuShared nu050t_joinP (rbtMid nu050t_cycP nu050t_MP none) ∧
      ¬ NuEnabled nu050t_joinP (rbtMid nu050t_cycP nu050t_MP none) ∧
      (nu050t_qAfterP refRBTPol nu050t_cycP nu050t_eP).stamp "join" = some 7 ∧
      RefRouteBT (nu050t_XP nu050t_takeP) (nu050t_q nu050t_takeP nu050t_MP)
        (.fire nu050t_takeP none nu050t_eTP) (nu050t_qAfterP refRBTPol nu050t_takeP nu050t_eTP) ∧
      NuShared nu050t_joinP (nu050t_qAfterP refRBTPol nu050t_takeP nu050t_eTP).M ∧
      (nu050t_qAfterP refRBTPol nu050t_takeP nu050t_eTP).stamp "join" = none ∧
      RefRouteBT (nu050t_XR nu050t_take) (nu050t_q nu050t_take nu050t_MK)
        (.fire nu050t_joinR (some 1) []) (nu050t_kAfter refRBTPol) ∧
      NuEnabled nu050t_joinR nu050t_MK' ∧
      (nu050t_kAfter refRBTPol).stamp "join" = some 7 := by
  refine ⟨nu050t_qStepP _ nu050t_cycP nu050t_eP rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
      (by decide), (rbtSharedB_iff _ _).1 (by decide), fun h => ?_, by decide,
    nu050t_qStepP _ nu050t_takeP nu050t_eTP rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
      (by decide), (rbtSharedB_iff _ _).1 (by decide), by decide,
    nu050t_kStep _ (by decide), (rbtEnB_iff _ _).1 (by decide), by decide⟩
  have := (rbtEnB_iff _ _).2 h
  revert this; decide

/-- ✗ A clock gated on the names alone violates NU-050 (line 1): after `takeP` takes the permit
for good, A and B still share name 1, so this policy gives the join a fresh clock at 7 ms,
although the empty permit place leaves the join not enabled. -/
@[evidence forbids NU_050_timed]
theorem NU_050_timed_forbids_sharedClock : ¬ NU_050_timed (RBTStepW nu050t_sharedPol) := by
  intro h
  have h1 := (h (nu050t_XP nu050t_takeP) nu050t_joinP rfl).1 (.fire nu050t_takeP none nu050t_eTP)
    _ _ (nu050t_qStepP _ nu050t_takeP nu050t_eTP rfl ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
      (by decide)) (fun hs => by
        have := (rbtEnB_iff _ _).2 hs
        revert this; decide)
  revert h1
  decide

/-- ✗ A kept clock judged on the names alone in the intermediate marking violates NU-050
(line 2): when `cycP` takes the permit and puts one back, A and B share name 1 throughout, so
this policy keeps the join's clock from 2 ms, where the empty permit place in between must
restart it at 7 ms. -/
@[evidence forbids NU_050_timed]
theorem NU_050_timed_forbids_midShared : ¬ NU_050_timed (RBTStepW nu050t_midSharedPol) := by
  intro h
  have h2 := (h (nu050t_XP nu050t_cycP) nu050t_joinP rfl).2.1 nu050t_cycP none nu050t_eP
    (by decide) _ _ (nu050t_qStepP _ nu050t_cycP nu050t_eP rfl
      ⟨by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩ (by decide)) (by decide)
    (fun hs => by
      have := (rbtEnB_iff _ _).2 hs
      revert this; decide) ((rbtEnB_iff _ _).1 (by decide))
  revert h2
  decide

/-- ✗ A fired join that keeps its own clock violates NU-050 (line 5): the join fires on name 1
at 7 ms and name 2 is still shared, so it must start a fresh clock at 7 ms; this policy keeps
the stamp from 2 ms. -/
@[evidence forbids NU_050_timed]
theorem NU_050_timed_forbids_firedKeep : ¬ NU_050_timed (RBTStepW nu050t_firedKeepPol) := by
  intro h
  have h5 := (h (nu050t_XR nu050t_take) nu050t_joinR rfl).2.2.2.2.1 nu050t_joinR (some 1) [] rfl
    _ _ (nu050t_kStep _ (by decide)) ((rbtEnB_iff _ _).1 (by decide))
  revert h5
  decide

/-- ✗ Clocks that never age violate NU-050 (line 6): in AC4 the join's clock starts at 5 ms;
after 9 ms this semantics restamps it to 14 ms, so the join could not fire at 15 ms. -/
@[evidence forbids NU_050_timed]
theorem NU_050_timed_forbids_ageless : ¬ NU_050_timed nu050t_agelessRel := by
  intro h
  obtain ⟨-, -, h9⟩ := nu050t_ac4_run 9 (.inl rfl)
  have h6 := (h nu050t_X4 nu050t_join4 rfl).2.2.2.2.2.1 9 _ _ ⟨_, h9, rfl⟩
  have h6c := h6.2.2 ((rbtEnB_iff _ _).1 (by decide))
  revert h6c
  decide

/-- ✗ Firing without the earliest bound violates NU-050 (line 7): in AC4 the join's clock
starts at 5 ms and its earliest bound is 10 ms, but this semantics lets it fire at 14 ms. -/
@[evidence forbids NU_050_timed]
theorem NU_050_timed_forbids_untimed : ¬ NU_050_timed nu050t_untimedRel := by
  intro h
  have hstep : nu050t_untimedRel nu050t_X4 (nu050t_a3 refRBTPol 9)
      (.fire nu050t_join4 (some 1) nu050t_eJ) _ :=
    RBTStepW.fire _ _ _ _ _ _ _ (by simp [nu050t_X4])
      ((refNuFire_matched rfl _ _ _ _ _).2 ⟨1, rfl, by decide, by decide, ⟨.action 0, rfl⟩,
        fun r hr => by simp at hr, rfl, rfl⟩) (by decide) (by simp [Timing.earliest])
  have h7 := (h nu050t_X4 nu050t_join4 rfl).2.2.2.2.2.2 (some 1) nu050t_eJ _ _ hstep
  exact absurd h7.2.1 (by decide)

/-- AC4 from the lines alone, for every relation that meets them: from the state just after `mv`
fired at 5 ms, a 9 ms delay keeps the join's stamp 5 and reads 14 ms (line 6), and from any state
at 14 ms whose join is stamped 5 the join cannot fire (line 7), so it fires at 15 ms at the
earliest. -/
theorem nu050t_ac4_of_statement {R : RBTRel Nat Nat Nat} (hR : NU_050_timed R) :
    (∀ s', R nu050t_X4 (nu050t_a2 refRBTPol) (.delay 9) s' →
      s'.stamp "join" = some 5 ∧ s'.now = 14) ∧
    ∀ s s' c e, s.stamp "join" = some 5 → s.now = 14 →
      ¬ R nu050t_X4 s (.fire nu050t_join4 c e) s' := by
  refine ⟨fun s' hd => ?_, fun s s' c e hs hn hf => ?_⟩
  · have h6 := (hR nu050t_X4 nu050t_join4 rfl).2.2.2.2.2.1 9 _ _ hd
    have hk := h6.2.2 ((rbtEnB_iff _ _).1 (by decide))
    have e2 : (nu050t_a2 refRBTPol).stamp "join" = some 5 := by decide
    exact ⟨hk.trans e2, h6.2.1.trans rfl⟩
  · have hg := ((hR nu050t_X4 nu050t_join4 rfl).2.2.2.2.2.2 c e s s' hf).2.1
    have hel : rbtElapsed s nu050t_join4 = 9 := by
      show s.now - (s.stamp "join").getD s.now = 9
      rw [hs, hn]; rfl
    rw [hel] at hg
    revert hg
    decide

end Examples

end Libpetri.Spec
