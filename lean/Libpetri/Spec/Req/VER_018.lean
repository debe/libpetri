import Libpetri.Spec.Registry
import Libpetri.StateEquation
import Libpetri.Novel.Certificate
import Libpetri.Novel.Commoner
import Libpetri.Novel.FiringBound.Ranking
import Libpetri.Spec.Req.VER_019
import Libpetri.Spec.Text.VER_018

set_option linter.missingDocs true

/-!
# VER-018: State-equation phase with refinement (`spec/07-verification.md`)

Before the fixpoint query the verifier asks one `QF_LIA` query: can a marking that satisfies the
marking equation `m = M0 + C·n` of [VER-016] violate the property? `unsat` proves the property,
since every reachable marking satisfies the equation for the counts of its run. A `sat` model is
a **candidate** `(M, n)`. The phase settles it, in this order, by a **witness** (a run within
the counts `n` that ends in a violating marking: the property is violated), a **trap** (an
initially marked trap the candidate leaves empty: `Σ_{q∈Q} m_q ≥ 1` is added), an **inductive
inequality** `a·M ≤ b` (re-checked in exact integer arithmetic) or a **relative** one (inductive
only together with the equation), and asks again. A proof goes to the certificate check of
[VER-016] before it is reported.

The requirement is a predicate over five parts:

* `S : SESearch`, the witness search, from the flat net, the injected places, `M0`, the
  candidate's counts, the violation and the node budget to a run, `none` (a completed search
  found nothing) or `exhausted` (the search proves nothing);
* `T : SETrapFn`, the trap search, from the flat net, the place count, `M0` and the candidate's
  marking to a trap or nothing;
* `X : SEIndCheck`, the exact re-check of an inductive inequality;
* `P : SEPhaseFn`, the refinement loop, from the net, `M0`, the violation, the refinement limit,
  the node budget, the answers of the solver (the state-equation query per list of refinements,
  the two `invariant` queries per candidate marking) and the refinements so far, to an outcome;
* `W : SEWrap`, the hand-over, from an outcome and the answer of the certificate check to what
  the phase returns to the pipeline.

The witness is `refSESearch` (the runs within the counts, shortest first), `refSETrap` (every
subset of the places, in order), `refSECheckInd` (the re-check of `check_inductive_exact`,
`invariant_synthesis.rs`), `refSEPhase` (the loop of `run_state_equation_phase`,
`state_equation_phase.rs`) and `refSEWrap` (`state_equation_decision`, `smt_verifier.rs`). From
the statement alone: a reported run reaches a violating marking (`VER_018_violated_sound`); a
trap or inductive refinement holds on every reachable marking (`VER_018_refinements_hold`); the
re-check accepts at least what the reference accepts, so the join of AC2 stays provable; a
`Proven` reported after a passed certificate check is sound (`VER_018_proven_sound`), and so is
the bare `unsat`, when the solver is right and the relative refinements hold
(`VER_018_unsat_sound`).

A second block, `VER_018_order` at the end of the file, places the phase in the pipeline: once,
after the linear bound of [VER-015] and before the fixpoint query, entered exactly on the flat
path with its option on.
-/

namespace Libpetri.Spec

open Libpetri (AMarking PlaceId Transition FlatNet FlatTransition Weight Counters dot isum
  enabledA fireA pre post consumeAllAt StepAInjRel ReachAInj ReachCnt StepCntRel ProvenFor)
open Libpetri.Novel.FiringBound (canFire not_canFire_never_enabled)

/-! ## The model -/

/-- Where a refinement comes from. -/
inductive SEOrigin where
  /-- An initially marked trap the candidate leaves empty. -/
  | trap
  /-- An inequality kept by every step of the exact step relation. -/
  | inductive
  /-- An inequality kept by every step from a marking that satisfies the marking equation. -/
  | relative
  deriving DecidableEq, Repr

/-- A refinement: the linear inequality `a·M ≤ b` over the places, and where it comes from. -/
structure SEIneq where
  /-- The weight of each place. -/
  a : Weight
  /-- The bound. -/
  b : Int
  /-- Where it comes from. -/
  origin : SEOrigin

/-- Whether the marking `m` meets `a·M ≤ b` over the first `w` places. -/
def SEIneq.holds (w : Nat) (r : SEIneq) (m : AMarking) : Bool := decide (dot r.a m w ≤ r.b)

/-- A candidate: the marking and the firing counts of a `sat` model. -/
structure SECand where
  /-- The candidate marking. -/
  m : AMarking
  /-- The firing count of each flat transition. -/
  n : Counters

/-- The answer of the state-equation query. -/
inductive SEAns where
  /-- `sat`, with the candidate the model gives. -/
  | sat (c : SECand)
  /-- `unsat`. -/
  | unsat
  /-- No `sat` or `unsat` answer: `unknown`, a transport failure, a model that cannot be
  decoded, or a spent phase budget. -/
  | aside

/-- The answer of an `invariant` query. -/
inductive SESynAns where
  /-- `sat`, with the weights and the bound the model gives. -/
  | found (a : Weight) (b : Int)
  /-- `unsat`: no such inequality. -/
  | none
  /-- No `sat` or `unsat` answer (`unknown`, a transport failure or a spent phase budget), or a
  model that cannot be decoded. -/
  | aside

/-- What a witness search ends with. -/
inductive SESearchOut where
  /-- A run, as flat transition indices in firing order. -/
  | found (run : List Nat)
  /-- The search completed and no run within the counts ends in a violating marking. -/
  | none
  /-- The search proves nothing. -/
  | exhausted
  deriving DecidableEq, Repr

/-- Why the phase steps aside. -/
inductive SEReason where
  /-- The state-equation query got no `sat` or `unsat` answer. -/
  | queryAside
  /-- A candidate is unsettled after the refinement limit. -/
  | limit
  /-- An inequality failed the exact re-check or does not exclude its candidate. -/
  | recheck
  /-- No trap and no inequality excludes the candidate. -/
  | noRefinement
  /-- An `invariant` query got no `sat` or `unsat` answer. -/
  | synthesisAside
  deriving DecidableEq, Repr

/-- What the phase ends with. Every arm carries the refinements added, in order. -/
inductive SEOutcome where
  /-- The state-equation query answered `unsat` over these refinements. -/
  | proven (refs : List SEIneq)
  /-- A run within a candidate's counts ends in a violating marking. -/
  | violated (run : List Nat) (refs : List SEIneq)
  /-- The phase steps aside. -/
  | inconclusive (why : SEReason) (refs : List SEIneq)

/-- The answer of the certificate check of [VER-016] on a proof of the phase. -/
inductive SECert where
  /-- Initiation, consecution and safety all `unsat`. -/
  | passed
  /-- A verification condition has a model. -/
  | failed
  /-- A verification condition got no `sat` or `unsat` answer. -/
  | inconclusive
  /-- The certificate check is disabled. -/
  | disabled
  deriving DecidableEq, Repr

/-- An outcome with the refinements reduced to their origins, for examples. -/
inductive SESummary where
  /-- A proof. -/
  | proven (origins : List SEOrigin)
  /-- A run. -/
  | violated (run : List Nat) (origins : List SEOrigin)
  /-- Stepping aside. -/
  | inconclusive (why : SEReason) (origins : List SEOrigin)
  deriving DecidableEq, Repr

/-- The refinements an outcome carries. -/
def SEOutcome.refs : SEOutcome → List SEIneq
  | .proven rs => rs
  | .violated _ rs => rs
  | .inconclusive _ rs => rs

/-- The summary of an outcome. -/
def SEOutcome.summary : SEOutcome → SESummary
  | .proven rs => .proven (rs.map (·.origin))
  | .violated run rs => .violated run (rs.map (·.origin))
  | .inconclusive why rs => .inconclusive why (rs.map (·.origin))

/-- Whether an outcome is a proof. -/
def SEOutcome.isProven : SEOutcome → Bool
  | .proven _ => true
  | _ => false

/-- Whether an outcome is stepping aside. -/
def SEOutcome.isInconclusive : SEOutcome → Bool
  | .inconclusive _ _ => true
  | _ => false

/-! ### Runs within the counts -/

/-- Fire the flat transitions named by index in order under the exact abstract semantics of
[VER-004] (`enabledA`, `fireA`), with no injection step; `none` on a disabled firing or an index
the net does not have. -/
def seReplay (net : FlatNet) : AMarking → List Nat → Option AMarking
  | a, [] => some a
  | a, k :: ks =>
    match net[k]? with
    | some ft => if enabledA a ft.1 = true then seReplay net (fireA a ft.1 ft.2) ks else none
    | none => none

/-- The run replays from `a0` and its last marking violates. -/
def seHits (net : FlatNet) (bad : AMarking → Bool) (a0 : AMarking) (run : List Nat) : Bool :=
  match seReplay net a0 run with
  | some a => bad a
  | none => false

/-- The run fires each flat transition `k` at most `c k` times. -/
def SEWithin (run : List Nat) (c : Counters) : Prop := ∀ k ∈ run, run.count k ≤ c k

instance (run : List Nat) (c : Counters) : Decidable (SEWithin run c) := by
  unfold SEWithin; infer_instance

/-- A witness search: `S net envs a0 c bad B` on the flat net `net` with the injected places
`envs`, from `M0 = a0`, within the counts `c`, for the violation `bad`, with the node budget
`B`. -/
abbrev SESearch : Type :=
  FlatNet → List PlaceId → AMarking → Counters → (AMarking → Bool) → Nat → SESearchOut

/-- The counts after one firing of `k`. -/
def seDec (c : Counters) (k : Nat) : Counters := fun j => if j = k then c j - 1 else c j

/-- The runs of length `L` over the transitions below `T` within the counts `c`, in
lexicographic order. -/
def seRuns (T : Nat) : Nat → Counters → List (List Nat)
  | 0, _ => [[]]
  | L + 1, c =>
    (List.range T).flatMap fun k =>
      if 0 < c k then (seRuns T L (seDec c k)).map (k :: ·) else []

/-- The sum of the counts of the transitions below `T`: no run within the counts is longer. -/
def seTotal (T : Nat) (c : Counters) : Nat := ∑ k ∈ Finset.range T, c k

/-- The levels in order: the first run of the first level that hits a violating marking. -/
def seScan (net : FlatNet) (bad : AMarking → Bool) (a0 : AMarking) (c : Counters) :
    List Nat → Option (List Nat)
  | [] => none
  | L :: Ls =>
    match (seRuns net.length L c).find? (seHits net bad a0) with
    | some r => some r
    | none => seScan net bad a0 c Ls

/-- **The reference witness search**: the runs within the counts, shortest first and in flat
order within a length, up to the sum of the counts; the first that ends in a violating marking is
the run. A search that finds nothing has completed: it reports `none` on a net with no injected
place and `exhausted` otherwise. It needs no node budget (it is not a breadth-first search over
markings, and the budget is a parameter it ignores). -/
def refSESearch : SESearch := fun net envs a0 c bad _ =>
  match seScan net bad a0 c (List.range (seTotal net.length c + 1)) with
  | some r => .found r
  | none => if envs.isEmpty then .none else .exhausted

/-! ### Traps -/

/-- A firing of `t` can take tokens from `p`: an input arc that requires one, a consume-all
input or a reset arc. -/
def seDrains (t : Transition) (p : PlaceId) : Bool :=
  decide (0 < pre t p) || consumeAllAt t p || t.resets.contains p

/-- **A trap** with clearing arcs: every flat transition that can take tokens from `Q` puts one
into `Q`. -/
def SEGTrap (net : FlatNet) (Q : List PlaceId) : Prop :=
  ∀ ft ∈ net, (∃ p ∈ Q, seDrains ft.1 p = true) → ∃ q ∈ Q, ft.2.contains q = true

/-- `SEGTrap` as a test. -/
def seGTrapB (net : FlatNet) (Q : List PlaceId) : Bool :=
  net.all fun ft => !(Q.any (seDrains ft.1)) || Q.any (ft.2.contains ·)

/-- A trap search: `T net w a0 m` on the flat net `net` with `w` places, from `M0 = a0`, for the
candidate marking `m`. -/
abbrev SETrapFn : Type := FlatNet → Nat → AMarking → AMarking → Option (List PlaceId)

/-- `Q` is a trap, marked at `a0` and empty in `m`. -/
def seTrapOk (net : FlatNet) (a0 m : AMarking) (Q : List PlaceId) : Bool :=
  seGTrapB net Q && Q.any (fun q => decide (0 < a0 q)) && Q.all (fun q => m q == 0)

/-- **The reference trap search**: the first subset of the places that is a trap, marked at
`M0` and empty in the candidate. -/
def refSETrap : SETrapFn := fun net w a0 m => (List.range w).sublists.find? (seTrapOk net a0 m)

/-- The refinement of a trap: `Σ_{q∈Q} m_q ≥ 1`, written `−Σ_{q∈Q} m_q ≤ −1`. -/
def seTrapIneq (Q : List PlaceId) : SEIneq :=
  ⟨fun p => if Q.contains p then -1 else 0, -1, .trap⟩

/-! ### Inductive inequalities -/

/-- `a·M ≤ b` holds at `M0` and every step of the exact step relation with injection keeps it. -/
def SEInductive (net : FlatNet) (envs : List PlaceId) (w : Nat) (a0 : AMarking) (r : SEIneq) :
    Prop :=
  dot r.a a0 w ≤ r.b ∧
    ∀ m m', dot r.a m w ≤ r.b → StepAInjRel net envs m m' → dot r.a m' w ≤ r.b

/-- An exact re-check: `X net envs w a0 r` accepts the inequality `r` on the flat net `net` with
the injected places `envs` and `w` places, from `M0 = a0`. -/
abbrev SEIndCheck : Type := FlatNet → List PlaceId → Nat → AMarking → SEIneq → Bool

/-- A consume-all input or a reset arc empties `p`. -/
def seCleared (t : Transition) (p : PlaceId) : Bool := t.resets.contains p || consumeAllAt t p

/-- The least the guard lets `p` hold: `max(pre, 1 if p is read)`. -/
def seLower (t : Transition) (p : PlaceId) : Int :=
  max (pre t p : Int) (if t.reads.contains p then 1 else 0)

/-- The coefficient of `a_p` when the firing keeps the bound (`λ = 1`): what the firing adds to
`p` at most. -/
def seKeepC (ft : FlatTransition) (p : PlaceId) : Int :=
  if seCleared ft.1 p then
    (if ft.1.inhibitors.contains p then (post ft.2 p : Int) else (post ft.2 p : Int) - seLower ft.1 p)
  else (post ft.2 p : Int) - pre ft.1 p

/-- The coefficient of `a_p` when the firing restores the bound from its guard (`λ = 0`): what
`p` holds after the firing at least (exactly, on a free place). -/
def seRestoreC (ft : FlatTransition) (p : PlaceId) : Int :=
  if seCleared ft.1 p then (post ft.2 p : Int)
  else if ft.1.inhibitors.contains p then (post ft.2 p : Int) - pre ft.1 p
  else (post ft.2 p : Int) - pre ft.1 p + seLower ft.1 p

/-- A place whose value after the firing the guard fixes: cleared or inhibited. -/
def seFree (ft : FlatTransition) (p : PlaceId) : Bool :=
  seCleared ft.1 p || ft.1.inhibitors.contains p

/-- The firing keeps `a·M ≤ b` (`λ = 1`). -/
def seKeeps (w : Nat) (a : Weight) (ft : FlatTransition) : Bool :=
  (List.range w).all (fun p => !(seCleared ft.1 p && !ft.1.inhibitors.contains p) || decide (0 ≤ a p))
    && decide (isum (fun p => seKeepC ft p * a p) w ≤ 0)

/-- The firing restores `a·M ≤ b` from its guard alone (`λ = 0`). -/
def seRestores (w : Nat) (r : SEIneq) (ft : FlatTransition) : Bool :=
  (List.range w).all (fun p => seFree ft p || decide (r.a p ≤ 0))
    && decide (isum (fun p => seRestoreC ft p * r.a p) w ≤ r.b)

/-- **The reference re-check**, `check_inductive_exact` (`invariant_synthesis.rs`): the
inequality holds at `M0`, no injected place has a positive weight, and every flat transition
that can fire keeps the bound or restores it from its guard. -/
def refSECheckInd : SEIndCheck := fun net envs w a0 r =>
  decide (dot r.a a0 w ≤ r.b)
    && envs.all (fun p => !decide (p < w) || decide (r.a p ≤ 0))
    && net.all (fun ft => !canFire ft.1 || seKeeps w r.a ft || seRestores w r ft)

/-! ### The refinement loop -/

/-- **The refinement of a candidate marking `m`**, cheapest first: a trap the trap search
finds; otherwise the inequality the first `invariant` query returns, kept only when the re-check
accepts it and it excludes `m`; otherwise, when that query proves there is none, the inequality
the second (relative) query returns, kept only when it excludes `m`. The error is why the phase
cannot go on. -/
def seRefine (T : SETrapFn) (X : SEIndCheck) (syn : Bool → AMarking → SESynAns) (net : FlatNet)
    (envs : List PlaceId) (w : Nat) (a0 m : AMarking) : Except SEReason SEIneq :=
  match T net w a0 m with
  | some Q => .ok (seTrapIneq Q)
  | none =>
    match syn false m with
    | .aside => .error .synthesisAside
    | .found a b =>
      if X net envs w a0 ⟨a, b, .inductive⟩ = true ∧ SEIneq.holds w ⟨a, b, .inductive⟩ m = false
      then .ok ⟨a, b, .inductive⟩ else .error .recheck
    | .none =>
      match syn true m with
      | .aside => .error .synthesisAside
      | .none => .error .noRefinement
      | .found a b =>
        if SEIneq.holds w ⟨a, b, .relative⟩ m = false then .ok ⟨a, b, .relative⟩
        else .error .recheck

/-- A refinement loop: `P net envs w a0 bad L B seq syn rs` on the flat net `net` with the
injected places `envs` and `w` places, from `M0 = a0`, for the violation `bad`, with the
refinement limit `L`, the node budget `B`, the state-equation query's answer `seq rs` over the
refinements `rs`, the `invariant` queries' answers `syn rel m` for a candidate marking `m`
(`rel` = the relative query), and the refinements `rs` added so far. -/
abbrev SEPhaseFn : Type :=
  FlatNet → List PlaceId → Nat → AMarking → (AMarking → Bool) → Nat → Nat →
    (List SEIneq → SEAns) → (Bool → AMarking → SESynAns) → List SEIneq → SEOutcome

/-- The loop over a witness search and a refinement function `R` of candidate markings, with
fuel. -/
def seLoopR (S : SESearch) (R : AMarking → Except SEReason SEIneq) (net : FlatNet)
    (envs : List PlaceId) (a0 : AMarking) (bad : AMarking → Bool) (L B : Nat)
    (seq : List SEIneq → SEAns) : Nat → List SEIneq → SEOutcome
  | 0, rs => .inconclusive .limit rs
  | fuel + 1, rs =>
    match seq rs with
    | .aside => .inconclusive .queryAside rs
    | .unsat => .proven rs
    | .sat c =>
      match S net envs a0 c.n bad B with
      | .found run => .violated run rs
      | _ =>
        if L ≤ rs.length then .inconclusive .limit rs
        else
          match R c.m with
          | .ok r => seLoopR S R net envs a0 bad L B seq fuel (rs ++ [r])
          | .error why => .inconclusive why rs

/-- The loop over given parts, with the fuel the refinement limit leaves. -/
def seLoopPhase (S : SESearch) (T : SETrapFn) (X : SEIndCheck) : SEPhaseFn :=
  fun net envs w a0 bad L B seq syn rs =>
    seLoopR S (seRefine T X syn net envs w a0) net envs a0 bad L B seq (L - rs.length + 1) rs

/-- **The reference phase**, `run_state_equation_phase` (`state_equation_phase.rs`): ask; prove
on `unsat`; on `sat`, search for a witness; stop at the refinement limit; refine and ask again. -/
def refSEPhase : SEPhaseFn := seLoopPhase refSESearch refSETrap refSECheckInd

/-! ### The hand-over -/

/-- A hand-over: from the names of the flat transitions, the phase's outcome and the answer of
the certificate check to what the step returns to the pipeline. -/
abbrev SEWrap : Type := (Nat → String) → SEOutcome → SECert → Verifier.PhaseOut

/-- The method of a `Proven` from this phase. -/
def ver018_method : String := "state-equation"

/-- **The reference hand-over** (`state_equation_decision`, `smt_verifier.rs`): a proof whose
certificate check passed, or is disabled, is `Proven` with the method `state-equation`; a failed
or inconclusive check withholds it; a run is `Violated` with the run's transitions and
`counterexampleConfirmed` `true`; stepping aside is an aside. -/
def refSEWrap : SEWrap := fun nm o c =>
  match o with
  | .proven _ =>
    match c with
    | .passed | .disabled => .decided (.proven ver018_method) [] none
    | .failed | .inconclusive => .aside "certificate check did not pass"
  | .violated run _ => .decided .violated (run.map nm) (some true)
  | .inconclusive _ _ => .aside "state-equation phase inconclusive"

/-- The invariant the certificate check of [VER-016] re-proves for a proof over the refinements
`rs`: `SE(M, n) ∧ ⋀ refinements(M)`, the row of every non-injected place below `w` and every
refinement. -/
def seCert (net : FlatNet) (envs : List PlaceId) (w : Nat) (a0 : AMarking) (rs : List SEIneq) :
    AMarking × Counters → Prop :=
  fun s => (∀ p, p < w → p ∉ envs → Libpetri.Row net a0 s.1 s.2 p) ∧ ∀ r ∈ rs, r.holds w s.1 = true

#spec_witness refSESearch
#spec_witness refSETrap
#spec_witness refSECheckInd
#spec_witness refSEPhase
#spec_witness refSEWrap

/-! ### Lemmas on the model -/

/-- Within the counts, for every transition. -/
theorem seWithin_iff {r : List Nat} {c : Counters} : SEWithin r c ↔ ∀ j, r.count j ≤ c j := by
  constructor
  · intro h j
    by_cases hj : j ∈ r
    · exact h j hj
    · rw [List.count_eq_zero_of_not_mem hj]; exact Nat.zero_le _
  · intro h j _
    exact h j

/-- A run within the counts starts with a transition whose count is positive, and goes on
within the counts that firing leaves. -/
theorem seWithin_cons {k : Nat} {r : List Nat} {c : Counters} :
    SEWithin (k :: r) c ↔ 0 < c k ∧ SEWithin r (seDec c k) := by
  simp only [seWithin_iff, List.count_cons, seDec]
  constructor
  · intro h
    have hk := h k
    simp only [beq_self_eq_true, if_true] at hk
    refine ⟨by omega, fun j => ?_⟩
    by_cases hj : j = k
    · subst hj; simp only [if_true]; omega
    · have := h j
      simp only [beq_iff_eq, Ne.symm hj, if_false, Nat.add_zero] at this
      simp only [hj, if_false]; exact this
  · rintro ⟨hk, h⟩ j
    by_cases hj : j = k
    · subst hj; have := h j; simp only [if_true] at this; simp only [beq_self_eq_true, if_true]
      omega
    · have := h j
      simp only [hj, if_false] at this
      simp only [beq_iff_eq, Ne.symm hj, if_false, Nat.add_zero]; exact this

/-- The runs a level lists are exactly the runs of that length over the transitions below `T`
within the counts. -/
theorem mem_seRuns {T : Nat} : ∀ {L : Nat} {c : Counters} {x : List Nat},
    x ∈ seRuns T L c ↔ x.length = L ∧ (∀ k ∈ x, k < T) ∧ SEWithin x c
  | 0, c, x => by
    simp only [seRuns, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, by simp, by simp [SEWithin]⟩
    · rintro ⟨h, -, -⟩; exact List.eq_nil_of_length_eq_zero h
  | L + 1, c, x => by
    simp only [seRuns, List.mem_flatMap, List.mem_range]
    constructor
    · rintro ⟨k, hk, hx⟩
      split at hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        obtain ⟨hl, hT, hw⟩ := (mem_seRuns (L := L)).mp hy
        refine ⟨by simp [hl], ?_, seWithin_cons.mpr ⟨by assumption, hw⟩⟩
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hk
        · exact hT j hj
      · simp at hx
    · rintro ⟨hl, hT, hw⟩
      match x, hl with
      | k :: y, hl =>
        obtain ⟨hck, hw'⟩ := seWithin_cons.mp hw
        refine ⟨k, hT k List.mem_cons_self, ?_⟩
        rw [if_pos hck]
        exact List.mem_map.mpr ⟨y, (mem_seRuns (L := L)).mpr ⟨by simpa using hl,
          fun j hj => hT j (List.mem_cons_of_mem _ hj), hw'⟩, rfl⟩

/-- A run that replays names transitions of the net only. -/
theorem seReplay_lt {net : FlatNet} : ∀ {a : AMarking} {run : List Nat} {a' : AMarking},
    seReplay net a run = some a' → ∀ k ∈ run, k < net.length
  | _, [], _, _ => by simp
  | a, k :: ks, a', h => by
    simp only [seReplay] at h
    cases hk : net[k]? with
    | none => simp [hk] at h
    | some ft =>
      simp only [hk] at h
      by_cases hen : enabledA a ft.1 = true
      · rw [if_pos hen] at h
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hk
          exact hlt
        · exact seReplay_lt h j hj
      · rw [if_neg hen] at h; cases h

/-- **A run that replays is a run of the abstraction**: its last marking is reachable with
injection (it injects nothing). -/
theorem seReplay_reach {net : FlatNet} {envs : List PlaceId} :
    ∀ {a : AMarking} {run : List Nat} {a' : AMarking},
      seReplay net a run = some a' → ReachAInj net envs a a'
  | a, [], a', h => by
    simp only [seReplay, Option.some.injEq] at h
    subst h; exact ReachAInj.init
  | a, k :: ks, a', h => by
    simp only [seReplay] at h
    cases hk : net[k]? with
    | none => simp [hk] at h
    | some ft =>
      simp only [hk] at h
      by_cases hen : enabledA a ft.1 = true
      · rw [if_pos hen] at h
        exact Relation.ReflTransGen.head
          (Or.inl ⟨ft, List.mem_of_getElem? hk, hen, rfl⟩) (seReplay_reach h)
      · rw [if_neg hen] at h; cases h

/-- A run that hits names transitions of the net only. -/
theorem seHits_lt {net : FlatNet} {bad : AMarking → Bool} {a0 : AMarking} {run : List Nat}
    (h : seHits net bad a0 run = true) : ∀ k ∈ run, k < net.length := by
  unfold seHits at h
  cases hr : seReplay net a0 run with
  | none => rw [hr] at h; cases h
  | some a => exact seReplay_lt hr

/-- One firing of a transition with a positive count lowers the sum of the counts by one. -/
theorem seTotal_dec {T k : Nat} {c : Counters} (hk : k < T) (hc : 0 < c k) :
    seTotal T (seDec c k) + 1 = seTotal T c := by
  unfold seTotal
  have h : ∀ j ∈ Finset.range T, c j = seDec c k j + (if j = k then 1 else 0) := by
    intro j _
    unfold seDec
    by_cases hj : j = k
    · subst hj; simp only [if_true]; omega
    · simp [hj]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp [Finset.mem_range, hk]

/-- No run within the counts is longer than the sum of the counts. -/
theorem seLen_le_total {T : Nat} : ∀ {x : List Nat} {c : Counters},
    (∀ k ∈ x, k < T) → SEWithin x c → x.length ≤ seTotal T c
  | [], _, _, _ => Nat.zero_le _
  | k :: y, c, hT, hw => by
    obtain ⟨hck, hw'⟩ := seWithin_cons.mp hw
    have h1 := seLen_le_total (c := seDec c k) (fun j hj => hT j (List.mem_cons_of_mem _ hj)) hw'
    have h2 := seTotal_dec (hT k List.mem_cons_self) hck
    simp only [List.length_cons]; omega

/-- What a scan that found a run says: the run is in its level, hits, and no shorter level of the
scan has a hit. -/
theorem seScan_some {net : FlatNet} {bad : AMarking → Bool} {a0 : AMarking} {c : Counters} :
    ∀ {n s : Nat} {r : List Nat}, seScan net bad a0 c (List.range' s n) = some r →
      r ∈ seRuns net.length r.length c ∧ seHits net bad a0 r = true ∧
        ∀ L, s ≤ L → L < r.length → ∀ x ∈ seRuns net.length L c, seHits net bad a0 x = false
  | 0, s, r, h => by simp [seScan] at h
  | n + 1, s, r, h => by
    rw [List.range'_succ] at h
    simp only [seScan] at h
    cases hf : (seRuns net.length s c).find? (seHits net bad a0) with
    | some r' =>
      rw [hf] at h
      cases h
      have hm := List.mem_of_find?_eq_some hf
      have hl := (mem_seRuns.mp hm).1
      refine ⟨by rw [hl]; exact hm, List.find?_some hf, fun L hL hL' => by omega⟩
    | none =>
      rw [hf] at h
      obtain ⟨h1, h2, h3⟩ := seScan_some h
      refine ⟨h1, h2, fun L hL hL' x hx => ?_⟩
      rcases Nat.eq_or_lt_of_le hL with rfl | hL
      · simpa using List.find?_eq_none.mp hf x hx
      · exact h3 L hL hL' x hx

/-- What a scan that found nothing says: no level of the scan has a hit. -/
theorem seScan_none {net : FlatNet} {bad : AMarking → Bool} {a0 : AMarking} {c : Counters} :
    ∀ {n s : Nat}, seScan net bad a0 c (List.range' s n) = none →
      ∀ L, s ≤ L → L < s + n → ∀ x ∈ seRuns net.length L c, seHits net bad a0 x = false
  | 0, s, _ => fun L h1 h2 => by omega
  | n + 1, s, h => by
    rw [List.range'_succ] at h
    simp only [seScan] at h
    cases hf : (seRuns net.length s c).find? (seHits net bad a0) with
    | some r' => rw [hf] at h; cases h
    | none =>
      rw [hf] at h
      intro L h1 h2 x hx
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · simpa using List.find?_eq_none.mp hf x hx
      · exact seScan_none h L h1 (by omega) x hx

/-- A run within the counts that hits lies in the level of its length. -/
theorem seHit_mem {net : FlatNet} {bad : AMarking → Bool} {a0 : AMarking} {c : Counters}
    {run : List Nat} (hw : SEWithin run c) (hh : seHits net bad a0 run = true) :
    run ∈ seRuns net.length run.length c ∧ run.length < seTotal net.length c + 1 :=
  ⟨mem_seRuns.mpr ⟨rfl, seHits_lt hh, hw⟩, Nat.lt_succ_of_le (seLen_le_total (seHits_lt hh) hw)⟩

/-- The reference search finds a run exactly when its scan does. -/
theorem refSESearch_found {net : FlatNet} {envs : List PlaceId} {a0 : AMarking} {c : Counters}
    {bad : AMarking → Bool} {B : Nat} {run : List Nat} :
    refSESearch net envs a0 c bad B = .found run ↔
      seScan net bad a0 c (List.range (seTotal net.length c + 1)) = some run := by
  unfold refSESearch
  cases seScan net bad a0 c (List.range (seTotal net.length c + 1)) with
  | some r => simp
  | none => simp only [reduceCtorEq, iff_false]; split <;> simp

/-! ### Traps -/

/-- `seGTrapB` decides `SEGTrap`. -/
theorem seGTrapB_iff {net : FlatNet} {Q : List PlaceId} : seGTrapB net Q = true ↔ SEGTrap net Q := by
  unfold seGTrapB SEGTrap
  rw [List.all_eq_true]
  refine forall_congr' fun ft => forall_congr' fun _ => ?_
  cases h1 : Q.any (seDrains ft.1) <;> cases h2 : Q.any (ft.2.contains ·) <;>
    simp_all [List.any_eq_true, List.any_eq_false]

/-- **A marked trap stays marked**, clearing arcs and injection included: a firing that can take
tokens from the trap puts one back, and a firing that cannot leaves every trap place at least as
full; an injection only adds a token. -/
theorem seGTrap_stays_marked {net : FlatNet} {envs : List PlaceId} {Q : List PlaceId}
    {a0 a : AMarking} (hT : SEGTrap net Q) (h0 : ∃ q ∈ Q, 0 < a0 q)
    (hr : ReachAInj net envs a0 a) : ∃ q ∈ Q, 0 < a q := by
  induction hr with
  | init => exact h0
  | @step a1 ft _ hmem hen ih =>
    by_cases hd : ∃ p ∈ Q, seDrains ft.1 p = true
    · obtain ⟨q, hq, hout⟩ := hT ft hmem hd
      refine ⟨q, hq, ?_⟩
      unfold fireA post
      rw [hout]
      simp only [if_true]
      split
      · omega
      · split <;> omega
    · obtain ⟨p, hp, hpos⟩ := ih
      refine ⟨p, hp, ?_⟩
      have hnd : seDrains ft.1 p = false := by
        cases h : seDrains ft.1 p with
        | false => rfl
        | true => exact absurd ⟨p, hp, h⟩ hd
      simp only [seDrains, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at hnd
      obtain ⟨⟨hpre, hca⟩, hres⟩ := hnd
      unfold fireA
      rw [if_neg (by rw [hres]; exact Bool.false_ne_true), if_neg (by rw [hca]; exact Bool.false_ne_true)]
      omega
  | @inject a1 p' _ _ ih =>
    obtain ⟨q, hq, hpos⟩ := ih
    refine ⟨q, hq, ?_⟩
    simp only
    split <;> omega

/-- The refinement of a trap holds wherever a place of the trap below `w` is marked. -/
theorem seTrapIneq_holds {w : Nat} {Q : List PlaceId} {a : AMarking} (hw : ∀ q ∈ Q, q < w)
    (h : ∃ q ∈ Q, 0 < a q) : (seTrapIneq Q).holds w a = true := by
  obtain ⟨q, hq, hpos⟩ := h
  have hqc : Q.contains q = true := by simpa using hq
  have hle : ∀ p ∈ Finset.range w,
      (seTrapIneq Q).a p * (a p : Int) ≤ (if p = q then -(a q : Int) else 0) := by
    intro p _
    by_cases hpq : p = q
    · subst hpq
      simp only [seTrapIneq, hqc, if_true]
      omega
    · simp only [seTrapIneq, if_neg hpq]
      split
      · omega
      · simp
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (hw q hq))] at hsum
  unfold SEIneq.holds
  rw [decide_eq_true_eq, Libpetri.dot_eq_isum]
  show ∑ p ∈ Finset.range w, (seTrapIneq Q).a p * (a p : Int) ≤ (seTrapIneq Q).b
  have hb : (seTrapIneq Q).b = -1 := rfl
  rw [hb]
  omega

/-- The refinement of a trap the statement accepts holds on every reachable marking. -/
theorem seTrap_holds_reach {net : FlatNet} {envs : List PlaceId} {w : Nat} {Q : List PlaceId}
    {a0 a : AMarking} (hT : SEGTrap net Q) (hw : ∀ q ∈ Q, q < w) (h0 : ∃ q ∈ Q, 0 < a0 q)
    (hr : ReachAInj net envs a0 a) : (seTrapIneq Q).holds w a = true :=
  seTrapIneq_holds hw (seGTrap_stays_marked hT h0 hr)

/-! ### Inductive inequalities -/

/-- An inductive inequality holds on every reachable marking. -/
theorem seInductive_reach {net : FlatNet} {envs : List PlaceId} {w : Nat} {a0 : AMarking}
    {r : SEIneq} (h : SEInductive net envs w a0 r) {a : AMarking} (hr : ReachAInj net envs a0 a) :
    r.holds w a = true := by
  unfold SEIneq.holds
  simp only [decide_eq_true_eq]
  have hr' : Relation.ReflTransGen (StepAInjRel net envs) a0 a := hr
  clear hr
  induction hr' with
  | refl => exact h.1
  | tail _ hs ih => exact h.2 _ _ ih hs

/-- An enabled transition finds its inhibited places empty. -/
theorem seEnabled_inh {m : AMarking} {t : Transition} (h : enabledA m t = true) {p : PlaceId}
    (hp : t.inhibitors.contains p = true) : m p = 0 := by
  unfold enabledA at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.2 p (by simpa using hp)

/-- An enabled transition finds its read places marked. -/
theorem seEnabled_read {m : AMarking} {t : Transition} (h : enabledA m t = true) {p : PlaceId}
    (hp : t.reads.contains p = true) : 1 ≤ m p := by
  unfold enabledA at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h.2 p (by simpa using hp)

/-- A cleared place holds what the firing puts there. -/
theorem seFire_cleared {m : AMarking} {t : Transition} {br : List PlaceId} {p : PlaceId}
    (h : seCleared t p = true) : fireA m t br p = post br p := by
  unfold fireA
  unfold seCleared at h
  by_cases hr : t.resets.contains p = true
  · rw [if_pos hr]
  · rw [if_neg hr]
    simp only [hr, Bool.false_or] at h
    rw [if_pos h]

/-- Any other place moves by `post − pre`. -/
theorem seFire_linear {m : AMarking} {t : Transition} {br : List PlaceId} {p : PlaceId}
    (h : seCleared t p = false) : fireA m t br p = m p - pre t p + post br p := by
  unfold fireA
  unfold seCleared at h
  simp only [Bool.or_eq_false_iff] at h
  rw [if_neg (by rw [h.1]; exact Bool.false_ne_true),
    if_neg (by rw [h.2]; exact Bool.false_ne_true)]

/-- An enabled transition finds at least `seLower` tokens on each place. -/
theorem seLower_le {m : AMarking} {t : Transition} (h : enabledA m t = true) (p : PlaceId) :
    seLower t p ≤ m p := by
  unfold seLower
  have hpre := Libpetri.pre_le_of_enabledA h p
  apply max_le (by exact_mod_cast hpre)
  split
  · have := seEnabled_read h (by assumption); exact_mod_cast this
  · positivity

/-- The `λ = 1` term: what one place adds to `a·M` is at most its keep coefficient. -/
theorem seKeep_term {m : AMarking} {ft : FlatTransition} (hen : enabledA m ft.1 = true)
    (p : PlaceId) {a : Int}
    (ha : seCleared ft.1 p = true → ft.1.inhibitors.contains p = false → 0 ≤ a) :
    a * ((fireA m ft.1 ft.2 p : Int) - m p) ≤ seKeepC ft p * a := by
  have hpre := Libpetri.pre_le_of_enabledA hen p
  unfold seKeepC
  cases hc : seCleared ft.1 p
  · rw [seFire_linear hc]
    simp only [Bool.false_eq_true, if_false]
    push_cast [Nat.cast_sub hpre]
    exact le_of_eq (by ring)
  · rw [seFire_cleared hc]
    simp only [if_true]
    cases hi : ft.1.inhibitors.contains p
    · have ha' := ha hc hi
      have hl := seLower_le hen p
      simp only [Bool.false_eq_true, if_false]
      nlinarith [mul_nonneg ha' (sub_nonneg.mpr hl)]
    · rw [seEnabled_inh hen hi]
      simp only [if_true]
      exact le_of_eq (by push_cast; ring)

/-- The `λ = 0` term: what one place holds after the firing, weighted, is at most its restore
coefficient. -/
theorem seRestore_term {m : AMarking} {ft : FlatTransition} (hen : enabledA m ft.1 = true)
    (p : PlaceId) {a : Int} (ha : seFree ft p = false → a ≤ 0) :
    a * (fireA m ft.1 ft.2 p : Int) ≤ seRestoreC ft p * a := by
  have hpre := Libpetri.pre_le_of_enabledA hen p
  unfold seRestoreC
  cases hc : seCleared ft.1 p
  · rw [seFire_linear hc]
    simp only [Bool.false_eq_true, if_false]
    cases hi : ft.1.inhibitors.contains p
    · have ha' := ha (by unfold seFree; rw [hc, hi]; rfl)
      have hl := seLower_le hen p
      simp only [Bool.false_eq_true, if_false]
      push_cast [Nat.cast_sub hpre]
      nlinarith [mul_nonneg (neg_nonneg.mpr ha') (sub_nonneg.mpr hl)]
    · have h0 := seEnabled_inh hen hi
      simp only [if_true]
      rw [h0] at hpre ⊢
      push_cast [Nat.cast_sub hpre]
      exact le_of_eq (by ring)
  · rw [seFire_cleared hc]
    simp only [if_true]
    exact le_of_eq (by ring)

/-- **The reference re-check is sound**: an inequality it accepts holds at `M0` and is kept by
every firing and every injection step of the exact step relation. -/
theorem refSECheckInd_sound {net : FlatNet} {envs : List PlaceId} {w : Nat} {a0 : AMarking}
    {r : SEIneq} (h : refSECheckInd net envs w a0 r = true) : SEInductive net envs w a0 r := by
  simp only [refSECheckInd, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨h0, henv⟩, hnet⟩ := h
  refine ⟨h0, ?_⟩
  rintro m m' hm (⟨ft, hmem, hen, rfl⟩ | ⟨p, hp, rfl⟩)
  · have hft := hnet ft hmem
    have hcf : canFire ft.1 = true := by
      cases hc : canFire ft.1 with
      | true => rfl
      | false => rw [not_canFire_never_enabled hc m] at hen; cases hen
    simp only [hcf, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hft
    rw [Libpetri.dot_eq_isum] at hm ⊢
    rcases hft with hk | hrs
    · simp only [seKeeps, Bool.and_eq_true, List.all_eq_true, List.mem_range,
        decide_eq_true_eq] at hk
      obtain ⟨hnn, hsum⟩ := hk
      have hsplit : isum (fun p => r.a p * (fireA m ft.1 ft.2 p : Int)) w =
          isum (fun p => r.a p * (m p : Int)) w +
            isum (fun p => r.a p * ((fireA m ft.1 ft.2 p : Int) - m p)) w := by
        rw [← Libpetri.isum_add]
        exact Libpetri.isum_congr fun p _ => by ring
      have hle : isum (fun p => r.a p * ((fireA m ft.1 ft.2 p : Int) - m p)) w ≤
          isum (fun p => seKeepC ft p * r.a p) w := by
        unfold isum
        refine Finset.sum_le_sum fun p hp => seKeep_term hen p fun hc hi => ?_
        have := hnn p (Finset.mem_range.mp hp)
        rw [hc, hi] at this
        simpa using this
      linarith
    · simp only [seRestores, Bool.and_eq_true, List.all_eq_true, List.mem_range,
        decide_eq_true_eq] at hrs
      obtain ⟨hsg, hsum⟩ := hrs
      have hle : isum (fun p => r.a p * (fireA m ft.1 ft.2 p : Int)) w ≤
          isum (fun p => seRestoreC ft p * r.a p) w := by
        unfold isum
        refine Finset.sum_le_sum fun p hp => seRestore_term hen p fun hf => ?_
        have := hsg p (Finset.mem_range.mp hp)
        rw [hf] at this
        simpa using this
      linarith
  · rw [Libpetri.dot_eq_isum] at hm ⊢
    have hle : isum (fun q => r.a q * (((fun q => if (q == p) = true then m q + 1 else m q) q : Nat)
          : Int)) w ≤ isum (fun q => r.a q * (m q : Int)) w := by
      unfold isum
      refine Finset.sum_le_sum fun q hq => ?_
      by_cases hqp : q = p
      · subst hqp
        have := henv q hp
        simp only [Finset.mem_range.mp hq, decide_true, Bool.not_true, Bool.false_or,
          decide_eq_true_eq] at this
        simp only [beq_self_eq_true, if_true]
        push_cast
        nlinarith
      · simp [hqp]
    linarith

/-! ### The loop over given parts -/

section Loop

variable (S : SESearch) (T : SETrapFn) (X : SEIndCheck) {net : FlatNet} {envs : List PlaceId}
  {w : Nat} {a0 : AMarking} {bad : AMarking → Bool} {L B : Nat} {seq : List SEIneq → SEAns}
  {syn : Bool → AMarking → SESynAns} {rs : List SEIneq}

/-- The loop steps aside on an unanswered query. -/
theorem seLoopPhase_aside (h : seq rs = .aside) :
    seLoopPhase S T X net envs w a0 bad L B seq syn rs = .inconclusive .queryAside rs := by
  simp [seLoopPhase, seLoopR, h]

/-- The loop proves on `unsat`. -/
theorem seLoopPhase_unsat (h : seq rs = .unsat) :
    seLoopPhase S T X net envs w a0 bad L B seq syn rs = .proven rs := by
  simp [seLoopPhase, seLoopR, h]

/-- The loop reports the run the search finds. -/
theorem seLoopPhase_found {c : SECand} {run : List Nat} (h : seq rs = .sat c)
    (hs : S net envs a0 c.n bad B = .found run) :
    seLoopPhase S T X net envs w a0 bad L B seq syn rs = .violated run rs := by
  simp [seLoopPhase, seLoopR, h, hs]

/-- The loop stops at the refinement limit. -/
theorem seLoopPhase_limit {c : SECand} (h : seq rs = .sat c)
    (hs : ∀ run, S net envs a0 c.n bad B ≠ .found run) (hL : L ≤ rs.length) :
    seLoopPhase S T X net envs w a0 bad L B seq syn rs = .inconclusive .limit rs := by
  simp only [seLoopPhase, seLoopR, h]
  cases hS : S net envs a0 c.n bad B with
  | found run => exact absurd hS (hs run)
  | none => simp [hL]
  | exhausted => simp [hL]

/-- The loop adds a refinement and asks again. -/
theorem seLoopPhase_refine {c : SECand} {r : SEIneq} (h : seq rs = .sat c)
    (hs : ∀ run, S net envs a0 c.n bad B ≠ .found run) (hL : rs.length < L)
    (hr : seRefine T X syn net envs w a0 c.m = .ok r) :
    seLoopPhase S T X net envs w a0 bad L B seq syn rs =
      seLoopPhase S T X net envs w a0 bad L B seq syn (rs ++ [r]) := by
  unfold seLoopPhase
  have hfuel : L - (rs ++ [r]).length + 1 = L - rs.length := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [hfuel]
  simp only [seLoopR, h]
  cases hS : S net envs a0 c.n bad B with
  | found run => exact absurd hS (hs run)
  | none => simp [Nat.not_le.mpr hL, hr]
  | exhausted => simp [Nat.not_le.mpr hL, hr]

/-- The loop steps aside when no refinement settles the candidate. -/
theorem seLoopPhase_error {c : SECand} {why : SEReason} (h : seq rs = .sat c)
    (hs : ∀ run, S net envs a0 c.n bad B ≠ .found run) (hL : rs.length < L)
    (hr : seRefine T X syn net envs w a0 c.m = .error why) :
    seLoopPhase S T X net envs w a0 bad L B seq syn rs = .inconclusive why rs := by
  simp only [seLoopPhase, seLoopR, h]
  cases hS : S net envs a0 c.n bad B with
  | found run => exact absurd hS (hs run)
  | none => simp [Nat.not_le.mpr hL, hr]
  | exhausted => simp [Nat.not_le.mpr hL, hr]

end Loop

/-! ## VER-018: State-equation phase with refinement -/

requirement VER_018
  id "VER-018"
  title "State-Equation Phase with Refinement"
  kind B
  scope "the SMT verifier's state-equation phase on the flat path, all implementations"
  source verbatim "spec/07-verification.md"
  covers VER_018.s1, VER_018.s2, VER_018.s3, VER_018.s4, VER_018.s5, VER_018.s6, VER_018.s7,
        VER_018.s8, VER_018.s9, VER_018.s10, VER_018.s11, VER_018.s12, VER_018.s13, VER_018.s14,
        VER_018.s15, VER_018.s16, VER_018.s20, VER_018.s21, VER_018.s22, VER_018.s17, VER_018.s18,
        VER_018.s19
  reading "A run the witness search S reports fires each flat transition k at most c k times (SEWithin) and replays from M0 under enabledA and fireA, with no injection step, to a marking the violation bad accepts (seHits)."
          "A run S reports is no longer than any run within the counts that replays to a violating marking."
          "S reports none (a completed search that found nothing) only when no place is injected and no run within the counts replays to a violating marking."
          "S reports a run on a net with injected places exactly when it reports that run on the same net with no injected place."
          "When some run within the counts replays to a violating marking, there is a node budget from which on S reports a run."
          "A set Q the trap search T returns is a trap with clearing arcs (SEGTrap: every flat transition that can take a token from Q, by a positive requirement, a consume-all input or a reset arc, puts a token into Q), its places lie below the place count w, some place of Q is marked in M0, and the candidate marking leaves every place of Q empty."
          "When T returns nothing, every trap with clearing arcs among the places below w that the candidate leaves empty is empty in M0."
          "An inequality the re-check X accepts is inductive (SEInductive): it holds at M0 and every firing of an enabled flat transition and every injection keeps it."
          "When the state-equation query over the refinements rs gets no sat or unsat answer, the phase P ends inconclusive (queryAside) with rs."
          "When it answers unsat, P ends with the proof over rs."
          "When it answers sat with the candidate c and S reports a run within c's counts, P ends Violated with that run and rs."
          "When it answers sat with c, S reports no run, and rs holds the refinement limit L or more, P ends inconclusive (limit) with rs."
          "When it answers sat with c, S reports no run, rs holds fewer than L refinements, and the refinement of c's marking (seRefine: the trap of T; otherwise the inductive inequality of the first invariant query when X accepts it and c violates it; otherwise, after unsat, the relative inequality of the second query when c violates it) is r, P over rs is P over rs followed by r."
          "In the same case, when the refinement of c's marking fails with a reason, P ends inconclusive with that reason and rs."
          "The hand-over W turns a proof into the decision Proven with the method state-equation, an empty trace and no counterexampleConfirmed, when the certificate check passed or is disabled."
          "W returns an aside exactly for an inconclusive outcome and for a proof whose certificate check failed or was inconclusive."
          "W turns a run into the decision Violated whose trace is the run's transitions, by name, in firing order, with counterexampleConfirmed true."
          "X accepts every inequality the reference re-check refSECheckInd accepts: one that holds at M0, gives no injected place below w a positive weight, and for which every flat transition that can fire (canFire) passes, from the least marking its guard allows (seLower), the keep test seKeeps or the restore test seRestores."
  assumes "The model is the quintuple (S, T, X, P, W) of SESearch, SETrapFn, SEIndCheck, SEPhaseFn and SEWrap over the untimed abstraction of VER-004 with injection: a flat net (FlatNet, the abstract semantics enabledA and fireA, posts read as sets: post puts one token in each place a row lists), its injected places envs, its place count w and M0. So the model covers rows that deposit at most one token per place. VER-016 reads deposits by count (CntRows, fireAD, cntCol) and agrees with the set reading on such rows (VER_016_unit_rows); a row that deposits two tokens in one place (the timeout forward of an exactly(2) input, Novel/ForwardDeposit.lean), which flatten builds and the phase reads, is outside this model. The violation is a Boolean predicate on markings (the error rule of VER-001 as violation_predicate reads it, with the relax-env quiescence of VER-006 under injection); which markings violate is VER-002's and VER-006's subject. The solver is not modelled: the answers of the state-equation query (SEAns, per list of refinements) and of the two invariant queries (SESynAns, per candidate marking) are inputs of P, so every line holds whatever the solver answers. The witness is refSESearch, refSETrap, refSECheckInd, refSEPhase and refSEWrap."
          "The environment mode is AlwaysAvailable: the Bounded(k) caps that prune a firing in the witness search and add conjuncts to the scripts only remove steps (VER-006) and are not modelled. A name-alignment property (NU-055) is refused by the phase before any query; that refusal is NU-055's line."
          "The first quoted sentence is line 10. 'A proof' is the outcome proven with the refinements; what the verifier returns for it is the hand-over, lines 15 and 16. That the bare unsat is a proof when the solver is right is VER_018_unsat_sound, from the statement alone: every reachable marking satisfies the equation for the counts of its run (rows_hold, counters_exist of VER-016) and every trap and inductive refinement holds on it (VER_018_refinements_hold); a relative refinement needs its premise, since only the certificate check re-proves it."
          "The second quoted sentence is line 9: a transport failure, unknown, a model that cannot be decoded and a timeout are one answer each in SEAns.aside (the phase's budget is the verifier's timeout, and each query gets what is left of it). 'The pipeline shall continue' is the hand-over (line 16: an inconclusive outcome is an aside) with VER_018_order and runPipeline, where an aside goes on to the next step. That the pipeline's state-equation step runs W over P is the wiring VER_018_order assumes and does not yet state (open item, carried there), so the 'pipeline continues' parts of this block reach runPipeline only through that wiring."
          "The third quoted sentence is line 11: the search runs on every sat candidate, and a run it reports ends the phase before seRefine is consulted (VER_018_forbids_noWitness)."
          "The fourth quoted sentence is line 1. The fifth is line 2: the run a search reports is a shortest one; how the search finds it (the runtimes' breadth-first search over markings and unspent counts, which the Witness paragraph names as motivation), the order among runs of one length (flat order in the runtimes) and the deduplication by marking and unspent counts are not pinned. The sixth is line 3. The seventh is line 4: 'still run' is that a run found without injection is found with it, which a search that skips injected nets breaks (VER_018_forbids_searchSkipsInj). The eighth is line 5: the node budget is a parameter of S, and the line states that some budget suffices, as the runtimes' breadth-first search over (marking, unspent counts) does once the budget exceeds those finitely many nodes; the reference search needs no budget. At the shipped budget (the twenty-first quoted sentence) nothing requires the search to report a run that exists, so AC3 holds within the node budget. A run the search misses leaves the candidate to refinement, and no false Proven follows: the run's last marking is reachable, so it satisfies the equation and every trap and inductive refinement (VER_018_refinements_hold), and it stays a solution of every later query while the relative refinements hold."
          "The ninth quoted sentence is line 6 ('places of the flat net' is that every place of Q lies below w) and the tenth is line 7. They state what a trap is and that one is found when it exists; which trap the search returns (the runtimes shrink the largest trap inside the empty places to a locally minimal one, the reference returns the first subset in order) changes the refinement text, not a verdict, and is not pinned. That a trap with clearing arcs stays marked on every reachable marking, injection included, is seGTrap_stays_marked; the plain trap of Commoner (input arcs only) does not, and a trap search that ignores reset and consume-all arcs breaks line 6 (VER_018_forbids_trapNoClearing)."
          "The eleventh quoted sentence is line 8. 'Exact integer arithmetic' is Lean's Int. The reference re-check refSECheckInd is the runtimes' check_inductive_exact (every flat transition that can fire keeps the bound or restores it from its guard, injected places weigh at most 0), and refSECheckInd_sound proves it sound; the Farkas query that proposes the inequality, its multipliers in {0, 1} and the least-magnitude objective are script text (VER-013) and not modelled."
          "The twelfth quoted sentence is line 18: X accepts every inequality the reference re-check accepts. 'A flat transition that can fire' is canFire (a transition that inhibits a place it needs never fires); 'the least marking its guard allows' is seLower (each place at its input requirement, at least 1 when it is read, 0 when it is inhibited); the keep test is seKeeps over the coefficients seKeepC and the restore test is seRestores over seRestoreC. Lines 8 and 18 together pin X between the inductive inequalities and the reference: a re-check without the restore test (the textbook Farkas check with the multiplier 1 only) rejects hasdata <= ready0 + ready1 on the join of AC2, so the join would end inconclusive, and breaks line 18 (VER_018_forbids_recheckKeepOnly). Java's BigInteger and TypeScript's bigint are exact; Rust computes in checked 128-bit arithmetic and rejects on an overflow, which needs M0 to hold 2^63 tokens or more in total or weights beyond the weight bound of the twenty-second quoted sentence, and is not modelled."
          "The thirteenth quoted sentence is lines 13 and 14 through seRefine, the fixed function the lines name: trap first, then the inductive query, then the relative query; the inductive inequality is kept only when X accepts it and it excludes the candidate, the relative one only when it excludes the candidate. 'Marked inductive' and 'marked relative' are the origins seRefine gives, which the report prints as the refinement's origin (AC2). A phase that skips the trap search, or labels a relative inequality inductive (so that it is used without the equation), breaks line 13 (VER_018_forbids_noTrap, VER_018_forbids_relativeAsInductive). The fourteenth quoted sentence is line 13 itself: P over rs is P over rs with r appended, so the state-equation query is asked again over every refinement. The fifteenth is line 14: a transport failure, unknown, a model that cannot be decoded and a timeout of an invariant query are one answer each in SESynAns.aside, which seRefine turns into the reason synthesisAside."
          "The sixteenth quoted sentence is line 12. The order is the runtimes': the witness search runs before the limit is tested, so a candidate at the limit can still be violated, and the query after the last refinement can still prove (the limit is tested after a sat candidate). That the outcome carries at most L refinements is VER_018_limit, from the statement alone. The limit is a parameter of P. The twentieth to twenty-second quoted sentences are configuration (kind N, ruling D45): the refinement limit 32 is the constant ver018_refinementLimit, the node budget 100 000 the constant ver018_nodeBudget (a parameter of S, line 5), and the weight bound max(8, tokens of M0) the function ver018_weightBound, all pinned below. No line of the statement checks the three: L and B are parameters of P and S, and the weight bound limits the invariant queries' search space and is script text (VER-013), so the model's solver answers range over every weight."
          "The seventeenth quoted sentence is lines 15 and 16 (ruling D52 (a)): a passed check gives the decision Proven (line 15), and a failed or inconclusive one an aside (line 16), so while the check is enabled a Proven comes from a passed check and from nothing else. 'Neither a counterexample nor counterexampleConfirmed' is the empty trace and the absent flag of line 15, as the result record of VER-003 has them where no replay applies and as VER-019's hand-over has them for its own Proven. The certificate check is not modelled; its answer is an input of W. That a passed check makes the proof sound is VER_018_proven_sound, from the statement alone, under the premise that the check is right (a passed check means the three verification conditions of Novel.Certificate.VCs hold against the raw counter step StepCntRel from (M0, 0) for seCert, the invariant SE(M, n) and the refinements); it rests on vc_sound_state_equation. That a decided Proven comes only from a proof with the check passed or disabled is VER_018_proven_needs_check. The eighteenth quoted sentence is line 15 for the disabled check, with the same empty trace and absent flag; its report line is text (kind Q), the constant ver018_certDisabledLine pinned below; with the check disabled a relative refinement is re-proved by nothing, and the proof rests on the solver alone."
          "The nineteenth quoted sentence is line 17 for the transitions: the trace of a decision is the run's transitions by name, as VER-019's pipeline block has it. The markings of the run, which the result also carries as its counterexample trace in replay order (Rust witness_result, smt_verifier.rs), are not a field of the decision PhaseOut, so no line checks them; they are the replay of those transitions (seReplay), whose last marking VER_018_violated_sound gives. That the result carries them is an open item for the result model of VER-019's pipeline block. That a reported run is a run of the abstraction to a violating marking, so a genuine violation is reported only for a replayed run, is VER_018_violated_sound, from the statement alone."
          "The body's motivation (the equation ignores firing order; the join's skip transition as the typical spurious candidate; the CAV 2014 and CAV 2003 references; the Farkas dual of the final unsat is not used; that every trap and inductive refinement holds in every reachable marking, which is VER_018_refinements_hold, and a relative one when the solver's answer is right, which is the premise of VER_018_unsat_sound), the 'Where it runs' paragraph and the measurements are not lines of this block. The paragraph is VER_018_order. The equation and the violation of the query are VER-016's rows and VER-001's error rule, inputs here through the solver's answers. 'Unlike VER-015 the query asks for the violation directly, so it covers every property' is the shape of the script (VER-013)."
          "AC1 (a property the equation excludes is Proven with method state-equation without a fixpoint query, with the PASSED certificate line) is lines 10 and 15: an unsat answer gives the proof, the hand-over returns a decision, which ends the run before the fixpoint query (VER_018_order). The report line is the constant ver018_certPassedLine, pinned below. VER_018_nonvacuous proves the ring t0: p0 to p1, t1: p1 to p0 after one trap refinement."
          "AC2 (the join-with-skip net proven with the refinement hasdata <= ready0 + ready1, listed as the result's discovered invariants) is VER_018_join_refinement: the reference re-check accepts that inequality on the join's flat net and it excludes the candidate that skips after the data arrived. The report line and the discovered-invariants list are text (kind Q), the function ver018_refinementLine pinned below; that the solver returns that inequality is not modelled."
          "AC3 (a candidate a run within its counts realises is reported violated, with that run confirmed) is lines 5, 11 and 17, within the node budget (see the eighth quoted sentence); VER_018_nonvacuous replays the run produce, produce, produce, cancel on the queue-and-bundle net with cancel."
          "AC4 (the phase's Proven is withheld unless the certificate check passes, while the check is enabled; Violated only for a replayed run) is line 16 with VER_018_proven_needs_check, and line 1 with VER_018_violated_sound."
          "AC5 (with the phase disabled, verdicts and reports are those of the pipeline without it) is VER_018_order line 4 with VER_018_order_disabled."
          "AC6 (LIBPETRI_SMT_DUMP records the scripts under the phases state-equation and invariant) and AC7 (the first query is exposed with the encoded scripts and pinned as a golden of VER-013 AC1) are about script text and its dump names (kind Q), checked by the dump and golden-script tests of VER-013; the phase names are the constants ver018_dumpPhases, pinned below."
          "The Implementation notes name the per-language option and modules (kind N). The Naming bullet's SHOULD, that an implementation cross-reference stateEquationPhase and the stateEquation option of VER-016 wherever it documents either, is about documentation text (kind N), and no line checks it. The test derivation is AC2 and AC3 on the join and queue nets under the options it names (the enumeration budget of VER-017 at 0 and assumeAtomicFiring), which the pipeline sets outside the model."
  signoff "2026-11-13 142e63675d5af03a ai"
  statement : SESearch → SETrapFn → SEIndCheck → SEPhaseFn → SEWrap → Prop :=
    fun S T X P W =>
      (∀ net envs a0 c bad B run, S net envs a0 c bad B = .found run →
        SEWithin run c ∧ seHits net bad a0 run = true) ∧
      (∀ net envs a0 c bad B run run', S net envs a0 c bad B = .found run →
        SEWithin run' c → seHits net bad a0 run' = true → run.length ≤ run'.length) ∧
      (∀ net envs a0 c bad B, S net envs a0 c bad B = .none →
        envs = [] ∧ ∀ run, SEWithin run c → seHits net bad a0 run = false) ∧
      (∀ net envs a0 c bad B run,
        S net envs a0 c bad B = .found run ↔ S net [] a0 c bad B = .found run) ∧
      (∀ net envs a0 c bad, (∃ run, SEWithin run c ∧ seHits net bad a0 run = true) →
        ∃ B0, ∀ B, B0 ≤ B → ∃ run, S net envs a0 c bad B = .found run) ∧
      (∀ net w a0 m Q, T net w a0 m = some Q →
        SEGTrap net Q ∧ (∀ q ∈ Q, q < w) ∧ (∃ q ∈ Q, 0 < a0 q) ∧ ∀ q ∈ Q, m q = 0) ∧
      (∀ net w a0 m, T net w a0 m = none → ∀ Q, (∀ q ∈ Q, q < w) → SEGTrap net Q →
        (∀ q ∈ Q, m q = 0) → ∀ q ∈ Q, a0 q = 0) ∧
      (∀ net envs w a0 r, X net envs w a0 r = true → SEInductive net envs w a0 r) ∧
      (∀ net envs w a0 bad L B seq syn rs, seq rs = .aside →
        P net envs w a0 bad L B seq syn rs = .inconclusive .queryAside rs) ∧
      (∀ net envs w a0 bad L B seq syn rs, seq rs = .unsat →
        P net envs w a0 bad L B seq syn rs = .proven rs) ∧
      (∀ net envs w a0 bad L B seq syn rs c run, seq rs = .sat c →
        S net envs a0 c.n bad B = .found run →
        P net envs w a0 bad L B seq syn rs = .violated run rs) ∧
      (∀ net envs w a0 bad L B seq syn rs c, seq rs = .sat c →
        (∀ run, S net envs a0 c.n bad B ≠ .found run) → L ≤ rs.length →
        P net envs w a0 bad L B seq syn rs = .inconclusive .limit rs) ∧
      (∀ net envs w a0 bad L B seq syn rs c r, seq rs = .sat c →
        (∀ run, S net envs a0 c.n bad B ≠ .found run) → rs.length < L →
        seRefine T X syn net envs w a0 c.m = .ok r →
        P net envs w a0 bad L B seq syn rs = P net envs w a0 bad L B seq syn (rs ++ [r])) ∧
      (∀ net envs w a0 bad L B seq syn rs c why, seq rs = .sat c →
        (∀ run, S net envs a0 c.n bad B ≠ .found run) → rs.length < L →
        seRefine T X syn net envs w a0 c.m = .error why →
        P net envs w a0 bad L B seq syn rs = .inconclusive why rs) ∧
      (∀ nm rs c, (c = .passed ∨ c = .disabled) →
        W nm (.proven rs) c = .decided (.proven ver018_method) [] none) ∧
      (∀ nm o c, (∃ n, W nm o c = .aside n) ↔
        (o.isInconclusive = true ∨ (o.isProven = true ∧ (c = .failed ∨ c = .inconclusive)))) ∧
      (∀ nm run rs c, W nm (.violated run rs) c = .decided .violated (run.map nm) (some true)) ∧
      (∀ net envs w a0 r, refSECheckInd net envs w a0 r = true → X net envs w a0 r = true)

/- The pinned readable form of VER-018: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_018 : SESearch → SETrapFn → SEIndCheck → SEPhaseFn → SEWrap → Prop :=
fun S T X P W =>
  (∀ (net : FlatNet) (envs : List PlaceId) (a0 : AMarking) (c : Counters) (bad : AMarking → Bool) (B : ℕ)
      (run : List ℕ), S net envs a0 c bad B = SESearchOut.found run → SEWithin run c ∧ seHits net bad a0 run = true) ∧
    (∀ (net : FlatNet) (envs : List PlaceId) (a0 : AMarking) (c : Counters) (bad : AMarking → Bool) (B : ℕ)
        (run run' : List ℕ),
        S net envs a0 c bad B = SESearchOut.found run →
          SEWithin run' c → seHits net bad a0 run' = true → run.length ≤ run'.length) ∧
      (∀ (net : FlatNet) (envs : List PlaceId) (a0 : AMarking) (c : Counters) (bad : AMarking → Bool) (B : ℕ),
          S net envs a0 c bad B = SESearchOut.none →
            envs = [] ∧ ∀ (run : List ℕ), SEWithin run c → seHits net bad a0 run = false) ∧
        (∀ (net : FlatNet) (envs : List PlaceId) (a0 : AMarking) (c : Counters) (bad : AMarking → Bool) (B : ℕ)
            (run : List ℕ),
            S net envs a0 c bad B = SESearchOut.found run ↔ S net [] a0 c bad B = SESearchOut.found run) ∧
          (∀ (net : FlatNet) (envs : List PlaceId) (a0 : AMarking) (c : Counters) (bad : AMarking → Bool),
              (∃ run, SEWithin run c ∧ seHits net bad a0 run = true) →
                ∃ B0, ∀ (B : ℕ), B0 ≤ B → ∃ run, S net envs a0 c bad B = SESearchOut.found run) ∧
            (∀ (net : FlatNet) (w : ℕ) (a0 m : AMarking) (Q : List PlaceId),
                T net w a0 m = some Q → SEGTrap net Q ∧ (∀ q ∈ Q, q < w) ∧ (∃ q ∈ Q, 0 < a0 q) ∧ ∀ q ∈ Q, m q = 0) ∧
              (∀ (net : FlatNet) (w : ℕ) (a0 m : AMarking),
                  T net w a0 m = none →
                    ∀ (Q : List PlaceId), (∀ q ∈ Q, q < w) → SEGTrap net Q → (∀ q ∈ Q, m q = 0) → ∀ q ∈ Q, a0 q = 0) ∧
                (∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (r : SEIneq),
                    X net envs w a0 r = true → SEInductive net envs w a0 r) ∧
                  (∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (bad : AMarking → Bool) (L B : ℕ)
                      (seq : List SEIneq → SEAns) (syn : Bool → AMarking → SESynAns) (rs : List SEIneq),
                      seq rs = SEAns.aside →
                        P net envs w a0 bad L B seq syn rs = SEOutcome.inconclusive SEReason.queryAside rs) ∧
                    (∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (bad : AMarking → Bool) (L B : ℕ)
                        (seq : List SEIneq → SEAns) (syn : Bool → AMarking → SESynAns) (rs : List SEIneq),
                        seq rs = SEAns.unsat → P net envs w a0 bad L B seq syn rs = SEOutcome.proven rs) ∧
                      (∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (bad : AMarking → Bool) (L B : ℕ)
                          (seq : List SEIneq → SEAns) (syn : Bool → AMarking → SESynAns) (rs : List SEIneq) (c : SECand)
                          (run : List ℕ),
                          seq rs = SEAns.sat c →
                            S net envs a0 c.n bad B = SESearchOut.found run →
                              P net envs w a0 bad L B seq syn rs = SEOutcome.violated run rs) ∧
                        (∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (bad : AMarking → Bool)
                            (L B : ℕ) (seq : List SEIneq → SEAns) (syn : Bool → AMarking → SESynAns) (rs : List SEIneq)
                            (c : SECand),
                            seq rs = SEAns.sat c →
                              (∀ (run : List ℕ), S net envs a0 c.n bad B ≠ SESearchOut.found run) →
                                L ≤ rs.length →
                                  P net envs w a0 bad L B seq syn rs = SEOutcome.inconclusive SEReason.limit rs) ∧
                          (∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (bad : AMarking → Bool)
                              (L B : ℕ) (seq : List SEIneq → SEAns) (syn : Bool → AMarking → SESynAns)
                              (rs : List SEIneq) (c : SECand) (r : SEIneq),
                              seq rs = SEAns.sat c →
                                (∀ (run : List ℕ), S net envs a0 c.n bad B ≠ SESearchOut.found run) →
                                  rs.length < L →
                                    seRefine T X syn net envs w a0 c.m = Except.ok r →
                                      P net envs w a0 bad L B seq syn rs =
                                        P net envs w a0 bad L B seq syn (rs ++ [r])) ∧
                            (∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (bad : AMarking → Bool)
                                (L B : ℕ) (seq : List SEIneq → SEAns) (syn : Bool → AMarking → SESynAns)
                                (rs : List SEIneq) (c : SECand) (why : SEReason),
                                seq rs = SEAns.sat c →
                                  (∀ (run : List ℕ), S net envs a0 c.n bad B ≠ SESearchOut.found run) →
                                    rs.length < L →
                                      seRefine T X syn net envs w a0 c.m = Except.error why →
                                        P net envs w a0 bad L B seq syn rs = SEOutcome.inconclusive why rs) ∧
                              (∀ (nm : ℕ → String) (rs : List SEIneq) (c : SECert),
                                  c = SECert.passed ∨ c = SECert.disabled →
                                    W nm (SEOutcome.proven rs) c =
                                      Verifier.PhaseOut.decided (Verifier.Verdict.proven ver018_method) [] none) ∧
                                (∀ (nm : ℕ → String) (o : SEOutcome) (c : SECert),
                                    (∃ n, W nm o c = Verifier.PhaseOut.aside n) ↔
                                      o.isInconclusive = true ∨
                                        o.isProven = true ∧ (c = SECert.failed ∨ c = SECert.inconclusive)) ∧
                                  (∀ (nm : ℕ → String) (run : List ℕ) (rs : List SEIneq) (c : SECert),
                                      W nm (SEOutcome.violated run rs) c =
                                        Verifier.PhaseOut.decided Verifier.Verdict.violated (List.map nm run)
                                          (some true)) ∧
                                    ∀ (net : FlatNet) (envs : List PlaceId) (w : ℕ) (a0 : AMarking) (r : SEIneq),
                                      refSECheckInd net envs w a0 r = true → X net envs w a0 r = true
-/
#guard_msgs in #print VER_018

/-! ### The reference -/

/-- The reference search meets lines 1 to 5. -/
theorem ver018_refSearch_lines :
    (∀ net envs a0 c bad B run, refSESearch net envs a0 c bad B = .found run →
      SEWithin run c ∧ seHits net bad a0 run = true) ∧
    (∀ net envs a0 c bad B run run', refSESearch net envs a0 c bad B = .found run →
      SEWithin run' c → seHits net bad a0 run' = true → run.length ≤ run'.length) ∧
    (∀ net envs a0 c bad B, refSESearch net envs a0 c bad B = .none →
      envs = [] ∧ ∀ run, SEWithin run c → seHits net bad a0 run = false) ∧
    (∀ net envs a0 c bad B run,
      refSESearch net envs a0 c bad B = .found run ↔ refSESearch net [] a0 c bad B = .found run) ∧
    (∀ net envs a0 c bad, (∃ run, SEWithin run c ∧ seHits net bad a0 run = true) →
      ∃ B0, ∀ B, B0 ≤ B → ∃ run, refSESearch net envs a0 c bad B = .found run) := by
  refine ⟨fun net envs a0 c bad B run h => ?_, fun net envs a0 c bad B run run' h hw hh => ?_,
    fun net envs a0 c bad B h => ?_, fun net envs a0 c bad B run => ?_,
    fun net envs a0 c bad ⟨run, hw, hh⟩ => ⟨0, fun B _ => ?_⟩⟩
  · rw [refSESearch_found, List.range_eq_range'] at h
    obtain ⟨hm, hh, -⟩ := seScan_some h
    exact ⟨(mem_seRuns.mp hm).2.2, hh⟩
  · rw [refSESearch_found, List.range_eq_range'] at h
    obtain ⟨-, -, h3⟩ := seScan_some h
    obtain ⟨hm, hlt⟩ := seHit_mem hw hh
    by_contra hcon
    have := h3 run'.length (Nat.zero_le _) (by omega) run' hm
    rw [hh] at this; cases this
  · unfold refSESearch at h
    cases hs : seScan net bad a0 c (List.range (seTotal net.length c + 1)) with
    | some r => rw [hs] at h; cases h
    | none =>
      rw [hs] at h
      refine ⟨?_, fun run hw => ?_⟩
      · cases envs with
        | nil => rfl
        | cons _ _ => simp at h
      · cases hh : seHits net bad a0 run with
        | false => rfl
        | true =>
          rw [List.range_eq_range'] at hs
          obtain ⟨hm, hlt⟩ := seHit_mem hw hh
          have := seScan_none hs run.length (Nat.zero_le _) (by omega) run hm
          rw [hh] at this; cases this
  · rw [refSESearch_found, refSESearch_found]
  · cases hs : seScan net bad a0 c (List.range (seTotal net.length c + 1)) with
    | some r => exact ⟨r, refSESearch_found.mpr hs⟩
    | none =>
      rw [List.range_eq_range'] at hs
      obtain ⟨hm, hlt⟩ := seHit_mem hw hh
      have := seScan_none hs run.length (Nat.zero_le _) (by omega) run hm
      rw [hh] at this; cases this

/-- The reference trap search meets lines 6 and 7. -/
theorem ver018_refTrap_lines :
    (∀ net w a0 m Q, refSETrap net w a0 m = some Q →
      SEGTrap net Q ∧ (∀ q ∈ Q, q < w) ∧ (∃ q ∈ Q, 0 < a0 q) ∧ ∀ q ∈ Q, m q = 0) ∧
    (∀ net w a0 m, refSETrap net w a0 m = none → ∀ Q, (∀ q ∈ Q, q < w) → SEGTrap net Q →
      (∀ q ∈ Q, m q = 0) → ∀ q ∈ Q, a0 q = 0) := by
  refine ⟨fun net w a0 m Q h => ?_, fun net w a0 m h Q hw hT hm q hq => ?_⟩
  · have hok := List.find?_some h
    have hsub := List.mem_sublists.mp (List.mem_of_find?_eq_some h)
    simp only [seTrapOk, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq,
      List.all_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hT, hmark⟩, hempty⟩ := hok
    exact ⟨seGTrapB_iff.mp hT, fun q hq => List.mem_range.mp (hsub.subset hq), hmark, hempty⟩
  · by_contra hne
    have hpos : 0 < a0 q := Nat.pos_of_ne_zero hne
    let Q' := (List.range w).filter (fun p => Q.contains p)
    have hmem : ∀ p, p ∈ Q' ↔ p ∈ Q := by
      intro p
      simp only [Q', List.mem_filter, List.mem_range, List.contains_iff_mem]
      exact ⟨fun h => h.2, fun h => ⟨hw p h, h⟩⟩
    have hT' : SEGTrap net Q' := by
      intro ft hft ⟨p, hp, hd⟩
      obtain ⟨q', hq', ho⟩ := hT ft hft ⟨p, (hmem p).mp hp, hd⟩
      exact ⟨q', (hmem q').mpr hq', ho⟩
    have hok : seTrapOk net a0 m Q' = true := by
      simp only [seTrapOk, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq,
        List.all_eq_true, beq_iff_eq]
      exact ⟨⟨seGTrapB_iff.mpr hT', q, (hmem q).mpr hq, hpos⟩,
        fun p hp => hm p ((hmem p).mp hp)⟩
    have hnone := List.find?_eq_none.mp h Q' (List.mem_sublists.mpr List.filter_sublist)
    exact hnone hok

/-- The reference hand-over steps aside exactly on stepping aside and on a proof whose check did
not pass. -/
theorem ver018_refWrap_aside (nm : Nat → String) (o : SEOutcome) (c : SECert) :
    (∃ n, refSEWrap nm o c = .aside n) ↔
      (o.isInconclusive = true ∨ (o.isProven = true ∧ (c = .failed ∨ c = .inconclusive))) := by
  cases o <;> cases c <;> simp [refSEWrap, SEOutcome.isInconclusive, SEOutcome.isProven]

/-- ✓ **The reference phase meets VER-018.** Example: on the ring `t0: p0 → p1`, `t1: p1 → p0`
with one token on `p0`, the candidate "both places empty" has no witness run, so the phase looks
for a trap, finds `{p0, p1}` (marked at the start, empty in the candidate), adds
`m_p0 + m_p1 ≥ 1` and asks again; the `unsat` answer is handed over as a proof. Had the witness
search found a run instead, the phase would hand it over as a confirmed `Violated`. -/
-- The search, the trap search and the re-check meet their lines (`ver018_refSearch_lines`,
-- `ver018_refTrap_lines`, `refSECheckInd_sound`); the loop unfolds as the lines say
-- (`seLoopPhase_*`); the hand-over is `state_equation_decision`'s.
@[evidence holds VER_018]
theorem VER_018_reference :
    VER_018 refSESearch refSETrap refSECheckInd refSEPhase refSEWrap := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := ver018_refSearch_lines
  obtain ⟨t1, t2⟩ := ver018_refTrap_lines
  refine ⟨s1, s2, s3, s4, s5, t1, t2, fun _ _ _ _ _ h => refSECheckInd_sound h,
    fun _ _ _ _ _ _ _ _ _ _ h => seLoopPhase_aside _ _ _ h,
    fun _ _ _ _ _ _ _ _ _ _ h => seLoopPhase_unsat _ _ _ h,
    fun _ _ _ _ _ _ _ _ _ _ _ _ h hs => seLoopPhase_found _ _ _ h hs,
    fun _ _ _ _ _ _ _ _ _ _ _ h hs hL => seLoopPhase_limit _ _ _ h hs hL,
    fun _ _ _ _ _ _ _ _ _ _ _ _ h hs hL hr => seLoopPhase_refine _ _ _ h hs hL hr,
    fun _ _ _ _ _ _ _ _ _ _ _ _ h hs hL hr => seLoopPhase_error _ _ _ h hs hL hr,
    fun nm rs c hc => ?_, ver018_refWrap_aside, fun _ _ _ _ => rfl, fun _ _ _ _ _ h => h⟩
  rcases hc with rfl | rfl <;> rfl

/-- ✓ **VER-018 can be met.** Example: the reference search, trap search, re-check, refinement
loop and hand-over together, the parts that turn the queue-and-bundle candidate into a confirmed
`Violated` and the ring candidate into a proof, satisfy every line at once. -/
@[evidence consistent VER_018]
theorem VER_018_consistent :
    ∃ (S : SESearch) (T : SETrapFn) (X : SEIndCheck) (P : SEPhaseFn) (W : SEWrap),
      VER_018 S T X P W :=
  ⟨_, _, _, _, _, VER_018_reference⟩

/-! ### What the statement says on its own -/

/-- A refinement that is a trap or an inductive inequality holds on every reachable marking. -/
def SESound (net : FlatNet) (envs : List PlaceId) (w : Nat) (a0 : AMarking) (r : SEIneq) : Prop :=
  r.origin ≠ .relative → ∀ a, ReachAInj net envs a0 a → r.holds w a = true

/-- **A trap or inductive refinement the loop adds holds on every reachable marking**, from the
statement alone: a trap the trap search returns stays marked, and an inequality the re-check
accepts is inductive. -/
theorem ver018_refine_sound {S : SESearch} {T : SETrapFn} {X : SEIndCheck} {P : SEPhaseFn}
    {W : SEWrap} (h : VER_018 S T X P W) {syn : Bool → AMarking → SESynAns} {net : FlatNet}
    {envs : List PlaceId} {w : Nat} {a0 m : AMarking} {r : SEIneq}
    (hr : seRefine T X syn net envs w a0 m = .ok r) : SESound net envs w a0 r := by
  obtain ⟨-, -, -, -, -, h6, -, h8, -⟩ := h
  intro horig a ha
  unfold seRefine at hr
  cases hT : T net w a0 m with
  | some Q =>
    rw [hT] at hr
    cases hr
    obtain ⟨hg, hw, hm, -⟩ := h6 _ _ _ _ _ hT
    exact seTrap_holds_reach hg hw hm ha
  | none =>
    rw [hT] at hr
    cases hs : syn false m with
    | aside => rw [hs] at hr; cases hr
    | found a' b =>
      rw [hs] at hr
      simp only at hr
      split at hr
      · rename_i hc
        cases hr
        exact seInductive_reach (h8 _ _ _ _ _ hc.1) ha
      · cases hr
    | none =>
      rw [hs] at hr
      cases hs2 : syn true m with
      | aside => rw [hs2] at hr; cases hr
      | none => rw [hs2] at hr; cases hr
      | found a' b =>
        rw [hs2] at hr
        simp only at hr
        split at hr
        · cases hr; exact absurd rfl horig
        · cases hr

/-- What the loop guarantees of its outcome from the refinements `rs`: every trap or inductive
refinement holds on every reachable marking, at most `max L |rs|` refinements, a proof comes
from an `unsat` answer over its refinements, and a run from a search on a `sat` candidate. -/
def SELoopInv (S : SESearch) (net : FlatNet) (envs : List PlaceId) (w : Nat) (a0 : AMarking)
    (bad : AMarking → Bool) (L B : Nat) (seq : List SEIneq → SEAns) (rs : List SEIneq)
    (o : SEOutcome) : Prop :=
  (∀ r ∈ o.refs, SESound net envs w a0 r) ∧ o.refs.length ≤ max L rs.length ∧
    (∀ rs', o = .proven rs' → seq rs' = .unsat) ∧
    (∀ run rs', o = .violated run rs' →
      ∃ c : SECand, seq rs' = .sat c ∧ S net envs a0 c.n bad B = .found run)

/-- One round of the loop keeps `SELoopInv`. -/
theorem ver018_loop_step {S : SESearch} {T : SETrapFn} {X : SEIndCheck} {P : SEPhaseFn}
    {W : SEWrap} (h : VER_018 S T X P W) {net : FlatNet} {envs : List PlaceId} {w : Nat}
    {a0 : AMarking} {bad : AMarking → Bool} {L B : Nat} {seq : List SEIneq → SEAns}
    {syn : Bool → AMarking → SESynAns} {rs : List SEIneq} (hv : ∀ r ∈ rs, SESound net envs w a0 r)
    (ih : ∀ r, rs.length < L → SESound net envs w a0 r →
      SELoopInv S net envs w a0 bad L B seq (rs ++ [r]) (P net envs w a0 bad L B seq syn (rs ++ [r]))) :
    SELoopInv S net envs w a0 bad L B seq rs (P net envs w a0 bad L B seq syn rs) := by
  have hsound := @ver018_refine_sound S T X P W h syn net envs w a0
  obtain ⟨-, -, -, -, -, -, -, -, h9, h10, h11, h12, h13, h14, -⟩ := h
  have hrest : ∀ why, SELoopInv S net envs w a0 bad L B seq rs (.inconclusive why rs) :=
    fun why => ⟨hv, le_max_right _ _, (fun _ h' => by cases h'), (fun _ _ h' => by cases h')⟩
  cases hq : seq rs with
  | aside => rw [h9 _ _ _ _ _ _ _ _ _ _ hq]; exact hrest _
  | unsat =>
    rw [h10 _ _ _ _ _ _ _ _ _ _ hq]
    exact ⟨hv, le_max_right _ _, (fun rs' h' => by cases h'; exact hq), (fun _ _ h' => by cases h')⟩
  | sat c =>
    cases hs : S net envs a0 c.n bad B with
    | found run =>
      rw [h11 _ _ _ _ _ _ _ _ _ _ _ _ hq hs]
      exact ⟨hv, le_max_right _ _, (fun _ h' => by cases h'),
        (fun run' rs' h' => by cases h'; exact ⟨c, hq, hs⟩)⟩
    | none | exhausted =>
      have hS : ∀ run, S net envs a0 c.n bad B ≠ .found run := by
        intro run h'; rw [hs] at h'; cases h'
      by_cases hL : L ≤ rs.length
      · rw [h12 _ _ _ _ _ _ _ _ _ _ _ hq hS hL]; exact hrest _
      · have hL' : rs.length < L := by omega
        cases hr : seRefine T X syn net envs w a0 c.m with
        | ok r =>
          rw [h13 _ _ _ _ _ _ _ _ _ _ _ _ hq hS hL' hr]
          obtain ⟨i1, i2, i3, i4⟩ := ih r hL' (hsound hr)
          refine ⟨i1, ?_, i3, i4⟩
          simp only [List.length_append, List.length_singleton] at i2
          omega
        | error why => rw [h14 _ _ _ _ _ _ _ _ _ _ _ _ hq hS hL' hr]; exact hrest _

/-- **The loop invariant**, from the statement alone, by induction on the refinements left. -/
theorem VER_018_loop {S : SESearch} {T : SETrapFn} {X : SEIndCheck} {P : SEPhaseFn}
    {W : SEWrap} (h : VER_018 S T X P W) {net : FlatNet} {envs : List PlaceId} {w : Nat}
    {a0 : AMarking} {bad : AMarking → Bool} {L B : Nat} {seq : List SEIneq → SEAns}
    {syn : Bool → AMarking → SESynAns} :
    ∀ (k : Nat) (rs : List SEIneq), L - rs.length ≤ k → (∀ r ∈ rs, SESound net envs w a0 r) →
      SELoopInv S net envs w a0 bad L B seq rs (P net envs w a0 bad L B seq syn rs)
  | 0, _, hk, hv => ver018_loop_step h hv fun _ hL _ => absurd hL (by omega)
  | k + 1, rs, hk, hv => ver018_loop_step h hv fun r _ hr =>
      VER_018_loop h k (rs ++ [r]) (by simp only [List.length_append, List.length_singleton]; omega)
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hv x hx
          · rw [List.mem_singleton] at hx; subst hx; exact hr)

/-- The loop invariant from no refinement. -/
theorem VER_018_start {S : SESearch} {T : SETrapFn} {X : SEIndCheck} {P : SEPhaseFn}
    {W : SEWrap} (h : VER_018 S T X P W) {net : FlatNet} {envs : List PlaceId} {w : Nat}
    {a0 : AMarking} {bad : AMarking → Bool} {L B : Nat} {seq : List SEIneq → SEAns}
    {syn : Bool → AMarking → SESynAns} :
    SELoopInv S net envs w a0 bad L B seq [] (P net envs w a0 bad L B seq syn []) :=
  VER_018_loop h L [] (by simp) (by simp)

/-- **Every trap and inductive refinement holds on every reachable marking**, from the statement
alone. Example: on the ring `t0: p0 → p1`, `t1: p1 → p0` with one token on `p0`, the trap
refinement `m_p0 + m_p1 ≥ 1` holds wherever the token is. -/
@[evidence cites "VER-018" "Every trap and inductive refinement holds in every reachable marking"]
theorem VER_018_refinements_hold {S : SESearch} {T : SETrapFn} {X : SEIndCheck} {P : SEPhaseFn}
    {W : SEWrap} (h : VER_018 S T X P W) {net : FlatNet} {envs : List PlaceId} {w : Nat}
    {a0 : AMarking} {bad : AMarking → Bool} {L B : Nat} {seq : List SEIneq → SEAns}
    {syn : Bool → AMarking → SESynAns} :
    ∀ r ∈ (P net envs w a0 bad L B seq syn []).refs, r.origin ≠ .relative →
      ∀ a, ReachAInj net envs a0 a → r.holds w a = true :=
  (VER_018_start h).1

/-- **At most the refinement limit**, from the statement alone. Example: with the limit 0 the
phase adds no refinement and steps aside on the first candidate no run settles. -/
@[evidence cites "VER-018" "after 32 refinements"]
theorem VER_018_limit {S : SESearch} {T : SETrapFn} {X : SEIndCheck} {P : SEPhaseFn}
    {W : SEWrap} (h : VER_018 S T X P W) {net : FlatNet} {envs : List PlaceId} {w : Nat}
    {a0 : AMarking} {bad : AMarking → Bool} {L B : Nat} {seq : List SEIneq → SEAns}
    {syn : Bool → AMarking → SESynAns} :
    (P net envs w a0 bad L B seq syn []).refs.length ≤ L := by
  have := (VER_018_start (syn := syn) h (net := net) (envs := envs) (w := w) (a0 := a0)
    (bad := bad) (L := L) (B := B) (seq := seq)).2.1
  simpa using this

/-- **A reported run is a run to a violating marking**, from the statement alone: a `Violated`
the phase hands over carries the transitions of a run within a candidate's counts that replays
from `M0` with no injection step, and its last marking violates and is reachable. Example: on the
queue-and-bundle net with `cancel`, the run `produce, produce, produce, cancel` ends with three
tokens stuck in `q`. -/
@[evidence cites "VER-018" "A genuine violation is never masked: the phase returns `Violated` only for a replayed run."]
theorem VER_018_violated_sound {S : SESearch} {T : SETrapFn} {X : SEIndCheck} {P : SEPhaseFn}
    {W : SEWrap} (h : VER_018 S T X P W) {net : FlatNet} {envs : List PlaceId} {w : Nat}
    {a0 : AMarking} {bad : AMarking → Bool} {L B : Nat} {seq : List SEIneq → SEAns}
    {syn : Bool → AMarking → SESynAns} {nm : Nat → String} {cert : SECert}
    {tr : List String} {conf : Option Bool}
    (hW : W nm (P net envs w a0 bad L B seq syn []) cert = .decided .violated tr conf) :
    ∃ run a, tr = run.map nm ∧ conf = some true ∧ (∃ c : SECand, SEWithin run c.n) ∧
      seReplay net a0 run = some a ∧ bad a = true ∧ ReachAInj net envs a0 a := by
  obtain ⟨-, -, -, hviol⟩ := VER_018_start (syn := syn) h (net := net) (envs := envs) (w := w)
    (a0 := a0) (bad := bad) (L := L) (B := B) (seq := seq)
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, h16, h17, -⟩ := h
  cases ho : P net envs w a0 bad L B seq syn [] with
  | proven rs =>
    rw [ho] at hW
    cases cert with
    | passed => rw [h15 nm rs .passed (Or.inl rfl)] at hW; simp at hW
    | disabled => rw [h15 nm rs .disabled (Or.inr rfl)] at hW; simp at hW
    | failed =>
      obtain ⟨n, hn⟩ := (h16 nm (.proven rs) .failed).mpr (Or.inr ⟨rfl, Or.inl rfl⟩)
      rw [hn] at hW; cases hW
    | inconclusive =>
      obtain ⟨n, hn⟩ := (h16 nm (.proven rs) .inconclusive).mpr (Or.inr ⟨rfl, Or.inr rfl⟩)
      rw [hn] at hW; cases hW
  | violated run rs =>
    rw [ho, h17] at hW
    simp only [Verifier.PhaseOut.decided.injEq, true_and] at hW
    obtain ⟨c, -, hs⟩ := hviol run rs ho
    obtain ⟨hw, hh⟩ := h1 _ _ _ _ _ _ _ hs
    unfold seHits at hh
    cases hr : seReplay net a0 run with
    | none => rw [hr] at hh; cases hh
    | some a =>
      rw [hr] at hh
      exact ⟨run, a, hW.1.symm, hW.2.symm, ⟨c, hw⟩, hr, hh, seReplay_reach hr⟩
  | inconclusive why rs =>
    rw [ho] at hW
    obtain ⟨n, hn⟩ := (h16 nm (.inconclusive why rs) cert).mpr (Or.inl rfl)
    rw [hn] at hW; cases hW

/-- **A `Proven` comes from a proof with the certificate check passed or disabled**, from the
statement alone. Example: a proof whose certificate check fails is handed over as an aside, and
the pipeline goes on to the fixpoint query. -/
@[evidence cites "VER-018" "AC4: while the certificate check is enabled, the phase's Proven is withheld unless the check passes"]
theorem VER_018_proven_needs_check {S : SESearch} {T : SETrapFn} {X : SEIndCheck}
    {P : SEPhaseFn} {W : SEWrap} (h : VER_018 S T X P W) {net : FlatNet} {envs : List PlaceId}
    {w : Nat} {a0 : AMarking} {bad : AMarking → Bool} {L B : Nat} {seq : List SEIneq → SEAns}
    {syn : Bool → AMarking → SESynAns} {nm : Nat → String} {cert : SECert} {m : String}
    {tr : List String} {conf : Option Bool}
    (hW : W nm (P net envs w a0 bad L B seq syn []) cert = .decided (.proven m) tr conf) :
    ∃ rs, P net envs w a0 bad L B seq syn [] = .proven rs ∧ seq rs = .unsat ∧
      (cert = .passed ∨ cert = .disabled) ∧ m = ver018_method := by
  obtain ⟨-, -, hprov, -⟩ := VER_018_start (syn := syn) h (net := net) (envs := envs) (w := w)
    (a0 := a0) (bad := bad) (L := L) (B := B) (seq := seq)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, h16, h17, -⟩ := h
  cases ho : P net envs w a0 bad L B seq syn [] with
  | proven rs =>
    rw [ho] at hW
    have hm : ∀ c, (c = SECert.passed ∨ c = .disabled) →
        W nm (.proven rs) c = .decided (.proven m) tr conf → m = ver018_method := by
      intro c hc hw'
      rw [h15 nm rs c hc] at hw'
      simp only [Verifier.PhaseOut.decided.injEq, Verifier.Verdict.proven.injEq] at hw'
      exact hw'.1.symm
    cases cert with
    | passed => exact ⟨rs, rfl, hprov rs ho, Or.inl rfl, hm _ (Or.inl rfl) hW⟩
    | disabled => exact ⟨rs, rfl, hprov rs ho, Or.inr rfl, hm _ (Or.inr rfl) hW⟩
    | failed =>
      obtain ⟨n, hn⟩ := (h16 nm (.proven rs) .failed).mpr (Or.inr ⟨rfl, Or.inl rfl⟩)
      rw [hn] at hW; cases hW
    | inconclusive =>
      obtain ⟨n, hn⟩ := (h16 nm (.proven rs) .inconclusive).mpr (Or.inr ⟨rfl, Or.inr rfl⟩)
      rw [hn] at hW; cases hW
  | violated run rs => rw [ho, h17] at hW; simp at hW
  | inconclusive why rs =>
    rw [ho] at hW
    obtain ⟨n, hn⟩ := (h16 nm (.inconclusive why rs) cert).mpr (Or.inl rfl)
    rw [hn] at hW; cases hW

/-- **A `Proven` after a passed certificate check is sound**, from the statement alone, when the
check is right: a passed check means the three verification conditions hold for
`SE(M, n) ∧ ⋀ refinements(M)` against the raw counter step from `(M0, 0)`, and then no reachable
marking violates (`vc_sound_state_equation` of [VER-016]). Example: on the ring with one token,
the trap refinement and the equation make `m_p0 + m_p1 = 1` an invariant, so no reachable marking
is empty. -/
@[evidence cites "VER-018" "A proof is the inductive invariant `SE(M, n) ∧ ⋀ refinements(M)` over the places and one counter per flat transition."]
theorem VER_018_proven_sound {S : SESearch} {T : SETrapFn} {X : SEIndCheck} {P : SEPhaseFn}
    {W : SEWrap} (h : VER_018 S T X P W) {net : FlatNet} {envs : List PlaceId} {w : Nat}
    {a0 : AMarking} {bad : AMarking → Bool} {L B : Nat} {seq : List SEIneq → SEAns}
    {syn : Bool → AMarking → SESynAns} {nm : Nat → String} {cert : SECert} {m : String}
    {tr : List String} {conf : Option Bool}
    (hW : W nm (P net envs w a0 bad L B seq syn []) cert = .decided (.proven m) tr conf)
    (hon : cert ≠ .disabled)
    (hcheck : cert = .passed → ∀ rs, P net envs w a0 bad L B seq syn [] = .proven rs →
      Novel.Certificate.VCs (StepCntRel net envs) (a0, fun _ => 0) (fun s => bad s.1 = true)
        (seCert net envs w a0 rs)) :
    ProvenFor (ReachAInj net envs a0) (fun a => bad a = true) := by
  obtain ⟨rs, hP, -, hc, -⟩ := VER_018_proven_needs_check h hW
  have hpass : cert = .passed := by
    rcases hc with hc | hc
    · exact hc
    · exact absurd hc hon
  exact Novel.Certificate.vc_sound_state_equation (hcheck hpass rs hP)

/-- **The bare `unsat` is a proof when the solver is right and the relative refinements hold**,
from the statement alone: every reachable marking satisfies the marking equation for the counts
of its run (`rows_hold`, `counters_exist`) and every trap and inductive refinement
(`VER_018_refinements_hold`), so a query that has no solution with the violation leaves no
reachable marking that violates. Example: on the net `t: a → b` with `M0 = {a: 1}`, after the
inequality `a + b ≤ 1` the query for `b ≥ 2` has no solution, and indeed no reachable marking
puts two tokens on `b`. -/
@[evidence cites "VER-018" "Every reachable marking satisfies the equation for the counts of its run, so `unsat` proves the property."]
theorem VER_018_unsat_sound {S : SESearch} {T : SETrapFn} {X : SEIndCheck} {P : SEPhaseFn}
    {W : SEWrap} (h : VER_018 S T X P W) {net : FlatNet} {envs : List PlaceId} {w : Nat}
    {a0 : AMarking} {bad : AMarking → Bool} {L B : Nat} {seq : List SEIneq → SEAns}
    {syn : Bool → AMarking → SESynAns} {rs : List SEIneq}
    (hP : P net envs w a0 bad L B seq syn [] = .proven rs)
    (hq : seq rs = .unsat → ∀ a n, (∀ p, p < w → p ∉ envs → Libpetri.Row net a0 a n p) →
      (∀ r ∈ rs, r.holds w a = true) → bad a = false)
    (hrel : ∀ r ∈ rs, r.origin = .relative → ∀ a, ReachAInj net envs a0 a → r.holds w a = true) :
    ProvenFor (ReachAInj net envs a0) (fun a => bad a = true) := by
  obtain ⟨hsound, -, hprov, -⟩ := VER_018_start (syn := syn) h (net := net) (envs := envs)
    (w := w) (a0 := a0) (bad := bad) (L := L) (B := B) (seq := seq)
  rw [hP] at hsound hprov
  intro a ha hbad
  obtain ⟨n, hn⟩ := Libpetri.counters_exist ha
  have hrows := Libpetri.rows_hold hn
  have hrefs : ∀ r ∈ rs, r.holds w a = true := by
    intro r hr
    by_cases ho : r.origin = .relative
    · exact hrel r hr ho a ha
    · exact hsound r hr ho a ha
  have := hq (hprov rs rfl) a n (fun p _ hp => hrows p hp) hrefs
  rw [hbad] at this; cases this

/-! ## Pure functions: the limits, the budgets and the report

Kind-N and report lines of the quoted sentences and the acceptance criteria, as functions,
pinned with `#guard`. They are not part of the statement. -/

/-- The refinement limit (twentieth quoted sentence; ruling D45). -/
def ver018_refinementLimit : Nat := 32

/-- The node budget of one witness search (twenty-first quoted sentence; ruling D45). -/
def ver018_nodeBudget : Nat := 100000

/-- The magnitude bound on the weights of an inductive or relative inequality: the larger of 8
and the tokens `M0` holds (twenty-second quoted sentence; ruling D45). -/
def ver018_weightBound (tokens : Nat) : Nat := max 8 tokens

/-- AC1: the certificate line of a passed check. -/
def ver018_certPassedLine : String := "  Certificate check: PASSED (init, consecution, safety)"

/-- The certificate line of a disabled check (eighteenth quoted sentence; ruling D52). -/
def ver018_certDisabledLine : String := "  Certificate check: not applicable (disabled)"

/-- The word the report prints for a refinement's origin. -/
def ver018_originWord : SEOrigin → String
  | .trap => "trap"
  | .inductive => "inductive"
  | .relative => "relative"

/-- AC2: the report line of one refinement, with the inequality as the report prints it. -/
def ver018_refinementLine (o : SEOrigin) (text : String) : String :=
  s!"    Refinement ({ver018_originWord o}): {text}"

/-- AC6: the dump phases of the phase's scripts ([VER-013]). -/
def ver018_dumpPhases : List String := ["state-equation", "invariant"]

#guard ver018_refinementLimit == 32
#guard ver018_nodeBudget == 100000
#guard ver018_weightBound 3 == 8
#guard ver018_weightBound 12 == 12
#guard ver018_method == "state-equation"
#guard ver018_certPassedLine == "  Certificate check: PASSED (init, consecution, safety)"
#guard ver018_certDisabledLine == "  Certificate check: not applicable (disabled)"
#guard ver018_refinementLine .inductive "hasdata <= ready0 + ready1" ==
  "    Refinement (inductive): hasdata <= ready0 + ready1"
#guard ver018_dumpPhases == ["state-equation", "invariant"]

/-! ### Examples -/

/-- A flat transition with `one`/`all` inputs, inhibitor arcs and reset arcs, no read arc. -/
def ver018_tr (name : String) (ins : List (PlaceId × Libpetri.Card)) (inh : List PlaceId)
    (resets : List PlaceId := []) : Transition :=
  { name, inputs := ins.map fun (p, c) => ⟨p, c, none⟩, inhibitors := inh, reads := [], resets }

/-- The queue-and-bundle net with the `cancel` alternative, over the places `budget` (0), `q`
(1), `s` (2), `src` (3), `out` (4) and `cancelled` (5): `produce: budget → q` inhibited by `s`
and `out`, `signal: src → s`, `bundle: all(q) + s → out`, `bundleEmpty: s, inhibitor(q) → out`,
`cancel: src → cancelled`. -/
def ver018_queueCancel : FlatNet :=
  [(ver018_tr "produce" [(0, .one)] [2, 4], [1]),
   (ver018_tr "signal" [(3, .one)] [], [2]),
   (ver018_tr "bundle" [(1, .all), (2, .one)] [], [4]),
   (ver018_tr "bundleEmpty" [(2, .one)] [1], [4]),
   (ver018_tr "cancel" [(3, .one)] [], [5])]

/-- The names of its transitions. -/
def ver018_names (i : Nat) : String :=
  ["produce", "signal", "bundle", "bundleEmpty", "cancel"].getD i "?"

/-- `M0 = {budget: 3, src: 1}`. -/
def ver018_queueA0 : AMarking := fun p => if p = 0 then 3 else if p = 3 then 1 else 0

/-- `DeadlockFree` with the sinks `sinks`: no transition is enabled and some place below `w` that
is not a sink holds a token. -/
def ver018_deadlock (net : FlatNet) (w : Nat) (sinks : List PlaceId) : AMarking → Bool := fun a =>
  net.all (fun ft => !enabledA a ft.1) && (List.range w).any fun p => a p != 0 && !sinks.contains p

/-- The violation of the test derivation: `DeadlockFree` with `out`, `budget` and `cancelled` as
sinks. -/
def ver018_queueBad : AMarking → Bool := ver018_deadlock ver018_queueCancel 6 [4, 0, 5]

/-- The candidate `{q: 3, cancelled: 1}` after `produce ×3, cancel ×1`. -/
def ver018_cancelCand : SECand :=
  ⟨fun p => if p = 1 then 3 else if p = 5 then 1 else 0,
   fun k => if k = 0 then 3 else if k = 4 then 1 else 0⟩

/-- The ring `t0: p0 → p1`, `t1: p1 → p0`. -/
def ver018_ring : FlatNet :=
  [(ver018_tr "t0" [(0, .one)] [], [1]), (ver018_tr "t1" [(1, .one)] [], [0])]

/-- One token on place `0`. -/
def ver018_one0 : AMarking := fun p => if p = 0 then 1 else 0

/-- No token anywhere. -/
def ver018_empty : AMarking := fun _ => 0

/-- Both places of the ring are empty. -/
def ver018_bothEmpty : AMarking → Bool := fun a => a 0 == 0 && a 1 == 0

/-- The state-equation query on the ring: first the candidate "both places empty after no
firing", then `unsat`. -/
def ver018_ringSeq : List SEIneq → SEAns := fun rs =>
  if rs.isEmpty then .sat ⟨ver018_empty, fun _ => 0⟩ else .unsat

/-- `t: a → b`, over the places `a` (0) and `b` (1). -/
def ver018_move : FlatNet := [(ver018_tr "t" [(0, .one)] [], [1])]

/-- `a + b ≤ 1`. -/
def ver018_sum : SEIneq := ⟨fun p => if p < 2 then 1 else 0, 1, .inductive⟩

/-- `b` holds at least two tokens. -/
def ver018_twoB : AMarking → Bool := fun a => decide (2 ≤ a 1)

/-- `b` holds a token. -/
def ver018_oneB : AMarking → Bool := fun a => decide (1 ≤ a 1)

/-- One token on each of `a` and `b`. -/
def ver018_both : AMarking := fun p => if p < 2 then 1 else 0

/-- The state-equation query on `t: a → b`: first the candidate `{a: 1, b: 1}`, then `unsat`. -/
def ver018_moveSeq : List SEIneq → SEAns := fun rs =>
  if rs.isEmpty then .sat ⟨ver018_both, fun _ => 0⟩ else .unsat

/-- The `invariant` queries on `t: a → b`: the first returns `a + b ≤ 1`, the second nothing. -/
def ver018_moveSyn : Bool → AMarking → SESynAns := fun rel _ =>
  if rel then .none else .found ver018_sum.a ver018_sum.b

/-- ✓ **AC1 and AC3 on worked examples.** On the queue-and-bundle net with `cancel`, from
`{budget: 3, src: 1}`, the candidate with the counts `produce ×3, cancel ×1` is realised: the
witness search reports `produce, produce, produce, cancel`, the shortest run within those counts
that leaves the net dead with three tokens in `q`, and the phase hands it over as a confirmed
`Violated` with those four transitions. On the ring `t0: p0 → p1`, `t1: p1 → p0` with one token on
`p0`, the candidate "both places empty after no firing" has no witness; `{p0, p1}` is a trap,
marked at the start and empty in the candidate, so the phase adds `m_p0 + m_p1 ≥ 1`, asks again,
and the `unsat` answer is a proof. On `t: a → b` from `{a: 1}`, the candidate `{a: 1, b: 1}`
leaves no place empty, so no trap applies; the first `invariant` query returns `a + b ≤ 1`, which
the exact re-check accepts (`t` keeps the sum) and the candidate violates, and the next `unsat`
is a proof of `b ≤ 1`. -/
@[evidence nonvacuous VER_018]
theorem VER_018_nonvacuous :
    refSESearch ver018_queueCancel [] ver018_queueA0 ver018_cancelCand.n ver018_queueBad
        ver018_nodeBudget = .found [0, 0, 0, 4] ∧
      (refSEPhase ver018_queueCancel [] 6 ver018_queueA0 ver018_queueBad ver018_refinementLimit
        ver018_nodeBudget (fun _ => .sat ver018_cancelCand) (fun _ _ => .none) []).summary =
        .violated [0, 0, 0, 4] [] ∧
      refSEWrap ver018_names (.violated [0, 0, 0, 4] []) .passed =
        .decided .violated ["produce", "produce", "produce", "cancel"] (some true) ∧
      refSETrap ver018_ring 2 ver018_one0 ver018_empty = some [0, 1] ∧
      (refSEPhase ver018_ring [] 2 ver018_one0 ver018_bothEmpty ver018_refinementLimit
        ver018_nodeBudget ver018_ringSeq (fun _ _ => .aside) []).summary = .proven [.trap] ∧
      refSECheckInd ver018_move [] 2 ver018_one0 ver018_sum = true ∧
      (refSEPhase ver018_move [] 2 ver018_one0 ver018_twoB ver018_refinementLimit
        ver018_nodeBudget ver018_moveSeq ver018_moveSyn []).summary = .proven [.inductive] :=
  ⟨by decide, by decide, rfl, by decide, by decide, by decide, by decide⟩

/-- The join of a compiled workflow net, over the places `aData` (0), `aEmpty` (1), `bData` (2),
`bEmpty` (3), `done` (4), `hasdata` (5), `ready0` (6), `ready1` (7), `skipped` (8) and `start`
(9): the two branches of `route`, the four arms, `mergeStart: ready0 + ready1 + all(hasdata) →
done` and `mergeSkip: ready0 + ready1, inhibitor(hasdata) → skipped`. -/
def ver018_join : FlatNet :=
  [(ver018_tr "route_b0" [(9, .one)] [], [0, 3]),
   (ver018_tr "route_b1" [(9, .one)] [], [1, 2]),
   (ver018_tr "armAData" [(0, .one)] [], [5, 6]),
   (ver018_tr "armAEmpty" [(1, .one)] [], [6]),
   (ver018_tr "armBData" [(2, .one)] [], [5, 7]),
   (ver018_tr "armBEmpty" [(3, .one)] [], [7]),
   (ver018_tr "mergeStart" [(6, .one), (7, .one), (5, .all)] [], [4]),
   (ver018_tr "mergeSkip" [(6, .one), (7, .one)] [5], [8])]

/-- `M0 = {start: 1}`. -/
def ver018_joinA0 : AMarking := fun p => if p = 9 then 1 else 0

/-- `hasdata ≤ ready0 + ready1`. -/
def ver018_joinIneq : SEIneq :=
  ⟨fun p => if p = 5 then 1 else if p = 6 ∨ p = 7 then -1 else 0, 0, .inductive⟩

/-- The spurious candidate: the data arrived and the join skipped (`hasdata: 1, skipped: 1`). -/
def ver018_skipCand : AMarking := fun p => if p = 5 ∨ p = 8 then 1 else 0

/-- ✓ **AC2 on the join of the test derivation.** The exact re-check accepts
`hasdata ≤ ready0 + ready1` on the join: it holds at `{start: 1}`, each arm keeps it,
`mergeStart` restores it because it empties `hasdata`, and `mergeSkip` restores it because it
needs `hasdata` empty. The candidate that skips after the data arrived violates it, so it is the
refinement that excludes that candidate. -/
@[evidence cites "VER-018" "AC2: the inequality hasdata <= ready0 + ready1 passes the exact re-check on the join and excludes the candidate that skips after the data arrived"]
theorem VER_018_join_refinement :
    refSECheckInd ver018_join [] 10 ver018_joinA0 ver018_joinIneq = true ∧
      ver018_joinIneq.holds 10 ver018_skipCand = false := by
  decide

/-- `clear`: a reset arc on `p0` and an output into `p1`, no input arc. -/
def ver018_clear : FlatNet := [(ver018_tr "clear" [] [] [0], [1])]

/-- ✓ **Why a trap must count clearing arcs.** On `clear` from `{p0: 1}`, `{p0}` is a trap in the
plain sense (no transition consumes from it through an input arc) and is marked at the start,
but `clear` empties it: the reachable marking after `clear` holds no token on `p0`. It is not a
trap with clearing arcs, since `clear` takes tokens from it and puts none back. -/
@[evidence cites "VER-018" "A transition with a consume-all input or a reset arc on a trap place removes tokens from the trap, so it too must put one back."]
theorem VER_018_plain_trap_fails :
    Novel.Commoner.Trap ver018_clear (· = 0) ∧
      ReachAInj ver018_clear [] ver018_one0 (fireA ver018_one0 (ver018_tr "clear" [] [] [0]) [1]) ∧
      fireA ver018_one0 (ver018_tr "clear" [] [] [0]) [1] 0 = 0 ∧ ¬ SEGTrap ver018_clear [0] := by
  refine ⟨?_, ReachAInj.step (ft := (ver018_tr "clear" [] [] [0], [1])) ReachAInj.init
    (List.mem_singleton.mpr rfl) (by decide), by decide,
    fun h => absurd (seGTrapB_iff.mpr h) (by decide)⟩
  intro ft hft ⟨p, hp, hc⟩
  simp only [ver018_clear, List.mem_singleton] at hft
  subst hft hp
  obtain ⟨s, hs, -, -⟩ := hc
  simp [ver018_tr] at hs

/-! ### Violations -/

/-- A search that ignores the counts: it searches as if every transition could fire once. -/
def ver018_searchNoCounts : SESearch := fun net envs a0 _ bad B =>
  refSESearch net envs a0 (fun _ => 1) bad B

/-- ✗ A search that ignores the counts violates VER-018 (line 1): on `t: a → b` with the
counts all zero it reports the run `t`, which fires `t` more often than the candidate allows. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_searchNoCounts :
    ¬ VER_018 ver018_searchNoCounts refSETrap refSECheckInd refSEPhase refSEWrap := by
  intro h
  have hf : ver018_searchNoCounts ver018_move [] ver018_one0 (fun _ => 0) ver018_oneB 0 =
      .found [0] := by decide
  have := (h.1 _ _ _ _ _ _ _ hf).1
  revert this; decide

/-- A search that scans the longest runs first. -/
def ver018_searchLongest : SESearch := fun net envs a0 c bad _ =>
  match seScan net bad a0 c (List.range (seTotal net.length c + 1)).reverse with
  | some r => .found r
  | none => if envs.isEmpty then .none else .exhausted

/-- The counts `t0 ×2, t1 ×1`. -/
def ver018_c21 : Counters := fun k => if k = 0 then 2 else if k = 1 then 1 else 0

/-- ✗ A search that is not breadth-first violates VER-018 (line 2): on the ring with the counts
`t0 ×2, t1 ×1` and the violation "a token on `p1`", it reports `t0, t1, t0` where `t0` alone
reaches a violating marking. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_searchLongest :
    ¬ VER_018 ver018_searchLongest refSETrap refSECheckInd refSEPhase refSEWrap := by
  intro h
  have hf : ver018_searchLongest ver018_ring [] ver018_one0 ver018_c21 ver018_oneB 0 =
      .found [0, 1, 0] := by decide
  have := h.2.1 _ _ _ _ _ _ _ [0] hf (by decide) (by decide)
  revert this; decide

/-- A search that reads a completed search as "no run" also under injection. -/
def ver018_searchNoneInj : SESearch := fun net _ a0 c bad B => refSESearch net [] a0 c bad B

/-- ✗ A completed search under injection read as "no run" violates VER-018 (line 3): on `t: a → b`
with `a` injected, a search with no counts completes and says no violating run exists, though an
injected token could enable a run it never tried. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_searchNoneInj :
    ¬ VER_018 ver018_searchNoneInj refSETrap refSECheckInd refSEPhase refSEWrap := by
  intro h
  have hf : ver018_searchNoneInj ver018_move [0] ver018_one0 (fun _ => 0) ver018_twoB 0 = .none := by
    decide
  have := (h.2.2.1 _ _ _ _ _ _ hf).1
  cases this

/-- A search that skips every net with injected places. -/
def ver018_searchSkipsInj : SESearch := fun net envs a0 c bad B =>
  if envs.isEmpty then refSESearch net envs a0 c bad B else .exhausted

/-- ✗ A search that skips injected nets violates VER-018 (line 4): on `t: a → b` with `a`
injected and the count `t ×1`, the run `t` reaches a token on `b`, which the search finds
without injection and misses with it. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_searchSkipsInj :
    ¬ VER_018 ver018_searchSkipsInj refSETrap refSECheckInd refSEPhase refSEWrap := by
  intro h
  have hf : ver018_searchSkipsInj ver018_move [] ver018_one0 (fun _ => 1) ver018_oneB 0 =
      .found [0] := by decide
  have := (h.2.2.2.1 ver018_move [0] ver018_one0 (fun _ => 1) ver018_oneB 0 [0]).mpr hf
  cases this

/-- A search that never finds anything. -/
def ver018_searchNever : SESearch := fun _ _ _ _ _ _ => .exhausted

/-- ✗ A search that never reports a run violates VER-018 (line 5): on `t: a → b` with the count
`t ×1`, the run `t` reaches a token on `b`, and no node budget makes the search report it. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_searchNever :
    ¬ VER_018 ver018_searchNever refSETrap refSECheckInd refSEPhase refSEWrap := by
  intro h
  obtain ⟨B0, hB⟩ := h.2.2.2.2.1 ver018_move [] ver018_one0 (fun _ => 1) ver018_oneB
    ⟨[0], by decide, by decide⟩
  obtain ⟨run, hrun⟩ := hB B0 le_rfl
  cases hrun

/-- A trap search with the plain trap of Commoner: input arcs only. -/
def ver018_trapPlain : SETrapFn := fun net w a0 m =>
  (List.range w).sublists.find? fun Q =>
    (net.all fun ft => !(Q.any fun p => decide (0 < pre ft.1 p)) || Q.any (ft.2.contains ·))
      && Q.any (fun q => decide (0 < a0 q)) && Q.all (fun q => m q == 0)

/-- ✗ A trap search that ignores reset and consume-all arcs violates VER-018 (line 6): on `clear`
from `{p0: 1}` it returns `{p0}` for the empty candidate, and the refinement `m_p0 ≥ 1` it adds
fails on the reachable marking after `clear` (`VER_018_plain_trap_fails`). -/
@[evidence forbids VER_018]
theorem VER_018_forbids_trapNoClearing :
    ¬ VER_018 refSESearch ver018_trapPlain refSECheckInd refSEPhase refSEWrap := by
  intro h
  have hf : ver018_trapPlain ver018_clear 2 ver018_one0 ver018_empty = some [0] := by decide
  have := (h.2.2.2.2.2.1 _ _ _ _ _ hf).1
  exact absurd (seGTrapB_iff.mpr this) (by decide)

/-- ✗ A trap search that never finds a trap violates VER-018 (line 7): on the ring with one token
on `p0`, `{p0, p1}` is a marked trap the empty candidate leaves empty. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_trapNever :
    ¬ VER_018 refSESearch (fun _ _ _ _ => none) refSECheckInd refSEPhase refSEWrap := by
  intro h
  have := h.2.2.2.2.2.2.1 ver018_ring 2 ver018_one0 ver018_empty rfl [0, 1] (by decide)
    (seGTrapB_iff.mp (by decide)) (by decide) 0 (by simp)
  revert this; decide

/-- `b ≤ 0` on `t: a → b`. -/
def ver018_bZero : SEIneq := ⟨fun p => if p = 1 then 1 else 0, 0, .inductive⟩

/-- ✗ A re-check that accepts everything violates VER-018 (line 8): `b ≤ 0` holds at `{a: 1}`,
but `t` breaks it. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_recheckAll :
    ¬ VER_018 refSESearch refSETrap (fun _ _ _ _ _ => true) refSEPhase refSEWrap := by
  intro h
  have hind := h.2.2.2.2.2.2.2.1 ver018_move [] 2 ver018_one0 ver018_bZero rfl
  have := hind.2 ver018_one0 (fireA ver018_one0 (ver018_tr "t" [(0, .one)] []) [1]) (by decide)
    (Or.inl ⟨(ver018_tr "t" [(0, .one)] [], [1]), by simp [ver018_move], by decide, rfl⟩)
  revert this; decide

/-- A re-check with the keep test only: the textbook Farkas check with the multiplier 1, without
the restore test that `check_inductive_exact` also allows. -/
def ver018_recheckKeepOnly : SEIndCheck := fun net envs w a0 r =>
  decide (dot r.a a0 w ≤ r.b)
    && envs.all (fun p => !decide (p < w) || decide (r.a p ≤ 0))
    && net.all (fun ft => !canFire ft.1 || seKeeps w r.a ft)

/-- ✗ A re-check without the restore test violates VER-018 (line 18). On the join of AC2,
`hasdata ≤ ready0 + ready1` holds at `{start: 1}` and every arm keeps it, but `mergeStart` and
`mergeSkip` each take a token from `ready0` and from `ready1`, so neither keeps the bound by
itself. Each restores it from its guard: `mergeStart` empties `hasdata`, and `mergeSkip` needs
`hasdata` empty. The reference re-check accepts the inequality; this one rejects it, so the
join would end inconclusive instead of proven. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_recheckKeepOnly :
    ¬ VER_018 refSESearch refSETrap ver018_recheckKeepOnly
      (seLoopPhase refSESearch refSETrap ver018_recheckKeepOnly) refSEWrap := by
  intro h
  have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ver018_join [] 10 ver018_joinA0 ver018_joinIneq
    VER_018_join_refinement.1
  revert this; decide

/-- A phase that reads an unanswered query as a proof. -/
def ver018_asideProves : SEPhaseFn := fun net envs w a0 bad L B seq syn rs =>
  match seq rs with
  | .aside => .proven rs
  | _ => refSEPhase net envs w a0 bad L B seq syn rs

/-- ✗ A phase that proves on an unanswered query violates VER-018 (line 9): a timeout is not a
proof. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_asideProves :
    ¬ VER_018 refSESearch refSETrap refSECheckInd ver018_asideProves refSEWrap := by
  intro h
  have := h.2.2.2.2.2.2.2.2.1 ver018_move [] 2 ver018_one0 ver018_twoB 32 0 (fun _ => .aside)
    (fun _ _ => .none) [] rfl
  cases this

/-- A phase that never proves: it steps aside on `unsat`. -/
def ver018_neverProves : SEPhaseFn := fun net envs w a0 bad L B seq syn rs =>
  match seq rs with
  | .unsat => .inconclusive .queryAside rs
  | _ => refSEPhase net envs w a0 bad L B seq syn rs

/-- ✗ A phase that never proves violates VER-018 (line 10): on `t: a → b` an `unsat` answer to
the query for `b ≥ 2` is a proof, and the phase steps aside. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_neverProves :
    ¬ VER_018 refSESearch refSETrap refSECheckInd ver018_neverProves refSEWrap := by
  intro h
  have := h.2.2.2.2.2.2.2.2.2.1 ver018_move [] 2 ver018_one0 ver018_twoB 32 0 (fun _ => .unsat)
    (fun _ _ => .none) [] rfl
  cases this

/-- A phase that never reports a run: it steps aside where the witness search found one. -/
def ver018_noWitness : SEPhaseFn := fun net envs w a0 bad L B seq syn rs =>
  match refSEPhase net envs w a0 bad L B seq syn rs with
  | .violated _ rs' => .inconclusive .noRefinement rs'
  | o => o

/-- ✗ A phase that skips the witness violates VER-018 (line 11): on `t: a → b` with the candidate
`t ×1` and the violation "a token on `b`", the run `t` is a witness and must be reported. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_noWitness :
    ¬ VER_018 refSESearch refSETrap refSECheckInd ver018_noWitness refSEWrap := by
  intro h
  have := h.2.2.2.2.2.2.2.2.2.2.1 ver018_move [] 2 ver018_one0 ver018_oneB 32 0
    (fun _ => .sat ⟨ver018_both, fun _ => 1⟩) (fun _ _ => .none) [] _ [0] rfl (by decide)
  have h2 := congrArg SEOutcome.summary this
  revert h2; decide

/-- A phase that ignores the refinement limit by one. -/
def ver018_overLimit : SEPhaseFn := fun net envs w a0 bad L B seq syn rs =>
  refSEPhase net envs w a0 bad (L + 1) B seq syn rs

/-- ✗ A phase that refines past the limit violates VER-018 (line 12): on the ring with the limit
0 and a query that always answers the empty candidate, the phase must step aside at once, and
this one adds the trap first. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_overLimit :
    ¬ VER_018 refSESearch refSETrap refSECheckInd ver018_overLimit refSEWrap := by
  intro h
  have hs : refSESearch ver018_ring [] ver018_one0 (fun _ => 0) ver018_bothEmpty 0 = .none := by
    decide
  have := h.2.2.2.2.2.2.2.2.2.2.2.1 ver018_ring [] 2 ver018_one0 ver018_bothEmpty 0 0
    (fun _ => .sat ⟨ver018_empty, fun _ => 0⟩) (fun _ _ => .aside) [] _ rfl
    (fun run h' => by rw [hs] at h'; cases h') (Nat.le_refl _)
  have h2 := congrArg SEOutcome.summary this
  revert h2; decide

/-- A phase that never looks for a trap. -/
def ver018_noTrap : SEPhaseFn := seLoopPhase refSESearch (fun _ _ _ _ => none) refSECheckInd

/-- ✗ A phase that skips the trap violates VER-018 (line 13): on the ring the trap `{p0, p1}`
settles the empty candidate, and this phase asks the `invariant` query instead and steps aside
when it gets no answer. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_noTrap :
    ¬ VER_018 refSESearch refSETrap refSECheckInd ver018_noTrap refSEWrap := by
  intro h
  have hs : refSESearch ver018_ring [] ver018_one0 (fun _ => 0) ver018_bothEmpty 0 = .none := by
    decide
  have := h.2.2.2.2.2.2.2.2.2.2.2.2.1 ver018_ring [] 2 ver018_one0 ver018_bothEmpty 32 0
    ver018_ringSeq (fun _ _ => .aside) [] _ (seTrapIneq [0, 1]) rfl
    (fun run h' => by rw [hs] at h'; cases h') (by decide) rfl
  have h2 := congrArg SEOutcome.summary this
  revert h2; decide

/-- Marks a relative inequality inductive. -/
def ver018_relabel : Except SEReason SEIneq → Except SEReason SEIneq
  | .ok r => .ok { r with origin := if r.origin = .relative then .inductive else r.origin }
  | .error e => .error e

/-- A phase that labels the relative inequality inductive, as if it held without the equation. -/
def ver018_relativeAsInductive : SEPhaseFn := fun net envs w a0 bad L B seq syn rs =>
  seLoopR refSESearch (fun m => ver018_relabel (seRefine refSETrap refSECheckInd syn net envs w a0 m))
    net envs a0 bad L B seq (L - rs.length + 1) rs

/-- The `invariant` queries on `t: a → b` when the first finds nothing: the relative query
returns `a + b ≤ 1`. -/
def ver018_relSyn : Bool → AMarking → SESynAns := fun rel _ =>
  if rel then .found ver018_sum.a ver018_sum.b else .none

/-- ✗ A phase that uses a relative inequality as an inductive one violates VER-018 (line 13): the
relative `a + b ≤ 1` must be added as relative, since only the certificate check re-proves it,
and this phase adds it as inductive. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_relativeAsInductive :
    ¬ VER_018 refSESearch refSETrap refSECheckInd ver018_relativeAsInductive refSEWrap := by
  intro h
  have hs : refSESearch ver018_move [] ver018_one0 (fun _ => 0) ver018_twoB 0 = .none := by
    decide
  have := h.2.2.2.2.2.2.2.2.2.2.2.2.1 ver018_move [] 2 ver018_one0 ver018_twoB 32 0
    ver018_moveSeq ver018_relSyn [] _ ⟨ver018_sum.a, ver018_sum.b, .relative⟩ rfl
    (fun run h' => by rw [hs] at h'; cases h') (by decide) rfl
  have h2 := congrArg SEOutcome.summary this
  revert h2; decide

/-- A phase that reads an unsettled candidate as a proof. -/
def ver018_unsettledProves : SEPhaseFn := fun net envs w a0 bad L B seq syn rs =>
  match refSEPhase net envs w a0 bad L B seq syn rs with
  | .inconclusive .noRefinement rs' => .proven rs'
  | o => o

/-- ✗ A phase that proves when nothing settles the candidate violates VER-018 (line 14): on
`t: a → b` with the candidate `{a: 1, b: 1}`, no trap and no inequality, the phase must step
aside. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_unsettledProves :
    ¬ VER_018 refSESearch refSETrap refSECheckInd ver018_unsettledProves refSEWrap := by
  intro h
  have hs : refSESearch ver018_move [] ver018_one0 (fun _ => 0) ver018_twoB 0 = .none := by
    decide
  have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ver018_move [] 2 ver018_one0 ver018_twoB 32 0
    ver018_moveSeq (fun _ _ => .none) [] _ .noRefinement rfl
    (fun run h' => by rw [hs] at h'; cases h') (by decide) rfl
  have h2 := congrArg SEOutcome.summary this
  revert h2; decide

/-- A hand-over that never reports a proof. -/
def ver018_wrapNeverProves : SEWrap := fun nm o c =>
  match o with
  | .proven _ => .aside "never"
  | o => refSEWrap nm o c

/-- ✗ A hand-over that withholds a proof whose certificate check passed violates VER-018
(line 15). -/
@[evidence forbids VER_018]
theorem VER_018_forbids_wrapNeverProves :
    ¬ VER_018 refSESearch refSETrap refSECheckInd refSEPhase ver018_wrapNeverProves := by
  intro h
  have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ver018_names [] .passed (Or.inl rfl)
  cases this

/-- The hand-over of ruling D52 (b): a disabled check withholds the proof. -/
def ver018_wrapDisabledWithholds : SEWrap := fun nm o c =>
  match o, c with
  | .proven _, .disabled => .aside "certificate check disabled"
  | o, c => refSEWrap nm o c

/-- ✗ A hand-over that withholds the proof when the certificate check is disabled violates
VER-018 (line 15, ruling D52 (a)): the three runtimes report it `Proven`. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_wrapDisabledWithholds :
    ¬ VER_018 refSESearch refSETrap refSECheckInd refSEPhase ver018_wrapDisabledWithholds := by
  intro h
  have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ver018_names [] .disabled (Or.inr rfl)
  cases this

/-- A hand-over that reports the bare `unsat` as a proof, whatever the certificate check says. -/
def ver018_wrapBareUnsat : SEWrap := fun nm o c =>
  match o with
  | .proven _ => .decided (.proven ver018_method) [] none
  | o => refSEWrap nm o c

/-- ✗ A hand-over that reports `Proven` on the bare `unsat` violates VER-018 (line 16): a proof
whose certificate check failed must be withheld. -/
@[evidence forbids VER_018]
theorem VER_018_forbids_wrapBareUnsat :
    ¬ VER_018 refSESearch refSETrap refSECheckInd refSEPhase ver018_wrapBareUnsat := by
  intro h
  obtain ⟨n, hn⟩ := (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ver018_names (.proven []) .failed).mpr
    (Or.inr ⟨rfl, Or.inl rfl⟩)
  cases hn

/-- A hand-over that reports a replayed run as unconfirmed. -/
def ver018_wrapUnconfirmed : SEWrap := fun nm o c =>
  match o with
  | .violated run _ => .decided .violated (run.map nm) none
  | o => refSEWrap nm o c

/-- ✗ A replayed run reported without `counterexampleConfirmed` `true` violates VER-018
(line 17). -/
@[evidence forbids VER_018]
theorem VER_018_forbids_wrapUnconfirmed :
    ¬ VER_018 refSESearch refSETrap refSECheckInd refSEPhase ver018_wrapUnconfirmed := by
  intro h
  have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ver018_names [0] [] .passed
  simp [ver018_wrapUnconfirmed] at this

/-! ## VER-018, the second block: where the phase sits in the pipeline

The block above is the phase when it runs. This block is the pipeline around it
(`Spec/Verifier/Pipeline.lean`): where the phase sits in the list of steps (once, after the
linear bound of [VER-015] and before the fixpoint query) and when its step is entered. It reads
the names of the pipeline's steps, in order, and the gate `seG` over the context `FBCtx` of
[VER-019]'s pipeline block (a ν match transition in the verified net, the `Ignore` policy with
environment places declared, the options of the two phases). The witness is the runtimes' step
names `rtStepNames` and their gate `refSeGate` (`smt_verifier.rs`
`flat_phases && self.state_equation_phase`, `SmtVerifier.java` `flatPhases && stateEquationPhase`,
`smt-verifier.ts` `!hasMatch && !this.ignoresEnvironment` then the phase's option). -/

/-- The step name of the linear bound ([VER-015]) in all three runtimes. -/
def ver018_lbStep : String := "linear bound"

/-- The phase is on by default (the fourth quoted sentence of the pipeline block). -/
def ver018_defaultOn : Bool := true

#guard ver018_defaultOn == true

requirement VER_018_order
  id "VER-018"
  title "State-Equation Phase with Refinement: its place in the pipeline"
  kind B
  scope "the SMT verifier's pipeline, all implementations"
  source verbatim "spec/07-verification.md"
  covers VER_018.s23, VER_018.s24, VER_018.s25, VER_018.s26
  reading "In the pipeline's step names, the linear bound comes before the state-equation phase: the list splits so that every linear-bound step is in the first part and every state-equation step in the second, and each part holds one of them."
          "In the same sense, the state-equation phase comes before the fixpoint query (the IC3/PDR query)."
          "The state-equation phase occurs exactly once in the step names."
          "The gate seG is true exactly when the verified net has no ν match transition, the policy is not Ignore with environment places declared, and the phase's option is on."
  assumes "The model is the pair (names, seG). names is the list of the pipeline's step names, in order (the names of the GStep list of Spec/Verifier/Pipeline.lean); runPipeline gives the order its meaning in a run (VER_018_order_runs). seG reads FBCtx, the context of VER-019's pipeline block. The witness is rtStepNames (the runtimes' thirteen step names) and refSeGate."
          "That the pipeline's state-equation step is entered under seG and runs the hand-over W of the first block over the phase P is the wiring this block assumes and does not state: in rtPipeline the step is still idle, and the integrator ties it when the phase's slice replaces the idle step (open item). VER_018_order_disabled takes the wiring as a premise."
          "The first quoted sentence is lines 1 to 3. 'Place' is the order of the step names (Before); in every run the steps are entered in that order, and the state-equation phase at most once (VER_018_order_runs). The runtimes run the linear bound twice, once before the enumeration route and once on the flat path; both come before the phase, and Before reads every occurrence. That the firing-bound phase comes after this phase is VER-019's order line."
          "The second quoted sentence is line 4. 'No match transition' is the nuNet flag of FBCtx; the name-coloured encoding of NU-050 applies only to such nets, so 'not on the name-coloured encoding' is the same condition. 'Not under Ignore with environment places registered' is the ignoreEnv flag, read on the net the dispatcher receives. 'Unless an earlier step has decided the query or the run has stopped' is the pipeline: a decision ends the run, and so does the stop poll before each step, with no decision (runPipeline). With this line, VER-019's pipeline block pins the firing-bound phase's gate to the runtimes' (VER_018_order_fb_gate), which closes the open item recorded there."
          "The third quoted sentence is line 4 with the option off: the gate is false, a step whose gate is false is skipped without a poll, and the run, its decision and its trail are those of the step list without the step (VER_018_order_disabled). The reports are not modelled. It is AC5."
          "The fourth quoted sentence is configuration (kind N): the constant ver018_defaultOn, pinned above."
  signoff "2026-11-13 cfe8823cc35862e7 ai"
  statement : List String → FBGate → Prop :=
    fun names seG =>
      Verifier.Before names ver018_lbStep ver019_seStep ∧
      Verifier.Before names ver019_seStep ver019_fixStep ∧
      names.count ver019_seStep = 1 ∧
      (∀ c : FBCtx, seG c = (!c.nuNet && !c.ignoreEnv && c.seOn))

/- The pinned readable form of VER-018's pipeline block. -/
/--
info: def Libpetri.Spec.VER_018_order : List String → FBGate → Prop :=
fun names seG =>
  Verifier.Before names ver018_lbStep ver019_seStep ∧
    Verifier.Before names ver019_seStep ver019_fixStep ∧
      List.count ver019_seStep names = 1 ∧ ∀ (c : FBCtx), seG c = (!c.nuNet && !c.ignoreEnv && c.seOn)
-/
#guard_msgs in #print VER_018_order

/-! ### The reference -/

/-- ✓ **The runtimes satisfy the pipeline block.** In their step list the linear bound comes
second and seventh, the state-equation phase eighth and only there, and the IC3/PDR query
twelfth; the phase is entered on the flat path with its option on. -/
@[evidence holds VER_018_order]
theorem VER_018_order_reference : VER_018_order Verifier.rtStepNames refSeGate :=
  ⟨by decide, by decide, by decide, fun _ => rfl⟩

/-- ✓ The pipeline blocks of VER-018 and VER-019 hold together: the runtimes' step list, the two
gates and the firing bound's hand-over satisfy both. -/
@[evidence consistent VER_018_order VER_019_order]
theorem VER_018_order_consistent :
    ∃ (names : List String) (seG fbG : FBGate) (W : FBWrap),
      VER_018_order names seG ∧ VER_019_order names seG fbG W :=
  ⟨_, _, _, _, VER_018_order_reference, VER_019_order_reference⟩

/-! ### What the statement says on its own -/

/-- **In every run the phase is entered in its place, and at most once**, from the statement
alone: no run enters a linear bound after the state-equation phase, the phase after the IC3/PDR
query, or the phase twice. Example: a run that enters the linear bound, the state-equation phase
and the IC3/PDR query logs them in that order, the phase once. -/
@[evidence cites "VER-018" "On the flat path, after [VER-015] and before the fixpoint query."]
theorem VER_018_order_runs {Q : Type} {steps : List (Verifier.GStep Q)} {seG : FBGate}
    (h : VER_018_order (steps.map Verifier.GStep.name) seG) {O : Verifier.Oracle}
    {stop : Verifier.Stop} {o : Verifier.Options} {q : Q} {t : Verifier.Trail}
    (ht : t.entered = []) :
    Verifier.Ordered (Verifier.runPipeline O stop o q steps t).2.entered ver018_lbStep
        ver019_seStep ∧
      Verifier.Ordered (Verifier.runPipeline O stop o q steps t).2.entered ver019_seStep
        ver019_fixStep ∧
      (Verifier.runPipeline O stop o q steps t).2.entered.count ver019_seStep ≤ 1 := by
  refine ⟨Verifier.runPipeline_ordered ht h.1, Verifier.runPipeline_ordered ht h.2.1, ?_⟩
  obtain ⟨l, hl, hs⟩ := Verifier.runPipeline_entered (O := O) (stop := stop) (o := o) (q := q)
    steps t
  rw [hl, ht, List.nil_append, ← h.2.2.1]
  exact hs.count_le _

/-- **A disabled phase changes nothing**, from the statement alone: when the state-equation step
is entered under the gate `seG` and the phase's option is off, a run of the pipeline is the run of
the list without that step. Example: on the join with the phase off, the verdict and the steps
entered are those of the pipeline that never had the phase. -/
@[evidence cites "VER-018" "With the phase disabled, verdicts and reports are those of the pipeline without it."]
theorem VER_018_order_disabled {Q : Type} {names : List String} {seG : FBGate}
    (h : VER_018_order names seG) {O : Verifier.Oracle} {stop : Verifier.Stop}
    {o : Verifier.Options} {q : Q} {s : Verifier.GStep Q} {c : FBCtx}
    (hw : s.applies o q = seG c) (hoff : c.seOn = false)
    (pre post : List (Verifier.GStep Q)) (t : Verifier.Trail) :
    Verifier.runPipeline O stop o q (pre ++ s :: post) t =
      Verifier.runPipeline O stop o q (pre ++ post) t :=
  ver019_runPipeline_skip (by rw [hw, h.2.2.2 c, hoff]; simp) post pre t

/-- **The firing bound runs where this phase runs**, from this block and VER-019's pipeline
block: with the state-equation gate fixed to the flat path, the firing-bound gate is the
runtimes'. Example: with this phase off and the firing bound on, a flat net enters the firing
bound and a ν-net does not. -/
@[evidence cites "VER-019" "on exactly the queries that the state-equation phase of [VER-018] runs on"]
theorem VER_018_order_fb_gate {names : List String} {seG fbG : FBGate} {W : FBWrap}
    (h18 : VER_018_order names seG) (h19 : VER_019_order names seG fbG W) : fbG = refFbGate :=
  VER_019_order_flat_gate h19 h18.2.2.2

/-! ### Examples -/

/-- A demo pipeline over the trivial query: the linear bound steps aside, the state-equation phase
hands over the outcome `out` with the certificate answer `cert`, then the fixpoint query asks the
solver. -/
def ver018_demoSteps (out : SEOutcome) (cert : SECert) : List (Verifier.GStep Unit) :=
  [{ name := ver018_lbStep, route := .smt, run := fun _ _ => .done (.aside "no demand") },
   { name := ver019_seStep, route := .smt,
     run := fun _ _ => .done (refSEWrap ver018_names out cert) },
   { name := ver019_fixStep, route := .smt, run := fun _ _ => Verifier.demoQuery "horn" }]

/-- A run of the demo pipeline with no stop and a solver that answers `sat`. -/
def ver018_demoRun (out : SEOutcome) (cert : SECert) :
    Option (Verifier.Route × Verifier.PhaseOut) × Verifier.Trail :=
  Verifier.runPipeline Verifier.satOracle Verifier.noStop {} () (ver018_demoSteps out cert) {}

/-- ✓ **The pipeline block on worked examples.** In the runtimes' list the state-equation phase
sits once, after both linear bounds and before the IC3/PDR query. On a flat net with the option on
the phase is entered; with the option off, on a ν-net, or under `Ignore` with environment places
it is not. In a demo pipeline, a proof whose certificate check passed ends the run after two
steps with `Proven` by `state-equation` and no solver script started by the fixpoint query; a
proof whose check failed is withheld, and the IC3/PDR query runs and decides after three steps;
the run `produce, produce, produce, cancel` ends it as a confirmed `Violated`. -/
@[evidence nonvacuous VER_018_order]
theorem VER_018_order_nonvacuous :
    Verifier.Before Verifier.rtStepNames ver018_lbStep ver019_seStep ∧
    Verifier.Before Verifier.rtStepNames ver019_seStep ver019_fixStep ∧
    Verifier.rtStepNames.count ver019_seStep = 1 ∧
    refSeGate ⟨false, false, true, false⟩ = true ∧ refSeGate ⟨false, false, false, true⟩ = false ∧
    refSeGate ⟨true, false, true, true⟩ = false ∧ refSeGate ⟨false, true, true, true⟩ = false ∧
    (ver018_demoRun (.proven []) .passed).2.entered = [ver018_lbStep, ver019_seStep] ∧
    (ver018_demoRun (.proven []) .passed).2.started = [] ∧
    (ver018_demoRun (.proven []) .passed).1 =
      some (.smt, .decided (.proven "state-equation") [] none) ∧
    (ver018_demoRun (.proven []) .failed).2.entered =
      [ver018_lbStep, ver019_seStep, ver019_fixStep] ∧
    (ver018_demoRun (.proven []) .failed).1 = some (.smt, .decided (.proven "IC3/PDR") [] none) ∧
    (ver018_demoRun (.violated [0, 0, 0, 4] []) .passed).1 =
      some (.smt, .decided .violated ["produce", "produce", "produce", "cancel"] (some true)) :=
  ⟨by decide, by decide, by decide, rfl, rfl, rfl, rfl, by decide, by decide, rfl, by decide, rfl,
    rfl⟩

/-! ### Violations -/

/-- A step list with the state-equation phase before the linear bound. -/
def ver018_seFirst : List String :=
  [ver019_seStep, ver018_lbStep, ver019_fbStep, ver019_witStep, ver019_fixStep]

/-- ✗ A pipeline that runs the phase before the linear bound violates VER-018's pipeline block
(line 1). -/
@[evidence forbids VER_018_order]
theorem VER_018_order_forbids_seFirst : ¬ VER_018_order ver018_seFirst refSeGate := by
  intro h
  exact absurd h.1 (by decide)

/-- A step list with the state-equation phase after the fixpoint query. -/
def ver018_seLate : List String := [ver018_lbStep, ver019_fixStep, ver019_seStep]

/-- ✗ A pipeline that runs the phase after the fixpoint query violates VER-018's pipeline block
(line 2): the query would decide first, and the phase could never spare it. -/
@[evidence forbids VER_018_order]
theorem VER_018_order_forbids_seLate : ¬ VER_018_order ver018_seLate refSeGate := by
  intro h
  exact absurd h.2.1 (by decide)

/-- A step list that runs the phase twice. -/
def ver018_seTwice : List String :=
  [ver018_lbStep, ver019_seStep, ver019_fbStep, ver019_seStep, ver019_fixStep]

/-- ✗ A pipeline that runs the phase a second time violates VER-018's pipeline block (line 3). -/
@[evidence forbids VER_018_order]
theorem VER_018_order_forbids_seTwice : ¬ VER_018_order ver018_seTwice refSeGate := by
  intro h
  exact absurd h.2.2.1 (by decide)

/-- A gate that ignores the phase's option. -/
def ver018_gateNoOption : FBGate := fun c => !c.nuNet && !c.ignoreEnv

/-- ✗ A phase that runs although it is disabled violates VER-018's pipeline block (line 4). -/
@[evidence forbids VER_018_order]
theorem VER_018_order_forbids_gateNoOption :
    ¬ VER_018_order Verifier.rtStepNames ver018_gateNoOption := by
  intro h
  exact absurd (h.2.2.2 ⟨false, false, false, false⟩) (by decide)

/-- A gate that also enters the phase on a ν-net. -/
def ver018_gateOnNu : FBGate := fun c => !c.ignoreEnv && c.seOn

/-- ✗ A phase that runs on a net with match transitions violates VER-018's pipeline block
(line 4): the flat encoding is name-blind there, and [VER-012] and [NU-053] are its exact
routes. -/
@[evidence forbids VER_018_order]
theorem VER_018_order_forbids_gateOnNu : ¬ VER_018_order Verifier.rtStepNames ver018_gateOnNu := by
  intro h
  exact absurd (h.2.2.2 ⟨true, false, true, false⟩) (by decide)

/-- A gate that also enters the phase under `Ignore` with environment places. -/
def ver018_gateUnderIgnore : FBGate := fun c => !c.nuNet && c.seOn

/-- ✗ A phase that runs under `Ignore` with environment places violates VER-018's pipeline block
(line 4): [VER-006] refuses every `Proven` there. -/
@[evidence forbids VER_018_order]
theorem VER_018_order_forbids_gateUnderIgnore :
    ¬ VER_018_order Verifier.rtStepNames ver018_gateUnderIgnore := by
  intro h
  exact absurd (h.2.2.2 ⟨false, true, true, false⟩) (by decide)

end Libpetri.Spec
