import Libpetri.Spec.Req.VER_014
import Libpetri.Spec.GlossaryTime

set_option linter.missingDocs true

/-!
# VER-002: Safety properties (`spec/07-verification.md`)

Two blocks, one per kind of claim the section makes.

* `VER_002` (kind F): when a marking violates each property. It is a predicate over a pair
  `(S, V)`: `S : StrandRel N` is the rest-set reading of [VER-014] (the same variable VER-014's
  statement fixes), and `V : SafetyViolRel N` is the violation reading: `V noReap X φ m` says the
  marking `m` of the timed net `X` violates the property `φ`, with `noReap` the option
  `assumeNoReaping`. `DeadlockFree` reads `S` for every list of conditional declarations, so
  VER-002 and VER-014 together fix it (`VER_002_deadlock_agree`). Quiescence is `VerQuiescent`:
  every transition the marking enables is reapable (its timing is `Deadline` or `Window`,
  glossary `Reapable`), and under `assumeNoReaping` no transition is enabled. The witness pair is
  `refStrand` and `refSafetyViol`, which reads `DeadlockFree` and `TerminatesAtSink` through
  VER-014's reference violations `refRestViol`, `MutualExclusion` through the encoder model's
  named reading `Seam.NTwoMarked`, and `QuiescentCount` with each place counted once
  (`Seam.ncount`), as every runtime counts it. Wrong readings: plain quiescence (the reaped rest
  of AC11 missed), a quiescence that ignores the option, a quiescence that counts `Exact` as
  reapable, a `DeadlockFree` that ignores the conditional declarations, a `DeadlockFree`
  satisfied by any marked sink, a `TerminatesAtSink` that needs every sink, an all-marked or
  set-valued `MutualExclusion`, marking properties that read quiescence, an off-by-one
  `PlaceBound`, an any-marked `Unreachable`, a `QuiescentCount` without quiescence, one without
  its waiver, one with a waiver on the upper bound and one that sums a place listed twice twice.
* `VER_002_count` (kind B): the `QuiescentCount` constructor. A negative or fractional `min`, a
  fractional `max`, or a `max` below `min`, is rejected where the constructor function is called; a whole
  `min ≥ 0` with an unbounded or whole `max ≥ min` builds the property. Witness:
  `refCountBuild`. Wrong builders: one that accepts `max < min` (the Rust struct literal skips the
  check), one that floors a fractional `min`, one that floors a fractional `max`, one that needs
  `max > min`.

`VER_002_reference_violates` ties the witness to the conformance reference: with no waiver, no
conditional declaration and no repeated place, on a net whose `reapable` flags are its timing
variants, `refSafetyViol` at `noReap = false` is `Reference.Violates`.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The model -/

/-- A [VER-002] property by place name. `deadlockFree sinks cond` carries the conditional sink
declarations of [VER-014]; `quiescentCount places min max waivedBy` has `max = none` for an
unbounded upper bound. `NameAligned` and `QuiescentNameAligned` read token names and are
[NU-055]'s, so they are not constructors here. -/
inductive VerProp (N : Type) where
  /-- `DeadlockFree`, with its declared sinks and conditional sink declarations. -/
  | deadlockFree (sinks : List N) (cond : List (CondSinks N))
  /-- `TerminatesAtSink`, with its declared sinks. -/
  | terminatesAtSink (sinks : List N)
  /-- `MutualExclusion` over a list of places (pairwise). -/
  | mutualExclusion (places : List N)
  /-- `PlaceBound(place, k)`. -/
  | placeBound (place : N) (k : Nat)
  /-- `Unreachable(places)`. -/
  | unreachable (places : List N)
  /-- `QuiescentCount(places, min, max, waivedBy)`; `max = none` is unbounded. -/
  | quiescentCount (places : List N) (min : Nat) (max : Option Nat) (waivedBy : List N)

/-- A violation reading of the [VER-002] properties: `V noReap X φ m` says the marking `m` of the
timed net `X` violates `φ`, with `noReap` the option `assumeNoReaping`. -/
abbrev SafetyViolRel (N : Type) : Type :=
  Bool → TimedNet N → VerProp N → CountMarking N → Prop

/-- **Quiescent** ([VER-002]): every transition the marking enables is reapable ([TIME-013]:
timing `Deadline` or `Window`); under `assumeNoReaping` (`noReap = true`), no transition is
enabled. -/
def VerQuiescent {N : Type} (noReap : Bool) (X : TimedNet N) (m : CountMarking N) : Prop :=
  ∀ t ∈ X.net.transitions, Enabled t m → noReap = false ∧ Reapable X t

/-- The reference violations. `DeadlockFree` and `TerminatesAtSink` are VER-014's `refRestViol`
at the quiescence `VerQuiescent noReap X` (`TerminatesAtSink` with no declaration, which it
ignores anyway); `MutualExclusion` is the encoder model's named reading `NTwoMarked`;
`QuiescentCount` sums each place once (`ncount`, the runtimes' `tokens_across`). -/
def refSafetyViol {N : Type} [DecidableEq N] : SafetyViolRel N := fun noReap X φ m =>
  match φ with
  | .deadlockFree sinks cond => refRestViol (VerQuiescent noReap X) .deadlockFree sinks cond m
  | .terminatesAtSink sinks => refRestViol (VerQuiescent noReap X) .terminatesAtSink sinks [] m
  | .mutualExclusion ps => NTwoMarked ps m
  | .placeBound p k => k < m p
  | .unreachable ps => ∀ p ∈ ps, m p ≠ 0
  | .quiescentCount ps lo hi w =>
    VerQuiescent noReap X m ∧
      ((ncount ps m < lo ∧ ∀ v ∈ w, m v = 0) ∨ ∃ h, hi = some h ∧ h < ncount ps m)

#spec_witness refSafetyViol

/-! ## VER-002 (F): the violation predicate -/

requirement VER_002
  id "VER-002"
  title "Safety Properties"
  kind F
  scope "every route that decides DeadlockFree, TerminatesAtSink, MutualExclusion, PlaceBound, Unreachable or QuiescentCount, all implementations (SHOULD; the shall sentences bind an implementation that offers the property)"
  source verbatim "spec/07-verification.md"
  quote "A marking is **quiescent** when every transition whose enablement check passes on it is reapable."
        "\"All transitions disabled\" in the error conditions below means \"every transition that is not reapable is disabled\"."
        "Without a conditional sink declaration ([VER-014]), the error condition is: (all transitions disabled) ∧ (some marked place is not a declared sink)."
        "The error condition is: (all transitions disabled) ∧ (no sink place has a token)."
        "Over a list of places the property is **pairwise**: violated iff some two entries of the list, at different positions, hold a token at once, which is the conjunction of `MutualExclusion(pi, pj)` over every pair."
        "A place listed twice pairs with itself, so `MutualExclusion(p, p)` is violated by any token in `p`; a list of fewer than two entries is never violated."
        "**PlaceBound(place, k)**: place never has more than k tokens"
        "**Unreachable(places)**: the given set of places is never all simultaneously non-empty."
        "The set is assumed non-empty: the property is not specified over an empty one."
        "The error condition is: (all transitions disabled) ∧ ((Σ < min ∧ every `waivedBy` place empty) ∨ Σ > max)."
        "A place listed twice in `places` is counted once."
        "The marking properties (`PlaceBound`, `Unreachable`, `MutualExclusion`) do not read quiescence, and their scripts do not depend on the option."
        "The verifier *shall* read a marking as quiescent exactly when every transition whose enablement check ([NU-020]) passes on it is reapable, and, under `assumeNoReaping`, exactly when no transition's enablement check passes on it."
        "*When* the verifier decides `DeadlockFree`, it *shall* report a marking as a violation exactly when the marking is quiescent and some marked place of it is stranded in the sense of [VER-014]."
        "*When* the verifier decides `TerminatesAtSink`, it *shall* report a marking as a violation exactly when the marking is quiescent and no declared sink holds a token."
        "*When* the verifier decides `MutualExclusion` over a list of places, it *shall* report a marking as a violation exactly when two entries of the list, at different positions, hold a token."
        "*When* the verifier decides `PlaceBound(place, k)`, it *shall* report a marking as a violation exactly when the place holds more than `k` tokens."
        "*When* the verifier decides `Unreachable` over a non-empty list of places, it *shall* report a marking as a violation exactly when every listed place holds a token."
        "*When* the verifier decides `QuiescentCount(places, min, max, waivedBy)`, it *shall* report a marking as a violation exactly when the marking is quiescent and either the tokens across `places`, each place counted once, number fewer than `min` while every `waivedBy` place is empty, or they number more than a bounded `max`."
  reading "For every rest-set reading S (the variable VER-014's statement fixes) and violation reading V, option value noReap (assumeNoReaping), timed net X and marking m, with quiescent meaning VerQuiescent noReap X m (every transition m enables is reapable, and under assumeNoReaping none is enabled):"
          "m violates DeadlockFree(sinks, cond), for every list cond of conditional declarations, exactly when m is quiescent and some place marked in m is stranded under S for sinks and cond;"
          "m violates TerminatesAtSink(sinks) exactly when m is quiescent and no place of sinks is marked in m;"
          "m violates MutualExclusion(ps) exactly when two positions i < j of ps hold places that are both marked in m, whatever the option;"
          "m violates PlaceBound(p, k) exactly when p holds more than k tokens in m, whatever the option;"
          "for a non-empty ps, m violates Unreachable(ps) exactly when every place of ps is marked in m, whatever the option;"
          "m violates QuiescentCount(ps, min, max, waivedBy) exactly when m is quiescent and either the sum of m over the distinct places of ps is below min while no waivedBy place is marked, or max is bounded and the sum is above it."
  assumes "A marking is a count marking by place name (N → Nat) of the verified net: the net after VER-001's inert places, VER-004's in-flight split and EXEC-042's terminal rewrite, which is how the verifier reads the user's net. How the user's net becomes the verified net is those requirements' subject. Whether a violating marking is reachable, and so the verdict, is VER-003's (the block VER_003); this block fixes only the predicate a route asks of one marking."
          "Reapable is the timing variant (ruling D2): glossary Reapable X t, Deadline or Window, read from the timed net X, so Delayed, Exact and Immediate transitions are never reapable here. The conformance reference's Reference.Trans carries a reapable flag of its own; VER_002_reference_violates states the agreement on a net whose flags are the timing variants. The quiescence paragraph's account of why (a late executor reaps and rests, TIME-013, Lean ReapingVsUntimed.reaping_refutes_ver004_ac3 and ReapAware.rest_sound) and 'On a net without a reapable transition this is the plain reading' (VER_002_no_reapable) are cited, not lines."
          "The option is the Bool noReap. 'An implementation MUST offer an opt-out, assumeNoReaping (assume_no_reaping), that assumes an on-time executor' and 'It restores the plain quiescence' are the quiescence reading under noReap = true; that Route B's graph keeps its strong semantics under it is the Route B paragraph's and is stated by no block: VER_012 does not model the timed layer, and NU_050_timed's lines hold of Route B's timed semantics with and without the latest-bound relaxation (Timing.relaxLate), so they do not tell the two apart. The three report MUSTs (the verdict assumes no transition is reaped and an on-time executor; the reapable transitions are named; the transitions whose latest bound Route B dropped are named) are report text (kind Q), not lines here."
          "Quiescence under modelled injection (an environment place, VER-006) is not this reading: ruling D49 (a) gives VER-006 its own definition, so the model here has no injection. The quoted sentences read quiescence through the enablement check (glossary Enablement check), which for a transition with a match specification ([NU-020]) also needs a name every correlated input holds enough tokens of (ruling D30); the glossary's Enabled is the count-level part only. Reference.Trans carries no match specification, so on the model the enablement check is the count-level check and the lines are the reading of a net without a matched transition (clash nu-b#8); the ν reading of quiescence, where a join with the counts but no shared name does not stop a marking from being quiescent, is NU-040's and NU-053's (NU-053 line 1, encode_coloured_quiescent)."
          "DeadlockFree reads VER-014's rest set: line 1 takes the rest-set reading S that VER-014's statement fixes and holds for every list of conditional declarations, so which marked place is stranded is VER-014's line 1 and VER-002 adds the quiescence. Taken alone VER-002 leaves S open; with VER-014, DeadlockFree is VER-014's violation reading at VER-002's quiescence (VER_002_deadlock_agree), and the two blocks hold together of refStrand, refRestViol and refSafetyViol (VER_002_014_consistent). A reading that ignores the declarations is killed at the reference rest set (VER_002_forbids_ignoreCond) and with every pair that satisfies VER-014 (VER_002_joint_forbids_ignoreCond)."
          "With no conditional declaration a place is stranded exactly when it is not a declared sink (VER-014 line 1), so 'Without a conditional sink declaration ([VER-014]), the error condition is: (all transitions disabled) ∧ (some marked place is not a declared sink)' is VER_002_deadlock_nil, a consequence of line 1 and VER-014's line 1. The bullet's 'no reachable quiescent marking exists where a token is stranded' is the verdict over the reachable markings, VER-003's (the block VER_003)."
          "Unreachable over an empty list is not specified (ruling D88 (a)), as the bullet's 'The set is assumed non-empty: the property is not specified over an empty one' says: line 5 assumes a non-empty list, and the conformance corpus holds no empty Unreachable. Line 5 is checked by VER_002_nonvacuous_marking, and an any-marked Unreachable is killed (VER_002_forbids_unreachAny); line 4 is checked by the same theorem, and an off-by-one PlaceBound is killed (VER_002_forbids_boundLe). MutualExclusion's 'An implementation MAY accept exactly two places' is the API (kind N); a list of two is MutualExclusion(p1, p2) by line 3 (VER_002_mutex_pair). 'A linear route ([VER-015]) proves a list of three or more pair by pair' is VER-015's. The pairwise MUST ('Every route and encoder of an implementation that accepts a list MUST read it this way ... whose SMT term stays (and (>= m_p1 1) (>= m_p2 1))') is line 3 for the predicate and VER_002_encoding (Seam.pairMarkedBad_iff) for the flat encoder; the script text is kind Q."
          "QuiescentCount: 'A place listed twice in places is counted once' is a sentence this migration adds (clash ver-a#8, D20): every runtime counts it once and the reference witness uses Seam.ncount. 'max MAY be unbounded' is max = none. 'An unbounded max MUST contribute no upper-bound clause to the encoding and MUST render without an upper bound in the report' is the script and the report (kind Q); for the predicate, max = none gives no upper-bound violation (line 6). The min and max construction MUST is the VER_002_count block. 'min = 0 with max unbounded holds on every marking' is VER_002_count_trivial, a consequence of line 6; the MAY skip and the SHOULD report are report text (Q). With a designed-terminal marker as waiver (VER-014) the sentence is line 6 with the marker in waivedBy."
          "'The marking properties (PlaceBound, Unreachable, MutualExclusion) do not read quiescence, and their scripts do not depend on the option' is lines 3, 4 and 5, which hold whatever the option and the net: VER_002_nonvacuous_marking reports a PlaceBound and an Unreachable violation at a marking that is not quiescent, and marking properties conjoined with quiescence are killed (VER_002_forbids_markingQuiescent). The scripts are kind Q. The quiescence conjunct of QuiescentCount is load-bearing as well: a QuiescentCount that does not read quiescence is killed (VER_002_forbids_countNoQuiescent)."
          "NameAligned and QuiescentNameAligned read token names and only Route B decides them: they are NU-055's blocks, not constructors of VerProp. The two-sink paragraph ('invert on the empty marking') is VER_002_inversion and VER_002_nonvacuous_sinks, consequences of lines 1 and 2."
          "The 'Every route reads this one quiescence' paragraph and the Route B paragraph (the encoders leave a reapable transition out of Bad's quiescence clause; graph routes rest when every enabled transition is reapable; Route B drops latest bounds by Late.relax, sound by Late.late_run_sound; no priority pruning with a reapable transition; VER-020 does not decide a net with a reapable transition; VER-022 reads the same quiescence) are about routes. The pipeline model (Verifier/Pipeline.lean, the block VER_003) does not state them route by route; VER_020_guard refuses a structural Proven with a reapable transition unless assumeNoReaping is set, NU_050_timed reads Route B's timed semantics on the relaxed net (Timing.relaxLate) as well, and the rest rests on the cited Lean facts. On the flat encoder, the marking properties' Bad equals line 3, 4 and 5 on covered markings (VER_002_encoding, from the Seam theorems)."
          "AC1 (each property can be constructed and passed to the verifier) is the VerProp constructors and the VER_002_count block; the API shape is kind N. AC2 (properties are verified against the net's reachable state space) is VER-003's (the block VER_003)."
          "AC3 and AC4 (DeadlockFree: a marked sink beside a token in a non-sink place is a violation; the empty quiescent marking is not, with or without sinks) are line 1, checked by VER_002_nonvacuous_sinks (and, with a conditional declaration, by VER_002_nonvacuous_cond); a DeadlockFree that any marked sink satisfies is killed (VER_002_forbids_anySink). AC5 and AC6 (TerminatesAtSink: a marking that marks any declared sink is not a violation; the empty quiescent marking is when a sink is declared) are line 2, checked by VER_002_nonvacuous_sinks; a TerminatesAtSink that needs every sink marked is killed (VER_002_forbids_everySink)."
          "AC7 (every route decides the same predicate; the SMT route and the ν graph route agree on every marking both classify) is about routes: VER_003 bounds the verdict of every route by the one violation reading V (VER_003_joint holds it together with this block), and NU-053 and VER-012 cover the ν graph; this block gives the one predicate, and VER_002_encoding ties the flat encoder's Bad for the marking properties to it."
          "AC8 (QuiescentCount below min with no waiver marked is a violation, above max is one whether or not a waiver is marked, below min with a waiver marked is not) is line 6, checked by VER_002_nonvacuous_count; a lower bound that ignores the waiver is killed (VER_002_forbids_noWaiver), so is a waiver on the upper bound (VER_002_forbids_waiverOnMax), and so is a sum that counts a repeated place twice (VER_002_forbids_listSum)."
          "AC9 (a negative or non-integral min, or a max below min, rejected at construction) is the VER_002_count block; its second sentence (two implementations given the same unbounded max emit the same script) is the script (kind Q)."
          "AC10 (MutualExclusion pairwise on every route) is line 3 at the marking level, checked by VER_002_nonvacuous_mutex on its markings: [c, a, b] with a and b marked violates, [a, b, c] with one place marked does not, [c, c] with c marked violates and [c] never does. The all-marked reading and a set-valued reading are killed (VER_002_forbids_allMarked, VER_002_forbids_mutexDedup). The verdicts and traces on the four route setups are verdicts on fixed nets, which no block states (VER_003 bounds every verdict and fixes none), and the conformance suite's (Q)."
          "AC11 (reap-quiescence: on p0 → t → p1 with t at window(3, 5), the initial marking violates DeadlockFree and TerminatesAtSink; under assumeNoReaping it does not) is the quiescence reading, checked at the initial marking by VER_002_nonvacuous_reap; plain quiescence is killed (VER_002_forbids_strict), so is a quiescence that ignores the option (VER_002_forbids_ignoreOption), and so is a quiescence that counts an Exact transition as reapable, Route B's drop-latest predicate Timing.hasDeadline (VER_002_forbids_exactReapable, on p0 → t → p1 with t at exact(3)). The empty trace, the per-route runs, the HORN clause leaving t out and the unchanged PlaceBound script are the routes' and the scripts' (kind Q)."
          "AC12 (a shadowed reapable transition: with an immediate u: p0 → p1 added the net is DeadlockFree Proven) is the quiescence reading at the initial marking, checked by VER_002_nonvacuous_reap: u is enabled and not reapable, so the marking is not quiescent. AC13 (the self-loop at window(3, 5) is violated with the empty trace, never Proven by the structural route) is checked at its initial marking by VER_002_nonvacuous_reap; the structural route's refusal is VER-020's (the block VER_020_guard: no structural Proven with a reapable transition unless assumeNoReaping is set)."
          "AC14 and AC15 (Route B reaps a join and reads a late executor, the report names the dropped bounds) and AC16 (every quiescence route: the firing bound, the VER-018 phase and Route A) are about routes and reports: Route B and its Late.relax graph are VER-012's and NU-050's, the phases VER-018's and VER-019's, Route A NU-053's; the report text is kind Q."
          "The Implementation notes (the per-language QuiescentCount entry points and their representation of an unbounded max; Java and Rust SHOULD use an absent optional) are the API (kind N). Rust's QuiescentCount is a public enum variant, so a struct literal bypasses the constructor's check; VER_002_count states the constructor."
  signoff "2026-11-13 8431b8ffece95a89 ai"
  statement : ∀ {N : Type} [DecidableEq N], StrandRel N → SafetyViolRel N → Prop :=
    fun S V =>
      (∀ noReap X sinks cond m, V noReap X (.deadlockFree sinks cond) m ↔
        VerQuiescent noReap X m ∧ ∃ p, Marked m p ∧ S sinks cond m p) ∧
      (∀ noReap X sinks m, V noReap X (.terminatesAtSink sinks) m ↔
        VerQuiescent noReap X m ∧ ∀ s ∈ sinks, ¬ Marked m s) ∧
      (∀ noReap X ps m, V noReap X (.mutualExclusion ps) m ↔
        ∃ (i j : Nat) (p q : _), i < j ∧ ps[i]? = some p ∧ ps[j]? = some q ∧
          Marked m p ∧ Marked m q) ∧
      (∀ noReap X p k m, V noReap X (.placeBound p k) m ↔ k < TokenCount m p) ∧
      (∀ noReap X ps m, ps ≠ [] → (V noReap X (.unreachable ps) m ↔ ∀ p ∈ ps, Marked m p)) ∧
      (∀ noReap X ps lo hi w m, V noReap X (.quiescentCount ps lo hi w) m ↔
        VerQuiescent noReap X m ∧
          (((ps.dedup.map m).sum < lo ∧ ∀ v ∈ w, ¬ Marked m v) ∨
            ∃ h, hi = some h ∧ h < (ps.dedup.map m).sum))

/- The pinned readable form of VER-002: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_002 : {N : Type} → [DecidableEq N] → StrandRel N → SafetyViolRel N → Prop :=
fun {N} [DecidableEq N] S V =>
  (∀ (noReap : Bool) (X : TimedNet N) (sinks : List N) (cond : List (CondSinks N)) (m : CountMarking N),
      V noReap X (VerProp.deadlockFree sinks cond) m ↔ VerQuiescent noReap X m ∧ ∃ p, Marked m p ∧ S sinks cond m p) ∧
    (∀ (noReap : Bool) (X : TimedNet N) (sinks : List N) (m : CountMarking N),
        V noReap X (VerProp.terminatesAtSink sinks) m ↔ VerQuiescent noReap X m ∧ ∀ s ∈ sinks, ¬Marked m s) ∧
      (∀ (noReap : Bool) (X : TimedNet N) (ps : List N) (m : CountMarking N),
          V noReap X (VerProp.mutualExclusion ps) m ↔
            ∃ i j p q, i < j ∧ ps[i]? = some p ∧ ps[j]? = some q ∧ Marked m p ∧ Marked m q) ∧
        (∀ (noReap : Bool) (X : TimedNet N) (p : N) (k : ℕ) (m : CountMarking N),
            V noReap X (VerProp.placeBound p k) m ↔ k < TokenCount m p) ∧
          (∀ (noReap : Bool) (X : TimedNet N) (ps : List N) (m : CountMarking N),
              ps ≠ [] → (V noReap X (VerProp.unreachable ps) m ↔ ∀ p ∈ ps, Marked m p)) ∧
            ∀ (noReap : Bool) (X : TimedNet N) (ps : List N) (lo : ℕ) (hi : Option ℕ) (w : List N) (m : CountMarking N),
              V noReap X (VerProp.quiescentCount ps lo hi w) m ↔
                VerQuiescent noReap X m ∧
                  (((List.map m ps.dedup).sum < lo ∧ ∀ v ∈ w, ¬Marked m v) ∨
                    ∃ h, hi = some h ∧ h < (List.map m ps.dedup).sum)
-/
#guard_msgs in #print VER_002

/-! ## The reference -/

/-- Two marked entries at different positions, as a filter length. -/
theorem ver002_two_le_filter_iff {N : Type} (f : N → Bool) : ∀ ps : List N,
    2 ≤ (ps.filter f).length ↔
      ∃ (i j : Nat) (p q : N), i < j ∧ ps[i]? = some p ∧ ps[j]? = some q ∧ f p = true ∧
        f q = true
  | [] => by simp
  | a :: ps => by
    have ih := ver002_two_le_filter_iff f ps
    constructor
    · intro h
      by_cases ha : f a = true
      · have h1 : 0 < (ps.filter f).length := by
          simp only [List.filter_cons, ha, if_true, List.length_cons] at h; omega
        obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos h1
        obtain ⟨hxm, hxf⟩ := List.mem_filter.mp hx
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hxm
        exact ⟨0, j + 1, a, x, by omega, by simp, by simpa using hj, ha, hxf⟩
      · have : 2 ≤ (ps.filter f).length := by
          simpa [List.filter_cons, ha] using h
        obtain ⟨i, j, p, q, hij, hi', hj', hp, hq⟩ := ih.mp this
        exact ⟨i + 1, j + 1, p, q, by omega, by simpa using hi', by simpa using hj', hp, hq⟩
    · rintro ⟨i, j, p, q, hij, hi', hj', hp, hq⟩
      cases j with
      | zero => omega
      | succ j =>
        have hqm : q ∈ ps.filter f :=
          List.mem_filter.mpr ⟨List.mem_iff_getElem?.mpr ⟨j, by simpa using hj'⟩, hq⟩
        cases i with
        | zero =>
          have ha : f a = true := by
            have : a = p := by simpa using hi'
            rw [this]; exact hp
          have := List.length_pos_of_mem hqm
          simp only [List.filter_cons, ha, if_true, List.length_cons]; omega
        | succ i =>
          have : 2 ≤ (ps.filter f).length :=
            ih.mpr ⟨i, j, p, q, by omega, by simpa using hi', by simpa using hj', hp, hq⟩
          by_cases ha : f a = true
          · simp only [List.filter_cons, ha, if_true, List.length_cons]; omega
          · simpa [List.filter_cons, ha] using this

/-- The encoder model's named `MutualExclusion` is the positional reading of line 3. -/
theorem ver002_nTwoMarked_iff {N : Type} [DecidableEq N] (ps : List N) (m : N → Nat) :
    NTwoMarked ps m ↔
      ∃ (i j : Nat) (p q : N), i < j ∧ ps[i]? = some p ∧ ps[j]? = some q ∧ Marked m p ∧
        Marked m q := by
  unfold NTwoMarked
  rw [ver002_two_le_filter_iff]
  simp only [decide_eq_true_eq, Marked]
  constructor
  · rintro ⟨i, j, p, q, h1, h2, h3, h4, h5⟩; exact ⟨i, j, p, q, h1, h2, h3, by omega, by omega⟩
  · rintro ⟨i, j, p, q, h1, h2, h3, h4, h5⟩; exact ⟨i, j, p, q, h1, h2, h3, by omega, by omega⟩

/-- With no conditional declaration a place may rest exactly where a sink is declared. -/
theorem ver002_resting_nil {N : Type} [DecidableEq N] (sinks : List N) (m : N → Nat) (p : N) :
    Resting sinks [] m p ↔ p ∈ sinks := by
  simp [Resting, IsMarker]

/-- ✓ VER-014's reference rest set and the reference violations satisfy VER-002. -/
@[evidence holds VER_002]
theorem VER_002_reference {N : Type} [DecidableEq N] :
    VER_002 (refStrand (N := N)) refSafetyViol := by
  refine ⟨fun _ _ _ _ _ => Iff.rfl, fun nr X sinks m => ?_, fun nr X ps m => ?_,
    fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun nr X ps lo hi w m => ?_⟩
  · simp only [refSafetyViol, refRestViol, Marked, ne_eq, not_not]
  · exact ver002_nTwoMarked_iff ps m
  · simp only [refSafetyViol, ncount, Marked, ne_eq, not_not]

/-! ## Ties to VER-014, the conformance reference and the encoder -/

/-- The reference reads `DeadlockFree` and `TerminatesAtSink` through VER-014's reference
violations at its own quiescence, conditional declarations included: one rest set for both
requirements. -/
theorem VER_002_rest_agree {N : Type} [DecidableEq N] (noReap : Bool) (X : TimedNet N)
    (sinks : List N) (cond : List (CondSinks N)) (m : N → Nat) :
    (refSafetyViol noReap X (.deadlockFree sinks cond) m ↔
      refRestViol (VerQuiescent noReap X) .deadlockFree sinks cond m) ∧
    (refSafetyViol noReap X (.terminatesAtSink sinks) m ↔
      refRestViol (VerQuiescent noReap X) .terminatesAtSink sinks cond m) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ✓ VER-014 and VER-002 hold together of one rest set: VER-014's reference pair and the
reference violations satisfy both. -/
@[evidence consistent VER_014 VER_002]
theorem VER_002_014_consistent {N : Type} [DecidableEq N] :
    ∃ (S : StrandRel N) (R : RestViolRel N) (V : SafetyViolRel N), VER_014 S R ∧ VER_002 S V :=
  ⟨refStrand, refRestViol, refSafetyViol, VER_014_reference, VER_002_reference⟩

/-- **VER-002 and VER-014 together fix `DeadlockFree`.** For every pair `(S, R)` that satisfies
VER-014 and every `V` that satisfies VER-002 with the same `S`, `V`'s `DeadlockFree` is `R`'s at
VER-002's quiescence, conditional declarations included. -/
theorem VER_002_deadlock_agree {N : Type} [DecidableEq N] {S : StrandRel N} {R : RestViolRel N}
    {V : SafetyViolRel N} (hS : VER_014 S R) (hV : VER_002 S V) (noReap : Bool) (X : TimedNet N)
    (sinks : List N) (cond : List (CondSinks N)) (m : CountMarking N) :
    V noReap X (.deadlockFree sinks cond) m ↔
      R (VerQuiescent noReap X) .deadlockFree sinks cond m := by
  rw [hV.1, hS.2.1]; rfl

/-- **With no conditional declaration, `DeadlockFree` reads the declared sinks** (the bullet's
error condition): a quiescent marking violates it exactly when some marked place is not a
declared sink, for every `S` that satisfies VER-014's line 1. -/
theorem VER_002_deadlock_nil {N : Type} [DecidableEq N] {S : StrandRel N} {R : RestViolRel N}
    {V : SafetyViolRel N} (hS : VER_014 S R) (hV : VER_002 S V) (noReap : Bool) (X : TimedNet N)
    (sinks : List N) (m : CountMarking N) :
    V noReap X (.deadlockFree sinks []) m ↔
      VerQuiescent noReap X m ∧ ∃ p, Marked m p ∧ p ∉ sinks := by
  rw [hV.1]
  simp only [hS.1, List.not_mem_nil, false_implies, implies_true, and_true]

/-- On a net whose `reapable` flags are the timing variants, the conformance reference's
reap-aware quiescence is `VerQuiescent` without the option. -/
theorem ver002_reapQuiescent_iff {N : Type} [DecidableEq N] (X : TimedNet N)
    (hc : ∀ t ∈ X.net.transitions, t.reapable = (X.timing t).reapable) (m : N → Nat) :
    ReapQuiescent X.net m ↔ VerQuiescent false X m := by
  unfold ReapQuiescent VerQuiescent
  constructor
  · intro h t ht he
    exact ⟨rfl, by rw [Reapable, TimingOf, ← hc t ht]; exact h t ht he⟩
  · intro h t ht he
    rw [hc t ht]; exact (h t ht he).2

/-- **The witness is the conformance reference.** On a net whose `reapable` flags are the timing
variants, with no conditional declaration, no waiver and no repeated counted place,
`refSafetyViol` without the option is `Reference.Violates`, which decides the verdicts of the
conformance corpus. -/
theorem VER_002_reference_violates {N : Type} [DecidableEq N] (X : TimedNet N)
    (hc : ∀ t ∈ X.net.transitions, t.reapable = (X.timing t).reapable) (m : N → Nat) :
    (∀ sinks, Violates X.net (.deadlockFree sinks) m ↔
      refSafetyViol false X (.deadlockFree sinks []) m) ∧
    (∀ sinks, Violates X.net (.terminatesAtSink sinks) m ↔
      refSafetyViol false X (.terminatesAtSink sinks) m) ∧
    (∀ ps, Violates X.net (.mutualExclusion ps) m ↔ refSafetyViol false X (.mutualExclusion ps) m) ∧
    (∀ p k, Violates X.net (.placeBound p k) m ↔ refSafetyViol false X (.placeBound p k) m) ∧
    (∀ ps, Violates X.net (.unreachable ps) m ↔ refSafetyViol false X (.unreachable ps) m) ∧
    (∀ ps lo hi, ps.Nodup → (Violates X.net (.quiescentCount ps lo hi) m ↔
      refSafetyViol false X (.quiescentCount ps lo hi []) m)) := by
  have hq := ver002_reapQuiescent_iff X hc m
  refine ⟨fun sinks => ?_, fun sinks => ?_, fun ps => ?_, fun _ _ => Iff.rfl, fun _ => Iff.rfl,
    fun ps lo hi hnd => ?_⟩
  · simp only [Violates, refSafetyViol, refRestViol, ver002_resting_nil, hq]
  · simp only [Violates, refSafetyViol, refRestViol, hq]
  · simp only [Violates, refSafetyViol, NTwoMarked]
    have : (fun p => m p != 0) = (fun n => decide (1 ≤ m n)) := by
      funext n; cases m n <;> simp
    rw [this]
  · simp only [Violates, refSafetyViol, ncount, List.dedup_eq_self.mpr hnd, hq]
    simp

/-- **On a net without a reapable transition the reap-aware reading is the plain one** (the
quiescence paragraph): `VerQuiescent` does not depend on the option. -/
theorem VER_002_no_reapable {N : Type} (X : TimedNet N)
    (hnr : ∀ t ∈ X.net.transitions, ¬ Reapable X t) (m : CountMarking N) :
    VerQuiescent false X m ↔ VerQuiescent true X m := by
  unfold VerQuiescent
  constructor
  · intro h t ht he; exact absurd (h t ht he).2 (hnr t ht)
  · intro h t ht he; exact absurd (h t ht he).1 (by simp)

/-- **The encoder reads the marking properties as line 3 to 5 do** ([VER-002] AC7, flat side):
on a marking the place index covers, the flat encoder's `Bad` for `PlaceBound`, pairwise
`MutualExclusion` and (non-empty, resolved) `Unreachable` holds of the restriction exactly when
`refSafetyViol` reports the marking, whatever the option. -/
@[evidence cites "VER-002" "AC7, flat encoder side: on a marking the place index covers, the encoded Bad of PlaceBound, pairwise MutualExclusion and a non-empty resolved Unreachable holds exactly when the reference violation reading does (Seam.placeBoundBad_iff, pairMarkedBad_iff, allMarkedBad_iff)"]
theorem VER_002_encoding {N : Type} [DecidableEq N] {ix : PlaceIndex N} {m : N → Nat}
    (h : Novel.Seam.Covers ix m) (noReap : Bool) (X : TimedNet N) :
    (∀ n k, placeBoundBad ix n k (restrict ix m) = true ↔
      refSafetyViol noReap X (.placeBound n k) m) ∧
    (∀ ps, pairMarkedBad ix ps (restrict ix m) = true ↔
      refSafetyViol noReap X (.mutualExclusion ps) m) ∧
    (∀ ps, (∀ n ∈ ps, n ∈ ix.names) → ps ≠ [] →
      (allMarkedBad ix ps (restrict ix m) = true ↔ refSafetyViol noReap X (.unreachable ps) m)) := by
  refine ⟨fun n k => placeBoundBad_iff h n k, fun ps => pairMarkedBad_iff h ps,
    fun ps hres hne => ?_⟩
  rw [allMarkedBad_iff h hres hne]
  simp only [refSafetyViol]
  exact ⟨fun h1 p hp => by have := h1 p hp; omega, fun h1 p hp => by have := h1 p hp; omega⟩

/-! ## Consequences of the lines, for every reading that satisfies them -/

/-- **The sink properties invert on the empty marking**: if the empty marking is quiescent, it
does not violate `DeadlockFree` and does violate `TerminatesAtSink`, whatever the sinks and the
conditional declarations. -/
theorem VER_002_inversion {N : Type} [DecidableEq N] {S : StrandRel N} {V : SafetyViolRel N}
    (hV : VER_002 S V) (noReap : Bool) (X : TimedNet N) (sinks : List N)
    (cond : List (CondSinks N)) (hq : VerQuiescent noReap X (fun _ => 0)) :
    ¬ V noReap X (.deadlockFree sinks cond) (fun _ => 0) ∧
      V noReap X (.terminatesAtSink sinks) (fun _ => 0) := by
  refine ⟨fun h => ?_, (hV.2.1 _ _ _ _).mpr ⟨hq, fun _ _ => by simp [Marked]⟩⟩
  obtain ⟨-, p, hp, -⟩ := (hV.1 _ _ _ _ _).mp h
  exact hp rfl

/-- **`min = 0` with `max` unbounded holds on every marking.** -/
theorem VER_002_count_trivial {N : Type} [DecidableEq N] {S : StrandRel N} {V : SafetyViolRel N}
    (hV : VER_002 S V)
    (noReap : Bool) (X : TimedNet N) (ps w : List N) (m : CountMarking N) :
    ¬ V noReap X (.quiescentCount ps 0 none w) m := by
  intro h
  obtain ⟨-, ⟨hlt, -⟩ | ⟨_, hh, -⟩⟩ := (hV.2.2.2.2.2 _ _ _ _ _ _ _).mp h
  · omega
  · exact absurd hh (by simp)

/-- **A list of two is `MutualExclusion(p1, p2)`**, and a place listed twice pairs with itself:
`[p, q]` is violated exactly when both are marked (`[p, p]`: when `p` is). -/
theorem VER_002_mutex_pair {N : Type} [DecidableEq N] {S : StrandRel N} {V : SafetyViolRel N}
    (hV : VER_002 S V)
    (noReap : Bool) (X : TimedNet N) (p q : N) (m : CountMarking N) :
    V noReap X (.mutualExclusion [p, q]) m ↔ Marked m p ∧ Marked m q := by
  rw [hV.2.2.1, ← ver002_nTwoMarked_iff, NTwoMarked]
  by_cases hp : 1 ≤ m p <;> by_cases hq : 1 ≤ m q <;> simp [hp, hq, Marked] <;> omega

/-- **A list of fewer than two entries is never violated.** -/
theorem VER_002_mutex_short {N : Type} [DecidableEq N] {S : StrandRel N} {V : SafetyViolRel N}
    (hV : VER_002 S V)
    (noReap : Bool) (X : TimedNet N) (ps : List N) (hl : ps.length < 2) (m : CountMarking N) :
    ¬ V noReap X (.mutualExclusion ps) m := by
  rw [hV.2.2.1, ← ver002_nTwoMarked_iff, NTwoMarked]
  have := List.length_filter_le (fun n => decide (1 ≤ m n)) ps
  omega

/-! ## Examples on the reference: AC3 to AC6, AC8, AC10 to AC13 -/

/-- A timed net with no transition: every marking is quiescent, with or without the option. -/
def ver002_X0 : TimedNet Nat :=
  { net := { places := [], transitions := [] }, timing := fun _ => .immediate, tol := 5 }

/-- A count marking from a list of `(place, count)` pairs; unlisted places hold nothing. -/
def ver002_mk (l : List (Nat × Nat)) : Nat → Nat :=
  fun p => ((l.find? (·.1 == p)).map (·.2)).getD 0

/-- AC11's `t: p0 → p1` (places 0, 1). -/
def ver002_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- AC12's `u: p0 → p1`, `immediate`. -/
def ver002_u : Trans Nat :=
  { core := { name := "u", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- AC13's self-loop `t: a → a` (place 0). -/
def ver002_loop : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 0) }

/-- Timing: `t` at `window(3, 5)`, everything else `immediate`. -/
def ver002_timing : Trans Nat → Novel.TimedScg.Timing :=
  fun t => if t.core.name = "t" then .window 3 5 else .immediate

/-- AC11's net: `p0 → t → p1`, `t` at `window(3, 5)`. -/
def ver002_X11 : TimedNet Nat :=
  { net := { places := [0, 1], transitions := [ver002_t] }, timing := ver002_timing, tol := 5 }

/-- AC12's net: AC11's with the `immediate` `u: p0 → p1` added. -/
def ver002_X12 : TimedNet Nat :=
  { net := { places := [0, 1], transitions := [ver002_t, ver002_u] }, timing := ver002_timing,
    tol := 5 }

/-- AC13's net: the self-loop `t: a → a` at `window(3, 5)`. -/
def ver002_X13 : TimedNet Nat :=
  { net := { places := [0], transitions := [ver002_loop] }, timing := ver002_timing, tol := 5 }

theorem ver002_X0_quiescent (noReap : Bool) (m : Nat → Nat) : VerQuiescent noReap ver002_X0 m := by
  intro t ht; simp [ver002_X0] at ht

/-- AC3 to AC6 on the reference, at quiescent markings, sink `1` (`done`), non-sink `0`
(`stuck`): `{done, stuck}` violates `DeadlockFree` (AC3) and not `TerminatesAtSink` (AC5); the
empty marking violates `TerminatesAtSink` (AC6) and not `DeadlockFree`, with or without a sink
(AC4); `{done}` with the sinks `[1, 2]` does not violate `TerminatesAtSink` (AC5, any sink). -/
@[evidence nonvacuous VER_002]
theorem VER_002_nonvacuous_sinks :
    refSafetyViol false ver002_X0 (.deadlockFree [1] []) (ver002_mk [(0, 1), (1, 1)]) ∧
    ¬ refSafetyViol false ver002_X0 (.terminatesAtSink [1]) (ver002_mk [(0, 1), (1, 1)]) ∧
    ¬ refSafetyViol false ver002_X0 (.deadlockFree [1] []) (fun _ => 0) ∧
    ¬ refSafetyViol false ver002_X0 (.deadlockFree [] []) (fun _ => 0) ∧
    refSafetyViol false ver002_X0 (.terminatesAtSink [1]) (fun _ => 0) ∧
    ¬ refSafetyViol false ver002_X0 (.terminatesAtSink [1, 2]) (ver002_mk [(1, 1)]) := by
  refine ⟨⟨ver002_X0_quiescent _ _, 0, by decide, by simp [Resting, IsMarker]⟩,
    fun ⟨_, h⟩ => absurd (h 1 (by simp)) (by decide), fun ⟨_, _, h, _⟩ => h rfl,
    fun ⟨_, _, h, _⟩ => h rfl, ⟨ver002_X0_quiescent _ _, fun _ _ => rfl⟩,
    fun ⟨_, h⟩ => absurd (h 1 (by simp)) (by decide)⟩

/-- AC8 on the reference (`places = [0]`, `min = 2`, `max = 3`, `waivedBy = [9]`): one token and
no waiver marked is a violation; four tokens with the waiver marked is one; one token with the
waiver marked is not. -/
@[evidence nonvacuous VER_002]
theorem VER_002_nonvacuous_count :
    refSafetyViol false ver002_X0 (.quiescentCount [0] 2 (some 3) [9]) (ver002_mk [(0, 1)]) ∧
    refSafetyViol false ver002_X0 (.quiescentCount [0] 2 (some 3) [9])
      (ver002_mk [(0, 4), (9, 1)]) ∧
    ¬ refSafetyViol false ver002_X0 (.quiescentCount [0] 2 (some 3) [9])
      (ver002_mk [(0, 1), (9, 1)]) := by
  refine ⟨⟨ver002_X0_quiescent _ _, Or.inl ⟨by decide, by simp [ver002_mk]⟩⟩,
    ⟨ver002_X0_quiescent _ _, Or.inr ⟨3, rfl, by decide⟩⟩, ?_⟩
  rintro ⟨-, ⟨-, hw⟩ | ⟨h, hh, hlt⟩⟩
  · exact absurd (hw 9 (by simp)) (by decide)
  · cases hh; revert hlt; decide

/-- AC10 at the marking level on the reference (`s, a, b, c` = `0, 1, 2, 3`): `[c, a, b]` with
`a` and `b` marked is violated; `[a, b, c]` with only `b` marked is not; `[c, c]` with `c`
marked is violated; `[c]` with `c` marked is not. -/
@[evidence nonvacuous VER_002]
theorem VER_002_nonvacuous_mutex :
    refSafetyViol false ver002_X0 (.mutualExclusion [3, 1, 2]) (ver002_mk [(1, 1), (2, 1)]) ∧
    ¬ refSafetyViol false ver002_X0 (.mutualExclusion [1, 2, 3]) (ver002_mk [(2, 1)]) ∧
    refSafetyViol false ver002_X0 (.mutualExclusion [3, 3]) (ver002_mk [(3, 1)]) ∧
    ¬ refSafetyViol false ver002_X0 (.mutualExclusion [3]) (ver002_mk [(3, 1)]) := by
  simp only [refSafetyViol, NTwoMarked]
  decide

/-- AC11 to AC13 at the initial marking on the reference. AC11: `{p0}` violates `DeadlockFree`
and `TerminatesAtSink` (sink `p1`), only the reapable `t` being enabled, and under
`assumeNoReaping` violates neither. AC12: with the `immediate` `u` added it does not violate
`DeadlockFree`. AC13: the self-loop at `{a}` violates `DeadlockFree`, and under
`assumeNoReaping` does not. -/
@[evidence nonvacuous VER_002]
theorem VER_002_nonvacuous_reap :
    refSafetyViol false ver002_X11 (.deadlockFree [1] []) (ver002_mk [(0, 1)]) ∧
    refSafetyViol false ver002_X11 (.terminatesAtSink [1]) (ver002_mk [(0, 1)]) ∧
    ¬ refSafetyViol true ver002_X11 (.deadlockFree [1] []) (ver002_mk [(0, 1)]) ∧
    ¬ refSafetyViol true ver002_X11 (.terminatesAtSink [1]) (ver002_mk [(0, 1)]) ∧
    ¬ refSafetyViol false ver002_X12 (.deadlockFree [1] []) (ver002_mk [(0, 1)]) ∧
    refSafetyViol false ver002_X13 (.deadlockFree [] []) (ver002_mk [(0, 1)]) ∧
    ¬ refSafetyViol true ver002_X13 (.deadlockFree [] []) (ver002_mk [(0, 1)]) := by
  have q11 : VerQuiescent false ver002_X11 (ver002_mk [(0, 1)]) := by
    intro t ht _
    simp only [ver002_X11, List.mem_singleton] at ht
    subst ht; exact ⟨rfl, by decide⟩
  have q13 : VerQuiescent false ver002_X13 (ver002_mk [(0, 1)]) := by
    intro t ht _
    simp only [ver002_X13, List.mem_singleton] at ht
    subst ht; exact ⟨rfl, by decide⟩
  have nq11 : ¬ VerQuiescent true ver002_X11 (ver002_mk [(0, 1)]) := fun h =>
    absurd (h ver002_t (by simp [ver002_X11]) (by decide)).1 (by decide)
  have nq12 : ¬ VerQuiescent false ver002_X12 (ver002_mk [(0, 1)]) := fun h =>
    absurd (h ver002_u (by simp [ver002_X12]) (by decide)).2 (by decide)
  have nq13 : ¬ VerQuiescent true ver002_X13 (ver002_mk [(0, 1)]) := fun h =>
    absurd (h ver002_loop (by simp [ver002_X13]) (by decide)).1 (by decide)
  exact ⟨⟨q11, 0, by decide, by simp [Resting, IsMarker]⟩, ⟨q11, fun s hs => by
      simp at hs; subst hs; decide⟩,
    fun h => nq11 h.1, fun h => nq11 h.1, fun h => nq12 h.1,
    ⟨q13, 0, by decide, by simp [Resting, IsMarker]⟩, fun h => nq13 h.1⟩

/-- AC12's initial marking is not quiescent: the `immediate` `u` is enabled. -/
theorem ver002_X12_not_quiescent : ¬ VerQuiescent false ver002_X12 (ver002_mk [(0, 1)]) := fun h =>
  absurd (h ver002_u (by simp [ver002_X12]) (by decide)).2 (by decide)

/-- `DeadlockFree` with a conditional declaration on the reference (VER-014's rest set at VER-002's
quiescence): marker `1` with the place `0`. A token in `0` with the marker empty is a violation;
with the marker marked, both tokens rest and it is not. -/
@[evidence nonvacuous VER_002]
theorem VER_002_nonvacuous_cond :
    refSafetyViol false ver002_X0 (.deadlockFree [] [⟨1, [0]⟩]) (ver002_mk [(0, 1)]) ∧
    ¬ refSafetyViol false ver002_X0 (.deadlockFree [] [⟨1, [0]⟩]) (ver002_mk [(0, 1), (1, 1)]) := by
  refine ⟨⟨ver002_X0_quiescent _ _, 0, by decide, by simp [Resting, IsMarker, ver002_mk]⟩, ?_⟩
  rintro ⟨-, p, hp, hr⟩
  apply hr
  by_cases h1 : p = 1
  · subst h1; simp [Resting, IsMarker]
  · by_cases h0 : p = 0
    · subst h0; simp [Resting, IsMarker, ver002_mk]
    · exfalso; apply hp
      have h0' : (0 == p) = false := by simpa using Ne.symm h0
      have h1' : (1 == p) = false := by simpa using Ne.symm h1
      simp [ver002_mk, List.find?, h0', h1']

/-- Lines 4 and 5 on the reference, at AC12's initial marking `{p0}`, which is not quiescent
(the marking properties do not read quiescence): `PlaceBound(p0, 0)` is violated and
`PlaceBound(p0, 1)` is not; `Unreachable([p0, p1])` is violated when both are marked and not when
only `p0` is. -/
@[evidence nonvacuous VER_002]
theorem VER_002_nonvacuous_marking :
    ¬ VerQuiescent false ver002_X12 (ver002_mk [(0, 1)]) ∧
    refSafetyViol false ver002_X12 (.placeBound 0 0) (ver002_mk [(0, 1)]) ∧
    ¬ refSafetyViol false ver002_X12 (.placeBound 0 1) (ver002_mk [(0, 1)]) ∧
    refSafetyViol false ver002_X12 (.unreachable [0, 1]) (ver002_mk [(0, 1), (1, 1)]) ∧
    ¬ refSafetyViol false ver002_X12 (.unreachable [0, 1]) (ver002_mk [(0, 1)]) := by
  refine ⟨ver002_X12_not_quiescent, ?_⟩
  simp only [refSafetyViol]
  decide

/-! ## Wrong readings -/

/-- Plain quiescence whatever the option: no transition enabled (AC11 broken). -/
def ver002_strict {N : Type} [DecidableEq N] : SafetyViolRel N :=
  fun _ X φ m => refSafetyViol true X φ m

/-- Reap-aware quiescence whatever the option (`assumeNoReaping` ignored). -/
def ver002_ignoreOption {N : Type} [DecidableEq N] : SafetyViolRel N :=
  fun _ X φ m => refSafetyViol false X φ m

/-- A `DeadlockFree` that any marked sink satisfies (AC3 broken). -/
def ver002_anySink {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .deadlockFree sinks cond =>
    refSafetyViol nr X (.deadlockFree sinks cond) m ∧ ∀ s ∈ sinks, m s = 0
  | φ => refSafetyViol nr X φ m

/-- A `TerminatesAtSink` that needs every declared sink marked (AC5 broken). -/
def ver002_everySink {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .terminatesAtSink sinks => VerQuiescent nr X m ∧ ∃ s ∈ sinks, m s = 0
  | φ => refSafetyViol nr X φ m

/-- `MutualExclusion` as "every listed place marked", the encoder's reading before the pairwise
rule (AC10 broken). -/
def ver002_allMarked {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .mutualExclusion ps => 2 ≤ ps.length ∧ ∀ p ∈ ps, m p ≠ 0
  | φ => refSafetyViol nr X φ m

/-- `MutualExclusion` over the set of listed places: a place listed twice does not pair with
itself (AC10's `[c, c]` broken). -/
def ver002_mutexDedup {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .mutualExclusion ps => NTwoMarked ps.dedup m
  | φ => refSafetyViol nr X φ m

/-- `PlaceBound` violated already at `k` tokens. -/
def ver002_boundLe {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .placeBound p k => k ≤ m p
  | φ => refSafetyViol nr X φ m

/-- `Unreachable` violated when any listed place is marked. -/
def ver002_unreachAny {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .unreachable ps => ∃ p ∈ ps, m p ≠ 0
  | φ => refSafetyViol nr X φ m

/-- `QuiescentCount` whose waiver also waives the upper bound (AC8 broken). -/
def ver002_waiverOnMax {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .quiescentCount ps lo hi w =>
    refSafetyViol nr X (.quiescentCount ps lo hi w) m ∧ ∀ v ∈ w, m v = 0
  | φ => refSafetyViol nr X φ m

/-- `QuiescentCount` summing over the list, so a place listed twice counts twice (the
conformance reference's `Violates` before deduplication). -/
def ver002_listSum {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .quiescentCount ps lo hi w =>
    VerQuiescent nr X m ∧
      (((ps.map m).sum < lo ∧ ∀ v ∈ w, m v = 0) ∨ ∃ h, hi = some h ∧ h < (ps.map m).sum)
  | φ => refSafetyViol nr X φ m

/-- Quiescence that counts `Exact` as reapable: Route B's drop-latest predicate
`Timing.hasDeadline` (`Deadline`, `Window`, `Exact`) read as reapability. -/
def ver002_exactQuiescent {N : Type} (noReap : Bool) (X : TimedNet N) (m : CountMarking N) :
    Prop :=
  ∀ t ∈ X.net.transitions, Enabled t m → noReap = false ∧ (X.timing t).hasDeadline = true

/-- `DeadlockFree` at the quiescence that counts `Exact` as reapable. -/
def ver002_exactReapable {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .deadlockFree sinks cond => refRestViol (ver002_exactQuiescent nr X) .deadlockFree sinks cond m
  | φ => refSafetyViol nr X φ m

/-- `p0 → t → p1` with `t` at `exact(3)`. -/
def ver002_XExact : TimedNet Nat :=
  { net := { places := [0, 1], transitions := [ver002_t] }, timing := fun _ => .exact 3, tol := 5 }

/-- A `DeadlockFree` that drops the conditional sink declarations. -/
def ver002_ignoreCond {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .deadlockFree sinks _ => refSafetyViol nr X (.deadlockFree sinks []) m
  | φ => refSafetyViol nr X φ m

/-- Marking properties that read quiescence: `PlaceBound`, `Unreachable` and `MutualExclusion`
conjoined with `VerQuiescent`. -/
def ver002_markingQuiescent {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .placeBound p k => VerQuiescent nr X m ∧ refSafetyViol nr X (.placeBound p k) m
  | .unreachable ps => VerQuiescent nr X m ∧ refSafetyViol nr X (.unreachable ps) m
  | .mutualExclusion ps => VerQuiescent nr X m ∧ refSafetyViol nr X (.mutualExclusion ps) m
  | φ => refSafetyViol nr X φ m

/-- `QuiescentCount` without its quiescence conjunct. -/
def ver002_countNoQuiescent {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .quiescentCount ps lo hi w =>
    (ncount ps m < lo ∧ ∀ v ∈ w, m v = 0) ∨ ∃ h, hi = some h ∧ h < ncount ps m
  | φ => refSafetyViol nr X φ m

/-- `QuiescentCount` whose lower bound ignores the waiver (AC8's third case broken). -/
def ver002_noWaiver {N : Type} [DecidableEq N] : SafetyViolRel N := fun nr X φ m =>
  match φ with
  | .quiescentCount ps lo hi _ =>
    VerQuiescent nr X m ∧ (ncount ps m < lo ∨ ∃ h, hi = some h ∧ h < ncount ps m)
  | φ => refSafetyViol nr X φ m

/-- ✗ The quiescence reading forbids plain quiescence: AC11's initial marking, only the
reapable `t` enabled, is quiescent without the option. -/
@[evidence forbids VER_002]
theorem VER_002_forbids_strict : ¬ VER_002 refStrand (ver002_strict (N := Nat)) := by
  intro h
  have hv := (h.1 false ver002_X11 [1] [] (ver002_mk [(0, 1)])).mpr
    ⟨fun t ht _ => by simp only [ver002_X11, List.mem_singleton] at ht; subst ht; exact ⟨rfl, by decide⟩,
      0, by decide, by simp [refStrand, Resting, IsMarker]⟩
  exact absurd (hv.1 ver002_t (by simp [ver002_X11]) (by decide)).1 (by decide)

/-- ✗ The quiescence reading forbids ignoring `assumeNoReaping`: under it AC11's initial
marking, `t` enabled, is not quiescent. -/
@[evidence forbids VER_002]
theorem VER_002_forbids_ignoreOption : ¬ VER_002 refStrand (ver002_ignoreOption (N := Nat)) := by
  intro h
  have hv : ver002_ignoreOption true ver002_X11 (.deadlockFree [1] []) (ver002_mk [(0, 1)]) :=
    VER_002_nonvacuous_reap.1
  obtain ⟨hq, -⟩ := (h.1 _ _ _ _ _).mp hv
  exact absurd (hq ver002_t (by simp [ver002_X11]) (by decide)).1 (by decide)

/-- ✗ The quiescence reading forbids counting `Exact` as reapable: on `p0 → t → p1` with `t` at
`exact(3)`, the marking `{p0}` enables the non-reapable `t`, so it is not quiescent and is no
`DeadlockFree` violation. -/
@[evidence forbids VER_002]
theorem VER_002_forbids_exactReapable :
    ¬ VER_002 refStrand (ver002_exactReapable (N := Nat)) := by
  intro h
  have hv : ver002_exactReapable false ver002_XExact (.deadlockFree [1] []) (ver002_mk [(0, 1)]) := by
    refine ⟨fun t ht _ => ?_, 0, by decide, by simp [Resting, IsMarker]⟩
    simp only [ver002_XExact, List.mem_singleton] at ht
    subst ht; exact ⟨rfl, rfl⟩
  obtain ⟨hq, -⟩ := (h.1 _ _ _ _ _).mp hv
  exact absurd (hq ver002_t (by simp [ver002_XExact]) (by decide)).2 (by decide)

/-- ✗ Line 1 forbids a `DeadlockFree` that ignores the conditional declarations, at VER-014's
reference rest set: marker `1` with the place `0`, both marked, rest (VER-014 AC1). -/
@[evidence forbids VER_002]
theorem VER_002_forbids_ignoreCond : ¬ VER_002 refStrand (ver002_ignoreCond (N := Nat)) := by
  intro h
  have hv : ver002_ignoreCond false ver002_X0 (.deadlockFree [] [⟨1, [0]⟩])
      (ver002_mk [(0, 1), (1, 1)]) :=
    ⟨ver002_X0_quiescent _ _, 0, by decide, by simp [Resting, IsMarker]⟩
  exact VER_002_nonvacuous_cond.2 ((h.1 _ _ _ _ _).mp hv)

/-- **No rest set that satisfies VER-014 lets VER-002 ignore the conditional declarations.** -/
theorem VER_002_joint_forbids_ignoreCond :
    ¬ ∃ (S : StrandRel Nat) (R : RestViolRel Nat), VER_014 S R ∧ VER_002 S ver002_ignoreCond := by
  rintro ⟨S, R, hS, hV⟩
  have hv : ver002_ignoreCond false ver002_X0 (.deadlockFree [] [⟨1, [0]⟩])
      (ver002_mk [(0, 1), (1, 1)]) :=
    ⟨ver002_X0_quiescent _ _, 0, by decide, by simp [Resting, IsMarker]⟩
  obtain ⟨-, p, hp, hs⟩ := (hV.1 _ _ _ _ _).mp hv
  obtain ⟨-, hmk, hpl⟩ := (hS.1 _ _ _ _).mp hs
  by_cases h1 : p = 1
  · exact hmk ⟨1, [0]⟩ (by simp) h1.symm
  · by_cases h0 : p = 0
    · subst h0; exact absurd (hpl ⟨1, [0]⟩ (by simp) (by simp)) (by decide)
    · apply hp
      have h0' : (0 == p) = false := by simpa using Ne.symm h0
      have h1' : (1 == p) = false := by simpa using Ne.symm h1
      simp [ver002_mk, List.find?, h0', h1']

/-- ✗ Line 1 forbids a `DeadlockFree` that a marked sink satisfies: `{stuck, done}`, `done` a
sink (AC3). -/
@[evidence forbids VER_002]
theorem VER_002_forbids_anySink : ¬ VER_002 refStrand (ver002_anySink (N := Nat)) := by
  intro h
  have hv := (h.1 false ver002_X0 [1] [] (ver002_mk [(0, 1), (1, 1)])).mpr
    ⟨ver002_X0_quiescent _ _, 0, by decide, by simp [refStrand, Resting, IsMarker]⟩
  exact absurd (hv.2 1 (by simp)) (by decide)

/-- ✗ Lines 3 to 5 forbid marking properties that read quiescence: at AC12's initial marking,
which is not quiescent, `PlaceBound(p0, 0)` is violated. -/
@[evidence forbids VER_002]
theorem VER_002_forbids_markingQuiescent :
    ¬ VER_002 refStrand (ver002_markingQuiescent (N := Nat)) := by
  intro h
  have hv := (h.2.2.2.1 false ver002_X12 0 0 (ver002_mk [(0, 1)])).mpr (by decide)
  exact ver002_X12_not_quiescent hv.1

/-- ✗ Line 6 forbids a `QuiescentCount` that does not read quiescence: at AC12's initial
marking, which is not quiescent, one token below `min = 2`. -/
@[evidence forbids VER_002]
theorem VER_002_forbids_countNoQuiescent :
    ¬ VER_002 refStrand (ver002_countNoQuiescent (N := Nat)) := by
  intro h
  have hv : ver002_countNoQuiescent false ver002_X12 (.quiescentCount [0] 2 none [])
      (ver002_mk [(0, 1)]) := Or.inl ⟨by decide, by simp⟩
  exact ver002_X12_not_quiescent ((h.2.2.2.2.2 _ _ _ _ _ _ _).mp hv).1

/-- ✗ Line 6 forbids a lower bound that ignores the waiver: one token below `min = 2` with the
waiver `9` marked (AC8). -/
@[evidence forbids VER_002]
theorem VER_002_forbids_noWaiver : ¬ VER_002 refStrand (ver002_noWaiver (N := Nat)) := by
  intro h
  have hv : ver002_noWaiver false ver002_X0 (.quiescentCount [0] 2 (some 3) [9])
      (ver002_mk [(0, 1), (9, 1)]) := ⟨ver002_X0_quiescent _ _, Or.inl (by decide)⟩
  exact VER_002_nonvacuous_count.2.2 ((VER_002_reference.2.2.2.2.2 _ _ _ _ _ _ _).mpr
    ((h.2.2.2.2.2 _ _ _ _ _ _ _).mp hv))

/-- ✗ Line 2 forbids a `TerminatesAtSink` that needs every sink: sinks `[1, 2]`, only `1`
marked (AC5). -/
@[evidence forbids VER_002]
theorem VER_002_forbids_everySink : ¬ VER_002 refStrand (ver002_everySink (N := Nat)) := by
  intro h
  have hv : ver002_everySink false ver002_X0 (.terminatesAtSink [1, 2]) (ver002_mk [(1, 1)]) :=
    ⟨ver002_X0_quiescent _ _, 2, by simp, by decide⟩
  obtain ⟨-, hs⟩ := (h.2.1 _ _ _ _).mp hv
  exact hs 1 (by simp) (by decide)

/-- ✗ Line 3 forbids the all-marked reading: `[c, a, b]` with `a` and `b` marked (AC10). -/
@[evidence forbids VER_002]
theorem VER_002_forbids_allMarked : ¬ VER_002 refStrand (ver002_allMarked (N := Nat)) := by
  intro h
  have hv := (h.2.2.1 false ver002_X0 [3, 1, 2] (ver002_mk [(1, 1), (2, 1)])).mpr
    ⟨1, 2, 1, 2, by decide, rfl, rfl, by decide, by decide⟩
  exact absurd (hv.2 3 (by simp)) (by decide)

/-- ✗ Line 3 forbids the set-valued reading: `[c, c]` with `c` marked (AC10). -/
@[evidence forbids VER_002]
theorem VER_002_forbids_mutexDedup : ¬ VER_002 refStrand (ver002_mutexDedup (N := Nat)) := by
  intro h
  have hv := (h.2.2.1 false ver002_X0 [3, 3] (ver002_mk [(3, 1)])).mpr
    ⟨0, 1, 3, 3, by decide, rfl, rfl, by decide, by decide⟩
  revert hv; simp only [ver002_mutexDedup, NTwoMarked]; decide

/-- ✗ Line 4 forbids an off-by-one `PlaceBound`: one token in a place bounded by one. -/
@[evidence forbids VER_002]
theorem VER_002_forbids_boundLe : ¬ VER_002 refStrand (ver002_boundLe (N := Nat)) := by
  intro h
  have := (h.2.2.2.1 false ver002_X0 0 1 (ver002_mk [(0, 1)])).mp
    (by simp only [ver002_boundLe]; decide)
  revert this; decide

/-- ✗ Line 5 forbids an any-marked `Unreachable`: `[0, 1]` with only `0` marked. -/
@[evidence forbids VER_002]
theorem VER_002_forbids_unreachAny : ¬ VER_002 refStrand (ver002_unreachAny (N := Nat)) := by
  intro h
  have := (h.2.2.2.2.1 false ver002_X0 [0, 1] (ver002_mk [(0, 1)]) (by simp)).mp
    ⟨0, by simp, by decide⟩
  exact absurd (this 1 (by simp)) (by decide)

/-- ✗ Line 6 forbids a waiver on the upper bound: four tokens above `max = 3` with the waiver
marked (AC8). -/
@[evidence forbids VER_002]
theorem VER_002_forbids_waiverOnMax : ¬ VER_002 refStrand (ver002_waiverOnMax (N := Nat)) := by
  intro h
  have hv := (h.2.2.2.2.2 false ver002_X0 [0] 2 (some 3) [9] (ver002_mk [(0, 4), (9, 1)])).mpr
    ⟨ver002_X0_quiescent _ _, Or.inr ⟨3, rfl, by decide⟩⟩
  exact absurd (hv.2 9 (by simp)) (by decide)

/-- ✗ Line 6 forbids counting a repeated place twice: `places = [0, 0]`, one token in `0`,
`min = 2`. -/
@[evidence forbids VER_002]
theorem VER_002_forbids_listSum : ¬ VER_002 refStrand (ver002_listSum (N := Nat)) := by
  intro h
  have hv := (h.2.2.2.2.2 false ver002_X0 [0, 0] 2 none [] (ver002_mk [(0, 1)])).mpr
    ⟨ver002_X0_quiescent _ _, Or.inl ⟨by decide, by simp⟩⟩
  obtain ⟨-, ⟨hlt, -⟩ | ⟨_, hh, -⟩⟩ := hv
  · revert hlt; decide
  · exact absurd hh (by simp)

/-! ## VER-002 (B): the `QuiescentCount` constructor -/

/-- A `QuiescentCount` constructor: the places, `min`, `max` (`none`: unbounded) and the waivers,
with the bounds as the caller passes them (rationals, so a negative or fractional bound is
expressible); `none` is a rejection where the property is constructed. -/
abbrev CountBuild (N : Type) : Type := List N → ℚ → Option ℚ → List N → Option (VerProp N)

/-- The reference constructor: it accepts a whole `min ≥ 0` and an unbounded or whole
`max ≥ min`, and rejects everything else (TypeScript `quiescentCount`, Python `quiescent_count`;
Java and Rust take integer types, and check the sign and the order). -/
def refCountBuild {N : Type} : CountBuild N := fun ps lo hi w =>
  if decide (0 ≤ lo) && lo.den == 1 && hi.all (fun h => decide (lo ≤ h) && h.den == 1) then
    some (.quiescentCount ps lo.num.toNat (hi.map (·.num.toNat)) w)
  else none

#spec_witness refCountBuild

requirement VER_002_count
  id "VER-002"
  title "QuiescentCount Construction"
  kind B
  scope "every implementation that offers QuiescentCount; the constructor"
  source verbatim "spec/07-verification.md"
  quote "`min` MUST be a non-negative integer and a bounded `max` MUST be an integer at least `min`; a call of the `QuiescentCount` constructor function (named under Implementation notes) breaking either MUST be rejected where it is made, as the language reports a caller's error, rather than yield a verdict. A value built without that function, such as a Rust enum literal or a TypeScript object literal, is not checked."
        "*If* the `QuiescentCount` constructor function is called with a `min` that is negative or not a whole number, or with a `max` that is not a whole number or is below `min`, *then* the call *shall* be rejected where it is made."
        "*When* the `QuiescentCount` constructor function is called with a whole non-negative `min` and a `max` that is unbounded or a whole number at least `min`, the call *shall* yield the property with those bounds."
  reading "For every constructor B: whenever min is negative, or min is not a whole number, or max is bounded by a number that is not whole or is below min, B rejects the construction (answers none), whatever the places and the waivers;"
          "whenever min is a natural number and max is unbounded or a natural number at least min, B yields QuiescentCount with exactly the given places, bounds and waivers."
  assumes "The bounds are rationals as the caller passes them, so that a negative and a fractional min are both expressible; Java (OptionalInt) and Rust (usize, Option<usize>) take integer types, which rule a fractional bound out before the constructor runs, and Rust's usize rules out a negative min. A rejection is none: how the language reports it (an exception, a panic, a ValueError) is the API (kind N), and no verdict is produced because no property exists."
          "A bounded max must be whole as well: TypeScript (Number.isInteger) and Python reject a fractional max, and Java and Rust cannot express one, so the sentence restates every runtime; a constructor that floors a fractional max is killed (VER_002_count_forbids_maxFloor), and so is one that clamps a negative min to 0 (VER_002_count_forbids_clampNeg)."
          "Line 1 is the quoted MUST and AC9's first sentence (a negative or non-integral min, or a non-integral max or one below min, is rejected at construction); line 2 is AC1 for QuiescentCount (it can be constructed). AC9's second sentence (two implementations given the same unbounded max emit the same script, whatever each stores for it) is the script (kind Q); the representation of an unbounded max is not observable, here none."
          "Rust's SmtProperty::QuiescentCount is a public enum variant, so a struct literal builds a property without the constructor's check (rust/libpetri-verification/src/property.rs:161-175); the spec scopes the requirement to the constructor function and says a literal is not checked."
  signoff "2026-11-13 f1b4293f956dd9b6 ai"
  statement : ∀ {N : Type}, CountBuild N → Prop :=
    fun B =>
      (∀ ps lo hi w, (lo < 0 ∨ lo.den ≠ 1 ∨ ∃ h, hi = some h ∧ (h.den ≠ 1 ∨ h < lo)) →
        B ps lo hi w = none) ∧
      (∀ ps (lo : Nat) (hi : Option Nat) w, (∀ h, hi = some h → lo ≤ h) →
        B ps (lo : ℚ) (hi.map (fun h => (h : ℚ))) w = some (.quiescentCount ps lo hi w))

/-- ✓ The reference constructor satisfies VER-002's construction block. -/
@[evidence holds VER_002_count]
theorem VER_002_count_reference {N : Type} : VER_002_count (refCountBuild (N := N)) := by
  refine ⟨fun ps lo hi w h => ?_, fun ps lo hi w h => ?_⟩
  · unfold refCountBuild
    rw [if_neg]
    rcases h with h | h | ⟨b, rfl, hb | hb⟩
    · simp [not_le.mpr h]
    · simp [h]
    · simp [hb]
    · simp [not_le.mpr hb]
  · unfold refCountBuild
    rw [if_pos]
    · cases hi with
      | none => simp
      | some b => simp
    · cases hi with
      | none => simp
      | some b => simpa using h b rfl

/-- The fraction `1/2`, written as its normal form (numerator 1, denominator 2) so that the
kernel evaluates it. -/
def ver002_half : ℚ := ⟨1, 2, by decide, by decide⟩

/-- AC9 and AC1 on the reference: `min = -1`, `min = 1/2`, `min = 0, max = 1/2` and
`min = 2, max = 1` are rejected; `min = max = 2` and `min = 0` unbounded build. -/
@[evidence nonvacuous VER_002_count]
theorem VER_002_count_nonvacuous :
    refCountBuild (N := Nat) [0] (-1) none [] = none ∧
    refCountBuild (N := Nat) [0] ver002_half none [] = none ∧
    refCountBuild (N := Nat) [0] 0 (some ver002_half) [] = none ∧
    refCountBuild (N := Nat) [0] 2 (some 1) [] = none ∧
    refCountBuild (N := Nat) [0] 2 (some 2) [] = some (.quiescentCount [0] 2 (some 2) []) ∧
    refCountBuild (N := Nat) [0] 0 none [] = some (.quiescentCount [0] 0 none []) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A constructor that does not check the order of the bounds (the Rust struct literal). -/
def ver002_buildNoOrder {N : Type} : CountBuild N := fun ps lo hi w =>
  if decide (0 ≤ lo) && lo.den == 1 then
    some (.quiescentCount ps lo.num.toNat (hi.map (·.num.toNat)) w)
  else none

/-- A constructor that clamps a negative `min` to `0` (`Int.toNat`) instead of rejecting it. -/
def ver002_buildClampNeg {N : Type} : CountBuild N := fun ps lo hi w =>
  if lo.den == 1 && hi.all (fun h => decide (lo ≤ h) && h.den == 1) then
    some (.quiescentCount ps lo.num.toNat (hi.map (·.num.toNat)) w)
  else none

/-- A constructor that floors a fractional `min` instead of rejecting it. -/
def ver002_buildFloor {N : Type} : CountBuild N := fun ps lo hi w =>
  if decide (0 ≤ lo) && hi.all (fun h => decide (lo ≤ h) && h.den == 1) then
    some (.quiescentCount ps lo.floor.toNat (hi.map (·.num.toNat)) w)
  else none

/-- A constructor that floors a fractional `max` instead of rejecting it. -/
def ver002_buildMaxFloor {N : Type} : CountBuild N := fun ps lo hi w =>
  if decide (0 ≤ lo) && lo.den == 1 && hi.all (fun h => decide (lo ≤ h)) then
    some (.quiescentCount ps lo.num.toNat (hi.map (·.floor.toNat)) w)
  else none

/-- A constructor that needs `max` strictly above `min`, so `exactly k` is rejected. -/
def ver002_buildStrict {N : Type} : CountBuild N := fun ps lo hi w =>
  if decide (0 ≤ lo) && lo.den == 1 && hi.all (fun h => decide (lo < h) && h.den == 1) then
    some (.quiescentCount ps lo.num.toNat (hi.map (·.num.toNat)) w)
  else none

/-- ✗ Line 1 forbids a constructor that accepts `max < min`: `min = 2`, `max = 1`. -/
@[evidence forbids VER_002_count]
theorem VER_002_count_forbids_noOrder : ¬ VER_002_count (ver002_buildNoOrder (N := Nat)) := by
  intro h
  have := h.1 [0] 2 (some 1) [] (Or.inr (Or.inr ⟨1, rfl, Or.inr (by norm_num)⟩))
  exact absurd this (by simp [ver002_buildNoOrder])

/-- ✗ Line 1 forbids a constructor that clamps a negative `min` to `0`: `min = -1` builds
`QuiescentCount(min = 0)` there. -/
@[evidence forbids VER_002_count]
theorem VER_002_count_forbids_clampNeg : ¬ VER_002_count (ver002_buildClampNeg (N := Nat)) := by
  intro h
  have := h.1 [0] (-1) none [] (Or.inl (by norm_num))
  revert this
  decide

/-- ✗ Line 1 forbids a constructor that floors a fractional `min`: `min = 1/2`. -/
@[evidence forbids VER_002_count]
theorem VER_002_count_forbids_floor : ¬ VER_002_count (ver002_buildFloor (N := Nat)) := by
  intro h
  have := h.1 [0] ver002_half none [] (Or.inr (Or.inl (by decide)))
  revert this
  decide

/-- ✗ Line 1 forbids a constructor that floors a fractional `max`: `min = 0`, `max = 1/2`. -/
@[evidence forbids VER_002_count]
theorem VER_002_count_forbids_maxFloor : ¬ VER_002_count (ver002_buildMaxFloor (N := Nat)) := by
  intro h
  have := h.1 [0] 0 (some ver002_half) [] (Or.inr (Or.inr ⟨ver002_half, rfl, Or.inl (by decide)⟩))
  revert this
  decide

/-- ✗ Line 2 forbids a constructor that needs `max > min`: `min = max = 2`. -/
@[evidence forbids VER_002_count]
theorem VER_002_count_forbids_strict : ¬ VER_002_count (ver002_buildStrict (N := Nat)) := by
  intro h
  have := h.2 [0] 2 (some 2) [] (fun _ hb => by cases hb; exact le_refl _)
  exact absurd this (by simp [ver002_buildStrict])

end Libpetri.Spec
