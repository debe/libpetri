import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Novel.Seam.Bad
import Libpetri.Reference.Semantics
import Libpetri.Spec.Text.VER_014

set_option linter.missingDocs true

/-!
# VER-014: Conditional sink places (`spec/07-verification.md`)

`DeadlockFree` reads a quiescent marking against the places where a token may rest: the
declared sinks, the markers of the conditional declarations `sinkPlacesWhen(marker, places…)`,
and the places of a declaration whose marker is marked. The requirement is a predicate over a
pair `(S, V)`:

* `S : StrandRel N`, the rest set read as a predicate: `S sinks cond m p` says a token in `p` of
  the marking `m` is stranded under the sinks `sinks` and the conditional declarations `cond`;
* `V : RestViolRel N`, the two properties that read the rest set: `V Q prop sinks cond m` says
  the marking `m` violates `prop` (`DeadlockFree` or `TerminatesAtSink`) under the quiescence
  reading `Q`.

The witness pair is `refStrand` (not `Seam.Resting`, `rest_set.rs` `resting_names`) and
`refRestViol`. Quiescence is a parameter: which transitions count (the reap-aware reading of
[VER-002], the injection reading of [VER-006], plain quiescence under `assumeNoReaping`) is not
this requirement's subject. The statement is checked against the witness pair
(`VER_014_reference`), against three wrong rest sets (a marker that must list itself, a place
excused whatever its marker holds, a place that needs all of its markers marked), against a
`DeadlockFree` that ignores the declarations and against a `TerminatesAtSink` that reads them.
`VER_014_encoding` ties the witness to the encoder: on a covered marking the encoded `Bad` of
`DeadlockFree` (`Seam.deadlockBad`) is `refRestViol` at plain quiescence.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.Seam

/-! ## The model -/

/-- A rest-set reading: `S sinks cond m p` says a token in place `p` of the marking `m` is
stranded under the declared sinks `sinks` and the conditional declarations `cond`. -/
abbrev StrandRel (N : Type) : Type := List N → List (CondSinks N) → (N → Nat) → N → Prop

/-- The two properties whose violation reads the rest set ([VER-002]). -/
inductive RestProp where
  /-- `DeadlockFree`. -/
  | deadlockFree
  /-- `TerminatesAtSink`. -/
  | terminatesAtSink
  deriving DecidableEq, Repr

/-- A violation reading of the rest-set properties: `V Q prop sinks cond m` says the marking `m`
violates `prop` under the quiescence reading `Q`, the declared sinks `sinks` and the conditional
declarations `cond`. -/
abbrev RestViolRel (N : Type) : Type :=
  ((N → Nat) → Prop) → RestProp → List N → List (CondSinks N) → (N → Nat) → Prop

/-- The reference rest set: a token in `p` is stranded when `p` is not a place where a token may
rest (`Seam.Resting`, `rest_set.rs` `resting_names` and `strands_token`). -/
def refStrand {N : Type} [DecidableEq N] : StrandRel N :=
  fun sinks cond m p => ¬ Resting sinks cond m p

/-- The reference violations: `DeadlockFree` is quiescence and a marked place where no token may
rest (`Seam.NDeadlock` with the quiescence as a parameter); `TerminatesAtSink` is quiescence and
no declared sink marked (`Reference.Violates`), whatever the conditional declarations say. -/
def refRestViol {N : Type} [DecidableEq N] : RestViolRel N :=
  fun Q prop sinks cond m =>
    match prop with
    | .deadlockFree => Q m ∧ ∃ p, m p ≠ 0 ∧ ¬ Resting sinks cond m p
    | .terminatesAtSink => Q m ∧ ∀ s ∈ sinks, m s = 0

#spec_witness refStrand
#spec_witness refRestViol

/-! ## VER-014: Conditional sink places -/

requirement VER_014
  id "VER-014"
  title "Conditional Sink Places (Designed Terminals)"
  kind F
  scope "every route that decides DeadlockFree or TerminatesAtSink, all implementations"
  source verbatim "spec/07-verification.md"
  covers VER_014.s1, VER_014.s2, VER_014.s3, VER_014.s4, VER_014.s5, VER_014.s6
  reading "For every rest-set reading S and violation reading V, and all sinks, conditional declarations cond, markings m and places p:"
          "S strands p in m exactly when p is not in sinks, p is the marker of no declaration of cond, and every declaration of cond whose places contain p has its marker unmarked in m;"
          "for every quiescence reading Q, m violates DeadlockFree under V exactly when Q holds of m and some place marked in m is stranded under S;"
          "for every quiescence reading Q, m violates TerminatesAtSink under V with the declarations cond exactly when it does with no declaration."
  assumes "A marking is a count marking, by place name (N → Nat), as the verifier's named reading of a flat marking is (Seam, `restrict`). A conditional declaration is `sinkPlacesWhen(marker, places…)`: a marker and a list of places (Seam.CondSinks, `rest_set.rs` `ConditionalSinks`); the declarations are a list, so 'Declarations union' and 'Repeated declarations for one marker accumulate' are the list itself, and line 1 reads every declaration of the list."
          "Quiescence is a parameter Q of lines 2 and 3, not a definition: which transitions a quiescent marking may still enable is VER-002's reap-aware reading, VER-006's reading under injection, or plain quiescence under `assumeNoReaping`, three predicates selected by the options. 'The `DeadlockFree` error condition becomes: (all transitions disabled) ∧ (some marked place is stranded)' is line 2 with Q the quiescence the options select. At Q = Seam.NQuiescent, refRestViol's DeadlockFree is Seam.NDeadlock (VER_014_deadlock_NDeadlock), and with no declaration both lines agree with the conformance reference's Violates at its reap-aware quiescence (VER_014_reference_violates)."
          "Line 1 is the first and fourth quoted sentences and the second: a place is excused by a marked marker of any one declaration that names it, so a place two markers excuse is stranded only when both are unmarked; a wrong rest set that needs all of its markers marked is killed (VER_014_forbids_allMarkers). The first sentence's 'quiescent' is dropped in line 1: whether a token is stranded is a function of the marking alone, and line 2 adds quiescence."
          "Unresolved names (a marker or a place that does not resolve in the flat net) are not a clause of line 1: a name the flat net does not hold has no flat variable, so it holds no token in a marking the index covers (Seam.Covers). An unresolved marker is then never marked and excuses nothing, and an unresolved place holds no token to strand, which is what 'An unresolved marker or place contributes nothing, as an unresolved sink does' says. The encoder skips such a declaration (`stranding_excuses`, Seam.strandingExcuses_spec); VER_014_encoding is stated on covered markings."
          "AC1 (a quiescent marking that marks a marker and holds tokens only in declared sinks, in the marker and in that marker's conditional places is not a DeadlockFree violation) is line 2 with line 1, checked on the reference by VER_014_nonvacuous (marker 0 and its place 1 and the sink 2 marked: no violation), and a DeadlockFree that ignores the declarations is killed (VER_014_forbids_ignoreCond)."
          "AC2 (a token in a conditional place whose marker is unmarked is a violation, exactly as without the declaration) is line 1, checked by VER_014_nonvacuous (marker 0 unmarked, a token in its place 1: a violation); a rest set that excuses a conditional place whatever its marker holds is killed (VER_014_forbids_uncond)."
          "AC3 (the marker needs no self-listing: `sinkPlacesWhen(p)` excuses a quiescent marking holding only `p`) is line 1, checked by VER_014_nonvacuous; a rest set in which the marker must list itself is killed (VER_014_forbids_noSelf)."
          "AC4 (TerminatesAtSink ignores the conditional declarations: a quiescent marking that marks a marker but no declared sink violates it) is line 3, checked by VER_014_nonvacuous; a TerminatesAtSink that counts the markers and their places as sinks is killed (VER_014_forbids_termReadsCond)."
          "AC5 (every route that decides DeadlockFree reads the same rest set, and the four implementations emit byte-identical scripts for the same declarations) is not a line here: that every route reads the same rest set is stated by no block (the pipeline model, Verifier/Pipeline.lean, does not say what each route reads), and the byte identity of the scripts is VER-013's golden-script check (kind Q). The flat encoder's agreement with line 2 is VER_014_encoding, the encoded Bad of DeadlockFree (Seam.deadlockBad_iff) restated through refRestViol."
          "The Encoding paragraph (the stranded disjunct `(and (>= m_p 1) (= m_k₁ 0) … (= m_kₙ 0))` per excused place, scripts without a declaration byte-identical to VER-002's, the report rendering `(sinks: a, b; when h: c, d; when p)`) is the encoder's and the report's text: the disjunct is cited by VER_014_encoding through Seam.deadlockBad_eq; the byte identity and the rendering are not modelled (kind N for the rendering, kind Q for the scripts)."
          "The Net-declared terminals paragraph (a terminal place declared on the net is verified with the place inhibiting each transition, added to the sinks and declared a marker for every place) is the terminal rewrite of EXEC-042 (Novel/TerminalRewrite.lean); it adds declarations and does not change lines 1 to 3, and it belongs to the EXEC-042 block."
          "The Implementation notes and the fixtures list name the per-language entry points and the fixture files (kind N); the test derivation is AC1 to AC4 on one fork, as above."
  signoff "2026-11-13 f46e3fb9203f172b ai"
  statement : ∀ {N : Type} [DecidableEq N], StrandRel N → RestViolRel N → Prop :=
    fun S V =>
      (∀ sinks cond m p,
        S sinks cond m p ↔
          p ∉ sinks ∧ (∀ c ∈ cond, c.marker ≠ p) ∧ ∀ c ∈ cond, p ∈ c.places → m c.marker = 0) ∧
      (∀ Q sinks cond m,
        V Q .deadlockFree sinks cond m ↔ Q m ∧ ∃ p, m p ≠ 0 ∧ S sinks cond m p) ∧
      (∀ Q sinks cond m,
        V Q .terminatesAtSink sinks cond m ↔ V Q .terminatesAtSink sinks [] m)

/- The pinned readable form of VER-014: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_014 : {N : Type} → [DecidableEq N] → StrandRel N → RestViolRel N → Prop :=
fun {N} [DecidableEq N] S V =>
  (∀ (sinks : List N) (cond : List (CondSinks N)) (m : N → ℕ) (p : N),
      S sinks cond m p ↔ p ∉ sinks ∧ (∀ c ∈ cond, c.marker ≠ p) ∧ ∀ c ∈ cond, p ∈ c.places → m c.marker = 0) ∧
    (∀ (Q : (N → ℕ) → Prop) (sinks : List N) (cond : List (CondSinks N)) (m : N → ℕ),
        V Q RestProp.deadlockFree sinks cond m ↔ Q m ∧ ∃ p, m p ≠ 0 ∧ S sinks cond m p) ∧
      ∀ (Q : (N → ℕ) → Prop) (sinks : List N) (cond : List (CondSinks N)) (m : N → ℕ),
        V Q RestProp.terminatesAtSink sinks cond m ↔ V Q RestProp.terminatesAtSink sinks [] m
-/
#guard_msgs in #print VER_014

/-! ## The reference -/

/-- The reference rest set is the stranding rule, read by name. -/
theorem refStrand_iff {N : Type} [DecidableEq N] (sinks : List N) (cond : List (CondSinks N))
    (m : N → Nat) (p : N) :
    refStrand sinks cond m p ↔
      p ∉ sinks ∧ (∀ c ∈ cond, c.marker ≠ p) ∧ ∀ c ∈ cond, p ∈ c.places → m c.marker = 0 := by
  simp only [refStrand, Resting, IsMarker, not_or, not_exists, not_and]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun c hc => h2 c hc, fun c hc hp => by
      by_contra hne; exact h3 c hc hne hp⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun c hc => h2 c hc, fun c hc hne hp => hne (h3 c hc hp)⟩

/-- The reference pair satisfies VER-014. -/
@[evidence holds VER_014]
theorem VER_014_reference {N : Type} [DecidableEq N] :
    VER_014 (refStrand (N := N)) refRestViol :=
  ⟨refStrand_iff, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩

/-- At plain quiescence the reference `DeadlockFree` is the named deadlock of the Seam model. -/
theorem VER_014_deadlock_NDeadlock {N : Type} [DecidableEq N] (net : NNet N) (sinks : List N)
    (cond : List (CondSinks N)) (m : N → Nat) :
    refRestViol (NQuiescent net) .deadlockFree sinks cond m ↔ NDeadlock net sinks cond m :=
  Iff.rfl

/-- **The encoder reads the reference rest set.** On a marking the place index covers, the
encoded `Bad` of `DeadlockFree` with the conditional declarations holds of the flat restriction
exactly when the marking violates `DeadlockFree` under `refRestViol` at plain quiescence. -/
@[evidence cites "VER-014" "Encoding: on a marking the place index covers, the flat encoder's DeadlockFree Bad, one stranded disjunct per excused place conjoined with its markers unmarked, holds exactly when refRestViol's DeadlockFree does at plain quiescence (no reaping, no injection)"]
theorem VER_014_encoding {N : Type} [DecidableEq N] {ix : PlaceIndex N} {net : NNet N}
    (hA : ArcsIn ix net) (hD : InputsDistinct net) (sinks : List N) (cond : List (CondSinks N))
    {m : N → Nat} (h : Covers ix m) :
    deadlockBad (flatNet ix net) ix sinks cond (restrict ix m) = true ↔
      refRestViol (NQuiescent net) .deadlockFree sinks cond m :=
  deadlockBad_iff hA hD sinks cond h

/-- With no conditional declaration the reference pair agrees with the conformance reference's
`Violates` at its reap-aware quiescence, for both properties; `TerminatesAtSink` agrees whatever
the declarations. -/
theorem VER_014_reference_violates {N : Type} [DecidableEq N] (net : Reference.Net N)
    (sinks : List N) (cond : List (CondSinks N)) (m : N → Nat) :
    (Reference.Violates net (.deadlockFree sinks) m ↔
      refRestViol (Reference.ReapQuiescent net) .deadlockFree sinks [] m) ∧
    (Reference.Violates net (.terminatesAtSink sinks) m ↔
      refRestViol (Reference.ReapQuiescent net) .terminatesAtSink sinks cond m) := by
  constructor
  · simp [Reference.Violates, refRestViol, Resting, IsMarker]
  · exact Iff.rfl

/-! ## Examples: AC1 to AC4 on the reference -/

/-- A count marking from a list of `(place, count)` pairs; unlisted places hold nothing. -/
def ver014_mk (l : List (Nat × Nat)) : Nat → Nat :=
  fun p => ((l.find? (·.1 == p)).map (·.2)).getD 0

/-- AC1 to AC4 on the reference, with every marking read as quiescent: a marked marker excuses
its place and itself (AC1); an unmarked marker excuses nothing (AC2); a marker with no places
excuses itself (AC3); `TerminatesAtSink` is violated when only a marker is marked (AC4). -/
@[evidence nonvacuous VER_014]
theorem VER_014_nonvacuous :
    ¬ refRestViol (N := Nat) (fun _ => True) .deadlockFree [2] [⟨0, [1]⟩]
        (ver014_mk [(0, 1), (1, 1), (2, 1)]) ∧
    refRestViol (N := Nat) (fun _ => True) .deadlockFree [2] [⟨0, [1]⟩] (ver014_mk [(1, 1)]) ∧
    ¬ refRestViol (N := Nat) (fun _ => True) .deadlockFree [] [⟨0, []⟩] (ver014_mk [(0, 1)]) ∧
    refRestViol (N := Nat) (fun _ => True) .terminatesAtSink [2] [⟨0, [1]⟩]
        (ver014_mk [(0, 1), (1, 1)]) := by
  refine ⟨?_, ⟨trivial, 1, by decide, ?_⟩, ?_, ⟨trivial, ?_⟩⟩
  · rintro ⟨-, p, hp, hr⟩
    apply hr
    by_cases h0 : p = 0
    · subst h0; exact Or.inr (Or.inl ⟨⟨0, [1]⟩, by simp, rfl⟩)
    by_cases h1 : p = 1
    · subst h1; exact Or.inr (Or.inr ⟨⟨0, [1]⟩, by simp, by decide, by simp⟩)
    by_cases h2 : p = 2
    · subst h2; exact Or.inl (by simp)
    exact absurd hp (by simp [ver014_mk, List.find?,
      show (0 == p) = false from by simp; omega, show (1 == p) = false from by simp; omega,
      show (2 == p) = false from by simp; omega])
  · simp [Resting, IsMarker, ver014_mk]
  · rintro ⟨-, p, hp, hr⟩
    apply hr
    by_cases h0 : p = 0
    · subst h0; exact Or.inr (Or.inl ⟨⟨0, []⟩, by simp, rfl⟩)
    exact absurd hp (by simp [ver014_mk, List.find?, show (0 == p) = false from by simp; omega])
  · simp [ver014_mk]

/-! ## Wrong models -/

/-- A rest set in which a marker must list itself to rest (AC3 broken). -/
def ver014_strandNoSelf {N : Type} [DecidableEq N] : StrandRel N :=
  fun sinks cond m p => p ∉ sinks ∧ ∀ c ∈ cond, p ∈ c.places → m c.marker = 0

/-- A rest set that excuses a conditional place whatever its marker holds (AC2 broken). -/
def ver014_strandUncond {N : Type} [DecidableEq N] : StrandRel N :=
  fun sinks cond _ p => p ∉ sinks ∧ (∀ c ∈ cond, c.marker ≠ p) ∧ ∀ c ∈ cond, p ∉ c.places

/-- A rest set that excuses a place only when every marker naming it is marked. -/
def ver014_strandAllMarkers {N : Type} [DecidableEq N] : StrandRel N :=
  fun sinks cond m p => p ∉ sinks ∧ (∀ c ∈ cond, c.marker ≠ p) ∧
    ((∃ c ∈ cond, p ∈ c.places) → ∃ c ∈ cond, p ∈ c.places ∧ m c.marker = 0)

/-- A `DeadlockFree` that reads the unconditional sinks only (AC1 broken). -/
def ver014_violIgnoreCond {N : Type} [DecidableEq N] : RestViolRel N :=
  fun Q prop sinks _ m => refRestViol Q prop sinks [] m

/-- A `TerminatesAtSink` that counts the markers and their places as sinks (AC4 broken). -/
def ver014_violTermReadsCond {N : Type} [DecidableEq N] : RestViolRel N :=
  fun Q prop sinks cond m =>
    match prop with
    | .deadlockFree => refRestViol Q .deadlockFree sinks cond m
    | .terminatesAtSink => Q m ∧ ∀ s, Resting sinks cond m s → m s = 0

/-- Line 1 forbids a marker that must list itself: `sinkPlacesWhen(0)` with 0 marked. -/
@[evidence forbids VER_014]
theorem VER_014_forbids_noSelf : ¬ VER_014 (ver014_strandNoSelf (N := Nat)) refRestViol := by
  intro h
  have := (h.1 [] [⟨0, []⟩] (fun _ => 1) 0).mp (by simp [ver014_strandNoSelf])
  simp at this

/-- Line 1 forbids excusing a conditional place whose marker is unmarked: `sinkPlacesWhen(0, 1)`
with a token in 1 and none in 0. -/
@[evidence forbids VER_014]
theorem VER_014_forbids_uncond : ¬ VER_014 (ver014_strandUncond (N := Nat)) refRestViol := by
  intro h
  have := (h.1 [] [⟨0, [1]⟩] (fun n => if n = 1 then 1 else 0) 1).mpr (by simp)
  simp [ver014_strandUncond] at this

/-- Line 1 forbids a rest set that needs all of a place's markers marked: place 2 declared
under markers 0 and 1, only 0 marked. -/
@[evidence forbids VER_014]
theorem VER_014_forbids_allMarkers :
    ¬ VER_014 (ver014_strandAllMarkers (N := Nat)) refRestViol := by
  intro h
  have := (h.1 [] [⟨0, [2]⟩, ⟨1, [2]⟩] (fun n => if n = 0 then 1 else 0) 2).mp
    (by simp [ver014_strandAllMarkers])
  simp at this

/-- Line 2 forbids a `DeadlockFree` that ignores the declarations: marker 0 and its place 1
marked, no sink. -/
@[evidence forbids VER_014]
theorem VER_014_forbids_ignoreCond :
    ¬ VER_014 (refStrand (N := Nat)) ver014_violIgnoreCond := by
  intro h
  have hv : ver014_violIgnoreCond (N := Nat) (fun _ => True) .deadlockFree [] [⟨0, [1]⟩]
      (fun n => if n ≤ 1 then 1 else 0) :=
    ⟨trivial, 1, by simp, by simp [Resting, IsMarker]⟩
  obtain ⟨-, p, hp, hs⟩ := ((h.2.1 _ _ _ _).mp hv)
  by_cases h0 : p = 0
  · subst h0; simp [refStrand, Resting, IsMarker] at hs
  by_cases h1 : p = 1
  · subst h1; simp [refStrand, Resting, IsMarker] at hs
  · simp at hp; omega

/-- Line 3 forbids a `TerminatesAtSink` that reads the declarations: marker 0 marked, sink 2
unmarked. -/
@[evidence forbids VER_014]
theorem VER_014_forbids_termReadsCond :
    ¬ VER_014 (refStrand (N := Nat)) ver014_violTermReadsCond := by
  intro h
  have hno : ver014_violTermReadsCond (N := Nat) (fun _ => True) .terminatesAtSink [2] []
      (fun n => if n = 0 then 1 else 0) :=
    ⟨trivial, fun s hs => by simp [Resting, IsMarker] at hs; simp [hs]⟩
  obtain ⟨-, hall⟩ := (h.2.2 _ _ [⟨0, []⟩] _).mpr hno
  have := hall 0 (Or.inr (Or.inl ⟨⟨0, []⟩, by simp, rfl⟩))
  simp at this

end Libpetri.Spec
