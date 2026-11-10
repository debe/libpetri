import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryNuVer
import Libpetri.Novel.RouteB.Exec
import Libpetri.Novel.RouteA.Plan

set_option linter.missingDocs true

/-!
# NU-051: EXTENDED coloured-consumer fragment (`spec/12-nu-nets.md`)

Two blocks share the ID.

* `NU_051` is a predicate over an abstract fragment classifier `C : Classifier` (glossary
  `GlossaryNuVer.lean`): from the coloured set, the fragment mode, the mint declaration, the
  timeout writes and the transition, the role the transition gets, or none. It is checked
  against the shipped classifier (`refClassify`, which is `Novel.RouteB.classifyS`), against
  classifiers that break one rule each (among them the three wrong classifiers the W0 probes
  found the earlier statement accepted), and against five mutant readings.
* `NU_051_relay` is a predicate over an abstract name-layer step of a coloured consumer, checked
  against the Route B step (`Novel.RouteB.consumeStep`) and against a step that mints a fresh
  name and one that keeps the consumed name in its input.

The carrier line, the "EXTENDED declined" note and the verdict lines wait for the verifier
pipeline (W10) and for rulings D95 and D20; the assumptions of `NU_051` say which line waits for
what.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.RouteB

/-! ## Vocabulary local to NU-051 -/

/-- A reset, read or inhibitor arc of `T` on a place of the coloured set `col`. -/
def ColouredTestArc (col : PlaceId → Bool) (T : NuTrans) : Prop :=
  ∃ p, col p = true ∧ (p ∈ T.base.resets ∨ p ∈ T.base.reads ∨ p ∈ T.base.inhibitors)

/-- An input arc at count one: [IO-001] `One` or [IO-002] `Exactly(1)`. -/
def UnitCount (s : InSpec) : Prop := s.card = .one ∨ s.card = .exactly 1

/-- Every branch of `T` deposits exactly one token into each coloured place it writes, and no
branch deposits a drained forward (a count read off the marking) into a coloured place. -/
def SingleColouredWrites (col : PlaceId → Bool) (T : NuTrans) : Prop :=
  ∀ r ∈ T.rows, (∀ p ∈ r.fixed, col p = true → r.fixed.count p = 1) ∧
    ∀ x ∈ r.drains, col x.1 = false

/-- Every timeout write of the list into a coloured place forwards the input place `p`. -/
def ForwardsOnly (col : PlaceId → Bool) (tw : List (PlaceId × TW)) (p : PlaceId) : Prop :=
  ∀ w ∈ tw, col w.1 = true → w.2 = TW.forward p

/-! ## NU-051: the fragment classifier -/

requirement NU_051
  id "NU-051"
  title "EXTENDED Coloured-Consumer Fragment"
  kind F
  scope "the fragment classifier of every ν verifier"
  source verbatim "spec/12-nu-nets.md"
  quote "*While* the fragment mode is BASE, the fragment classifier *shall* give no role to a transition without a match spec that consumes a coloured place."
        "*While* the fragment mode is EXTENDED, the fragment classifier *shall* give a transition without a match spec that consumes a coloured place no role other than the coloured-consumer role of its one coloured input, and that role only when it consumes exactly one coloured input, at count one, and puts on each branch exactly one token, and never a drained batch, into each coloured place the branch writes."
        "*If* a transition without a match spec consumes a coloured place and its timeout writes a coloured place other than by forwarding that consumed input, *then* the fragment classifier *shall* give it no role."
        "*While* the fragment mode is EXTENDED, *if* a transition without a match spec consumes exactly one coloured input, at count one, has no reset, read or inhibitor arc on a coloured place, puts on each branch exactly one token, and never a drained batch, into each coloured place the branch writes, and on timeout writes a coloured place only by forwarding that input, *then* the fragment classifier *shall* give it the coloured-consumer role of that input's place, whether or not it is declared a mint."
        "*If* a coloured place carries a reset, read or inhibitor arc of a transition, *then* the fragment classifier *shall* give that transition no role, in both BASE and EXTENDED."
        "*If* a matched transition consumes a coloured place through an input that is not one of its match keys, *then* the fragment classifier *shall* give it no role, in both BASE and EXTENDED."
        "The fragment classifier *shall* give the coloured-consumer role to no other transition: to none while the fragment mode is BASE, to no matched transition and to no transition that consumes no coloured place."
  reading "For every coloured set col, mint declaration, list of timeout writes tw and transition T:"
          "under BASE, a transition with no match spec and a coloured input gets no role;"
          "under EXTENDED, if a transition with no match spec and a coloured input gets a role, its branches deposit one token into each coloured place they write and drain none into one, its coloured inputs are a single input s, at count One or Exactly(1), the role is the coloured-consumer role of s's place, and every timeout write into a coloured place forwards s's place;"
          "under EXTENDED, a transition with no match spec, no reset, read or inhibitor arc on a coloured place, whose branches deposit one token into each coloured place they write and drain none into one, whose coloured inputs are a single input s at count One or Exactly(1), and whose every timeout write into a coloured place forwards s's place, gets the coloured-consumer role of s's place;"
          "in either mode, a transition with a reset, read or inhibitor arc on a coloured place gets no role;"
          "in either mode, a transition with match keys ks that consumes a coloured place through an input whose place is not in ks gets no role;"
          "in either mode, a transition that gets the coloured-consumer role of a place is classified under EXTENDED, has no match spec and has a coloured input."
  assumes "The classifier is per transition, as the glossary term Fragment classifier reads it: no role for one transition means the net falls back to the sound over-approximation ([NU-050]); the Rust `classify` (rust/libpetri-verification/src/name_fragment.rs) returns no fragment for the net as soon as one transition is refused. The coloured set is an argument. How a verifier builds it (the match keys, and under EXTENDED the declared carriers and the relay targets of [NU-054]) is the verifier pipeline's subject (W10), not a line here. So every line speaks of the places coloured in the mode at hand: a place coloured only by a declared carrier or a relay target is not coloured under BASE, where the coloured set is the match keys alone."
          "The first paragraph of the section is not a line. Its sentence 'Both are decided solely by the solver-free Route B quotient' conflicts with [NU-053], which lets Route A decide the EXTENDED fragment, and with AC7 and AC8, which speak of both routes (clash nu-c#1, ruling D20 open). The two-value knob, BASE as the default and its builder option names are configuration (kind N); the key format is [VER-012]'s subject."
          "Line 1 is the first quoted sentence. It is the BASE half of AC1 for a fixture whose consumed place is coloured under BASE, that is a match key of the net (the coloured place a mint feeds): a consumer of a place coloured only by an EXTENDED carrier or relay target consumes no coloured place under BASE, gets an ordinary role there, and the net is not refused on its account. Whether a given fixture's place is coloured in each mode is the coloured-set computation (W10). Line 2 is the second quoted sentence (the prose: 'The analyzer' takes such a transition 'only as a drain/relay role and only when it consumes exactly one coloured input at count exactly one'; 'A consumer that consumes more than one coloured place, or consumes at any count other than one (`Exactly(n≥2)`, `AtLeast`, `All`), is rejected') and AC2, and its last conjunct is the third quoted sentence and the Route B half of AC8: a timeout write into a coloured place that is a unit token or a forward of another input leaves the transition with no role. Its first conjunct (SingleColouredWrites: every branch puts exactly one token into each coloured place it writes, and no drained batch, a forward from an `All` or `AtLeast` input whose count is read off the marking ([IO-014]), into one) is the clause 'puts on each branch exactly one token, and never a drained batch' of the second quoted sentence. The markdown gives it only as the reason for refusing higher input counts ('the base marking adds exactly one token per output place, so re-emitting a higher input cardinality into the name layer would over-count'); the shipped classifier refuses on it (`classifyT`, the branch check), and so does the line."
          "Line 3 is the fourth quoted sentence and the EXTENDED half of AC1: the role is given, not only allowed (the markdown's 'MAY consume' is a permission to the net author; the classifier that the author relies on then has to give the role). Its premises are the sentence's conditions one for one: one coloured input at count one, no test arc on a coloured place (line 4), one token and no drained batch per coloured place a branch writes (SingleColouredWrites, as in line 2), and only forwards of that input on timeout (ForwardsOnly, as in line 2). A transition that builds has SingleColouredWrites whenever its coloured timeout writes forward its one coloured input: an output branch names a place at most once ([IO-011]), and that input is consumed at count one, so its forward deposits one token. The model takes the branches and the timeout writes as two separate arguments, so the line states the premise."
          "The mint declaration plays no part in lines 1 to 3 and 6, which hold for both values of declared; the role sentence says so ('whether or not it is declared a mint'). This agrees with [NU-010], whose mint writes a coloured place without consuming one: a declared transition that consumes a coloured place is a consumer here, and the mint rule (Novel.RouteB.classifyS_mint) is [NU-010]'s verifier line, not this block's."
          "'Because the consumed count is fixed at one, the role is identified by the input place name alone' is encoded by lines 2 and 3, which fix the role to `consume s.place`: Role.consume carries a place and nothing else."
          "Line 4 is the fifth quoted sentence and AC3. The prose says the analyzer rejects a net in which 'any coloured place carries' such an arc 'on any transition'; per transition that is line 4, and the net falls back because one of its transitions gets no role. Its reason ('it never turns a `Proven`/`Violated` into an unsound verdict') is [NU-050]'s soundness, not a line."
          "Line 5 is the sixth quoted sentence and the first half of AC7. 'A non-coloured non-key input (a budget or permit) is unaffected' is not a line: line 5 speaks only of coloured inputs, and NU_051_nonvacuous shows a join with an uncoloured budget input that gets its join role. The second half of AC7 ('a stranding such a net can reach is not reported `Proven`') is a verdict and waits for the verifier pipeline (W10)."
          "Line 6 is the seventh quoted sentence, the converse of lines 1 to 3: the coloured-consumer role exists only under EXTENDED ('BASE reproduces the shipped mint → matched-join fragment exactly'), only for 'a transition with **no** match spec' (a matched transition takes a name by its match test, [NU-020], not by the consumer step), and only for a transition that consumes a coloured place (the relay step removes the name 'from its coloured input'). With line 2 it pins down every transition the role is given to."
          "The relay and drain semantics ('A coloured consumer relays the consumed name-symbol into each coloured output of the fired branch ... or drains it ... on a branch that produces no coloured output') is the block NU_051_relay. AC6 (MAY: one `Xor` consumer relays on one branch and drains on another) is permitted by lines 2 and 3, which do not depend on the branches: the fixture of NU_051_nonvacuous is such a consumer, and NU_051_relay_nonvacuous relays on one branch and drains on the other."
          "The relay/drain action precondition is an assumption on the net author (kind A), not a line: the action threads the consumed name into its coloured outputs, or into none, and never mints a fresh name while consuming a coloured token. No analysis can check it. It enters Route B as the consumer contract of the name step (`Novel.RouteB.Contract`, under which `name_step_simulates_exec` holds), the premise of [NU-050]'s soundness (W9). 'MUST be documented as such' is a documentation duty (kind Q). 'the report of a verdict names the consumers whose action writes it assumes' is a report line of the verifier pipeline (W10)."
          "The carrier bullet is not a line yet. Where a declared carrier that is not a place of the net must fail is ruling D95 (clash nu-c#2: AC4 has no mode, the body ignores carriers under BASE, and Java and TypeScript reject at the builder while Rust refuses only on some Route B paths), so AC4 waits for it and for the verifier pipeline (W10). That the carriers join the coloured set before roles are given, and are ignored under BASE, is the coloured-set computation of the pipeline (W10)."
          "The diagnosability bullet (an 'EXTENDED declined' note) is a report line (kind N) of the verifier pipeline (W10); whether every refusal must carry it is clash nu-c#10 (ruling D20 open)."
          "AC5 (SHOULD: an end-to-end quiescence verdict on a carrier fixture, attributable to Route B) is a verdict and report line of the verifier pipeline (W10) and depends on the carrier line (D95)."
          "AC8's executor half (with the minting forks m1, m2, the consumers r1, r2 and a join on KA and KB, the executor reaches done and `placeBound(done, 0)` is not `Proven`) is a verdict line (W10, with the reference ν firing of W9). Its Route A half is Novel.RouteA.shipped_consume, cited by NU_051_routeA_consume, and is not a line: the timeout sentence speaks of the fragment classifier, which is Route B's, and no Route A classifier is abstracted here, because whether Route A decides the EXTENDED fragment at all is clash nu-c#1 (ruling D20 open). Its last sentence ('A consumer whose timeout forwards its coloured input is still a relay') is line 3 with a forward of the consumed input, shown in NU_051_nonvacuous."
          "AC2's 'no false `Proven` from an over-counted name layer, no dropped base-enabled firing' is the soundness the refusal buys ([NU-050], W9); the block states the refusal."
          "Whether a transition is a mint (declared, and writing no coloured place on timeout) is [NU-010]'s verifier line (Novel.RouteB.classifyS_mint), not this block's."
  signoff "pending"
  statement : Classifier → Prop :=
    fun C =>
      (∀ col declared tw T, T.keys = none → ColouredInputs col T ≠ [] →
        C col .base declared tw T = none) ∧
      (∀ col declared tw T r, T.keys = none → ColouredInputs col T ≠ [] →
        C col .extended declared tw T = some r →
          SingleColouredWrites col T ∧ ∃ s, ColouredInputs col T = [s] ∧ UnitCount s ∧
            r = .consume s.place ∧ ForwardsOnly col tw s.place) ∧
      (∀ col declared tw T s, T.keys = none → ¬ ColouredTestArc col T →
        SingleColouredWrites col T → ColouredInputs col T = [s] → UnitCount s →
        ForwardsOnly col tw s.place → C col .extended declared tw T = some (.consume s.place)) ∧
      (∀ col mode declared tw T, ColouredTestArc col T → C col mode declared tw T = none) ∧
      (∀ col mode declared tw T ks, T.keys = some ks →
        (∃ s ∈ ColouredInputs col T, s.place ∉ ks) → C col mode declared tw T = none) ∧
      (∀ col mode declared tw T p, C col mode declared tw T = some (.consume p) →
        mode = .extended ∧ T.keys = none ∧ ColouredInputs col T ≠ [])

/- The pinned readable form of NU-051: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_051 : Classifier → Prop :=
fun C =>
  (∀ (col : PlaceId → Bool) (declared : Bool) (tw : List (PlaceId × TW)) (T : NuTrans),
      T.keys = none → ColouredInputs col T ≠ [] → C col Mode.base declared tw T = none) ∧
    (∀ (col : PlaceId → Bool) (declared : Bool) (tw : List (PlaceId × TW)) (T : NuTrans) (r : Role),
        T.keys = none →
          ColouredInputs col T ≠ [] →
            C col Mode.extended declared tw T = some r →
              SingleColouredWrites col T ∧
                ∃ s,
                  ColouredInputs col T = [s] ∧ UnitCount s ∧ r = Role.consume s.place ∧ ForwardsOnly col tw s.place) ∧
      (∀ (col : PlaceId → Bool) (declared : Bool) (tw : List (PlaceId × TW)) (T : NuTrans) (s : InSpec),
          T.keys = none →
            ¬ColouredTestArc col T →
              SingleColouredWrites col T →
                ColouredInputs col T = [s] →
                  UnitCount s →
                    ForwardsOnly col tw s.place → C col Mode.extended declared tw T = some (Role.consume s.place)) ∧
        (∀ (col : PlaceId → Bool) (mode : Mode) (declared : Bool) (tw : List (PlaceId × TW)) (T : NuTrans),
            ColouredTestArc col T → C col mode declared tw T = none) ∧
          (∀ (col : PlaceId → Bool) (mode : Mode) (declared : Bool) (tw : List (PlaceId × TW)) (T : NuTrans)
              (ks : List PlaceId),
              T.keys = some ks → (∃ s ∈ ColouredInputs col T, s.place ∉ ks) → C col mode declared tw T = none) ∧
            ∀ (col : PlaceId → Bool) (mode : Mode) (declared : Bool) (tw : List (PlaceId × TW)) (T : NuTrans)
              (p : PlaceId),
              C col mode declared tw T = some (Role.consume p) →
                mode = Mode.extended ∧ T.keys = none ∧ ColouredInputs col T ≠ []
-/
#guard_msgs in #print NU_051

/-! ### Bridge lemmas over the shipped classifier -/

/-- A test arc on a coloured place fails `arcsOk`. -/
theorem nu051_arcsOk_false {col : PlaceId → Bool} {T : NuTrans} (h : ColouredTestArc col T) :
    arcsOk col T = false := by
  obtain ⟨p, hp, hr | hr | hr⟩ := h <;>
    simp only [arcsOk, Bool.not_eq_false', Bool.or_eq_true, List.any_eq_true] <;>
    first
      | exact Or.inl (Or.inl ⟨p, hr, hp⟩)
      | exact Or.inl (Or.inr ⟨p, hr, hp⟩)
      | exact Or.inr ⟨p, hr, hp⟩

/-- Without a test arc on a coloured place, `arcsOk` holds. -/
theorem nu051_arcsOk_true {col : PlaceId → Bool} {T : NuTrans} (h : ¬ ColouredTestArc col T) :
    arcsOk col T = true := by
  cases hc : arcsOk col T with
  | true => rfl
  | false =>
    exfalso
    apply h
    simp only [arcsOk, Bool.not_eq_false', Bool.or_eq_true, List.any_eq_true] at hc
    rcases hc with (⟨p, hr, hp⟩ | ⟨p, hr, hp⟩) | ⟨p, hr, hp⟩
    · exact ⟨p, hp, Or.inl hr⟩
    · exact ⟨p, hp, Or.inr (Or.inl hr)⟩
    · exact ⟨p, hp, Or.inr (Or.inr hr)⟩

/-- When `classifyT` refuses, `classifyS` refuses. -/
theorem nu051_classifyS_none {col : PlaceId → Bool} {mode : Mode} {declared : Bool}
    {tw : List (PlaceId × TW)} {T : NuTrans} (h : classifyT col mode true T = none) :
    classifyS col mode declared tw T = none := by
  simp [classifyS, h]

/-- The branch rule of `classifyT` passes when every branch writes one token into each coloured
place it writes and drains none into one. -/
theorem nu051_rows_ok {col : PlaceId → Bool} {T : NuTrans} (h : SingleColouredWrites col T) :
    (T.rows.any fun r => r.fixed.any (fun p => col p && r.fixed.count p != 1)
      || r.drains.any fun x => col x.1) = false := by
  rw [Bool.eq_false_iff]
  intro hany
  obtain ⟨r, hr, hor⟩ := List.any_eq_true.mp hany
  obtain ⟨hfix, hdr⟩ := h r hr
  rcases Bool.or_eq_true_iff.mp hor with hf | hd
  · obtain ⟨p, hp, hpc⟩ := List.any_eq_true.mp hf
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hpc
    exact hpc.2 (hfix p hp hpc.1)
  · obtain ⟨x, hx, hxc⟩ := List.any_eq_true.mp hd
    rw [hdr x hx] at hxc
    exact Bool.false_ne_true hxc

/-- The converse: a branch check that passes gives SingleColouredWrites. -/
theorem nu051_rows_of {col : PlaceId → Bool} {T : NuTrans}
    (h : (T.rows.any fun r => r.fixed.any (fun p => col p && r.fixed.count p != 1)
      || r.drains.any fun x => col x.1) = false) : SingleColouredWrites col T := by
  intro r hr
  have hr' := List.any_eq_false.mp h r hr
  simp only [Bool.or_eq_true, List.any_eq_true, not_or, not_exists, not_and, Bool.and_eq_true,
    bne_iff_ne, ne_eq, not_not] at hr'
  refine ⟨fun p hp hc => hr'.1 p hp hc, fun x hx => ?_⟩
  cases hc : col x.1 with
  | false => rfl
  | true => exact absurd hc (hr'.2 x hx)

/-- `classifyT` (with or without the off-key rule) gives the coloured-consumer role only under
EXTENDED, to a transition without a match spec whose branches pass the branch check and whose
coloured inputs are one input at count one, the role's place. -/
theorem nu051_classifyT_consume {col : PlaceId → Bool} {mode : Mode} {off : Bool} {T : NuTrans}
    {p : PlaceId} (h : classifyT col mode off T = some (Role.consume p)) :
    mode = .extended ∧ T.keys = none ∧ SingleColouredWrites col T ∧
      ∃ s, ColouredInputs col T = [s] ∧ UnitCount s ∧ p = s.place := by
  unfold classifyT at h
  by_cases h1 : (!(arcsOk col T)) = true
  · simp [h1] at h
  rw [if_neg h1] at h
  by_cases h2 : (T.rows.any fun r => r.fixed.any (fun p => col p && r.fixed.count p != 1)
      || r.drains.any fun x => col x.1) = true
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  have hw : SingleColouredWrites col T := nu051_rows_of (by simpa using h2)
  cases hk : T.keys with
  | some ks =>
    exfalso
    rw [hk] at h
    simp only at h
    split_ifs at h
    all_goals (cases hm : ks.mapM (keyCount T) <;> simp [hm] at h)
  | none =>
    rw [hk] at h
    simp only at h
    unfold ColouredInputs
    generalize List.filter (fun s => col s.place) T.base.inputs = l at h ⊢
    split_ifs at h with h3
    · match mode, l, h with
      | .extended, [s], h =>
        refine ⟨rfl, rfl, hw, s, rfl, ?_⟩
        cases hc : s.card with
        | one =>
          simp only [hc] at h; exact ⟨Or.inl hc, (Role.consume.inj (Option.some.inj h)).symm⟩
        | exactly n =>
          simp only [hc] at h
          split at h
          · rename_i heq; cases heq
          · rename_i heq; cases heq
            exact ⟨Or.inr hc, (Role.consume.inj (Option.some.inj h)).symm⟩
          · cases h
        | all => simp [hc] at h
        | atLeast n => simp [hc] at h
      | .base, _, h => simp at h
      | .extended, [], h => simp at h
      | .extended, _ :: _ :: _, h => simp at h
    all_goals cases h

/-- The shipped classifier satisfies NU-051. -/
@[evidence holds NU_051]
theorem NU_051_reference : NU_051 refClassify := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro col declared tw T hk hne
    apply nu051_classifyS_none
    unfold ColouredInputs at hne
    simp only [classifyT, hk]
    split_ifs <;> simp_all
  · intro col declared tw T r hk hne h
    have hT := classifyS_sub h
    have hS := h
    unfold ColouredInputs at hne ⊢
    simp only [classifyT, hk] at hT
    by_cases h1 : (!(arcsOk col T)) = true
    · simp [h1] at hT
    · rw [if_neg h1] at hT
      split_ifs at hT with h2 h3 h4
      · generalize hl : List.filter (fun s => col s.place) T.base.inputs = l at hT hne ⊢
        match l, hT with
        | [s], hT =>
          have hr : r = Role.consume s.place := by
            cases hc : s.card with
            | one => simp only [hc] at hT; exact (Option.some.inj hT).symm
            | exactly n =>
              simp only [hc] at hT
              split at hT
              · rename_i heq; cases heq
              · exact (Option.some.inj hT).symm
              · cases hT
            | all => simp [hc] at hT
            | atLeast n => simp [hc] at hT
          have hu : UnitCount s := by
            cases hc : s.card with
            | one => exact Or.inl hc
            | exactly n =>
              simp only [hc] at hT
              split at hT
              · rename_i heq; cases heq
              · rename_i heq; cases heq; exact Or.inr hc
              · cases hT
            | all => simp [hc] at hT
            | atLeast n => simp [hc] at hT
          subst hr
          exact ⟨(nu051_classifyT_consume (classifyS_sub hS)).2.2.1, s, rfl, hu, rfl,
            classifyS_consume hS⟩
      · exact absurd (by simpa using h3) hne
      · exact absurd (by simpa using h3) hne
  · intro col declared tw T s hk harc hrows hs hu hfw
    have ha := nu051_arcsOk_true harc
    have hro := nu051_rows_ok hrows
    unfold ColouredInputs at hs
    have hT : classifyT col .extended true T = some (Role.consume s.place) := by
      simp only [classifyT, hk, ha, hro, hs, Bool.not_true, Bool.false_eq_true, if_false,
        List.isEmpty_cons, Bool.not_false, if_true]
      rcases hu with hc | hc <;> simp [hc]
    have hall : tw.all (fun w => !col w.1 || w.2 == TW.forward s.place) = true := by
      rw [List.all_eq_true]
      intro w hw
      cases hcw : col w.1 with
      | false => rfl
      | true => simp [hfw w hw hcw]
    simp only [refClassify, classifyS, hT, hall, if_true]
  · intro col mode declared tw T h
    exact nu051_classifyS_none (by simp [classifyT, nu051_arcsOk_false h])
  · intro col mode declared tw T ks hk ⟨s, hs, hns⟩
    apply nu051_classifyS_none
    unfold ColouredInputs at hs
    have hoff : (List.filter (fun s => col s.place) T.base.inputs).any
        (fun s => !ks.contains s.place) = true :=
      List.any_eq_true.mpr ⟨s, hs, by simpa using hns⟩
    simp only [classifyT, hk]
    split_ifs <;> first | rfl | simp_all
  · intro col mode declared tw T p h
    obtain ⟨hm, hk, -, s, hs, -, -⟩ := nu051_classifyT_consume (classifyS_sub h)
    exact ⟨hm, hk, by rw [hs]; simp⟩

/-! ### Fixtures

Places are numbers. The coloured set of the consumer fixtures is `{0, 1}`; places `2`, `3` and
`5` are uncoloured. -/

/-- The coloured set `{0, 1}`. -/
def nu051_col : PlaceId → Bool := fun p => [0, 1].contains p

/-- An input arc at count `Exactly(2)`. -/
def nu051_inTwo (p : PlaceId) : InSpec := { place := p, card := .exactly 2, guard := none }

/-- The coloured consumer of AC1, AC6 and AC8: no match spec, coloured input `0` at count one,
uncoloured input `3` (the request), and two branches (an `Xor`): branch 1 writes the coloured
place `1` (a relay), branch 2 the uncoloured place `2` (a drain). -/
def nu051_cons : NuTrans where
  base := { name := "r", inputs := [inOne 0, inOne 3], inhibitors := [], reads := [],
            resets := [] }
  rows := [⟨[1], []⟩, ⟨[2], []⟩]
  keys := none
  relays := []

/-- The AC2 consumer at count `Exactly(2)`. -/
def nu051_consTwoCount : NuTrans :=
  { nu051_cons with base := { nu051_cons.base with inputs := [nu051_inTwo 0, inOne 3] } }

/-- The AC2 consumer of two coloured inputs, `0` and `1`, writing the uncoloured place `2`. -/
def nu051_consTwoInputs : NuTrans where
  base := { name := "r2", inputs := [inOne 0, inOne 1], inhibitors := [], reads := [],
            resets := [] }
  rows := [⟨[2], []⟩]
  keys := none
  relays := []

/-- The AC3 consumer: `nu051_cons` with a reset arc on its coloured input `0`. -/
def nu051_consReset : NuTrans :=
  { nu051_cons with base := { nu051_cons.base with resets := [0] } }

/-- A consumer of the coloured place `0` (count one) and the request `3` whose one branch puts two
tokens into the coloured place `1`. -/
def nu051_consDouble : NuTrans :=
  { nu051_cons with rows := [⟨[1, 1], []⟩] }

/-- A consumer of the coloured place `0` (count one) and the request `3` whose one branch puts a
drained batch of `3` into the coloured place `1`. -/
def nu051_consDrained : NuTrans :=
  { nu051_cons with rows := [⟨[], [(1, 3)]⟩] }

/-- A transition with no match spec that consumes only the uncoloured request `3` and writes the
uncoloured place `2`: an ordinary transition. -/
def nu051_ord : NuTrans where
  base := { name := "o", inputs := [inOne 3], inhibitors := [], reads := [], resets := [] }
  rows := [⟨[2], []⟩]
  keys := none
  relays := []

/-- A one-key ν-transition: match spec keyed on the coloured place `0`, which it consumes at count
one, writing the uncoloured place `2`. -/
def nu051_key1 : NuTrans where
  base := { name := "k", inputs := [inOne 0], inhibitors := [], reads := [], resets := [] }
  rows := [⟨[2], []⟩]
  keys := some [0]
  relays := []

/-- A join keyed on the coloured places `0`, `1`, writing the uncoloured place `3`. -/
def nu051_join : NuTrans where
  base := { name := "J2", inputs := [inOne 0, inOne 1], inhibitors := [], reads := [],
            resets := [] }
  rows := [⟨[3], []⟩]
  keys := some [0, 1]
  relays := []

/-- The join `nu051_join` with a read arc on its coloured key `0`. -/
def nu051_joinRead : NuTrans :=
  { nu051_join with base := { nu051_join.base with reads := [0] } }

/-- A mint: no match spec, consumes the uncoloured budget `3`, writes the coloured place `0`. -/
def nu051_mint : NuTrans where
  base := { name := "m", inputs := [inOne 3], inhibitors := [], reads := [], resets := [] }
  rows := [⟨[0], []⟩]
  keys := none
  relays := []

/-- The mint `nu051_mint` with an inhibitor arc on the coloured place `1`. -/
def nu051_mintInh : NuTrans :=
  { nu051_mint with base := { nu051_mint.base with inhibitors := [1] } }

/-- A join keyed on the coloured places `0`, `1` of `colW` that also consumes the uncoloured
budget place `5`, writing `3`: a non-coloured non-key input. -/
def nu051_joinBudget : NuTrans where
  base := { name := "JB", inputs := [inOne 0, inOne 1, inOne 5], inhibitors := [], reads := [],
            resets := [] }
  rows := [⟨[3], []⟩]
  keys := some [0, 1]
  relays := []

/-- All rules of NU-051 bite on the shipped classifier: the consumer fixture, an `Xor` that relays
into `1` on one branch and drains on the other, gets the coloured-consumer role of `0` under
EXTENDED (AC1, AC6), also when declared a mint and when its timeout forwards its coloured input
into `1` (AC8, last sentence), and no role under BASE (AC1), nor when its timeout writes a unit
token into `1` or forwards the request `3` there (AC8); the `Exactly(2)` consumer and the consumer
of two coloured inputs get no role (AC2), nor do the consumers that put two tokens or a drained
batch into a coloured place; the consumer with a reset arc on its coloured input gets none in
either mode (AC3), and so do the join with a read arc and the mint with an inhibitor arc on a
coloured place, while the same join and mint without the arc get their roles; the off-key join
`tJ` gets none in either mode (AC7) while the join with an uncoloured budget input gets its join
role; the transition with no coloured input gets the ordinary role and the one-key join its join
role, in each mode, not the coloured-consumer role (line 6). -/
@[evidence nonvacuous NU_051]
theorem NU_051_nonvacuous :
    refClassify nu051_col .extended false [] nu051_cons = some (.consume 0) ∧
    refClassify nu051_col .extended true [] nu051_cons = some (.consume 0) ∧
    refClassify nu051_col .extended false [(1, .forward 0)] nu051_cons = some (.consume 0) ∧
    refClassify nu051_col .base false [] nu051_cons = none ∧
    refClassify nu051_col .extended false [(1, .unit)] nu051_cons = none ∧
    refClassify nu051_col .extended false [(1, .forward 3)] nu051_cons = none ∧
    refClassify nu051_col .extended false [] nu051_consTwoCount = none ∧
    refClassify nu051_col .extended false [] nu051_consTwoInputs = none ∧
    refClassify nu051_col .extended false [] nu051_consDouble = none ∧
    refClassify nu051_col .extended false [] nu051_consDrained = none ∧
    refClassify nu051_col .base false [] nu051_consReset = none ∧
    refClassify nu051_col .extended false [] nu051_consReset = none ∧
    refClassify nu051_col .base false [] nu051_join = some (.join [(0, 1), (1, 1)] []) ∧
    refClassify nu051_col .base false [] nu051_joinRead = none ∧
    refClassify nu051_col .extended false [] nu051_joinRead = none ∧
    refClassify nu051_col .extended true [] nu051_mint = some .mint ∧
    refClassify nu051_col .base true [] nu051_mintInh = none ∧
    refClassify nu051_col .extended true [] nu051_mintInh = none ∧
    refClassify colW .base false [] tJ = none ∧
    refClassify colW .extended false [] tJ = none ∧
    refClassify colW .base false [] nu051_joinBudget = some (.join [(0, 1), (1, 1)] []) ∧
    refClassify nu051_col .base false [] nu051_ord = some .ordinary ∧
    refClassify nu051_col .extended false [] nu051_ord = some .ordinary ∧
    refClassify nu051_col .extended false [] nu051_key1 = some (.join [(0, 1)] []) := by
  decide

/-! ### Classifiers that break one rule each -/

/-- A classifier that reads BASE as EXTENDED. -/
def nu051_baseAsExtended : Classifier := fun col _ declared tw T =>
  refClassify col .extended declared tw T

/-- ✗ A coloured consumer under BASE violates NU-051 (line 1): reading BASE as EXTENDED gives
`nu051_cons` the coloured-consumer role. -/
@[evidence forbids NU_051]
theorem NU_051_forbids_baseAsExtended : ¬ NU_051 nu051_baseAsExtended := by
  intro h
  have := h.1 nu051_col false [] nu051_cons rfl (by decide)
  revert this; decide

/-- A classifier that reads every input arc as `One`. -/
def nu051_anyCount : Classifier := fun col mode declared tw T =>
  refClassify col mode declared tw
    { T with base := { T.base with inputs := T.base.inputs.map fun s => { s with card := .one } } }

/-- ✗ A coloured consumer at count `Exactly(2)` violates NU-051 (line 2, AC2). -/
@[evidence forbids NU_051]
theorem NU_051_forbids_anyCount : ¬ NU_051 nu051_anyCount := by
  intro h
  obtain ⟨-, s, hs, hu, -, -⟩ :=
    h.2.1 nu051_col false [] nu051_consTwoCount (.consume 0) rfl (by decide) (by decide)
  have hs' : ColouredInputs nu051_col nu051_consTwoCount = [nu051_inTwo 0] := rfl
  rw [hs'] at hs
  cases hs
  rcases hu with hc | hc <;> cases hc

/-- A classifier that gives a transition without a match spec and with two or more coloured
inputs, under EXTENDED, the coloured-consumer role of the first. -/
def nu051_wideConsumer : Classifier := fun col mode declared tw T =>
  match T.keys, mode, ColouredInputs col T with
  | none, .extended, s :: _ :: _ => some (.consume s.place)
  | _, _, _ => refClassify col mode declared tw T

/-- ✗ A coloured consumer of two coloured inputs violates NU-051 (line 2, the single coloured
input, AC2). -/
@[evidence forbids NU_051]
theorem NU_051_forbids_wideConsumer : ¬ NU_051 nu051_wideConsumer := by
  intro h
  obtain ⟨-, s, hs, -, -, -⟩ :=
    h.2.1 nu051_col false [] nu051_consTwoInputs (.consume 0) rfl (by decide) (by decide)
  have hs' : ColouredInputs nu051_col nu051_consTwoInputs = [inOne 0, inOne 1] := rfl
  rw [hs'] at hs
  cases hs

/-- A classifier that gives a coloured consumer the ordinary role. -/
def nu051_consumerOrdinary : Classifier := fun col mode declared tw T =>
  match refClassify col mode declared tw T with
  | some (.consume _) => some .ordinary
  | r => r

/-- ✗ A coloured consumer classified as ordinary violates NU-051 (line 2, the role). -/
@[evidence forbids NU_051]
theorem NU_051_forbids_consumerOrdinary : ¬ NU_051 nu051_consumerOrdinary := by
  intro h
  obtain ⟨-, s, -, -, hr, -⟩ :=
    h.2.1 nu051_col false [] nu051_cons .ordinary rfl (by decide) (by decide)
  cases hr

/-- A classifier that gives a coloured consumer the coloured-consumer role of its last input
place, coloured or not. -/
def nu051_lastInput : Classifier := fun col mode declared tw T =>
  match refClassify col mode declared tw T with
  | some (.consume p) => some (.consume ((T.base.inputs.getLast?.map (·.place)).getD p))
  | r => r

/-- ✗ A coloured consumer given the role of another place violates NU-051 (line 2, the role's
place): `nu051_cons` gets the role of its uncoloured request `3`. -/
@[evidence forbids NU_051]
theorem NU_051_forbids_lastInput : ¬ NU_051 nu051_lastInput := by
  intro h
  obtain ⟨-, s, hs, -, hr, -⟩ :=
    h.2.1 nu051_col false [] nu051_cons (.consume 3) rfl (by decide) (by decide)
  have hs' : ColouredInputs nu051_col nu051_cons = [inOne 0] := rfl
  rw [hs'] at hs
  cases hs
  revert hr; decide

/-- The classifier of W0 probe mutant 3: under EXTENDED it decides the coloured-consumer role of
a transition without a match spec from its input arcs, its test arcs and its timeout writes only,
and skips the branch check. -/
def nu051_skipBranches : Classifier := fun col mode declared tw T =>
  if T.keys = none ∧ mode = .extended then
    match ColouredInputs col T with
    | [s] =>
      if arcsOk col T && (s.card == .one || s.card == .exactly 1)
          && tw.all (fun w => !col w.1 || w.2 == TW.forward s.place)
      then some (.consume s.place) else none
    | _ => refClassify col mode declared tw T
  else refClassify col mode declared tw T

/-- ✗ A coloured consumer whose branch puts two tokens into a coloured place violates NU-051
(line 2, the branch check): the name layer would add one token where the base marking adds
two. -/
@[evidence forbids NU_051]
theorem NU_051_forbids_skipBranches : ¬ NU_051 nu051_skipBranches := by
  intro h
  obtain ⟨hw, -⟩ :=
    h.2.1 nu051_col false [] nu051_consDouble (.consume 0) rfl (by decide) (by decide)
  have := (hw ⟨[1, 1], []⟩ (by simp [nu051_consDouble, nu051_cons])).1 1 (by simp) rfl
  revert this; decide

/-- A classifier that does not look at the timeout writes. -/
def nu051_ignoreTimeout : Classifier := fun col mode declared _ T =>
  refClassify col mode declared [] T

/-- ✗ A coloured consumer whose timeout writes a unit token into a coloured place violates
NU-051 (line 2, AC8). -/
@[evidence forbids NU_051]
theorem NU_051_forbids_ignoreTimeout : ¬ NU_051 nu051_ignoreTimeout := by
  intro h
  obtain ⟨-, s, hs, -, -, hfw⟩ :=
    h.2.1 nu051_col false [(1, .unit)] nu051_cons (.consume 0) rfl (by decide) (by decide)
  have := hfw (1, .unit) (by simp) rfl
  cases this

/-- The classifier that never gives a role. -/
def nu051_never : Classifier := fun _ _ _ _ _ => none

/-- ✗ A classifier that refuses every coloured consumer violates NU-051 (line 3, AC1). -/
@[evidence forbids NU_051]
theorem NU_051_forbids_never : ¬ NU_051 nu051_never := by
  intro h
  have hw : SingleColouredWrites nu051_col nu051_cons := by
    intro r hr
    simp only [nu051_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by decide, by decide⟩
  have := h.2.2.1 nu051_col false [] nu051_cons (inOne 0) rfl
    (fun ⟨p, hp, hr⟩ => by simp [nu051_cons] at hr) hw rfl (Or.inl rfl)
    (fun _ hw => by cases hw)
  cases this

/-- A classifier that does not look at reset, read and inhibitor arcs. -/
def nu051_ignoreArcs : Classifier := fun col mode declared tw T =>
  refClassify col mode declared tw
    { T with base := { T.base with resets := [], reads := [], inhibitors := [] } }

/-- ✗ A reset arc on a coloured place violates NU-051 when the classifier ignores it (line 4,
AC3). -/
@[evidence forbids NU_051]
theorem NU_051_forbids_ignoreArcs : ¬ NU_051 nu051_ignoreArcs := by
  intro h
  have := h.2.2.2.1 nu051_col .extended false [] nu051_consReset ⟨0, rfl, Or.inl (by decide)⟩
  revert this; decide

/-- A classifier that does not look at read arcs. -/
def nu051_ignoreReads : Classifier := fun col mode declared tw T =>
  refClassify col mode declared tw { T with base := { T.base with reads := [] } }

/-- ✗ A read arc of a matched join on a coloured place violates NU-051 when the classifier
ignores it (line 4 on a matched transition, AC3). -/
@[evidence forbids NU_051]
theorem NU_051_forbids_ignoreReads : ¬ NU_051 nu051_ignoreReads := by
  intro h
  have := h.2.2.2.1 nu051_col .base false [] nu051_joinRead ⟨0, rfl, Or.inr (Or.inl (by decide))⟩
  revert this; decide

/-- A classifier that does not look at inhibitor arcs. -/
def nu051_ignoreInhibitors : Classifier := fun col mode declared tw T =>
  refClassify col mode declared tw { T with base := { T.base with inhibitors := [] } }

/-- ✗ An inhibitor arc of a declared mint on a coloured place violates NU-051 when the classifier
ignores it (line 4 on a mint, AC3). -/
@[evidence forbids NU_051]
theorem NU_051_forbids_ignoreInhibitors : ¬ NU_051 nu051_ignoreInhibitors := by
  intro h
  have := h.2.2.2.1 nu051_col .extended true [] nu051_mintInh
    ⟨1, rfl, Or.inr (Or.inr (by decide))⟩
  revert this; decide

/-- The classifier as shipped before the off-key rule (`4d7a9d9`): `classifyS` over
`classifyT` with the off-key rule switched off. -/
def nu051_preOffKey : Classifier := fun col mode declared tw T =>
  match classifyT col mode false T with
  | some Role.mint =>
    if declared && tw.all (fun w => !col w.1) then some Role.mint else none
  | some (Role.consume p) =>
    if tw.all (fun w => !col w.1 || w.2 == TW.forward p) then some (Role.consume p) else none
  | some (Role.join cin rel) =>
    if tw.all (fun w => !col w.1 || cin.any (fun k => w.2 == TW.forward k.1))
    then some (Role.join cin rel) else none
  | r => r

/-- ✗ The off-key join violates NU-051 under the classifier before the off-key rule (line 5,
AC7). -/
@[evidence forbids NU_051]
theorem NU_051_forbids_preOffKey : ¬ NU_051 nu051_preOffKey := by
  intro h
  have := h.2.2.2.2.1 colW .base false [] tJ [0, 1] rfl
    ⟨inOne 2, by show inOne 2 ∈ [inOne 0, inOne 1, inOne 2]; simp, by decide⟩
  revert this; decide

/-- The classifier of W0 probe mutant 1: where the shipped classifier gives the ordinary role to
a transition without a match spec, it gives the coloured-consumer role of its first input place,
in both modes. -/
def nu051_ordinaryAsConsume : Classifier := fun col mode declared tw T =>
  match refClassify col mode declared tw T with
  | some Role.ordinary =>
    match T.keys, T.base.inputs with
    | none, s :: _ => some (Role.consume s.place)
    | _, _ => some Role.ordinary
  | r => r

/-- ✗ The coloured-consumer role under BASE, on a transition that consumes no coloured place,
violates NU-051 (line 6): `nu051_ord` gets the role of its uncoloured input `3`. -/
@[evidence forbids NU_051]
theorem NU_051_forbids_ordinaryAsConsume : ¬ NU_051 nu051_ordinaryAsConsume := by
  intro h
  have := (h.2.2.2.2.2 nu051_col .base false [] nu051_ord 3 (by decide)).1
  cases this

/-- The classifier of W0 probe mutant 2: under EXTENDED it gives a one-key join the
coloured-consumer role of its key, so the name layer takes any resident name off the key without
the match test ([NU-020]). -/
def nu051_joinAsConsume : Classifier := fun col mode declared tw T =>
  match refClassify col mode declared tw T with
  | some (Role.join [(k, 1)] _) =>
    if mode = .extended then some (Role.consume k) else refClassify col mode declared tw T
  | r => r

/-- ✗ A matched transition given the coloured-consumer role violates NU-051 (line 6). -/
@[evidence forbids NU_051]
theorem NU_051_forbids_joinAsConsume : ¬ NU_051 nu051_joinAsConsume := by
  intro h
  have := (h.2.2.2.2.2 nu051_col .extended false [] nu051_key1 0 (by decide)).2.1
  cases this

/-! ### Mutant readings -/

/-- Mutant reading that drops line 3: the classifier must refuse what NU-051 refuses, but need
not give a coloured consumer its role. -/
def NU_051_mutant_noConsumer (C : Classifier) : Prop :=
  (∀ col declared tw T, T.keys = none → ColouredInputs col T ≠ [] →
    C col .base declared tw T = none) ∧
  (∀ col declared tw T r, T.keys = none → ColouredInputs col T ≠ [] →
    C col .extended declared tw T = some r →
      SingleColouredWrites col T ∧ ∃ s, ColouredInputs col T = [s] ∧ UnitCount s ∧
        r = .consume s.place ∧ ForwardsOnly col tw s.place) ∧
  (∀ col mode declared tw T, ColouredTestArc col T → C col mode declared tw T = none) ∧
  (∀ col mode declared tw T ks, T.keys = some ks →
    (∃ s ∈ ColouredInputs col T, s.place ∉ ks) → C col mode declared tw T = none) ∧
  (∀ col mode declared tw T p, C col mode declared tw T = some (.consume p) →
    mode = .extended ∧ T.keys = none ∧ ColouredInputs col T ≠ [])

/-- The classifier that never gives a role kills the first mutant: it refuses everything (the
mutant holds), but not the coloured consumer `nu051_cons` (NU-051 fails). -/
@[evidence mutant NU_051]
theorem NU_051_mutant_noConsumer_killed :
    NU_051_mutant_noConsumer nu051_never ∧ ¬ NU_051 nu051_never :=
  ⟨⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ h => (by cases h)⟩, NU_051_forbids_never⟩

/-- Mutant reading that drops line 1 and the mode of line 6: a coloured consumer is checked as
under EXTENDED in both modes. -/
def NU_051_mutant_noBase (C : Classifier) : Prop :=
  (∀ col declared tw T r, T.keys = none → ColouredInputs col T ≠ [] →
    C col .extended declared tw T = some r →
      SingleColouredWrites col T ∧ ∃ s, ColouredInputs col T = [s] ∧ UnitCount s ∧
        r = .consume s.place ∧ ForwardsOnly col tw s.place) ∧
  (∀ col declared tw T s, T.keys = none → ¬ ColouredTestArc col T →
    SingleColouredWrites col T → ColouredInputs col T = [s] → UnitCount s →
    ForwardsOnly col tw s.place → C col .extended declared tw T = some (.consume s.place)) ∧
  (∀ col mode declared tw T, ColouredTestArc col T → C col mode declared tw T = none) ∧
  (∀ col mode declared tw T ks, T.keys = some ks →
    (∃ s ∈ ColouredInputs col T, s.place ∉ ks) → C col mode declared tw T = none) ∧
  (∀ col mode declared tw T p, C col mode declared tw T = some (.consume p) →
    T.keys = none ∧ ColouredInputs col T ≠ [])

/-- Reading BASE as EXTENDED kills the second mutant: every other line is the shipped
classifier's under EXTENDED (the mutant holds), but `nu051_cons` gets a role under BASE. -/
@[evidence mutant NU_051]
theorem NU_051_mutant_noBase_killed :
    NU_051_mutant_noBase nu051_baseAsExtended ∧ ¬ NU_051 nu051_baseAsExtended := by
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := NU_051_reference
  exact ⟨⟨h2, h3, fun col _ declared tw T h => h4 col .extended declared tw T h,
    fun col _ declared tw T ks hk ho => h5 col .extended declared tw T ks hk ho,
    fun col _ declared tw T p h => (h6 col .extended declared tw T p h).2⟩,
    NU_051_forbids_baseAsExtended⟩

/-- Mutant reading that drops line 5: everything but the off-key rule. -/
def NU_051_mutant_noOffKey (C : Classifier) : Prop :=
  (∀ col declared tw T, T.keys = none → ColouredInputs col T ≠ [] →
    C col .base declared tw T = none) ∧
  (∀ col declared tw T r, T.keys = none → ColouredInputs col T ≠ [] →
    C col .extended declared tw T = some r →
      SingleColouredWrites col T ∧ ∃ s, ColouredInputs col T = [s] ∧ UnitCount s ∧
        r = .consume s.place ∧ ForwardsOnly col tw s.place) ∧
  (∀ col declared tw T s, T.keys = none → ¬ ColouredTestArc col T →
    SingleColouredWrites col T → ColouredInputs col T = [s] → UnitCount s →
    ForwardsOnly col tw s.place → C col .extended declared tw T = some (.consume s.place)) ∧
  (∀ col mode declared tw T, ColouredTestArc col T → C col mode declared tw T = none) ∧
  (∀ col mode declared tw T p, C col mode declared tw T = some (.consume p) →
    mode = .extended ∧ T.keys = none ∧ ColouredInputs col T ≠ [])

/-- Without a match spec the off-key switch of `classifyT` plays no part. -/
theorem nu051_classifyT_off {col : PlaceId → Bool} {mode : Mode} {T : NuTrans}
    (hk : T.keys = none) (off : Bool) : classifyT col mode off T = classifyT col mode true T := by
  simp [classifyT, hk]

/-- Without a match spec the classifier before the off-key rule is the shipped one. -/
theorem nu051_preOffKey_eq {col : PlaceId → Bool} {mode : Mode} {declared : Bool}
    {tw : List (PlaceId × TW)} {T : NuTrans} (hk : T.keys = none) :
    nu051_preOffKey col mode declared tw T = refClassify col mode declared tw T := by
  unfold nu051_preOffKey refClassify classifyS
  rw [nu051_classifyT_off hk false]
  rcases classifyT col mode true T with _ | ((_ | _) | _ | _) <;> rfl

/-- The classifier before the off-key rule gives the coloured-consumer role only where
`classifyT` without the off-key rule does. -/
theorem nu051_preOffKey_consume {col : PlaceId → Bool} {mode : Mode} {declared : Bool}
    {tw : List (PlaceId × TW)} {T : NuTrans} {p : PlaceId}
    (h : nu051_preOffKey col mode declared tw T = some (.consume p)) :
    classifyT col mode false T = some (.consume p) := by
  unfold nu051_preOffKey at h
  split at h <;> (try split_ifs at h) <;> simp_all

/-- The classifier before the off-key rule kills the third mutant: it agrees with the shipped
classifier on every transition without a match spec, refuses every transition with a test arc on
a coloured place and gives the coloured-consumer role only where `classifyT` does (the mutant
holds), but gives the off-key join `tJ` a join role (NU-051 fails). This is the retrodiction of
`4d7a9d9` (`Novel.RouteB.offKey_rule_is_necessary` shows the name layer then keeps a name the
executor has taken). -/
@[evidence mutant NU_051]
theorem NU_051_mutant_noOffKey_killed :
    NU_051_mutant_noOffKey nu051_preOffKey ∧ ¬ NU_051 nu051_preOffKey := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := NU_051_reference
  refine ⟨⟨fun col declared tw T hk hne => ?_, fun col declared tw T r hk hne h => ?_,
    fun col declared tw T s hk ha hr hs hu hf => ?_, fun col mode declared tw T h => ?_,
    fun col mode declared tw T p h => ?_⟩, NU_051_forbids_preOffKey⟩
  · rw [nu051_preOffKey_eq hk]; exact h1 col declared tw T hk hne
  · rw [nu051_preOffKey_eq hk] at h; exact h2 col declared tw T r hk hne h
  · rw [nu051_preOffKey_eq hk]; exact h3 col declared tw T s hk ha hr hs hu hf
  · simp [nu051_preOffKey, classifyT, nu051_arcsOk_false h]
  · obtain ⟨hm, hk, -, s, hs, -, -⟩ := nu051_classifyT_consume (nu051_preOffKey_consume h)
    exact ⟨hm, hk, by rw [hs]; simp⟩

/-- Mutant reading that drops line 6: the five lines before it, which constrain the classifier
only where it refuses or gives the coloured-consumer role to a coloured consumer. -/
def NU_051_mutant_noConsumerOnly (C : Classifier) : Prop :=
  (∀ col declared tw T, T.keys = none → ColouredInputs col T ≠ [] →
    C col .base declared tw T = none) ∧
  (∀ col declared tw T r, T.keys = none → ColouredInputs col T ≠ [] →
    C col .extended declared tw T = some r →
      SingleColouredWrites col T ∧ ∃ s, ColouredInputs col T = [s] ∧ UnitCount s ∧
        r = .consume s.place ∧ ForwardsOnly col tw s.place) ∧
  (∀ col declared tw T s, T.keys = none → ¬ ColouredTestArc col T →
    SingleColouredWrites col T → ColouredInputs col T = [s] → UnitCount s →
    ForwardsOnly col tw s.place → C col .extended declared tw T = some (.consume s.place)) ∧
  (∀ col mode declared tw T, ColouredTestArc col T → C col mode declared tw T = none) ∧
  (∀ col mode declared tw T ks, T.keys = some ks →
    (∃ s ∈ ColouredInputs col T, s.place ∉ ks) → C col mode declared tw T = none)

/-- A classifier that agrees with the shipped one wherever the shipped one refuses or gives the
coloured-consumer role satisfies the reading without line 6: no other line looks anywhere
else. -/
theorem nu051_noConsumerOnly_of_agree (M : Classifier)
    (hM : ∀ col mode declared tw T,
      (refClassify col mode declared tw T = none ∨
        ∃ p, refClassify col mode declared tw T = some (.consume p)) →
      M col mode declared tw T = refClassify col mode declared tw T) :
    NU_051_mutant_noConsumerOnly M := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := NU_051_reference
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro col declared tw T hk hne
    rw [hM _ _ _ _ _ (Or.inl (h1 col declared tw T hk hne))]
    exact h1 col declared tw T hk hne
  · intro col declared tw T r hk hne h
    cases hr : refClassify col .extended declared tw T with
    | none => rw [hM _ _ _ _ _ (Or.inl hr), hr] at h; cases h
    | some r' =>
      obtain ⟨hw, s, hs, hu, hrr, hf⟩ := h2 col declared tw T r' hk hne hr
      rw [hM _ _ _ _ _ (Or.inr ⟨s.place, hrr ▸ hr⟩), hr] at h
      cases h
      exact ⟨hw, s, hs, hu, hrr, hf⟩
  · intro col declared tw T s hk ha hr hs hu hf
    have := h3 col declared tw T s hk ha hr hs hu hf
    rw [hM _ _ _ _ _ (Or.inr ⟨_, this⟩)]; exact this
  · intro col mode declared tw T h
    rw [hM _ _ _ _ _ (Or.inl (h4 col mode declared tw T h))]
    exact h4 col mode declared tw T h
  · intro col mode declared tw T ks hk ho
    rw [hM _ _ _ _ _ (Or.inl (h5 col mode declared tw T ks hk ho))]
    exact h5 col mode declared tw T ks hk ho

/-- W0 probe mutant 1 kills the fourth mutant: it agrees with the shipped classifier wherever
that one refuses or gives the coloured-consumer role (the mutant holds), but gives the
coloured-consumer role to a transition that consumes no coloured place, under BASE (NU-051
fails). -/
@[evidence mutant NU_051]
theorem NU_051_mutant_noConsumerOnly_killed :
    NU_051_mutant_noConsumerOnly nu051_ordinaryAsConsume ∧ ¬ NU_051 nu051_ordinaryAsConsume :=
  ⟨nu051_noConsumerOnly_of_agree nu051_ordinaryAsConsume fun col mode declared tw T h => by
    unfold nu051_ordinaryAsConsume
    rcases h with h | ⟨p, h⟩ <;> rw [h], NU_051_forbids_ordinaryAsConsume⟩

/-- Mutant reading that drops the branch check of line 2: a coloured consumer that gets a role
has one coloured input at count one, the role is its place's and its timeout forwards it, but its
branches may put any count into a coloured place. -/
def NU_051_mutant_noBranchCheck (C : Classifier) : Prop :=
  (∀ col declared tw T, T.keys = none → ColouredInputs col T ≠ [] →
    C col .base declared tw T = none) ∧
  (∀ col declared tw T r, T.keys = none → ColouredInputs col T ≠ [] →
    C col .extended declared tw T = some r →
      ∃ s, ColouredInputs col T = [s] ∧ UnitCount s ∧ r = .consume s.place ∧
        ForwardsOnly col tw s.place) ∧
  (∀ col declared tw T s, T.keys = none → ¬ ColouredTestArc col T →
    SingleColouredWrites col T → ColouredInputs col T = [s] → UnitCount s →
    ForwardsOnly col tw s.place → C col .extended declared tw T = some (.consume s.place)) ∧
  (∀ col mode declared tw T, ColouredTestArc col T → C col mode declared tw T = none) ∧
  (∀ col mode declared tw T ks, T.keys = some ks →
    (∃ s ∈ ColouredInputs col T, s.place ∉ ks) → C col mode declared tw T = none) ∧
  (∀ col mode declared tw T p, C col mode declared tw T = some (.consume p) →
    mode = .extended ∧ T.keys = none ∧ ColouredInputs col T ≠ [])

/-- W0 probe mutant 3 kills the fifth mutant: skipping the branch check keeps every other line
(the mutant holds), but `nu051_consDouble` gets the coloured-consumer role (NU-051 fails). -/
@[evidence mutant NU_051]
theorem NU_051_mutant_noBranchCheck_killed :
    NU_051_mutant_noBranchCheck nu051_skipBranches ∧ ¬ NU_051 nu051_skipBranches := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := NU_051_reference
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, NU_051_forbids_skipBranches⟩
  · intro col declared tw T hk hne
    unfold nu051_skipBranches
    rw [if_neg (fun h => by cases h.2)]
    exact h1 col declared tw T hk hne
  · intro col declared tw T r hk hne h
    unfold nu051_skipBranches at h
    rw [if_pos ⟨hk, rfl⟩] at h
    have h2' := fun h' => (h2 col declared tw T r hk hne h').2
    generalize hl : ColouredInputs col T = l at h hne h2'
    match l, h, h2' with
    | [s], h, _ =>
      dsimp only at h
      split_ifs at h with hc
      cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨-, hu⟩, hall⟩ := hc
      refine ⟨s, rfl, hu, rfl, fun w hw hcw => ?_⟩
      have := List.all_eq_true.mp hall w hw
      simpa [hcw] using this
    | [], h, h2' => exact h2' h
    | _ :: _ :: _, h, h2' => exact h2' h
  · intro col declared tw T s hk ha hr hs hu hf
    have harc := nu051_arcsOk_true ha
    unfold nu051_skipBranches
    rw [if_pos ⟨hk, rfl⟩, hs]
    have hall : tw.all (fun w => !col w.1 || w.2 == TW.forward s.place) = true := by
      rw [List.all_eq_true]
      intro w hw
      cases hcw : col w.1 with
      | false => rfl
      | true => simp [hf w hw hcw]
    have hu' : (s.card == .one || s.card == .exactly 1) = true := by
      rcases hu with hc | hc <;> simp [hc]
    simp only [harc, hu', hall, Bool.and_self, if_true]
  · intro col mode declared tw T h
    have harc := nu051_arcsOk_false h
    have h4' := h4 col mode declared tw T h
    unfold nu051_skipBranches
    split_ifs
    · generalize ColouredInputs col T = l
      match l with
      | [s] => simp [harc]
      | [] => exact h4'
      | _ :: _ :: _ => exact h4'
    · exact h4'
  · intro col mode declared tw T ks hk ho
    unfold nu051_skipBranches
    rw [if_neg (fun h => by rw [hk] at h; cases h.1)]
    exact h5 col mode declared tw T ks hk ho
  · intro col mode declared tw T p h
    unfold nu051_skipBranches at h
    split_ifs at h with hc
    · generalize hl : ColouredInputs col T = l at h
      match l, h, hl with
      | [s], h, _ =>
        dsimp only at h
        split_ifs at h
        exact ⟨hc.2, hc.1, by simp⟩
      | [], h, hl =>
        have := h6 col mode declared tw T p h
        rwa [hl] at this
      | _ :: _ :: _, h, hl =>
        have := h6 col mode declared tw T p h
        rwa [hl] at this
    · exact h6 col mode declared tw T p h

/-! ### Route A -/

/-- Route A refuses a coloured consumer whose coloured timeout write is not a forward of its
consumed input: a `Consume` row of the shipped plan forwards its input in every timeout write
into a coloured place (`Novel.RouteA.shipped_consume`). -/
@[evidence cites "NU-051" "AC8, Route A half: a coloured consumer whose timeout forwards another input, or writes a unit token, into a coloured place is refused by the shipped Route A plan"]
theorem NU_051_routeA_consume {C : List PlaceId} {ext : Bool} {s : Novel.RouteA.SrcRow}
    {i : PlaceId} {outs : List PlaceId}
    (h : Novel.RouteA.classifyRowG C ext (Novel.RouteA.shippedGate C s).1
      (Novel.RouteA.shippedGate C s).2 s.ms s.t s.d = some (.consume i outs)) :
    ∀ w ∈ s.tw, w.1 ∈ C → w.2 = some i :=
  Novel.RouteA.shipped_consume h

/-! ## NU-051: the relay and drain step of a coloured consumer -/

/-- A name-layer step of a coloured consumer, abstractly: from the coloured places `co` (in
order), the consumed coloured input, the coloured outputs of the fired branch, the consumed name
and a name marking (glossary-free: `Novel.RouteB.NM`, the tokens of each name in each coloured
place), the name marking after the firing. -/
abbrev ConsumerStep :=
  (co : List PlaceId) → PlaceId → List PlaceId → ℕ → NM co → NM co

/-- The Route B step of a coloured consumer (`Novel.RouteB.consumeStep`, the `Role::Consume` arm
of `name_successors`), registered as a witness model. -/
def refConsumerStep : ConsumerStep := fun co inp outs s M => consumeStep co inp outs s M

#spec_witness refConsumerStep

requirement NU_051_relay
  id "NU-051"
  title "EXTENDED Coloured-Consumer Fragment"
  kind F
  scope "the name layer of Route B"
  source verbatim "spec/12-nu-nets.md"
  quote "*When* a coloured consumer fires on a branch with a name its coloured input holds, the name layer *shall* remove one token of that name from the input, add one token of that name to each coloured output of the branch and change no other count, so a branch with no coloured output drains the name."
  reading "For every list co of distinct coloured places, consumed input inp, list outs of distinct coloured outputs of the fired branch, consumed name s resident in inp and name marking M, and for every name u and coloured place i: the step's count of u at i, plus one if u is s and i is inp, equals M's count of u at i, plus one if u is s and i is in outs."
  assumes "The step is the name layer of Route B (`Novel.RouteB.NM`: the tokens of each name in each coloured place); which transition gets the coloured-consumer role is the block NU_051. The step is applied to a name resident in the consumed input (Route B's `will_fire` for a consumer), hence the premise that s has a token in inp, which the sentence states as 'with a name its coloured input holds'. Which resident name a consumer takes (any, on Route B; the oldest, FIFO, in the executor) is not this line's: it is the action contract and [NU-050]'s soundness; the outputs are the coloured places of the fired branch, without repetition (`colOut`), hence the premises on co and outs."
          "The line is the quoted sentence, which restates 'A coloured consumer relays the consumed name-symbol into each coloured output of the fired branch (threading the same name), or drains it (dead-letters the name) on a branch that produces no coloured output'. A relay back into the consumed input leaves its count as it was, which the equation allows. That the name the action writes is the consumed one is the action contract (kind A, see NU_051): this line says what the name layer does, the contract is why that matches the executor ([NU-050], W9)."
          "AC6 (one `Xor` consumer relays on one branch and drains on another) is this line with outs the coloured outputs of each branch; NU_051_relay_nonvacuous applies it to one branch with a coloured output and one with none. The other acceptance criteria are the block NU_051's subject, which accounts for each."
  signoff "pending"
  statement : ConsumerStep → Prop :=
    fun S => ∀ (co : List PlaceId), co.Nodup → ∀ (inp : PlaceId) (outs : List PlaceId) (s : ℕ)
      (M : NM co), outs.Nodup → 1 ≤ cnt co M s inp → ∀ (u : ℕ) (i : Fin co.length),
        S co inp outs s M u i + (if u = s ∧ co[i.1] = inp then 1 else 0) =
          M u i + (if u = s ∧ co[i.1] ∈ outs then 1 else 0)

/- The pinned readable form of the relay line of NU-051. -/
/--
info: def Libpetri.Spec.NU_051_relay : ConsumerStep → Prop :=
fun S =>
  ∀ (co : List PlaceId),
    co.Nodup →
      ∀ (inp : PlaceId) (outs : List PlaceId) (s : ℕ) (M : NM co),
        outs.Nodup →
          1 ≤ cnt co M s inp →
            ∀ (u : ℕ) (i : Fin co.length),
              (S co inp outs s M u i + if u = s ∧ co[↑i] = inp then 1 else 0) =
                M u i + if u = s ∧ co[↑i] ∈ outs then 1 else 0
-/
#guard_msgs in #print NU_051_relay

/-- The Route B consumer step satisfies the relay line: it removes one token of `s` from the
input (`removeAt_apply`, the name is resident) and adds one to each output
(`foldl_add_apply`). -/
@[evidence holds NU_051_relay]
theorem NU_051_relay_reference : NU_051_relay refConsumerStep := by
  intro co hco inp outs s M hnd hres u i
  simp only [refConsumerStep, consumeStep]
  rw [foldl_add_apply hco s outs hnd, removeAt_apply hco inp s 1 M hres u i]
  by_cases h : u = s ∧ co[i.1] = inp
  · obtain ⟨rfl, hi⟩ := h
    have h1 : 1 ≤ M u i := by rw [← hi, cnt_get hco] at hres; exact hres
    simp only [hi, and_self, if_true]
    split_ifs <;> omega
  · rw [if_neg h]
    simp only [Nat.sub_zero, Nat.add_zero]

/-- The fixture name marking: one token of name `0` in the coloured place `0` of `[0, 1]`. -/
def nu051_M : NM [0, 1] := fun u i => if u = 0 ∧ i.1 = 0 then 1 else 0

/-- A step that consumes the name and mints a fresh one (`s + 1`) into the outputs: the
consume-and-remint transition the contract excludes. -/
def nu051_remint : ConsumerStep := fun co inp outs s M =>
  outs.foldl (fun M p => addAt co p (s + 1) 1 M) (removeAt co inp s 1 M)

/-- ✗ A consumer step that re-mints violates the relay line: relaying name `0` from `0` into `1`
leaves no token of `0` in `1`. -/
@[evidence forbids NU_051_relay]
theorem NU_051_relay_forbids_remint : ¬ NU_051_relay nu051_remint := by
  intro h
  have := h [0, 1] (by decide) 0 [1] 0 nu051_M (by decide) (by decide) 0 ⟨1, by decide⟩
  revert this; decide

/-- A step that copies the name into the outputs and leaves the consumed token in the input. -/
def nu051_keepInput : ConsumerStep := fun co _ outs s M =>
  outs.foldl (fun M p => addAt co p s 1 M) M

/-- ✗ A consumer step that does not take the name out of its input violates the relay line. -/
@[evidence forbids NU_051_relay]
theorem NU_051_relay_forbids_keepInput : ¬ NU_051_relay nu051_keepInput := by
  intro h
  have := h [0, 1] (by decide) 0 [1] 0 nu051_M (by decide) (by decide) 0 ⟨0, by decide⟩
  revert this; decide

/-- Mutant reading of the relay line that keeps only its relay half: each coloured output of the
branch other than the input gains one token of the consumed name, and nothing is said of the
input or of any other count. -/
def NU_051_relay_mutant_relayOnly (S : ConsumerStep) : Prop :=
  ∀ (co : List PlaceId), co.Nodup → ∀ (inp : PlaceId) (outs : List PlaceId) (s : ℕ)
    (M : NM co), outs.Nodup → 1 ≤ cnt co M s inp → ∀ (i : Fin co.length),
      co[i.1] ∈ outs → co[i.1] ≠ inp → S co inp outs s M s i = M s i + 1

/-- The step that leaves the consumed token in its input kills the relay-only mutant: it adds one
token of the name to each output (`foldl_add_apply`), so it meets the mutant reading, but the
relay line asks the input to lose the token (`NU_051_relay_forbids_keepInput`). -/
@[evidence mutant NU_051_relay]
theorem NU_051_relay_mutant_relayOnly_killed :
    NU_051_relay_mutant_relayOnly nu051_keepInput ∧ ¬ NU_051_relay nu051_keepInput := by
  refine ⟨fun co hco _ outs s M hnd _ i ho _ => ?_, NU_051_relay_forbids_keepInput⟩
  simp only [nu051_keepInput]
  rw [foldl_add_apply hco s outs hnd]
  simp [ho]

/-- The relay line bites on the Route B step: name `0` is resident in place `0`; the branch that
writes the coloured place `1` moves it there (relay), the branch with no coloured output leaves
no token of it (drain), and no other name gains a token. -/
@[evidence nonvacuous NU_051_relay]
theorem NU_051_relay_nonvacuous :
    1 ≤ cnt [0, 1] nu051_M 0 0 ∧
    refConsumerStep [0, 1] 0 [1] 0 nu051_M 0 ⟨0, by decide⟩ = 0 ∧
    refConsumerStep [0, 1] 0 [1] 0 nu051_M 0 ⟨1, by decide⟩ = 1 ∧
    refConsumerStep [0, 1] 0 [] 0 nu051_M 0 ⟨0, by decide⟩ = 0 ∧
    refConsumerStep [0, 1] 0 [] 0 nu051_M 0 ⟨1, by decide⟩ = 0 ∧
    refConsumerStep [0, 1] 0 [1] 0 nu051_M 1 ⟨1, by decide⟩ = 0 := by
  decide

end Libpetri.Spec
