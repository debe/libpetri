import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryNuVer
import Libpetri.Reference.NuLink
import Libpetri.Spec.Text.NU_055

set_option linter.missingDocs true

/-!
# NU-055: Name alignment (`spec/12-nu-nets.md`)

Three blocks, one per kind of claim the section makes.

* `NU_055` (kind F): the alignment predicate on a class of the Route B graph. It is a predicate
  over an abstract check `A : AlignCheck` that answers, for the coloured set, a non-empty list
  `S` of places and a class, whether the class is aligned on `S`. Witness: `refAlignCheck`, the
  shipped `alignedAll` (`Novel/RouteB/Aligned.lean`). Its one line fixes the check on every
  non-empty list, so the invariances the spec derives from it (name permutation, canonical key,
  order and repeats of `S`) are theorems of the line (`NU_055_perm`, `NU_055_key`,
  `NU_055_members`), not lines. Wrong checks: the cross pairs without the self pairs (AC7), a
  check that compares names with a fixed name, and a check that reads only the first place of
  `S`. Mutant reading: the line without its self pairs, which the cross-pairs check meets.
* `NU_055_sound` (kind B, with the premises the soundness theorems need as hypotheses): a
  Route B `Proven` of `NameAligned(S)` holds in every marking a contract-keeping run of the
  reference ν executor reaches (`NuLink.RefNuRunB`, untimed, environment-free, atomic), and a
  `Proven` of `QuiescentNameAligned(S)` in every marking at which it rests (`NuRests`). It is a
  predicate over an abstract pair of deciders, asked on the Route B call of a reference net.
  Witnesses: `refNameAligned` (glossary `GlossaryNuVer.lean`) and `refQuiescentNameAligned`
  (here).
* `NU_055_truncation` (kind F): the verdict read off a built graph. A graph that did not close
  never gives `Proven`, gives `Unknown` when no class violates the property and, when it reached
  the class bound, `Violated` when one does (the prefix rule, ruling D59 (a)); a closed graph
  gives `Proven` exactly when no class violates it; a `Violated` names a violating class. It is
  a predicate over an abstract verdict function on a built graph. Witness: `refClassVerdict`, the
  shipped `Decide.verdict`.

The refusal order is a fourth block, `NU_055_refusal` in `NU_055_steps.lean`. Left out, each by
an assumes sentence of a block: the routing and gate rules ('Route B only', Route B before a budget
place, lifting the no-match gates for these properties only), which are dispatch and classifier
rules of the verifier pipeline; the counterexample's report shape (VER-003 under ruling D40 (a));
the timed graph (gap R6) and in-flight markings, which the spec itself leaves unproved; the API
shape and descriptions (N).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel.RouteB Libpetri.Novel.CanonicalKey

/-! ## NU-055 (F): the alignment predicate -/

/-- An alignment check: for the coloured set `co`, the base type `β` of the classes, a list of
places `S` and a class of the Route B graph, whether the class is aligned on `S`. -/
abbrev AlignCheck := (co : List PlaceId) → (β : Type) → List PlaceId → NState co β → Bool

/-- The shipped check: `alignedAll` (Rust `aligned_all`), every pair of places of `S`, self
pairs included, `aligned`. Registered as a witness model. -/
def refAlignCheck : AlignCheck := fun _ _ ps S => alignedAll ps S

#spec_witness refAlignCheck

requirement NU_055
  id "NU-055"
  title "Name Alignment"
  kind F
  scope "every verifier that offers NameAligned or QuiescentNameAligned (MAY); the predicate on a class of the Route B graph"
  source verbatim "spec/12-nu-nets.md"
  covers NU_055.s2, NU_055.s3, NU_055.s5, NU_055.s6, NU_055.s7, NU_055.s9, NU_055.s10
  reading "For every coloured set co, base type β, non-empty list ps and class S of the graph, the check A answers true exactly when any name-symbol s resident in a place p of ps and any name-symbol t resident in a place q of ps, p = q allowed, are equal."
  assumes "The model is a class of the Route B graph (NState co β, Graph.lean): a base b, a name layer m giving each name-symbol and each coloured place (a position of co) a count, and a bound above every live symbol. A name-symbol s is resident in p when its count there is not 0 (Name.lean resident). The NameAligned bullet speaks of a marking; its EARS restatement and the line speak of a class of the graph, which is where Route B evaluates the predicate. A marking's names are read on its coloured places through the one projection nameOf: its class is its name view (view co nameOf m), and on that view the line is the statement that all tokens in the places of S carry one name (alignedAll_view_iff, cited). Places are PlaceId, so 'its places compare by name' is equality of ids, and the check takes S as a list."
          "The line is the definition of the NameAligned bullet (its second and third sentences, restated by the EARS sentence): self pairs included, so a place holding two names fails whatever the others hold, and an empty place has no resident symbol and imposes nothing. The QuiescentNameAligned bullet reads 'the same predicate'; where it is read is NU_055_sound's subject. The first sentence of the NameAligned bullet ('in every reachable marking') is NU_055_sound's."
          "The permutation sentence, the first half of the canonical-key sentence and the S-order sentences ('a place listed twice counts once', 'The order of S changes no verdict', read on the predicate) are consequences of the line, not lines of their own: the line fixes A on every non-empty list, so A is the shipped check there (NU_055_eq_ref), and NU_055_perm, NU_055_key and NU_055_members derive the three invariances. The spec states them with 'so' and 'therefore', and they get no EARS sentence. The models that break one of them (nu055_symZero, nu055_headOnly) are killed by the line itself. The second half of the canonical-key sentence ('deciding it on the name-permutation quotient decides it on the graph') is also a claim about the verdict: the verdict on a closed graph is the predicate's answer over its classes, NU_055_truncation line 3."
          "An uncoloured place has no row in the name layer, so nothing is resident there (resident_of_not_mem) and the line holds vacuously for it (alignedAll_uncoloured, cited). That such a place is refused (refusal step 6, 'Coloured places only', AC2) is not a line of this block: it is line 6 of the refusal block NU_055_refusal (NU_055_steps.lean), whose NU_055_refusal_uncoloured_refused shows that such a place never reaches the graph, and whose NU_055_refusal_forbids_noUncoloured kills the design's mutant 'proves on an uncoloured place'."
          "'A place listed twice counts once, at its first occurrence' also fixes the description and which place a reason names, and 'The order of S changes no verdict' also covers the reason of an Unknown. The description (the Property: line) is N (an API note), and which place a reason names is the refusal order's (NU_055_refusal). On the predicate, the only part of the verdict this block models, order and repeats change nothing (NU_055_members)."
          "'An empty S MUST be rejected where it is constructed' and 'S is a non-empty list' are the language API (N): each constructor rejects an empty list (Java records, the TypeScript signature, the Rust panic, the Python ValueError). The line is stated for a non-empty S only, so the block fixes no answer for the empty list, which never reaches a verdict."
          "AC5 (invariance under name permutation, on a class and that class permuted, and under reordering S) is NU_055_perm and NU_055_members, theorems of the line; its run of the worked example with names minted in another scope ([NU-010]) is a test of the minter (NU-010, NU-011) and of the verdict, not of the predicate, and is not encoded."
          "AC7 ('S is a list'; the cross pair of reply and staged without the self pairs would accept a marking with two stale replies in reply) is the line with self pairs: NU_055_forbids_crossOnly kills the check without self pairs. AC7's construction rules are the API (N, above) and NU_055_members; its descriptions are N; its verdicts and witness lengths on the worked example are tests on the fixtures (Q), as the Route B graph of that net is not computed in Lean."
  signoff "2026-11-13 844b7488adecca57 ai"
  statement : AlignCheck → Prop :=
    fun A => ∀ (co : List PlaceId) (β : Type) (ps : List PlaceId) (S : NState co β), ps ≠ [] →
      (A co β ps S = true ↔
        ∀ p ∈ ps, ∀ q ∈ ps, ∀ s t, resident co p S.m s = true → resident co q S.m t = true →
          s = t)

/- The pinned readable form of NU_055: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_055 : AlignCheck → Prop :=
fun A =>
  ∀ (co : List PlaceId) (β : Type) (ps : List PlaceId) (S : NState co β),
    ps ≠ [] →
      (A co β ps S = true ↔
        ∀ p ∈ ps, ∀ q ∈ ps, ∀ (s t : ℕ), resident co p S.m s = true → resident co q S.m t = true → s = t)
-/
#guard_msgs in #print NU_055

/-! ### The reference -/

/-- Renaming the name-symbols of a class does not change `alignedAll`. -/
theorem nu055_alignedAll_perm {co : List PlaceId} {β : Type} (ps : List PlaceId)
    (σ : Equiv.Perm ℕ) {a b : NState co β} (hm : b.m = a.m ∘ σ) :
    alignedAll ps a = alignedAll ps b := by
  apply Bool.eq_iff_iff.mpr
  simp only [alignedAll_eq_true_iff]
  constructor
  · intro h p hp q hq
    have h1 : AlignedM p q a.m := aligned_eq_true_iff.mp (h p hp q hq)
    have h2 : AlignedM p q b.m := by rw [hm]; exact (alignedM_comp a.m σ).mpr h1
    exact aligned_eq_true_iff.mpr h2
  · intro h p hp q hq
    have h1 : AlignedM p q b.m := aligned_eq_true_iff.mp (h p hp q hq)
    rw [hm] at h1
    exact aligned_eq_true_iff.mpr ((alignedM_comp a.m σ).mp h1)

/-- The shipped check satisfies NU-055: `alignedAll` is the pairwise reading with self pairs
(`alignedAll_eq_true_iff`, `aligned_eq_true_iff`). -/
@[evidence holds NU_055]
theorem NU_055_reference : NU_055 refAlignCheck := by
  intro co β ps S _
  simp only [refAlignCheck, alignedAll_eq_true_iff, aligned_eq_true_iff]

/-! ### Consequences of the line -/

/-- The line fixes the check on every non-empty list: a check that meets NU-055 is the shipped
`alignedAll` there. -/
theorem NU_055_eq_ref {A : AlignCheck} (h : NU_055 A) {co : List PlaceId} {β : Type}
    {ps : List PlaceId} (hne : ps ≠ []) (S : NState co β) : A co β ps S = alignedAll ps S := by
  apply Bool.eq_iff_iff.mpr
  rw [h co β ps S hne, alignedAll_eq_true_iff]
  simp only [aligned_eq_true_iff]

/-- "The predicate compares names only for equality, so it is invariant under any permutation of
the name-symbols": a check that meets NU-055 gives the same answer on a class and on that class
with its name-symbols renamed by a permutation (AC5). -/
theorem NU_055_perm {A : AlignCheck} (h : NU_055 A) {co : List PlaceId} {β : Type}
    {ps : List PlaceId} (hne : ps ≠ []) (σ : Equiv.Perm ℕ) {a b : NState co β}
    (hm : b.m = a.m ∘ σ) : A co β ps a = A co β ps b := by
  rw [NU_055_eq_ref h hne, NU_055_eq_ref h hne]
  exact nu055_alignedAll_perm ps σ hm

/-- "It is therefore a function of the canonical key of a class": a check that meets NU-055
gives the same answer on two classes with the same key (`alignedAll_key_inv`). -/
theorem NU_055_key {A : AlignCheck} (h : NU_055 A) {co : List PlaceId} {β : Type}
    {ps : List PlaceId} (hne : ps ≠ []) {a b : NState co β} (hk : keyOf a = keyOf b) :
    A co β ps a = A co β ps b := by
  rw [NU_055_eq_ref h hne, NU_055_eq_ref h hne]
  exact alignedAll_key_inv ps hk

/-- "A place listed twice counts once" and "The order of `S` changes no verdict", on the
predicate: a check that meets NU-055 gives the same answer on two lists with the same members
(`alignedAll_congr_mem`; AC5, AC7). -/
theorem NU_055_members {A : AlignCheck} (h : NU_055 A) {co : List PlaceId} {β : Type}
    {ps ps' : List PlaceId} (hne : ps ≠ []) (hm : ∀ x, x ∈ ps ↔ x ∈ ps') (S : NState co β) :
    A co β ps S = A co β ps' S := by
  have hne' : ps' ≠ [] := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil ps hne
    exact List.ne_nil_of_mem ((hm x).mp hx)
  rw [NU_055_eq_ref h hne, NU_055_eq_ref h hne']
  exact alignedAll_congr_mem hm S

/-! ### Examples: classes over the coloured set `[0, 1]` -/

/-- Coloured set of the examples: places `0` and `1`. -/
def nu055_co : List PlaceId := [0, 1]

/-- Place `0` holds the name-symbol `0`, place `1` holds `0` too: aligned. -/
def nu055_same : NState nu055_co Unit :=
  ⟨(), fun s _ => if s = 0 then 1 else 0, 1, fun s hs _ => by simp; omega⟩

/-- Place `0` holds the name-symbols `0` and `1`, place `1` nothing: two names in one place. -/
def nu055_two : NState nu055_co Unit :=
  ⟨(), fun s i => if i.1 = 0 ∧ s ≤ 1 then 1 else 0, 2, fun s hs _ => by simp; omega⟩

/-- Place `0` holds the name-symbol `0`, place `1` holds `0` and `1`. -/
def nu055_mixed : NState nu055_co Unit :=
  ⟨(), fun s i => if (i.1 = 0 ∧ s = 0) ∨ (i.1 = 1 ∧ s ≤ 1) then 1 else 0, 2,
    fun s hs _ => by simp; omega⟩

/-- Place `0` holds the name-symbol `0`. -/
def nu055_zero : NState nu055_co Unit :=
  ⟨(), fun s i => if i.1 = 0 ∧ s = 0 then 1 else 0, 1, fun s hs _ => by simp; omega⟩

/-- Place `0` holds the name-symbol `1`: `nu055_zero` with `0` and `1` swapped. -/
def nu055_one : NState nu055_co Unit :=
  ⟨(), fun s i => if i.1 = 0 ∧ s = 1 then 1 else 0, 2, fun s hs _ => by simp; omega⟩

theorem nu055_one_perm : nu055_one.m = nu055_zero.m ∘ Equiv.swap 0 1 := by
  funext s i
  simp only [nu055_one, nu055_zero, Function.comp_apply]
  by_cases h0 : s = 0
  · subst h0; simp
  · by_cases h1 : s = 1
    · subst h1; simp
    · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]; simp [h0, h1]

theorem nu055_one_key : keyOf nu055_zero = keyOf nu055_one := by
  simp only [keyOf, nu055_one_perm, canonicalKey_comp]

/-! ### Violation: the cross pairs without the self pairs (AC7) -/

/-- A check that compares every two distinct places of `S` and never a place with itself. -/
def nu055_crossOnly : AlignCheck := fun _ _ ps S =>
  ps.all fun p => ps.all fun q => p == q || aligned p q S

/-- ✗ The cross pairs alone violate NU-055: on the singleton `[0]` the check accepts place `0`
holding the names `0` and `1`, which the line refuses (AC7: a place holding two names violates
the predicate whatever the others hold). -/
@[evidence forbids NU_055]
theorem NU_055_forbids_crossOnly : ¬ NU_055 nu055_crossOnly := by
  intro h
  have := NU_055_eq_ref h (ps := [0]) (by simp) nu055_two
  revert this
  decide

/-- Mutant reading of NU-055 without the self pairs: the check answers true exactly when any two
names resident in two different places of `S` are equal. -/
def NU_055_mutant_crossOnly (A : AlignCheck) : Prop :=
  ∀ (co : List PlaceId) (β : Type) (ps : List PlaceId) (S : NState co β), ps ≠ [] →
    (A co β ps S = true ↔
      ∀ p ∈ ps, ∀ q ∈ ps, p ≠ q → ∀ s t, resident co p S.m s = true →
        resident co q S.m t = true → s = t)

/-- The cross-pairs check kills the mutant reading without self pairs: it is that reading, so it
meets it, but NU-055, whose line includes the self pairs, rejects it on a place holding two names
(`NU_055_forbids_crossOnly`, AC7). -/
@[evidence mutant NU_055]
theorem NU_055_mutant_crossOnly_killed :
    NU_055_mutant_crossOnly nu055_crossOnly ∧ ¬ NU_055 nu055_crossOnly := by
  refine ⟨fun co β ps S _ => ?_, NU_055_forbids_crossOnly⟩
  simp only [nu055_crossOnly, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    aligned_eq_true_iff]
  constructor
  · intro h p hp q hq hne
    exact (h p hp q hq).resolve_left hne
  · intro h p hp q hq
    by_cases hpq : p = q
    · exact .inl hpq
    · exact .inr (h p hp q hq hpq)

/-! ### Violation: a check that reads the names -/

/-- A check that compares every resident name with the fixed name-symbol `0`. -/
def nu055_symZero : AlignCheck := fun _ _ ps S =>
  ps.all fun p => (List.range S.bound).all fun s => !resident _ p S.m s || s == 0

/-- ✗ Comparing names with a fixed name violates NU-055: place `0` holding the one name `1`
is aligned on `[0]`, and the check refuses it. The line kills it directly; the same model also
breaks the permutation and key consequences (`nu055_zero` is accepted, its swap `nu055_one`,
with the same key, is not). -/
@[evidence forbids NU_055]
theorem NU_055_forbids_symZero : ¬ NU_055 nu055_symZero := by
  intro h
  have := NU_055_eq_ref h (ps := [0]) (by simp) nu055_one
  revert this
  decide

/-! ### Violation: a check that reads only the first place -/

/-- A check that reads only the first place of `S`, with itself. -/
def nu055_headOnly : AlignCheck := fun _ _ ps S =>
  match ps with
  | [] => true
  | p :: _ => aligned p p S

/-- ✗ Reading only the first place violates NU-055: on `nu055_mixed` the check accepts `[0, 1]`
because place `0` holds one name, while place `1` holds two and the line refuses the list. The
line kills it directly; the same model also breaks the members consequence (`[1, 0]` is
refused). -/
@[evidence forbids NU_055]
theorem NU_055_forbids_headOnly : ¬ NU_055 nu055_headOnly := by
  intro h
  have := NU_055_eq_ref h (ps := [0, 1]) (by simp) nu055_mixed
  revert this
  decide

/-! ### The line exercised -/

/-- The line of NU-055 is exercised by the shipped check, on both sides of its `iff`: places `0`
and `1` holding the one name `0` are aligned, and so is the singleton `[0]` there (two places
and self pairs); place `0` holding two names is not aligned on `[0]` (a place holding two names)
nor on `[1, 0]` (whatever the others hold); place `1` empty imposes nothing on `[1]`. The
consequences show on the same examples: the class with the names swapped gives the same answer
(NU_055_perm, NU_055_key), and `[0, 1]` and `[1, 0, 1]` give the same answer on the mixed class
(NU_055_members). -/
@[evidence nonvacuous NU_055]
theorem NU_055_nonvacuous :
    refAlignCheck nu055_co Unit [0, 1] nu055_same = true ∧
      refAlignCheck nu055_co Unit [0] nu055_same = true ∧
      refAlignCheck nu055_co Unit [0] nu055_two = false ∧
      refAlignCheck nu055_co Unit [1, 0] nu055_two = false ∧
      refAlignCheck nu055_co Unit [1] nu055_two = true ∧
      refAlignCheck nu055_co Unit [0] nu055_zero = refAlignCheck nu055_co Unit [0] nu055_one ∧
      refAlignCheck nu055_co Unit [0, 1] nu055_mixed = false ∧
      refAlignCheck nu055_co Unit [1, 0, 1] nu055_mixed = false := by
  decide

/-! ## NU-055 (B): a Route B `Proven` holds for the reference executor -/

/-- A `QuiescentNameAligned` call: a name-alignment call and the reapable set (transition
names) its quiescence reads ([VER-002], [TIME-013]). -/
structure QAlignQuery extends AlignQuery where
  /-- The reapable transitions, by name. -/
  reap : String → Bool

/-- A decider of `QuiescentNameAligned(S)`: a verdict for each call. -/
abbrev QAlignDecider := QAlignQuery → RouteBVerdict

/-- The shipped decider of `QuiescentNameAligned(S)`: Route B's build on the untimed base
(no early stop: the early stop of [VER-012] AC5 is for reachability-safety properties), then its
verdict for the quiescence property "every resting class is name-aligned". Registered as a
witness model. -/
noncomputable def refQuiescentNameAligned : QAlignDecider := fun q =>
  Decide.verdict (routeB (co := q.co) untimedBase q.net q.role q.conflict)
    (Decide.build (routeB (co := q.co) untimedBase q.net q.role q.conflict) q.maxClasses
      (fun _ => false) (fun S => !alignedAll q.ps S) false q.fuel (initState q.co q.a0))
    (.quiescence (fun S => !alignedAll q.ps S) q.reap)

#spec_witness refQuiescentNameAligned

/-- A ν transition of the reference over the places, values and names Route B reads. -/
abbrev NuTransA := Spec.NuTrans PlaceId (KeyFn Colour ℕ)

/-- A queue marking of stamped tokens over those places and values. -/
abbrev QMarkA := Reference.QMarking PlaceId (Stamped Colour)

/-- One name-alignment call on a reference ν net: the transitions, the coloured set and the roles
the classifier gave, the class bound and the fuel of the build, the places `S` in the caller's
order and the initial queue marking. -/
structure AlignQueryR where
  /-- The transitions of the net. -/
  X : List NuTransA
  /-- The coloured set, in the classifier's order. -/
  co : List PlaceId
  /-- The role of each translated transition. -/
  role : Novel.RouteB.NuTrans → Role
  /-- The class bound. -/
  maxClasses : ℕ
  /-- The fuel of the Lean build. -/
  fuel : ℕ
  /-- The places `S`, in the caller's order. -/
  ps : List PlaceId
  /-- The initial marking. -/
  M0 : QMarkA

/-- The reapable set of a reference net, by transition name ([TIME-013], [VER-002]): the names
of its reapable transitions (as NU-050's `reapNames`). -/
def alignReapNames (X : List NuTransA) (s : String) : Bool :=
  X.any fun t => t.base.core.name == s && t.base.reapable

/-- The Route B call of a name-alignment call on a reference net: the translated net
(`NuLink.toNuTransB`), conflict priority off, the counts of the initial marking. -/
def AlignQueryR.call (q : AlignQueryR) : AlignQuery :=
  ⟨q.co, q.X.map Reference.NuLink.toNuTransB, q.role, false, q.maxClasses, q.fuel, q.ps,
    Reference.qCount q.M0⟩

/-- The Route B call of a `QuiescentNameAligned` call on a reference net: `AlignQueryR.call`
with the reapable set of the net. -/
def AlignQueryR.qcall (q : AlignQueryR) : QAlignQuery :=
  { toAlignQuery := q.call, reap := alignReapNames q.X }

requirement NU_055_sound
  id "NU-055"
  title "Name Alignment: soundness"
  kind B
  scope "every verifier that offers NameAligned or QuiescentNameAligned (MAY), judged against the reference ν executor, untimed and environment-free, with atomic firings"
  source verbatim "spec/12-nu-nets.md"
  covers NU_055.s1, NU_055.s4, NU_055.s41, NU_055.s42, NU_055.s43
  reading "For every call q (a net X of reference ν transitions, its coloured set co, its roles, the build limits, the places S and the initial marking M0) and every projection nameOf, where co lists each place once, every translated transition is in Route B's fragment for its role (InFragment), every transition has the shape B1 needs (B1Shape: distinct input places, correlated inputs taking a fixed count, correlated inputs coloured), every place of S is coloured, every coloured place is empty in M0, and at every marking a contract-keeping run reaches every key and relay projection of every transition gives each token of its place the name nameOf gives it (NuProj):"
          "if D answers Proven for NameAligned(S) on the Route B call of q, then in every marking M a contract-keeping reference run from M0 reaches, any two tokens in places of S, the same place allowed, carry the same name;"
          "if, in addition, every join key consumes at least one token (PosKeys), and Dq answers Proven for QuiescentNameAligned(S) on the Route B call of q with the reapable set of q (the names of its reapable transitions), then the same holds in every marking M a contract-keeping reference run from M0 reaches and at which every ν-enabled transition is reapable (NuRests)."
  assumes "The executor is the reference ν firing RefNuFire (Reference/Nu.lean), untimed and environment-free, one atomic firing per step: a run is NuLink.RefNuRunB, a sequence of firings of transitions of X each of whose actions keeps the contract of the role Route B gives its transition (NuLink.NuContract): a declared mint writes one name no coloured place holds into every coloured place it writes (NU-010, ruling D78 (a), NuLink.nuContract_mint_iff), a coloured consumer writes only a name it received from a coloured input (NU-051, NU-054). This is design correction S7 (a): the lines are stated over the reference executor, as NU_050_soundB's are. The 'untimed, environment-free executor with atomic firings' of the Soundness paragraph is this run; Novel's NuStepC (Sim.lean), where a coloured consumer takes any resident name (ruling D16 is why that differs from EXEC-010's FIFO), is the graph's semantics the holds proof passes through, not the executor of the lines. A firing whose action breaks its contract is not a step of the run; the spec makes no claim about it."
          "The premises are hypotheses (design correction S6), one per premise bullet of the Soundness paragraph: 'the coloured places start empty' (every place of co empty in M0); 'the mints and coloured consumers keep their contracts' (the run, above); 'the projection contract of [NU-050]' (NuProj at every marking a contract-keeping run reaches, one projection nameOf for every key and relay); 'every firing writes one token to each output place its branch names' (built into RefNuFire, IO-016 AC4); 'every place of S coloured' (ps ⊆ co; in the shipped verifier the refusal order enforces it, and the empty start with it: NU_055_refusal_build_premises); 'the conditions the classifier establishes (InFragment)', over the translated net; 'unguarded inputs', which needs no hypothesis since IO-006 removed guards and every translated input is unguarded (NuLink.guardFree_toNuTransB); and, for the quiescent form, PosKeys. B1Shape is the shape the bridge needs, which every transition that builds and that the classifier accepts as a join meets (CORE-030 AC3; Route B accepts only One and Exactly keys), as in NU_050_soundB."
          "q.co.Nodup is not a spec premise and gets no premise bullet: it says the list the call holds is a set, as the spec's coloured set is and as the classifier's coloured order (Rust coloured_order, the co of the Lean theorems) lists each place once. It does not narrow the claim about a call the shipped pipeline makes. The Route B call's initial counts are those of M0 (AlignQueryR.call), the marking the runs start from."
          "Conflict-only priority (NU-052) is off in the Route B call (AlignQueryR.call sets the conflict flag false), as in NU_050_soundB: the priority pass is the executor's (RefExec), not one firing's, so a reference run takes no priority and the translated net is explored with conflict false. The Soundness paragraph's 'Conflict-only priority ([NU-052]) applies as it does to every Route B property' is not a line here: a Proven under conflict priority is sound for Novel's NuStepC with the same prune (routeB_untimed_nameAligned_sound and routeB_untimed_quiescentNameAligned_sound take the conflict flag, cited), and its tie to RefExec's priority pass is NU-052's, as for every Route B property."
          "The lines ask soundness for every coloured set and role assignment that meets InFragment, not only for the classifier's. That is the premise bullet as written ('the conditions the classifier establishes (InFragment)', a condition, not the classifier), and Route B alone takes co and role as inputs; the classifier's own output meets InFragment (classifyS_inFragment, Novel/RouteB/Classify.lean, NU-051). That the coloured set is the one the classifier computes for the call, not one the caller names, is the pipeline's and no block states it; how the set is computed is Q-tested (NU_051_colours' assumes)."
          "The lines are soundness only: a decider that never answers Proven meets them. Ruling D59 (a) reads VER-012's 'exact (sound and complete)' (clash ver-d#1) as sound against the executor and complete for the free-choice name semantics of the graph: soundness is this block; completeness against the graph is NU_055_truncation line 3 (a closed graph none of whose classes violates answers Proven) and VER-012's block. The holds proof is bridge B1 on contract-keeping runs (NuLink.refNuRunB_names_reach: every contract-keeping reference run is a NuStepC run of the translated net with conflict off) composed with routeB_untimed_nameAligned_sound and routeB_untimed_quiescentNameAligned_sound; for the quiescent form a reference rest is an executor rest of the translated net (nu055_execRests_of_nuRests), resting read with the names of the reapable transitions."
          "The deciders are AlignDecider (glossary GlossaryNuVer.lean, witness refNameAligned) and QAlignDecider (here, witness refQuiescentNameAligned), asked on the Route B call of q (AlignQueryR.call; AlignQueryR.qcall adds the reapable set): Route B alone, from the initial class, with no refusal step and no routing. The quiescent line reads resting with the call's reapable set, the names of the reapable transitions of X, as the reap-aware quiescence of VER-002 does on the graph and NuRests does on the reference marking. Every refusal of the refusal order (steps 1 to 7: cancellation and budget, an absent place, Bounded(k) outside its premises, in-flight state, the fragment declines of EXTENDED and BASE, an arrival into a coloured place, a modelled environment place, an uncoloured place of S, a marked coloured place) and the 'Coloured places only' and 'Modelled injection' rules are the block NU_055_refusal (NU_055_steps.lean), worded under ruling D20 (clashes nu-c#7, nu-c#9, NC-7, NC-8)."
          "Three rules of the section are dispatch and classifier rules of the verifier pipeline, not lines of any NU-055 block: 'Route B only' (no other route decides, no NU-053 fallback, no script); the rule that sends these properties to Route B before a budget place; and 'an implementation MUST lift both gates for the name-alignment properties, and only for them', the classifier's no-fragment for a net without a matched transition (Rust classify, whose matchless flag is set from property.is_name_alignment()) and the dispatcher's flat-phase routing of such a net (the name_alignment trigger of verify_net). NU_053_dispatch models the routing: its routeB guard enters Route B on a name-alignment call whatever the join and budget flags, and on any other call only with a ν-join. The classifier gate is lifted here by construction: the lines take every co and role that meet InFragment, a net without a matched transition included (the nonvacuous example is one)."
          "Not covered, as the spec itself says: the timed name × time graph the shipped Route B builds (gap R6 of Novel/RouteB/Sound.lean), the all-immediate worked example included; markings with actions in flight (the reference run has none); faithfulness of a carrier's name to what its token is about, which rests on the unchecked contracts of NU-051."
          "AC1 (the worked example under EXTENDED: QuiescentNameAligned(box, list) and QuiescentCount Proven, NameAligned(box, list) Violated in 8 firings, the buggy variant Violated in 12, each attributed to Route B) is a fixture test (Q): the graph of that net is not computed in Lean. Its Proven verdicts are the kind lines 1 and 2 make sound; its Violated verdicts and witness lengths are graph facts."
          "AC2 (an uncoloured or absent place gives Unknown naming it, the first in S) and AC6 (an environment place under AlwaysAvailable gives Unknown naming it, a marked coloured place gives Unknown naming it) and AC8 (the refusal order on the worked example) are lines 1, 5, 6 and 7 of NU_055_refusal. AC3 (under BASE the net is outside the fragment, the reason names EXTENDED and the report names the ignored relay declarations) is its line 2; the report note naming the ignored relay declarations is NU-054's (AC5). AC4 (no other route decides; the script encoders return none) is the pipeline's 'Route B only' rule, not encoded; its last clause (a truncation stays Unknown unless the prefix rule finds a violation) is NU_055_truncation lines 2 and 5."
  signoff "2026-11-13 d20b41b4b40c0e65 ai"
  statement : AlignDecider → QAlignDecider → Prop :=
    fun D Dq =>
      (∀ (q : AlignQueryR) (nameOf : Colour → ℕ),
        q.co.Nodup → (∀ T ∈ q.X.map Reference.NuLink.toNuTransB, InFragment q.co T (q.role T)) →
        (∀ t ∈ q.X, Reference.NuLink.B1Shape q.co t) → (∀ p ∈ q.ps, p ∈ q.co) →
        (∀ p ∈ q.co, q.M0 p = []) →
        (∀ M, Reference.NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M →
          ∀ t ∈ q.X, Reference.NuLink.NuProj nameOf t M) →
        D q.call = .proven →
        ∀ M, Reference.NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M →
          ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ M p, ∀ d ∈ M p', nameOf c.val = nameOf d.val) ∧
      (∀ (q : AlignQueryR) (nameOf : Colour → ℕ),
        q.co.Nodup → (∀ T ∈ q.X.map Reference.NuLink.toNuTransB, InFragment q.co T (q.role T)) →
        (∀ T ∈ q.X.map Reference.NuLink.toNuTransB, PosKeys (q.role T)) →
        (∀ t ∈ q.X, Reference.NuLink.B1Shape q.co t) → (∀ p ∈ q.ps, p ∈ q.co) →
        (∀ p ∈ q.co, q.M0 p = []) →
        (∀ M, Reference.NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M →
          ∀ t ∈ q.X, Reference.NuLink.NuProj nameOf t M) →
        Dq q.qcall = .proven →
        ∀ M, Reference.NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M → Reference.NuRests q.X M →
          ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ M p, ∀ d ∈ M p', nameOf c.val = nameOf d.val)

/- The pinned readable form of NU_055_sound: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_055_sound : AlignDecider → QAlignDecider → Prop :=
fun D Dq =>
  (∀ (q : AlignQueryR) (nameOf : Colour → ℕ),
      q.co.Nodup →
        (∀ T ∈ List.map Reference.NuLink.toNuTransB q.X, InFragment q.co T (q.role T)) →
          (∀ t ∈ q.X, Reference.NuLink.B1Shape q.co t) →
            (∀ p ∈ q.ps, p ∈ q.co) →
              (∀ p ∈ q.co, q.M0 p = []) →
                (∀ (M : Reference.QMarking PlaceId (Stamped Colour)),
                    Reference.NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M →
                      ∀ t ∈ q.X, Reference.NuLink.NuProj nameOf t M) →
                  D q.call = Decide.Verdict.proven →
                    ∀ (M : Reference.QMarking PlaceId (Stamped Colour)),
                      Reference.NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M →
                        ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ M p, ∀ d ∈ M p', nameOf c.val = nameOf d.val) ∧
    ∀ (q : AlignQueryR) (nameOf : Colour → ℕ),
      q.co.Nodup →
        (∀ T ∈ List.map Reference.NuLink.toNuTransB q.X, InFragment q.co T (q.role T)) →
          (∀ T ∈ List.map Reference.NuLink.toNuTransB q.X, PosKeys (q.role T)) →
            (∀ t ∈ q.X, Reference.NuLink.B1Shape q.co t) →
              (∀ p ∈ q.ps, p ∈ q.co) →
                (∀ p ∈ q.co, q.M0 p = []) →
                  (∀ (M : Reference.QMarking PlaceId (Stamped Colour)),
                      Reference.NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M →
                        ∀ t ∈ q.X, Reference.NuLink.NuProj nameOf t M) →
                    Dq q.qcall = Decide.Verdict.proven →
                      ∀ (M : Reference.QMarking PlaceId (Stamped Colour)),
                        Reference.NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M →
                          Reference.NuRests q.X M →
                            ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ M p, ∀ d ∈ M p', nameOf c.val = nameOf d.val
-/
#guard_msgs in #print NU_055_sound

/-! ### The reference -/

open Libpetri.Reference in
/-- A name Route B's executor accepts for a translated matched transition is eligible for the
reference selection (as NU-050's `nu050_eligible_of_selectable`). -/
theorem nu055_eligible_of_selectable {co : List PlaceId} {nameOf : Colour → ℕ} {t : NuTransA}
    {ms : MatchSpec PlaceId (KeyFn Colour ℕ)} {M : QMarkA} {n : ℕ} (hm : t.mspec = some ms)
    (hsh : NuLink.B1Shape co t) (hproj : NuLink.NuProj nameOf t M)
    (hsel : Novel.RouteB.Selectable co (NuLink.toNuTransB t)
      (Novel.RouteB.nameLayer co nameOf (NuLink.vals M)) n) :
    eligible (matchIn ms t M) n = true := by
  have hmo : NuLink.msOf t = ms := by simp [NuLink.msOf, hm]
  obtain ⟨hne, hall⟩ := hsel ms.keyPlaces (by simp [NuLink.toNuTransB, hm])
  unfold eligible matchIn
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq,
    List.isEmpty_eq_false_iff, List.mem_map]
  refine ⟨fun he => hne (by simpa [MatchSpec.keyPlaces] using he), ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have hp : k.1 ∈ ms.keyPlaces := List.mem_map.2 ⟨k, hk, rfl⟩
  have hcol := hsh.keysColoured k.1 (by rw [hmo]; exact hp)
  have hpr := hproj k (by rw [hmo]; exact List.mem_append_left _ hk)
  obtain ⟨h1, h2⟩ := hall k.1 hp
  rw [NuLink.cnt_vals_mem hcol, ← NuLink.named_length_eq_count hpr] at h1 h2
  rw [NuLink.keyReq_toNuTransB] at h2
  simp only [NuLink.stamps_length]
  exact ⟨h1, h2⟩

open Libpetri.Reference in
/-- **A reference rest is an executor rest of the translated net** (as NU-050's
`nu050_execRests_of_nuRests`): where every ν-enabled transition of `X` is reapable, every
transition Route B's executor model can fire is reapable by name. -/
theorem nu055_execRests_of_nuRests {co : List PlaceId} {nameOf : Colour → ℕ}
    {X : List NuTransA} {M : QMarkA} (hsh : ∀ t ∈ X, NuLink.B1Shape co t)
    (hproj : ∀ t ∈ X, NuLink.NuProj nameOf t M) (h : NuRests X M) :
    Novel.RouteB.ExecRests (co := co) (nameOf := nameOf) (net := X.map NuLink.toNuTransB)
      (alignReapNames X) (NuLink.vals M) := by
  intro T hT hen
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT
  have hnu : NuEnabled t M := by
    refine ⟨?_, fun ms hm => ?_⟩
    · have h1 := hen.1
      show Enabled t.base (qCount M)
      unfold Enabled
      rw [NuLink.qCount_eq_alpha, ← Link.enabledC_toTransition]
      exact h1
    · obtain ⟨n, hn⟩ := hen.2 ms.keyPlaces (by simp [NuLink.toNuTransB, hm])
      exact ⟨n, nu055_eligible_of_selectable hm (hsh t ht) (hproj t ht) hn⟩
  have hr := h t ht hnu
  show alignReapNames X t.base.core.name = true
  exact List.any_eq_true.2 ⟨t, ht, by simp [hr]⟩

/-- The tokens of a place, read without stamps, are the values of the place. -/
theorem nu055_val_mem_vals {M : QMarkA} {p : PlaceId} {c : Stamped Colour} (hc : c ∈ M p) :
    c.val ∈ Reference.NuLink.vals M p :=
  List.mem_map_of_mem hc

/-- The coloured places of `M0`, read without stamps, are empty. -/
theorem nu055_vals_empty {co : List PlaceId} {M0 : QMarkA} (hempty : ∀ p ∈ co, M0 p = []) :
    ∀ i : Fin co.length, Reference.NuLink.vals M0 co[i.1] = [] := by
  intro i
  simp [Reference.NuLink.vals, hempty _ (List.getElem_mem i.2)]

/-- The shipped deciders satisfy NU-055's soundness lines: B1 makes every contract-keeping
reference run a run of Route B's executor model on the translated net
(`NuLink.refNuRunB_names_reach`), and `routeB_untimed_nameAligned_sound` and
`routeB_untimed_quiescentNameAligned_sound` carry a `Proven` to every marking that run reaches
(and, for the quiescent form, rests at). -/
@[evidence holds NU_055_sound]
theorem NU_055_sound_reference : NU_055_sound refNameAligned refQuiescentNameAligned := by
  refine ⟨fun q nameOf hco hfr hsh hps hempty hproj hP M hM => ?_,
    fun q nameOf hco hfr hpos hsh hps hempty hproj hP M hM hrest => ?_⟩
  · have hR := Reference.NuLink.refNuRunB_names_reach hsh hproj hM
    simp only [refNameAligned, AlignQueryR.call, Reference.NuLink.qCount_eq_alpha] at hP
    have h := routeB_untimed_nameAligned_sound hco hfr
      (Reference.NuLink.guardFree_toNuTransB q.X) hps (nu055_vals_empty hempty) hP hR
    intro p hp p' hp' c hc d hd
    exact h p hp p' hp' _ (nu055_val_mem_vals hc) _ (nu055_val_mem_vals hd)
  · have hR := Reference.NuLink.refNuRunB_names_reach hsh hproj hM
    simp only [refQuiescentNameAligned, AlignQueryR.qcall, AlignQueryR.call,
      Reference.NuLink.qCount_eq_alpha] at hP
    have h := routeB_untimed_quiescentNameAligned_sound hco hfr hpos
      (Reference.NuLink.guardFree_toNuTransB q.X) hps (nu055_vals_empty hempty) hP hR
      (nu055_execRests_of_nuRests hsh (hproj M hM) hrest)
    intro p hp p' hp' c hc d hd
    exact h p hp p' hp' _ (nu055_val_mem_vals hc) _ (nu055_val_mem_vals hd)

/-! ### Examples: a mint drawing on a budget of two -/

open Libpetri.Reference in
/-- One coloured place `0`; a mint that takes one token from the budget place `1` and writes one
token to place `0`; no match, not reapable. -/
def nu055_tR : NuTransA where
  base :=
    { core := { name := "mint", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] }
      out := some (.place 0) }
  mspec := none

open Libpetri.Reference in
/-- The initial marking: two budget tokens in place `1`, nothing else. -/
def nu055_M0 : QMarkA := fun p => if p = 1 then [⟨7, 0⟩, ⟨8, 1⟩] else []

open Libpetri.Reference in
/-- The marking after the first mint, which writes the name `10`. -/
def nu055_M1 : QMarkA := qFire nu055_M0 nu055_tR.base [(0, ⟨10, 2⟩)]

open Libpetri.Reference in
/-- The marking after the second mint, which writes the name `11`. -/
def nu055_M2 : QMarkA := qFire nu055_M1 nu055_tR.base [(0, ⟨11, 3⟩)]

open Libpetri.Reference in
/-- The run of the example: each mint keeps Route B's mint contract, writing a name no coloured
place holds. -/
theorem nu055_runB2 :
    NuLink.RefNuRunB [0] id (fun _ => .mint) [nu055_tR] nu055_M0 nu055_M2 := by
  have f1 : RefNuFire nu055_tR nu055_M0 none (qDelivered nu055_M0 nu055_tR.base)
      [(0, ⟨10, 2⟩)] nu055_M1 :=
    (refNuFire_restrictsTo nu055_tR rfl _ _ _ _ _).2 ⟨rfl, by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  have f2 : RefNuFire nu055_tR nu055_M1 none (qDelivered nu055_M1 nu055_tR.base)
      [(0, ⟨11, 3⟩)] nu055_M2 :=
    (refNuFire_restrictsTo nu055_tR rfl _ _ _ _ _).2 ⟨rfl, by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩
  exact (Relation.ReflTransGen.single ⟨nu055_tR, List.mem_singleton_self _, none, _, _, f1,
    ⟨10, by decide, by decide⟩⟩).tail
    ⟨nu055_tR, List.mem_singleton_self _, none, _, _, f2, ⟨11, by decide, by decide⟩⟩

/-- After the two mints place `0` holds the names `10` and `11`. -/
theorem nu055_M2_zero : nu055_M2 0 = [⟨10, 2⟩, ⟨11, 3⟩] := by decide

open Libpetri.Reference in
/-- After the two mints the budget is spent and the mint is not ν-enabled: the net rests. -/
theorem nu055_M2_rests : NuRests [nu055_tR] nu055_M2 := by
  intro t ht hen
  simp only [List.mem_singleton] at ht
  subst ht
  have := hen.1
  revert this
  decide

/-- The call `NameAligned([0])` (and `QuiescentNameAligned([0])`) on the mint net, a class bound
of one class. -/
def nu055_qR : AlignQueryR := ⟨[nu055_tR], [0], fun _ => .mint, 1, 3, [0], nu055_M0⟩

theorem nu055_qR_fragment :
    ∀ T ∈ nu055_qR.X.map Reference.NuLink.toNuTransB, InFragment nu055_qR.co T (nu055_qR.role T) := by
  intro T hT
  simp only [nu055_qR, List.map_cons, List.map_nil, List.mem_singleton] at hT
  subst hT
  refine ⟨⟨?_, ?_, ?_⟩, rfl, ?_⟩ <;>
    simp [Reference.NuLink.toNuTransB, Reference.NuLink.outRows, nu055_tR,
      Reference.Link.toTransition, Reference.Link.toInSpec, Reference.Out.branches, Reference.Out.findTimeout, idx]
  decide

theorem nu055_qR_shape : ∀ t ∈ nu055_qR.X, Reference.NuLink.B1Shape nu055_qR.co t := by
  intro t ht
  simp only [nu055_qR, List.mem_singleton] at ht
  subst ht
  exact ⟨by decide, by simp [Reference.NuLink.msOf, nu055_tR, MatchSpec.keyPlaces],
    by simp [Reference.NuLink.msOf, nu055_tR, MatchSpec.keyPlaces]⟩

theorem nu055_qR_proj (nameOf : Colour → ℕ) :
    ∀ M, Reference.NuLink.RefNuRunB nu055_qR.co nameOf nu055_qR.role nu055_qR.X nu055_qR.M0 M →
      ∀ t ∈ nu055_qR.X, Reference.NuLink.NuProj nameOf t M := by
  intro M _ t ht k hk
  simp only [nu055_qR, List.mem_singleton] at ht
  subst ht
  simp [Reference.NuLink.msOf, nu055_tR] at hk

theorem nu055_qR_empty : ∀ p ∈ nu055_qR.co, nu055_qR.M0 p = [] := by decide

theorem nu055_qR_ps : ∀ p ∈ nu055_qR.ps, p ∈ nu055_qR.co := by decide

theorem nu055_qR_posKeys :
    ∀ T ∈ nu055_qR.X.map Reference.NuLink.toNuTransB, PosKeys (nu055_qR.role T) := by
  intro T _ cin rel hr
  cases hr

/-! ### Violations: deciders that always answer `Proven` -/

/-- A decider of `NameAligned(S)` that always answers `Proven`. -/
def nu055_alwaysProven : AlignDecider := fun _ => .proven

/-- A decider of `QuiescentNameAligned(S)` that always answers `Proven`. -/
def nu055_qAlwaysProven : QAlignDecider := fun _ => .proven

/-- ✗ A decider that always proves violates NU-055's soundness (line 1): two contract-keeping
mints put the names `10` and `11` in place `0`. -/
@[evidence forbids NU_055_sound]
theorem NU_055_sound_forbids_alwaysProven :
    ¬ NU_055_sound nu055_alwaysProven refQuiescentNameAligned := by
  intro h
  have := h.1 nu055_qR id (by decide) nu055_qR_fragment nu055_qR_shape nu055_qR_ps
    nu055_qR_empty (nu055_qR_proj id) rfl nu055_M2 nu055_runB2 0 (by decide) 0 (by decide)
    ⟨10, 2⟩ (by rw [nu055_M2_zero]; simp) ⟨11, 3⟩ (by rw [nu055_M2_zero]; simp)
  simp at this

/-- ✗ A quiescent decider that always proves violates NU-055's soundness (line 2): after the two
mints the budget is spent, the net rests, and place `0` holds the names `10` and `11`. -/
@[evidence forbids NU_055_sound]
theorem NU_055_sound_forbids_qAlwaysProven :
    ¬ NU_055_sound refNameAligned nu055_qAlwaysProven := by
  intro h
  have := h.2 nu055_qR id (by decide) nu055_qR_fragment nu055_qR_posKeys nu055_qR_shape
    nu055_qR_ps nu055_qR_empty (nu055_qR_proj id) rfl nu055_M2 nu055_runB2 nu055_M2_rests 0
    (by decide) 0 (by decide) ⟨10, 2⟩ (by rw [nu055_M2_zero]; simp) ⟨11, 3⟩
    (by rw [nu055_M2_zero]; simp)
  simp at this

/-! ### Mutant: alignment at the initial marking only -/

/-- Mutant reading of NU-055's soundness that reads "in every reachable marking" as "in the
initial marking": under the same premises, a `Proven` says only that the tokens in the places of
`S` carry one name in the initial marking. -/
def NU_055_sound_mutant_initialOnly (D : AlignDecider) (Dq : QAlignDecider) : Prop :=
  (∀ (q : AlignQueryR) (nameOf : Colour → ℕ),
    q.co.Nodup → (∀ T ∈ q.X.map Reference.NuLink.toNuTransB, InFragment q.co T (q.role T)) →
    (∀ t ∈ q.X, Reference.NuLink.B1Shape q.co t) → (∀ p ∈ q.ps, p ∈ q.co) →
    (∀ p ∈ q.co, q.M0 p = []) →
    (∀ M, Reference.NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M →
      ∀ t ∈ q.X, Reference.NuLink.NuProj nameOf t M) →
    D q.call = .proven →
    ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ q.M0 p, ∀ d ∈ q.M0 p', nameOf c.val = nameOf d.val) ∧
  (∀ (q : AlignQueryR) (nameOf : Colour → ℕ),
    q.co.Nodup → (∀ T ∈ q.X.map Reference.NuLink.toNuTransB, InFragment q.co T (q.role T)) →
    (∀ T ∈ q.X.map Reference.NuLink.toNuTransB, PosKeys (q.role T)) →
    (∀ t ∈ q.X, Reference.NuLink.B1Shape q.co t) → (∀ p ∈ q.ps, p ∈ q.co) →
    (∀ p ∈ q.co, q.M0 p = []) →
    (∀ M, Reference.NuLink.RefNuRunB q.co nameOf q.role q.X q.M0 M →
      ∀ t ∈ q.X, Reference.NuLink.NuProj nameOf t M) →
    Dq q.qcall = .proven → Reference.NuRests q.X q.M0 →
    ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ q.M0 p, ∀ d ∈ q.M0 p', nameOf c.val = nameOf d.val)

/-- The decider that always proves kills the initial-only mutant: the premises put no token in a
place of `S` at the start, so it meets the mutant reading, but the two mints reach two names in
place `0`, which NU-055's soundness rejects (`NU_055_sound_forbids_alwaysProven`). -/
@[evidence mutant NU_055_sound]
theorem NU_055_sound_mutant_initialOnly_killed :
    NU_055_sound_mutant_initialOnly nu055_alwaysProven refQuiescentNameAligned ∧
      ¬ NU_055_sound nu055_alwaysProven refQuiescentNameAligned := by
  refine ⟨⟨fun q _ _ _ _ hps hempty _ _ p hp _ _ c hc _ _ => ?_,
      fun q _ _ _ _ _ hps hempty _ _ _ p hp _ _ c hc _ _ => ?_⟩,
    NU_055_sound_forbids_alwaysProven⟩
  · rw [hempty p (hps p hp)] at hc
    exact absurd hc List.not_mem_nil
  · rw [hempty p (hps p hp)] at hc
    exact absurd hc List.not_mem_nil

/-! ### Every line exercised -/

/-- The call `NameAligned([0])` on the net with no transition, place `0` empty, a class bound of
two classes. -/
def nu055_qREmpty : AlignQueryR := ⟨[], [0], fun _ => .ordinary, 2, 2, [0], fun _ => []⟩

/-- Both lines of NU-055's soundness are exercised by the shipped deciders. Both answer `Proven`
on the net with no transition (a closed graph of one aligned class), so the antecedents of
lines 1 and 2 are met; on the mint net, where a contract-keeping run reaches place `0` holding two
names, neither answers `Proven`, which lines 1 and 2 force (NU_055_sound_reference with
nu055_runB2). -/
@[evidence nonvacuous NU_055_sound]
theorem NU_055_sound_nonvacuous :
    refNameAligned nu055_qREmpty.call = .proven ∧
      refQuiescentNameAligned nu055_qREmpty.qcall = .proven ∧
      refNameAligned nu055_qR.call ≠ .proven ∧ refQuiescentNameAligned nu055_qR.qcall ≠ .proven := by
  refine ⟨by decide, by decide, fun hP => ?_, fun hP => ?_⟩
  · have := NU_055_sound_reference.1 nu055_qR id (by decide) nu055_qR_fragment nu055_qR_shape
      nu055_qR_ps nu055_qR_empty (nu055_qR_proj id) hP nu055_M2 nu055_runB2 0 (by decide) 0
      (by decide) ⟨10, 2⟩ (by rw [nu055_M2_zero]; simp) ⟨11, 3⟩ (by rw [nu055_M2_zero]; simp)
    simp at this
  · have := NU_055_sound_reference.2 nu055_qR id (by decide) nu055_qR_fragment nu055_qR_posKeys
      nu055_qR_shape nu055_qR_ps nu055_qR_empty (nu055_qR_proj id) hP nu055_M2 nu055_runB2
      nu055_M2_rests 0 (by decide) 0 (by decide) ⟨10, 2⟩ (by rw [nu055_M2_zero]; simp) ⟨11, 3⟩
      (by rw [nu055_M2_zero]; simp)
    simp at this

/-! ## NU-055 (F): the verdict on a built graph -/

/-- A verdict function on a built graph: from the explorer, the build's outcome (stored classes,
expanded count, whether it closed or stopped) and the property, the verdict. -/
abbrev ClassVerdict :=
  (S K L : Type) → Explorer S K L → Decide.Out S → Decide.Prop' S L → RouteBVerdict

/-- The shipped verdict function (`Decide.verdict`, Rust `verify_via_name_scg` over
`decide_over_classes`), registered as a witness model. -/
def refClassVerdict : ClassVerdict := fun _ _ _ E o p => Decide.verdict E o p

#spec_witness refClassVerdict

/-- The two name-alignment properties over the list `ps`: `NameAligned(ps)` as a safety
property, `QuiescentNameAligned(ps)` as a quiescence property over some reapable set. -/
def AlignProp {co : List PlaceId} {β L : Type} (ps : List PlaceId)
    (p : Decide.Prop' (NState co β) L) : Prop :=
  p = .safety (fun S => !alignedAll ps S) ∨ ∃ reap, p = .quiescence (fun S => !alignedAll ps S) reap

requirement NU_055_truncation
  id "NU-055"
  title "Name Alignment: the verdict on a built graph"
  kind F
  scope "every verifier that offers NameAligned or QuiescentNameAligned (MAY); the verdict Route B reads off a built graph"
  source verbatim "spec/12-nu-nets.md"
  covers NU_055.s7, NU_055.s8, NU_055.s36, NU_055.s38, NU_055.s39, NU_055.s40, NU_055.s37
  reading "For every explorer E over classes, every build outcome o, every non-empty list ps and every property p that is NameAligned(ps) or QuiescentNameAligned(ps) over some reapable set, where a class violates p as Decide.violatesAt reads it (for NameAligned a stored class that is not aligned, for QuiescentNameAligned an expanded class at which the net rests and that is not aligned):"
          "if V answers Proven, the graph closed (o.complete);"
          "if the graph did not close and no class violates p, V answers Unknown;"
          "if the graph closed and the build was not stopped, V answers Proven exactly when no class violates p;"
          "if V answers Violated at the class index i, class i violates p;"
          "if the graph did not close and the build was not stopped (it reached the class bound, or, for NameAligned, it ended at the early stop of VER-012 AC5, at its first violating class), and some class violates p, V answers Violated."
  assumes "The model is a verdict function on a built graph (Decide.Out: the stored classes in discovery order, the number expanded, whether the build closed and whether it stopped) and a property (Decide.Prop'), restricted to the two name-alignment properties (AlignProp) on a non-empty S, the only S that reaches a verdict (NU_055's assumes). How the build stores and expands classes is Decide.build's, cited by NU_055_sound through the soundness theorems; it is not a line here."
          "'Does not close' is o.complete = false: in the shipped build that is the class bound reached, the early stop (for NameAligned, a build that stops at its first violating class, VER-012 AC5), the total budget or a cancellation (cut). In the Lean model the fuel running out is a stopped build, as a cut is (Decide.loop with fuel 0 gives stopped = true). The quoted Truncation sentence names the class bound only; its EARS restatement names the budget and the cancellation as well, as VER-013 does for every route and refusal step 1 does for a call cancelled or out of budget before it starts. Lines 1 and 2 hold for each cause."
          "Line 3 is 'deciding it on the name-permutation quotient decides it on the graph', read on the verdict, and its EARS restatement: on a closed graph, Proven exactly when no class violates the property. Under ruling D59 (a) (clash ver-d#1, VD-1 (a)), 'exact (sound and complete)' is sound against the executor (NU_055_sound) and complete for the free-choice name semantics of the graph, which is this line: a closed graph with no violating class answers Proven. Line 3 says that a closed graph with a violating class does not answer Proven; that it answers Violated is the prefix rule on a graph that was not stopped (NU_050_prefix line 2, on the same ClassVerdict), which line 5 states for a graph that did not close. Its premise o.stopped = false rules out only an outcome the build never makes (Decide.loop: a closed build is never stopped)."
          "Line 4 is the EARS restatement of the Violated paragraph's 'to a violating class': the class a Violated names violates the property, for NameAligned a stored class and for QuiescentNameAligned an expanded resting class. The paragraph's first sentence is not quoted, because the line encodes only its 'to a violating class': the rest of it (the shortest path, the attribution to Route B, counterexampleConfirmed absent, counterexampleTiming) is VER-003's and VER-012's report shape under ruling D40 (a) (clash ver-a#11): a trace carries a guarantee against the executor only when counterexampleConfirmed is true, and Route B leaves it absent, so a Violated is sound for the graph only; the report fields are kind N and the trace on the fixtures kind Q. The line does not model the counterexample path: it reads 'the class its counterexample ends at' as the class index the Violated verdict carries (Decide.verdict), the class the reported shortest path ends at; that identification is assumed here, not stated, and the path's shape is VER-003's under D40 (a). For QuiescentNameAligned the line is stronger than the sentence's 'violate the property': the class is an expanded one at which the net rests, as the prefix rule of the Truncation paragraph reads it. The line has no closure premise, so it holds on a truncated graph too, matching the prefix rule's 'violated by a stored class' and 'violated by an expanded class at which the net rests'."
          "Line 5 is the prefix rule of the Truncation paragraph under ruling D59 (a) (clash nu-b#1): a graph that did not close answers Violated when a stored class violates NameAligned, or an expanded class at which the net rests violates QuiescentNameAligned, as Rust, Java and TypeScript do (nu_scg_verifier.rs, NuScgVerifier.java, nu-scg-verifier.ts; NU_050_prefix line 2 states it for every property on the same ClassVerdict). 'Does not close within the class bound' is o.complete = false with o.stopped = false: a build that reached the class bound, or one that ended at the early stop (for NameAligned, a build that stops at its first violating class, VER-012 AC5), which holds a violating class, so Violated is the right answer there. A build stopped by the total budget or a cancellation answers Unknown whatever its prefix holds (VER-013, NU_050_prefix line 1), and the Lean fuel running out is such a stopped build, so line 5 reads o.stopped = false. Its 'otherwise the verdict is Unknown' is line 2. The verdict that answers Unknown on every graph that did not close (D59 (b)) meets lines 1 to 4 and is killed by line 5 (NU_055_truncation_forbids_unknownWhenCut, NU_055_truncation_mutant_noPrefix_killed). The 'shortest witness in the explored graph' and the 'report line naming the truncation' are the report shape (VER-003, kind N) and the witness lengths on the fixtures are Q; line 5 asks only for a Violated, whose class line 4 fixes."
          "AC4's last clause ('a Route B truncation stays Unknown unless the prefix rule finds a violation') is lines 1, 2 and 5; the rest of AC4 is accounted for in NU_055_sound's assumes."
  signoff "2026-11-13 3bc70272dbf00c2f ai"
  statement : ClassVerdict → Prop :=
    fun V => ∀ (co : List PlaceId) (β K L : Type) (E : Explorer (NState co β) K L)
      (o : Decide.Out (NState co β)) (ps : List PlaceId) (p : Decide.Prop' (NState co β) L),
      ps ≠ [] → AlignProp ps p →
        (V _ _ _ E o p = .proven → o.complete = true) ∧
        (o.complete = false → (∀ i, Decide.violatesAt E o p i = false) →
          V _ _ _ E o p = .unknown) ∧
        (o.complete = true → o.stopped = false →
          (V _ _ _ E o p = .proven ↔ ∀ i, Decide.violatesAt E o p i = false)) ∧
        (∀ i, V _ _ _ E o p = .violated i → Decide.violatesAt E o p i = true) ∧
        (o.complete = false → o.stopped = false → (∃ i, Decide.violatesAt E o p i = true) →
          ∃ i, V _ _ _ E o p = .violated i)

/- The pinned readable form of NU_055_truncation: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_055_truncation : ClassVerdict → Prop :=
fun V =>
  ∀ (co : List PlaceId) (β K L : Type) (E : Explorer (NState co β) K L) (o : Decide.Out (NState co β))
    (ps : List PlaceId) (p : Decide.Prop' (NState co β) L),
    ps ≠ [] →
      AlignProp ps p →
        (V (NState co β) K L E o p = Decide.Verdict.proven → o.complete = true) ∧
          (o.complete = false →
              (∀ (i : ℕ), Decide.violatesAt E o p i = false) → V (NState co β) K L E o p = Decide.Verdict.unknown) ∧
            (o.complete = true →
                o.stopped = false →
                  (V (NState co β) K L E o p = Decide.Verdict.proven ↔ ∀ (i : ℕ), Decide.violatesAt E o p i = false)) ∧
              (∀ (i : ℕ), V (NState co β) K L E o p = Decide.Verdict.violated i → Decide.violatesAt E o p i = true) ∧
                (o.complete = false →
                  o.stopped = false →
                    (∃ i, Decide.violatesAt E o p i = true) →
                      ∃ i, V (NState co β) K L E o p = Decide.Verdict.violated i)
-/
#guard_msgs in #print NU_055_truncation

/-! ### The reference -/

/-- A class that violates a property is a stored class. -/
theorem nu055_violatesAt_lt {S K L : Type} (E : Explorer S K L) (o : Decide.Out S)
    (p : Decide.Prop' S L) (i : ℕ) (h : Decide.violatesAt E o p i = true) : i < o.cls.length := by
  by_contra hi
  have hn : o.cls[i]? = none := List.getElem?_eq_none (by omega)
  cases p <;> simp [Decide.violatesAt, hn] at h

/-- The search of `Decide.verdict` finds nothing exactly when no class violates. -/
theorem nu055_find_none_iff {S K L : Type} (E : Explorer S K L) (o : Decide.Out S)
    (p : Decide.Prop' S L) :
    (List.range o.cls.length).find? (Decide.violatesAt E o p) = none ↔
      ∀ i, Decide.violatesAt E o p i = false := by
  rw [List.find?_eq_none]
  constructor
  · intro h i
    cases hv : Decide.violatesAt E o p i
    · rfl
    · exact absurd hv (h i (List.mem_range.mpr (nu055_violatesAt_lt E o p i hv)))
  · intro h i _
    simp [h i]

/-- The shipped verdict function satisfies the four lines: `Proven` only from a closed build
(`Decide.truncated_never_proven`); with no violating class an unclosed build gives `Unknown`; a
closed build gives `Proven` exactly when its search finds no violating class; a `Violated` is the
index that search found (`Decide.verdict`). -/
@[evidence holds NU_055_truncation]
theorem NU_055_truncation_reference : NU_055_truncation refClassVerdict := by
  intro co β K L E o ps p _ _
  refine ⟨fun h => (Decide.truncated_never_proven E o p h).1, fun hc hv => ?_,
    fun hc hs => ?_, fun i h => ?_, fun _ hs hex => ?_⟩
  · simp only [refClassVerdict, Decide.verdict]
    split
    · rfl
    · rw [(nu055_find_none_iff E o p).mpr hv]
      simp [hc]
  · simp only [refClassVerdict, Decide.verdict, hs, Bool.false_eq_true, if_false]
    rw [← nu055_find_none_iff E o p]
    cases (List.range o.cls.length).find? (Decide.violatesAt E o p) with
    | none => simp [hc]
    | some j => simp
  · simp only [refClassVerdict, Decide.verdict] at h
    split at h
    · cases h
    · cases hf : (List.range o.cls.length).find? (Decide.violatesAt E o p) with
      | none =>
        rw [hf] at h
        by_cases hc : o.complete = true <;> simp [hc] at h
      | some j =>
        rw [hf] at h
        cases h
        exact List.find?_some hf
  · simp only [refClassVerdict, Decide.verdict, hs, Bool.false_eq_true, if_false]
    cases hf : (List.range o.cls.length).find? (Decide.violatesAt E o p) with
    | none =>
      obtain ⟨i, hi⟩ := hex
      rw [(nu055_find_none_iff E o p).mp hf i] at hi
      cases hi
    | some j => exact ⟨j, rfl⟩

/-! ### Examples -/

/-- The aligned class of the examples: the empty name layer over the coloured set `[0]`. -/
def nu055_x0 : NState [0] Unit := ⟨(), fun _ _ => 0, 0, fun _ _ _ => rfl⟩

/-- The misaligned class of the examples: place `0` holds the name-symbols `0` and `1`. -/
def nu055_x2 : NState [0] Unit :=
  ⟨(), fun s _ => if s ≤ 1 then 1 else 0, 2, fun s hs _ => by simp; omega⟩

/-- An explorer with no successor: every expanded class is one at which the net rests. -/
def nu055_E : Explorer (NState [0] Unit) Unit String := ⟨fun _ => (), fun _ => 0, fun _ _ => []⟩

/-- A build that stored the aligned class and did not close (the class bound was reached). -/
def nu055_trunc : Decide.Out (NState [0] Unit) := ⟨[nu055_x0], 0, false, false, false⟩

/-- A build that stored the aligned class and closed. -/
def nu055_closed : Decide.Out (NState [0] Unit) := ⟨[nu055_x0], 1, true, false, false⟩

/-- A build that stored the misaligned class, did not expand it and did not close. -/
def nu055_truncBad : Decide.Out (NState [0] Unit) := ⟨[nu055_x2], 0, false, false, false⟩

/-- A build that stored and expanded the misaligned class and did not close (the class bound was
reached). -/
def nu055_truncBadExp : Decide.Out (NState [0] Unit) := ⟨[nu055_x2], 1, false, false, false⟩

/-- A build that stored and expanded the misaligned class and closed. -/
def nu055_closedBad : Decide.Out (NState [0] Unit) := ⟨[nu055_x2], 1, true, false, false⟩

/-- A closed build of the aligned class, then the misaligned one. -/
def nu055_closedTwo : Decide.Out (NState [0] Unit) :=
  ⟨[nu055_x0, nu055_x2], 2, true, false, false⟩

/-- `NameAligned([0])` as a safety property over the example classes. -/
def nu055_pSafe : Decide.Prop' (NState [0] Unit) String := .safety (fun S => !alignedAll [0] S)

/-- `QuiescentNameAligned([0])` as a quiescence property over the example classes, nothing
reapable. -/
def nu055_pQuiet : Decide.Prop' (NState [0] Unit) String :=
  .quiescence (fun S => !alignedAll [0] S) (fun _ => false)

theorem nu055_pSafe_align : AlignProp [0] nu055_pSafe := Or.inl rfl

theorem nu055_pQuiet_align : AlignProp [0] nu055_pQuiet := Or.inr ⟨_, rfl⟩

/-- No class of a build that stores only the aligned class violates `NameAligned([0])`. -/
theorem nu055_noViolation (o : Decide.Out (NState [0] Unit)) (ho : o.cls = [nu055_x0]) :
    ∀ i, Decide.violatesAt nu055_E o nu055_pSafe i = false := by
  intro i
  match i with
  | 0 => simp [Decide.violatesAt, ho, nu055_pSafe]; decide
  | _ + 1 => simp [Decide.violatesAt, ho, nu055_pSafe]

/-! ### Violation: a truncated graph read as closed -/

/-- A verdict function that reads an unclosed build as closed: `Proven` when no class violates. -/
def nu055_closedReading : ClassVerdict := fun _ _ _ E o p =>
  if o.stopped then .unknown
  else match (List.range o.cls.length).find? (Decide.violatesAt E o p) with
    | some i => .violated i
    | none => .proven

/-- ✗ Reading a truncated graph as closed violates NU-055 (line 1): the build that reached the
class bound with one aligned class is answered `Proven`. -/
@[evidence forbids NU_055_truncation]
theorem NU_055_truncation_forbids_closedReading : ¬ NU_055_truncation nu055_closedReading := by
  intro h
  have := (h [0] Unit Unit String nu055_E nu055_trunc [0] nu055_pSafe (by simp)
    nu055_pSafe_align).1 (by decide)
  revert this
  decide

/-! ### Violation: a truncation reported as a violation -/

/-- A verdict function that reports an unclosed build as `Violated` at its first class. -/
def nu055_truncViolated : ClassVerdict := fun _ _ _ E o p =>
  if o.complete then Decide.verdict E o p else .violated 0

/-- ✗ Reporting a truncation as a violation violates NU-055 (line 2): the build that reached the
class bound has no violating class and is answered `Violated`. -/
@[evidence forbids NU_055_truncation]
theorem NU_055_truncation_forbids_truncViolated : ¬ NU_055_truncation nu055_truncViolated := by
  intro h
  have := (h [0] Unit Unit String nu055_E nu055_trunc [0] nu055_pSafe (by simp)
    nu055_pSafe_align).2.1 rfl (nu055_noViolation nu055_trunc rfl)
  revert this
  decide

/-! ### Violation: a verdict function that never decides -/

/-- A verdict function that always answers `Unknown`. -/
def nu055_alwaysUnknown : ClassVerdict := fun _ _ _ _ _ _ => .unknown

/-- ✗ Never deciding violates NU-055 (line 3): the closed build of one aligned class has no
violating class and must be answered `Proven`. -/
@[evidence forbids NU_055_truncation]
theorem NU_055_truncation_forbids_alwaysUnknown : ¬ NU_055_truncation nu055_alwaysUnknown := by
  intro h
  have := ((h [0] Unit Unit String nu055_E nu055_closed [0] nu055_pSafe (by simp)
    nu055_pSafe_align).2.2.1 rfl rfl).mpr (nu055_noViolation nu055_closed rfl)
  revert this
  decide

/-! ### Violation: a closed graph proved without reading its classes -/

/-- A verdict function that answers `Proven` on every closed build and reads the classes only of
a build that did not close. Composed with the shipped build it is harmless for `NameAligned`,
whose early stop keeps a build holding a misaligned class from closing, and wrong for
`QuiescentNameAligned`, which has no early stop. -/
def nu055_provenWhenClosed : ClassVerdict := fun _ _ _ E o p =>
  if o.complete then .proven else Decide.verdict E o p

/-- ✗ Proving every closed graph violates NU-055 (line 3): the closed build whose one class is
expanded, rests (no successor) and holds two names in place `0` violates
`QuiescentNameAligned([0])` and is answered `Proven`. -/
@[evidence forbids NU_055_truncation]
theorem NU_055_truncation_forbids_provenWhenClosed :
    ¬ NU_055_truncation nu055_provenWhenClosed := by
  intro h
  have := ((h [0] Unit Unit String nu055_E nu055_closedBad [0] nu055_pQuiet (by simp)
    nu055_pQuiet_align).2.2.1 rfl rfl).mp rfl 0
  revert this
  decide

/-! ### Violation: a `Violated` that names the wrong class -/

/-- A verdict function that reports every violation at the first class. -/
def nu055_firstClass : ClassVerdict := fun _ _ _ E o p =>
  match Decide.verdict E o p with
  | .violated _ => .violated 0
  | v => v

/-- ✗ Naming a class that does not violate violates NU-055 (line 4): in the closed build of the
aligned class and then the misaligned one, the second class violates `NameAligned([0])` and the
verdict names the first. -/
@[evidence forbids NU_055_truncation]
theorem NU_055_truncation_forbids_firstClass : ¬ NU_055_truncation nu055_firstClass := by
  intro h
  have := (h [0] Unit Unit String nu055_E nu055_closedTwo [0] nu055_pSafe (by simp)
    nu055_pSafe_align).2.2.2.1 0 (by decide)
  revert this
  decide

/-! ### Violation: a truncation always answered `Unknown` (ruling D59 (b)) -/

/-- A verdict function that answers `Unknown` on every build that did not close, whatever its
stored classes hold, and reads a closed build as the shipped one does: the reading D59 (b), which
the ruling rejected. -/
def nu055_unknownWhenCut : ClassVerdict := fun _ _ _ E o p =>
  if o.complete then Decide.verdict E o p else .unknown

/-- ✗ Answering `Unknown` on every truncation violates NU-055 (line 5, the prefix rule): the build
that reached the class bound has stored the class with two names in place `0`, which violates
`NameAligned([0])`, and is answered `Unknown`. -/
@[evidence forbids NU_055_truncation]
theorem NU_055_truncation_forbids_unknownWhenCut : ¬ NU_055_truncation nu055_unknownWhenCut := by
  intro h
  obtain ⟨i, hi⟩ := (h [0] Unit Unit String nu055_E nu055_truncBad [0] nu055_pSafe (by simp)
    nu055_pSafe_align).2.2.2.2 rfl rfl ⟨0, by decide⟩
  simp [nu055_unknownWhenCut, nu055_truncBad] at hi

/-- Mutant reading of the truncation block without the prefix rule: lines 1 to 4 alone, under
which a truncated graph may answer `Unknown` whatever its stored classes hold. -/
def NU_055_truncation_mutant_noPrefix (V : ClassVerdict) : Prop :=
  ∀ (co : List PlaceId) (β K L : Type) (E : Explorer (NState co β) K L)
    (o : Decide.Out (NState co β)) (ps : List PlaceId) (p : Decide.Prop' (NState co β) L),
    ps ≠ [] → AlignProp ps p →
      (V _ _ _ E o p = .proven → o.complete = true) ∧
      (o.complete = false → (∀ i, Decide.violatesAt E o p i = false) →
        V _ _ _ E o p = .unknown) ∧
      (o.complete = true → o.stopped = false →
        (V _ _ _ E o p = .proven ↔ ∀ i, Decide.violatesAt E o p i = false)) ∧
      (∀ i, V _ _ _ E o p = .violated i → Decide.violatesAt E o p i = true)

/-- The verdict function of D59 (b) kills the mutant without the prefix rule: on a closed build
it is the shipped verdict and on any other it answers `Unknown`, so it meets lines 1 to 4, but
line 5 asks for `Violated` on the truncated build that stored a misaligned class
(`NU_055_truncation_forbids_unknownWhenCut`). -/
@[evidence mutant NU_055_truncation]
theorem NU_055_truncation_mutant_noPrefix_killed :
    NU_055_truncation_mutant_noPrefix nu055_unknownWhenCut ∧
      ¬ NU_055_truncation nu055_unknownWhenCut := by
  refine ⟨fun co β K L E o ps p hps hp => ?_, NU_055_truncation_forbids_unknownWhenCut⟩
  obtain ⟨-, -, h3, h4, -⟩ := NU_055_truncation_reference co β K L E o ps p hps hp
  refine ⟨fun h => ?_, fun hc _ => ?_, fun hc hs => ?_, fun i h => ?_⟩
  · unfold nu055_unknownWhenCut at h
    split at h
    · assumption
    · cases h
  · simp [nu055_unknownWhenCut, hc]
  · simp only [nu055_unknownWhenCut, hc, ↓reduceIte]
    exact h3 hc hs
  · unfold nu055_unknownWhenCut at h
    split at h
    · exact h4 i h
    · cases h

/-! ### Mutant: soundness of the verdict only -/

/-- Mutant reading of the truncation block that keeps the soundness of each verdict and drops
what a verdict must be: `Proven` only from a closed graph none of whose classes violates, and a
`Violated` at a violating class, but no line that forces `Unknown` on a truncated graph or
`Proven` on a closed one. -/
def NU_055_truncation_mutant_soundOnly (V : ClassVerdict) : Prop :=
  ∀ (co : List PlaceId) (β K L : Type) (E : Explorer (NState co β) K L)
    (o : Decide.Out (NState co β)) (ps : List PlaceId) (p : Decide.Prop' (NState co β) L),
    ps ≠ [] → AlignProp ps p →
      (V _ _ _ E o p = .proven → o.complete = true) ∧
      (V _ _ _ E o p = .proven → ∀ i, Decide.violatesAt E o p i = false) ∧
      (∀ i, V _ _ _ E o p = .violated i → Decide.violatesAt E o p i = true)

/-- The verdict function that never decides kills the soundness-only mutant: it never answers
`Proven` or `Violated`, so it meets the mutant reading, but line 3 asks for `Proven` on a closed
graph of one aligned class (`NU_055_truncation_forbids_alwaysUnknown`). -/
@[evidence mutant NU_055_truncation]
theorem NU_055_truncation_mutant_soundOnly_killed :
    NU_055_truncation_mutant_soundOnly nu055_alwaysUnknown ∧
      ¬ NU_055_truncation nu055_alwaysUnknown := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ _ => ⟨fun h => ?_, fun h => ?_, fun _ h => ?_⟩,
    NU_055_truncation_forbids_alwaysUnknown⟩ <;> cases h

/-! ### Every line exercised -/

/-- The five lines of the truncation block are exercised by the shipped verdict function, for
both properties. On the closed build of one aligned class it answers `Proven` (lines 1 and 3);
on the same class in a build that reached the class bound it answers `Unknown` (line 2). On the
closed build whose one class rests misaligned it answers `Violated` at that class for
`QuiescentNameAligned` (lines 3 and 4). On the build that stored that class without expanding it
and did not close, it answers `Unknown` for `QuiescentNameAligned` (line 2, the prefix reading:
a class not expanded is not one at which the net rests) and `Violated` at that class for
`NameAligned` (lines 4 and 5, a stored class). On the build that expanded that class and did not
close it answers `Violated` at it for `QuiescentNameAligned` (lines 4 and 5, an expanded class at
which the net rests). On the closed build of two classes it names the second, misaligned one
(line 4). -/
@[evidence nonvacuous NU_055_truncation]
theorem NU_055_truncation_nonvacuous :
    refClassVerdict _ _ _ nu055_E nu055_closed nu055_pSafe = .proven ∧
      refClassVerdict _ _ _ nu055_E nu055_trunc nu055_pSafe = .unknown ∧
      refClassVerdict _ _ _ nu055_E nu055_closed nu055_pQuiet = .proven ∧
      refClassVerdict _ _ _ nu055_E nu055_closedBad nu055_pQuiet = .violated 0 ∧
      refClassVerdict _ _ _ nu055_E nu055_truncBad nu055_pQuiet = .unknown ∧
      refClassVerdict _ _ _ nu055_E nu055_truncBad nu055_pSafe = .violated 0 ∧
      refClassVerdict _ _ _ nu055_E nu055_truncBadExp nu055_pQuiet = .violated 0 ∧
      refClassVerdict _ _ _ nu055_E nu055_closedTwo nu055_pSafe = .violated 1 := by
  decide

end Libpetri.Spec
