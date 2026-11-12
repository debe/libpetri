import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryNuVer

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
  Route B `Proven` of `NameAligned(S)` holds in every marking the untimed, environment-free,
  atomic executor `NuStepC` reaches, and a `Proven` of `QuiescentNameAligned(S)` in every
  marking at which it rests. It is a predicate over an abstract pair of deciders. Witnesses:
  `refNameAligned` (glossary `GlossaryNuVer.lean`) and `refQuiescentNameAligned` (here).
* `NU_055_truncation` (kind F): the verdict read off a built graph. A graph that did not close
  never gives `Proven`, and gives `Unknown` when no class violates the property; a closed graph
  gives `Proven` exactly when no class violates it; a `Violated` names a violating class. It is
  a predicate over an abstract verdict function on a built graph. Witness: `refClassVerdict`, the
  shipped `Decide.verdict`.

The refusal order is a fourth block, `NU_055_refusal` in `NU_055_steps.lean`. Left out, each by
an assumes sentence of a block: the routing rules ('Route B only', Route B before a budget place),
which are dispatch rules of the verifier pipeline; the prefix rule's `Violated` on a truncated graph and exactness against the executor (open ruling
D59); the counterexample's shape (open ruling D40); the timed graph (gap R6) and in-flight
markings, which the spec itself leaves unproved; the API shape and descriptions (N).
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
  quote "For places `p` and `q` of `S`, the same place included, and the name-symbols `s` and `t`: `s` resident in `p` and `t` resident in `q` imply `s = t`."
        "An empty place imposes nothing, but a place holding two names violates it whatever the others hold, so the singleton `NameAligned(p)` says that `p` never holds two names."
        "*Where* name alignment is offered, `NameAligned(S)` for a non-empty `S` *shall* hold on a class of the graph exactly when, for places `p` and `q` of `S`, the same place included, every name-symbol resident in `p` equals every name-symbol resident in `q`."
        "The predicate compares names only for equality, so it is invariant under any permutation of the name-symbols."
        "It is therefore a function of the canonical key of a class ([VER-012] AC2), and deciding it on the name-permutation quotient decides it on the graph."
        "Its places compare by name, and a place listed twice counts once, at its first occurrence, so `NameAligned(box, list, box)` is `NameAligned(box, list)`."
        "The order of `S` changes no verdict; it fixes the description and which place a reason names."
  reading "For every coloured set co, base type β, non-empty list ps and class S of the graph, the check A answers true exactly when any name-symbol s resident in a place p of ps and any name-symbol t resident in a place q of ps, p = q allowed, are equal."
  assumes "The model is a class of the Route B graph (NState co β, Graph.lean): a base b, a name layer m giving each name-symbol and each coloured place (a position of co) a count, and a bound above every live symbol. A name-symbol s is resident in p when its count there is not 0 (Name.lean resident). The NameAligned bullet speaks of a marking; its EARS restatement and the line speak of a class of the graph, which is where Route B evaluates the predicate. A marking's names are read on its coloured places through the one projection nameOf: its class is its name view (view co nameOf m), and on that view the line is the statement that all tokens in the places of S carry one name (alignedAll_view_iff, cited). Places are PlaceId, so 'its places compare by name' is equality of ids, and the check takes S as a list."
          "The line is the definition of the NameAligned bullet (its second and third sentences, restated by the EARS sentence): self pairs included, so a place holding two names fails whatever the others hold, and an empty place has no resident symbol and imposes nothing. The QuiescentNameAligned bullet reads 'the same predicate'; where it is read is NU_055_sound's subject. The first sentence of the NameAligned bullet ('in every reachable marking') is NU_055_sound's."
          "The permutation sentence, the first half of the canonical-key sentence and the S-order sentences ('a place listed twice counts once', 'The order of S changes no verdict', read on the predicate) are consequences of the line, not lines of their own: the line fixes A on every non-empty list, so A is the shipped check there (NU_055_eq_ref), and NU_055_perm, NU_055_key and NU_055_members derive the three invariances. The spec states them with 'so' and 'therefore', and they get no EARS sentence. The models that break one of them (nu055_symZero, nu055_headOnly) are killed by the line itself. The second half of the canonical-key sentence ('deciding it on the name-permutation quotient decides it on the graph') is also a claim about the verdict: the verdict on a closed graph is the predicate's answer over its classes, NU_055_truncation line 3."
          "An uncoloured place has no row in the name layer, so nothing is resident there (resident_of_not_mem) and the line holds vacuously for it (alignedAll_uncoloured, cited). That such a place is refused (refusal step 6, 'Coloured places only', AC2) is not a line of this block: it is line 6 of the refusal block NU_055_refusal (NU_055_steps.lean), whose NU_055_refusal_uncoloured_refused shows that such a place never reaches the graph, and whose NU_055_refusal_forbids_noUncoloured kills the design's mutant 'proves on an uncoloured place'."
          "'A place listed twice counts once, at its first occurrence' also fixes the description and which place a reason names, and 'The order of S changes no verdict' also covers the reason of an Unknown. The description (the Property: line) is N (an API note), and which place a reason names is the refusal order's (NU_055_refusal). On the predicate, the only part of the verdict this block models, order and repeats change nothing (NU_055_members)."
          "'An empty S MUST be rejected where it is constructed' and 'S is a non-empty list' are the language API (N): each constructor rejects an empty list (Java records, the TypeScript signature, the Rust panic, the Python ValueError). The line is stated for a non-empty S only, so the block fixes no answer for the empty list, which never reaches a verdict."
          "AC5 (invariance under name permutation, on a class and that class permuted, and under reordering S) is NU_055_perm and NU_055_members, theorems of the line; its run of the worked example with names minted in another scope ([NU-010]) is a test of the minter (NU-010, NU-011, wave W9) and of the verdict, not of the predicate, and is not encoded."
          "AC7 ('S is a list'; the cross pair of reply and staged without the self pairs would accept a marking with two stale replies in reply) is the line with self pairs: NU_055_forbids_crossOnly kills the check without self pairs. AC7's construction rules are the API (N, above) and NU_055_members; its descriptions are N; its verdicts and witness lengths on the worked example are tests on the fixtures (Q), as the Route B graph of that net is not computed in Lean."
  signoff "pending"
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

/-! ## NU-055 (B): a Route B `Proven` holds for the atomic executor -/

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

requirement NU_055_sound
  id "NU-055"
  title "Name Alignment: soundness"
  kind B
  scope "every verifier that offers NameAligned or QuiescentNameAligned (MAY), judged against the untimed, environment-free executor with atomic firings"
  source verbatim "spec/12-nu-nets.md"
  quote "**NameAligned(S)**, for a non-empty list `S` of places: in every reachable marking, the places of `S` together hold at most one distinct name."
        "**QuiescentNameAligned(S)**: the same predicate, read only in the reachable quiescent markings."
        "Lean `Novel/RouteB/Aligned.lean` (`routeB_untimed_nameAligned_sound`, `routeB_untimed_quiescentNameAligned_sound`) proves: for the **untimed, environment-free executor with atomic firings**, a `Proven` of either property holds in every marking that executor reaches (for the quiescent form, every marking at which it rests): the tokens in the places of `S` all carry the same name."
        "*If* the premises above hold, *then* Route B *shall* answer `Proven` for `NameAligned(S)` only if the tokens in the places of `S` all carry the same name in every marking the untimed, environment-free executor with atomic firings reaches."
        "*If* the premises above hold, *then* Route B *shall* answer `Proven` for `QuiescentNameAligned(S)` only if the tokens in the places of `S` all carry the same name in every marking that the untimed, environment-free executor with atomic firings reaches and rests at, resting being read with the reapable set of the call ([VER-002])."
  reading "For every call q with a duplicate-free coloured set, every transition in the fragment for its role and without input guards, every place of S coloured, and an initial marking m0 whose coloured places are empty and whose counts are q's initial marking, and for every projection nameOf:"
          "if D answers Proven for NameAligned(S), then in every marking m that NuStepC reaches from m0, any two tokens in places of S, the same place allowed, carry the same name;"
          "if, in addition, every join key consumes at least one token (PosKeys), and Dq answers Proven for QuiescentNameAligned(S) with the reapable set reap, then the same holds in every marking m that NuStepC reaches from m0 and at which every transition the executor can fire is reapable (ExecRests reap, the call's own reapable set)."
  assumes "The executor is Novel's NuStepC (Sim.lean): untimed, environment-free, one atomic firing per step, a coloured consumer taking any resident name (ruling D16 is why that differs from EXEC-010's FIFO). It is the executor the Soundness paragraph names. It is not the reference ν firing: RefNu and its reachability RefNuReach do not exist yet. Design correction S7 (a) states this line over RefNuReach once the bridge B1 (Reference/NuLink.lean, wave W9) exists; that changes the statement and its hash, so the block stays pending until then."
          "The premises are hypotheses (design correction S6), one per premise bullet of the Soundness paragraph: 'the coloured places start empty' (hempty); 'every place of S coloured' (ps ⊆ co; in the shipped verifier the refusal order enforces it, and hempty with it: NU_055_refusal_build_premises); 'the conditions the classifier establishes (InFragment)', 'unguarded inputs' (GuardFree) and, for the quiescent form, PosKeys. The contracts of the mints and coloured consumers (NU-010, NU-051, NU-054), the projection contract of NU-050 (one projection nameOf, Exec.ProjCoherent) and one token per output place of the firing's branch (IO-016 AC4) are built into NuStepC, as the Soundness paragraph says. Conflict-only priority (NU-052) is the conflict flag of the call, read by NuStepC through the same prune."
          "Two hypotheses are not spec premises and get no premise bullet. q.co.Nodup says the list the call holds is a set: the spec's coloured set is a set, and the classifier's coloured order (Rust coloured_order, the co of the Lean theorems) lists each place once. q.a0 = alpha m0 says the call's initial counts are those of m0, the marking the runs start from. Neither narrows the claim about a call the shipped pipeline makes."
          "The lines ask soundness for every coloured set and role assignment that meets InFragment, not only for the classifier's. That is the premise bullet as written ('the conditions the classifier establishes (InFragment)', a condition, not the classifier), and Route B alone takes co and role as inputs; the classifier's own output meets InFragment (classifyS_inFragment, Novel/RouteB/Classify.lean, NU-051). That the coloured set is the one the classifier computes for the call, not one the caller names, is the pipeline's (wave W10)."
          "The lines are soundness only: a decider that never answers Proven meets them. That a closed graph none of whose classes violates gives Proven is NU_055_truncation line 3, on the verdict function; whether a Proven or a Violated of the deciders is exact against the executor (VER-012's 'exact (sound and complete)', clash ver-d#1) waits for ruling D59."
          "The deciders are AlignDecider (glossary GlossaryNuVer.lean, witness refNameAligned) and QAlignDecider (here, witness refQuiescentNameAligned): Route B alone, from the initial class, with no refusal step and no routing. The quiescent line reads resting with the call's reapable set q.reap, the one the decider is given, as the reap-aware quiescence of VER-002 does on the graph. Every refusal of the refusal order (steps 1 to 7: cancellation and budget, an absent place, Bounded(k) outside its premises, in-flight state, the fragment declines of EXTENDED and BASE, an arrival into a coloured place, a modelled environment place, an uncoloured place of S, a marked coloured place) and the 'Coloured places only' and 'Modelled injection' rules are the block NU_055_refusal (NU_055_steps.lean), worded under ruling D20 (clashes nu-c#7, nu-c#9, NC-7, NC-8). 'Route B only' (no other route decides, no NU-053 fallback, no script) and the routing rule that sends these properties to Route B before a budget place are dispatch rules of the verifier pipeline. None of them is encoded here."
          "Not covered, as the spec itself says: the timed name × time graph the shipped Route B builds (gap R6 of Novel/RouteB/Sound.lean), the all-immediate worked example included; markings with actions in flight (the Lean model has none); faithfulness of a carrier's name to what its token is about, which rests on the unchecked contracts of NU-051."
          "AC1 (the worked example under EXTENDED: QuiescentNameAligned(box, list) and QuiescentCount Proven, NameAligned(box, list) Violated in 8 firings, the buggy variant Violated in 12, each attributed to Route B) is a fixture test (Q): the graph of that net is not computed in Lean. Its Proven verdicts are the kind lines 1 and 2 make sound; its Violated verdicts and witness lengths are graph facts."
          "AC2 (an uncoloured or absent place gives Unknown naming it, the first in S) and AC6 (an environment place under AlwaysAvailable gives Unknown naming it, a marked coloured place gives Unknown naming it) and AC8 (the refusal order on the worked example) are lines 1, 5, 6 and 7 of NU_055_refusal. AC3 (under BASE the net is outside the fragment, the reason names EXTENDED and the report names the ignored relay declarations) is its line 2; the report note naming the ignored relay declarations is NU-054's (AC5). AC4 (no other route decides; the script encoders return none) is the pipeline's 'Route B only' rule, not encoded; its last clause (a truncation stays Unknown unless the prefix rule finds a violation) is NU_055_truncation line 2."
  signoff "pending"
  statement : AlignDecider → QAlignDecider → Prop :=
    fun D Dq =>
      (∀ (q : AlignQuery) (nameOf : Colour → ℕ) (m0 m : CMarking),
        q.co.Nodup → (∀ T ∈ q.net, InFragment q.co T (q.role T)) →
        (∀ T ∈ q.net, GuardFree T.base) → (∀ p ∈ q.ps, p ∈ q.co) →
        (∀ i : Fin q.co.length, m0 q.co[i.1] = []) → q.a0 = alpha m0 →
        D q = .proven →
        Relation.ReflTransGen (NuStepC q.co nameOf q.net q.role q.conflict) m0 m →
        ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ m p, ∀ d ∈ m p', nameOf c = nameOf d) ∧
      (∀ (q : QAlignQuery) (nameOf : Colour → ℕ) (m0 m : CMarking),
        q.co.Nodup → (∀ T ∈ q.net, InFragment q.co T (q.role T)) →
        (∀ T ∈ q.net, PosKeys (q.role T)) →
        (∀ T ∈ q.net, GuardFree T.base) → (∀ p ∈ q.ps, p ∈ q.co) →
        (∀ i : Fin q.co.length, m0 q.co[i.1] = []) → q.a0 = alpha m0 →
        Dq q = .proven →
        Relation.ReflTransGen (NuStepC q.co nameOf q.net q.role q.conflict) m0 m →
        ExecRests (co := q.co) (nameOf := nameOf) (net := q.net) q.reap m →
        ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ m p, ∀ d ∈ m p', nameOf c = nameOf d)

/- The pinned readable form of NU_055_sound: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_055_sound : AlignDecider → QAlignDecider → Prop :=
fun D Dq =>
  (∀ (q : AlignQuery) (nameOf : Colour → ℕ) (m0 m : CMarking),
      q.co.Nodup →
        (∀ T ∈ q.net, InFragment q.co T (q.role T)) →
          (∀ T ∈ q.net, GuardFree T.base) →
            (∀ p ∈ q.ps, p ∈ q.co) →
              (∀ (i : Fin q.co.length), m0 q.co[↑i] = []) →
                q.a0 = alpha m0 →
                  D q = Decide.Verdict.proven →
                    Relation.ReflTransGen (NuStepC q.co nameOf q.net q.role q.conflict) m0 m →
                      ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ m p, ∀ d ∈ m p', nameOf c = nameOf d) ∧
    ∀ (q : QAlignQuery) (nameOf : Colour → ℕ) (m0 m : CMarking),
      q.co.Nodup →
        (∀ T ∈ q.net, InFragment q.co T (q.role T)) →
          (∀ T ∈ q.net, PosKeys (q.role T)) →
            (∀ T ∈ q.net, GuardFree T.base) →
              (∀ p ∈ q.ps, p ∈ q.co) →
                (∀ (i : Fin q.co.length), m0 q.co[↑i] = []) →
                  q.a0 = alpha m0 →
                    Dq q = Decide.Verdict.proven →
                      Relation.ReflTransGen (NuStepC q.co nameOf q.net q.role q.conflict) m0 m →
                        ExecRests q.reap m → ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ m p, ∀ d ∈ m p', nameOf c = nameOf d
-/
#guard_msgs in #print NU_055_sound

/-! ### The reference -/

/-- The shipped deciders satisfy NU-055's soundness lines: they are the build and verdict
`routeB_untimed_nameAligned_sound` and `routeB_untimed_quiescentNameAligned_sound` speak of. -/
@[evidence holds NU_055_sound]
theorem NU_055_sound_reference : NU_055_sound refNameAligned refQuiescentNameAligned := by
  refine ⟨fun q nameOf m0 m hco hfr hG hps hempty ha0 hP hR => ?_,
    fun q nameOf m0 m hco hfr hpos hG hps hempty ha0 hP hR hrest => ?_⟩
  · unfold refNameAligned at hP
    rw [ha0] at hP
    exact routeB_untimed_nameAligned_sound hco hfr hG hps hempty hP hR
  · unfold refQuiescentNameAligned at hP
    rw [ha0] at hP
    exact routeB_untimed_quiescentNameAligned_sound hco hfr hpos hG hps hempty hP hR hrest

/-! ### Examples: a mint that fires twice -/

/-- One coloured place `0`, one mint with no input that writes `0`. -/
def nu055_tM : NuTrans where
  base := { name := "M", inputs := [], inhibitors := [], reads := [], resets := [] }
  rows := [⟨[0], []⟩]
  keys := none
  relays := []

/-- The marking with the names `l` in place `0`. -/
def nu055_mk (l : List Colour) : CMarking := fun p => if p = 0 then l else []

/-- The mint fires from `nu055_mk l` and adds a fresh name `f`. -/
theorem nu055_mint_step (l : List Colour) (f : ℕ) (hf : f ∉ l) :
    NuStepC [0] id [nu055_tM] (fun _ => Role.mint) false (nu055_mk l) (nu055_mk (l ++ [f])) := by
  refine ⟨nu055_tM, by simp, ⟨[0], []⟩, by simp [nu055_tM], by simp [enabledC, nu055_tM], ?_, ?_,
    fun h => by cases h⟩
  · funext p
    rcases p with _ | p <;>
      simp [alpha, alphaFireC, nu055_mk, consumedAt, specAt, nu055_tM, Row.resolve]
  · refine ⟨0, [], fun _ => [f], fun h => by simp [nu055_tM] at h, List.Forall₂.nil, ?_, ?_,
      fun h => by simp [nu055_tM] at h, ?_, ?_⟩
    · intro i u; simp [rmvList, nu055_tM]
    · intro i; fin_cases i; simp [Row.resolve]
    · refine ⟨f, ?_, ?_⟩
      · intro i; fin_cases i
        simp [nameLayer, nu055_mk]
        intro x hx hxf; exact hf (hxf ▸ hx)
      · intro i w hw; simpa using hw
    · funext u i
      fin_cases i
      by_cases huf : u = f
      · subst huf; simp [rmvList, nameLayer, nu055_mk, nu055_tM, List.filter_append]
      · have : ¬ f = u := fun h => huf h.symm
        simp [rmvList, nameLayer, nu055_mk, nu055_tM, List.filter_append, this]

/-- The mint fires twice: place `0` ends with the names `0` and `1`. -/
theorem nu055_mint_run :
    Relation.ReflTransGen (NuStepC [0] id [nu055_tM] (fun _ => Role.mint) false)
      (nu055_mk []) (nu055_mk [0, 1]) :=
  (Relation.ReflTransGen.single (nu055_mint_step [] 0 (by simp))).tail
    (nu055_mint_step [0] 1 (by simp))

/-- The call `NameAligned([0])` on the mint net. -/
def nu055_qMint : AlignQuery := ⟨[0], [nu055_tM], fun _ => Role.mint, false, 0, 0, [0],
  alpha (nu055_mk [])⟩

/-- The call `QuiescentNameAligned([0])` on the mint net, every transition reapable. -/
def nu055_qqMint : QAlignQuery := { toAlignQuery := nu055_qMint, reap := fun _ => true }

theorem nu055_mint_inFragment :
    ∀ T ∈ [nu055_tM], InFragment [0] T ((fun _ => Role.mint) T) := by
  intro T hT
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT
  subst hT
  exact ⟨⟨by simp [nu055_tM], by decide, by decide⟩, rfl, by simp [nu055_tM]⟩

theorem nu055_mint_guardFree : ∀ T ∈ [nu055_tM], GuardFree T.base := by
  intro T hT s hs
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT
  subst hT
  simp [nu055_tM] at hs

/-! ### Violations: deciders that always answer `Proven` -/

/-- A decider of `NameAligned(S)` that always answers `Proven`. -/
def nu055_alwaysProven : AlignDecider := fun _ => .proven

/-- A decider of `QuiescentNameAligned(S)` that always answers `Proven`. -/
def nu055_qAlwaysProven : QAlignDecider := fun _ => .proven

/-- ✗ A decider that always proves violates NU-055's soundness (line 1): the mint fires twice and
place `0` holds two names. -/
@[evidence forbids NU_055_sound]
theorem NU_055_sound_forbids_alwaysProven :
    ¬ NU_055_sound nu055_alwaysProven refQuiescentNameAligned := by
  intro h
  have := h.1 nu055_qMint id (nu055_mk []) (nu055_mk [0, 1]) (by simp [nu055_qMint])
    nu055_mint_inFragment nu055_mint_guardFree (by simp [nu055_qMint])
    (by intro i; fin_cases i; rfl) rfl rfl nu055_mint_run 0 (by simp [nu055_qMint]) 0
    (by simp [nu055_qMint]) 0 (by simp [nu055_mk]) 1 (by simp [nu055_mk])
  simp at this

/-- ✗ A quiescent decider that always proves violates NU-055's soundness (line 2): with every
transition reapable, every marking is a resting one, and the mint run rests with two names in
place `0`. -/
@[evidence forbids NU_055_sound]
theorem NU_055_sound_forbids_qAlwaysProven :
    ¬ NU_055_sound refNameAligned nu055_qAlwaysProven := by
  intro h
  have := h.2 nu055_qqMint id (nu055_mk []) (nu055_mk [0, 1]) (by simp [nu055_qqMint, nu055_qMint])
    nu055_mint_inFragment
    (by intro T _ cin rel hr; cases hr)
    nu055_mint_guardFree (by simp [nu055_qqMint, nu055_qMint])
    (by intro i; fin_cases i; rfl) rfl rfl nu055_mint_run
    (fun _ _ _ => rfl) 0 (by simp [nu055_qqMint, nu055_qMint]) 0
    (by simp [nu055_qqMint, nu055_qMint]) 0 (by simp [nu055_mk]) 1 (by simp [nu055_mk])
  simp at this

/-! ### Mutant: alignment at the initial marking only -/

/-- Mutant reading of NU-055's soundness that reads "in every reachable marking" as "in the
initial marking": under the same premises, a `Proven` says only that the tokens in the places of
`S` carry one name in the initial marking. -/
def NU_055_sound_mutant_initialOnly (D : AlignDecider) (Dq : QAlignDecider) : Prop :=
  (∀ (q : AlignQuery) (nameOf : Colour → ℕ) (m0 : CMarking),
    q.co.Nodup → (∀ T ∈ q.net, InFragment q.co T (q.role T)) →
    (∀ T ∈ q.net, GuardFree T.base) → (∀ p ∈ q.ps, p ∈ q.co) →
    (∀ i : Fin q.co.length, m0 q.co[i.1] = []) → q.a0 = alpha m0 →
    D q = .proven →
    ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ m0 p, ∀ d ∈ m0 p', nameOf c = nameOf d) ∧
  (∀ (q : QAlignQuery) (nameOf : Colour → ℕ) (m0 : CMarking),
    q.co.Nodup → (∀ T ∈ q.net, InFragment q.co T (q.role T)) →
    (∀ T ∈ q.net, PosKeys (q.role T)) →
    (∀ T ∈ q.net, GuardFree T.base) → (∀ p ∈ q.ps, p ∈ q.co) →
    (∀ i : Fin q.co.length, m0 q.co[i.1] = []) → q.a0 = alpha m0 →
    Dq q = .proven →
    ExecRests (co := q.co) (nameOf := nameOf) (net := q.net) q.reap m0 →
    ∀ p ∈ q.ps, ∀ p' ∈ q.ps, ∀ c ∈ m0 p, ∀ d ∈ m0 p', nameOf c = nameOf d)

/-- A place of `S` is empty in an initial marking whose coloured places are empty, when every
place of `S` is coloured. -/
theorem nu055_initial_empty {co ps : List PlaceId} {m0 : CMarking}
    (hps : ∀ p ∈ ps, p ∈ co) (hempty : ∀ i : Fin co.length, m0 co[i.1] = []) {p : PlaceId}
    (hp : p ∈ ps) : m0 p = [] := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hps p hp)
  exact hempty ⟨i, hi⟩

/-- The decider that always proves kills the initial-only mutant: the premises put no token in a
place of `S` at the start, so it meets the mutant reading, but the mint run reaches two names in
place `0`, which NU-055's soundness rejects (`NU_055_sound_forbids_alwaysProven`). -/
@[evidence mutant NU_055_sound]
theorem NU_055_sound_mutant_initialOnly_killed :
    NU_055_sound_mutant_initialOnly nu055_alwaysProven refQuiescentNameAligned ∧
      ¬ NU_055_sound nu055_alwaysProven refQuiescentNameAligned := by
  refine ⟨⟨fun q _ m0 _ _ _ hps hempty _ _ p hp _ _ c hc _ _ => ?_,
      fun q _ m0 _ _ _ _ hps hempty _ _ _ p hp _ _ c hc _ _ => ?_⟩,
    NU_055_sound_forbids_alwaysProven⟩
  · rw [nu055_initial_empty hps hempty hp] at hc
    exact absurd hc (List.not_mem_nil)
  · rw [nu055_initial_empty hps hempty hp] at hc
    exact absurd hc (List.not_mem_nil)

/-! ### Every line exercised -/

/-- The call `NameAligned([0])` on the net with no transition, place `0` empty. -/
def nu055_qEmpty : AlignQuery := ⟨[0], [], fun _ => Role.ordinary, false, 2, 2, [0], fun _ => 0⟩

/-- The call `QuiescentNameAligned([0])` on the net with no transition. -/
def nu055_qqEmpty : QAlignQuery := { toAlignQuery := nu055_qEmpty, reap := fun _ => false }

/-- Both lines of NU-055's soundness are exercised by the shipped deciders. Both answer `Proven`
on the net with no transition (a closed graph of one aligned class), so the antecedents of
lines 1 and 2 are met; on the mint net, where a run reaches place `0` holding two names, neither
answers `Proven`, which lines 1 and 2 force (NU_055_sound_reference with nu055_mint_run). -/
@[evidence nonvacuous NU_055_sound]
theorem NU_055_sound_nonvacuous :
    refNameAligned nu055_qEmpty = .proven ∧ refQuiescentNameAligned nu055_qqEmpty = .proven ∧
      refNameAligned nu055_qMint ≠ .proven ∧ refQuiescentNameAligned nu055_qqMint ≠ .proven := by
  refine ⟨by decide, by decide, fun hP => ?_, fun hP => ?_⟩
  · have := NU_055_sound_reference.1 nu055_qMint id (nu055_mk []) (nu055_mk [0, 1])
      (by simp [nu055_qMint]) nu055_mint_inFragment nu055_mint_guardFree (by simp [nu055_qMint])
      (by intro i; fin_cases i; rfl) rfl hP nu055_mint_run 0 (by simp [nu055_qMint]) 0
      (by simp [nu055_qMint]) 0 (by simp [nu055_mk]) 1 (by simp [nu055_mk])
    simp at this
  · have := NU_055_sound_reference.2 nu055_qqMint id (nu055_mk []) (nu055_mk [0, 1])
      (by simp [nu055_qqMint, nu055_qMint]) nu055_mint_inFragment
      (by intro T _ cin rel hr; cases hr) nu055_mint_guardFree
      (by simp [nu055_qqMint, nu055_qMint]) (by intro i; fin_cases i; rfl) rfl hP
      nu055_mint_run (fun _ _ _ => rfl) 0 (by simp [nu055_qqMint, nu055_qMint]) 0
      (by simp [nu055_qqMint, nu055_qMint]) 0 (by simp [nu055_mk]) 1 (by simp [nu055_mk])
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
  quote "It is therefore a function of the canonical key of a class ([VER-012] AC2), and deciding it on the name-permutation quotient decides it on the graph."
        "*When* the graph closes, Route B *shall* answer `Proven` for `NameAligned(S)` exactly when every class of the graph is name-aligned on `S`, and for `QuiescentNameAligned(S)` exactly when every class of the graph at which the net rests is."
        "A graph that does not close within the class bound never yields `Proven` (Lean `Decide.truncated_never_proven`)."
        "*If* the graph does not close, because the build reaches the class bound, runs out of total budget or is cancelled ([VER-013]), *then* Route B *shall not* answer `Proven` for either property."
        "*If* the graph does not close and the prefix rule finds no violation, *then* Route B *shall* answer `Unknown`."
        "*If* Route B answers `Violated` for either property, *then* the class its counterexample ends at *shall* violate the property."
  reading "For every explorer E over classes, every build outcome o, every non-empty list ps and every property p that is NameAligned(ps) or QuiescentNameAligned(ps) over some reapable set, where a class violates p as Decide.violatesAt reads it (for NameAligned a stored class that is not aligned, for QuiescentNameAligned an expanded class at which the net rests and that is not aligned):"
          "if V answers Proven, the graph closed (o.complete);"
          "if the graph did not close and no class violates p, V answers Unknown;"
          "if the graph closed and the build was not stopped, V answers Proven exactly when no class violates p;"
          "if V answers Violated at the class index i, class i violates p."
  assumes "The model is a verdict function on a built graph (Decide.Out: the stored classes in discovery order, the number expanded, whether the build closed and whether it stopped) and a property (Decide.Prop'), restricted to the two name-alignment properties (AlignProp) on a non-empty S, the only S that reaches a verdict (NU_055's assumes). How the build stores and expands classes is Decide.build's, cited by NU_055_sound through the soundness theorems; it is not a line here."
          "'Does not close' is o.complete = false: in the shipped build that is the class bound reached, the total budget or a cancellation (cut), or the fuel of the Lean model run out. The quoted Truncation sentence names the class bound only; its EARS restatement names the budget and the cancellation as well, as VER-013 does for every route and refusal step 1 does for a call cancelled or out of budget before it starts. Lines 1 and 2 hold for each cause."
          "Line 3 is 'deciding it on the name-permutation quotient decides it on the graph', read on the verdict, and its EARS restatement: on a closed graph, Proven exactly when no class violates the property. It needs no open ruling. Ruling D59 asks whether a truncated graph may answer Violated and whether a closed graph's verdict is exact against the executor (VER-012's 'exact (sound and complete)', clash ver-d#1, VD-1); line 3 says only that a closed graph with a violating class does not answer Proven, not whether it answers Violated or Unknown, and that a closed graph with none answers Proven, which holds under either answer. Its premise o.stopped = false rules out only an outcome the build never makes (Decide.loop: a closed build is never stopped)."
          "Line 4 is the EARS restatement of the Violated paragraph's 'to a violating class': the class a Violated names violates the property, for NameAligned a stored class and for QuiescentNameAligned an expanded resting class. The paragraph's first sentence is not quoted, because the line encodes only its 'to a violating class': the rest of it (the shortest path, the attribution to Route B, counterexampleConfirmed absent, counterexampleTiming) is VER-003's and VER-012's report shape and waits for ruling D40 (clash ver-a#11); a Violated is sound for the graph only, not for the executor. The line does not model the counterexample path: it reads 'the class its counterexample ends at' as the class index the Violated verdict carries (Decide.verdict), the class the reported shortest path ends at; that identification is assumed here, not stated, and the path's shape waits for D40. For QuiescentNameAligned the line is stronger than the sentence's 'violate the property': the class is an expanded one at which the net rests, as the prefix rule of the Truncation paragraph reads it. The line has no closure premise, so it holds on a truncated graph too, matching the prefix rule's 'violated by a stored class' and 'violated by an expanded class at which the net rests'."
          "The prefix rule's Violated on a truncated graph (a NameAligned violated by a stored class, a QuiescentNameAligned violated by an expanded class at which the net rests, with the shortest witness and a report line naming the truncation) is not a line: whether a truncated graph may answer Violated is open ruling D59 (NU-050 and VER-012). Lines 2 and 4 hold under either answer, as D59 (b) answers Unknown on every truncated graph. The witness lengths and the report line are Q and VER-003's."
          "AC4's last clause ('a Route B truncation stays Unknown unless the prefix rule finds a violation') is lines 1 and 2; the rest of AC4 is NU_055_sound's assumes (pipeline, wave W10)."
  signoff "pending"
  statement : ClassVerdict → Prop :=
    fun V => ∀ (co : List PlaceId) (β K L : Type) (E : Explorer (NState co β) K L)
      (o : Decide.Out (NState co β)) (ps : List PlaceId) (p : Decide.Prop' (NState co β) L),
      ps ≠ [] → AlignProp ps p →
        (V _ _ _ E o p = .proven → o.complete = true) ∧
        (o.complete = false → (∀ i, Decide.violatesAt E o p i = false) →
          V _ _ _ E o p = .unknown) ∧
        (o.complete = true → o.stopped = false →
          (V _ _ _ E o p = .proven ↔ ∀ i, Decide.violatesAt E o p i = false)) ∧
        (∀ i, V _ _ _ E o p = .violated i → Decide.violatesAt E o p i = true)

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
              ∀ (i : ℕ), V (NState co β) K L E o p = Decide.Verdict.violated i → Decide.violatesAt E o p i = true
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
    fun hc hs => ?_, fun i h => ?_⟩
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
    nu055_pSafe_align).2.2.2 0 (by decide)
  revert this
  decide

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

/-- The four lines of the truncation block are exercised by the shipped verdict function, for
both properties. On the closed build of one aligned class it answers `Proven` (lines 1 and 3);
on the same class in a build that reached the class bound it answers `Unknown` (line 2). On the
closed build whose one class rests misaligned it answers `Violated` at that class for
`QuiescentNameAligned` (lines 3 and 4). On the build that stored that class without expanding it
and did not close, it answers `Unknown` for `QuiescentNameAligned` (line 2, the prefix reading:
a class not expanded is not one at which the net rests) and `Violated` at that class for
`NameAligned` (line 4, a stored class). On the closed build of two classes it names the second,
misaligned one (line 4). -/
@[evidence nonvacuous NU_055_truncation]
theorem NU_055_truncation_nonvacuous :
    refClassVerdict _ _ _ nu055_E nu055_closed nu055_pSafe = .proven ∧
      refClassVerdict _ _ _ nu055_E nu055_trunc nu055_pSafe = .unknown ∧
      refClassVerdict _ _ _ nu055_E nu055_closed nu055_pQuiet = .proven ∧
      refClassVerdict _ _ _ nu055_E nu055_closedBad nu055_pQuiet = .violated 0 ∧
      refClassVerdict _ _ _ nu055_E nu055_truncBad nu055_pQuiet = .unknown ∧
      refClassVerdict _ _ _ nu055_E nu055_truncBad nu055_pSafe = .violated 0 ∧
      refClassVerdict _ _ _ nu055_E nu055_closedTwo nu055_pSafe = .violated 1 := by
  decide

end Libpetri.Spec
