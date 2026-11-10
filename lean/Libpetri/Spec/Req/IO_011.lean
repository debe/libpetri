import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary

set_option linter.missingDocs true

/-!
# IO-011: Output And (`spec/02-input-output-specs.md`)

A predicate over an abstract firing relation `F : FireRel N`, the firing relation of an executor
with output validation enabled ([CONC-026], the default), checked against the reference semantics
(`Reference.Fires`, as `RefFire`), against concrete firing relations that break it, and against
mutant readings.

The statement quantifies over the transitions that build (`Builds`: the build-time checks
of the Output Composition preamble, [IO-011]–[IO-014]), so a definition that building rejects is
not a transition the statement speaks of. It covers the firing half of IO-011 in two clauses:
every child of an `And` (nested `And`s flattened) receives tokens, and the produced set is, on
the places the spec names, exactly one output branch, and that branch is unique (one index of the
branch list), so an `And` nested in the alternative an inner `Xor` chose is held to the same rule.
The build-time half (a place named twice in one output branch is rejected) is the first conjunct
of `Builds`; the reference semantics, which takes every `Trans N` as built, still fires
`And(P, P)` (`IO_011_reference_fires_duplicate`), and that transition is outside the scope.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Terms local to IO-011 -/

/-- The children of an `And` node, with nested `And`s flattened: `And(A, And(B, C))` has the
children `A`, `B` and `C`. A node that is not an `And` is its own one child. (Local term, not in
`spec/glossary.md`.) -/
def andChildren {N : Type} : Out N → List (Out N)
  | .and l r => andChildren l ++ andChildren r
  | o => [o]

/-- **Received tokens** (local term, not in `spec/glossary.md`): the child output spec `c`
received tokens from a firing that deposited `d` when the produced set contains a place that `c`
names (`outPlaces`, the `allPlaces` of IO-017). -/
def ChildReceived {N : Type} (d : List N) (c : Out N) : Prop :=
  ∃ p ∈ outPlaces c, Produced d p

/-- **One unique branch** (local term): exactly one index `i` of the output-branch list of `o`
holds a branch that is exact for `d` on the places `o` names. -/
def IO_011_uniqueBranch {N : Type} (o : Out N) (d : List N) : Prop :=
  ∃ (i : Nat) (b : List N), o.branches[i]? = some b ∧ ExactOn o d b ∧
    ∀ (j : Nat) (b' : List N), o.branches[j]? = some b' → ExactOn o d b' → j = i

/-- **The build line** of IO-011 on its own: building a transition whose output spec names a place
twice in one output branch fails, and once the input-arc check passes it fails with IO-011's
message naming the place the walk reports (`firstDup`). -/
def IO_011_buildLine {N : Type} [DecidableEq N] [ToString N] (Build : Trans N → Option String) :
    Prop :=
  ∀ (t : Trans N) (o : Out N), OutputSpec t = some o → DupBranch o →
    Build t ≠ none ∧ (PreOutputChecks t → ∀ p, firstDup o = some p → Build t = some (msgDup t p))

/-! ## IO-011: Output And -/

requirement IO_011
  id "IO-011"
  title "Output And"
  kind B
  scope "executors with output validation enabled (the default, CONC-026)"
  source verbatim "spec/02-input-output-specs.md"
  quote "`And(children)` is a node of an output spec that represents a parallel fork in which all children are active."
        "*When* a transition whose output spec is `And(children)` fires and its action completes, every child, with nested `And`s flattened, *shall* have received tokens: the produced set contains a place that the child names."
        "The same holds for an `And` nested in the alternative that an inner `Xor` chose: the produced set *shall* equal, on the places the output spec names, one output branch of the output spec."
        "That output branch is unique, because the output branches of a spec that builds are pairwise distinct sets ([IO-012])."
        "This requirement applies to an executor with output validation enabled, which is the default ([CONC-026])."
        "*If* a single output branch (one choice at every `Xor`, with nested `And`s flattened) names the same place twice, *then* the output spec *shall* be rejected, with"
        "*If* the output spec names a place twice in one output branch, *then* `<P>` in the message *shall* be the place that the following walk of the spec reports first, so that every implementation names the same place:"
        "A `Place(P)` node and a `ForwardInput(from, P)` node name `P`."
        "A `Timeout` node walks its child and names the places its child names."
        "An `Xor` node walks its children left to right."
        "*If* a child reports a place, *then* the `Xor` *shall* report that place."
        "Otherwise the `Xor` names the places its children name, each once, in the order the walk first meets them."
        "An `And` node walks its children left to right."
        "*If* a child reports a place, *then* the `And` *shall* report that place."
        "Otherwise, *if* a place the child names, taken in the order the walk first met them, is already named by an earlier child, *then* the `And` *shall* report the first such place."
        "Otherwise the `And` names the places its children name, each once, in the order the walk first meets them."
        "The walk reports a place exactly when some output branch names a place twice, because the alternatives of an `Xor` under an `And` are chosen independently of the `And`'s other children."
  reading "Let Build be the builder (Build t = none: t builds; Build t = some msg: building t fails with msg) and F the firings."
          "For every transition t whose output spec o names a place twice in one output branch (DupBranch), building t fails; and if t's input places are distinct, it fails with IO-011's message for t and the place p the walk of o reports (firstDup o = some p, msgDup t p)."
          "For every transition t that builds (Builds) whose output spec is an And node o with no Timeout node in it:"
          "for every child c of o (nested Ands flattened) and every deposit d, every firing of t that deposits d produces some place that c names;"
          "for every deposit d, every firing of t that deposits d has as its produced set, on the places o names, exactly the places of the output branch at one index of o's branch list, and of no branch at any other index (IO_011_uniqueBranch)."
          "F is the firing relation of an executor with output validation enabled."
  assumes "The model is the pair (Build, F). Build is the transition builder, read as the message building a transition fails with, none when it builds; the witness is the reference builder refBuild, which runs the build-time checks of the Output Composition preamble in order (glossary: Build-time checks). The build error is msgDup, byte for byte: the message of the paragraph 'A place at most once per branch' with <t> the transition's name and <P> the place the walk reports. The preamble does not place the CORE-030 input-arc check among the output-spec checks; refBuild runs it first, so on a transition with two input arcs on one place the build line only requires that building fails."
          "The walk is firstDup, through dupScan, clause for clause: steps 1 and 2 are its place, forward and timeout clauses, step 3 its xor clause (xorJoin: the first child's report, else the second's, else the places of both, each once, in first-seen order), step 4 its and clause (andStep at each child: the child's report, else the first place the child names that an earlier child of the And names, else the child's places join the pool). The reference Out is binary: an n-ary And or Xor is right-nested, and dupScan walks a .and met as a child of a .and as part of its parent, so the children of And(c1, ..., cn) are walked as the n-ary node's children. A spec with an And written as a direct child of an And is the one shape the binary Out cannot tell from the flat n-ary node; on it the builders walk the inner And first, the loader's walk (Load.dupWalk, over the spec as written) does the same, and firstDup reads the flat node."
          "'The walk reports a place exactly when some output branch names a place twice' is the theorem firstDup_eq_none_iff, and the place it reports is named twice in some output branch (firstDup_some); the build line therefore names a place exactly when it rejects a duplicate. AC5's And(Xor(A, B), Xor(B, A)) names B (IO_011_ac5); naming the first place repeated in the first repeating output branch, in IO-016 order, would name A, and that builder violates the build line (IO_011_forbids_firstBranchName)."
          "'Which place the message names' is a constraint on the message only: which transitions build is the first build line together with the other build-time checks, and IO-013's third line ties Builds to the builder."
          "Ruling D15: the premise PreOutputChecks t (glossary) is the checks the reference builder runs before the output-spec checks: distinct input places ([CORE-030]), input arcs that each require at least one token ([IO-002], [IO-004]) and no input arc and read arc on one place ([EXEC-012]). A transition that fails one of them fails with that check's message, so on it the build lines only require that building fails, as for CORE-030 before the ruling."
           "A firing is read as one step from a marking to a marking that deposits the tokens of one outcome (glossary: Fire, Deposit); timing and priority play no part. A completion that fails validation (AC3) deposits no outcome and is not a firing here."
          "Scope: 'applies to an executor with output validation enabled' is read as a restriction on the model: F is the firing relation of such an executor. An executor with the CONC-026 skip enabled is not an F this block speaks of; what it does (an And(A, B) firing that deposits only A, CONC-026 AC4) is exactly what io011_leftOnlyFire models, and this block forbids it of a validating executor (IO_011_forbids_leftOnly)."
          "Scope: the statement quantifies over transitions that build. Building runs the checks of the Output Composition preamble (WellFormedOut: no place twice in one output branch, at most one Timeout node, no Xor node inside the Timeout child, no ForwardInput outside a Timeout child, every ForwardInput's from an input place, no two output branches at different indices with the same set of places). CORE-022 applies to transitions that build, and a definition the checks reject is not a transition of any net. Build reads one transition definition, so the construction paths that reach the builder are not encoded."
          "The reference semantics reads an n-ary And as right-nested binary `Out.and` nodes; `andChildren` flattens them back, so the children of And(A, B, C) are A, B and C. Flattening is the recursive reading of 'ALL child output specs must receive tokens': a nested And has received tokens exactly when each of its own children has."
          "'Received tokens' and 'the produced set' are read on the set of places the deposit touches (Produced, membership in d), and an output branch is read as a set of places (glossary: Output branch): several tokens into one place of the chosen branch conform, and the order of the deposit plays no part (CORE-036). How many tokens is IO-016's subject. Places outside the output spec are not constrained here (CORE-035 ties the marking to the deposit)."
          "'Fires and its action completes' is read on output specs with no Timeout node (findTimeout = none), where every firing ends with its action. An output spec with its one Timeout node anywhere in it, such as And(A, Timeout(d, B)), is IO-013's: the deposit alone cannot tell the timeout outcome from the action outcome, so this block does not restate it there."
          "The second clause is the recursive reading of 'ALL children receive tokens' below an Xor: an And under the Xor alternative the action chose must give every one of its children tokens, and the Xor itself must take one alternative (IO-012). Without it a deposit [0, 3] for And(Xor(And(0, 1), 2), 3) (a partial write of the chosen alternative) and a deposit [0, 1, 2] for And(0, Xor(1, 2)) (both alternatives) satisfy the first clause."
          "'That output branch is unique' is read by index: one entry of the IO-016 branch list, one per assignment. On a transition that builds it follows from the existence half and the last build check (IO_011_unique_of_wf), so it adds no constraint on F beyond the scope; no weaker mutant can tell it apart, and the evidence for it is that lemma and IO_011_reference_ambiguous, which shows that without the scope the reference fires And(Q, Xor(P, P)) with two exact branches."
          "AC1 (requires at least 1 child) is structural and not encoded: the reference output spec has binary And nodes only, so an And with no child cannot be written; an And with one child is that child."
          "AC2 (after the action completes, all children have received tokens) is the first clause, and the second at every depth."
          "AC3 (validation failure if a child received no tokens) is read on firings: a completion in which a child received no tokens is not a firing, so the marking never shows it. That the failure is reported (an ActionFailed outcome, the error the user sees) is not observable in the firing relation, which has no events or errors; it is EXEC-030's and IO-015's subject and is not encoded here."
          "AC4 and the paragraph 'A place at most once per branch' are the build line, and the first build check of WellFormedOut (every output branch Nodup, equivalently no BranchDuplicate, IO_011_noDuplicate_of_wf) for the firing lines' scope: And(P, P), And(P, And(Q, P)) and Xor(A, And(P, P)) are rejected with the message naming P, and Xor(And(P, A), And(P, B)) builds (IO_011_ac4). The construction paths and MOD-020's more specific message are not in the model. The reference semantics still fires And(P, P) depositing two tokens in P (IO_011_reference_fires_duplicate); that transition does not build, so the firing lines do not speak of it."
          "AC5 (And(Xor(A, B), Xor(B, A)) is rejected naming B) is the build line on that spec, checked under the reference builder (IO_011_ac5)."
  signoff "pending"
  statement : ∀ {N : Type} [DecidableEq N] [ToString N], (Trans N → Option String) → FireRel N →
      Prop :=
    fun {N} [DecidableEq N] [ToString N] Build F =>
      (∀ (t : Trans N) (o : Out N), OutputSpec t = some o → DupBranch o →
        Build t ≠ none ∧
        (PreOutputChecks t → ∀ p, firstDup o = some p → Build t = some (msgDup t p))) ∧
      ∀ (t : Trans N) (l r : Out N), OutputSpec t = some (.and l r) →
      Builds t → (Out.and l r).findTimeout = none →
      (∀ c ∈ andChildren (.and l r), ∀ d : List N,
        on (fun m m' => F t m d m'), shall (fun _ _ => ChildReceived d c)) ∧
      (∀ d : List N, on (fun m m' => F t m d m'),
        shall (fun _ _ => IO_011_uniqueBranch (.and l r) d))

/- The pinned readable form of IO-011: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_011 : {N : Type} →
  [DecidableEq N] → [ToString N] → (Reference.Trans N → Option String) → FireRel N → Prop :=
fun {N} [DecidableEq N] [ToString N] Build F =>
  (∀ (t : Reference.Trans N) (o : Out N),
      OutputSpec t = some o →
        DupBranch o →
          Build t ≠ none ∧ (PreOutputChecks t → ∀ (p : N), firstDup o = some p → Build t = some (msgDup t p))) ∧
    ∀ (t : Reference.Trans N) (l r : Out N),
      OutputSpec t = some (l.and r) →
        Builds t →
          (l.and r).findTimeout = none →
            (∀ c ∈ andChildren (l.and r),
                ∀ (d : List N), on fun m m' => F t m d m', shall fun x x_1 => ChildReceived d c) ∧
              ∀ (d : List N), on fun m m' => F t m d m', shall fun x x_1 => IO_011_uniqueBranch (l.and r) d
-/
#guard_msgs in #print IO_011

/-- Every output branch of `o` contains a place that `o` names. -/
theorem branch_meets_outPlaces {N : Type} :
    ∀ (o : Out N), ∀ b ∈ o.branches, ∃ p ∈ outPlaces o, p ∈ b
  | .place p, b, hb => by
    simp only [Out.branches, List.mem_singleton] at hb
    exact ⟨p, by simp [outPlaces], by simp [hb]⟩
  | .forward _ q, b, hb => by
    simp only [Out.branches, List.mem_singleton] at hb
    exact ⟨q, by simp [outPlaces], by simp [hb]⟩
  | .and l r, b, hb => by
    simp only [Out.branches, cross, List.mem_flatMap, List.mem_map] at hb
    obtain ⟨x, hx, y, -, rfl⟩ := hb
    obtain ⟨p, hp, hpx⟩ := branch_meets_outPlaces l x hx
    exact ⟨p, by simp [outPlaces, hp], List.mem_append_left _ hpx⟩
  | .xor l r, b, hb => by
    simp only [Out.branches, List.mem_append] at hb
    rcases hb with hb | hb
    · obtain ⟨p, hp, hpb⟩ := branch_meets_outPlaces l b hb
      exact ⟨p, by simp [outPlaces, hp], hpb⟩
    · obtain ⟨p, hp, hpb⟩ := branch_meets_outPlaces r b hb
      exact ⟨p, by simp [outPlaces, hp], hpb⟩
  | .timeout c, b, hb => by
    obtain ⟨p, hp, hpb⟩ := branch_meets_outPlaces c b hb
    exact ⟨p, by simpa [outPlaces] using hp, hpb⟩

/-- **Uniqueness follows from the build checks.** If no two output branches of `o` at different
indices claim the same set of places (the last check of `WellFormedOut`), then two indices whose
branches are both exact for a deposit `d` are the same index. -/
theorem IO_011_unique_of_wf {N : Type} (o : Out N)
    (hp : o.branches.Pairwise (fun b b' => ¬ SameSet b b')) {d : List N} {i j : Nat}
    {b b' : List N} (hi : o.branches[i]? = some b) (hj : o.branches[j]? = some b')
    (eb : ExactOn o d b) (eb' : ExactOn o d b') : j = i := by
  have hbm : b ∈ o.branches := List.mem_iff_getElem?.mpr ⟨i, hi⟩
  have hbm' : b' ∈ o.branches := List.mem_iff_getElem?.mpr ⟨j, hj⟩
  have hs : SameSet b b' := fun q =>
    ⟨fun hq => (eb' q (outPlaces_of_branch o b hbm q hq)).1
        ((eb q (outPlaces_of_branch o b hbm q hq)).2 hq),
     fun hq => (eb q (outPlaces_of_branch o b' hbm' q hq)).1
        ((eb' q (outPlaces_of_branch o b' hbm' q hq)).2 hq)⟩
  obtain ⟨hil, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  rw [List.pairwise_iff_getElem] at hp
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd hs (hp i j hil hjl h)
  · exact h.symm
  · exact absurd (fun q => (hs q).symm) (hp j i hjl hil h)

/-- The first build check is AC4's: a spec that passes it has no output branch naming a place
twice (`BranchDuplicate`). -/
theorem IO_011_noDuplicate_of_wf {N : Type} [DecidableEq N] {inputs : List N} {o : Out N}
    (h : WellFormedOut inputs o) (p : N) : ¬ BranchDuplicate o p := by
  rintro ⟨b, hb, hc⟩
  have hn : b.Nodup := by
    by_contra hn
    exact h.1 ⟨b, hb, hn⟩
  have := List.nodup_iff_count_le_one.mp hn p
  omega

/-- Every output branch of `o` gives every flattened `And` child of `o` a place it names. -/
theorem branch_receives_andChildren {N : Type} :
    ∀ (o : Out N), ∀ b ∈ o.branches, ∀ c ∈ andChildren o, ChildReceived b c
  | .and l r, b, hb, c, hc => by
    simp only [Out.branches, cross, List.mem_flatMap, List.mem_map] at hb
    obtain ⟨x, hx, y, hy, rfl⟩ := hb
    simp only [andChildren, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨p, hp, hpx⟩ := branch_receives_andChildren l x hx c hc
      exact ⟨p, hp, List.mem_append_left _ hpx⟩
    · obtain ⟨p, hp, hpy⟩ := branch_receives_andChildren r y hy c hc
      exact ⟨p, hp, List.mem_append_right _ hpy⟩
  | .place p, b, hb, c, hc => by
    simp only [andChildren, List.mem_singleton] at hc
    exact hc ▸ branch_meets_outPlaces _ b hb
  | .forward s q, b, hb, c, hc => by
    simp only [andChildren, List.mem_singleton] at hc
    exact hc ▸ branch_meets_outPlaces _ b hb
  | .xor l r, b, hb, c, hc => by
    simp only [andChildren, List.mem_singleton] at hc
    exact hc ▸ branch_meets_outPlaces _ b hb
  | .timeout k, b, hb, c, hc => by
    simp only [andChildren, List.mem_singleton] at hc
    exact hc ▸ branch_meets_outPlaces _ b hb

/-- The reference builder satisfies the build line: a spec naming a place twice in one output
branch fails the first output-spec check, whose message names the place the walk reports. -/
theorem IO_011_refBuild_names {N : Type} [DecidableEq N] [ToString N] :
    IO_011_buildLine (refBuild (N := N)) := by
  intro t o ho hd
  refine ⟨fun h => (((refBuild_eq_none_iff t).1 h).2 o ho).1 hd, fun hin p hp => ?_⟩
  simp only [OutputSpec] at ho
  rw [refBuild_of_pre hin]
  simp [ho, checkOut, hp]

/-- The reference semantics satisfies IO-011: the reference builder names the walk's place
(`IO_011_refBuild_names`), and with no Timeout node the only outcome a reference
firing can take is an action branch (`deposit` of a `timedOut` choice needs `findTimeout`), and
every action branch of an `And` is the concatenation of one branch per child
(`Out.branches`, `cross`), each of which contains a place its child names
(`branch_receives_andChildren`); the deposit is itself the branch at its index, so it is exact
for itself, and on a transition that builds no other index is (`IO_011_unique_of_wf`). -/
@[evidence holds IO_011]
theorem IO_011_reference {N : Type} [DecidableEq N] [ToString N] :
    IO_011 (refBuild (N := N)) (RefFire (N := N)) := by
  refine ⟨IO_011_refBuild_names, ?_⟩
  intro t l r ht hwf hto
  have key : ∀ d m m', RefFire t m d m' → ∃ i : Nat, (Out.and l r).branches[i]? = some d := by
    intro d m m' hf
    obtain ⟨-, ⟨ch, hch⟩, -⟩ := hf
    rw [show t.out = some (.and l r) from ht] at hch
    cases ch with
    | action i => exact ⟨i, hch⟩
    | timedOut j => simp [deposit, hto] at hch
  refine ⟨fun c hc d m m' hf => ?_, fun d m m' hf => ?_⟩
  · obtain ⟨i, hi⟩ := key d m m' hf
    exact branch_receives_andChildren _ d (List.mem_iff_getElem?.mpr ⟨i, hi⟩) c hc
  · obtain ⟨i, hi⟩ := key d m m' hf
    exact ⟨i, d, hi, fun _ _ => Iff.rfl, fun j b' hj eb' =>
      IO_011_unique_of_wf _ (hwf.2 _ ht).2.2.2.2.2 hi hj (fun _ _ => Iff.rfl) eb'⟩

/-! ### Examples -/

/-- A transition of the examples: no arcs in, output spec `And(Place(0), Place(1))`. -/
def io011_t : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 0) (.place 1)) }

/-- A transition of the examples: no arcs in, output spec `And(Place(0), And(Place(1),
Place(2)))`, the right-nested form of `And(Place(0), Place(1), Place(2))`. -/
def io011_nested : Trans Nat :=
  { core := { name := "n", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 0) (.and (.place 1) (.place 2))) }

/-- A transition of the examples whose one output branch names place `0` twice: `And(Place(0),
Place(0))`. It does not build. -/
def io011_dup : Trans Nat :=
  { core := { name := "d", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 0) (.place 0)) }

/-- The marking of the examples in which every place is empty. -/
def io011_empty : Nat → Nat := fun _ => 0

/-- The marking after `io011_t` fires from the empty marking: one token in places `0` and `1`. -/
def io011_after : Nat → Nat := fun n => if n = 0 ∨ n = 1 then 1 else 0

/-- The marking after `io011_dup` fires from the empty marking in the reference semantics: two
tokens in place `0`. -/
def io011_afterDup : Nat → Nat := fun n => if n = 0 then 2 else 0

/-- `io011_t` builds. -/
theorem io011_t_builds : Builds io011_t := by decide

/-- `io011_nested` builds. -/
theorem io011_nested_builds : Builds io011_nested := by decide

/-- `io011_dup` does not build: its one output branch names place `0` twice (AC4). -/
theorem io011_dup_not_builds : ¬ Builds io011_dup := by decide

/-- A firing relation that writes only the first child: `io011_t` fires without changing the
marking and deposits `[0]`; no other transition fires. It is what an executor with the
[CONC-026] skip enabled may do (CONC-026 AC4). -/
def io011_leftOnlyFire : FireRel Nat :=
  fun t m d m' => t = io011_t ∧ d = [0] ∧ m' = m

/-- A firing relation that writes only the first two leaves of the nested `And`: `io011_nested`
fires without changing the marking and deposits `[0, 1]`; no other transition fires. -/
def io011_shallowFire : FireRel Nat :=
  fun t m d m' => t = io011_nested ∧ d = [0, 1] ∧ m' = m

/-- ✗ Writing one child of an `And` only violates IO-011: `io011_t` deposits `[0]`, and its
child `Place(1)` receives no token. -/
@[evidence forbids IO_011]
theorem IO_011_forbids_leftOnly : ¬ IO_011 refBuild io011_leftOnlyFire := by
  intro h
  have := (h.2 io011_t (.place 0) (.place 1) rfl io011_t_builds rfl).1 (.place 1)
    (by simp [andChildren]) [0] io011_empty io011_empty ⟨rfl, rfl, rfl⟩
  obtain ⟨p, hp, hpd⟩ := this
  simp [outPlaces] at hp
  subst hp
  simp [Produced] at hpd

/-- ✗ Writing only part of a nested `And` violates IO-011: `io011_nested` deposits `[0, 1]`, and
its flattened child `Place(2)` receives no token. -/
@[evidence forbids IO_011]
theorem IO_011_forbids_shallow : ¬ IO_011 refBuild io011_shallowFire := by
  intro h
  have := (h.2 io011_nested (.place 0) (.and (.place 1) (.place 2)) rfl io011_nested_builds rfl).1
    (.place 2) (by simp [andChildren]) [0, 1] io011_empty io011_empty ⟨rfl, rfl, rfl⟩
  obtain ⟨p, hp, hpd⟩ := this
  simp [outPlaces] at hp
  subst hp
  simp [Produced] at hpd

/-- Mutant reading of IO-011 that weakens "every child" to "some child": an `And` firing must
write at least one of its children. -/
def IO_011_mutant_someChild {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (F : FireRel N) : Prop :=
  IO_011_buildLine Build ∧ ∀ (t : Trans N) (l r : Out N), OutputSpec t = some (.and l r) → Builds t →
    (Out.and l r).findTimeout = none → ∀ d : List N,
      on (fun m m' => F t m d m'), shall (fun _ _ => ∃ c ∈ andChildren (.and l r),
        ChildReceived d c)

/-- The left-only firing kills the "some child" mutant: its one firing writes `Place(0)`, a
child of `io011_t`, so the mutant holds; it does not write `Place(1)`, so IO-011 does not. -/
@[evidence mutant IO_011]
theorem IO_011_mutant_someChild_killed :
    IO_011_mutant_someChild refBuild io011_leftOnlyFire ∧ ¬ IO_011 refBuild io011_leftOnlyFire := by
  refine ⟨⟨IO_011_refBuild_names, ?_⟩, IO_011_forbids_leftOnly⟩
  rintro t l r ht - - d m m' ⟨rfl, rfl, -⟩
  have h2 : (some (Out.and (.place 0) (.place 1)) : Option (Out Nat)) = some (.and l r) := ht
  cases h2
  exact ⟨.place 0, by simp [andChildren], 0, by simp [outPlaces], by simp [Produced]⟩

/-- Mutant reading of IO-011 that does not flatten nested `And`s: only the two immediate
children of the top `And` node must receive tokens, so a nested `And` counts as received once
any of its places is written. -/
def IO_011_mutant_noFlatten {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (F : FireRel N) : Prop :=
  IO_011_buildLine Build ∧ ∀ (t : Trans N) (l r : Out N), OutputSpec t = some (.and l r) → Builds t →
    (Out.and l r).findTimeout = none → ∀ c ∈ [l, r], ∀ d : List N,
      on (fun m m' => F t m d m'), shall (fun _ _ => ChildReceived d c)

/-- The shallow firing kills the no-flatten mutant: its one firing writes `Place(0)` and place
`1` of `And(Place(1), Place(2))`, so both immediate children received tokens and the mutant
holds; the flattened child `Place(2)` received none, so IO-011 does not. -/
@[evidence mutant IO_011]
theorem IO_011_mutant_noFlatten_killed :
    IO_011_mutant_noFlatten refBuild io011_shallowFire ∧ ¬ IO_011 refBuild io011_shallowFire := by
  refine ⟨⟨IO_011_refBuild_names, ?_⟩, IO_011_forbids_shallow⟩
  rintro t l r ht - - c hc d m m' ⟨rfl, rfl, -⟩
  have h2 : (some (Out.and (.place 0) (.and (.place 1) (.place 2))) : Option (Out Nat)) =
      some (.and l r) := ht
  cases h2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨0, by simp [outPlaces], by simp [Produced]⟩
  · exact ⟨1, by simp [outPlaces], by simp [Produced]⟩

/-- IO-011 is exercised by the reference semantics: `io011_t` builds, has the output spec
`And(Place(0), Place(1))` with no Timeout node, fires from the empty marking depositing
`[0, 1]`, and each of its two children received a token (the conclusion is checked on a real
firing, not vacuously). -/
@[evidence nonvacuous IO_011]
theorem IO_011_nonvacuous :
    OutputSpec io011_t = some (.and (.place 0) (.place 1)) ∧ Builds io011_t ∧
      andChildren (Out.and (.place 0) (.place 1)) = [.place 0, .place 1] ∧
      RefFire io011_t io011_empty [0, 1] io011_after ∧
      ChildReceived [0, 1] (.place 0) ∧ ChildReceived [0, 1] (.place 1) := by
  refine ⟨rfl, io011_t_builds, rfl, ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩,
    ⟨0, by simp [outPlaces], by simp [Produced]⟩, ⟨1, by simp [outPlaces], by simp [Produced]⟩⟩
  funext n
  by_cases h0 : n = 0
  · subst h0; simp [fireNC, depProd, nconsumed, nspecAt, io011_t, io011_empty, io011_after]
  · by_cases h1 : n = 1
    · subst h1; simp [fireNC, depProd, nconsumed, nspecAt, io011_t, io011_empty, io011_after]
    · simp [fireNC, depProd, nconsumed, nspecAt, io011_t, io011_empty, io011_after, h0, h1, Ne.symm h0, Ne.symm h1]

/-! ### The build-time half: what the reference semantics does with a duplicate -/

/-- The reference semantics fires `And(Place(0), Place(0))`, an output spec whose one output
branch names place `0` twice, and the firing deposits two tokens in place `0`. The transition
does not build (`io011_dup_not_builds`), so the statement, which quantifies over transitions
that build, does not speak of this firing. Not tagged as evidence. -/
theorem IO_011_reference_fires_duplicate :
    OutputBranch io011_dup [0, 0] ∧ ¬ Builds io011_dup ∧
      RefFire io011_dup io011_empty [0, 0] io011_afterDup ∧ Deposits [0, 0] 0 = 2 := by
  refine ⟨by simp [OutputBranch, io011_dup, Out.branches, cross], io011_dup_not_builds,
    ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩, by decide⟩
  funext n
  by_cases h0 : n = 0
  · subst h0; simp [fireNC, depProd, nconsumed, nspecAt, io011_dup, io011_empty, io011_afterDup]
  · simp [fireNC, depProd, nconsumed, nspecAt, io011_dup, io011_empty, io011_afterDup, h0, Ne.symm h0]

/-! ### The second clause: partial or double writes below a nested `Xor` -/

/-- A transition of the examples: output spec `And(Xor(And(Place(0), Place(1)), Place(2)),
Place(3))`. -/
def io011_xorAnd : Trans Nat :=
  { core := { name := "x", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.xor (.and (.place 0) (.place 1)) (.place 2)) (.place 3)) }

/-- A transition of the examples: output spec `And(Place(0), Xor(Place(1), Place(2)))`. -/
def io011_andXor : Trans Nat :=
  { core := { name := "y", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 0) (.xor (.place 1) (.place 2))) }

/-- `io011_xorAnd` builds. -/
theorem io011_xorAnd_builds : Builds io011_xorAnd := by decide

/-- `io011_andXor` builds. -/
theorem io011_andXor_builds : Builds io011_andXor := by decide

/-- A firing relation that picks the alternative `And(Place(0), Place(1))` of the inner `Xor`
and writes only `Place(0)` of it: `io011_xorAnd` deposits `[0, 3]`; nothing else fires. -/
def io011_partialFire : FireRel Nat :=
  fun t m d m' => t = io011_xorAnd ∧ d = [0, 3] ∧ m' = m

/-- A firing relation that writes both alternatives of the inner `Xor`: `io011_andXor` deposits
`[0, 1, 2]`; nothing else fires. -/
def io011_bothArmsFire : FireRel Nat :=
  fun t m d m' => t = io011_andXor ∧ d = [0, 1, 2] ∧ m' = m

/-- ✗ A partial write of the `And` an inner `Xor` chose violates IO-011: `[0, 3]` matches no
output branch of `And(Xor(And(0, 1), 2), 3)` on its places (the branches are `[0, 1, 3]` and
`[2, 3]`). -/
@[evidence forbids IO_011]
theorem IO_011_forbids_partialXorAnd : ¬ IO_011 refBuild io011_partialFire := by
  intro h
  obtain ⟨i, b, hb, hiff, -⟩ := (h.2 io011_xorAnd _ _ rfl io011_xorAnd_builds rfl).2 [0, 3]
    io011_empty io011_empty ⟨rfl, rfl, rfl⟩
  have hb := List.mem_iff_getElem?.mpr ⟨i, hb⟩
  simp [Out.branches, cross] at hb
  rcases hb with rfl | rfl
  · have := (hiff 1 (by simp [outPlaces])).2 (by simp); simp [Produced] at this
  · have := (hiff 0 (by simp [outPlaces])).1 (by simp [Produced]); simp at this

/-- ✗ Writing both alternatives of an inner `Xor` violates IO-011: `[0, 1, 2]` matches neither
output branch `[0, 1]` nor `[0, 2]` of `And(0, Xor(1, 2))`. -/
@[evidence forbids IO_011]
theorem IO_011_forbids_bothArms : ¬ IO_011 refBuild io011_bothArmsFire := by
  intro h
  obtain ⟨i, b, hb, hiff, -⟩ := (h.2 io011_andXor _ _ rfl io011_andXor_builds rfl).2 [0, 1, 2]
    io011_empty io011_empty ⟨rfl, rfl, rfl⟩
  have hb := List.mem_iff_getElem?.mpr ⟨i, hb⟩
  simp [Out.branches, cross] at hb
  rcases hb with rfl | rfl
  · have := (hiff 2 (by simp [outPlaces])).1 (by simp [Produced]); simp at this
  · have := (hiff 1 (by simp [outPlaces])).1 (by simp [Produced]); simp at this

/-- Mutant reading of IO-011 with the first clause only: every flattened child received tokens,
but an `Xor` child counts as received once any place it names is written. -/
def IO_011_mutant_childrenOnly {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (F : FireRel N) : Prop :=
  IO_011_buildLine Build ∧ ∀ (t : Trans N) (l r : Out N), OutputSpec t = some (.and l r) → Builds t →
    (Out.and l r).findTimeout = none → ∀ c ∈ andChildren (.and l r), ∀ d : List N,
      on (fun m m' => F t m d m'), shall (fun _ _ => ChildReceived d c)

/-- The partial firing kills the children-only mutant: both flattened children of
`io011_xorAnd`, the `Xor` and `Place(3)`, received a token from `[0, 3]`, so the mutant holds;
IO-011's second clause does not. -/
@[evidence mutant IO_011]
theorem IO_011_mutant_childrenOnly_killed :
    IO_011_mutant_childrenOnly refBuild io011_partialFire ∧ ¬ IO_011 refBuild io011_partialFire := by
  refine ⟨⟨IO_011_refBuild_names, ?_⟩, IO_011_forbids_partialXorAnd⟩
  rintro t l r ht - - c hc d m m' ⟨rfl, rfl, -⟩
  have h2 : (some (Out.and (.xor (.and (.place 0) (.place 1)) (.place 2)) (.place 3)) :
      Option (Out Nat)) = some (.and l r) := ht
  cases h2
  simp only [andChildren, List.mem_append, List.mem_singleton] at hc
  rcases hc with rfl | rfl
  · exact ⟨0, by simp [outPlaces], by simp [Produced]⟩
  · exact ⟨3, by simp [outPlaces], by simp [Produced]⟩

/-- The second clause is exercised by the reference semantics: `io011_andXor` builds and fires
from the empty marking depositing `[0, 1]`, which is exact for its output branch at index 0,
`[0, 1]`, and for no other index. -/
@[evidence nonvacuous IO_011]
theorem IO_011_nonvacuous_xor :
    OutputSpec io011_andXor = some (.and (.place 0) (.xor (.place 1) (.place 2))) ∧
      Builds io011_andXor ∧
      RefFire io011_andXor io011_empty [0, 1] io011_after ∧
      IO_011_uniqueBranch (Out.and (.place 0) (.xor (.place 1) (.place 2))) [0, 1] := by
  refine ⟨rfl, io011_andXor_builds, ⟨by decide, ⟨.action 0, rfl⟩, ?_⟩,
    ⟨0, [0, 1], rfl, fun _ _ => Iff.rfl, fun j b' hj eb' =>
      IO_011_unique_of_wf _ (io011_andXor_builds.2 _ rfl).2.2.2.2.2 rfl hj (fun _ _ => Iff.rfl) eb'⟩⟩
  funext n
  by_cases h0 : n = 0
  · subst h0; simp [fireNC, depProd, nconsumed, nspecAt, io011_andXor, io011_empty, io011_after]
  · by_cases h1 : n = 1
    · subst h1; simp [fireNC, depProd, nconsumed, nspecAt, io011_andXor, io011_empty, io011_after]
    · simp [fireNC, depProd, nconsumed, nspecAt, io011_andXor, io011_empty, io011_after, h0, h1, Ne.symm h0, Ne.symm h1]

/-! ### The uniqueness sentence: why it needs the build scope -/

/-- A transition of the examples: output spec `And(Place(1), Xor(Place(0), Place(0)))`, the
`And(Q, Xor(P, P))` of [IO-012] AC5. It does not build: branches 0 and 1 both claim `{1, 0}`. -/
def io011_ambig : Trans Nat :=
  { core := { name := "a", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 1) (.xor (.place 0) (.place 0))) }

/-- Without the build scope the uniqueness sentence fails of the reference semantics: it fires
`io011_ambig` from the empty marking depositing `[1, 0]`, which is exact for the branches at
indices 0 and 1 alike. `io011_ambig` does not build, so IO-011 does not speak of it. Not tagged as
evidence. -/
theorem IO_011_reference_ambiguous :
    ¬ Builds io011_ambig ∧ (∃ m', RefFire io011_ambig io011_empty [1, 0] m') ∧
      ¬ IO_011_uniqueBranch (Out.and (.place 1) (.xor (.place 0) (.place 0))) [1, 0] := by
  refine ⟨by decide, ⟨_, by decide, ⟨.action 0, rfl⟩, rfl⟩, ?_⟩
  rintro ⟨i, b, hb, -, huniq⟩
  have h0 := huniq 0 [1, 0] rfl (fun _ _ => Iff.rfl)
  have h1 := huniq 1 [1, 0] rfl (fun _ _ => Iff.rfl)
  omega

/-! ### The build line: which place the message names -/

/-- AC5's spec `And(Xor(A, B), Xor(B, A))`, with `A = 0` and `B = 1`, on a transition named `w`. -/
def io011_cross : Trans Nat :=
  { core := { name := "w", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.xor (.place 0) (.place 1)) (.xor (.place 1) (.place 0))) }

/-- A transition named `w` with no arcs in and output spec `o`. -/
def io011_named (o : Out Nat) : Trans Nat :=
  { core := { name := "w", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some o }

set_option maxRecDepth 8000 in
/-- ✓ AC5: `And(Xor(A, B), Xor(B, A))` names a place twice in one output branch, and the
reference builder rejects it naming `B`: its second child's places, in the order the walk met
them, are `B, A`, and `B` is the first that its first child names. -/
theorem IO_011_ac5 :
    DupBranch (Out.and (.xor (.place 0) (.place 1)) (.xor (.place 1) (.place 0)) : Out Nat) ∧
      refBuild io011_cross = some (msgDup io011_cross 1) ∧
      msgDup io011_cross 1 = "output spec of transition 'w' names place '1' twice in one AND branch; outputs are sets (IO-015) — a weighted output is not supported, add a second place or a follow-up transition" :=
  ⟨by decide, rfl, by decide⟩

/-- ✓ AC4: `And(P, P)`, `And(P, And(Q, P))` and `Xor(A, And(P, P))`, with `P = 0`, `Q = 1`,
`A = 2`, are rejected with the message naming `P`; `Xor(And(P, A), And(P, B))` builds. -/
theorem IO_011_ac4 :
    refBuild (io011_named (.and (.place 0) (.place 0))) =
        some (msgDup (io011_named (.and (.place 0) (.place 0))) 0) ∧
      refBuild (io011_named (.and (.place 0) (.and (.place 1) (.place 0)))) =
        some (msgDup (io011_named (.and (.place 0) (.and (.place 1) (.place 0)))) 0) ∧
      refBuild (io011_named (.xor (.place 2) (.and (.place 0) (.place 0)))) =
        some (msgDup (io011_named (.xor (.place 2) (.and (.place 0) (.place 0)))) 0) ∧
      refBuild (io011_named (.xor (.and (.place 0) (.place 2)) (.and (.place 0) (.place 3)))) =
        none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The place the message names before the ruling: the first place repeated in the first output
branch, in [IO-016] order, that repeats one. -/
def io011_firstBranchDup (o : Out Nat) : Option Nat :=
  o.branches.findSome? fun b => b.find? fun p => decide (2 ≤ b.count p)

/-- A builder that names the first place repeated in the first repeating output branch, and
otherwise is the reference builder. -/
def io011_firstBranchBuild (t : Trans Nat) : Option String :=
  match t.out with
  | some o =>
    match io011_firstBranchDup o with
    | some p => some (msgDup t p)
    | none => refBuild t
  | none => refBuild t

/-- ✗ Naming the first place repeated in the first repeating output branch violates IO-011:
the branches of `And(Xor(A, B), Xor(B, A))` are `[A, B]`, `[A, A]`, `[B, B]`, `[B, A]`, so it
names `A`, not `B`. -/
@[evidence forbids IO_011]
theorem IO_011_forbids_firstBranchName : ¬ IO_011 io011_firstBranchBuild (RefFire (N := Nat)) := by
  intro h
  have := (h.1 io011_cross _ rfl (by decide)).2 (by decide) 1 rfl
  change some (msgDup io011_cross 0) = some (msgDup io011_cross 1) at this
  exact absurd this (by decide)

/-- Mutant reading of the build line: the message may name any place that some output branch
names twice, not the one the walk reports. -/
def IO_011_mutant_anyDupName {N : Type} [DecidableEq N] [ToString N]
    (Build : Trans N → Option String) (F : FireRel N) : Prop :=
  (∀ (t : Trans N) (o : Out N), OutputSpec t = some o → DupBranch o →
    Build t ≠ none ∧
    (PreOutputChecks t → ∃ p, BranchDuplicate o p ∧ Build t = some (msgDup t p))) ∧
  ∀ (t : Trans N) (l r : Out N), OutputSpec t = some (.and l r) → Builds t →
    (Out.and l r).findTimeout = none →
    (∀ c ∈ andChildren (.and l r), ∀ d : List N,
      on (fun m m' => F t m d m'), shall (fun _ _ => ChildReceived d c)) ∧
    (∀ d : List N, on (fun m m' => F t m d m'),
      shall (fun _ _ => IO_011_uniqueBranch (.and l r) d))

/-- The place `io011_firstBranchDup` returns is named twice in one output branch. -/
theorem io011_firstBranchDup_some {o : Out Nat} {p : Nat} (h : io011_firstBranchDup o = some p) :
    BranchDuplicate o p := by
  obtain ⟨b, hb, hf⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨b, hb, by simpa using List.find?_some hf⟩

/-- The first-branch builder kills the any-place mutant: every name it reports is a place named
twice in one output branch, and its firings are the reference's, so the mutant holds; on AC5's
spec it names `A`, not the walk's `B`, so IO-011 does not. -/
@[evidence mutant IO_011]
theorem IO_011_mutant_anyDupName_killed :
    IO_011_mutant_anyDupName io011_firstBranchBuild (RefFire (N := Nat)) ∧
      ¬ IO_011 io011_firstBranchBuild (RefFire (N := Nat)) := by
  refine ⟨⟨fun t o ho hd => ?_, IO_011_reference.2⟩, IO_011_forbids_firstBranchName⟩
  have ho' : t.out = some o := ho
  have href := IO_011_refBuild_names t o ho hd
  cases hf : io011_firstBranchDup o with
  | some p =>
    refine ⟨by simp [io011_firstBranchBuild, ho', hf], fun _ => ⟨p, io011_firstBranchDup_some hf, ?_⟩⟩
    simp [io011_firstBranchBuild, ho', hf]
  | none =>
    have hb : io011_firstBranchBuild t = refBuild t := by simp [io011_firstBranchBuild, ho', hf]
    rw [hb]
    refine ⟨href.1, fun hin => ?_⟩
    cases hp : firstDup o with
    | some p => exact ⟨p, firstDup_some hp, href.2 hin p hp⟩
    | none => exact absurd hd ((firstDup_eq_none_iff o).1 hp)

/-- The build line is exercised by the reference: AC5's spec names a place twice in one output
branch, the walk reports `B` (`1`), and the reference builder rejects the transition with the
message naming it. -/
@[evidence nonvacuous IO_011]
theorem IO_011_nonvacuous_name :
    OutputSpec io011_cross = some (.and (.xor (.place 0) (.place 1)) (.xor (.place 1) (.place 0))) ∧
      DupBranch (Out.and (.xor (.place 0) (.place 1)) (.xor (.place 1) (.place 0)) : Out Nat) ∧
      PreOutputChecks io011_cross ∧
      firstDup (Out.and (.xor (.place 0) (.place 1)) (.xor (.place 1) (.place 0)) : Out Nat) = some 1 ∧
      refBuild io011_cross = some (msgDup io011_cross 1) :=
  ⟨rfl, by decide, by decide, rfl, rfl⟩

/-! ### AC4's cases against the build checks -/

/-- AC4: `And(P, P)` names `P` twice in one branch, and does not build. -/
example : BranchDuplicate (Out.and (.place 0) (.place 0) : Out Nat) 0 ∧
    ¬ WellFormedOut [] (Out.and (.place 0) (.place 0) : Out Nat) :=
  ⟨⟨[0, 0], by simp [Out.branches, cross], by decide⟩, by decide⟩

/-- AC4: `And(P, And(Q, P))` names `P` twice in one branch, and does not build. -/
example : BranchDuplicate (Out.and (.place 0) (.and (.place 1) (.place 0)) : Out Nat) 0 ∧
    ¬ WellFormedOut [] (Out.and (.place 0) (.and (.place 1) (.place 0)) : Out Nat) :=
  ⟨⟨[0, 1, 0], by simp [Out.branches, cross], by decide⟩, by decide⟩

/-- AC4: `Xor(A, And(P, P))` names `P` twice in one branch, and does not build. -/
example : BranchDuplicate (Out.xor (.place 2) (.and (.place 0) (.place 0)) : Out Nat) 0 ∧
    ¬ WellFormedOut [] (Out.xor (.place 2) (.and (.place 0) (.place 0)) : Out Nat) :=
  ⟨⟨[0, 0], by simp [Out.branches, cross], by decide⟩, by decide⟩

/-- AC4: `Xor(And(P, A), And(P, B))` names no place twice in one branch, and builds. -/
example : (∀ p, ¬ BranchDuplicate
    (Out.xor (.and (.place 0) (.place 1)) (.and (.place 0) (.place 2)) : Out Nat) p) ∧
    WellFormedOut [] (Out.xor (.and (.place 0) (.place 1)) (.and (.place 0) (.place 2)) : Out Nat) :=
  ⟨IO_011_noDuplicate_of_wf (inputs := []) (by decide), by decide⟩

/-! ### The other build checks on the cases of [IO-012] AC5, [IO-013] AC7 and [IO-014] AC7 -/

/-- [IO-012] AC5: `Xor(P, P)`, `Xor(And(A, B), And(B, A))`, `Xor(A, Xor(A, B))`,
`Xor(And(A, Xor(B, C)), And(A, B))` and `Xor(P, Timeout(d, P))` do not build;
`Xor(And(A, B, C), And(A, B))`, `Xor(And(P, A), And(P, B))` and `Xor(A, Timeout(d, B))` do. -/
example :
    ¬ WellFormedOut [] (Out.xor (.place 0) (.place 0) : Out Nat) ∧
    ¬ WellFormedOut [] (Out.xor (.and (.place 0) (.place 1)) (.and (.place 1) (.place 0)) : Out Nat) ∧
    ¬ WellFormedOut [] (Out.xor (.place 0) (.xor (.place 0) (.place 1)) : Out Nat) ∧
    ¬ WellFormedOut [] (Out.xor (.and (.place 0) (.xor (.place 1) (.place 2)))
        (.and (.place 0) (.place 1)) : Out Nat) ∧
    ¬ WellFormedOut [] (Out.xor (.place 0) (.timeout (.place 0)) : Out Nat) ∧
    WellFormedOut [] (Out.xor (.and (.place 0) (.and (.place 1) (.place 2)))
        (.and (.place 0) (.place 1)) : Out Nat) ∧
    WellFormedOut [] (Out.xor (.and (.place 0) (.place 1)) (.and (.place 0) (.place 2)) : Out Nat) ∧
    WellFormedOut [] (Out.xor (.place 0) (.timeout (.place 1)) : Out Nat) := by
  decide

/-- [IO-013] AC7: `Timeout(d, Timeout(e, P))`, `Xor(Timeout(d, A), Timeout(e, B))` and
`And(Timeout(d, A), Xor(B, Timeout(e, C)))` do not build; `Timeout(d, And(A, B))` does. -/
example :
    ¬ WellFormedOut [] (Out.timeout (.timeout (.place 0)) : Out Nat) ∧
    ¬ WellFormedOut [] (Out.xor (.timeout (.place 0)) (.timeout (.place 1)) : Out Nat) ∧
    ¬ WellFormedOut [] (Out.and (.timeout (.place 0)) (.xor (.place 1) (.timeout (.place 2))) :
        Out Nat) ∧
    WellFormedOut [] (Out.timeout (.and (.place 0) (.place 1)) : Out Nat) := by
  decide

/-- [IO-014] AC7, with `a = 0` an input place: `ForwardInput(a, b)`, `Xor(c, ForwardInput(a, b))`
and `And(c, Xor(e, ForwardInput(a, b)))` do not build; `Timeout(d, ForwardInput(a, b))` and
`Xor(c, Timeout(d, And(e, ForwardInput(a, b))))` do. A forward from a place that is not an input
does not build ([IO-014] AC3). -/
example :
    ¬ WellFormedOut [0] (Out.forward 0 1 : Out Nat) ∧
    ¬ WellFormedOut [0] (Out.xor (.place 2) (.forward 0 1) : Out Nat) ∧
    ¬ WellFormedOut [0] (Out.and (.place 2) (.xor (.place 3) (.forward 0 1)) : Out Nat) ∧
    WellFormedOut [0] (Out.timeout (.forward 0 1) : Out Nat) ∧
    WellFormedOut [0] (Out.xor (.place 2) (.timeout (.and (.place 3) (.forward 0 1))) : Out Nat) ∧
    ¬ WellFormedOut [] (Out.timeout (.forward 0 1) : Out Nat) := by
  decide

end Libpetri.Spec
