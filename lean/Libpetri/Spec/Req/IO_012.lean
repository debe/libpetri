import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Spec.Text.IO_012

set_option linter.missingDocs true

/-!
# IO-012: Output Xor (`spec/02-input-output-specs.md`)

A predicate over three models, checked against the reference build check, builder and firing
relation, against models that break it, and against one mutant reading per clause and per scope
decision:

* `C : Out N → Option (Nat × Nat × List N)`, the **ambiguity check** run when a transition is
  built: `none` when the output spec passes it, `some (i, j, ps)` when it fails with the message
  naming the output branches `i` and `j` and the places `ps`;
* `Build : Trans N → Option String`, the **transition builder**: `none` when the transition
  builds, `some msg` when building fails with `msg`;
* `F : FireRel N`, the firing relation of an executor with output validation enabled
  ([CONC-026], the default).

The spec makes an ambiguous output spec a build-time error, so a transition that builds has
pairwise distinct output branches. The reference semantics then satisfies the block
(`IO_012_reference`), and the second firing line of the markdown (no two output branches equal
the produced set) is a consequence of the build check and the first line
(`IO_012_unique`), not a separate clause.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

variable {N : Type}

/-! ## Terms local to IO-012 -/

/-- **A clash** (local term): in the branch list `bs` (one entry per assignment, numbered from
0 as [IO-016] and [VER-001] number them), the entries at the indices `i < j` claim the same set
of places. Two different indices are two distinct assignments, so a clash is "two distinct
assignments claim the same set of places". -/
def IO_012_clash (bs : List (List N)) (i j : Nat) : Prop :=
  i < j ∧ ∃ bi bj, bs[i]? = some bi ∧ bs[j]? = some bj ∧ SameSet bi bj

/-- **Unambiguous** (local term): no two distinct assignments of the output spec `o` claim the
same set of places, at any depth. This is the output spec of a transition that passes the
[IO-012] build check: its output branches are pairwise distinct sets. -/
def IO_012_unambiguous (o : Out N) : Prop := ∀ i j, ¬ IO_012_clash o.branches i j

/-- **The reported clash** (local term, steps 3 and 4 of the check): `j` is the first index
whose branch claims the set of an earlier branch, `i` is the smallest index of such an earlier
branch, and `ps` is branch `i` as a list, its places in the order the spec as written names them
(`Out.branches` lists a branch's places leaf by leaf, left to right). -/
def IO_012_reported (o : Out N) (i j : Nat) (ps : List N) : Prop :=
  IO_012_clash o.branches i j ∧
    (∀ j' < j, ∀ i', ¬ IO_012_clash o.branches i' j') ∧
    (∀ i' < i, ¬ IO_012_clash o.branches i' j) ∧
    o.branches[i]? = some ps

/-- **May have ended with the timeout outcome** (local term, compared per place, CORE-036): the deposit
`d` of a firing of `t` from `m` puts in every place as many tokens as some timeout-outcome
deposit `d₀` of `t` from `m`. Such a firing is not constrained by IO-012. -/
def IO_012_timeoutLike [DecidableEq N] (t : Trans N) (m : N → Nat) (d : List N) : Prop :=
  ∃ d₀, TimeoutOutcome t (Consumes t m) d₀ ∧ SamePerPlace d d₀

/-! ## IO-012: Output Xor -/

requirement IO_012
  id "IO-012"
  title "Output Xor"
  kind B
  scope "build check: every transition, on every construction path; firing lines: executors with output validation enabled (the default, CONC-026)"
  source verbatim "spec/02-input-output-specs.md"
  covers IO_012.s1, IO_012.s2, IO_012.s3, IO_012.s4, IO_012.s5, IO_012.s6, IO_012.s7, IO_012.s8,
        IO_012.s9, IO_012.s10, IO_012.s11, IO_012.s12, IO_012.s13, IO_012.s14, IO_012.s15,
        IO_012.s16, IO_012.s17, IO_012.s18, IO_012.s19
  reading "Build check. For every output spec o (the output spec of the transition being built), with bs its output branches (Out.branches, one entry per assignment, numbered from 0):"
          "the check C passes (C o = none) exactly when no two entries of bs at indices i < j claim the same set of places (IO_012_unambiguous; IO_012_clash compares the entries as sets, SameSet);"
          "the check fails reporting (i, j, ps) (C o = some (i, j, ps)) exactly when the entries i < j clash, no entry before j clashes with an earlier one, no entry before i clashes with entry j, and ps is entry i as a list (IO_012_reported)."
          "Building. For every transition t whose output spec o is ambiguous (not IO_012_unambiguous): building t fails (Build t ≠ none); and when every earlier build-time check passes (the checks before the output spec, PreOutputChecks: input places distinct, CORE-030, every input arc requiring at least one token, IO-002/IO-004, and no input arc and read arc on one place, EXEC-012; no output branch naming a place twice, IO-011; at most one Timeout node and no Xor node inside its child, IO-013; no ForwardInput outside a Timeout child and every forward from an input place, IO-014), building fails with IO-012's message for the pair (i, j) and the places ps the check reports (msgAmbiguous t i j ps)."
          "Firing. For every transition t whose output spec is Xor(l, r) and passes the check, every deposit d, and every firing of t under F from m to m' that deposits d and whose deposit is not, place by place, a timeout-outcome deposit of t from m (IO_012_timeoutLike): some output branch b of Xor(l, r) is exact for d: on every place q the output spec names, d puts one or more tokens in q exactly when q is in b (ExactOn)."
          "The second firing line is a consequence, not a clause: on an output spec that passes the check two exact branches would be the same set (both lie within outPlaces), so at most one is exact (theorem IO_012_unique)."
          "`on R, shall Q` reads: every step from m to m' with R m m' satisfies Q m m'; here Q ignores both markings."
  assumes "A firing is read as one step from a marking to a marking that deposits the tokens of one outcome (glossary: Fire, Deposit); timing and priority play no part. A completion that fails, by an action exception (EXEC-030) or by IO-015 validation, deposits no outcome and is not a firing here: an action failure does not end the firing with its action."
          "F models an executor with output validation enabled, the default; an executor with the CONC-026 skip enabled is not constrained by the firing line (scope). The build check is independent of any executor: C is the check itself."
          "The check is modelled by what it reports, not by its text: C o = some (i, j, ps) stands for the message `output spec of transition '<t>' is ambiguous: output branches <i> and <j> both claim {<places>}; no write can tell them apart (IO-012)`, with <places> the names of ps joined by ', '. The transition name, the rendering of names, the message text, and the claim that it is byte-identical across implementations are not in the model; the cross-language tests of AC5 pin them."
          "The check C is stated for one output spec in isolation; the third line ties it to the builder. In the builder it runs last of the output-spec checks (the Output Composition preamble: IO-011, IO-013's two checks, IO-014 and IO-014 AC3 before it, and in an implementation with run-time token types, Java, IO-014's check that a ForwardInput's to place can hold the tokens of from), after the checks before the output spec (PreOutputChecks, ruling D15 below) and the TIME-001 timing check (glossary: Build-time checks), so a transition that an earlier check rejects reports that check's message instead: the third line asks for IO-012's message only when every earlier check passes, and otherwise only that building fails. Trans carries no timing interval and no token types, so the message part of the third line is claimed of transitions whose timing passes TIME-001's check and, in Java, whose every ForwardInput has a to place that can hold the tokens of its from place. The message is the glossary's msgAmbiguous, the text the markdown gives. That the check runs on every construction path (builders, composition, channel merge, fusion) and that no executor option skips it is read as: every transition in a net has an output spec C passes. The firing line is stated for such transitions; the model has no construction paths to enumerate."
          "'An implementation MAY decide the check without enumerating every branch' is the extensional reading: the block constrains C only by what it returns, so any algorithm that returns the same (i, j, ps) satisfies it. IO_012_check is one such algorithm, the enumeration of the numbered steps."
          "Place identity is equality on N, the implementation's own Place equality (names in TypeScript, Rust and Python, name and token type in Java; CORE-002, MOD-024). A ForwardInput(from, to) claims `to`, a Timeout its child's claim (Out.branches)."
          "Branches are numbered by the reference enumeration Out.branches over the right-nested binary Out: an n-ary Xor(c₁, …, cₙ) is xor c₁ (xor c₂ … cₙ) and concatenates its children's lists in child order; an n-ary And is the cartesian product with the first child varying slowest. These are IO-016's lists and VER-001's <t>_b<i> numbering, so the binary nesting changes no index."
          "'Receives tokens' is read as IO-015's exact explanation, as AC4 directs: a child whose output branch is a strict subset of the produced set has received tokens but is not satisfied. Read literally, `Xor(And(A, B, C), And(A, B))` writing {A, B} would have two children receiving tokens; under the exact reading only the second child's branch equals it."
          "The produced set is compared on the places the output spec names (outPlaces), as IO-015 compares on declared places: a token in a place the spec never names is CORE-072's business. A token in a named place outside the selected branch still breaks the firing line (IO-015 AC9). A branch fixes which places receive tokens, not how many (glossary: Output branch): several tokens into one place of the branch conform."
          "A firing ends with its action unless it is the timeout outcome (glossary: Timeout outcome, IO-013); the abstract firing relation does not label the outcome, so a firing whose deposit puts in every place as many tokens as some timeout-outcome deposit of t from the same marking is not checked (IO-012), whatever the order of its tokens. When the action happens to write such a deposit, that firing is not checked either. An Xor that contains a Timeout node is otherwise covered."
          "The firing line covers a transition whose whole output spec is an Xor. An Xor nested inside And or Timeout is covered by IO-015, which validates every Xor an assignment reaches. The build check covers every output spec, an Xor at any depth included: And(Q, Xor(P, P)) is rejected."
          "AC1 (at least two children) is structural: the binary xor node has the two children l and r, and an n-ary Xor nests as xor c₁ (xor c₂ … cₙ) (checked by example below); the reference loader rejects an xor with fewer than two children. In the runtimes the check sits in the Xor constructor (Java's Arc.Out.Xor record, the xor() factory of Rust and TypeScript, Python through Rust's xor()); Rust's public Out::Xor variant and a TypeScript object literal skip that constructor, so the transition builders of Rust and TypeScript run the check again, with the factory's message, after the timing check and before the output-spec checks, as they do the IO-002/IO-004 counts and TIME-001's timing (RD-54)."
          "AC2 (exactly one child received tokens) is the firing line (at least one exact branch, so one child of the top Xor) together with its consequence IO_012_unique (not two). An output branch takes exactly one child of the top Xor."
          "AC3 (zero branches satisfied → validation error) is the firing line: such a completion is not a firing. The test derivation's 'action produces to both' case is also the firing line under the exact reading: Xor(P1, P2) has no output branch {P1, P2}."
          "AC4 (two branches whose claims are the same set never reach a firing) is the build check: such a spec does not pass C, and the firing line is stated only for specs that pass. The strict-subset remark of AC4 is the exact reading above: Xor(And(A, B, C), And(A, B)) passes the check (checked by example below)."
          "AC5 (the rejected and accepted specs and their reported pairs and places) is checked by example on IO_012_check below, with the places A, B, C, P, Q, a named by the numbers 0, 1, 2, 3, 4, 5. The Timeout duration d is not in the reference Out. The composition case (two output ports in different alternatives bound to one host place) is the check applied to the composed spec; composition itself is MOD-024's model, not this block's."
          "The Test derivation's build cases are AC5's; its firing cases are AC3's."
          "Ruling D15: the premise PreOutputChecks t (glossary) is the checks the reference builder runs before the output-spec checks: distinct input places ([CORE-030]), input arcs that each require at least one token ([IO-002], [IO-004]) and no input arc and read arc on one place ([EXEC-012]). A transition that fails one of them fails with that check's message, so on it the build lines only require that building fails, as for CORE-030 before the ruling."
  signoff "2026-11-13 15c285956716e4b0 ai"
  statement : ∀ {N : Type} [DecidableEq N] [ToString N], (Out N → Option (Nat × Nat × List N)) →
      (Trans N → Option String) → FireRel N → Prop :=
    fun {N} [DecidableEq N] [ToString N] C Build F =>
      (∀ o : Out N, C o = none ↔ IO_012_unambiguous o) ∧
      (∀ (o : Out N) (i j : Nat) (ps : List N), C o = some (i, j, ps) ↔ IO_012_reported o i j ps) ∧
      (∀ (t : Trans N) (o : Out N), OutputSpec t = some o → ¬ IO_012_unambiguous o →
        Build t ≠ none ∧
        (PreOutputChecks t → ¬ DupBranch o → timeoutCount o ≤ 1 → xorInTimeout o = false →
          forwardOutside o = none →
          (∀ s ∈ forwardSources o, s ∈ inPlaces t) →
          ∀ i j ps, C o = some (i, j, ps) → Build t = some (msgAmbiguous t i j ps))) ∧
      (∀ (t : Trans N) (l r : Out N), OutputSpec t = some (.xor l r) →
        IO_012_unambiguous (.xor l r) → ∀ d : List N,
          on (fun m m' => F t m d m' ∧ ¬ IO_012_timeoutLike t m d),
            shall (fun _ _ => ∃ b ∈ (Out.xor l r).branches, ExactOn (.xor l r) d b))

/- The pinned readable form of IO-012: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.IO_012 : {N : Type} →
  [DecidableEq N] →
    [ToString N] → (Out N → Option (ℕ × ℕ × List N)) → (Reference.Trans N → Option String) → FireRel N → Prop :=
fun {N} [DecidableEq N] [ToString N] C Build F =>
  (∀ (o : Out N), C o = none ↔ IO_012_unambiguous o) ∧
    (∀ (o : Out N) (i j : ℕ) (ps : List N), C o = some (i, j, ps) ↔ IO_012_reported o i j ps) ∧
      (∀ (t : Reference.Trans N) (o : Out N),
          OutputSpec t = some o →
            ¬IO_012_unambiguous o →
              Build t ≠ none ∧
                (PreOutputChecks t →
                  ¬DupBranch o →
                    timeoutCount o ≤ 1 →
                      xorInTimeout o = false →
                        forwardOutside o = none →
                          (∀ s ∈ forwardSources o, s ∈ inPlaces t) →
                            ∀ (i j : ℕ) (ps : List N),
                              C o = some (i, j, ps) → Build t = some (msgAmbiguous t i j ps))) ∧
        ∀ (t : Reference.Trans N) (l r : Out N),
          OutputSpec t = some (l.xor r) →
            IO_012_unambiguous (l.xor r) →
              ∀ (d : List N),
                on fun m m' => F t m d m' ∧ ¬IO_012_timeoutLike t m d, shall fun x x_1 =>
                  ∃ b ∈ (l.xor r).branches, ExactOn (l.xor r) d b
-/
#guard_msgs in #print IO_012

/-- The third line of IO-012 on its own (the builder rejects an ambiguous output spec, with
IO-012's message once the earlier checks pass), for the mutants below. -/
def IO_012_buildLine [DecidableEq N] [ToString N] (C : Out N → Option (Nat × Nat × List N))
    (Build : Trans N → Option String) : Prop :=
  ∀ (t : Trans N) (o : Out N), OutputSpec t = some o → ¬ IO_012_unambiguous o →
    Build t ≠ none ∧
    (PreOutputChecks t → ¬ DupBranch o → timeoutCount o ≤ 1 → xorInTimeout o = false →
          forwardOutside o = none →
      (∀ s ∈ forwardSources o, s ∈ inPlaces t) →
      ∀ i j ps, C o = some (i, j, ps) → Build t = some (msgAmbiguous t i j ps))

/-! ## The reference ambiguity check

`IO_012_check` is the check as the numbered steps run it: enumerate the output branches
(`Out.branches`), visit them in index order, and report the first later branch whose set equals
an earlier one's. It is generic in the comparison (`IO_012_scan r`), so that the list-equality
mutant below is the same algorithm with another `r`. -/

/-- Step 3 for the pair of indices `i` (earlier) and `j` (later), comparing the branches with
`r`: the report `(i, j, bs[i])` when both exist and `r` relates them. -/
def IO_012_pairAt (r : List N → List N → Bool) (bs : List (List N)) (j i : Nat) :
    Option (Nat × Nat × List N) :=
  match bs[i]?, bs[j]? with
  | some bi, some bj => if r bi bj then some (i, j, bi) else none
  | _, _ => none

/-- Steps 3 and 4 over the branch list `bs`, comparing branches with `r`: visit `j = 0, 1, …` and,
for each, `i = 0, …, j - 1`; report the first pair `r` relates. -/
def IO_012_scan (r : List N → List N → Bool) (bs : List (List N)) :
    Option (Nat × Nat × List N) :=
  (List.range bs.length).findSome? fun j => (List.range j).findSome? (IO_012_pairAt r bs j)

/-- A clash under the comparison `r`: the entries `i < j` of `bs` exist and `r` relates them. -/
def IO_012_clashBy (r : List N → List N → Bool) (bs : List (List N)) (i j : Nat) : Prop :=
  i < j ∧ ∃ bi bj, bs[i]? = some bi ∧ bs[j]? = some bj ∧ r bi bj = true

/-- `findSome?` over `List.range n` returns the value at the first index where `f` is `some`. -/
theorem IO_012_findSome_range {α : Type} (f : Nat → Option α) (n : Nat) (a : α) :
    (List.range n).findSome? f = some a ↔ ∃ k < n, f k = some a ∧ ∀ k' < k, f k' = none := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.findSome?_append]
    cases h : (List.range n).findSome? f with
    | none =>
      have hn : ∀ k < n, f k = none := fun k hk =>
        List.findSome?_eq_none_iff.1 h k (List.mem_range.2 hk)
      simp only [Option.none_or, List.findSome?_singleton]
      constructor
      · intro hfa
        refine ⟨n, by omega, ?_, hn⟩
        cases hfn : f n <;> simp_all
      · rintro ⟨k, hk, hfk, -⟩
        by_cases hkn : k < n
        · rw [hn k hkn] at hfk; cases hfk
        · have : k = n := by omega
          subst this; simp [hfk]
    | some b =>
      obtain ⟨k₀, hk₀, hfk₀, hpre₀⟩ := (ih b).1 h
      simp only [Option.some_or, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨k₀, by omega, hfk₀, hpre₀⟩
      · rintro ⟨k, hk, hfk, hpre⟩
        rcases Nat.lt_trichotomy k k₀ with hlt | heq | hgt
        · rw [hpre₀ k hlt] at hfk; cases hfk
        · subst heq; rw [hfk₀] at hfk; exact Option.some.inj hfk
        · rw [hpre k₀ hgt] at hfk₀; cases hfk₀

/-- When the pair test reports. -/
theorem IO_012_pairAt_eq_some (r : List N → List N → Bool) (bs : List (List N)) (j i : Nat)
    (x : Nat × Nat × List N) :
    IO_012_pairAt r bs j i = some x ↔
      ∃ bi bj, bs[i]? = some bi ∧ bs[j]? = some bj ∧ r bi bj = true ∧ x = (i, j, bi) := by
  unfold IO_012_pairAt
  cases hi : bs[i]? with
  | none => simp
  | some bi =>
    cases hj : bs[j]? with
    | none => simp
    | some bj =>
      by_cases hr : r bi bj
      · simp only [hr, if_true, Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨bi, bj, rfl, rfl, hr, rfl⟩
        · rintro ⟨_, _, h1, h2, -, rfl⟩; cases h1; rfl
      · simp only [hr]; simp
        intro h; exact absurd h hr

/-- When the pair test passes. -/
theorem IO_012_pairAt_eq_none (r : List N → List N → Bool) (bs : List (List N)) (j i : Nat) :
    IO_012_pairAt r bs j i = none ↔
      ¬ ∃ bi bj, bs[i]? = some bi ∧ bs[j]? = some bj ∧ r bi bj = true := by
  unfold IO_012_pairAt
  cases hi : bs[i]? with
  | none => simp
  | some bi =>
    cases hj : bs[j]? with
    | none => simp
    | some bj => by_cases hr : r bi bj <;> simp [hr]

/-- The inner scan for `j` passes exactly when no earlier entry clashes with entry `j`. -/
theorem IO_012_inner_none (r : List N → List N → Bool) (bs : List (List N)) (j : Nat) :
    (List.range j).findSome? (IO_012_pairAt r bs j) = none ↔
      ∀ i, ¬ IO_012_clashBy r bs i j := by
  rw [List.findSome?_eq_none_iff]
  simp only [List.mem_range, IO_012_pairAt_eq_none, IO_012_clashBy, not_and]

/-- The inner scan for `j₀` reports `(i, j, ps)` exactly when `j₀ = j`, `i` is the smallest index
clashing with `j`, and `ps` is entry `i`. -/
theorem IO_012_inner_some (r : List N → List N → Bool) (bs : List (List N)) (j₀ i j : Nat)
    (ps : List N) :
    (List.range j₀).findSome? (IO_012_pairAt r bs j₀) = some (i, j, ps) ↔
      j₀ = j ∧ IO_012_clashBy r bs i j ∧ (∀ i' < i, ¬ IO_012_clashBy r bs i' j) ∧
        bs[i]? = some ps := by
  rw [IO_012_findSome_range]
  constructor
  · rintro ⟨k, hk, hks, hpre⟩
    obtain ⟨bi, bj, hbi, hbj, hr, he⟩ := (IO_012_pairAt_eq_some r bs j₀ k _).1 hks
    simp only [Prod.mk.injEq] at he
    obtain ⟨hik, hjj, hps⟩ := he
    subst hik hjj hps
    exact ⟨rfl, ⟨hk, _, _, hbi, hbj, hr⟩,
      fun i' hi' hc => (IO_012_pairAt_eq_none r bs _ i').1 (hpre i' hi') hc.2, hbi⟩
  · rintro ⟨rfl, ⟨hij, bi, bj, hbi, hbj, hr⟩, hpre, hps⟩
    refine ⟨i, hij, (IO_012_pairAt_eq_some r bs _ i _).2 ⟨bi, bj, hbi, hbj, hr, ?_⟩,
      fun i' hi' => (IO_012_pairAt_eq_none r bs _ i').2 fun hc => hpre i' hi' ⟨by omega, hc⟩⟩
    rw [hbi] at hps; cases hps; rfl

/-- The scan passes exactly when no two entries clash. -/
theorem IO_012_scan_none (r : List N → List N → Bool) (bs : List (List N)) :
    IO_012_scan r bs = none ↔ ∀ i j, ¬ IO_012_clashBy r bs i j := by
  unfold IO_012_scan
  rw [List.findSome?_eq_none_iff]
  simp only [List.mem_range, IO_012_inner_none]
  constructor
  · intro h i j hc
    have ⟨_, _, _, _, hbj, _⟩ := hc
    exact h j (List.getElem?_eq_some_iff.1 hbj).1 i hc
  · intro h j _ i; exact h i j

/-- The scan reports `(i, j, ps)` exactly when `j` is the first index clashing with an earlier
one, `i` the smallest index clashing with `j`, and `ps` entry `i`. -/
theorem IO_012_scan_some (r : List N → List N → Bool) (bs : List (List N)) (i j : Nat)
    (ps : List N) :
    IO_012_scan r bs = some (i, j, ps) ↔
      IO_012_clashBy r bs i j ∧ (∀ j' < j, ∀ i', ¬ IO_012_clashBy r bs i' j') ∧
        (∀ i' < i, ¬ IO_012_clashBy r bs i' j) ∧ bs[i]? = some ps := by
  unfold IO_012_scan
  rw [IO_012_findSome_range]
  simp only [IO_012_inner_some, IO_012_inner_none]
  constructor
  · rintro ⟨j₀, -, ⟨rfl, hc, hpre, hps⟩, hearly⟩
    exact ⟨hc, hearly, hpre, hps⟩
  · rintro ⟨hc, hearly, hpre, hps⟩
    have ⟨_, _, _, _, hbj, _⟩ := hc
    exact ⟨j, (List.getElem?_eq_some_iff.1 hbj).1, ⟨rfl, hc, hpre, hps⟩, hearly⟩


/-- **The reference ambiguity check** of IO-012: steps 1 to 4 run on the output spec `o`, branches
compared as sets. -/
def IO_012_check [DecidableEq N] (o : Out N) : Option (Nat × Nat × List N) :=
  IO_012_scan sameSetB o.branches

/- The reference ambiguity check is the witness build check of IO-012's `holds` theorem. -/
#spec_witness IO_012_check

/-- Under the set comparison, a clash of the scan is a clash of the statement. -/
theorem IO_012_clashBy_sameSet [DecidableEq N] (bs : List (List N)) (i j : Nat) :
    IO_012_clashBy sameSetB bs i j ↔ IO_012_clash bs i j := by
  simp only [IO_012_clashBy, IO_012_clash, sameSetB_iff]

/-- The reference check passes exactly the unambiguous output specs. -/
theorem IO_012_check_none [DecidableEq N] (o : Out N) :
    IO_012_check o = none ↔ IO_012_unambiguous o := by
  simp only [IO_012_check, IO_012_scan_none, IO_012_clashBy_sameSet, IO_012_unambiguous]

/-- The reference check reports exactly the clash IO-012 names. -/
theorem IO_012_check_some [DecidableEq N] (o : Out N) (i j : Nat) (ps : List N) :
    IO_012_check o = some (i, j, ps) ↔ IO_012_reported o i j ps := by
  simp only [IO_012_check, IO_012_scan_some, IO_012_clashBy_sameSet, IO_012_reported]

/-! ### The reference builder runs the check

The glossary's reference builder (`refBuild`) runs IO-012's check last, through `firstClash`
on the branch list. The two lemmas below show that `firstClash` reports the pair
`IO_012_check` reports, so the builder fails with IO-012's message for that pair. -/

/-- `find?` over `List.range n` returns the first index where `p` holds. -/
theorem io012_find_range (p : Nat → Bool) (n i : Nat) :
    (List.range n).find? p = some i ↔ i < n ∧ p i = true ∧ ∀ k < i, p k = false := by
  rw [List.find?_eq_findSome?_guard, IO_012_findSome_range]
  constructor
  · rintro ⟨k, hk, hg, hpre⟩
    simp only [Option.guard] at hg
    split at hg
    · rename_i hpk
      cases hg
      refine ⟨hk, hpk, fun k' hk' => ?_⟩
      have := hpre k' hk'
      simp only [Option.guard] at this
      split at this
      · cases this
      · rename_i h; simpa using h
    · cases hg
  · rintro ⟨hi, hpi, hpre⟩
    refine ⟨i, hi, by simp [Option.guard, hpi], fun k hk => ?_⟩
    simp [Option.guard, hpre k hk]

/-- The branches at `a < b` clash exactly when `firstClash`'s test relates them. -/
theorem io012_sameSetB_getD [DecidableEq N] (bs : List (List N)) (a b : Nat) (hab : a < b)
    (hb : b < bs.length) :
    sameSetB (bs.getD a []) (bs.getD b []) = true ↔ IO_012_clash bs a b := by
  have ha : a < bs.length := by omega
  simp only [IO_012_clash, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha,
    List.getElem?_eq_getElem hb, Option.getD_some, sameSetB_iff]
  constructor
  · intro hs; exact ⟨hab, _, _, rfl, rfl, hs⟩
  · rintro ⟨-, bi, bj, h1, h2, hs⟩
    obtain rfl := Option.some.inj h1
    obtain rfl := Option.some.inj h2
    exact hs

/-- When the check reports `(i, j, ps)`, `firstClash` reports `(i, j)` and branch `i` is `ps`. -/
theorem io012_firstClash_of_check [DecidableEq N] (o : Out N) (i j : Nat) (ps : List N)
    (h : IO_012_check o = some (i, j, ps)) :
    firstClash o.branches = some (i, j) ∧ o.branches.getD i [] = ps := by
  obtain ⟨hc, hearly, hpre, hps⟩ := (IO_012_check_some o i j ps).1 h
  have hj : j < o.branches.length := by
    obtain ⟨-, _, _, -, hbj, -⟩ := hc
    exact (List.getElem?_eq_some_iff.1 hbj).1
  refine ⟨?_, by simp [List.getD_eq_getElem?_getD, hps]⟩
  unfold firstClash
  rw [IO_012_findSome_range]
  refine ⟨j, hj, ?_, fun k hk => ?_⟩
  · rw [Option.map_eq_some_iff]
    refine ⟨i, (io012_find_range _ j i).2 ⟨hc.1, (io012_sameSetB_getD _ i j hc.1 hj).2 hc,
      fun k hk => ?_⟩, rfl⟩
    cases hb : sameSetB (o.branches.getD k []) (o.branches.getD j []) with
    | false => rfl
    | true =>
      have hij := hc.1
      exact absurd ((io012_sameSetB_getD _ k j (by omega) hj).1 hb) (hpre k hk)
  · rw [Option.map_eq_none_iff, List.find?_eq_none]
    intro x hx hb
    have hx' := List.mem_range.1 hx
    exact hearly k hk x ((io012_sameSetB_getD _ x k hx' (by omega)).1 hb)

/-- The reference builder satisfies IO-012's build line: an ambiguous output spec does not build,
and when every earlier check passes the builder fails with IO-012's message for the pair the
check reports. -/
theorem IO_012_refBuild_rejects [DecidableEq N] [ToString N] (t : Trans N) (o : Out N)
    (ho : OutputSpec t = some o) (hu : ¬ IO_012_unambiguous o) :
    refBuild t ≠ none ∧
      (PreOutputChecks t → ¬ DupBranch o → timeoutCount o ≤ 1 → xorInTimeout o = false →
          forwardOutside o = none →
        (∀ s ∈ forwardSources o, s ∈ inPlaces t) →
        ∀ i j ps, IO_012_check o = some (i, j, ps) → refBuild t = some (msgAmbiguous t i j ps)) := by
  have ho' : t.out = some o := ho
  refine ⟨fun h => hu ?_, fun hin hd hc hxt hf hs i j ps hck => ?_⟩
  · have hw := ((refBuild_eq_none_iff t).1 h).2 o ho
    rintro i j ⟨hij, bi, bj, hbi, hbj, hss⟩
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hbi
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hbj
    exact List.pairwise_iff_getElem.1 hw.2.2.2.2.2 i j hi hj hij hss
  · obtain ⟨hfc, hps⟩ := io012_firstClash_of_check o i j ps hck
    have hfind : (forwardSources o).find? (fun s => decide (s ∉ inPlaces t)) = none := by
      rw [List.find?_eq_none]; intro s hm; simpa using hs s hm
    have hc2 : ¬ 2 ≤ timeoutCount o := by omega
    rw [refBuild_of_pre hin]
    simp only [ho', checkOut,
      (firstDup_eq_none_iff o).2 hd, hc2, hxt, Bool.false_eq_true, hf, hfind, hfc, hps, if_false]

/-! ### AC5: the reported pairs and places

Places by number: `A` = 0, `B` = 1, `C` = 2, `P` = 3, `Q` = 4, `a` = 5. -/

/-- `Xor(P, P)` is rejected: branches 0 and 1 claim `{P}`. -/
example : IO_012_check (Out.xor (.place 3) (.place 3)) = some (0, 1, [3]) := by decide

/-- `Xor(And(A, B), And(B, A))` is rejected: branches 0 and 1 claim `{A, B}`. -/
example : IO_012_check (Out.xor (.and (.place 0) (.place 1)) (.and (.place 1) (.place 0))) =
    some (0, 1, [0, 1]) := by decide

/-- `Xor(A, Xor(A, B))` is rejected: branches 0 and 1 claim `{A}`. -/
example : IO_012_check (Out.xor (.place 0) (.xor (.place 0) (.place 1))) = some (0, 1, [0]) := by
  decide

/-- `And(Q, Xor(P, P))` is rejected: branches 0 and 1 claim `{Q, P}`, in spec order. -/
example : IO_012_check (Out.and (.place 4) (.xor (.place 3) (.place 3))) = some (0, 1, [4, 3]) := by
  decide

/-- `Xor(And(A, Xor(B, C)), And(A, B))` is rejected: branches 0 and 2 claim `{A, B}`. -/
example : IO_012_check
    (Out.xor (.and (.place 0) (.xor (.place 1) (.place 2))) (.and (.place 0) (.place 1))) =
    some (0, 2, [0, 1]) := by decide

/-- `Xor(P, Timeout(d, P))` is rejected: branches 0 and 1 claim `{P}`. -/
example : IO_012_check (Out.xor (.place 3) (.timeout (.place 3))) = some (0, 1, [3]) := by decide

/-- `Xor(B, Timeout(d, ForwardInput(a, B)))` is rejected: branches 0 and 1 claim `{B}`. -/
example : IO_012_check (Out.xor (.place 1) (.timeout (.forward 5 1))) = some (0, 1, [1]) := by
  decide

/-- `Xor(And(A, B, C), And(A, B))` builds: a strict subset is not the same set. -/
example : IO_012_check
    (Out.xor (.and (.place 0) (.and (.place 1) (.place 2))) (.and (.place 0) (.place 1))) =
    none := by decide

/-- `Xor(And(P, A), And(P, B))` builds. -/
example : IO_012_check (Out.xor (.and (.place 3) (.place 0)) (.and (.place 3) (.place 1))) =
    none := by decide

/-- `Xor(A, Timeout(d, B))` builds. -/
example : IO_012_check (Out.xor (.place 0) (.timeout (.place 1))) = none := by decide

/-- Step 3 visits `j` first: in `Xor(P, Xor(Q, Xor(Q, P)))` (branches `{P}`, `{Q}`, `{Q}`, `{P}`)
the report is branches 1 and 2, not 0 and 3. -/
example : IO_012_check (Out.xor (.place 3) (.xor (.place 4) (.xor (.place 4) (.place 3)))) =
    some (1, 2, [4]) := by decide

/-! ### The firing line, and its consequence -/

/-- The reference semantics satisfies the firing line of IO-012: a firing either deposits one
output branch of the spec, which is exact for itself, or is a timeout outcome, and then its deposit
is, place by place, a timeout-outcome deposit. -/
theorem IO_012_reference_someBranch [DecidableEq N] (t : Trans N) (l r : Out N)
    (ht : OutputSpec t = some (.xor l r)) (d : List N) :
    on (fun m m' => RefFire t m d m' ∧ ¬ IO_012_timeoutLike t m d),
      shall (fun _ _ => ∃ b ∈ (Out.xor l r).branches, ExactOn (.xor l r) d b) := by
  rintro m m' ⟨⟨-, ⟨ch, hch⟩, -⟩, hto⟩
  have ht' : t.out = some (.xor l r) := ht
  rw [ht'] at hch
  cases ch with
  | action i => exact ⟨d, List.mem_of_getElem? hch, fun _ _ => Iff.rfl⟩
  | timedOut j =>
    exfalso
    simp only [deposit, Option.bind_eq_some_iff] at hch
    obtain ⟨c, hc, hd⟩ := hch
    exact hto ⟨d, ⟨_, c, ht', hc, List.mem_of_getElem? hd⟩, fun _ => rfl⟩

/-- ✓ IO-012 holds of the reference: the reference check (`IO_012_check`) reports exactly what
the block names, the reference builder (`refBuild`) rejects every ambiguous output spec with
IO-012's message once the earlier checks pass, and the reference firings satisfy the firing
line. -/
@[evidence holds IO_012]
theorem IO_012_reference [DecidableEq N] [ToString N] :
    IO_012 (N := N) IO_012_check refBuild RefFire :=
  ⟨IO_012_check_none, IO_012_check_some, IO_012_refBuild_rejects,
    fun t l r ht _ d => IO_012_reference_someBranch t l r ht d⟩

/-- Every place of an output branch is a place the output spec names. -/
theorem IO_012_branch_sub : ∀ (o : Out N), ∀ b ∈ o.branches, ∀ q ∈ b, q ∈ outPlaces o
  | .place p, b, hb, q, hq => by
    simp only [Out.branches, List.mem_singleton] at hb; subst hb; simpa [outPlaces] using hq
  | .forward _ dst, b, hb, q, hq => by
    simp only [Out.branches, List.mem_singleton] at hb; subst hb; simpa [outPlaces] using hq
  | .and l r, b, hb, q, hq => by
    simp only [Out.branches, cross, List.mem_flatMap, List.mem_map] at hb
    obtain ⟨x, hx, y, hy, rfl⟩ := hb
    simp only [outPlaces, List.mem_append] at hq ⊢
    exact hq.imp (IO_012_branch_sub l x hx q) (IO_012_branch_sub r y hy q)
  | .xor l r, b, hb, q, hq => by
    simp only [Out.branches, List.mem_append] at hb
    simp only [outPlaces, List.mem_append]
    exact hb.imp (fun h => IO_012_branch_sub l b h q hq) (fun h => IO_012_branch_sub r b h q hq)
  | .timeout c, b, hb, q, hq => IO_012_branch_sub c b hb q hq

/-- **The second firing line, as a consequence.** On an output spec that passes the check, no two
output branches at different positions are both exact for any deposit: both would lie within the
places the spec names and agree with the produced set there, so they would be the same set. -/
theorem IO_012_unique [DecidableEq N] (o : Out N) (hu : IO_012_unambiguous o) (d : List N) :
    o.branches.Pairwise (fun b b' => ¬ (ExactOn o d b ∧ ExactOn o d b')) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij ⟨h1, h2⟩
  refine hu i j ⟨hij, _, _, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    fun q => ?_⟩
  constructor
  · intro hq
    have hp := IO_012_branch_sub o _ (List.getElem_mem hi) q hq
    exact (h2 q hp).1 ((h1 q hp).2 hq)
  · intro hq
    have hp := IO_012_branch_sub o _ (List.getElem_mem hj) q hq
    exact (h1 q hp).1 ((h2 q hp).2 hq)

/-! ### Examples over small nets -/

/-- AC1: an `Xor` node has at least two children. The children of an n-ary `Xor`, read back from
its right-nested binary form. -/
def xorChildren : Out N → List (Out N)
  | .xor l r => l :: xorChildren r
  | o => [o]

/-- AC1: an `Xor` node has at least two children. -/
example (l r : Out N) : 2 ≤ (xorChildren (Out.xor l r)).length := by
  cases r <;> simp [xorChildren]

/-- The transition of the examples: no arcs in, output spec `Xor(Place(0), Place(1))`. -/
def io012_t : Trans Nat :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.xor (.place 0) (.place 1)) }

/-- A transition with the arcs of `io012_t` (none) whose two `Xor` children are the same
place: `Xor(Place(0), Place(0))`. The ambiguity check rejects its output spec. -/
def io012_dup : Trans Nat :=
  { core := io012_t.core, out := some (.xor (.place 0) (.place 0)) }

/-- A transition with no arcs whose output spec is `Xor(Place(0), Timeout(Place(1)))`. -/
def io012_to : Trans Nat :=
  { core := io012_t.core, out := some (.xor (.place 0) (.timeout (.place 1))) }

/-- The marking of the examples in which every place is empty. -/
def io012_empty : Nat → Nat := fun _ => 0

/-- The marking after one token is deposited in place `0` from the empty marking. -/
def io012_after : Nat → Nat := fun n => if n = 0 then 1 else 0

/-- The reference firing of an arc-less example transition whose first output branch is `[0]`
from the empty marking. -/
theorem io012_fire0 (t : Trans Nat) (hcore : t.core = io012_t.core)
    (hout : ∃ o, t.out = some o ∧ o.branches[0]? = some [0]) :
    RefFire t io012_empty [0] io012_after := by
  obtain ⟨o, hr, hb⟩ := hout
  refine ⟨by rw [hcore]; decide, ⟨.action 0, by simp [deposit, hr, hb]⟩, ?_⟩
  funext n
  rw [hcore]
  by_cases h : n = 0
  · subst h; simp [fireNC, depProd, nconsumed, nspecAt, io012_t, io012_empty, io012_after]
  · simp [fireNC, depProd, nconsumed, nspecAt, io012_t, io012_empty, io012_after, h, Ne.symm h]

/-- The firing relation in which exactly the transitions with output spec `o` fire, each with
deposit `D`, leaving the marking unchanged. -/
def io012_oneFire (o : Out Nat) (D : List Nat) : FireRel Nat :=
  fun t m d m' => t.out = some o ∧ d = D ∧ m' = m

/-- `Xor(Place(0), Place(1))` passes the check. -/
theorem io012_t_unambiguous : IO_012_unambiguous (Out.xor (.place (0 : Nat)) (.place 1)) :=
  (IO_012_check_none _).1 (by decide)

/-- `Xor(Place(0), Timeout(Place(1)))` passes the check. -/
theorem io012_to_unambiguous :
    IO_012_unambiguous (Out.xor (.place (0 : Nat)) (.timeout (.place 1))) :=
  (IO_012_check_none _).1 (by decide)

/-- The model in which `IO_012_check` is the build check, `refBuild` the builder and
`io012_oneFire o D` the firings satisfies the build clauses of IO-012. -/
theorem io012_check_build :
    (∀ o : Out Nat, IO_012_check o = none ↔ IO_012_unambiguous o) ∧
      (∀ (o : Out Nat) (i j : Nat) (ps : List Nat),
        IO_012_check o = some (i, j, ps) ↔ IO_012_reported o i j ps) ∧
      IO_012_buildLine (N := Nat) IO_012_check refBuild :=
  ⟨IO_012_check_none, IO_012_check_some, IO_012_refBuild_rejects⟩

/-- ✗ A build check that accepts every output spec violates IO-012 (the first build clause,
AC4/AC5): it passes `Xor(Place(0), Place(0))`, whose two output branches claim `{0}`. -/
@[evidence forbids IO_012]
theorem IO_012_forbids_acceptAll :
    ¬ IO_012 (fun _ => none) refBuild (RefFire (N := Nat)) := by
  intro h
  exact ((h.1 (Out.xor (.place 0) (.place 0))).1 rfl) 0 1
    ⟨by decide, [0], [0], rfl, rfl, fun _ => Iff.rfl⟩

/-- A build check that reports the first clashing `i` rather than the first clashing `j`: on
`Xor(Place(3), Xor(Place(4), Xor(Place(4), Place(3))))` it reports branches 0 and 3, otherwise it
is `IO_012_check`. -/
def io012_iMajor (o : Out Nat) : Option (Nat × Nat × List Nat) :=
  if o.branches = [[3], [4], [4], [3]] then some (0, 3, [3]) else IO_012_check o

/-- The output spec on which `io012_iMajor` differs from `IO_012_check`. -/
def io012_pqqp : Out Nat := .xor (.place 3) (.xor (.place 4) (.xor (.place 4) (.place 3)))

/-- ✗ A build check that reports the wrong pair violates IO-012 (the second build clause, step
3): on `io012_pqqp` the first clashing `j` is 2 (with `i` = 1), not 3. -/
@[evidence forbids IO_012]
theorem IO_012_forbids_iMajor : ¬ IO_012 io012_iMajor refBuild (RefFire (N := Nat)) := by
  intro h
  have hr := (h.2.1 io012_pqqp 0 3 [3]).1 (by decide)
  exact hr.2.1 2 (by decide) 1 ⟨by decide, [4], [4], rfl, rfl, fun _ => Iff.rfl⟩

/-- ✗ A firing that writes no child violates IO-012 (the firing line, AC3): `io012_t` fires with
an empty deposit, and no output branch of `Xor(Place(0), Place(1))` is empty. -/
@[evidence forbids IO_012]
theorem IO_012_forbids_silent :
    ¬ IO_012 IO_012_check refBuild (io012_oneFire (.xor (.place 0) (.place 1)) []) := by
  intro h
  have := h.2.2.2 io012_t (.place 0) (.place 1) rfl io012_t_unambiguous [] io012_empty io012_empty
    ⟨⟨rfl, rfl, rfl⟩, by simp [IO_012_timeoutLike, TimeoutOutcome, io012_t, Out.findTimeout]⟩
  simp [Out.branches, ExactOn, outPlaces, Produced] at this

/-- ✗ A firing that writes both children violates IO-012 (the firing line; the test derivation's
"produces to both"): `Xor(Place(0), Place(1))` has no output branch `{0, 1}`. -/
@[evidence forbids IO_012]
theorem IO_012_forbids_both :
    ¬ IO_012 IO_012_check refBuild (io012_oneFire (.xor (.place 0) (.place 1)) [0, 1]) := by
  intro h
  have := h.2.2.2 io012_t (.place 0) (.place 1) rfl io012_t_unambiguous [0, 1] io012_empty
    io012_empty
    ⟨⟨rfl, rfl, rfl⟩, by simp [IO_012_timeoutLike, TimeoutOutcome, io012_t, Out.findTimeout]⟩
  simp [Out.branches, ExactOn, outPlaces, Produced] at this

/-- ✗ An `Xor` with a `Timeout` child is checked too (the firing line): `Xor(Place(0),
Timeout(Place(1)))` firing with an empty deposit is not, place by place, a timeout outcome (that
puts a token in `1`) and matches no output branch. -/
@[evidence forbids IO_012]
theorem IO_012_forbids_silentWithTimeout :
    ¬ IO_012 IO_012_check refBuild (io012_oneFire (.xor (.place 0) (.timeout (.place 1))) []) := by
  intro h
  have hto : ¬ IO_012_timeoutLike io012_to io012_empty [] := by
    rintro ⟨d₀, ⟨o, c, ho, hc, hd⟩, hp⟩
    simp only [io012_to, Option.some.injEq] at ho
    subst ho
    simp only [Out.findTimeout, Option.or, Option.some.injEq] at hc
    subst hc
    simp only [Out.timeoutDeposits, List.mem_singleton] at hd
    subst hd
    have := hp 1
    simp [Deposits, depProd] at this
  have := h.2.2.2 io012_to (.place 0) (.timeout (.place 1)) rfl io012_to_unambiguous []
    io012_empty io012_empty ⟨⟨rfl, rfl, rfl⟩, hto⟩
  simp [Out.branches, ExactOn, outPlaces, Produced] at this

/-- The output spec `Xor(Place(0), Timeout(And(Place(1), And(Place(2), ForwardInput(9, 3)))))`:
from a firing that consumed nothing from `9`, its timeout outcome deposits `[1, 2]`. -/
def io012_toFwd : Out Nat :=
  .xor (.place 0) (.timeout (.and (.place 1) (.and (.place 2) (.forward 9 3))))

/-- The firing relation in which exactly the arc-less transitions with output spec
`io012_toFwd` fire, depositing `[2, 1]` (the timeout deposit in the other order), leaving the
marking unchanged. -/
def io012_permFire : FireRel Nat :=
  fun t m d m' => t.out = some io012_toFwd ∧ t.core.inputs = [] ∧ d = [2, 1] ∧ m' = m

/-- ✓ IO-012 allows a firing whose deposit is a timeout-outcome deposit in another order
([CORE-036]): `[2, 1]` equals the timeout deposit `[1, 2]` place by place, so the firing may have ended with
the timeout outcome and the firing line does not constrain it, although `[2, 1]` matches no
output branch (`{0}`, `{1, 2, 3}`). -/
@[evidence allows IO_012]
theorem IO_012_allows_permutedTimeout : IO_012 IO_012_check refBuild io012_permFire := by
  refine ⟨IO_012_check_none, IO_012_check_some, IO_012_refBuild_rejects, ?_⟩
  rintro t l r ht - d m m' ⟨⟨hout, hin, rfl, -⟩, hto⟩
  exfalso
  apply hto
  have hc : Consumes t m 9 = 0 := by simp [Consumes, nconsumed, nspecAt, hin]
  refine ⟨[1, 2], ⟨io012_toFwd, _, hout, rfl, ?_⟩, fun p => ?_⟩
  · simp [Out.timeoutDeposits, cross, hc]
  · simp only [Deposits, depProd, List.count_cons, List.count_nil]
    omega

/-! ### Mutant readings -/

/-- Mutant reading of IO-012 that drops the build check: only the firing line, scoped as in
IO-012. -/
def IO_012_mutant_dropBuild [DecidableEq N] (_C : Out N → Option (Nat × Nat × List N))
    (_Build : Trans N → Option String) (F : FireRel N) : Prop :=
  ∀ (t : Trans N) (l r : Out N), OutputSpec t = some (.xor l r) →
    IO_012_unambiguous (.xor l r) → ∀ d : List N,
      on (fun m m' => F t m d m' ∧ ¬ IO_012_timeoutLike t m d),
        shall (fun _ _ => ∃ b ∈ (Out.xor l r).branches, ExactOn (.xor l r) d b)

/-- The accept-everything check kills the first mutant: the reference firings satisfy the firing
line, so the mutant holds, but `Xor(Place(0), Place(0))` builds and IO-012 fails. -/
@[evidence mutant IO_012]
theorem IO_012_mutant_dropBuild_killed :
    IO_012_mutant_dropBuild (fun _ => none) refBuild (RefFire (N := Nat)) ∧
      ¬ IO_012 (fun _ => none) refBuild (RefFire (N := Nat)) :=
  ⟨fun t l r ht _ d => IO_012_reference_someBranch t l r ht d, IO_012_forbids_acceptAll⟩

/-- Mutant reading of IO-012 that drops the firing line: only the build check. -/
def IO_012_mutant_dropSome [DecidableEq N] [ToString N] (C : Out N → Option (Nat × Nat × List N))
    (Build : Trans N → Option String) (_F : FireRel N) : Prop :=
  (∀ o : Out N, C o = none ↔ IO_012_unambiguous o) ∧
    (∀ (o : Out N) (i j : Nat) (ps : List N), C o = some (i, j, ps) ↔ IO_012_reported o i j ps) ∧
    IO_012_buildLine C Build

/-- The silent firing kills the second mutant: the reference check satisfies the build clauses,
but no output branch is exact for the empty deposit. -/
@[evidence mutant IO_012]
theorem IO_012_mutant_dropSome_killed :
    IO_012_mutant_dropSome IO_012_check refBuild (io012_oneFire (.xor (.place 0) (.place 1)) []) ∧
      ¬ IO_012 IO_012_check refBuild (io012_oneFire (.xor (.place 0) (.place 1)) []) :=
  ⟨io012_check_build, IO_012_forbids_silent⟩

/-- Mutant reading of IO-012 that lets the check report any clashing pair: the order of step 3
(first `j`, then smallest `i`) is dropped. -/
def IO_012_mutant_anyPair [DecidableEq N] (C : Out N → Option (Nat × Nat × List N))
    (Build : Trans N → Option String) (F : FireRel N) : Prop :=
  (∀ o : Out N, C o = none ↔ IO_012_unambiguous o) ∧
    (∀ (o : Out N) (i j : Nat) (ps : List N), C o = some (i, j, ps) →
      IO_012_clash o.branches i j ∧ o.branches[i]? = some ps) ∧
    IO_012_mutant_dropBuild C Build F

/-- The `i`-first check kills the third mutant: it reports a clashing pair with its places, so the
mutant holds, but on `io012_pqqp` it is not the pair step 3 names. -/
@[evidence mutant IO_012]
theorem IO_012_mutant_anyPair_killed :
    IO_012_mutant_anyPair io012_iMajor refBuild (RefFire (N := Nat)) ∧
      ¬ IO_012 io012_iMajor refBuild (RefFire (N := Nat)) := by
  refine ⟨⟨fun o => ?_, fun o i j ps => ?_,
    fun t l r ht _ d => IO_012_reference_someBranch t l r ht d⟩, IO_012_forbids_iMajor⟩
  · unfold io012_iMajor
    split
    · rename_i hb
      simp only [reduceCtorEq, false_iff]
      intro hu
      exact hu 1 2 ⟨by decide, [4], [4], by rw [hb]; rfl, by rw [hb]; rfl, fun _ => Iff.rfl⟩
    · exact IO_012_check_none o
  · unfold io012_iMajor
    split
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq]
      rintro ⟨rfl, rfl, rfl⟩
      exact ⟨⟨by decide, [3], [3], by rw [hb]; rfl, by rw [hb]; rfl, fun _ => Iff.rfl⟩,
        by rw [hb]; rfl⟩
    · intro hs
      have := (IO_012_check_some o i j ps).1 hs
      exact ⟨this.1, this.2.2.2⟩

/-- Mutant reading of IO-012 that compares output branches as lists, not as sets (against [IO-012], which compares sets):
`Xor(And(A, B), And(B, A))` would build. -/
def IO_012_mutant_listEq [DecidableEq N] (C : Out N → Option (Nat × Nat × List N))
    (Build : Trans N → Option String) (F : FireRel N) : Prop :=
  (∀ o : Out N, C o = none ↔ ∀ i j, ¬ IO_012_clashBy (fun b b' => decide (b = b')) o.branches i j) ∧
    (∀ (o : Out N) (i j : Nat) (ps : List N), C o = some (i, j, ps) ↔
      IO_012_clashBy (fun b b' => decide (b = b')) o.branches i j ∧
        (∀ j' < j, ∀ i', ¬ IO_012_clashBy (fun b b' => decide (b = b')) o.branches i' j') ∧
        (∀ i' < i, ¬ IO_012_clashBy (fun b b' => decide (b = b')) o.branches i' j) ∧
        o.branches[i]? = some ps) ∧
    IO_012_mutant_dropBuild C Build F

/-- The list-comparing check: steps 1 to 4 with branches compared as lists. -/
def io012_listCheck (o : Out Nat) : Option (Nat × Nat × List Nat) :=
  IO_012_scan (fun b b' => decide (b = b')) o.branches

/-- The list-comparing check kills the fourth mutant: it is the mutant's algorithm, so the mutant
holds, but it passes `Xor(And(0, 1), And(1, 0))`, whose two branches are the same set. -/
@[evidence mutant IO_012]
theorem IO_012_mutant_listEq_killed :
    IO_012_mutant_listEq io012_listCheck refBuild (RefFire (N := Nat)) ∧
      ¬ IO_012 io012_listCheck refBuild (RefFire (N := Nat)) := by
  refine ⟨⟨fun o => IO_012_scan_none _ _, fun o i j ps => IO_012_scan_some _ _ i j ps,
    fun t l r ht _ d => IO_012_reference_someBranch t l r ht d⟩, fun h => ?_⟩
  have hu := (h.1 (Out.xor (.and (.place 0) (.place 1)) (.and (.place 1) (.place 0)))).1
    (by decide)
  exact hu 0 1 ⟨by decide, [0, 1], [1, 0], rfl, rfl, fun q => by simp [or_comm]⟩

/-- Mutant reading of IO-012 that skips every transition whose `Xor` contains a `Timeout` node
(an earlier scope), and checks the others without the timeout exclusion. -/
def IO_012_mutant_noTimeout [DecidableEq N] [ToString N]
    (C : Out N → Option (Nat × Nat × List N)) (Build : Trans N → Option String) (F : FireRel N) :
    Prop :=
  IO_012_mutant_dropSome C Build F ∧
    ∀ (t : Trans N) (l r : Out N), OutputSpec t = some (.xor l r) →
      IO_012_unambiguous (.xor l r) → (Out.xor l r).findTimeout = none → ∀ d : List N,
        on (fun m m' => F t m d m'),
          shall (fun _ _ => ∃ b ∈ (Out.xor l r).branches, ExactOn (.xor l r) d b)

/-- The silent firing under `Xor(Place(0), Timeout(Place(1)))` kills the Timeout-excluding
mutant: the mutant never looks at that transition, IO-012 does. -/
@[evidence mutant IO_012]
theorem IO_012_mutant_noTimeout_killed :
    IO_012_mutant_noTimeout IO_012_check refBuild (io012_oneFire (.xor (.place 0) (.timeout (.place 1))) []) ∧
      ¬ IO_012 IO_012_check refBuild (io012_oneFire (.xor (.place 0) (.timeout (.place 1))) []) := by
  refine ⟨⟨io012_check_build, ?_⟩, IO_012_forbids_silentWithTimeout⟩
  rintro t l r ht - hto d m m' ⟨hout, -, -⟩
  have ht' : t.out = some (.xor l r) := ht
  rw [hout] at ht'
  cases ht'
  simp [Out.findTimeout] at hto

/-- `Xor(Place(0), Place(0))` is ambiguous: its two output branches both claim `{0}`. -/
theorem io012_dup_ambiguous : ¬ IO_012_unambiguous (Out.xor (.place (0 : Nat)) (.place 0)) :=
  fun hu => hu 0 1 ⟨by decide, [0], [0], rfl, rfl, fun _ => Iff.rfl⟩

/-- ✗ A builder that builds every transition violates IO-012 (the build line): `io012_dup`,
whose output spec `Xor(Place(0), Place(0))` is ambiguous, builds. -/
@[evidence forbids IO_012]
theorem IO_012_forbids_buildAll :
    ¬ IO_012 IO_012_check (fun _ => none) (RefFire (N := Nat)) := by
  intro h
  exact (h.2.2.1 io012_dup _ rfl io012_dup_ambiguous).1 rfl

/-- A builder that rejects whatever the reference builder rejects, but always with the message
`rejected`. -/
def io012_buildVague {N : Type} [DecidableEq N] [ToString N] (t : Trans N) : Option String :=
  (refBuild t).map fun _ => "rejected"

/-- `Xor(P, P)` over place names, on a transition `t` with no arcs. -/
def io012_dupS : Trans String :=
  { core := { name := "t", inputs := [], inhibitors := [], reads := [], resets := [] },
    out := some (.xor (.place "P") (.place "P")) }

/-- ✗ A builder that rejects an ambiguous output spec with another message violates IO-012 (the
build line): `Xor(P, P)` passes every earlier check, so building it must fail with IO-012's
message for branches 0 and 1 and `{P}`, not with `rejected`. -/
@[evidence forbids IO_012]
theorem IO_012_forbids_buildVague :
    ¬ IO_012 IO_012_check io012_buildVague (RefFire (N := String)) := by
  intro h
  have hu : ¬ IO_012_unambiguous (Out.xor (.place "P") (.place "P")) :=
    fun hu => hu 0 1 ⟨by decide, ["P"], ["P"], rfl, rfl, fun _ => Iff.rfl⟩
  have := (h.2.2.1 io012_dupS _ rfl hu).2 (by decide) (by decide) (by decide) rfl rfl
    (by simp [forwardSources]) 0 1 ["P"] (by decide)
  revert this
  decide

/-- Mutant reading of IO-012 without the build line: the check reports as IO-012 says and the
firing line holds, but nothing ties the check to building. -/
def IO_012_mutant_dropBuildLine [DecidableEq N] (C : Out N → Option (Nat × Nat × List N))
    (_Build : Trans N → Option String) (F : FireRel N) : Prop :=
  (∀ o : Out N, C o = none ↔ IO_012_unambiguous o) ∧
    (∀ (o : Out N) (i j : Nat) (ps : List N), C o = some (i, j, ps) ↔ IO_012_reported o i j ps) ∧
    IO_012_mutant_dropBuild C _Build F

/-- The build-everything builder kills the build-line mutant: the reference check and firings
satisfy every other line, but `Xor(Place(0), Place(0))` builds. -/
@[evidence mutant IO_012]
theorem IO_012_mutant_dropBuildLine_killed :
    IO_012_mutant_dropBuildLine IO_012_check (fun _ => none) (RefFire (N := Nat)) ∧
      ¬ IO_012 IO_012_check (fun _ => none) (RefFire (N := Nat)) :=
  ⟨⟨IO_012_check_none, IO_012_check_some,
    fun t l r ht _ d => IO_012_reference_someBranch t l r ht d⟩, IO_012_forbids_buildAll⟩

/-- Mutant reading of IO-012 that asks only that an ambiguous output spec does not build, with
any message. -/
def IO_012_mutant_anyMessage [DecidableEq N] (C : Out N → Option (Nat × Nat × List N))
    (Build : Trans N → Option String) (F : FireRel N) : Prop :=
  (∀ o : Out N, C o = none ↔ IO_012_unambiguous o) ∧
    (∀ (o : Out N) (i j : Nat) (ps : List N), C o = some (i, j, ps) ↔ IO_012_reported o i j ps) ∧
    (∀ (t : Trans N) (o : Out N), OutputSpec t = some o → ¬ IO_012_unambiguous o →
      Build t ≠ none) ∧
    IO_012_mutant_dropBuild C Build F

/-- The vague builder kills the any-message mutant: it rejects whatever the reference builder
rejects, but not with IO-012's message. -/
@[evidence mutant IO_012]
theorem IO_012_mutant_anyMessage_killed :
    IO_012_mutant_anyMessage IO_012_check io012_buildVague (RefFire (N := String)) ∧
      ¬ IO_012 IO_012_check io012_buildVague (RefFire (N := String)) := by
  refine ⟨⟨IO_012_check_none, IO_012_check_some, fun t o ho hu => ?_,
    fun t l r ht _ d => IO_012_reference_someBranch t l r ht d⟩, IO_012_forbids_buildVague⟩
  have := (IO_012_refBuild_rejects t o ho hu).1
  simpa [io012_buildVague] using this

/-- The build check and the firing line of IO-012 are exercised by the reference: `io012_t` has
the output spec `Xor(Place(0), Place(1))`, which the reference check passes; it fires from the
empty marking writing place `0`, which is not a timeout outcome (the trigger of the firing line);
the branch `{0}` is exact, the branch `{1}` is not; and the reference check rejects
`Xor(Place(0), Place(0))`, the output spec of `io012_dup`, reporting branches 0 and 1 and the
places `[0]`. -/
@[evidence nonvacuous IO_012]
theorem IO_012_nonvacuous :
    OutputSpec io012_t = some (.xor (.place 0) (.place 1)) ∧
      IO_012_check (Out.xor (.place (0 : Nat)) (.place 1)) = none ∧
      RefFire io012_t io012_empty [0] io012_after ∧
      ¬ IO_012_timeoutLike io012_t io012_empty [0] ∧
      ExactOn (Out.xor (.place (0 : Nat)) (.place 1)) [0] [0] ∧
      ¬ ExactOn (Out.xor (.place (0 : Nat)) (.place 1)) [0] [1] ∧
      OutputSpec io012_dup = some (.xor (.place 0) (.place 0)) ∧
      IO_012_check (Out.xor (.place (0 : Nat)) (.place 0)) = some (0, 1, [0]) := by
  refine ⟨rfl, by decide, io012_fire0 io012_t rfl ⟨_, rfl, rfl⟩,
    by simp [IO_012_timeoutLike, TimeoutOutcome, io012_t, Out.findTimeout], fun _ _ => Iff.rfl,
    ?_, rfl, by decide⟩
  simp [ExactOn, outPlaces, Produced]

end Libpetri.Spec
