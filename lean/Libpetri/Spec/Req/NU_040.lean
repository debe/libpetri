import Libpetri.Spec.Registry
import Libpetri.Reference.Nu
import Libpetri.Reference.Semantics
import Libpetri.Spec.Text.NU_040

set_option linter.missingDocs true

/-!
# NU-040: Bounded budget and decidability (`spec/12-nu-nets.md`)

Most of NU-040 is not a requirement on an implementation: the decidability paragraphs cite the
literature, and the `Budget` / `Pending` pattern is modelling advice. Two groups of sentences
bind the verifier, and each is a block:

* `NU_040_mint` (kind F), over a declaration function `DM budgets explicit t`: a transition with
  an input arc on a declared budget place is a declared mint ([NU-010]); a transition named as a
  mint on the verifier stays one whatever budget places are declared; and nothing else is a
  declared mint. The block has exactly one model (`NU_040_mint_unique`), the witness
  `nu040DeclaredMint`, which is the `declared_mints` / `declaredMints` of the three runtimes.
* `NU_040_jodl` (kind F), over a violation predicate `PS X sinks pending M` (the net's
  transitions, its declared sink places, the pending place, a marking): a marking violates
  `JoinedOrDeadLettered(pending)` exactly when it rests ([VER-002]'s quiescence, with a matched
  transition enabled only as [NU-020] says, `NuRests`) and `pending` holds a token. The sink
  places are an argument the predicate must ignore: the property has no sink clause. The witness
  is `refJodl`.

On a net without a matched transition the predicate is the count-level reference property
`quiescentCount [pending] 0 (some 0)` (`NU_040_jodl_matchFree`), the predicate every name-blind
route encodes. On a net with one, the count-level reading misses a stranded correlation group
(`NU_040_jodl_forbids_countLevel`), which is why the runtimes turn a name-blind verdict on a
quiescence property of such a net into `Unknown`.

AC1 and AC2 are about one net each; they are worked examples over the reference ν firing
(`NU_040_ac1`, `NU_040_ac2`, `NU_040_stranded`), not lines.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The witnesses -/

/-- **The reference mint declaration** ([NU-010], [NU-040]): a transition is a declared mint when
the verifier names it (`explicit`, `mintTransitions` / `mint_transitions`) or when it has an input
arc on a declared budget place. This is `declared_mints` of
`rust/libpetri-verification/src/name_fragment.rs`, `NameFragment.declaredMints`
(`java/src/main/java/org/libpetri/analysis/NameFragment.java`) and `declaredMints`
(`typescript/src/verification/analysis/name-fragment.ts`), read per transition. -/
def nu040DeclaredMint {N : Type} [DecidableEq N] (budgets : List N) (explicit : List String)
    (t : Trans N) : Bool :=
  explicit.contains t.core.name || t.core.inputs.any fun s => budgets.contains s.place

/- The reference declaration is the witness model of NU_040_mint's `holds` theorem. -/
#spec_witness nu040DeclaredMint

/-- **The reference `JoinedOrDeadLettered` violation** ([NU-040] AC4): the marking rests (every
transition it ν-enables is reapable, `NuRests`) and `pending` holds a token. The declared sink
places are an argument and play no part. This is the predicate of the
`JoinedOrDeadLettered` arm of `decide_over_classes` (`rust/libpetri-verification/src/graph_decision.rs`,
Route B), of `encode_violation` (`name_coloured_encoder.rs`, Route A), of
`encode_property_violation` (`smt_encoder.rs`) and of `violates_indexed` (`abstract_replay.rs`)
(the name-blind routes). -/
def refJodl {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]
    (X : List (NuTrans N (KeyFn V Nm))) (_sinks : List N) (pending : N)
    (M : QMarking N (Stamped V)) : Prop :=
  NuRests X M ∧ M pending ≠ []

/- The reference violation predicate is the witness model of NU_040_jodl's `holds` theorem. -/
#spec_witness refJodl

/-! ## NU-040, budget places declare mints -/

requirement NU_040_mint
  id "NU-040"
  title "Bounded Budget and Decidability (budget places declare mints)"
  kind F
  scope "the mint declaration every verifier route reads (declared_mints / declaredMints), Route A and Route B of NU-050"
  source verbatim "spec/12-nu-nets.md"
  covers NU_040.s1, NU_040.s2, NU_040.s3
  reading "Let DM B E t say whether the transition t is a declared mint, when B are the places declared to the verifier as budget places and E the names declared to it as mint transitions."
          "For all B, E and t: if some input arc of t is on a place of B, then DM B E t is true."
          "For all B, E and t: if the name of t is in E, then DM B E t is true, whatever B is."
          "For all B, E and t: if DM B E t is true, then the name of t is in E or some input arc of t is on a place of B."
  assumes "The model is one declaration function DM: from the declared budget places, the names declared as mints on the verifier (mintTransitions / mint_transitions) and a transition, whether the transition is a declared mint. The three runtimes compute it once per net as a set of names, seeded with the named mints and extended by every transition with an input arc on a budget place (declared_mints in rust/libpetri-verification/src/name_fragment.rs, NameFragment.declaredMints in java/src/main/java/org/libpetri/analysis/NameFragment.java, declaredMints in typescript/src/verification/analysis/name-fragment.ts); read per transition it is nu040DeclaredMint, the only model of the three lines (NU_040_mint_unique)."
          "An input arc is one of the transition's input specifications (input_specs / inputSpecs), whatever its cardinality: a read, inhibitor or reset arc on a budget place declares nothing (the third line, NU_040_mint_mutant_noOnlyWhen_killed). The second line is the word 'also' of the sentence before the first quote: the budget declaration adds to the named one and never replaces it (NU_040_mint_mutant_noAlso_killed). The three lines are the rule of NU-010's sentence 'the ν routes of [NU-050] read a transition as a mint ... only when the net declares it, in one of two ways', stated here once for both."
          "What a declared mint must write (one fresh name into every coloured place it writes without consuming one) is the mint contract of NU-010, and how the routes read the write is NU-010's and NU-051's classification; neither is a line here. A named mint that is not a transition of the net is NU-010 AC6 (the declaration fails and names it); per transition, as here, it marks no transition."
          "How a budget place is declared (budgetPlace / budget_place / budget_places on the verifier) is configuration, kind N. A declared budget place that is not a place of the net declares no mint, since no transition has an input arc on it."
  signoff "2026-11-13 abc4a216c30f4b57 ai"
  statement : ∀ {N : Type} [DecidableEq N], (List N → List String → Trans N → Bool) → Prop :=
    fun DM =>
      (∀ budgets explicit (t : Trans _),
        (∃ s ∈ t.core.inputs, s.place ∈ budgets) → DM budgets explicit t = true) ∧
      (∀ budgets explicit (t : Trans _), t.core.name ∈ explicit → DM budgets explicit t = true) ∧
      (∀ budgets explicit (t : Trans _), DM budgets explicit t = true →
        t.core.name ∈ explicit ∨ ∃ s ∈ t.core.inputs, s.place ∈ budgets)

/- The pinned readable form of NU_040_mint: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_040_mint : {N : Type} →
  [DecidableEq N] → (List N → List String → Reference.Trans N → Bool) → Prop :=
fun {N} [DecidableEq N] DM =>
  (∀ (budgets : List N) (explicit : List String) (t : Reference.Trans N),
      (∃ s ∈ t.core.inputs, s.place ∈ budgets) → DM budgets explicit t = true) ∧
    (∀ (budgets : List N) (explicit : List String) (t : Reference.Trans N),
        t.core.name ∈ explicit → DM budgets explicit t = true) ∧
      ∀ (budgets : List N) (explicit : List String) (t : Reference.Trans N),
        DM budgets explicit t = true → t.core.name ∈ explicit ∨ ∃ s ∈ t.core.inputs, s.place ∈ budgets
-/
#guard_msgs in #print NU_040_mint

/-! ## NU-040, `JoinedOrDeadLettered` -/

requirement NU_040_jodl
  id "NU-040"
  title "Bounded Budget and Decidability (JoinedOrDeadLettered)"
  kind F
  scope "every verifier route that decides JoinedOrDeadLettered: Route B, Route A, and on a net without a matched transition the untimed encoder, the structural and abstract-replay checks"
  source verbatim "spec/12-nu-nets.md"
  covers NU_040.s4, NU_040.s5, NU_040.s6
  reading "Let PS X S p M say that the marking M violates JoinedOrDeadLettered(p) on the net with transitions X and declared sink places S."
          "For all X, S, p and M: if M rests on X (every transition of X that is ν-enabled at M, enabled on its counts and, with a match, with some name eligible, is reapable: NuRests) and p holds a token in M, then PS X S p M, whatever the sink places S are and whether or not they are marked."
          "For all X, S, p and M: if PS X S p M, then M rests on X and p holds a token in M."
  assumes "The model is one violation predicate PS per route, over the transitions of a ν net (NuTrans, a match specification or none), the declared sink places, the pending place and a queue marking of stamped tokens. The property itself is 'no reachable marking violates': which markings a route reaches, and that its Proven is sound for the executor, are NU-050's and VER-012's (Route B: Novel.RouteB.routeB_untimed_quiescence_sound; Route A: routeA_quiescence_sound_plan and routeA_quiescence_sound_reaping). 'Every route that decides it decides this same predicate' is the line read per route: each route's predicate is a model of this block, so all of them are refJodl (NU_040_jodl_unique)."
          "Quiescence is VER-002's: every transition the marking enables is reapable ([TIME-013]: Deadline or Window timing). 'Enables' is NU-020's for a matched transition (NuEnabled: enabled on the counts, and some name eligible, which needs at least one correlated input) and the counts alone otherwise. The third quoted sentence is that reading of NuRests in the first two lines, worked by NU_040_jodl_forbids_presentOnly (the required count of a correlated input) and NU_040_jodl_forbids_emptyMatch (a match without a correlated input)."
          "A route that reads enablement on token counts alone does not decide JoinedOrDeadLettered(pending) on a net with a transition that has a match specification, and answers Unknown there ([NU-050]): that sentence is descriptive, and the runtimes do it in the quiescence branch of apply_nu_guard (rust/libpetri-verification/src/smt_verifier.rs) and of SmtVerifier.applyNuGuard (java/src/main/java/org/libpetri/smt/SmtVerifier.java, typescript/src/verification/smt-verifier.ts), since the count-level reading misses a stranded group (NU_040_jodl_forbids_countLevel). On a net without a matched transition the predicate is the count-level reference property quiescentCount [pending] 0 (some 0) (NU_040_jodl_matchFree), which the name-blind routes encode."
          "Environment places are outside the model: the routes treat an input or read arc on an injectable environment place as satisfiable by injection (VER-006), so such a transition does not make a marking quiescent; the line is about the closed net. A pending name that is not a place of the net is configuration (kind N): the encoders make the property unviolatable (the JoinedOrDeadLettered arm of encode_property_violation in smt_encoder.rs), which the line does not pin. A run that never comes to rest does not violate the property; the definitional paragraph says so."
          "AC4 (JoinedOrDeadLettered(pending) is exactly 'no reachable quiescent marking holds a pending token', quiescent as in VER-002 with a matched transition enabled as in NU-020, with no sink clause, and every route that decides it decides this same predicate) is the block: the two lines give the predicate on one marking, the sink places are an argument it must ignore (NU_040_jodl_forbids_sinkClause), and two models of the block agree everywhere (NU_040_jodl_unique)."
          "AC1 and AC2 are about one net each (a fork gated on a budget place, a matched join and a dead-letter transition) and are worked examples over the reference ν firing, not lines. A group is live while its pending token is present, as the Pending bullet says. NU_040_ac1: budget plus pending stays k, and each branch place holds as many tokens as pending, on every reachable marking, so PlaceBound(Budget, k), PlaceBound(Pending, k) and the branch bounds hold. NU_040_ac2: pending is empty at every reachable rest."
          "That the untimed encoder can check PlaceBound(Budget, k) once the budget place is declared (the budget bullet and the test derivation) is an offer of the verifier, not a safety line: no line here states it. Declaring the budget place is NU_040_mint's and configuration; without it the name-blind untimed encoder answers Unknown for every property of a net with a matched transition (the unbounded-fresh-names branch of apply_nu_guard in smt_verifier.rs and of applyNuGuard in SmtVerifier.java and smt-verifier.ts), which is why the edited sentences name the declaration. That downgrade reads the name-blind verdict only: a coloured Route A verdict returns before it (apply_nu_guard in smt_verifier.rs, the coloured branch first), and Route B can answer Proven with declared mints and no budget place (NU-010 AC4). An existence theorem that the name-blind route answers Proven there is an open item for the ν consistency theorem."
          "AC3 and the decidability paragraphs state facts about the literature and point at NU-050 AC2 (a net with unbounded fresh names and no budget is never Proven, ruling D59 (a)); the Budget and Pending pattern is modelling advice. Neither is a line here."
  signoff "2026-11-13 c0e5e0834cca34c8 ai"
  statement : ∀ {N V Nm : Type} [DecidableEq N] [LinearOrder Nm],
      (List (NuTrans N (KeyFn V Nm)) → List N → N → QMarking N (Stamped V) → Prop) → Prop :=
    fun PS =>
      (∀ X sinks pending M, NuRests X M → M pending ≠ [] → PS X sinks pending M) ∧
      (∀ X sinks pending M, PS X sinks pending M → NuRests X M ∧ M pending ≠ [])

/- The pinned readable form of NU_040_jodl: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.NU_040_jodl : {N V Nm : Type} →
  [DecidableEq N] →
    [LinearOrder Nm] → (List (NuTrans N (KeyFn V Nm)) → List N → N → QMarking N (Stamped V) → Prop) → Prop :=
fun {N V Nm} [DecidableEq N] [LinearOrder Nm] PS =>
  (∀ (X : List (NuTrans N (KeyFn V Nm))) (sinks : List N) (pending : N) (M : QMarking N (Stamped V)),
      NuRests X M → M pending ≠ [] → PS X sinks pending M) ∧
    ∀ (X : List (NuTrans N (KeyFn V Nm))) (sinks : List N) (pending : N) (M : QMarking N (Stamped V)),
      PS X sinks pending M → NuRests X M ∧ M pending ≠ []
-/
#guard_msgs in #print NU_040_jodl

/-! ## Holds -/

/-- The whole reference declaration: a transition is a declared mint exactly when the verifier
names it or it has an input arc on a declared budget place. -/
theorem nu040DeclaredMint_iff {N : Type} [DecidableEq N] (budgets : List N)
    (explicit : List String) (t : Trans N) :
    nu040DeclaredMint budgets explicit t = true ↔
      t.core.name ∈ explicit ∨ ∃ s ∈ t.core.inputs, s.place ∈ budgets := by
  simp [nu040DeclaredMint]

/-- ✓ The reference declaration satisfies NU_040_mint: a transition with an input arc on a
declared budget place is a declared mint, a named transition is one whatever the budget places,
and no other transition is. -/
@[evidence holds NU_040_mint]
theorem NU_040_mint_reference {N : Type} [DecidableEq N] :
    NU_040_mint (nu040DeclaredMint (N := N)) :=
  ⟨fun b e t h => (nu040DeclaredMint_iff b e t).2 (Or.inr h),
    fun b e t h => (nu040DeclaredMint_iff b e t).2 (Or.inl h),
    fun b e t h => (nu040DeclaredMint_iff b e t).1 h⟩

/-- NU_040_mint has exactly one model: every declaration function that meets it is the
reference declaration, so every route reads the same transitions as declared mints. -/
theorem NU_040_mint_unique {N : Type} [DecidableEq N]
    {DM : List N → List String → Trans N → Bool} (h : NU_040_mint DM) :
    ∀ budgets explicit t, DM budgets explicit t = nu040DeclaredMint budgets explicit t := by
  intro b e t
  have key : DM b e t = true ↔ nu040DeclaredMint b e t = true := by
    rw [nu040DeclaredMint_iff]
    exact ⟨h.2.2 b e t, fun h' => h'.elim (h.2.1 b e t) (h.1 b e t)⟩
  cases hd : DM b e t <;> cases hr : nu040DeclaredMint b e t <;> simp_all

/-- ✓ The reference violation predicate satisfies NU_040_jodl. -/
@[evidence holds NU_040_jodl]
theorem NU_040_jodl_reference {N V Nm : Type} [DecidableEq N] [LinearOrder Nm] :
    NU_040_jodl (refJodl (N := N) (V := V) (Nm := Nm)) :=
  ⟨fun _ _ _ _ hr hp => ⟨hr, hp⟩, fun _ _ _ _ h => h⟩

/-- NU_040_jodl has exactly one model: two predicates that satisfy it agree everywhere, so every
route that decides `JoinedOrDeadLettered` decides the same predicate. -/
theorem NU_040_jodl_unique {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]
    {PS : List (NuTrans N (KeyFn V Nm)) → List N → N → QMarking N (Stamped V) → Prop}
    (h : NU_040_jodl PS) : ∀ X sinks pending M, PS X sinks pending M ↔ refJodl X sinks pending M :=
  fun X sinks pending M => ⟨h.2 X sinks pending M, fun ⟨hr, hp⟩ => h.1 X sinks pending M hr hp⟩

/-! ## Without a match: the count-level reference property -/

section MatchFree
variable {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]

/-- A transition without a match is ν-enabled exactly when it is enabled on its counts. -/
theorem nuEnabled_of_none {t : NuTrans N (KeyFn V Nm)} (h : t.mspec = none)
    (M : QMarking N (Stamped V)) : NuEnabled t M ↔ Enabled t.base (qCount M) :=
  ⟨fun h' => h'.1, fun h' => ⟨h', fun ms hms => by rw [h] at hms; cases hms⟩⟩

/-- On a net without a matched transition a ν rest is the count-level reap-quiescence of
[VER-002] (`Reference.ReapQuiescent`). -/
theorem nuRests_matchFree {X : List (NuTrans N (KeyFn V Nm))} (hX : ∀ t ∈ X, t.mspec = none)
    (places : List N) (M : QMarking N (Stamped V)) :
    NuRests X M ↔ ReapQuiescent ⟨places, X.map (·.base)⟩ (qCount M) := by
  constructor
  · intro h t ht hen
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
    exact h u hu ((nuEnabled_of_none (hX u hu) M).2 hen)
  · intro h t ht hen
    exact h t.base (List.mem_map.2 ⟨t, ht, rfl⟩) ((nuEnabled_of_none (hX t ht) M).1 hen)

/-- **Every name-blind route decides the same predicate.** On a net without a matched
transition, `refJodl` is the count-level reference property `quiescentCount [pending] 0 (some 0)`
of `Reference.Violates` on the token counts, the predicate the untimed encoder and the
structural checks encode. -/
theorem NU_040_jodl_matchFree {X : List (NuTrans N (KeyFn V Nm))} (hX : ∀ t ∈ X, t.mspec = none)
    (places sinks : List N) (pending : N) (M : QMarking N (Stamped V)) :
    refJodl X sinks pending M ↔
      Violates ⟨places, X.map (·.base)⟩ (.quiescentCount [pending] 0 (some 0)) (qCount M) := by
  unfold refJodl
  rw [nuRests_matchFree hX places M]
  simp [Violates, qCount, List.length_pos_iff]

end MatchFree

/-! ## The scatter-gather example net -/

/-- A token with value (and name) `v`, created at 0. -/
def nu040_tok (v : Nat) : Stamped Nat := ⟨v, 0⟩

/-- The key: a token's name is its value. -/
def nu040_key : KeyFn Nat Nat := some

/-- The match of the join: branch places 1 (`a`) and 2 (`b`). -/
def nu040_ms : MatchSpec Nat (KeyFn Nat Nat) := { keys := [(1, nu040_key), (2, nu040_key)] }

/-- Places: 0 `budget`, 1 `a`, 2 `b`, 3 `pending`, 4 `done`, 5 `dead`. The fork takes one budget
token and writes `a`, `b` and `pending`. -/
def nu040_fork : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "fork", inputs := [⟨0, .one⟩], inhibitors := [], reads := [],
                        resets := [] },
              out := some (.and (.place 1) (.and (.place 2) (.place 3))) } }

/-- The join: one token of one name from `a` and from `b`, and one `pending` token; it returns
the budget token and marks `done`. -/
def nu040_join : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "join", inputs := [⟨1, .one⟩, ⟨2, .one⟩, ⟨3, .one⟩],
                        inhibitors := [], reads := [], resets := [] },
              out := some (.and (.place 0) (.place 4)) }
    mspec := some nu040_ms }

/-- The dead-letter transition: it gives up on the oldest group, taking the oldest token of `a`,
of `b` and of `pending`, returns the budget token and marks `dead`. `reap` is its reapable bit
([TIME-013]). -/
def nu040_dl (reap : Bool) : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "deadLetter", inputs := [⟨1, .one⟩, ⟨2, .one⟩, ⟨3, .one⟩],
                        inhibitors := [], reads := [], resets := [] },
              out := some (.and (.place 0) (.place 5)), reapable := reap } }

/-- The scatter-gather net of AC1 and AC2: fork, join and an immediate dead-letter. -/
def nu040_net : List (NuTrans Nat (KeyFn Nat Nat)) := [nu040_fork, nu040_join, nu040_dl false]

/-- The initial marking: `k` budget tokens, nothing else. -/
def nu040_M0 (k : Nat) : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then List.replicate k (nu040_tok 0) else []

/-- A group the dead-letter can still handle: name 0 in `a`, name 1 in `b`, a `pending` token. -/
def nu040_Mg : QMarking Nat (Stamped Nat) := fun p =>
  if p = 1 then [nu040_tok 0] else if p = 2 then [nu040_tok 1]
  else if p = 3 then [nu040_tok 7] else []

/-! ## Counting a ν firing -/

section Counting
variable {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]

/-- On a place that is not a correlated input and has no reset arc, a ν firing (matched or not)
removes the FIFO prefix of the plain firing and appends what it emitted there. -/
theorem refNuFire_unkeyed {t : NuTrans N (KeyFn V Nm)} {M : QMarking N (Stamped V)} {c δ e M'}
    (hf : RefNuFire t M c δ e M') {p : N}
    (hk : ∀ ms, t.mspec = some ms → keyAt ms p = none) (hr : p ∉ t.base.core.resets) :
    M' p = (M p).drop (qTake M t.base p) ++ qEmittedTo e p ∧ Enabled t.base (qCount M) ∧
      ∃ (f : N → Nat) (ch : Novel.ForwardDeposit.Choice), deposit f t.base.out ch = some (e.map Prod.fst) := by
  cases h : t.mspec with
  | none =>
    obtain ⟨-, hen, ⟨ch, hdep⟩, -, rfl⟩ := (refNuFire_restrictsTo t h M c δ e M').1 hf
    exact ⟨by rw [qFire_apply]; simp [hr], hen, _, ch, hdep⟩
  | some ms =>
    obtain ⟨n, -, -, hen, ⟨ch, hdep⟩, -, -, rfl⟩ := (refNuFire_matched h M c δ e M').1 hf
    refine ⟨?_, hen, _, ch, hdep⟩
    rw [qAppend_apply]
    simp [nuConsume, hr, nuPost, hk ms h, qPostInput]

/-- The count form of `refNuFire_unkeyed`. -/
theorem refNuFire_unkeyed_count {t : NuTrans N (KeyFn V Nm)} {M : QMarking N (Stamped V)}
    {c δ e M'} (hf : RefNuFire t M c δ e M') {p : N}
    (hk : ∀ ms, t.mspec = some ms → keyAt ms p = none) (hr : p ∉ t.base.core.resets) :
    qCount M' p = qCount M p - qTake M t.base p + (e.map Prod.fst).count p := by
  have h := (refNuFire_unkeyed hf hk hr).1
  simp [qCount, h, qEmittedTo_length]

/-- Dropping the first `k` tokens of a name removes `k` tokens, or every token of the name when
there are fewer. -/
theorem nu040_dropNamed_length (f : KeyFn V Nm) (n : Nm) :
    ∀ (k : Nat) (l : List (Stamped V)),
      (dropNamed f n k l).length = l.length - min k (named f n l).length
  | 0, l => by simp [dropNamed]
  | _ + 1, [] => by simp [dropNamed]
  | k + 1, x :: xs => by
    have hle : (named f n xs).length ≤ xs.length := List.length_filter_le _ _
    by_cases h : f x.val = some n
    · have ih := nu040_dropNamed_length f n k xs
      have hn : named f n (x :: xs) = x :: named f n xs := by simp [named, h]
      rw [dropNamed, if_pos h, ih, hn]
      simp only [List.length_cons]
      omega
    · have ih := nu040_dropNamed_length f n (k + 1) xs
      have hn : named f n (x :: xs) = named f n xs := by simp [named, h]
      rw [dropNamed, if_neg h, List.length_cons, ih, hn]
      simp only [List.length_cons]
      omega

/-- The selection input holds one stamp per token of the name on a correlated input. -/
theorem nu040_stamps_length (f : KeyFn V Nm) (n : Nm) : ∀ l : List (Stamped V),
    (stamps (l.filterMap fun x => (f x.val).map fun n' => (n', x.stamp)) n).length =
      (named f n l).length
  | [] => rfl
  | x :: xs => by
    have ih := nu040_stamps_length f n xs
    unfold stamps named at ih ⊢
    cases h : f x.val with
    | none => simp [h, ih]
    | some m =>
      by_cases hm : m = n
      · subst hm; simp [h, ih]
      · simp [h, hm, ih]

end Counting

/-- The fork's only outcome writes `a`, `b` and `pending`. -/
theorem nu040_fork_dep {f : Nat → Nat} {ch d} (h : deposit f nu040_fork.base.out ch = some d) :
    d = [1, 2, 3] := by
  cases ch with
  | action i =>
    cases i with
    | zero => simpa [deposit, nu040_fork, Out.branches, cross] using h.symm
    | succ i => simp [deposit, nu040_fork, Out.branches, cross] at h
  | timedOut j => simp [deposit, nu040_fork, Out.findTimeout] at h

/-- The join's only outcome writes `budget` and `done`. -/
theorem nu040_join_dep {f : Nat → Nat} {ch d} (h : deposit f nu040_join.base.out ch = some d) :
    d = [0, 4] := by
  cases ch with
  | action i =>
    cases i with
    | zero => simpa [deposit, nu040_join, Out.branches, cross] using h.symm
    | succ i => simp [deposit, nu040_join, Out.branches, cross] at h
  | timedOut j => simp [deposit, nu040_join, Out.findTimeout] at h

/-- The dead-letter's only outcome writes `budget` and `dead`. -/
theorem nu040_dl_dep {reap : Bool} {f : Nat → Nat} {ch d}
    (h : deposit f (nu040_dl reap).base.out ch = some d) : d = [0, 5] := by
  cases ch with
  | action i =>
    cases i with
    | zero => simpa [deposit, nu040_dl, Out.branches, cross] using h.symm
    | succ i => simp [deposit, nu040_dl, Out.branches, cross] at h
  | timedOut j => simp [deposit, nu040_dl, Out.findTimeout] at h

/-- The fork takes a budget token and adds one token to `a`, `b` and `pending`. -/
theorem nu040_fork_effect {M M' : QMarking Nat (Stamped Nat)} {c δ e}
    (hf : RefNuFire nu040_fork M c δ e M') :
    qCount M' 0 + 1 = qCount M 0 ∧ qCount M' 1 = qCount M 1 + 1 ∧
      qCount M' 2 = qCount M 2 + 1 ∧ qCount M' 3 = qCount M 3 + 1 := by
  have hk : ∀ p ms, nu040_fork.mspec = some ms → keyAt ms p = none := by
    intro p ms hms; simp [nu040_fork] at hms
  have hr : ∀ p, p ∉ nu040_fork.base.core.resets := by simp [nu040_fork]
  obtain ⟨-, hen, f, ch, hdep⟩ := refNuFire_unkeyed hf (hk 0) (hr 0)
  have hd := nu040_fork_dep hdep
  have hen' : 1 ≤ qCount M 0 := by
    simpa [Enabled, enabledNA, nu040_fork, Card.required] using hen
  have c0 := refNuFire_unkeyed_count hf (hk 0) (hr 0)
  have c1 := refNuFire_unkeyed_count hf (hk 1) (hr 1)
  have c2 := refNuFire_unkeyed_count hf (hk 2) (hr 2)
  have c3 := refNuFire_unkeyed_count hf (hk 3) (hr 3)
  have t0 : qTake M nu040_fork.base 0 = 1 := rfl
  have t1 : qTake M nu040_fork.base 1 = 0 := rfl
  have t2 : qTake M nu040_fork.base 2 = 0 := rfl
  have t3 : qTake M nu040_fork.base 3 = 0 := rfl
  rw [hd, t0] at c0; rw [hd, t1] at c1; rw [hd, t2] at c2; rw [hd, t3] at c3
  simp at c0 c1 c2 c3
  omega

/-- The dead-letter takes one token from `a`, `b` and `pending` and returns a budget token. -/
theorem nu040_dl_effect {reap : Bool} {M M' : QMarking Nat (Stamped Nat)} {c δ e}
    (hf : RefNuFire (nu040_dl reap) M c δ e M') :
    qCount M' 0 = qCount M 0 + 1 ∧ qCount M' 1 + 1 = qCount M 1 ∧
      qCount M' 2 + 1 = qCount M 2 ∧ qCount M' 3 + 1 = qCount M 3 := by
  have hk : ∀ p ms, (nu040_dl reap).mspec = some ms → keyAt ms p = none := by
    intro p ms hms; simp [nu040_dl] at hms
  have hr : ∀ p, p ∉ (nu040_dl reap).base.core.resets := by simp [nu040_dl]
  obtain ⟨-, hen, f, ch, hdep⟩ := refNuFire_unkeyed hf (hk 0) (hr 0)
  have hd := nu040_dl_dep hdep
  have hen' : 1 ≤ qCount M 1 ∧ 1 ≤ qCount M 2 ∧ 1 ≤ qCount M 3 := by
    simpa [Enabled, enabledNA, nu040_dl, Card.required] using hen
  have c0 := refNuFire_unkeyed_count hf (hk 0) (hr 0)
  have c1 := refNuFire_unkeyed_count hf (hk 1) (hr 1)
  have c2 := refNuFire_unkeyed_count hf (hk 2) (hr 2)
  have c3 := refNuFire_unkeyed_count hf (hk 3) (hr 3)
  have t0 : qTake M (nu040_dl reap).base 0 = 0 := rfl
  have t1 : qTake M (nu040_dl reap).base 1 = 1 := rfl
  have t2 : qTake M (nu040_dl reap).base 2 = 1 := rfl
  have t3 : qTake M (nu040_dl reap).base 3 = 1 := rfl
  rw [hd, t0] at c0; rw [hd, t1] at c1; rw [hd, t2] at c2; rw [hd, t3] at c3
  simp at c0 c1 c2 c3
  omega

/-- The join takes one token of its chosen name from `a` and from `b` (the name is eligible, so
each holds one), one `pending` token, and returns a budget token. -/
theorem nu040_join_effect {M M' : QMarking Nat (Stamped Nat)} {c δ e}
    (hf : RefNuFire nu040_join M c δ e M') :
    qCount M' 0 = qCount M 0 + 1 ∧ qCount M' 1 + 1 = qCount M 1 ∧
      qCount M' 2 + 1 = qCount M 2 ∧ qCount M' 3 + 1 = qCount M 3 := by
  have hk : ∀ p, p = 0 ∨ p = 3 → ∀ ms, nu040_join.mspec = some ms → keyAt ms p = none := by
    intro p hp ms hms
    simp only [nu040_join, Option.some.injEq] at hms
    subst hms
    rcases hp with rfl | rfl <;> rfl
  have hr : ∀ p, p ∉ nu040_join.base.core.resets := by simp [nu040_join]
  obtain ⟨-, hen, f, ch, hdep⟩ := refNuFire_unkeyed hf (hk 0 (Or.inl rfl)) (hr 0)
  have hd := nu040_join_dep hdep
  have hen' : 1 ≤ qCount M 3 := by
    have := hen; simp [Enabled, enabledNA, nu040_join, Card.required] at this; exact this.2.2
  have c0 := refNuFire_unkeyed_count hf (hk 0 (Or.inl rfl)) (hr 0)
  have c3 := refNuFire_unkeyed_count hf (hk 3 (Or.inr rfl)) (hr 3)
  have t0 : qTake M nu040_join.base 0 = 0 := rfl
  have t3 : qTake M nu040_join.base 3 = 1 := rfl
  rw [hd, t0] at c0; rw [hd, t3] at c3
  simp at c0 c3
  -- the correlated inputs
  obtain ⟨n, -, hs, -, ⟨ch', hdep'⟩, -, -, rfl⟩ := (refNuFire_matched rfl M c δ e M').1 hf
  have hd' := nu040_join_dep hdep'
  have hel := (refSelect_eq_some_iff.1 hs).1
  have s1 := nu040_stamps_length nu040_key n (M 1)
  have s2 := nu040_stamps_length nu040_key n (M 2)
  simp only [eligible, matchIn, nu040_ms, List.map_cons, List.map_nil, List.isEmpty_cons,
    Bool.not_false, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, Bool.and_eq_true,
    decide_eq_true_eq, s1, s2] at hel
  have l1 : (named nu040_key n (M 1)).length ≤ (M 1).length := List.length_filter_le _ _
  have l2 : (named nu040_key n (M 2)).length ≤ (M 2).length := List.length_filter_le _ _
  have k1 : Card.one.consumesAll = false := rfl
  have k2 : Card.one.required = 1 := rfl
  have e1 : qCount (qAppend (nuConsume nu040_ms nu040_join M n) e) 1 =
      (M 1).length - min 1 (named nu040_key n (M 1)).length := by
    simp [qCount, qAppend_apply, qEmittedTo_length, hd', nuConsume, nu040_join, nuPost, keyAt,
      nu040_ms, corrTake, nspecAt, consumptionCount, nu040_dropNamed_length, k1, k2]
  have e2 : qCount (qAppend (nuConsume nu040_ms nu040_join M n) e) 2 =
      (M 2).length - min 1 (named nu040_key n (M 2)).length := by
    simp [qCount, qAppend_apply, qEmittedTo_length, hd', nuConsume, nu040_join, nuPost, keyAt,
      nu040_ms, corrTake, nspecAt, consumptionCount, nu040_dropNamed_length, k1, k2]
  simp only [qCount] at e1 e2 c0 c3 hen' ⊢
  omega

/-- The invariant of the scatter-gather net from `k` budget tokens: `budget + pending = k`, and
each branch place holds as many tokens as `pending`. -/
def nu040_inv (k : Nat) (M : QMarking Nat (Stamped Nat)) : Prop :=
  qCount M 0 + qCount M 3 = k ∧ qCount M 1 = qCount M 3 ∧ qCount M 2 = qCount M 3

/-- Every firing of the scatter-gather net keeps the invariant: the fork moves a budget token to
`pending` and adds a branch token to `a` and `b`; the join and the dead-letter undo that. -/
theorem nu040_step_inv {k : Nat} {M M' : QMarking Nat (Stamped Nat)}
    (h : RefNuStep nu040_net M M') (hi : nu040_inv k M) : nu040_inv k M' := by
  obtain ⟨t, ht, c, δ, e, hf⟩ := h
  simp only [nu040_net, List.mem_cons, List.not_mem_nil, or_false] at ht
  unfold nu040_inv at hi ⊢
  rcases ht with rfl | rfl | rfl
  · have := nu040_fork_effect hf; omega
  · have := nu040_join_effect hf; omega
  · have := nu040_dl_effect hf; omega

/-- AC1 worked out: from `k` budget tokens, every marking the reference ν firing reaches on the
scatter-gather net holds `budget + pending = k`, and `a` and `b` hold as many tokens as
`pending`. So `PlaceBound(Budget, k)` and `PlaceBound(Pending, k)` hold, the branch places are
bounded by `k` too, and at most `k` groups are live (have a `pending` token) at once. -/
@[evidence cites "NU-040" "AC1 and the second half of AC2 on the scatter-gather net: with Budget(k), a fork gated on a Budget input, a matched join and a dead-letter that return the budget token, every marking the reference ν firing reaches holds budget + pending = k, so PlaceBound(Budget, k) and PlaceBound(Pending, k) hold"]
theorem NU_040_ac1 (k : Nat) {M : QMarking Nat (Stamped Nat)}
    (h : RefNuReach nu040_net (nu040_M0 k) M) :
    nu040_inv k M ∧ qCount M 0 ≤ k ∧ qCount M 3 ≤ k ∧ qCount M 1 ≤ k ∧ qCount M 2 ≤ k := by
  have : nu040_inv k M := by
    induction h with
    | refl => simp [nu040_inv, nu040_M0, qCount]
    | tail _ hs ih => exact nu040_step_inv hs ih
  obtain ⟨h0, h1, h2⟩ := this
  exact ⟨⟨h0, h1, h2⟩, by omega, by omega, by omega, by omega⟩

/-- AC2 worked out: on the scatter-gather net, a reachable marking at which `pending` holds a
token also holds a token in `a` and in `b`, so the (immediate, not reapable) dead-letter is
enabled and the marking does not rest. Every reachable rest has `pending = 0`, and
`JoinedOrDeadLettered(pending)` is never violated. -/
@[evidence cites "NU-040" "AC2 on the scatter-gather net: every forked group is joined or dead-lettered, so pending is empty at every reachable quiescent marking and JoinedOrDeadLettered(pending) holds"]
theorem NU_040_ac2 (k : Nat) (sinks : List Nat) {M : QMarking Nat (Stamped Nat)}
    (h : RefNuReach nu040_net (nu040_M0 k) M) :
    (NuRests nu040_net M → M 3 = []) ∧ ¬ refJodl nu040_net sinks 3 M := by
  obtain ⟨⟨-, h1, h2⟩, -⟩ := NU_040_ac1 k h
  have key : NuRests nu040_net M → M 3 = [] := by
    intro hr
    by_contra hne
    have hp : 1 ≤ qCount M 3 := List.length_pos_iff.2 hne
    have hen : NuEnabled (nu040_dl false) M := by
      refine (nuEnabled_of_none rfl M).2 ?_
      have : 1 ≤ qCount M 1 ∧ 1 ≤ qCount M 2 ∧ 1 ≤ qCount M 3 := by omega
      simpa [Enabled, enabledNA, nu040_dl, Card.required] using this
    have := hr (nu040_dl false) (by simp [nu040_net]) hen
    simp [nu040_dl] at this
  exact ⟨key, fun ⟨hr, hp⟩ => hp (key hr)⟩

/-! ## A stranded group: the fork does not keep the mint contract -/

/-- The fork and the join, without the dead-letter. -/
def nu040_noDl : List (NuTrans Nat (KeyFn Nat Nat)) := [nu040_fork, nu040_join]

/-- What a fork that breaks the mint contract emits: name 0 into `a`, name 1 into `b`, and a
`pending` token. -/
def nu040_badEmit : List (Nat × Stamped Nat) := [(1, nu040_tok 0), (2, nu040_tok 1), (3, nu040_tok 7)]

/-- The marking after that fork fires once from one budget token. -/
def nu040_stranded : QMarking Nat (Stamped Nat) := qFire (nu040_M0 1) nu040_fork.base nu040_badEmit

/-- From one budget token, the fork reaches the stranded marking. -/
theorem nu040_reach_stranded : RefNuReach nu040_noDl (nu040_M0 1) nu040_stranded := by
  refine Relation.ReflTransGen.single ⟨nu040_fork, by simp [nu040_noDl], none,
    qDelivered (nu040_M0 1) nu040_fork.base, nu040_badEmit, ?_⟩
  refine (refNuFire_restrictsTo nu040_fork rfl _ _ _ _ _).2 ⟨rfl, by decide, ⟨.action 0, rfl⟩,
    rfl, rfl⟩

/-- At the stranded marking no name is in both branches, so the join is not ν-enabled, although
it is enabled on its counts. -/
theorem nu040_stranded_join :
    ¬ NuEnabled nu040_join nu040_stranded ∧ Enabled nu040_join.base (qCount nu040_stranded) := by
  refine ⟨fun ⟨_, h⟩ => ?_, by decide⟩
  obtain ⟨n, hn⟩ := h nu040_ms rfl
  have hs := (refSelect_spec (matchIn nu040_ms nu040_join nu040_stranded)).2 ⟨n, hn⟩
  have h0 : refSelect (matchIn nu040_ms nu040_join nu040_stranded) = none := by decide
  rw [h0] at hs
  cases hs

/-- The stranded marking rests on the fork and the join: the fork has no budget token and the
join has no name. -/
theorem nu040_stranded_rests : NuRests nu040_noDl nu040_stranded := by
  intro t ht hen
  simp only [nu040_noDl, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · have := (nuEnabled_of_none rfl _).1 hen
    exact absurd this (by decide)
  · exact absurd hen nu040_stranded_join.1

/-! ## A stranded group: two forks that each keep the mint contract -/

/-- Fork `mA` takes a budget token and mints one name into `a` and a `pending` token. -/
def nu040_mA : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "mA", inputs := [⟨0, .one⟩], inhibitors := [], reads := [],
                        resets := [] },
              out := some (.and (.place 1) (.place 3)) } }

/-- Fork `mB` takes a request token (place 6) and mints one name into `b`. -/
def nu040_mB : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "mB", inputs := [⟨6, .one⟩], inhibitors := [], reads := [],
                        resets := [] },
              out := some (.place 2) } }

/-- The two forks and the join, without a dead-letter. -/
def nu040_twoForks : List (NuTrans Nat (KeyFn Nat Nat)) := [nu040_mA, nu040_mB, nu040_join]

/-- One budget token and one request token. -/
def nu040_M0two : QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [nu040_tok 0] else if p = 6 then [nu040_tok 0] else []

/-- After `mA` mints name 0 (with its `pending` token, name 7). -/
def nu040_afterA : QMarking Nat (Stamped Nat) :=
  qFire nu040_M0two nu040_mA.base [(1, nu040_tok 0), (3, nu040_tok 7)]

/-- After `mB` then mints name 1: each fork wrote one fresh name, and the names differ. -/
def nu040_strandedTwo : QMarking Nat (Stamped Nat) :=
  qFire nu040_afterA nu040_mB.base [(2, nu040_tok 1)]

/-- The two forks reach the stranded marking, each minting one fresh name. -/
theorem nu040_reach_strandedTwo : RefNuReach nu040_twoForks nu040_M0two nu040_strandedTwo := by
  refine Relation.ReflTransGen.tail (b := nu040_afterA) (Relation.ReflTransGen.single ?_) ?_
  · exact ⟨nu040_mA, by simp [nu040_twoForks], none, qDelivered nu040_M0two nu040_mA.base,
      [(1, nu040_tok 0), (3, nu040_tok 7)],
      (refNuFire_restrictsTo nu040_mA rfl _ _ _ _ _).2 ⟨rfl, by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩⟩
  · exact ⟨nu040_mB, by simp [nu040_twoForks], none, qDelivered nu040_afterA nu040_mB.base,
      [(2, nu040_tok 1)],
      (refNuFire_restrictsTo nu040_mB rfl _ _ _ _ _).2 ⟨rfl, by decide, ⟨.action 0, rfl⟩, rfl, rfl⟩⟩

/-- The two-fork stranded marking rests: neither fork has an input token, and the join is enabled
on its counts but has no name in both branches. -/
theorem nu040_strandedTwo_rests :
    NuRests nu040_twoForks nu040_strandedTwo ∧
      Enabled nu040_join.base (qCount nu040_strandedTwo) := by
  refine ⟨fun t ht hen => ?_, by decide⟩
  simp only [nu040_twoForks, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact absurd ((nuEnabled_of_none rfl _).1 hen) (by decide)
  · exact absurd ((nuEnabled_of_none rfl _).1 hen) (by decide)
  · obtain ⟨_, h⟩ := hen
    obtain ⟨n, hn⟩ := h nu040_ms rfl
    have hs := (refSelect_spec (matchIn nu040_ms nu040_join nu040_strandedTwo)).2 ⟨n, hn⟩
    have h0 : refSelect (matchIn nu040_ms nu040_join nu040_strandedTwo) = none := by decide
    rw [h0] at hs
    cases hs

/-- ✓ Worked example. Fork `mA` takes the one budget token and mints name 0 into branch `a` with a
`pending` token; fork `mB` mints name 1 into branch `b`. Each fork keeps the mint contract, yet
the join is enabled on its token counts and no name is in both branches. The marking rests,
`pending` holds a token, and `JoinedOrDeadLettered(pending)` is violated there, also when `done`
is declared a sink. On the scatter-gather net with a dead-letter transition, no reachable marking
violates the property. -/
@[evidence nonvacuous NU_040_jodl]
theorem NU_040_jodl_nonvacuous :
    RefNuReach nu040_twoForks nu040_M0two nu040_strandedTwo ∧
      refJodl nu040_twoForks [4] 3 nu040_strandedTwo ∧
      Enabled nu040_join.base (qCount nu040_strandedTwo) ∧
      ∀ M, RefNuReach nu040_net (nu040_M0 1) M → ¬ refJodl nu040_net [] 3 M :=
  ⟨nu040_reach_strandedTwo, ⟨nu040_strandedTwo_rests.1, by decide⟩, nu040_strandedTwo_rests.2,
    fun _ h => (NU_040_ac2 1 [] h).2⟩

/-- A read-only gate: it reads budget place 0, takes a request token (place 9) and writes branch
`a`. -/
def nu040_gate : Trans Nat :=
  { core := { name := "gate", inputs := [⟨9, .one⟩], inhibitors := [], reads := [0], resets := [] }
    out := some (.place 1) }

/-- ✓ Worked example. With budget place 0 declared, the fork, which takes a budget token, is a
declared mint although no mint is named; the join, which only returns a budget token, is not;
a gate that only reads the budget place is not; without the budget declaration the fork is not a
mint either; and a named fork is a mint whatever budget places are declared. -/
@[evidence nonvacuous NU_040_mint]
theorem NU_040_mint_nonvacuous :
    nu040DeclaredMint [0] [] nu040_fork.base = true ∧
      nu040DeclaredMint [0] [] nu040_join.base = false ∧
      nu040DeclaredMint [0] [] nu040_gate = false ∧
      nu040DeclaredMint [] [] nu040_fork.base = false ∧
      nu040DeclaredMint [0] ["mB"] nu040_mB.base = true := by
  decide

/-! ## Forbidden models, one per load-bearing part of a line -/

/-- A declaration that ignores budget places: only the explicitly named transitions are
mints. -/
def nu040_explicitOnly : List Nat → List String → Trans Nat → Bool :=
  fun _ explicit t => explicit.contains t.core.name

/-- ✗ Worked example: with place 0 declared as a budget place and no mint named, the fork takes a
budget token, so the first line makes it a declared mint; the explicit-only declaration does
not. -/
@[evidence forbids NU_040_mint]
theorem NU_040_mint_forbids_explicitOnly : ¬ NU_040_mint nu040_explicitOnly := by
  intro h
  have := h.1 [0] [] nu040_fork.base ⟨⟨0, .one⟩, by simp [nu040_fork], by simp⟩
  exact absurd this (by decide)

/-- A declaration that reads only the first input arc of a transition. -/
def nu040_firstArcOnly : List Nat → List String → Trans Nat → Bool :=
  fun budgets explicit t => explicit.contains t.core.name ||
    (t.core.inputs.head?.map fun s => budgets.contains s.place).getD false

/-- ✗ Worked example: a fork whose budget arc is its second input (after a request place 9) takes
a budget token, so the first line makes it a declared mint; reading only the first arc misses
it. -/
@[evidence forbids NU_040_mint]
theorem NU_040_mint_forbids_firstArcOnly : ¬ NU_040_mint nu040_firstArcOnly := by
  intro h
  let t : Trans Nat :=
    { core := { name := "fork", inputs := [⟨9, .one⟩, ⟨0, .one⟩], inhibitors := [], reads := [],
                resets := [] }
      out := none }
  have := h.1 [0] [] t ⟨⟨0, .one⟩, by simp [t], by simp⟩
  exact absurd this (by decide)

/-- A declaration that makes every transition a mint. -/
def nu040_everyMint : List Nat → List String → Trans Nat → Bool := fun _ _ _ => true

/-- ✗ Worked example: with place 0 declared and no mint named, the join only returns a budget
token, so the third line keeps it from being a declared mint; the every-mint declaration makes it
one, and a route would read its writes as fresh names. -/
@[evidence forbids NU_040_mint]
theorem NU_040_mint_forbids_everyMint : ¬ NU_040_mint nu040_everyMint := by
  intro h
  have := h.2.2 [0] [] nu040_join.base rfl
  exact absurd this (by decide)

/-- The declaration the reverse index "place to the transitions it affects" would give: an
input, read or inhibitor arc on a budget place makes a transition a mint. -/
def nu040_anyArc {N : Type} [DecidableEq N] (budgets : List N) (explicit : List String)
    (t : Trans N) : Bool :=
  explicit.contains t.core.name || t.core.inputs.any (fun s => budgets.contains s.place) ||
    t.core.reads.any budgets.contains || t.core.inhibitors.any budgets.contains

/-- A declaration in which the budget places replace the named mints: once a budget place is
declared, only the transitions that take its token are mints. -/
def nu040_replacing {N : Type} [DecidableEq N] (budgets : List N) (explicit : List String)
    (t : Trans N) : Bool :=
  if budgets.isEmpty then explicit.contains t.core.name
  else t.core.inputs.any fun s => budgets.contains s.place

/-! ## Mutants: the mint block without one of its lines -/

/-- NU_040_mint without its third line: a transition may be a mint for other reasons. -/
def NU_040_mint_mutant_noOnlyWhen {N : Type} [DecidableEq N]
    (DM : List N → List String → Trans N → Bool) : Prop :=
  (∀ budgets explicit (t : Trans N),
    (∃ s ∈ t.core.inputs, s.place ∈ budgets) → DM budgets explicit t = true) ∧
  (∀ budgets explicit (t : Trans N), t.core.name ∈ explicit → DM budgets explicit t = true)

/-- ✗ Worked example: the reverse-index declaration makes every named transition and every
budget consumer a mint, so it meets the first two lines. It also makes the read-only gate a mint:
with place 0 declared and no mint named, the gate copies whatever its request carries into `a`,
and a route would trust that copy as a fresh name. The third line forbids it, so the third line is
load-bearing. -/
@[evidence mutant NU_040_mint]
theorem NU_040_mint_mutant_noOnlyWhen_killed :
    NU_040_mint_mutant_noOnlyWhen (nu040_anyArc (N := Nat)) ∧ ¬ NU_040_mint (nu040_anyArc (N := Nat)) := by
  refine ⟨⟨fun b e t ⟨s, hs, hb⟩ => ?_, fun b e t h => ?_⟩, fun h => ?_⟩
  · simp only [nu040_anyArc, Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem]
    exact Or.inl (Or.inl (Or.inr ⟨s, hs, hb⟩))
  · simp only [nu040_anyArc, Bool.or_eq_true, List.contains_iff_mem]
    exact Or.inl (Or.inl (Or.inl h))
  · have := h.2.2 [0] [] nu040_gate (by decide)
    revert this
    decide

/-- NU_040_mint without its second line: the budget declaration may replace the named mints. -/
def NU_040_mint_mutant_noAlso {N : Type} [DecidableEq N]
    (DM : List N → List String → Trans N → Bool) : Prop :=
  (∀ budgets explicit (t : Trans N),
    (∃ s ∈ t.core.inputs, s.place ∈ budgets) → DM budgets explicit t = true) ∧
  (∀ budgets explicit (t : Trans N), DM budgets explicit t = true →
    t.core.name ∈ explicit ∨ ∃ s ∈ t.core.inputs, s.place ∈ budgets)

/-- ✗ Worked example: the replacing declaration marks a budget consumer as a mint and marks
nothing else, so it meets the first and third lines. With budget place 0 declared and fork `mB`
named as a mint, `mB` takes no budget token and the replacing declaration drops it, so a route
would read its fresh name as a copy. The second line forbids it, so the second line is
load-bearing. -/
@[evidence mutant NU_040_mint]
theorem NU_040_mint_mutant_noAlso_killed :
    NU_040_mint_mutant_noAlso (nu040_replacing (N := Nat)) ∧ ¬ NU_040_mint (nu040_replacing (N := Nat)) := by
  refine ⟨⟨fun b e t ⟨s, hs, hb⟩ => ?_, fun b e t h => ?_⟩, fun h => ?_⟩
  · have hne : b.isEmpty = false := by
      cases b with
      | nil => simp at hb
      | cons _ _ => rfl
    simp only [nu040_replacing, hne, Bool.false_eq_true, if_false, List.any_eq_true,
      List.contains_iff_mem]
    exact ⟨s, hs, hb⟩
  · unfold nu040_replacing at h
    split at h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  · have := h.2.1 [0] ["mB"] nu040_mB.base (by simp [nu040_mB])
    exact absurd this (by decide)

/-! ## Forbidden models of `JoinedOrDeadLettered` -/

/-- The count-level reading: quiescence with "enabled" read on the token counts only. -/
def nu040_countLevel : List (NuTrans Nat (KeyFn Nat Nat)) → List Nat → Nat →
    QMarking Nat (Stamped Nat) → Prop :=
  fun X _ pending M =>
    (∀ t ∈ X, Enabled t.base (qCount M) → t.base.reapable = true) ∧ M pending ≠ []

/-- ✗ Worked example: at the two-fork stranded marking the join is enabled on its counts, so the
count-level reading finds no rest and reports nothing, although the group in `pending` can never
be joined. The first line makes it a violation. -/
@[evidence forbids NU_040_jodl]
theorem NU_040_jodl_forbids_countLevel : ¬ NU_040_jodl nu040_countLevel := by
  intro h
  obtain ⟨hq, -⟩ :=
    h.1 nu040_twoForks [] 3 nu040_strandedTwo nu040_strandedTwo_rests.1 (by decide)
  have := hq nu040_join (by simp [nu040_twoForks]) nu040_strandedTwo_rests.2
  exact absurd this (by decide)

/-- The reading with a sink clause, as `DeadlockFree` has one: a marked declared sink excuses
the marking. -/
def nu040_sinkClause : List (NuTrans Nat (KeyFn Nat Nat)) → List Nat → Nat →
    QMarking Nat (Stamped Nat) → Prop :=
  fun X sinks pending M => NuRests X M ∧ M pending ≠ [] ∧ ∀ s ∈ sinks, M s = []

/-- ✗ Worked example: at the stranded marking with branch `a` declared a sink (and marked), the
sink-clause reading excuses the stranded group. The first line makes it a violation whether or
not a sink is marked. -/
@[evidence forbids NU_040_jodl]
theorem NU_040_jodl_forbids_sinkClause : ¬ NU_040_jodl nu040_sinkClause := by
  intro h
  obtain ⟨-, -, hs⟩ := h.1 nu040_noDl [1] 3 nu040_stranded nu040_stranded_rests (by decide)
  exact absurd (hs 1 (by simp)) (by decide)

/-- The strict reading: quiescent means no transition enabled at all, reapable or not. -/
def nu040_strict : List (NuTrans Nat (KeyFn Nat Nat)) → List Nat → Nat →
    QMarking Nat (Stamped Nat) → Prop :=
  fun X _ pending M => (∀ t ∈ X, ¬ NuEnabled t M) ∧ M pending ≠ []

/-- ✗ Worked example: a reapable dead-letter (a Deadline or Window transition, [TIME-013]) is
enabled on a group with a token in each branch and a `pending` token; a late executor reaps it
and rests with it enabled. The first line makes that rest a violation; the strict reading sees no
quiescence there. -/
@[evidence forbids NU_040_jodl]
theorem NU_040_jodl_forbids_strict : ¬ NU_040_jodl nu040_strict := by
  intro h
  have hen : NuEnabled (nu040_dl true) nu040_Mg := (nuEnabled_of_none rfl _).2 (by decide)
  have hr : NuRests [nu040_dl true] nu040_Mg := by
    intro t ht _
    simp only [List.mem_singleton] at ht
    subst ht; rfl
  obtain ⟨hq, -⟩ := h.1 [nu040_dl true] [] 3 nu040_Mg hr (by decide)
  exact hq _ (by simp) hen

/-- The reading that ignores quiescence: every marking with a `pending` token violates. -/
def nu040_pendingOnly : List (NuTrans Nat (KeyFn Nat Nat)) → List Nat → Nat →
    QMarking Nat (Stamped Nat) → Prop :=
  fun _ _ pending M => M pending ≠ []

/-- ✗ Worked example: on the scatter-gather net a marking with a token in `a`, in `b` and in
`pending` does not rest, since the dead-letter is enabled and not reapable; the group is still
being handled. The second line forbids reporting it; the reading that ignores quiescence reports
it. -/
@[evidence forbids NU_040_jodl]
theorem NU_040_jodl_forbids_pendingOnly : ¬ NU_040_jodl nu040_pendingOnly := by
  intro h
  obtain ⟨hr, -⟩ := h.2 nu040_net [] 3 nu040_Mg (show nu040_Mg 3 ≠ [] by decide)
  have hen : NuEnabled (nu040_dl false) nu040_Mg := (nuEnabled_of_none rfl _).2 (by decide)
  exact absurd (hr _ (by simp [nu040_net]) hen) (by decide)

/-- The reading in which a name counts once it has one token in every correlated input,
whatever the input's required count (the Route A join test of `name_coloured_encoder.rs`,
which the runtime only uses for joins that take one token per correlated input). -/
def nu040_presentOnly : List (NuTrans Nat (KeyFn Nat Nat)) → List Nat → Nat →
    QMarking Nat (Stamped Nat) → Prop :=
  fun X _ pending M =>
    (∀ t ∈ X, (Enabled t.base (qCount M) ∧ ∀ ms, t.mspec = some ms →
        ∃ n, ms.keys.all (fun k => (M k.1).any fun x => k.2 x.val == some n) = true) →
      t.base.reapable = true) ∧ M pending ≠ []

/-- A join that takes two tokens of the name from `a`, one from `b` and one `pending` token. -/
def nu040_join2 : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "join", inputs := [⟨1, .exactly 2⟩, ⟨2, .one⟩, ⟨3, .one⟩],
                        inhibitors := [], reads := [], resets := [] },
              out := some (.and (.place 0) (.place 4)) }
    mspec := some nu040_ms }

/-- `a` holds names 1 and 2, `b` holds name 1, and a `pending` token. -/
def nu040_M2 : QMarking Nat (Stamped Nat) := fun p =>
  if p = 1 then [nu040_tok 1, nu040_tok 2] else if p = 2 then [nu040_tok 1]
  else if p = 3 then [nu040_tok 7] else []

/-- ✗ Worked example: a join takes two tokens of one name from `a` and one from `b`. With names 1
and 2 in `a` and name 1 in `b`, it holds three branch tokens, enough on its counts, but no name
has two tokens in `a`: the join is not enabled and the marking rests with a `pending` token, so
the first line makes it a violation. The reading that is content with one token of name 1 in
each branch takes the join as enabled and reports nothing. -/
@[evidence forbids NU_040_jodl]
theorem NU_040_jodl_forbids_presentOnly : ¬ NU_040_jodl nu040_presentOnly := by
  intro h
  have hr : NuRests [nu040_join2] nu040_M2 := by
    intro t ht hen
    simp only [List.mem_singleton] at ht
    subst ht
    obtain ⟨n, hn⟩ := hen.2 nu040_ms rfl
    have hs := (refSelect_spec (matchIn nu040_ms nu040_join2 nu040_M2)).2 ⟨n, hn⟩
    have h0 : refSelect (matchIn nu040_ms nu040_join2 nu040_M2) = none := by decide
    rw [h0] at hs
    cases hs
  obtain ⟨hq, -⟩ := h.1 [nu040_join2] [] 3 nu040_M2 hr (by decide)
  have hen : Enabled nu040_join2.base (qCount nu040_M2) ∧ ∀ ms, nu040_join2.mspec = some ms →
      ∃ n, ms.keys.all (fun k => (nu040_M2 k.1).any fun x => k.2 x.val == some n) = true :=
    ⟨by decide, fun ms hms => by
      simp only [nu040_join2, Option.some.injEq] at hms
      subst hms
      exact ⟨1, by decide⟩⟩
  exact absurd (hq nu040_join2 (by simp) hen) (by decide)

/-- The reading in which a match that correlates no input is enabled whenever its counts are
(the eligibility test without "at least one correlated input"). -/
def nu040_keyless : List (NuTrans Nat (KeyFn Nat Nat)) → List Nat → Nat →
    QMarking Nat (Stamped Nat) → Prop :=
  fun X _ pending M =>
    (∀ t ∈ X, (Enabled t.base (qCount M) ∧ ∀ ms, t.mspec = some ms →
        ∃ n : Nat, (matchIn ms t M).keys.all (fun k =>
          decide (1 ≤ (stamps k.1 n).length) && decide (k.2 ≤ (stamps k.1 n).length)) = true) →
      t.base.reapable = true) ∧ M pending ≠ []

/-- A matched dead-letter whose match correlates no input: it takes a `pending` token. -/
def nu040_keylessDl : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "deadLetter", inputs := [⟨3, .one⟩], inhibitors := [], reads := [],
                        resets := [] },
              out := some (.place 5) }
    mspec := some { keys := [] } }

/-- ✗ Worked example: a dead-letter carries a match that correlates no input. A match builder
refuses such a match ([NU-020]), but a path that is not a builder can make one, and it never
fires. With a `pending` token the marking rests, so the first line makes it a violation. The
reading that drops "at least one correlated input" takes the dead-letter as enabled and reports
nothing. -/
@[evidence forbids NU_040_jodl]
theorem NU_040_jodl_forbids_emptyMatch : ¬ NU_040_jodl nu040_keyless := by
  intro h
  let M : QMarking Nat (Stamped Nat) := fun p => if p = 3 then [nu040_tok 7] else []
  have hr : NuRests [nu040_keylessDl] M := by
    intro t ht hen
    simp only [List.mem_singleton] at ht
    subst ht
    obtain ⟨n, hn⟩ := hen.2 _ rfl
    simp [eligible, matchIn] at hn
  obtain ⟨hq, -⟩ := h.1 [nu040_keylessDl] [] 3 M hr (by decide)
  have hen : Enabled nu040_keylessDl.base (qCount M) ∧ ∀ ms, nu040_keylessDl.mspec = some ms →
      ∃ n : Nat, (matchIn ms nu040_keylessDl M).keys.all (fun k =>
        decide (1 ≤ (stamps k.1 n).length) && decide (k.2 ≤ (stamps k.1 n).length)) = true :=
    ⟨by decide, fun ms hms => by
      simp only [nu040_keylessDl, Option.some.injEq] at hms
      subst hms
      exact ⟨0, by simp [matchIn]⟩⟩
  exact absurd (hq nu040_keylessDl (by simp) hen) (by decide)

/-! ## Mutants: the JoinedOrDeadLettered block without one of its lines -/

/-- NU_040_jodl without its first line: a route may leave a stranded group unreported. -/
def NU_040_jodl_mutant_mayMiss {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]
    (PS : List (NuTrans N (KeyFn V Nm)) → List N → N → QMarking N (Stamped V) → Prop) : Prop :=
  ∀ X sinks pending M, PS X sinks pending M → NuRests X M ∧ M pending ≠ []

/-- ✗ Worked example: the count-level reading reports only markings that rest and hold a
`pending` token (count-level rest implies the ν rest), so it meets the second line; it misses
the stranded group, so it is not NU_040_jodl. The first line is load-bearing. -/
@[evidence mutant NU_040_jodl]
theorem NU_040_jodl_mutant_mayMiss_killed :
    NU_040_jodl_mutant_mayMiss nu040_countLevel ∧ ¬ NU_040_jodl nu040_countLevel := by
  refine ⟨fun X _ _ M ⟨hq, hp⟩ => ⟨fun t ht hen => hq t ht hen.1, hp⟩,
    NU_040_jodl_forbids_countLevel⟩

/-- NU_040_jodl without its second line: a route may report a marking that does not rest. -/
def NU_040_jodl_mutant_mayOverReport {N V Nm : Type} [DecidableEq N] [LinearOrder Nm]
    (PS : List (NuTrans N (KeyFn V Nm)) → List N → N → QMarking N (Stamped V) → Prop) : Prop :=
  ∀ X sinks pending M, NuRests X M → M pending ≠ [] → PS X sinks pending M

/-- ✗ Worked example: the reading that ignores quiescence reports every rest with a `pending`
token, so it meets the first line; it also reports a group the dead-letter is still handling,
so it is not NU_040_jodl. The second line is load-bearing. -/
@[evidence mutant NU_040_jodl]
theorem NU_040_jodl_mutant_mayOverReport_killed :
    NU_040_jodl_mutant_mayOverReport nu040_pendingOnly ∧ ¬ NU_040_jodl nu040_pendingOnly :=
  ⟨fun _ _ _ _ _ hp => hp, NU_040_jodl_forbids_pendingOnly⟩

end Libpetri.Spec
