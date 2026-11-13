import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Spec.Glossary
import Libpetri.Reference.Link

set_option linter.missingDocs true

/-!
# VER-001: SMT Verification Pipeline (`spec/07-verification.md`)

Every route of the verifier reads one net and one expansion of its transitions. VER-001 fixes
both, as two functions, so the requirement is a predicate over a pair `(V, X)`:

* `V : VerifiedNetFn N`, the verified net: `V net m0` is the net verification runs for the net
  `net` and the initial marking `m0` (a `Seam.NMarking`, the shipped `MarkingState`: each marked
  place once, with a non-zero count, in the order the marking lists them);
* `X : ExpandFn N`, the expansion into virtual transitions: `X t` is the list of `t`'s virtual
  transitions, each a name and a deposit, or `none` when `t` has no expansion.

The witness pair is `refVerifiedNet` (`smt_verifier.rs` `inert_places_net`) and `refVirtual`
(`branch_outcomes.rs` `outcomes` with the names of `net_flattener.rs` `flatten`). The rows of the
expansion are read on the reference outcome rule (`Reference.deposit` over
`ForwardDeposit.Choice`): the action branches in enumeration order, then the timeout outcome
when it deposits differently from every branch. `VER_001_rows_are_outcomes` shows that the rows
are exactly the ways a reference firing can end, from any marking.

The statement is checked against the witness pair (`VER_001_reference`), and against twelve wrong
models: a verified net that drops the stray place, one that puts it first, one that lists two
stray places in reverse marking order, one that loses the transitions, an expansion without the
timeout row (the pre-fix flattener), one whose timeout row forwards one token per
`ForwardInput`, one that adds the timeout row even when a branch deposits the same, one that gives a transition with no output spec no row, one that reverses the branch
order, one that puts the timeout row first, one that names every row `<t>_b<i>`, and one that
gives a drained forward a row with a fixed count.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## The model -/

/-- A verified-net function: `V net m0` is the net verification runs for the net `net` and the
initial marking `m0`. -/
abbrev VerifiedNetFn (N : Type) : Type := Reference.Net N → NMarking N → Reference.Net N

/-- A virtual transition: its name and its deposit, a list of places with repetition. -/
abbrev VirtualRow (N : Type) : Type := String × List N

/-- An expansion: `X t` lists the virtual transitions of `t`, or is `none` when `t` has no
expansion. -/
abbrev ExpandFn (N : Type) : Type := Reference.Trans N → Option (List (VirtualRow N))

variable {N : Type} [DecidableEq N]

/-- The required count of `t`'s input arc on `p` (`requiredCount`), 0 when `p` has no input arc:
what a `ForwardInput` from `p` deposits on the timeout outcome when the arc is `One` or
`Exactly(n)` (`branch_outcomes.rs` `forward_deposit`). -/
def timeoutRequired (t : Trans N) (p : N) : Nat :=
  match nspecAt t.core p with
  | none => 0
  | some s => requiredCount s.card

/-- **A drained forward**: the child of `t`'s `Timeout` forwards an `All` or `AtLeast` input
(`branch_outcomes.rs` `drained_forward`, `Deposit::Drained`). Its deposit is the drained batch,
which no fixed count holds. -/
def DrainedForward (t : Trans N) : Prop :=
  ∃ o c, t.out = some o ∧ o.findTimeout = some c ∧
    ∃ src ∈ forwardSources c, ∃ s, nspecAt t.core src = some s ∧ s.card.consumesAll = true

/-- The name of the `i`-th of `k` virtual transitions of the transition named `name`: the name
itself when `k = 1`, `<name>_b<i>` otherwise (`net_flattener.rs` `flatten`). -/
def virtualName (name : String) (k i : Nat) : String :=
  if k = 1 then name else name ++ "_b" ++ toString i

/-! ## The reference -/

/-- **The reference verified net** (`inert_places_net`): the declared places, then every place
the initial marking marks that the net does not declare, in the marking's order; the
transitions unchanged, so the added places carry no arc. -/
def refVerifiedNet : VerifiedNetFn N := fun net m0 =>
  { places := net.places ++ m0.places.filter (fun p => p ∉ net.places)
    transitions := net.transitions }

/-- The action rows of `t`: its output branches in enumeration order, or the one empty deposit
of a transition with no output spec. -/
def ver001_actionRows (t : Trans N) : List (List N) :=
  match t.out with
  | none => [[]]
  | some o => o.branches

/-- The timeout row of `t`: the timeout outcome at the required counts, unless an action row
deposits the same per place (`if !result.contains(&outcome)`). -/
def ver001_timeoutRows (t : Trans N) : List (List N) :=
  match deposit (timeoutRequired t) t.out (.timedOut 0) with
  | none => []
  | some d => if (ver001_actionRows t).any (fun b => b.isPerm d) then [] else [d]

/-- The reference rows (`branch_outcomes.rs` `outcomes`). -/
def refVirtualRows (t : Trans N) : List (List N) := ver001_actionRows t ++ ver001_timeoutRows t

/-- `rows` with the names `flatten` gives them. -/
def ver001_labelRows (name : String) (rows : List (List N)) : List (VirtualRow N) :=
  ((List.range rows.length).map (virtualName name rows.length)).zip rows

/-- `DrainedForward`, as a `Bool`. -/
def ver001_drainedB (t : Trans N) : Bool :=
  match t.out with
  | none => false
  | some o =>
    match o.findTimeout with
    | none => false
    | some c => (forwardSources c).any fun src =>
        match nspecAt t.core src with
        | none => false
        | some s => s.card.consumesAll

theorem ver001_drainedB_iff (t : Trans N) : ver001_drainedB t = true ↔ DrainedForward t := by
  constructor
  · intro h
    unfold ver001_drainedB at h
    split at h
    · exact absurd h Bool.false_ne_true
    · rename_i o ho
      split at h
      · exact absurd h Bool.false_ne_true
      · rename_i c hc
        obtain ⟨src, hsrc, hs⟩ := List.any_eq_true.mp h
        split at hs
        · exact absurd hs Bool.false_ne_true
        · rename_i s hspec
          exact ⟨o, c, ho, hc, src, hsrc, s, hspec, hs⟩
  · rintro ⟨o, c, ho, hc, src, hsrc, s, hs, hca⟩
    unfold ver001_drainedB
    rw [ho]
    dsimp only
    rw [hc]
    dsimp only
    exact List.any_eq_true.mpr ⟨src, hsrc, by rw [hs]; exact hca⟩

instance (t : Trans N) : Decidable (DrainedForward t) :=
  decidable_of_iff _ (ver001_drainedB_iff t)

/-- **The reference expansion**: no expansion for a drained forward, else the reference rows
with their names. -/
def refVirtual : ExpandFn N := fun t =>
  if ver001_drainedB t then none else some (ver001_labelRows t.core.name (refVirtualRows t))

#spec_witness refVerifiedNet
#spec_witness refVirtual

/-! ## VER-001: SMT Verification Pipeline -/

requirement VER_001
  id "VER-001"
  title "SMT Verification Pipeline"
  kind F
  scope "every verification route, all implementations"
  source verbatim "spec/07-verification.md"
  quote "*When* the verifier verifies a net from an initial marking, it *shall* verify the net whose places are the declared places followed by every place the initial marking marks that the net does not declare, in the order the marking lists them, and whose transitions are the net's own, with no arc added."
        "*When* the verifier expands a transition that has an output spec and no `Timeout` that forwards an `All` or `AtLeast` input, it *shall* produce one virtual transition per output branch the action may write, in enumeration order, then one virtual transition for the timeout outcome when the spec has a `Timeout` and that outcome deposits differently from every branch."
        "The verifier *shall* expand a transition with no output spec into one virtual transition that deposits nothing."
        "The virtual transition of the timeout outcome *shall* deposit one token in each place the `Timeout` child names through `Place` and, for each `ForwardInput(from, to)` of the child, as many tokens in `to` as the required count of the input on `from`."
        "The verifier *shall* name a virtual transition `<t>` when its transition `t` has one virtual transition, and `<t>_b<i>` when it is the `i`-th of several, counting from 0."
        "*If* the `Timeout` of a transition forwards an `All` or `AtLeast` input, *then* no route *shall* read an expansion of that transition into virtual transitions."
  reading "For every verified-net function V and expansion X, where X is the expansion every route reads:"
          "the places of V net m0 are the places of net followed by the places m0 marks that net does not hold, in m0's order;"
          "the transitions of V net m0 are those of net;"
          "for every transition t without a drained forward, with an output spec or without one, X t is some list of rows whose deposits, row by row and in order, put the same count in every place as acts followed by tos, where acts[i] is the deposit of the i-th action outcome (the one empty deposit when t has no output spec), and tos is empty when the timeout outcome (at the required counts) is absent or deposits the same per place as some action row, and is that one timeout deposit otherwise;"
          "whenever X t is some list rows, the names of rows are the name of t if rows has one entry, and name_b0, name_b1, ... otherwise;"
          "for every transition t with a drained forward, X t is none: there is no expansion of t for a route to read."
  assumes "A place is its name: the model's place type N is the name, and a net, a marking, a sink, a property and a forward name places through it. This is a modelling assumption of this block and not one of its lines; no quoted sentence comes from the paragraph 'Places are identified by name'. That paragraph is about how a route resolves the place a caller names (an environment place, a sink, a property's place, a terminal, a match key, a port), which is an input of the pipeline. The pipeline model (Verifier/Pipeline.lean, with the block VER_003) reads places by name throughout and states only the refusal of a property place the net does not resolve (VER_003 line 3); no block states the other resolutions, so a route that tests membership by object identity is forbidden by no line. Java's structural Place equality (CORE-002, MOD-024) does not arise for a net whose places have distinct names, as the paragraph says."
          "The initial marking is a Seam.NMarking, the shipped MarkingState: each place it marks once, with a non-zero count, in the order the builder first mentioned it. A place set to zero is not in it, so 'The same net with no token on a gets the verdict and the scripts it got before' (AC3) is line 1 with no added place: refVerifiedNet is then the net itself (VER_001_no_inert). The paragraph 'Undeclared marked places are inert places' says 'marks', as the first quoted sentence does."
          "Line 1 and line 2 are the first quoted sentence. 'In the order the marking lists them' is killed by a verified net that lists two stray places in reverse (VER_001_forbids_strayReversed), and 'followed by' by one that puts the stray place first (VER_001_forbids_inertFirst). The added places carry no arc because the transitions are the net's own (line 2), on a net that declares the places of its arcs (Seam.ArcsDeclared, which every PetriNet builder ensures). That such a place keeps its tokens forever is CORE-072's lines 3 and 4 on the executor and the reference firing rule on the verified net (an arc-less place is not changed by fireNC). That DeadlockFree counts it as stranded unless it is a declared sink and PlaceBound counts its tokens is Reference.Violates, which reads every name (checked on the AC3 net by VER_001_nonvacuous). That it is its own trivial P-invariant is VER-005's subject. The rule is what lets the flat encoder meet the Covers premise of Seam.postfix_deadlock_sound: the verified net's place index covers the initial marking (VER_001_covers)."
          "Lines 3 to 5 are the second to sixth quoted sentences. Line 3 covers the second sentence (a transition with an output spec) and the third (a transition with no output spec, whose one action outcome is the empty deposit); the fourth sentence is the timeout deposit line 3 reads, at the input's required count (timeoutRequired); a timeout row that deposits one token per ForwardInput is killed (VER_001_forbids_unitForward). The deposit of a virtual transition is a list of places with repetition, and only its count per place is normative (glossary Deposit, SamePerPlace), so line 3 relates the rows to the outcomes row by row with SamePerPlace: the order of places inside a row is free, the order of the rows is not ('in enumeration order', 'then'). The timeout outcome is read at its first alternative (Choice.timedOut 0): a Timeout child holds no Xor node (IO-013 AC8, glossary Timeout outcome), so on a transition that builds it has exactly one. The required count of a One or Exactly(n) input is what a firing consumes from it in every marking, so the rows are exactly the ways a reference firing from any marking can end (VER_001_rows_are_outcomes); the flat model of Novel/ForwardDeposit.lean states the same over flat place ids (deposit_mem_fixedRows, fixedRows_mem_deposit, both cited for VER-001)."
          "timeoutRequired is 0 for a ForwardInput whose from place has no input arc on t. A built transition has no such forward: by IO-014 AC1 and AC3 the from place must be a declared input place of the transition, validated at build time, and an invalid from reference is a build error. For a spec that is not built through the builder, IO-014 says that a forward from a place the firing consumed no token from, which a declared input cannot do but a mis-declared spec can, deposits no token in to, and the 0 is that sentence; the fourth quoted sentence speaks only of an input that exists."
          "Line 5 is the sixth quoted sentence: X is the expansion the routes read, and a drained forward has none. The Rust flattener still builds rows for such a transition, with the input's required count standing in for the drained batch, but no route reads them: the linear bound ahead of the enumeration runs only without a drained forward (smt_verifier.rs, branch_outcomes::drained_forward), and the verifier refuses the net before the first route that reads the flat net. That refusal, its place in the pipeline after the graph routes ('so no exit of the pipeline bypasses it'), and that the graph routes (VER-017, VER-010, VER-012) count the drained batch exactly (Novel/TransferRows.lean) are verifier behaviour that no block states: the pipeline model (Verifier/Pipeline.lean) has no refusal step for a drained forward, and the graph routes' exact count is Novel/TransferRows.lean, with VER_012's step for Route B (untimedBase.fire resolves drained forwards). The refusal is test evidence (Rust smt_verifier.rs a_forward_of_a_drained_input_is_decided_by_the_graph_and_refused_by_the_linear_routes). Novel.ForwardDeposit.drained_forward_has_no_row shows that no fixed row equals the drained batch."
          "'The rule applies before any route runs, so every route sees the same net' and 'Every analysis that fires a transition whose Timeout forwards no All / AtLeast input reads this one expansion' are not lines here: the routes are the verifier pipeline's, and in the block VER_003 the verified-net function abs is one parameter whose query every line reads whichever route decided, with VER-001's expansion part of it. The second is limited to transitions without a drained forward, which line 5 and the sixth quoted sentence leave without an expansion. That the scripts of a net with no added place and no new timeout row are byte for byte those it got before is VER-013's golden-script check (kind Q); the model side is VER_001_no_inert and line 3 (a timeout outcome equal to a branch adds no row)."
          "AC1 (the pipeline accepts a net, an initial marking and a property) and AC2 (it returns Proven, Violated or Unknown with supporting evidence) are the verdict contract of VER-003, the block VER_003; this block fixes the net and the expansion that contract reads."
          "AC3 (inert undeclared places) is line 1, checked on its net by VER_001_nonvacuous (the verified net of t: c to d with a stray token on a has the places c, d, a, and with stray tokens on a and b the places c, d, a, b; DeadlockFree with sink d and PlaceBound(a, 0) are violated at the initial marking); a verified net that drops the stray place is killed (VER_001_forbids_dropInert), and so are one that puts it before the declared places (VER_001_forbids_inertFirst) and one that reverses the stray places (VER_001_forbids_strayReversed). That the verdict is the same at every enumeration budget and on every route is stated by no block (VER_003 bounds each verdict and does not make two verdicts agree); it is the AC3 tests'."
          "AC4 (timeout forwards deposit per consumed token) is lines 3 and 4, checked by VER_001_nonvacuous (the AC4 transition expands into t_b0 with post c, t_b1 with post b and t_b2 with post 2 b, and its timed-out firing reaches b = 2); an expansion without the timeout row is killed (VER_001_forbids_noTimeoutRow), and so are one that adds the timeout row when a branch deposits the same, against AC4's last sentence (VER_001_forbids_noDedup), one that reverses the branches (VER_001_forbids_reversedBranches) and one that puts the timeout row first (VER_001_forbids_timeoutFirst). That the linear bound (VER-015) reads these three rows and does not prove PlaceBound(b, 1), and which routes report it Violated with which trace, are verdicts on one net, which no block states (VER_003 bounds every verdict and fixes none), kind Q."
          "AC5 (drained forwards are decided by the graphs and refused by the linear routes) is line 5 for the expansion, checked by VER_001_nonvacuous (the all(a) transition has no expansion); an expansion that gives it rows with a fixed count is killed (VER_001_forbids_fixedDrained). The verdicts at the default budget and at budget 0, the route Unavailable and the reason text are verdicts on one net, which no block states (VER_003 bounds every verdict and fixes none; the reason text is kind N); Rust smt_verifier.rs a_forward_of_a_drained_input_is_decided_by_the_graph_and_refused_by_the_linear_routes checks them."
          "The third quoted sentence is checked by VER_001_nonvacuous (t: one(a) with no output spec expands into the one row t with an empty deposit), and an expansion that gives such a transition no row is killed (VER_001_forbids_noneNoRow)."
          "The Implementation notes (the SMT route's phases in order, the CHC system as SMT-LIB2 text solved by the z3 executable, the Rust feature and the Python binding) are kind N; the phase order is stated where the spec keeps it as a requirement, on the pipeline model Verifier/Pipeline.lean (the blocks VER_015_order, VER_018_order and VER_019_order; the runtimes' step list is rtStepNames, pinned by rtStepNames_order). The test derivation's first sentence (a simple mutual exclusion net gets Proven for the mutual exclusion property) is a verdict: it belongs with AC1 and AC2 to the verdict contract of VER-003 (the block VER_003) and the MutualExclusion property of VER-002. The rest of the test derivation is AC3 to AC5, as above."
          "VER-001 is a SHOULD requirement; its shall sentences bind an implementation that verifies (ruling D22). Timing plays no part in the expansion: the timeout outcome is one way a firing can end, whatever the Timeout's duration."
  signoff "2026-11-13 d08edec1867cc96d ai"
  statement : ∀ {N : Type} [DecidableEq N], VerifiedNetFn N → ExpandFn N → Prop :=
    fun V X =>
      (∀ net m0, (V net m0).places = net.places ++ m0.places.filter (fun p => p ∉ net.places)) ∧
      (∀ net m0, (V net m0).transitions = net.transitions) ∧
      (∀ t, ¬ DrainedForward t → ∃ rows, X t = some rows ∧ ∃ acts tos,
        List.Forall₂ SamePerPlace (rows.map Prod.snd) (acts ++ tos) ∧
        (∀ i, acts[i]? = deposit (timeoutRequired t) t.out (.action i)) ∧
        ((tos = [] ∧ ∀ d, deposit (timeoutRequired t) t.out (.timedOut 0) = some d →
            ∃ b ∈ acts, SamePerPlace b d) ∨
          ∃ d, tos = [d] ∧ deposit (timeoutRequired t) t.out (.timedOut 0) = some d ∧
            ∀ b ∈ acts, ¬ SamePerPlace b d)) ∧
      (∀ t rows, X t = some rows →
        rows.map Prod.fst = (List.range rows.length).map (virtualName t.core.name rows.length)) ∧
      (∀ t, DrainedForward t → X t = none)

/- The pinned readable form of VER-001: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_001 : {N : Type} → [DecidableEq N] → VerifiedNetFn N → ExpandFn N → Prop :=
fun {N} [DecidableEq N] V X =>
  (∀ (net : Reference.Net N) (m0 : NMarking N),
      (V net m0).places = net.places ++ List.filter (fun p => decide (p ∉ net.places)) m0.places) ∧
    (∀ (net : Reference.Net N) (m0 : NMarking N), (V net m0).transitions = net.transitions) ∧
      (∀ (t : Reference.Trans N),
          ¬DrainedForward t →
            ∃ rows,
              X t = some rows ∧
                ∃ acts tos,
                  List.Forall₂ SamePerPlace (List.map Prod.snd rows) (acts ++ tos) ∧
                    (∀ (i : ℕ), acts[i]? = deposit (timeoutRequired t) t.out (Novel.ForwardDeposit.Choice.action i)) ∧
                      ((tos = [] ∧
                          ∀ (d : List N),
                            deposit (timeoutRequired t) t.out (Novel.ForwardDeposit.Choice.timedOut 0) = some d →
                              ∃ b ∈ acts, SamePerPlace b d) ∨
                        ∃ d,
                          tos = [d] ∧
                            deposit (timeoutRequired t) t.out (Novel.ForwardDeposit.Choice.timedOut 0) = some d ∧
                              ∀ b ∈ acts, ¬SamePerPlace b d)) ∧
        (∀ (t : Reference.Trans N) (rows : List (VirtualRow N)),
            X t = some rows →
              List.map Prod.fst rows = List.map (virtualName t.core.name rows.length) (List.range rows.length)) ∧
          ∀ (t : Reference.Trans N), DrainedForward t → X t = none
-/
#guard_msgs in #print VER_001

/-! ## The reference satisfies VER-001 -/

theorem ver001_samePerPlace_iff (b d : List N) : SamePerPlace b d ↔ b.isPerm d = true := by
  rw [List.isPerm_iff, List.perm_iff_count]
  rfl

omit [DecidableEq N] in
/-- The action rows are the action outcomes: `ver001_actionRows t` at `i` is the deposit of the
`i`-th action outcome. -/
theorem ver001_actionRows_getElem? (t : Trans N) (c : N → Nat) (i : Nat) :
    (ver001_actionRows t)[i]? = deposit c t.out (.action i) := by
  unfold ver001_actionRows deposit
  cases t.out with
  | none => cases i <;> rfl
  | some o => rfl

/-- The timeout row: empty when there is no timeout outcome or an action row deposits the same
per place, else the timeout deposit. -/
theorem ver001_timeoutRows_spec (t : Trans N) :
    (ver001_timeoutRows t = [] ∧ ∀ d, deposit (timeoutRequired t) t.out (.timedOut 0) = some d →
        ∃ b ∈ ver001_actionRows t, SamePerPlace b d) ∨
      ∃ d, ver001_timeoutRows t = [d] ∧ deposit (timeoutRequired t) t.out (.timedOut 0) = some d ∧
        ∀ b ∈ ver001_actionRows t, ¬ SamePerPlace b d := by
  unfold ver001_timeoutRows
  cases hd : deposit (timeoutRequired t) t.out (.timedOut 0) with
  | none => exact Or.inl ⟨rfl, fun d h => absurd h (by simp)⟩
  | some d =>
    dsimp only
    by_cases ha : (ver001_actionRows t).any (fun b => b.isPerm d) = true
    · rw [if_pos ha]
      refine Or.inl ⟨rfl, fun d' h => ?_⟩
      cases h
      obtain ⟨b, hb, hp⟩ := List.any_eq_true.mp ha
      exact ⟨b, hb, (ver001_samePerPlace_iff b d).mpr hp⟩
    · rw [if_neg ha]
      refine Or.inr ⟨d, rfl, rfl, fun b hb hs => ha ?_⟩
      exact List.any_eq_true.mpr ⟨b, hb, (ver001_samePerPlace_iff b d).mp hs⟩

omit [DecidableEq N] in
theorem ver001_labelRows_snd (name : String) (rows : List (List N)) :
    (ver001_labelRows name rows).map Prod.snd = rows := by
  unfold ver001_labelRows
  exact List.map_snd_zip (by simp)

omit [DecidableEq N] in
theorem ver001_labelRows_length (name : String) (rows : List (List N)) :
    (ver001_labelRows name rows).length = rows.length := by
  simp [ver001_labelRows]

omit [DecidableEq N] in
theorem ver001_labelRows_fst (name : String) (rows : List (List N)) :
    (ver001_labelRows name rows).map Prod.fst =
      (List.range (ver001_labelRows name rows).length).map
        (virtualName name (ver001_labelRows name rows).length) := by
  rw [ver001_labelRows_length]
  unfold ver001_labelRows
  exact List.map_fst_zip (by simp)

/-- **The reference pair satisfies VER-001.** -/
@[evidence holds VER_001]
theorem VER_001_reference : VER_001 (refVerifiedNet (N := N)) refVirtual := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro t ht
    have hb : ver001_drainedB t = false := by
      cases h : ver001_drainedB t with
      | false => rfl
      | true => exact absurd ((ver001_drainedB_iff t).mp h) ht
    refine ⟨_, by simp only [refVirtual, hb]; rfl, ver001_actionRows t, ver001_timeoutRows t,
      ?_, fun i => ver001_actionRows_getElem? t _ i, ver001_timeoutRows_spec t⟩
    rw [ver001_labelRows_snd]
    exact List.forall₂_same.mpr fun _ _ _ => rfl
  · intro t rows h
    unfold refVirtual at h
    split at h
    · exact absurd h (by simp)
    · cases h
      exact ver001_labelRows_fst _ _
  · intro t ht
    simp [refVirtual, (ver001_drainedB_iff t).mpr ht]

/-- **Line 3 fixes the rows**: whatever list of rows satisfies it has the reference deposits, in
the reference order, each up to the order of places inside it. -/
theorem VER_001_rows_unique {t : Trans N} {rows : List (VirtualRow N)} {acts tos : List (List N)}
    (hr : List.Forall₂ SamePerPlace (rows.map Prod.snd) (acts ++ tos))
    (ha : ∀ i, acts[i]? = deposit (timeoutRequired t) t.out (.action i))
    (ht : (tos = [] ∧ ∀ d, deposit (timeoutRequired t) t.out (.timedOut 0) = some d →
        ∃ b ∈ acts, SamePerPlace b d) ∨
      ∃ d, tos = [d] ∧ deposit (timeoutRequired t) t.out (.timedOut 0) = some d ∧
        ∀ b ∈ acts, ¬ SamePerPlace b d) :
    List.Forall₂ SamePerPlace (rows.map Prod.snd) (refVirtualRows t) := by
  have hacts : acts = ver001_actionRows t :=
    List.ext_getElem? fun i => by rw [ha i, ver001_actionRows_getElem?]
  subst hacts
  have htos : tos = ver001_timeoutRows t := by
    rcases ht with ⟨rfl, hno⟩ | ⟨d, rfl, hd, hne⟩
    · rcases ver001_timeoutRows_spec t with ⟨h, -⟩ | ⟨d, -, hd, hne⟩
      · exact h.symm
      · obtain ⟨b, hb, hs⟩ := hno d hd
        exact absurd hs (hne b hb)
    · rcases ver001_timeoutRows_spec t with ⟨-, hno⟩ | ⟨d', h, hd', -⟩
      · obtain ⟨b, hb, hs⟩ := hno d hd
        exact absurd hs (hne b hb)
      · rw [h]
        rw [hd] at hd'
        cases hd'
        rfl
  subst htos
  exact hr

/-- Two row lists whose first rows deposit differently somewhere are not row by row the same. -/
theorem ver001_not_forall₂_head {a b : List N} {l l' : List (List N)} (p : N)
    (h : Deposits a p ≠ Deposits b p) : ¬ List.Forall₂ SamePerPlace (a :: l) (b :: l') :=
  fun hf => h ((List.forall₂_cons.mp hf).1 p)

/-! ## The rows are the ways a reference firing can end -/

omit [DecidableEq N] in
/-- The timeout deposits read the consumed counts at the forward sources only. -/
theorem ver001_timeoutDeposits_congr {f g : N → Nat} :
    ∀ (c : Out N), (∀ src ∈ forwardSources c, f src = g src) →
      c.timeoutDeposits f = c.timeoutDeposits g
  | .place _, _ => rfl
  | .forward src _, h => by simp [Out.timeoutDeposits, h src (by simp [forwardSources])]
  | .and l r, h => by
    simp only [Out.timeoutDeposits]
    rw [ver001_timeoutDeposits_congr l (fun s hs => h s (by simp [forwardSources, hs])),
      ver001_timeoutDeposits_congr r (fun s hs => h s (by simp [forwardSources, hs]))]
  | .xor l r, h => by
    simp only [Out.timeoutDeposits]
    rw [ver001_timeoutDeposits_congr l (fun s hs => h s (by simp [forwardSources, hs])),
      ver001_timeoutDeposits_congr r (fun s hs => h s (by simp [forwardSources, hs]))]
  | .timeout c, h => by
    simp only [Out.timeoutDeposits]
    exact ver001_timeoutDeposits_congr c (fun s hs => h s (by simpa [forwardSources] using hs))

/-- Without a drained forward, the timeout outcome of a firing from any marking deposits what it
deposits at the required counts. -/
theorem ver001_deposit_timedOut {t : Trans N} (h : ¬ DrainedForward t) (m : N → Nat)
    (j : Nat) :
    deposit (Consumes t m) t.out (.timedOut j) = deposit (timeoutRequired t) t.out (.timedOut j) := by
  unfold deposit
  cases ho : t.out with
  | none => rfl
  | some o =>
    dsimp only
    cases hc : o.findTimeout with
    | none => rfl
    | some c =>
      simp only [Option.bind_some]
      rw [ver001_timeoutDeposits_congr c fun src hsrc => ?_]
      unfold Consumes nconsumed timeoutRequired
      cases hs : nspecAt t.core src with
      | none => rfl
      | some s =>
        dsimp only
        have hca : s.card.consumesAll = false := by
          cases hb : s.card.consumesAll with
          | false => rfl
          | true => exact absurd ⟨o, c, ho, hc, src, hsrc, s, hs, hb⟩ h
        simp [hca, requiredCount]

/-- **The rows of the reference expansion are exactly the ways a reference firing can end**,
from any marking, when no `Timeout` forwards an `All` / `AtLeast` input: every action outcome and
the timeout outcome deposit the same per place as some row, and every row is the deposit of one
outcome. -/
@[evidence cites "VER-001" "the virtual transitions of a transition without a drained forward are exactly the ways a reference firing from any marking can end: every action outcome and the timeout outcome (IO-013 AC5, IO-014) deposit the same per place as some row, and every row is the deposit of one outcome"]
theorem VER_001_rows_are_outcomes {t : Trans N} (h : ¬ DrainedForward t) (m : N → Nat) :
    (∀ i d, deposit (Consumes t m) t.out (.action i) = some d →
        ∃ r ∈ refVirtualRows t, SamePerPlace r d) ∧
    (∀ d, deposit (Consumes t m) t.out (.timedOut 0) = some d →
        ∃ r ∈ refVirtualRows t, SamePerPlace r d) ∧
    (∀ r ∈ refVirtualRows t, ∃ ch, deposit (Consumes t m) t.out ch = some r) := by
  refine ⟨fun i d hd => ?_, fun d hd => ?_, fun r hr => ?_⟩
  · rw [← ver001_actionRows_getElem? t (Consumes t m)] at hd
    exact ⟨d, List.mem_append_left _ (List.mem_of_getElem? hd), fun _ => rfl⟩
  · rw [ver001_deposit_timedOut h] at hd
    rcases ver001_timeoutRows_spec t with ⟨-, hno⟩ | ⟨d', h', hd', -⟩
    · obtain ⟨b, hb, hs⟩ := hno d hd
      exact ⟨b, List.mem_append_left _ hb, hs⟩
    · rw [hd] at hd'
      cases hd'
      exact ⟨d, List.mem_append_right _ (by rw [h']; exact List.mem_singleton_self d),
        fun _ => rfl⟩
  · rcases List.mem_append.mp hr with ha | ht
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
      exact ⟨.action i, by rw [← ver001_actionRows_getElem? t (Consumes t m)]; exact hi⟩
    · refine ⟨.timedOut 0, ?_⟩
      rw [ver001_deposit_timedOut h]
      rcases ver001_timeoutRows_spec t with ⟨h', -⟩ | ⟨d', h', hd', -⟩
      · rw [h'] at ht; exact absurd ht List.not_mem_nil
      · rw [h', List.mem_singleton] at ht
        rw [ht]; exact hd'

/-! ## Inert places -/

/-- **The verified net covers the initial marking**: every place `m0` marks is a place of
`refVerifiedNet net m0`. This is the `Covers` premise of `Seam.postfix_deadlock_sound`, met by
the inert-place rule (`Seam.inertNet` is the same place list). -/
@[evidence cites "VER-001" "inert undeclared places: the place index of the verified net covers the initial marking, the Covers premise of Seam.postfix_deadlock_sound that a net losing its stray token fails"]
theorem VER_001_covers (net : Reference.Net N) (m0 : NMarking N) :
    Covers (flatIndex (refVerifiedNet net m0).places) m0.count :=
  inert_covers (Link.toNNet net) m0

/-- **No added place, no change**: a marking that marks only declared places leaves the net as
it is. -/
@[evidence cites "VER-001" "a net whose initial marking marks only declared places is unaffected: the verified net is the net itself"]
theorem VER_001_no_inert (net : Reference.Net N) (m0 : NMarking N)
    (h : ∀ p ∈ m0.places, p ∈ net.places) : refVerifiedNet net m0 = net := by
  have : m0.places.filter (fun p => p ∉ net.places) = [] :=
    List.filter_eq_nil_iff.mpr fun p hp => by simpa using h p hp
  unfold refVerifiedNet
  rw [this, List.append_nil]

/-! ## Examples: AC3 to AC5 on the reference

Places `a = 0`, `b = 1`, `c = 2`, `d = 3`. -/

/-- AC3's transition core: `t` consumes one token from `c`. -/
def ver001_coreCD : NTransition Nat :=
  { name := "t", inputs := [⟨2, .one⟩], inhibitors := [], reads := [], resets := [] }

/-- AC3's net: `t : c → d`, declaring `c` and `d`. -/
def ver001_netAC3 : Reference.Net Nat :=
  { places := [2, 3]
    transitions := [{ core := ver001_coreCD, out := some (.place 3) }] }

/-- AC3's initial marking `{a: 1}`: `a` is on no arc and not declared. -/
def ver001_m0AC3 : NMarking Nat := ⟨[(0, 1)], by decide, by decide⟩

/-- AC4's transition: `t : exactly(2, a) → xor(c, timeout(50, forwardInput(a, b)))`. -/
def ver001_tAC4 : Reference.Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .exactly 2⟩], inhibitors := [], reads := [], resets := [] }
    out := some (.xor (.place 2) (.timeout (.forward 0 1))) }

/-- AC5's transition: AC4's with `all(a)` in place of `exactly(2, a)`. -/
def ver001_tAC5 : Reference.Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .all⟩], inhibitors := [], reads := [], resets := [] }
    out := some (.xor (.place 2) (.timeout (.forward 0 1))) }

/-- A spec whose timeout outcome equals a branch: `t : one(a) → xor(c, timeout(50, b))` (AC4's
last sentence). -/
def ver001_tSame : Reference.Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] }
    out := some (.xor (.place 2) (.timeout (.place 1))) }

/-- A transition with one virtual transition: `t : one(a) → c`. -/
def ver001_tOne : Reference.Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] }
    out := some (.place 2) }

/-- A transition with no output spec: `t : one(a)`. -/
def ver001_tNone : Reference.Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] }
    out := none }

/-- AC3's net from `{a: 1, b: 1}`: two stray places, `a` listed first. -/
def ver001_m0Two : NMarking Nat := ⟨[(0, 1), (1, 1)], by decide, by decide⟩

theorem ver001_tNone_notDrained : ¬ DrainedForward ver001_tNone := by
  rw [← ver001_drainedB_iff]; decide

theorem ver001_tAC4_notDrained : ¬ DrainedForward ver001_tAC4 := by
  rw [← ver001_drainedB_iff]; decide

theorem ver001_tSame_notDrained : ¬ DrainedForward ver001_tSame := by
  rw [← ver001_drainedB_iff]; decide

theorem ver001_tOne_notDrained : ¬ DrainedForward ver001_tOne := by
  rw [← ver001_drainedB_iff]; decide

theorem ver001_tAC5_drained : DrainedForward ver001_tAC5 := by
  rw [← ver001_drainedB_iff]; decide

/-- AC3 to AC5 on the reference. AC3: the verified net has the places `c, d, a`, and at the
initial marking `DeadlockFree` with sink `d` and `PlaceBound(a, 0)` are violated. AC4: the
transition expands into `t_b0` (post `c`), `t_b1` (post `b`) and `t_b2` (post `2·b`), and its
timed-out firing from `{a: 2}` reaches `b = 2`. AC5: the `all(a)` transition has no expansion.
And a transition with one outcome keeps its own name, a transition with no output spec has one
row that deposits nothing, and two stray places keep the marking's order. -/
@[evidence nonvacuous VER_001]
theorem VER_001_nonvacuous :
    (refVerifiedNet ver001_netAC3 ver001_m0AC3).places = [2, 3, 0] ∧
    (refVerifiedNet ver001_netAC3 ver001_m0Two).places = [2, 3, 0, 1] ∧
    Reference.Violates (refVerifiedNet ver001_netAC3 ver001_m0AC3) (.deadlockFree [3])
      ver001_m0AC3.count ∧
    Reference.Violates (refVerifiedNet ver001_netAC3 ver001_m0AC3) (.placeBound 0 0)
      ver001_m0AC3.count ∧
    refVirtual ver001_tAC4 = some [("t_b0", [2]), ("t_b1", [1]), ("t_b2", [1, 1])] ∧
    (∃ m', Reference.Fires ver001_tAC4 (fun p => if p = 0 then 2 else 0) [1, 1] m' ∧ m' 1 = 2) ∧
    refVirtual ver001_tAC5 = none ∧
    refVirtual ver001_tOne = some [("t", [2])] ∧
    refVirtual ver001_tNone = some [("t", [])] := by
  refine ⟨rfl, rfl, ⟨?_, 0, by decide, by decide⟩, show 0 < ver001_m0AC3.count 0 by decide,
    by decide, ⟨_, ⟨by decide, ⟨.timedOut 0, by decide⟩, rfl⟩, by decide⟩, by decide, by decide,
    by decide⟩
  intro t ht hen
  simp only [refVerifiedNet, ver001_netAC3, List.mem_singleton] at ht
  subst ht
  revert hen
  decide

/-! ## Wrong models -/

/-- A verified net that drops the stray place: the pre-fix flattener's place list (AC3). -/
def ver001_dropInert : VerifiedNetFn N := fun net _ => net

/-- A verified net that puts the stray places before the declared ones. -/
def ver001_inertFirst : VerifiedNetFn N := fun net m0 =>
  { places := m0.places.filter (fun p => p ∉ net.places) ++ net.places
    transitions := net.transitions }

/-- A verified net that lists the stray places in reverse marking order. -/
def ver001_strayReversed : VerifiedNetFn N := fun net m0 =>
  { places := net.places ++ (m0.places.filter (fun p => p ∉ net.places)).reverse
    transitions := net.transitions }

/-- A verified net that keeps the places and loses the transitions. -/
def ver001_dropTransitions : VerifiedNetFn N := fun net m0 =>
  { refVerifiedNet net m0 with transitions := [] }

/-- An expansion built from a row function, with the reference names and drained check. -/
def ver001_expandWith (rows : Reference.Trans N → List (List N)) : ExpandFn N := fun t =>
  if ver001_drainedB t then none else some (ver001_labelRows t.core.name (rows t))

/-- The pre-fix expansion: the action branches only, no timeout row (AC4). -/
def ver001_noTimeoutRow : ExpandFn N := ver001_expandWith ver001_actionRows

/-- An expansion that adds the timeout row even when a branch deposits the same. -/
def ver001_noDedup : ExpandFn N := ver001_expandWith fun t =>
  ver001_actionRows t ++ (deposit (timeoutRequired t) t.out (.timedOut 0)).toList

/-- An expansion whose timeout row deposits one token in `to` per `ForwardInput`, whatever the
input's required count (the reading before IO-014), otherwise the reference. -/
def ver001_unitForward : ExpandFn N := ver001_expandWith fun t =>
  ver001_actionRows t ++
    match deposit (fun _ => 1) t.out (.timedOut 0) with
    | none => []
    | some d => if (ver001_actionRows t).any (fun b => b.isPerm d) then [] else [d]

/-- An expansion that gives a transition with no output spec no row. -/
def ver001_noneNoRow : ExpandFn N := ver001_expandWith fun t =>
  match t.out with
  | none => []
  | some _ => refVirtualRows t

/-- An expansion that lists the action rows in reverse enumeration order. -/
def ver001_reversedBranches : ExpandFn N := ver001_expandWith fun t =>
  (ver001_actionRows t).reverse ++ ver001_timeoutRows t

/-- An expansion that puts the timeout row before the action rows. -/
def ver001_timeoutFirst : ExpandFn N := ver001_expandWith fun t =>
  ver001_timeoutRows t ++ ver001_actionRows t

/-- An expansion that names every row `<t>_b<i>`, a single one included. -/
def ver001_alwaysIndexed : ExpandFn N := fun t =>
  if ver001_drainedB t then none else
    let rows := refVirtualRows t
    some (((List.range rows.length).map fun i => t.core.name ++ "_b" ++ toString i).zip rows)

/-- An expansion that gives a drained forward rows with fixed counts, the input's required count
standing in for the drained batch (the Rust flattener's fallback, read as an expansion; AC5). -/
def ver001_fixedDrained : ExpandFn N := fun t =>
  some (ver001_labelRows t.core.name (refVirtualRows t))

/-- Line 1 forbids dropping the stray place: AC3's verified net has the place `a`. -/
@[evidence forbids VER_001]
theorem VER_001_forbids_dropInert : ¬ VER_001 (ver001_dropInert (N := Nat)) refVirtual := by
  intro h
  have := h.1 ver001_netAC3 ver001_m0AC3
  revert this; decide

/-- Line 1 forbids putting the stray place first: `a` comes after `c` and `d`. -/
@[evidence forbids VER_001]
theorem VER_001_forbids_inertFirst : ¬ VER_001 (ver001_inertFirst (N := Nat)) refVirtual := by
  intro h
  have := h.1 ver001_netAC3 ver001_m0AC3
  revert this; decide

/-- Line 1 forbids reordering the stray places: from `{a: 1, b: 1}`, `a` comes before `b`. -/
@[evidence forbids VER_001]
theorem VER_001_forbids_strayReversed :
    ¬ VER_001 (ver001_strayReversed (N := Nat)) refVirtual := by
  intro h
  have := h.1 ver001_netAC3 ver001_m0Two
  revert this; decide

/-- Line 2 forbids changing the transitions: AC3's net keeps `t`. -/
@[evidence forbids VER_001]
theorem VER_001_forbids_dropTransitions :
    ¬ VER_001 (ver001_dropTransitions (N := Nat)) refVirtual := by
  intro h
  have := h.2.1 ver001_netAC3 ver001_m0AC3
  simp [ver001_dropTransitions, ver001_netAC3] at this

/-- Line 3 forbids an expansion without the timeout row: AC4's transition has the row `t_b2`
(post `2·b`). -/
@[evidence forbids VER_001]
theorem VER_001_forbids_noTimeoutRow :
    ¬ VER_001 (refVerifiedNet (N := Nat)) ver001_noTimeoutRow := by
  intro h
  obtain ⟨rows, hX, acts, tos, hr, ha, ht⟩ := h.2.2.1 ver001_tAC4 ver001_tAC4_notDrained
  have hu := VER_001_rows_unique hr ha ht
  have hX' : ver001_noTimeoutRow ver001_tAC4 = some [("t_b0", [2]), ("t_b1", [1])] := by decide
  rw [hX'] at hX
  cases hX
  have := hu.length_eq
  revert this; decide

/-- Line 3 forbids adding a timeout row a branch already deposits: on `xor(c, timeout(50, b))`
the timeout outcome is the branch `b`, and the transition keeps its two rows. -/
@[evidence forbids VER_001]
theorem VER_001_forbids_noDedup : ¬ VER_001 (refVerifiedNet (N := Nat)) ver001_noDedup := by
  intro h
  obtain ⟨rows, hX, acts, tos, hr, ha, ht⟩ := h.2.2.1 ver001_tSame ver001_tSame_notDrained
  have hu := VER_001_rows_unique hr ha ht
  have hX' : ver001_noDedup ver001_tSame =
      some [("t_b0", [2]), ("t_b1", [1]), ("t_b2", [1])] := by decide
  rw [hX'] at hX
  cases hX
  have := hu.length_eq
  revert this; decide

/-- Line 3 forbids a timeout row that forwards one token per `ForwardInput` (the fourth quoted
sentence): AC4's `forwardInput(a, b)` from `exactly(2, a)` deposits `2·b`, while the one-token
row `[b]` is the branch `b` and is deduplicated away, so the mutant has two rows, not three. -/
@[evidence forbids VER_001]
theorem VER_001_forbids_unitForward :
    ¬ VER_001 (refVerifiedNet (N := Nat)) ver001_unitForward := by
  intro h
  obtain ⟨rows, hX, acts, tos, hr, ha, ht⟩ := h.2.2.1 ver001_tAC4 ver001_tAC4_notDrained
  have hu := VER_001_rows_unique hr ha ht
  have hX' : ver001_unitForward ver001_tAC4 = some [("t_b0", [2]), ("t_b1", [1])] := by decide
  rw [hX'] at hX
  cases hX
  have := hu.length_eq
  revert this; decide

/-- Line 3 forbids a transition with no output spec without a row: `t : one(a)` has the one row
`t` that deposits nothing. -/
@[evidence forbids VER_001]
theorem VER_001_forbids_noneNoRow : ¬ VER_001 (refVerifiedNet (N := Nat)) ver001_noneNoRow := by
  intro h
  obtain ⟨rows, hX, acts, tos, hr, ha, ht⟩ := h.2.2.1 ver001_tNone ver001_tNone_notDrained
  have hu := VER_001_rows_unique hr ha ht
  have hX' : ver001_noneNoRow ver001_tNone = some [] := by decide
  rw [hX'] at hX
  cases hX
  have := hu.length_eq
  revert this; decide

/-- Line 3 forbids reversing the branch order: AC4's `t_b0` deposits in `c`, not in `b`. -/
@[evidence forbids VER_001]
theorem VER_001_forbids_reversedBranches :
    ¬ VER_001 (refVerifiedNet (N := Nat)) ver001_reversedBranches := by
  intro h
  obtain ⟨rows, hX, acts, tos, hr, ha, ht⟩ := h.2.2.1 ver001_tAC4 ver001_tAC4_notDrained
  have hu := VER_001_rows_unique hr ha ht
  have hX' : ver001_reversedBranches ver001_tAC4 =
      some [("t_b0", [1]), ("t_b1", [2]), ("t_b2", [1, 1])] := by decide
  have hR : refVirtualRows ver001_tAC4 = [[2], [1], [1, 1]] := by decide
  rw [hX'] at hX
  cases hX
  rw [hR] at hu
  exact ver001_not_forall₂_head 2 (by decide) hu

/-- Line 3 forbids putting the timeout row first: AC4's `t_b0` deposits in `c`, not `2·b`. -/
@[evidence forbids VER_001]
theorem VER_001_forbids_timeoutFirst :
    ¬ VER_001 (refVerifiedNet (N := Nat)) ver001_timeoutFirst := by
  intro h
  obtain ⟨rows, hX, acts, tos, hr, ha, ht⟩ := h.2.2.1 ver001_tAC4 ver001_tAC4_notDrained
  have hu := VER_001_rows_unique hr ha ht
  have hX' : ver001_timeoutFirst ver001_tAC4 =
      some [("t_b0", [1, 1]), ("t_b1", [2]), ("t_b2", [1])] := by decide
  have hR : refVirtualRows ver001_tAC4 = [[2], [1], [1, 1]] := by decide
  rw [hX'] at hX
  cases hX
  rw [hR] at hu
  exact ver001_not_forall₂_head 2 (by decide) hu

/-- Line 4 forbids naming a single row `<t>_b0`: `t : one(a) → c` has the one row `t`. -/
@[evidence forbids VER_001]
theorem VER_001_forbids_alwaysIndexed :
    ¬ VER_001 (refVerifiedNet (N := Nat)) ver001_alwaysIndexed := by
  intro h
  have hX : ver001_alwaysIndexed ver001_tOne = some [("t_b0", [2])] := by decide
  have := h.2.2.2.1 ver001_tOne _ hX
  revert this; decide

/-- Line 5 forbids fixed rows for a drained forward: AC5's transition has no expansion. -/
@[evidence forbids VER_001]
theorem VER_001_forbids_fixedDrained :
    ¬ VER_001 (refVerifiedNet (N := Nat)) ver001_fixedDrained := by
  intro h
  have := h.2.2.2.2 ver001_tAC5 ver001_tAC5_drained
  simp [ver001_fixedDrained] at this

end Libpetri.Spec
