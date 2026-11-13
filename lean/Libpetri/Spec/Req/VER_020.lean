import Libpetri.Spec.Registry
import Libpetri.Novel.SiphonSearch
import Libpetri.Reference.Nu
import Libpetri.Novel.EnvSemantics.Arrivals

set_option linter.missingDocs true

/-!
# VER-020: Siphon and trap analysis (`spec/07-verification.md`)

The structural deadlock pre-check decides Commoner's condition on the flat net: every nonempty
siphon contains a trap that is marked initially. It finds every minimal siphon, contracts each
one to the maximal trap inside it and asks whether that trap holds a token. The requirement is a
predicate over a triple `(F, T, C)`:

* `F : Ver020Search`, the siphon search: `F net n b stop` is the list of siphons it returns on
  the flat net `net` with `n` places, under a budget of `b` search nodes and the stop oracle
  `stop` of [VER-013], or `none` when it does not return;
* `T : Ver020Trap`, the trap contraction: `T net n sip` is the trap it computes inside the
  siphon `sip`;
* `C : Ver020Check`, the structural check: `C net n stop a0` is its answer on the initial
  marking `a0` (no potential deadlock, potential deadlock or inconclusive).

The witness triple is `refSiphonSearch` (`SiphonSearch.findMinimalSiphons`), `refMaxTrap`
(`SiphonSearch.maximalTrapIn`) and `refStructCheck` (`SiphonSearch.structuralCheck` at the
budget of 10 000 nodes), the models of `structural_check.rs` that the fidelity check pins. The
statement is checked against them (`VER_020_reference`), against a search without the minimality
filter, the padding search of the pre-fix Rust, a search that never returns, a search that does
not read the stop oracle, a contraction that returns the siphon unchanged, and four wrong checks:
one without the empty-net guard, one that accepts a nonempty but unmarked trap, one without the
50-place cut and one that passes a smaller node budget. `VER_020_commoner` shows, from the
statement alone, that a no-potential-deadlock answer on an ordinary net rules out every
reachable dead marking (AC2), and `VER_020_finds_ac4` that every conforming search finds
`{x, y}` and `{a, b}` on the two AC4 witnesses.

What a search node is, and how the search spends the budget it is given, is not stated: the
statement fixes the number the check passes (10 000) and that a search on the AC4 witnesses
returns at it, not the node count of the reference.

When the verifier turns the check's answer into a `Proven` is the second block,
`VER_020_guard` (kind B, ruling D93): a predicate over the structural route `R`, which reads the
property, whether the net has a match transition, whether a transition is reapable and
`assumeNoReaping`, the flat net, the declared sinks and conditional sinks and the environment
places registered on the net it receives (the `Arrivals` rewrite of [VER-006] leaves none). Its
witness is `refStructRoute`; it is checked against a route that ignores the check's answer and
one route per dropped guard conjunct. `VER_020_guard_sound` composes both blocks: a structural
`Proven` on a net whose inputs lie below `n` rules out every reachable dead marking of the flat
net. `VER_020_guard_match` shows why the match conjunct guards soundness: on a ν-join net whose
flat net the check passes, the ν net is stuck at its initial marking. `VER_020_guard_arrivals`
shows what the rewrite leaves the route on the reference closure of [VER-006]: the net itself
under `Arrivals(0)`, and under `Arrivals(1, 1)` a source place that the check does not pass.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Novel Libpetri.Novel.Commoner Libpetri.Novel.SiphonSearch

/-! ## The model -/

/-- A siphon search: `F net n b stop` is the list of place sets it returns on the flat net `net`
with places `0 … n-1`, under a budget of `b` search nodes and the stop oracle `stop`; `none`
when it does not return (the budget is exceeded or the stop fires). The shape of
`find_minimal_siphons`. -/
abbrev Ver020Search : Type :=
  FlatNet → Nat → Nat → (Nat → Bool) → Option (List (List PlaceId))

/-- A trap contraction: `T net n sip` is the place set it computes inside the siphon `sip`. The
shape of `find_maximal_trap_in`. -/
abbrev Ver020Trap : Type := FlatNet → Nat → List PlaceId → List PlaceId

/-- A structural check: `C net n stop a0` is its answer on the flat net `net` with `n` places,
the stop oracle `stop` and the initial marking `a0`. The shape of `structural_check`. -/
abbrev Ver020Check : Type := FlatNet → Nat → (Nat → Bool) → AMarking → SiphonSearch.Verdict

/-- The reference siphon search: `find_minimal_siphons` (`structural_check.rs`). -/
def refSiphonSearch : Ver020Search := findMinimalSiphons

/-- The reference trap contraction: `find_maximal_trap_in` (`structural_check.rs`). -/
def refMaxTrap : Ver020Trap := maximalTrapIn

/-- The reference check: `structural_check` (`structural_check.rs`) with the shipped budget of
10 000 search nodes (`SIPHON_SEARCH_BUDGET`). -/
def refStructCheck : Ver020Check :=
  fun net n stop a0 => structuralCheck net n siphonSearchBudget stop a0

#spec_witness refSiphonSearch
#spec_witness refMaxTrap
#spec_witness refStructCheck

/-! ## VER-020: Siphon and trap analysis -/

requirement VER_020
  id "VER-020"
  title "Siphon and Trap Analysis"
  kind F
  scope "the structural deadlock pre-check (siphon search, trap contraction, structural check) of every implementation"
  source verbatim "spec/07-verification.md"
  quote "*When* the siphon search returns, every set it returns *shall* be a nonempty siphon that contains no other nonempty siphon."
        "*When* the siphon search returns, every nonempty siphon *shall* contain a set it returns."
        "The maximal trap the check computes inside a set of places *shall* be a trap inside that set that contains every trap inside it."
        "*If* the net has more than 50 places or no transition, *then* the structural check *shall* answer inconclusive."
        "The structural check *shall* pass the siphon search a budget of 10 000 search nodes."
        "*If* the siphon search does not return, *then* the structural check *shall* answer inconclusive."
        "*When* the siphon search returns on a net with at most 50 places and at least one transition, the structural check *shall* answer no potential deadlock exactly when the maximal trap inside each returned siphon holds a token in the initial marking, and potential deadlock otherwise."
        "*While* the total budget of [VER-013] is not spent, the siphon search *shall* return at a budget of 10 000 search nodes on the two witnesses above with minimal siphons `{x, y}` and `{a, b}`."
        "*If* the total budget of [VER-013] is spent before the siphon search starts on a net with at least one place, *then* the siphon search *shall not* return."
  reading "For every flat net net with n places, every budget b, stop oracle stop and list sips that F returns: every K in sips is nonempty, lies below n, is a siphon, and every nonempty siphon inside K is all of K."
          "For every flat net net, n, b, stop and list sips that F returns: every nonempty siphon below n contains some K in sips."
          "For every flat net net, n and list sip below n: T net n sip lies inside sip, is a trap, and contains every trap that lies inside sip."
          "For every flat net net, n, stop and initial marking a0: C answers inconclusive when n is above 50 or net has no transition; otherwise it runs F at the budget 10 000 with stop, answers inconclusive when F returns nothing, and else answers no potential deadlock when the maximal trap T of every returned siphon holds a token of a0, and potential deadlock when one does not."
          "With a stop oracle that never fires and the budget 10 000, F returns a list on the ring netRing with 4 places and on netPad with 3 places."
          "For every flat net net, every n above 0 and every budget b, F with a stop oracle that fires at every poll returns nothing."
  assumes "The model is the triple (F, T, C) of Ver020Search, Ver020Trap and Ver020Check over the flat net (Soundness.FlatNet: a list of flat transitions, each a transition and the places one outcome deposits into), whose places are the indices 0 to n - 1, and the initial marking as a count per index (AMarking). That the flat net's vectors are what the Rust computes (pre[p] > 0 exactly on a consuming input arc, post[p] > 0 exactly on an output place, vectors of length n, the marking read by index) is premises P1 to P4 of Novel/SiphonSearch.lean, kept by the fidelity pins on structural_check.rs. The witness triple is refSiphonSearch, refMaxTrap and refStructCheck."
          "Lines 1 and 2 are the first two quoted sentences. 'Contains no other nonempty siphon' is the last clause of line 1: a nonempty siphon inside K is all of K. Siphons are taken among the places below n (the flat net has no other place). With both lines a list the search returns is exactly the set of minimal siphons. 'An implementation MUST therefore find every minimal siphon before it concludes \"no potential deadlock\"' is lines 1, 2 and 4 together: the check concludes no potential deadlock only from a list the search returned, and such a list holds every minimal siphon. Lines 1 and 2 do not make the search return. Line 5 does on the two AC4 witnesses; on any other net a search may give up, and the check is then inconclusive by line 4, which conforms."
          "Line 3 is the third quoted sentence, on any set of places below n given as a list. The check applies it only to the siphons the search returns."
          "Line 4 is the fourth to seventh quoted sentences, with the limits of ruling D45 as numbers in the formula: the 50-place cut and the 10 000-node budget, which the three runtimes share (structural_check.rs, structural-check.ts and StructuralCheck.java). 'No transition' is the flat net being empty, the guard flat.transitions.is_empty() of structural_check.rs: outcomes() gives every transition at least one outcome (branch_outcomes.rs), so the flat net is empty exactly when the net has no transition. The fifth quoted sentence fixes the number the check passes to the search and nothing more. What a search node is (in the reference one call of grow_siphon, counted by the Rust's node counter) and how the search spends the budget it is given are the search's own and are not stated: a search that returns a correct list past its budget, or gives up before it, conforms to lines 1, 2 and 4, and only lines 5 and 6 bound it. VER_020_forbids_budget therefore kills a check that passes a smaller number to the reference search, not a search that spends its budget differently. 'Deciding the condition is co-NP-complete, so the search MAY run under a budget; past it the result is inconclusive, never a proof.' is the sixth quoted sentence: a search that does not return, for its budget or for the stop, makes the check answer inconclusive. Java and TypeScript answer no potential deadlock at once on a net with transitions and no place; the reference search returns no siphon there, so line 4 gives the same answer."
          "Line 5 is the eighth quoted sentence and the first sentence of AC4. The stop oracle that never fires is a total budget of VER-013 that is not spent. The two witnesses are netRing (t1: g + x to y + g, t2: h + y to x + h, places g h x y numbered 0 to 3) and netPad (t1: a + c to b + c, t2: b to a, places a b c numbered 0 to 2). With lines 1 and 2, a search that returns there finds {x, y} on the ring and {a, b} on netPad, as sets of places (VER_020_finds_ac4, from the statement alone). Other nets are not named. A search that never returns is killed by this line (VER_020_forbids_neverReturns)."
          "Line 6 is the ninth quoted sentence. A total budget that is spent before the search starts is a stop oracle that fires at every poll; the stop oracle is indexed by the search's node counter (premise P5 of Novel/SiphonSearch.lean), and when it fires at every poll the counter does not matter. A net with no place gives the search no start place, so the line asks nothing of it. That the reference also gives up when the stop fires later, after some nodes, is shown on the reference only (VER_020_nonvacuous); the statement does not say how often a search polls the stop. A search that does not read the stop oracle is killed by this line (VER_020_forbids_ignoresStop)."
          "The 'Commoner's theorem governs ORDINARY nets only' paragraph, its MUST sentence and AC3 are about when the verifier turns the check's answer into a Proven, which the check does not decide: it reads the pre and post vectors only and is called behind the guard. The guard sentence after the paragraph 'A match transition hides a dead marking from the flat net' is the second block, VER_020_guard (ruling D93), with the ν-join net of VER_020_guard_match for the match conjunct. Here the ordinary premise is a premise of VER_020_commoner, and Commoner.ordinary_is_necessary shows it cannot be dropped. That the three witnesses of the paragraph return a verdict from a route that models what disables them is the other routes' (VER-017, VER-018 and the fixpoint query), reached through the guard."
          "The 'Commoner's theorem needs at least one transition' paragraph is the empty-net guard of line 4: on a net with no transition the check answers inconclusive (VER_020_nonvacuous on the one-place witness), and a check without the guard is killed (VER_020_forbids_unguarded, the retrodiction SiphonSearch.empty_net_structural_proven_dead). That the one-place witness is Violated is the enumeration route's verdict (VER-017), not the check's."
          "The 'A structural proof needs every minimal siphon' paragraph is lines 1, 2 and 4: every minimal siphon is returned, and each one's maximal trap must hold a token in the initial marking, so an empty or unmarked trap gives potential deadlock. 'Growing a siphon by committing to one input of each producer (the first, or all of them) is incomplete' is killed by VER_020_forbids_padding (the pre-fix Rust search, SiphonSearch.pre_fix_padding_proves_dead_net); a test of a nonempty but unmarked trap is killed by VER_020_forbids_nonemptyTrap (SiphonSearch.pre_fix_unmarked_trap_proves_dead_net)."
          "AC1 (siphons and traps are identified from the net structure) is lines 1 to 3."
          "AC2 (every siphon containing an initially marked trap ensures deadlock-freedom of an ordinary net) is VER_020_commoner, proved from the statement and Commoner.commoner: on an ordinary net whose input arcs lie on places below n, a no-potential-deadlock answer means no marking reachable under the untimed relation ReachA is dead. 'Liveness only for free-choice nets' is a remark about the theory with no behaviour of the check; it is not stated. The answer is about the untimed net; that it holds for timed runs too when no transition is reapable is SiphonSearch.structural_proven_sound_timed, behind the reapable conjunct of VER_020_guard."
          "AC3 (a structural Proven only for DeadlockFree on a net with no match transition, no reapable transition unless assumeNoReaping is set, no read, inhibitor or reset arc, no consume-all input, no input arc weight above one, no declared sink or conditional sink and no environment place registered on the net the verifier decides; the three witnesses decided by another route; never for a net with no transition) is VER_020_guard, as above, except its last clause: on a net with no transition the check answers inconclusive (line 4, VER_020_nonvacuous), so no Proven can come from it."
          "AC4 (the search is complete: it finds {x, y} and {a, b} in the two witnesses and neither net is proven structurally; an unmarked maximal trap blocks a structural proof; a net with more than 50 places or an exhausted search budget is inconclusive) is, for every conforming triple: line 5 with lines 1 and 2 for 'finds {x, y} and {a, b}' (VER_020_finds_ac4); lines 1, 2 and 4 for 'neither net is proven structurally' and 'an unmarked maximal trap blocks a structural proof', since a returned list holds every minimal siphon and a check answers no potential deadlock only when each one's maximal trap is marked; line 4 for the 50-place cut (VER_020_forbids_noPlaceCut) and for a search that does not return. That a search gives up past its budget is the reference's, as line 4 says above: VER_020_nonvacuous shows on the reference that the search at a budget of 1 node gives up on the ring, that the check answers potential deadlock on both witnesses from the stated markings and on the ring a to b and back from the empty marking, and that a stopped search gives inconclusive. A check that passes a smaller budget is killed (VER_020_forbids_budget)."
          "The test derivation (a net with known siphon and trap structure, the identification verified) is AC1 and AC4, as above."
  signoff "2026-11-13 65822d981cd6d6c8 ai"
  statement : Ver020Search → Ver020Trap → Ver020Check → Prop :=
    fun F T C =>
      (∀ net n b stop sips, F net n b stop = some sips → ∀ K ∈ sips,
        (∃ p, p ∈ K) ∧ (∀ p ∈ K, p < n) ∧ Siphon net (· ∈ K) ∧
        ∀ S : PlaceId → Prop, (∃ p, S p) → Siphon net S → (∀ p, S p → p ∈ K) → ∀ p ∈ K, S p) ∧
      (∀ net n b stop sips, F net n b stop = some sips →
        ∀ S : PlaceId → Prop, (∀ p, S p → p < n) → (∃ p, S p) → Siphon net S →
          ∃ K ∈ sips, ∀ p ∈ K, S p) ∧
      (∀ net (n : Nat) (sip : List PlaceId), (∀ p ∈ sip, p < n) →
        (∀ p ∈ T net n sip, p ∈ sip) ∧ Trap net (· ∈ T net n sip) ∧
        ∀ U : PlaceId → Prop, Trap net U → (∀ p, U p → p ∈ sip) → ∀ p, U p → p ∈ T net n sip) ∧
      (∀ net n stop (a0 : AMarking), C net n stop a0 =
        if 50 < n || net.isEmpty then .inconclusive
        else
          match F net n 10000 stop with
          | none => .inconclusive
          | some sips =>
            if sips.all (fun sip => (T net n sip).any fun p => decide (0 < a0 p))
            then .noPotentialDeadlock else .potentialDeadlock) ∧
      (F netRing 4 10000 (fun _ => false) ≠ none ∧ F netPad 3 10000 (fun _ => false) ≠ none) ∧
      (∀ net n b, 0 < n → F net n b (fun _ => true) = none)

/- The pinned readable form of VER-020: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.VER_020 : Ver020Search → Ver020Trap → Ver020Check → Prop :=
fun F T C =>
  (∀ (net : FlatNet) (n b : ℕ) (stop : ℕ → Bool) (sips : List (List PlaceId)),
      F net n b stop = some sips →
        ∀ K ∈ sips,
          (∃ p, p ∈ K) ∧
            (∀ p ∈ K, p < n) ∧
              (Siphon net fun x => x ∈ K) ∧
                ∀ (S : PlaceId → Prop), (∃ p, S p) → Siphon net S → (∀ (p : PlaceId), S p → p ∈ K) → ∀ p ∈ K, S p) ∧
    (∀ (net : FlatNet) (n b : ℕ) (stop : ℕ → Bool) (sips : List (List PlaceId)),
        F net n b stop = some sips →
          ∀ (S : PlaceId → Prop),
            (∀ (p : PlaceId), S p → p < n) → (∃ p, S p) → Siphon net S → ∃ K ∈ sips, ∀ p ∈ K, S p) ∧
      (∀ (net : FlatNet) (n : ℕ) (sip : List PlaceId),
          (∀ p ∈ sip, p < n) →
            (∀ p ∈ T net n sip, p ∈ sip) ∧
              (Trap net fun x => x ∈ T net n sip) ∧
                ∀ (U : PlaceId → Prop),
                  Trap net U → (∀ (p : PlaceId), U p → p ∈ sip) → ∀ (p : PlaceId), U p → p ∈ T net n sip) ∧
        (∀ (net : FlatNet) (n : ℕ) (stop : ℕ → Bool) (a0 : AMarking),
            C net n stop a0 =
              if (decide (50 < n) || List.isEmpty net) = true then Verdict.inconclusive
              else
                match F net n 10000 stop with
                | none => Verdict.inconclusive
                | some sips =>
                  if (sips.all fun sip => (T net n sip).any fun p => decide (0 < a0 p)) = true then
                    Verdict.noPotentialDeadlock
                  else Verdict.potentialDeadlock) ∧
          ((F netRing 4 10000 fun x => false) ≠ none ∧ (F netPad 3 10000 fun x => false) ≠ none) ∧
            ∀ (net : FlatNet) (n b : ℕ), 0 < n → (F net n b fun x => true) = none
-/
#guard_msgs in #print VER_020

/-! ## The reference -/

/-- The reference search gives up at its first node when the stop fires at every poll: on a
net with at least one place, `grow_siphon` on the first start place polls the stop before it
does anything else. -/
theorem refSiphonSearch_stopped (net : FlatNet) {n : Nat} (b : Nat) (hn : 0 < n) :
    refSiphonSearch net n b (fun _ => true) = none := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [refSiphonSearch, findMinimalSiphons, searchZ, List.range_succ_eq_map, seqM, growZ]

/-- The reference triple satisfies VER-020: the search is sound and minimal
(`findMinimalSiphons_sound`) and complete (`findMinimalSiphons_complete`), the contraction
returns the maximal trap (`maximalTrapIn_spec`), the check is `structural_check` at the
shipped budget, by definition, the search returns on the two AC4 witnesses (by evaluation), and
it gives up when the stop fires at every poll (`refSiphonSearch_stopped`). -/
@[evidence holds VER_020]
theorem VER_020_reference : VER_020 refSiphonSearch refMaxTrap refStructCheck :=
  ⟨fun _ _ _ _ _ h _ hK => findMinimalSiphons_sound h hK,
    fun _ _ _ _ _ h S hSb hne hS => findMinimalSiphons_complete h S hSb hne hS,
    fun _ _ _ hsip => maximalTrapIn_spec hsip,
    fun _ _ _ _ => rfl,
    ⟨by decide, by decide⟩,
    fun net _ b hn => refSiphonSearch_stopped net b hn⟩

/-- **A no-potential-deadlock answer rules out every reachable dead marking of an ordinary
net** (AC2), from the statement alone: on every triple satisfying VER-020, when the check
answers no potential deadlock on an ordinary net whose input arcs lie on places below `n`, no
marking reachable under the untimed relation `ReachA` is dead. The proof rebuilds Commoner's
condition from lines 1 to 4 and applies `Commoner.commoner`. -/
@[evidence cites "VER-020" "AC2: on an ordinary net, a check that answers no potential deadlock (every minimal siphon's maximal trap marked initially, at least one transition) rules out every dead marking reachable in the untimed net"]
theorem VER_020_commoner {F : Ver020Search} {T : Ver020Trap} {C : Ver020Check}
    (h : VER_020 F T C) {net : FlatNet} {n : Nat} {stop : Nat → Bool} {a0 : AMarking}
    (hord : Ordinary net) (hbelow : InputsBelow net n)
    (hC : C net n stop a0 = .noPotentialDeadlock) {a : AMarking} (hr : ReachA net a0 a) :
    ¬ Dead net a := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := h
  rw [h4] at hC
  split at hC
  · cases hC
  · rename_i hcut
    have hne : net ≠ [] := by
      rintro rfl
      simp at hcut
    split at hC
    · cases hC
    · rename_i sips hF
      split at hC
      · rename_i hall
        refine commoner hne hord hbelow ?_ hr
        intro S hSb hSne hS
        obtain ⟨K, hK, hKS⟩ := h2 net n 10000 stop sips hF S hSb hSne hS
        obtain ⟨_, hKn, _, _⟩ := h1 net n 10000 stop sips hF K hK
        obtain ⟨hTK, hT, _⟩ := h3 net n K hKn
        obtain ⟨p, hp, hpos⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall K hK)
        exact ⟨(· ∈ T net n K), fun q hq => hKS q (hTK q hq), hT, p, hp, of_decide_eq_true hpos⟩
      · cases hC

/-- On a list a search returns, a nonempty siphon `K` lying inside `{p, q}`, where every flat
transition that outputs into `p` consumes from `q` and nothing else of `{p, q}`, and the other
way round, holds both `p` and `q`. -/
theorem ver020_pair_closed {net : FlatNet} {p q : PlaceId} {K : List PlaceId}
    (hne : ∃ r, r ∈ K) (hKS : ∀ r ∈ K, r = p ∨ r = q) (hK : Siphon net (· ∈ K))
    (hp : ∀ r, r ∈ K → (∃ ft ∈ net, ft.2.contains p = true ∧ ∀ s, Commoner.Consumes ft.1 s → s ∈ K → s = q))
    (hq : ∀ r, r ∈ K → (∃ ft ∈ net, ft.2.contains q = true ∧ ∀ s, Commoner.Consumes ft.1 s → s ∈ K → s = p)) :
    p ∈ K ∧ q ∈ K := by
  obtain ⟨r, hr⟩ := hne
  have toq : p ∈ K → q ∈ K := fun hpK => by
    obtain ⟨ft, hft, hout, hcons⟩ := hp r hr
    obtain ⟨s, hs, hc⟩ := hK ft hft ⟨p, hpK, hout⟩
    exact hcons s hc hs ▸ hs
  have top : q ∈ K → p ∈ K := fun hqK => by
    obtain ⟨ft, hft, hout, hcons⟩ := hq r hr
    obtain ⟨s, hs, hc⟩ := hK ft hft ⟨q, hqK, hout⟩
    exact hcons s hc hs ▸ hs
  rcases hKS r hr with rfl | rfl
  · exact ⟨hr, toq hr⟩
  · exact ⟨top hr, hr⟩

/-- **Every conforming search finds `{x, y}` and `{a, b}` on the AC4 witnesses** (AC4, "The
siphon search is complete"), from the statement alone: line 5 makes the search return there,
line 2 puts a returned set inside the siphon `{x, y}` (resp. `{a, b}`), and line 1 makes that
set a siphon, which then holds both places. -/
@[evidence cites "VER-020" "AC4: every conforming siphon search returns, on the ring with minimal siphon {x, y} and on the padding witness with minimal siphon {a, b}, a list holding that siphon"]
theorem VER_020_finds_ac4 {F : Ver020Search} {T : Ver020Trap} {C : Ver020Check}
    (h : VER_020 F T C) :
    (∃ sips, F netRing 4 10000 (fun _ => false) = some sips ∧
      ∃ K ∈ sips, ∀ p, p ∈ K ↔ p = 2 ∨ p = 3) ∧
    (∃ sips, F netPad 3 10000 (fun _ => false) = some sips ∧
      ∃ K ∈ sips, ∀ p, p ∈ K ↔ p = 0 ∨ p = 1) := by
  obtain ⟨h1, h2, -, -, ⟨hRing, hPad⟩, -⟩ := h
  constructor
  · obtain ⟨sips, hs⟩ := Option.ne_none_iff_exists'.mp hRing
    have hsiph : Siphon netRing (fun p => p = 2 ∨ p = 3) := by
      intro ft hft _
      simp only [netRing, List.mem_cons, List.not_mem_nil, or_false] at hft
      rcases hft with rfl | rfl
      · exact ⟨2, Or.inl rfl, ⟨2, .one, none⟩, by simp [tR1], rfl, by decide⟩
      · exact ⟨3, Or.inr rfl, ⟨3, .one, none⟩, by simp [tR2], rfl, by decide⟩
    obtain ⟨K, hK, hKS⟩ := h2 netRing 4 10000 _ sips hs (fun p => p = 2 ∨ p = 3)
      (fun p hp => by rcases hp with rfl | rfl <;> decide) ⟨2, Or.inl rfl⟩ hsiph
    obtain ⟨hne, -, hKsiph, -⟩ := h1 netRing 4 10000 _ sips hs K hK
    have both := ver020_pair_closed (p := 2) (q := 3) hne hKS hKsiph
      (fun _ _ => ⟨(tR2, [2, 1]), by simp [netRing], by decide, fun s hc hs => by
        obtain ⟨a, ha, rfl, _⟩ := hc
        simp only [tR2, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · rfl
        · rcases hKS _ hs with h | h <;> simp at h⟩)
      (fun _ _ => ⟨(tR1, [3, 0]), by simp [netRing], by decide, fun s hc hs => by
        obtain ⟨a, ha, rfl, _⟩ := hc
        simp only [tR1, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · rfl
        · rcases hKS _ hs with h | h <;> simp at h⟩)
    refine ⟨sips, hs, K, hK, fun p => ⟨hKS p, ?_⟩⟩
    rintro (rfl | rfl)
    · exact both.1
    · exact both.2
  · obtain ⟨sips, hs⟩ := Option.ne_none_iff_exists'.mp hPad
    have hsiph : Siphon netPad (fun p => p = 0 ∨ p = 1) := by
      intro ft hft _
      simp only [netPad, List.mem_cons, List.not_mem_nil, or_false] at hft
      rcases hft with rfl | rfl
      · exact ⟨0, Or.inl rfl, ⟨0, .one, none⟩, by simp [tP1], rfl, by decide⟩
      · exact ⟨1, Or.inr rfl, ⟨1, .one, none⟩, by simp [tP2], rfl, by decide⟩
    obtain ⟨K, hK, hKS⟩ := h2 netPad 3 10000 _ sips hs (fun p => p = 0 ∨ p = 1)
      (fun p hp => by rcases hp with rfl | rfl <;> decide) ⟨0, Or.inl rfl⟩ hsiph
    obtain ⟨hne, -, hKsiph, -⟩ := h1 netPad 3 10000 _ sips hs K hK
    have both := ver020_pair_closed (p := 0) (q := 1) hne hKS hKsiph
      (fun _ _ => ⟨(tP2, [0]), by simp [netPad], by decide, fun s hc _ => by
        obtain ⟨a, ha, rfl, _⟩ := hc
        simp only [tP2, List.mem_cons, List.not_mem_nil, or_false] at ha
        subst ha
        rfl⟩)
      (fun _ _ => ⟨(tP1, [1, 2]), by simp [netPad], by decide, fun s hc hs => by
        obtain ⟨a, ha, rfl, _⟩ := hc
        simp only [tP1, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · rfl
        · rcases hKS _ hs with h | h <;> simp at h⟩)
    refine ⟨sips, hs, K, hK, fun p => ⟨hKS p, ?_⟩⟩
    rintro (rfl | rfl)
    · exact both.1
    · exact both.2

/-! ## Examples: AC4 on the reference -/

/-- AC4 and the empty-net paragraph on the reference. The ring `t1: x + g → y + g`,
`t2: y + h → x + h` (places `g h x y` = `0 1 2 3`): the search returns the minimal siphon
`{x, y}`, and the check answers potential deadlock from `{g:1, h:1}` and no potential deadlock
once `x` is marked too. The padding witness `t1: a + c → b + c`, `t2: b → a` (places `a b c`):
the search returns `{a, b}` and the check answers potential deadlock from `{c:1}`. The ring
`a ⇄ b` from the empty marking: its maximal trap `{a, b}` is unmarked, potential deadlock. The
net with one place and no transition: inconclusive. A search stopped after its first node:
inconclusive. The reference search at a budget of 1 node gives up on the ring (an exhausted
budget). -/
@[evidence nonvacuous VER_020]
theorem VER_020_nonvacuous :
    refSiphonSearch netRing 4 1 (fun _ => false) = none ∧
    ([2, 3] : List PlaceId) ∈ (refSiphonSearch netRing 4 10000 fun _ => false).getD [] ∧
    refStructCheck netRing 4 (fun _ => false) (fun p => if p = 0 ∨ p = 1 then 1 else 0) =
      .potentialDeadlock ∧
    refStructCheck netRing 4 (fun _ => false) (fun p => if p = 0 ∨ p = 1 ∨ p = 2 then 1 else 0) =
      .noPotentialDeadlock ∧
    ([0, 1] : List PlaceId) ∈ (refSiphonSearch netPad 3 10000 fun _ => false).getD [] ∧
    refStructCheck netPad 3 (fun _ => false) a0Pad = .potentialDeadlock ∧
    refMaxTrap netCyc 2 [0, 1] = [0, 1] ∧
    refStructCheck netCyc 2 (fun _ => false) (fun _ => 0) = .potentialDeadlock ∧
    refStructCheck [] 1 (fun _ => false) aOne = .inconclusive ∧
    refStructCheck netCyc 2 (fun _ => true) (fun p => if p = 0 then 1 else 0) = .inconclusive ∧
    refStructCheck netCyc 2 (fun k => decide (2 ≤ k)) (fun p => if p = 0 then 1 else 0) =
      .inconclusive := by
  decide

/-! ## Wrong models -/

/-- `t: b → a` (places `a b` = `0 1`): growing from `{a}` reaches the siphon `{a, b}`, and
`{b}` alone is a siphon. -/
def ver020_tSrc : Transition :=
  { name := "t", inputs := [⟨1, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- The net of `ver020_tSrc`. -/
def ver020_netSrc : FlatNet := [(ver020_tSrc, [0])]

/-- `t: a →` (no output): `{a}` is a siphon and not a trap. -/
def ver020_tDrain : Transition :=
  { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- The net of `ver020_tDrain`. -/
def ver020_netDrain : FlatNet := [(ver020_tDrain, [])]

/-- `t: a → a` on a net of many places: every place is its own minimal siphon. -/
def ver020_tLoop : Transition :=
  { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- The net of `ver020_tLoop`. -/
def ver020_netLoop : FlatNet := [(ver020_tLoop, [0])]

/-- A search without the minimality filter: every siphon the growth found, smaller ones found
later included. -/
def ver020_searchNoFilter : Ver020Search :=
  fun net n b stop => (searchZ net n b stop none).map fun st => st.1.map (toList n)

/-- The pre-fix search of f52c482: grow by every input of a producer
(`SiphonSearch.preFixFind`). -/
def ver020_searchPadding : Ver020Search := fun net n _ _ => some (preFixFind net n)

/-- A contraction that returns the siphon unchanged. -/
def ver020_trapNoContract : Ver020Trap := fun _ _ sip => sip

/-- The check before the empty-net guard (`SiphonSearch.structuralCheckUnguarded`). -/
def ver020_checkUnguarded : Ver020Check :=
  fun net n stop a0 => structuralCheckUnguarded net n siphonSearchBudget stop a0

/-- A check that accepts a nonempty maximal trap whether or not it is marked. -/
def ver020_checkNonemptyTrap : Ver020Check :=
  fun net n stop _ =>
    if 50 < n || net.isEmpty then .inconclusive
    else
      match findMinimalSiphons net n siphonSearchBudget stop with
      | none => .inconclusive
      | some sips =>
        if sips.all (fun sip => !(maximalTrapIn net n sip).isEmpty)
        then .noPotentialDeadlock else .potentialDeadlock

/-- A check without the 50-place cut. -/
def ver020_checkNoPlaceCut : Ver020Check :=
  fun net n stop a0 =>
    if net.isEmpty then .inconclusive else siphonVerdict net n siphonSearchBudget stop a0

/-- A check that runs the search under a budget of 10 nodes. -/
def ver020_checkBudget : Ver020Check :=
  fun net n stop a0 => structuralCheck net n 10 stop a0

/-- Line 1 forbids a search without the minimality filter: on `t: b → a` it returns `{a, b}`
beside `{b}`, and the siphon `{b}` lies inside `{a, b}`. -/
@[evidence forbids VER_020]
theorem VER_020_forbids_noFilter :
    ¬ VER_020 ver020_searchNoFilter refMaxTrap refStructCheck := by
  intro h
  have hs : ver020_searchNoFilter ver020_netSrc 2 10000 (fun _ => false) = some [[0, 1], [1]] := by
    decide
  have hsiph : Siphon ver020_netSrc (· = 1) := by
    intro ft hft ⟨p, hp, hout⟩
    simp only [ver020_netSrc, List.mem_singleton] at hft
    subst hft hp
    simp at hout
  have := (h.1 _ _ _ _ _ hs [0, 1] (by simp)).2.2.2 (· = 1) ⟨1, rfl⟩ hsiph (by simp) 0 (by simp)
  simp at this

/-- Line 2 forbids the padding search of the pre-fix Rust: on `t1: a + c → b + c`, `t2: b → a`
it returns only `{a, b, c}`, which is not inside the siphon `{a, b}`. With it the check proved
this dead net deadlock-free (`SiphonSearch.pre_fix_padding_proves_dead_net`). -/
@[evidence forbids VER_020]
theorem VER_020_forbids_padding :
    ¬ VER_020 ver020_searchPadding refMaxTrap refStructCheck := by
  intro h
  have hs : ver020_searchPadding netPad 3 10000 (fun _ => false) = some [[0, 1, 2]] := by
    decide
  have hsiph : Siphon netPad (fun p => p = 0 ∨ p = 1) := by
    intro ft hft _
    simp only [netPad, List.mem_cons, List.not_mem_nil, or_false] at hft
    rcases hft with rfl | rfl
    · exact ⟨0, Or.inl rfl, ⟨0, .one, none⟩, by simp [tP1], rfl, by decide⟩
    · exact ⟨1, Or.inr rfl, ⟨1, .one, none⟩, by simp [tP2], rfl, by decide⟩
  obtain ⟨K, hK, hKS⟩ := h.2.1 netPad 3 10000 (fun _ => false) _ hs (fun p => p = 0 ∨ p = 1)
    (fun p hp => by rcases hp with rfl | rfl <;> decide) ⟨0, Or.inl rfl⟩ hsiph
  simp only [List.mem_singleton] at hK
  subst hK
  have := hKS 2 (by simp)
  simp at this

/-- Line 3 forbids a contraction that returns the siphon unchanged: on `t: a →` the siphon
`{a}` is not a trap. -/
@[evidence forbids VER_020]
theorem VER_020_forbids_noContract :
    ¬ VER_020 refSiphonSearch ver020_trapNoContract refStructCheck := by
  intro h
  have hT := (h.2.2.1 ver020_netDrain 1 [0] (by simp)).2.1
  obtain ⟨q, hq, hout⟩ := hT (ver020_tDrain, []) (by simp [ver020_netDrain])
    ⟨0, by simp [ver020_trapNoContract], ⟨0, .one, none⟩, by simp [ver020_tDrain], rfl, by decide⟩
  simp at hout

/-- Line 4 forbids the check without the empty-net guard: on one marked place and no transition
it answers no potential deadlock, where the guarded check answers inconclusive
(`SiphonSearch.empty_net_structural_proven_dead`). -/
@[evidence forbids VER_020]
theorem VER_020_forbids_unguarded :
    ¬ VER_020 refSiphonSearch refMaxTrap ver020_checkUnguarded := by
  intro h
  have := h.2.2.2.1 [] 1 (fun _ => false) aOne
  revert this
  decide

/-- Line 4 forbids a check that accepts a nonempty but unmarked trap: on the ring `a ⇄ b` from
the empty marking it answers no potential deadlock, and the net is dead
(`SiphonSearch.pre_fix_unmarked_trap_proves_dead_net`). -/
@[evidence forbids VER_020]
theorem VER_020_forbids_nonemptyTrap :
    ¬ VER_020 refSiphonSearch refMaxTrap ver020_checkNonemptyTrap := by
  intro h
  have := h.2.2.2.1 netCyc 2 (fun _ => false) (fun _ => 0)
  revert this
  decide

/-- Line 4 forbids a check without the 50-place cut: on 51 places it answers where the check
must answer inconclusive. -/
@[evidence forbids VER_020]
theorem VER_020_forbids_noPlaceCut :
    ¬ VER_020 refSiphonSearch refMaxTrap ver020_checkNoPlaceCut := by
  intro h
  have := h.2.2.2.1 ver020_netLoop 51 (fun _ => false) (fun _ => 1)
  revert this
  decide

/-- Line 4 forbids a check that passes the reference search a budget of 10 nodes: on `t: a → a`
with 20 places its search runs out and it answers inconclusive, where the search at 10 000
nodes returns. Line 4 fixes the number the check passes, not how the search spends it: a search
that ignores its budget argument and stops at 10 nodes of its own, under a check that passes
10 000, is not forbidden (see the assumes line of line 4). -/
@[evidence forbids VER_020]
theorem VER_020_forbids_budget :
    ¬ VER_020 refSiphonSearch refMaxTrap ver020_checkBudget := by
  intro h
  have := h.2.2.2.1 ver020_netLoop 20 (fun _ => false) (fun _ => 1)
  revert this
  decide

/-- The check line 4 builds around a search `F` with the reference contraction: a mutant search
paired with this check breaks no line but the ones about the search. -/
def ver020_checkOf (F : Ver020Search) : Ver020Check :=
  fun net n stop a0 =>
    if 50 < n || net.isEmpty then .inconclusive
    else
      match F net n 10000 stop with
      | none => .inconclusive
      | some sips =>
        if sips.all (fun sip => (refMaxTrap net n sip).any fun p => decide (0 < a0 p))
        then .noPotentialDeadlock else .potentialDeadlock

/-- A search that never returns, as one that reports its budget spent at once. -/
def ver020_searchNever : Ver020Search := fun _ _ _ _ => none

/-- A search that does not read the stop oracle. -/
def ver020_searchIgnoresStop : Ver020Search :=
  fun net n b _ => findMinimalSiphons net n b (fun _ => false)

/-- Line 5 forbids a search that never returns. With the check of line 4 around it (inconclusive
everywhere) it satisfies lines 1 to 4, which say nothing until the search returns; on the ring
of AC4 it finds no siphon. -/
@[evidence forbids VER_020]
theorem VER_020_forbids_neverReturns :
    ¬ VER_020 ver020_searchNever refMaxTrap (ver020_checkOf ver020_searchNever) :=
  fun h => h.2.2.2.2.1.1 rfl

/-- Line 6 forbids a search that does not read the stop oracle: on `t: a → a` with one place and
a total budget spent before it starts, it still returns `{a}`, and with the check of line 4 the
structural route answers past the total budget. -/
@[evidence forbids VER_020]
theorem VER_020_forbids_ignoresStop :
    ¬ VER_020 ver020_searchIgnoresStop refMaxTrap (ver020_checkOf ver020_searchIgnoresStop) := by
  intro h
  have := h.2.2.2.2.2 ver020_netLoop 1 10000 (by decide)
  revert this
  decide

/-! ## VER-020 (B): when the structural answer becomes a `Proven` -/

/-- **What the structural route reads** of the net it receives: whether the property is
`DeadlockFree`, whether the net declares a match (ν-join) transition ([NU-020]), whether a
transition is reapable ([VER-002]) and whether `assumeNoReaping` is set, the flat net with its
place count, the declared sinks and conditional sinks, and the environment places registered on
the net it receives. The route runs after the `Arrivals` rewrite of [VER-006], which closes the
net and clears the registration, so under `Arrivals` the list is empty; under `AlwaysAvailable`,
`Bounded` and `Ignore` no rewrite runs and it holds the environment places the caller
registered. -/
structure StructInput (K : Type) where
  /-- Whether the property is `DeadlockFree`. -/
  deadlockFree : Bool
  /-- Whether the net declares a match (ν-join) transition ([NU-020]). -/
  hasMatch : Bool
  /-- Whether some transition is reapable ([VER-002]). -/
  reapable : Bool
  /-- Whether `assumeNoReaping` is set. -/
  assumeNoReaping : Bool
  /-- The flat net the check reads. -/
  flat : FlatNet
  /-- The flat net's place count. -/
  n : Nat
  /-- The declared sinks. -/
  sinks : List K
  /-- The markers of the declared conditional sinks. -/
  condSinks : List K
  /-- The environment places registered on the net the route receives: none after the
  `Arrivals` rewrite. -/
  envPlaces : List K

/-- **The structural route**: from the structural check, what the route reads of the net, the
stop oracle and the initial marking, whether the verifier answers `Proven` from the check. -/
abbrev StructRouteFn (K : Type) : Type :=
  Ver020Check → StructInput K → (Nat → Bool) → AMarking → Bool

/-- The arc test of the structural guard (`commoner_applies`, `smt_verifier.rs`): no read,
inhibitor or reset arc, and every input arc neither consume-all nor of weight above one. -/
def commonerApplies (net : FlatNet) : Bool :=
  net.all fun ft => ft.1.inhibitors.isEmpty && ft.1.reads.isEmpty && ft.1.resets.isEmpty &&
    ft.1.inputs.all fun s => !s.card.consumesAll && decide (s.card.required ≤ 1)

/-- The arc test is exactly `Commoner.Ordinary`, the premise of Commoner's theorem. -/
theorem commonerApplies_iff (net : FlatNet) : commonerApplies net = true ↔ Ordinary net := by
  simp [commonerApplies, Ordinary, List.all_eq_true, and_assoc]

/-- **The reference guard** (`structural_candidate`, `smt_verifier.rs`; `SmtVerifier.java` and
`smt-verifier.ts` compute the same conjunction): `DeadlockFree`, no match transition, no reapable
transition unless `assumeNoReaping`, the arc test, no sink, no conditional sink, no environment
place registered on the net it receives. -/
def refStructGate {K : Type} (x : StructInput K) : Bool :=
  x.deadlockFree && !x.hasMatch && (!x.reapable || x.assumeNoReaping) &&
    commonerApplies x.flat && x.sinks.isEmpty && x.condSinks.isEmpty && x.envPlaces.isEmpty

/-- **The reference route**: `Proven` exactly when the guard passes and the check answers no
potential deadlock. -/
def refStructRoute {K : Type} : StructRouteFn K := fun C x stop a0 =>
  refStructGate x && decide (C x.flat x.n stop a0 = .noPotentialDeadlock)

#spec_witness refStructRoute

requirement VER_020_guard
  id "VER-020"
  title "Siphon and Trap Analysis: Structural Proven Guard"
  kind B
  scope "the verifier's structural route (the step that turns the structural check's answer into a Proven) of every implementation"
  source verbatim "spec/07-verification.md"
  quote "The verifier *shall* convert a no-potential-deadlock answer into a `Proven` only when it decides `DeadlockFree` on a net with no match transition ([NU-020]), no reapable transition ([VER-002]) unless `assumeNoReaping` is set, no read, inhibitor or reset arc, no consume-all input, no input arc weight above one, no declared sink or conditional sink and no environment place registered on the net it decides (the `Arrivals` rewrite of [VER-006] leaves none)."
  reading "For every structural check C, input x, stop oracle stop and initial marking a0: when R answers Proven, C answers no potential deadlock on the flat net of x with its place count, stop and a0; the property is DeadlockFree; x has no match transition; no transition is reapable or assumeNoReaping is set; the flat net is ordinary (no inhibitor, read or reset arc, every input arc neither consume-all nor of weight above one); and the declared sinks, the conditional sinks and the environment places registered on the net the route receives are all empty."
  assumes "The model is a route R : StructRouteFn over StructInput, what the route reads of the net it receives: the property as the flag deadlockFree, the flags hasMatch, reapable and assumeNoReaping, the flat net with its place count (Soundness.FlatNet, as in VER_020), the declared sinks, the markers of the declared conditional sinks, and the environment places registered on the net it receives. The witness is refStructRoute: refStructGate (structural_candidate in smt_verifier.rs, the same conjunction in SmtVerifier.java and smt-verifier.ts) and the check's answer. R takes the check C as an argument and the line holds for every C, so the line does not depend on the check being the one of VER_020; VER_020_guard_sound composes the two blocks."
          "'Registered on the net it decides (the Arrivals rewrite of VER-006 leaves none)' is the W1 review note W1-SK-7: under Arrivals and ArrivalsBetween all three verifiers close the net and clear the environment places before any route (with_arrivals in smt_verifier.rs, applyArrivals in SmtVerifier.java and smt-verifier.ts), Arrivals(0) included; under AlwaysAvailable, Bounded and Ignore no rewrite runs, the registered places stay and the route does not run. The field envPlaces is the list on the net the route receives, and the formula is the one the older wording 'no registered environment place' gives; the parenthesis names which net that is. That the rewrite clears the list is VER-006's (VER_006_arrivals assumes, kind N there): the closure of Novel/EnvSemantics returns rows and a marking, no registration. What the rewrite leaves the route is VER_020_guard_arrivals, on the reference closure of VER-006: under Arrivals(0) nothing is added and the route proves t: a → a; once an arrival is injected the closure adds a source place that no transition refills, so the source is a siphon with no trap inside it and the check answers potential deadlock (shown under Arrivals(1, 1); the optional source of Arrivals(k) with k ≥ 1 is the same kind of siphon). So the structural route proves a net whose places were registered only under Arrivals(0); a closed net with a source goes to the other routes. A route that reads the places before the rewrite only refuses more and breaks no line; that the route does prove on the net it receives is the offer in Ver020GuardCovers, which such a route fails."
          "'No input arc weight above one' reads the pre vector, as commoner_applies does in all three runtimes (pre[p] ≤ 1); an output weight above one is not refused, and Commoner's argument does not need it refused: a dead marking's empty places form a siphon whatever the outputs deposit, and a trap stays marked whatever they deposit. The model takes one input arc per place (InputsDistinctPlaces of Soundness.lean), which CORE-030 AC3 makes true of every net the verifier sees: building a transition with two input arcs on one place fails (TransitionBuilder::build in transition.rs, the same check in Java and TypeScript), so the summed pre[p] of the flattener is the arc's required count. The per-arc reading would not be enough without it: t: one(a) one(a) → a from {a:1} passes a per-arc test and is dead at once. commonerApplies_iff shows the arc test is Commoner.Ordinary. 'Read, inhibitor or reset arc' and 'consume-all input' are the other conjuncts of Ordinary. The read arc of the flat net is ft.1.reads."
          "The line is the safety half ('only when'). That the route does prove when every conjunct holds and the check answers no potential deadlock is an offer, so it is the coverage clause Ver020GuardCovers with its reference proof refStructRoute_covers, for the consistency theorem (convention of GlossaryExec), not a line. That a structural Proven is reported with the method structural and the route Structural, and that the report says why the route did not run, are kind Q."
          "The paragraph 'A match transition hides a dead marking from the flat net' is the reason for the match conjunct: VER_020_guard_match shows a ν-join net whose flat net passes the check, so no marking reachable in the flat net is dead, while the ν net, with different names on the two joined places, is stuck at its initial marking. VER_020_guard_forbids_noMatch kills the route without the match conjunct on that net. Its last sentence (the route does not decide a net with a reapable transition unless assumeNoReaping is set) is the reapable conjunct, killed by VER_020_guard_forbids_noReap; the timed reading behind it is SiphonSearch.structural_proven_sound_timed."
          "The 'Commoner's theorem governs ORDINARY nets only' paragraph: its list of disablements the fixpoints do not see ('a read arc, an inhibitor arc, a reset arc, a consume-all input or an input arc weight above one') is Ordinary, and its MUST sentence ('MUST therefore refuse to do so for any net carrying one of them, exactly as it already refuses when sinks are declared or environment places are registered on the net it decides') is the Ordinary, sink and environment conjuncts. Its three witnesses each pass the check and fail the arc test, so the reference route does not prove them (VER_020_guard_nonvacuous); a route without the arc test is killed on the exactly(2) witness (VER_020_guard_forbids_noOrdinary)."
          "AC3 (a structural Proven only for DeadlockFree on a net with no match transition, no reapable transition unless assumeNoReaping, no read, inhibitor or reset arc, no consume-all input, no input arc weight above one, no declared sink or conditional sink and no environment place registered on the net the verifier decides; each of the three witnesses decided by another route; never for a net with no transition) is the line, conjunct by conjunct, with one forbids theorem per conjunct and one for a route that ignores the check's answer (VER_020_guard_forbids_ignoresCheck). 'Decided by another route' and that the one-place witness is Violated are the other routes' (VER-017, the fixpoint query), not this line's. 'Never for a net with no transition' is the empty-net guard of VER_020 line 4: the check answers inconclusive there, and the line asks for a no-potential-deadlock answer. AC1, AC2 and AC4 are VER_020's."
  signoff "2026-11-13 e2ac0ef51eab9ee2 ai"
  statement : ∀ {K : Type}, StructRouteFn K → Prop :=
    fun R => ∀ (C : Ver020Check) (x : StructInput _) (stop : Nat → Bool) (a0 : AMarking),
      R C x stop a0 = true →
        C x.flat x.n stop a0 = .noPotentialDeadlock ∧ x.deadlockFree = true ∧
        x.hasMatch = false ∧ (x.reapable = false ∨ x.assumeNoReaping = true) ∧
        Ordinary x.flat ∧ x.sinks = [] ∧ x.condSinks = [] ∧ x.envPlaces = []

/- The pinned readable form of VER-020's guard block. -/
/--
info: def Libpetri.Spec.VER_020_guard : {K : Type} → StructRouteFn K → Prop :=
fun {K} R =>
  ∀ (C : Ver020Check) (x : StructInput K) (stop : ℕ → Bool) (a0 : AMarking),
    R C x stop a0 = true →
      C x.flat x.n stop a0 = Verdict.noPotentialDeadlock ∧
        x.deadlockFree = true ∧
          x.hasMatch = false ∧
            (x.reapable = false ∨ x.assumeNoReaping = true) ∧
              Ordinary x.flat ∧ x.sinks = [] ∧ x.condSinks = [] ∧ x.envPlaces = []
-/
#guard_msgs in #print VER_020_guard

/-! ### The reference -/

/-- The reference route meets the guard: it answers `Proven` only when its guard passes, and
each conjunct of the guard is a conjunct of the line (`commonerApplies_iff` for the arc test). -/
@[evidence holds VER_020_guard]
theorem VER_020_guard_reference {K : Type} : VER_020_guard (refStructRoute (K := K)) := by
  intro C x stop a0 h
  simp only [refStructRoute, refStructGate, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hd, hm⟩, hr⟩, ho⟩, hs⟩, hc⟩, he⟩, hC⟩ := h
  exact ⟨hC, hd, hm, hr.imp id id, (commonerApplies_iff _).1 ho, hs, hc, he⟩

/-- **The offer** (coverage, not a line): the route answers `Proven` whenever every conjunct of
the guard holds and the check answers no potential deadlock, the environment places read on the
net the route receives. Under `Arrivals(0)` that is the net itself with its registration
cleared, so the route proves it when the check passes. Once an arrival is injected the closed
net has a source place no transition refills; it is a siphon with no trap inside it, so the
check does not pass and the offer asks nothing (`VER_020_guard_arrivals`). -/
def Ver020GuardCovers {K : Type} (R : StructRouteFn K) : Prop :=
  ∀ (C : Ver020Check) (x : StructInput K) (stop : Nat → Bool) (a0 : AMarking),
    C x.flat x.n stop a0 = .noPotentialDeadlock → x.deadlockFree = true → x.hasMatch = false →
    (x.reapable = false ∨ x.assumeNoReaping = true) → Ordinary x.flat → x.sinks = [] →
    x.condSinks = [] → x.envPlaces = [] → R C x stop a0 = true

/-- The reference route makes the offer. -/
theorem refStructRoute_covers {K : Type} : Ver020GuardCovers (refStructRoute (K := K)) := by
  intro C x stop a0 hC hd hm hr ho hs hc he
  have ho' := (commonerApplies_iff _).2 ho
  simp only [refStructRoute, refStructGate, hd, hm, ho', hs, hc, he, hC, List.isEmpty_nil,
    Bool.not_false, Bool.true_and, Bool.and_true, decide_true]
  rcases hr with hr | hr <;> simp [hr]

/-- **A structural `Proven` rules out every reachable dead marking of the flat net**, from the
two blocks alone: when the route answers `Proven` with a check that meets VER-020, on a net whose
input arcs lie below `n`, no marking reachable under the untimed relation `ReachA` is dead. The
guard gives the ordinary premise and the no-potential-deadlock answer; `VER_020_commoner` does
the rest. -/
@[evidence cites "VER-020" "AC2 and AC3: a structural Proven, given only behind the guard, rules out every dead marking reachable in the flat net"]
theorem VER_020_guard_sound {K : Type} {F : Ver020Search} {T : Ver020Trap} {C : Ver020Check}
    {R : StructRouteFn K} (hc : VER_020 F T C) (hg : VER_020_guard R) {x : StructInput K}
    {stop : Nat → Bool} {a0 : AMarking} (hbelow : InputsBelow x.flat x.n)
    (hR : R C x stop a0 = true) {a : AMarking} (hr : ReachA x.flat a0 a) : ¬ Dead x.flat a :=
  have h := hg C x stop a0 hR
  VER_020_commoner hc h.2.2.2.2.1 hbelow h.1 hr

/-! ### The ν-join net: why the match conjunct guards soundness -/

/-- The flat join `a + b → c` (places `a b c` = `0 1 2`). -/
def ver020_tJoin : Transition :=
  { name := "join", inputs := [⟨0, .one, none⟩, ⟨1, .one, none⟩], inhibitors := [], reads := [],
    resets := [] }

/-- The flat fork `c → a + b`. -/
def ver020_tFork : Transition :=
  { name := "fork", inputs := [⟨2, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- The flat net of the ν-join net: the join and the fork, names dropped. -/
def ver020_netJoin : FlatNet := [(ver020_tJoin, [2]), (ver020_tFork, [0, 1])]

/-- One token on `a` and one on `b`. -/
def ver020_a0Join : AMarking := fun p => if p = 0 ∨ p = 1 then 1 else 0

/-- The key of the ν join: a token's name is its value. -/
def ver020_nuKey : KeyFn Nat Nat := some

/-- The match of the ν join: places `a` and `b` joined by name. -/
def ver020_nuMs : MatchSpec Nat (KeyFn Nat Nat) := { keys := [(0, ver020_nuKey), (1, ver020_nuKey)] }

/-- The ν join `a + b → c`, matched on `a` and `b`. -/
def ver020_nuJoin : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "join", inputs := [⟨0, .one⟩, ⟨1, .one⟩], inhibitors := [],
                        reads := [], resets := [] }, out := some (.place 2) }
    mspec := some ver020_nuMs }

/-- The fork `c → a + b`, no match. -/
def ver020_nuFork : NuTrans Nat (KeyFn Nat Nat) :=
  { base := { core := { name := "fork", inputs := [⟨2, .one⟩], inhibitors := [], reads := [],
                        resets := [] }, out := some (.and (.place 0) (.place 1)) } }

/-- The ν-join net: the matched join and the fork. -/
def ver020_nuNet : List (NuTrans Nat (KeyFn Nat Nat)) := [ver020_nuJoin, ver020_nuFork]

/-- Its initial marking: a token of name 1 on `a`, a token of name 2 on `b`. -/
def ver020_nuM0 : Reference.QMarking Nat (Stamped Nat) := fun p =>
  if p = 0 then [⟨1, 0⟩] else if p = 1 then [⟨2, 0⟩] else []

/-- The ν net's initial counts are the flat net's initial marking. -/
theorem ver020_nuM0_count (p : Nat) : Reference.qCount ver020_nuM0 p = ver020_a0Join p := by
  unfold Reference.qCount ver020_nuM0 ver020_a0Join
  by_cases h0 : p = 0
  · simp [h0]
  · by_cases h1 : p = 1 <;> simp [h0, h1]

/-- **The flat net hides the ν net's dead marking.** Example: a join of `a` and `b` into `c`,
and a fork of `c` back into `a` and `b`, with one token on `a` and one on `b`. The flat net,
which counts tokens and drops names, passes the structural check: its minimal siphons `{a, c}`
and `{b, c}` are traps marked from the start, so no marking reachable in the flat net is dead.
In the ν net the token on `a` has name 1 and the one on `b` name 2, so the join finds no common
name and the fork has nothing on `c`: no transition can fire and the net is stuck at once. A
structural `Proven` would be wrong, which is why the route refuses a net with a match transition. -/
@[evidence cites "VER-020" "A match transition hides a dead marking from the flat net: a ν-join net whose flat net passes the structural check is stuck at its initial marking"]
theorem VER_020_guard_match :
    refStructCheck ver020_netJoin 3 (fun _ => false) ver020_a0Join = .noPotentialDeadlock ∧
    (∀ a, ReachA ver020_netJoin ver020_a0Join a → ¬ Dead ver020_netJoin a) ∧
    (∀ M', ¬ Reference.RefNuStep ver020_nuNet ver020_nuM0 M') := by
  have hC : refStructCheck ver020_netJoin 3 (fun _ => false) ver020_a0Join =
      .noPotentialDeadlock := by decide
  refine ⟨hC, fun a hr => VER_020_commoner VER_020_reference
    ((commonerApplies_iff _).1 (by decide)) (by unfold InputsBelow; decide) hC hr, ?_⟩
  rintro M' ⟨t, ht, c, δ, e, hf⟩
  have hen := Reference.refNuFire_nuEnabled hf
  simp only [ver020_nuNet, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · obtain ⟨n, hn⟩ := hen.2 ver020_nuMs rfl
    have h := (refSelect_spec _).2 ⟨n, hn⟩
    have h0 : refSelect (matchIn ver020_nuMs ver020_nuJoin ver020_nuM0) = none := by decide
    rw [h0] at h
    cases h
  · have := hen.1
    revert this
    decide

/-! ### Examples -/

/-- `t: one(a) read(g) → g`, `t2: one(g) → a` (places `a g` = `0 1`), the read witness. -/
def ver020_tRead1 : Transition :=
  { name := "t1", inputs := [⟨0, .one, none⟩], inhibitors := [], reads := [1], resets := [] }

/-- The second transition of the read witness. -/
def ver020_tRead2 : Transition :=
  { name := "t2", inputs := [⟨1, .one, none⟩], inhibitors := [], reads := [], resets := [] }

/-- The read witness, dead at `{a:1}`. -/
def ver020_netRead : FlatNet := [(ver020_tRead1, [1]), (ver020_tRead2, [0])]

/-- `t: one(a) inhibitor(b) → a` (places `a b` = `0 1`), the inhibitor witness. -/
def ver020_tInh : Transition :=
  { name := "t", inputs := [⟨0, .one, none⟩], inhibitors := [1], reads := [], resets := [] }

/-- The inhibitor witness, dead at `{a:1, b:1}`. -/
def ver020_netInh : FlatNet := [(ver020_tInh, [0])]

/-- The route's input for `t: a → a` with one place, every conjunct of the guard passing. -/
def ver020_x0 : StructInput Nat :=
  { deadlockFree := true, hasMatch := false, reapable := false, assumeNoReaping := false,
    flat := ver020_netLoop, n := 1, sinks := [], condSinks := [], envPlaces := [] }

/-- The route's input for the ν-join net: the flat net and a match transition. -/
def ver020_xJoin : StructInput Nat :=
  { ver020_x0 with hasMatch := true, flat := ver020_netJoin, n := 3 }

/-- ✓ **The guard on small nets.** `t: a → a` with a token on `a`: the check answers no
potential deadlock and the route proves it, also with a reapable transition under
`assumeNoReaping`, and also under `Arrivals(0)`, where nothing is injected, the net is left as
it is and the route reads it with no environment place left. It does not prove it with a
reapable transition and no `assumeNoReaping`, with an environment place registered on the net
it receives (the same net under `AlwaysAvailable`), with a declared sink, or for a property
other than `DeadlockFree`. The
ν-join net is refused. The three witnesses of the ordinary-nets paragraph (`one(a) read(g)`,
`exactly(2, a)`, `one(a) inhibitor(b)`) each pass the check, and the route proves none of them. -/
@[evidence nonvacuous VER_020_guard]
theorem VER_020_guard_nonvacuous :
    refStructRoute refStructCheck ver020_x0 (fun _ => false) (fun _ => 1) = true ∧
    refStructRoute refStructCheck { ver020_x0 with reapable := true, assumeNoReaping := true }
      (fun _ => false) (fun _ => 1) = true ∧
    refStructRoute refStructCheck { ver020_x0 with reapable := true } (fun _ => false)
      (fun _ => 1) = false ∧
    refStructRoute refStructCheck { ver020_x0 with envPlaces := [0] } (fun _ => false)
      (fun _ => 1) = false ∧
    refStructRoute refStructCheck { ver020_x0 with sinks := [0] } (fun _ => false)
      (fun _ => 1) = false ∧
    refStructRoute refStructCheck { ver020_x0 with deadlockFree := false } (fun _ => false)
      (fun _ => 1) = false ∧
    refStructCheck ver020_netJoin 3 (fun _ => false) ver020_a0Join = .noPotentialDeadlock ∧
    refStructRoute refStructCheck ver020_xJoin (fun _ => false) ver020_a0Join = false ∧
    refStructCheck ver020_netRead 2 (fun _ => false) aOne = .noPotentialDeadlock ∧
    refStructRoute refStructCheck { ver020_x0 with flat := ver020_netRead, n := 2 }
      (fun _ => false) aOne = false ∧
    refStructCheck netEx 1 (fun _ => false) a0Ex = .noPotentialDeadlock ∧
    refStructRoute refStructCheck { ver020_x0 with flat := netEx } (fun _ => false) a0Ex = false ∧
    refStructCheck ver020_netInh 2 (fun _ => false) (fun _ => 1) = .noPotentialDeadlock ∧
    refStructRoute refStructCheck { ver020_x0 with flat := ver020_netInh, n := 2 }
      (fun _ => false) (fun _ => 1) = false := by
  decide

/-- ✓ **What the `Arrivals` rewrite leaves the route**, on the reference closure of [VER-006].
Example: `t: a → a` with a token on `a`, and `a` registered as an environment place. Under
`Arrivals(0)` nothing is injected: the closure adds no place and no transition, the
registration is cleared, and the route proves the net. Under `Arrivals(1, 1)` the closure adds a
source holding one token and a transition that moves it to `a`. Nothing puts a token back into
the source, so the source alone is a siphon, and the one transition that takes from it puts
nothing back, so no trap lies inside it. The check answers potential deadlock and the route
does not prove the net, although `t` keeps its token on `a` and can always fire again. Such a
net goes to the other routes. -/
@[evidence cites "VER-020" "no environment place registered on the net it decides (the Arrivals rewrite of VER-006 leaves none)"]
theorem VER_020_guard_arrivals :
    EnvSemantics.closureRows ver020_netLoop [0] 1 0 0 = ver020_netLoop ∧
    refStructRoute refStructCheck
      { ver020_x0 with flat := EnvSemantics.closureRows ver020_netLoop [0] 1 0 0 }
      (fun _ => false) (EnvSemantics.closureM0 (fun _ => 1) [0] 1 0 0) = true ∧
    commonerApplies (EnvSemantics.closureRows ver020_netLoop [0] 1 1 1) = true ∧
    refStructCheck (EnvSemantics.closureRows ver020_netLoop [0] 1 1 1) 2 (fun _ => false)
      (EnvSemantics.closureM0 (fun _ => 1) [0] 1 1 1) = .potentialDeadlock ∧
    refStructRoute refStructCheck
      { ver020_x0 with flat := EnvSemantics.closureRows ver020_netLoop [0] 1 1 1, n := 2 }
      (fun _ => false) (EnvSemantics.closureM0 (fun _ => 1) [0] 1 1 1) = false :=
  ⟨by simp [EnvSemantics.closureRows, EnvSemantics.envRows, EnvSemantics.groupRows],
    by decide, by decide, by decide, by decide⟩

/-! ### Wrong routes -/

/-- A route that also reads the environment places `pre` registered before the `Arrivals`
rewrite, as if they were still on the net it receives. -/
def ver020_routePreRewrite (pre : List Nat) : StructRouteFn Nat := fun C x stop a0 =>
  refStructRoute C { x with envPlaces := x.envPlaces ++ pre } stop a0

/-- ✓ The line allows a route that reads the registration from before the `Arrivals` rewrite:
it only refuses more. The offer rules it out. Example: `t: a → a` with a token on `a`, and `a`
registered before an `Arrivals(0)` rewrite cleared it. The check passes and every conjunct of
the guard holds on the net the route receives, but the route still counts `a` as registered
and refuses, so it never gives the `Proven` that `Ver020GuardCovers` asks for. -/
@[evidence allows VER_020_guard]
theorem VER_020_guard_allows_preRewrite :
    VER_020_guard (ver020_routePreRewrite [0]) ∧
      ¬ Ver020GuardCovers (ver020_routePreRewrite [0]) := by
  refine ⟨fun C x stop a0 h => ?_, fun hc => ?_⟩
  · have := VER_020_guard_reference C { x with envPlaces := x.envPlaces ++ [0] } stop a0 h
    simp at this
  · have := hc refStructCheck ver020_x0 (fun _ => false) (fun _ => 1) (by decide) rfl rfl
      (Or.inl rfl) ((commonerApplies_iff _).1 (by decide)) rfl rfl rfl
    revert this
    decide

/-- A route that proves whenever the guard passes, without reading the check's answer. -/
def ver020_routeIgnoresCheck : StructRouteFn Nat := fun _ x _ _ => refStructGate x

/-- The route without the `DeadlockFree` conjunct. -/
def ver020_routeNoDlf : StructRouteFn Nat := fun C x stop a0 =>
  refStructRoute C { x with deadlockFree := true } stop a0

/-- The route without the match conjunct. -/
def ver020_routeNoMatch : StructRouteFn Nat := fun C x stop a0 =>
  refStructRoute C { x with hasMatch := false } stop a0

/-- The route without the reapable conjunct. -/
def ver020_routeNoReap : StructRouteFn Nat := fun C x stop a0 =>
  refStructRoute C { x with reapable := false } stop a0

/-- The route without the arc test (`commoner_applies`). -/
def ver020_routeNoOrdinary : StructRouteFn Nat := fun C x stop a0 =>
  x.deadlockFree && !x.hasMatch && (!x.reapable || x.assumeNoReaping) && x.sinks.isEmpty &&
    x.condSinks.isEmpty && x.envPlaces.isEmpty &&
    decide (C x.flat x.n stop a0 = .noPotentialDeadlock)

/-- The route without the sink conjunct. -/
def ver020_routeNoSink : StructRouteFn Nat := fun C x stop a0 =>
  refStructRoute C { x with sinks := [] } stop a0

/-- The route without the conditional-sink conjunct. -/
def ver020_routeNoCondSink : StructRouteFn Nat := fun C x stop a0 =>
  refStructRoute C { x with condSinks := [] } stop a0

/-- The route without the environment-place conjunct. -/
def ver020_routeNoEnv : StructRouteFn Nat := fun C x stop a0 =>
  refStructRoute C { x with envPlaces := [] } stop a0

/-- ✗ A route that ignores the check's answer: on `t: a → a` with `a` empty the check answers
potential deadlock (the trap `{a}` is unmarked), and this route still proves the net. -/
@[evidence forbids VER_020_guard]
theorem VER_020_guard_forbids_ignoresCheck : ¬ VER_020_guard ver020_routeIgnoresCheck := by
  intro h
  have := (h refStructCheck ver020_x0 (fun _ => false) (fun _ => 0) (by decide)).1
  revert this
  decide

/-- ✗ A route that proves other properties too: with the property not `DeadlockFree`, on
`t: a → a` with a token on `a`, it still answers `Proven` from the check. -/
@[evidence forbids VER_020_guard]
theorem VER_020_guard_forbids_noDlf : ¬ VER_020_guard ver020_routeNoDlf := by
  intro h
  have := (h refStructCheck { ver020_x0 with deadlockFree := false } (fun _ => false)
    (fun _ => 1) (by decide)).2.1
  revert this
  decide

/-- ✗ A route that does not refuse a match transition: on the ν-join net it proves deadlock
freedom from the flat net, while the ν net is stuck at its initial marking
(`VER_020_guard_match`). -/
@[evidence forbids VER_020_guard]
theorem VER_020_guard_forbids_noMatch : ¬ VER_020_guard ver020_routeNoMatch := by
  intro h
  have := (h refStructCheck ver020_xJoin (fun _ => false) ver020_a0Join (by decide)).2.2.1
  revert this
  decide

/-- ✗ A route that does not refuse a reapable transition: on `t: a → a` with the transition
reapable and no `assumeNoReaping`, it proves a net that can rest with the transition still
enabled ([VER-002]). -/
@[evidence forbids VER_020_guard]
theorem VER_020_guard_forbids_noReap : ¬ VER_020_guard ver020_routeNoReap := by
  intro h
  have := (h refStructCheck { ver020_x0 with reapable := true } (fun _ => false) (fun _ => 1)
    (by decide)).2.2.2.1
  revert this
  decide

/-- ✗ A route without the arc test: on `t: exactly(2, a) → a` from `{a:1}`, the spec's second
witness, the check answers no potential deadlock and this route proves a net that is dead at
once. -/
@[evidence forbids VER_020_guard]
theorem VER_020_guard_forbids_noOrdinary : ¬ VER_020_guard ver020_routeNoOrdinary := by
  intro h
  have := (h refStructCheck { ver020_x0 with flat := netEx } (fun _ => false) a0Ex
    (by decide)).2.2.2.2.1
  rw [← commonerApplies_iff] at this
  revert this
  decide

/-- ✗ A route that does not refuse a declared sink: on `t: a → a` with `a` declared a sink it
proves the net. -/
@[evidence forbids VER_020_guard]
theorem VER_020_guard_forbids_noSink : ¬ VER_020_guard ver020_routeNoSink := by
  intro h
  have := (h refStructCheck { ver020_x0 with sinks := [0] } (fun _ => false) (fun _ => 1)
    (by decide)).2.2.2.2.2.1
  revert this
  decide

/-- ✗ A route that does not refuse a conditional sink: on `t: a → a` with a conditional sink
on `a` it proves the net. -/
@[evidence forbids VER_020_guard]
theorem VER_020_guard_forbids_noCondSink : ¬ VER_020_guard ver020_routeNoCondSink := by
  intro h
  have := (h refStructCheck { ver020_x0 with condSinks := [0] } (fun _ => false) (fun _ => 1)
    (by decide)).2.2.2.2.2.2.1
  revert this
  decide

/-- ✗ A route that does not refuse a registered environment place: on `t: a → a` with `a`
registered on the net it receives (under `AlwaysAvailable`, `Bounded` or `Ignore`, where no
rewrite runs), it proves the net, although tokens injected on `a` are not in the flat net the
check reads. -/
@[evidence forbids VER_020_guard]
theorem VER_020_guard_forbids_noEnv : ¬ VER_020_guard ver020_routeNoEnv := by
  intro h
  have := (h refStructCheck { ver020_x0 with envPlaces := [0] } (fun _ => false) (fun _ => 1)
    (by decide)).2.2.2.2.2.2.2
  revert this
  decide

/-- ✓ The two VER-020 blocks hold together with the offer: the reference siphon search,
contraction and check, and the reference route, which proves exactly behind the guard. -/
@[evidence consistent VER_020 VER_020_guard]
theorem VER_020_guard_joint {K : Type} :
    ∃ (F : Ver020Search) (T : Ver020Trap) (C : Ver020Check) (R : StructRouteFn K),
      VER_020 F T C ∧ VER_020_guard R ∧ Ver020GuardCovers R :=
  ⟨_, _, _, _, VER_020_reference, VER_020_guard_reference, refStructRoute_covers⟩

end Libpetri.Spec
