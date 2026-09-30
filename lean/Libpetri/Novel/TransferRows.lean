import Libpetri.Novel.Enumeration

/-!
# Drained forwards are transfers the graph routes decide ([IO-014], [VER-001] AC5, [VER-017])

A timeout `ForwardInput(src, dst)` from an `All` / `AtLeast` input deposits one token in `dst`
per token the firing drained from `src` ([IO-014]): a count that depends on the marking the
firing drains, a **transfer**. No constant row holds it (`ForwardDeposit.drained_forward_has_no_row`),
which is why every route that reads the flat net — the P-invariants, the linear bound, the state
equation, the firing bound, the CHC fixpoint query, Route A — refuses such a net
(`branch_outcomes::drained_forward`, checked in `verify_net` after the graph routes and before the
first linear one).

The graph routes do not read constant rows. The state-class graph expands a transition by
`branch_outcomes::outcomes`, where a drained forward is the symbolic `Deposit::Drained(src)`, and
`produce_marking` (`state_class_graph.rs`) resolves it through `Outcome::resolved` with the count
`input_consume_count(spec, marking.count(src))` of the marking the firing drains — for an
`All` / `AtLeast` input the whole available count ([IO-007]). This module models those
**marking-dependent rows** (`transferRows`) and proves that they are exactly what the executor
deposits, with no `FixedForwards` premise:

* `consumedAt_eq_consumedA`: on an unguarded consume-all arc the concrete consumption is a
  function of the token counts (`consumedA`), so the graph can compute it from the class's
  marking alone.
* `transfer_step_simulated` / `transferRows_mem_deposit`: every way a concrete firing ends —
  action branch or timeout, drained forwards included — is a row of `transferRows` at the
  α-image of the marking it fires in, with the same successor (`fireAD`), and every such row is
  a way a firing can end. So the transfer rows neither miss nor add an outcome.
* `transfer_reachability_simulated`: Proposition 1 over the transfer rows, `α(R(N)) ⊆ R(N̂ᵀ)`,
  for every net whose consume-all arcs are unguarded — drained forwards included.
* `transfer_enumeration_exact` / `transfer_enumeration_sound`: the enumeration loop of
  `Enumeration.lean` run with the transfer successor (`succTransfer`) decides exactly the
  transfer-row reachable set when it closes, and its `Proven` holds of the α-image of every
  concrete run. This is the coverage the fixed-row results (`forward_enumeration_sound`) lacked
  for `All` / `AtLeast` forwards.
* `transferRows_fixed`: on a spec whose forwards all draw from `One` / `Exactly` inputs the
  transfer rows are the fixed rows' members, so nothing changes for the nets the flat routes
  accept.

Premises, as in `Enumeration.lean`: the Rust successor over an untimed class is `fireAD` of one
of these rows (the symbolic `outcomes` list, resolved, has the same members up to the order of a
deposit and duplicates: `outcomes` keeps the drained timeout outcome even when it resolves to an
action branch's counts, which only repeats a successor), and class identity is marking equality.
Timing (the timed state-class graph resolves the same deposit, `produce_marking` being shared),
colours and environment places are out of scope, as there.
-/

namespace Libpetri.Novel.TransferRows

open Libpetri ForwardDeposit Enumeration

/-- Tokens one firing removes from `p`, read off token counts: the fixed `required_count` of a
`One` / `Exactly` input, the whole count of an `All` / `AtLeast` input, `0` off the inputs.
Models `input_consume_count(spec, marking.count(p))` (`state_class_graph.rs`), which
`produce_marking`'s `drained` closure applies to a forward's `from` place. -/
def consumedA (a : AMarking) (t : Transition) (p : PlaceId) : Nat :=
  match specAt t p with
  | none => 0
  | some s => if s.card.consumesAll then a p else s.card.required

/-- **The drained count is a function of the counts.** On an unguarded consume-all arc
(`GuardFreeConsumeAll`, as Proposition 1 requires) the executor drains every token of the place,
so the concrete consumption is `consumedA` of the α-image. -/
theorem consumedAt_eq_consumedA {m : CMarking} {t : Transition} (hG : GuardFreeConsumeAll t)
    (p : PlaceId) : consumedAt m t p = consumedA (alpha m) t p := by
  unfold consumedAt consumedA
  cases hs : specAt t p with
  | none => rfl
  | some s =>
    obtain ⟨hmem, hplace⟩ := specAt_sound hs
    simp only [consumeCount]
    cases hca : s.card.consumesAll with
    | false => rfl
    | true =>
      have hg : s.guard = none := hG s hmem hca
      simp [matchCount, hg, hplace, alpha]

/-- **The marking-dependent rows** of a transition at abstract marking `a`: the action branches,
then the timeout child's deposits with every forward resolved at `a` (`consumedA`). The graph's
`outcomes` + `Outcome::resolved`, as a list of deposits. -/
def transferRows (t : Transition) (o : OutSpec) (a : AMarking) : List Deposit :=
  match findTimeout o with
  | none => branches o
  | some c => branches o ++ timeoutDeposits (consumedA a t) c

/-- **Every way a firing ends is a transfer row** at the marking it fires in — drained forwards
included — with the successor the graph computes. -/
theorem transfer_step_simulated (m : CMarking) (t : Transition) (o : OutSpec)
    (hG : GuardFreeConsumeAll t) (hEn : enabledC m t = true) {ch : Choice} {d : Deposit}
    (h : deposit (consumedAt m t) o ch = some d) :
    d ∈ transferRows t o (alpha m) ∧ enabledA (alpha m) t = true ∧
      alphaFireC m t (fun p => d.count p) = fireAD (alpha m) t d := by
  obtain ⟨hEnA, hFire⟩ := prop1_step_deposit m t d hG hEn
  refine ⟨?_, hEnA, hFire⟩
  cases ch with
  | action i =>
    have hb : d ∈ branches o := List.mem_of_getElem? h
    unfold transferRows
    split
    · exact hb
    · exact List.mem_append_left _ hb
  | timedOut j =>
    simp only [deposit] at h
    cases hc : findTimeout o with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      simp only [Option.bind_some] at h
      have hd : d ∈ timeoutDeposits (consumedAt m t) c := List.mem_of_getElem? h
      have heq : timeoutDeposits (consumedAt m t) c = timeoutDeposits (consumedA (alpha m) t) c :=
        timeoutDeposits_congr c fun src _ => consumedAt_eq_consumedA hG src
      unfold transferRows
      rw [hc]
      exact List.mem_append_right _ (heq ▸ hd)

/-- **Every transfer row is a way a firing can end**: the rows add no deposit the executor never
makes at that marking. -/
theorem transferRows_mem_deposit {m : CMarking} {t : Transition} {o : OutSpec}
    (hG : GuardFreeConsumeAll t) {r : Deposit} (hr : r ∈ transferRows t o (alpha m)) :
    ∃ ch, deposit (consumedAt m t) o ch = some r := by
  unfold transferRows at hr
  split at hr
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    exact ⟨.action i, hi⟩
  · rename_i c hc
    rcases List.mem_append.mp hr with hb | ht
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
      exact ⟨.action i, hi⟩
    · have heq : timeoutDeposits (consumedAt m t) c =
          timeoutDeposits (consumedA (alpha m) t) c :=
        timeoutDeposits_congr c fun src _ => consumedAt_eq_consumedA hG src
      rw [← heq] at ht
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ht
      exact ⟨.timedOut j, by simp [deposit, hc, hj]⟩

/-- On a spec whose forwards all draw from `One` / `Exactly` inputs the resolved timeout deposits
are the fixed ones: `transferRows` and `fixedRows` have the same members, so the graph and the
flat routes read one expansion there. -/
theorem transferRows_fixed {t : Transition} {o c : OutSpec} (hFwd : FixedForwards t o)
    (hc : findTimeout o = some c) (a : AMarking) :
    timeoutDeposits (consumedA a t) c = timeoutDeposits (pre t) c :=
  timeoutDeposits_congr c fun src hs => by
    have hca := hFwd src (forwardSources_findTimeout hc src hs)
    unfold consumedA pre
    unfold consumeAllAt at hca
    cases hsp : specAt t src with
    | none => rfl
    | some s => rw [hsp] at hca; simp [hca]

/-! ## Reachability and the enumeration over transfer rows -/

/-- One abstract step of the graph over transfer rows: an enabled transition fires one of its
rows resolved at the current marking. -/
def StepAT (net : SpecNet) (a a' : AMarking) : Prop :=
  ∃ to ∈ net, enabledA a to.1 = true ∧ ∃ r ∈ transferRows to.1 to.2 a, a' = fireAD a to.1 r

/-- **Proposition 1 over transfer rows.** Every concrete run, whichever way each firing ends and
whatever each drained forward carries, is an abstract run of the transfer rows. Only the
consume-all arcs must be unguarded; no `FixedForwards` premise. -/
theorem transfer_reachability_simulated {net : SpecNet}
    (hG : ∀ to ∈ net, GuardFreeConsumeAll to.1) {m0 m : CMarking}
    (h : Relation.ReflTransGen (StepCD net) m0 m) :
    Relation.ReflTransGen (StepAT net) (alpha m0) (alpha m) := by
  refine Relation.ReflTransGen.lift alpha (fun x y hs => ?_) m0 m h
  obtain ⟨to, hmem, hEn, ch, d, hdep, hEff⟩ := hs
  obtain ⟨hd, hEnA, hFire⟩ := transfer_step_simulated x to.1 to.2 (hG to hmem) hEn hdep
  exact ⟨to, hmem, hEnA, d, hd, by rw [hEff, hFire]⟩

/-- The graph's successors over transfer rows: one per enabled transition and row, in order. -/
def succTransfer (net : SpecNet) (a : AMarking) : List AMarking :=
  net.flatMap fun to =>
    if enabledA a to.1 = true then (transferRows to.1 to.2 a).map (fireAD a to.1) else []

theorem succTransfer_iff_step (net : SpecNet) (a b : AMarking) :
    b ∈ succTransfer net a ↔ StepAT net a b := by
  unfold succTransfer StepAT
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨to, hmem, hb⟩
    split at hb
    · rename_i hen
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
      exact ⟨to, hmem, hen, r, hr, rfl⟩
    · simp at hb
  · rintro ⟨to, hmem, hen, r, hr, rfl⟩
    exact ⟨to, hmem, by rw [if_pos hen]; exact List.mem_map.mpr ⟨r, hr, rfl⟩⟩

theorem reach_succTransfer_iff (net : SpecNet) (a0 a : AMarking) :
    Reach (succTransfer net) a0 a ↔ Relation.ReflTransGen (StepAT net) a0 a := by
  unfold Reach
  have : (fun x y => y ∈ succTransfer net x) = StepAT net := by
    funext x y
    exact propext (succTransfer_iff_step net x y)
  rw [this]

/-- **[VER-017] over transfer rows.** If the enumeration closes, its classes are exactly the
markings the transfer rows reach, and reading a bad predicate off them decides it exactly. -/
theorem transfer_enumeration_exact {net : SpecNet} {maxClasses fuel : Nat} {a0 : AMarking}
    [DecidableEq AMarking]
    (h : (build (succTransfer net) maxClasses fuel a0).2 = true) (bad : AMarking → Bool) :
    (∀ a, a ∈ (build (succTransfer net) maxClasses fuel a0).1 ↔
      Relation.ReflTransGen (StepAT net) a0 a) ∧
    (proven bad (build (succTransfer net) maxClasses fuel a0).1 = true ↔
      ∀ a, Relation.ReflTransGen (StepAT net) a0 a → bad a = false) := by
  refine ⟨fun a => (run_complete_iff_reach h a).trans (reach_succTransfer_iff net a0 a), ?_⟩
  rw [(decided_exact bad h).1]
  exact forall_congr' fun a => by rw [reach_succTransfer_iff]

/-- **A closed graph's `Proven` holds for the executor, drained forwards included**: over the
transfer rows of a net whose consume-all arcs are unguarded, no marking a concrete run reaches is
bad under `alpha`, whichever way each firing ends. The counterpart of
`Enumeration.forward_enumeration_sound` without its `FixedForwards` premise — the reason the
graph routes may decide the nets the linear routes refuse. -/
theorem transfer_enumeration_sound {net : SpecNet} {maxClasses fuel : Nat} {m0 m : CMarking}
    [DecidableEq AMarking]
    (hG : ∀ to ∈ net, GuardFreeConsumeAll to.1)
    (h : (build (succTransfer net) maxClasses fuel (alpha m0)).2 = true)
    (bad : AMarking → Bool)
    (hp : proven bad (build (succTransfer net) maxClasses fuel (alpha m0)).1 = true)
    (hR : Relation.ReflTransGen (StepCD net) m0 m) : bad (alpha m) = false :=
  ((transfer_enumeration_exact h bad).2.mp hp) _ (transfer_reachability_simulated hG hR)

/-- Every class a (possibly truncated) build discovers is transfer-reachable, so a violation read
off a truncated graph's prefix is real in the transfer semantics ([VER-017]). -/
theorem transfer_build_reach {net : SpecNet} {maxClasses fuel : Nat} {a0 : AMarking}
    [DecidableEq AMarking] (a : AMarking)
    (ha : a ∈ (build (succTransfer net) maxClasses fuel a0).1) :
    Relation.ReflTransGen (StepAT net) a0 a :=
  (reach_succTransfer_iff net a0 a).mp (build_reach a ha)

/-! ## The retrodiction net, as a transfer -/

/-- `t : all(a) → xor(c, timeout(forward(a, b)))` from `a = 3`: the timeout row resolved at the
α-image deposits all three drained tokens in `b`, the count no constant row holds. -/
theorem all_forward_transfer_row :
    transferRows tAll oFwd (fun p => if p = pa then 3 else 0) =
      [[pc], [pb],
        [pb, pb, pb]] := by
  decide

end Libpetri.Novel.TransferRows
