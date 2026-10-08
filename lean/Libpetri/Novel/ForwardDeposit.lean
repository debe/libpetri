import Libpetri.Soundness

/-!
# Timeout outcomes and `ForwardInput` deposits ([IO-013], [IO-014], [IO-016])

A firing ends one of two ways, and they deposit differently:

* **The action completes** and writes a branch of the output spec ([IO-015]): the places
  of one alternative at every `Xor`. A `ForwardInput(src, dst)` leaf is then a claim on
  `dst` like any place. The analyses model one token per claimed place ([IO-016]); that is
  `UnitOutput` (`Basic.lean`) and this file keeps it.
* **The executor's `Timeout` fires** ([IO-013]). The marking receives the timeout child's
  tokens *and nothing else* (AC5), and a `ForwardInput(src, dst)` leaf deposits one token in
  `dst` **per token the firing consumed from `src`** ([IO-014] AC2, AC4). Rust:
  `timeout_outputs` / `collect_timeout_outputs` (`executor_core/output.rs:419-470`) walk
  the first `Timeout`'s child (`find_timeout`) and re-emit every snapshotted consumed token.

Before the fix the flattener (`net_flattener.rs`) and the state-class graph
(`state_class_graph.rs::expand_transition` / `compute_successor`) read the timeout child as if
the action had written it: one token per leaf, siblings included. That is `oldRows` below.
On `t : exactly(2, a) → xor(c, timeout(forward(a, b)))` from `a = 2` the executor ends at
`b = 2`, while every row deposits at most one token in `b`, and `placeBound(b, 1)` was proven
by the linear bound (VER-015), the fixpoint query and the enumeration (VER-017) alike.

The fix is `branch_outcomes.rs::outcomes`: the action branches first, in
`enumerate_branches` order, then each timeout deposit not already among them, with a forward
from a `One` / `Exactly(n)` input depositing `required_count = n`
(`branch_outcomes::forward_deposit` returns `Deposit::Tokens(n)` for that input). That is
`fixedRows`. A forward from an `All` / `AtLeast` input deposits the drained batch, which no
constant row can express (`forward_deposit` returns `Deposit::Drained` for it,
`drained_forward_has_no_row`); `branch_outcomes::drained_forward` refuses such a net on
every route that reads the flat net (checked in `verify_net` after the graph routes, before the
first linear one; the linear bound that runs ahead of the enumeration skips such a net). The graph routes resolve the batch at the marking each firing drains;
`TransferRows.lean` proves those marking-dependent rows exact (`transfer_step_simulated`,
`transfer_enumeration_sound`).

Results:
* `forward_exactly_two_breaks_unit_output` (retrodiction, by `decide`): on the net above the
  concrete timeout deposit `[b, b]` is no old row, and no old branch satisfies `UnitOutput`
  for it.
* `old_rows_prove_bound_one` / `timeout_firing_reaches_b_two`: the old flat net's reachable
  markings all satisfy `b ≤ 1` (so every route was right about the model it was given), while
  the concrete timed-out firing puts two tokens in `b`.
* `fixed_rows_example`: the fixed rows of that spec are `[c]`, `[b]`, `[b, b]` — the
  `t_b0` / `t_b1` / `t_b2` rows of `flatten_forward_deposits_every_consumed_token`.
* `deposit_mem_fixedRows` / `fixedRows_mem_deposit`: with every forward drawing from a
  `One` / `Exactly` input, the fixed rows are exactly the concrete deposits (up to order):
  every way a firing can end is a row, and every row is a way a firing can end.
* `prop1_step_deposit` / `forward_step_simulated`: Proposition 1's step lemma with the
  deposit as the post vector; a concrete firing that ends either way is matched by an
  abstract firing of one fixed row. `fireAD_eq_fireA` / `action_deposit_is_unit_output` tie it
  to `Basic.lean`: on a duplicate-free branch ([IO-011]) the deposit is `post` and the
  `UnitOutput` hypothesis holds.
* `rows_reachability_simulated`: Proposition 1 over reachability for any deposit rows, with no
  multiplicity premise: a concrete step that deposits a row's counts (`StepCR`) is an abstract
  step of that row (`StepAD`, `ReachAD`).
* `stepCD_stepCR`, `forward_reachability_simulated`: every concrete step ending in one of the
  declared outcomes is a `StepCR` of the fixed rows, so Proposition 1 holds for `fixedRows`.
  `Seam/Net.lean`, `Enumeration.lean`, `LinearBound.lean` and `Certificate.lean` build on these
  (`reachNC_reachAD`, `rows_enumeration_exact`, `linear_bound_sound_rows`, `vc_sound_rows`).

Out of scope: timing (a timeout is a nondeterministic outcome here, as in the analyses),
colours (only counts, as in `Basic.lean`), n-ary `And` / `Xor` (modelled as binary nodes; the
enumeration order of a right fold is the same), the executors' rejection of a `Xor` or nested
`Timeout` under a `Timeout` (read here as alternatives, as `branch_outcomes::timeout_deposits`
does), and the transition with no output spec (one empty outcome in Rust).
-/

namespace Libpetri.Novel.ForwardDeposit

open Libpetri

/-! ## Output specs and what a firing deposits -/

/-- An output spec. Models `libpetri-core/src/output.rs` `enum Out`, with binary `and` / `xor`. -/
inductive OutSpec where
  | place (p : PlaceId)
  | and (l r : OutSpec)
  | xor (l r : OutSpec)
  | timeout (c : OutSpec)
  | forward (src dst : PlaceId)
  deriving DecidableEq, Repr

/-- A deposit: the places receiving a token, with repetition. `d.count p` tokens land in `p`. -/
abbrev Deposit := List PlaceId

/-- The cross product of two alternative lists: an `And` deposits one alternative of each. -/
def cross (xs ys : List Deposit) : List Deposit :=
  xs.flatMap (fun x => ys.map (fun y => x ++ y))

/-- The branches an action may write ([IO-015]), one token per claimed place ([IO-016]).
Models `libpetri-core/src/output.rs::enumerate_branches`; a `forward` claims its `dst`. -/
def branches : OutSpec → List Deposit
  | .place p => [[p]]
  | .forward _ dst => [[dst]]
  | .and l r => cross (branches l) (branches r)
  | .xor l r => branches l ++ branches r
  | .timeout c => branches c

/-- What a `Timeout` child deposits when the timeout fires ([IO-013] AC5, [IO-014]): a minted
token per place, and per `forward src dst` one token in `dst` per token consumed from `src`.
Models `collect_timeout_outputs` (`executor_core/output.rs:431-470`). -/
def timeoutDeposits (consumed : PlaceId → Nat) : OutSpec → List Deposit
  | .place p => [[p]]
  | .forward src dst => [List.replicate (consumed src) dst]
  | .and l r => cross (timeoutDeposits consumed l) (timeoutDeposits consumed r)
  | .xor l r => timeoutDeposits consumed l ++ timeoutDeposits consumed r
  | .timeout c => timeoutDeposits consumed c

/-- The first `Timeout` node's child. Models `libpetri-core/src/output.rs::find_timeout`. -/
def findTimeout : OutSpec → Option OutSpec
  | .timeout c => some c
  | .and l r => (findTimeout l).or (findTimeout r)
  | .xor l r => (findTimeout l).or (findTimeout r)
  | _ => none

/-- How a firing ends: the action wrote its `i`-th branch, or the timeout fired and its child
deposited its `j`-th alternative. -/
inductive Choice where
  | action (i : Nat)
  | timedOut (j : Nat)
  deriving DecidableEq, Repr

/-- **The concrete deposit** of a firing that consumed `consumed p` tokens from each place and
ended with `choice` ([IO-013], [IO-014], [IO-015] under the [IO-016] convention). `none` for a
choice the spec does not offer. -/
def deposit (consumed : PlaceId → Nat) (o : OutSpec) : Choice → Option Deposit
  | .action i => (branches o)[i]?
  | .timedOut j => (findTimeout o).bind fun c => (timeoutDeposits consumed c)[j]?

/-! ## The flattener's rows, before and after -/

/-- The pre-fix rows: every analysis read the timeout child as a branch the action writes,
one token per leaf (`enumerate_branches` + `post[pid] += 1`, `net_flattener.rs` before the fix). -/
def oldRows (o : OutSpec) : List Deposit := branches o

/-- `ds` appended to `acc`, skipping a deposit whose post vector is already there. Models the
`if !result.contains(&outcome)` loop of `branch_outcomes.rs::outcomes`, which compares
deposits as name-sorted maps, i.e. up to order. -/
def dedupAppend : List Deposit → List Deposit → List Deposit
  | acc, [] => acc
  | acc, d :: ds => dedupAppend (if acc.any (fun e => e.isPerm d) then acc else acc ++ [d]) ds

/-- **The fixed rows** (`branch_outcomes.rs::outcomes`, read by `flatten`, `expand_transition`
and the ν fragment): the action branches, then the timeout deposits with a forward from `src`
depositing `required_count` of `t`'s input on `src` — `pre t src`, `0` when `src` is no input. -/
def fixedRows (t : Transition) (o : OutSpec) : List Deposit :=
  match findTimeout o with
  | none => branches o
  | some c => dedupAppend (branches o) (timeoutDeposits (pre t) c)

/-- The places a `forward` of `o` draws from. -/
def forwardSources : OutSpec → List PlaceId
  | .place _ => []
  | .forward src _ => [src]
  | .and l r => forwardSources l ++ forwardSources r
  | .xor l r => forwardSources l ++ forwardSources r
  | .timeout c => forwardSources c

/-- Every forward of `o` draws from a place `t` consumes a fixed count from (`One` /
`Exactly`), or from no input place at all. The complement is what
`branch_outcomes::drained_forward` refuses. -/
def FixedForwards (t : Transition) (o : OutSpec) : Prop :=
  ∀ src ∈ forwardSources o, consumeAllAt t src = false

/-! ## The retrodiction: `exactly(2, a) → xor(c, timeout(forward(a, b)))` -/

section Retrodiction

/-- Places `a = 0`, `b = 1`, `c = 2`. -/
def pa : PlaceId := 0
def pb : PlaceId := 1
def pc : PlaceId := 2

/-- `t : exactly(2, a)`, no other arc. -/
def tFwd : Transition :=
  { name := "t"
  , inputs := [{ place := pa, card := .exactly 2, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

/-- `xor(c, timeout(50, forward_input(a, b)))`. -/
def oFwd : OutSpec := .xor (.place pc) (.timeout (.forward pa pb))

/-- `M0 = {a: 2}`. -/
def m0Fwd : CMarking := fun p => if p == pa then [10, 20] else []

theorem fwd_enabled : enabledC m0Fwd tFwd = true := by decide

/-- The executor's deposit when the timeout fires: both consumed tokens land in `b`. -/
theorem fwd_timeout_deposit :
    deposit (consumedAt m0Fwd tFwd) oFwd (.timedOut 0) = some [pb, pb] := by decide

/-- **Retrodiction.** The concrete timeout deposit `[b, b]` is no old row (in any order), and no
old branch satisfies `UnitOutput` for it: the pre-fix abstraction could not simulate this
firing, and Proposition 1 did not apply. -/
theorem forward_exactly_two_breaks_unit_output :
    deposit (consumedAt m0Fwd tFwd) oFwd (.timedOut 0) = some [pb, pb]
    ∧ (∀ r ∈ oldRows oFwd, r.isPerm [pb, pb] = false)
    ∧ (∀ br ∈ oldRows oFwd, ¬ UnitOutput (fun p => [pb, pb].count p) br) := by
  refine ⟨fwd_timeout_deposit, by decide, ?_⟩
  intro br hbr hU
  have h := hU pb
  simp only [oldRows, oFwd, branches, List.mem_append, List.mem_singleton] at hbr
  rcases hbr with rfl | rfl <;> simp [post, pb, pc] at h

/-- The old flat net: `t` with each old row. -/
def oldNet : FlatNet := (oldRows oFwd).map fun br => (tFwd, br)

theorem oldNet_eq : oldNet = [(tFwd, [pc]), (tFwd, [pb])] := rfl

/-- Everything the old flat net reaches from `α(M0)` has `2·b + a ≤ 2`. -/
theorem old_rows_invariant {a : AMarking} (h : ReachA oldNet (alpha m0Fwd) a) :
    2 * a pb + a pa ≤ 2 := by
  induction h using ReachA.rec' with
  | init => decide
  | step hr hmem hen ih =>
    rename_i a ft
    simp only [oldNet_eq, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;>
    · have hpre : 2 ≤ a pa := by simpa [enabledA, tFwd, pa, Card.required] using hen
      simp only [fireA, tFwd, consumeAllAt, specAt, pre, post, Card.consumesAll,
        Card.required, pa, pb, pc] at ih hpre ⊢
      simp at ih hpre ⊢
      omega

/-- The old abstraction proves `placeBound(b, 1)`, correctly for the net it was given. -/
theorem old_rows_prove_bound_one {a : AMarking} (h : ReachA oldNet (alpha m0Fwd) a) :
    a pb ≤ 1 := by
  have := old_rows_invariant h
  omega

/-- The concrete timed-out firing ends at `b = 2` (and `a = 0`): the α-image of the executor's
successor, the firing consuming both tokens and depositing `[b, b]`. -/
theorem timeout_firing_reaches_b_two :
    alphaFireC m0Fwd tFwd (fun p => [pb, pb].count p) pb = 2
    ∧ alphaFireC m0Fwd tFwd (fun p => [pb, pb].count p) pa = 0 := by
  constructor <;> decide

/-- The fixed rows of the spec: the `t_b0` / `t_b1` / `t_b2` rows of
`net_flattener::tests::flatten_forward_deposits_every_consumed_token`. -/
theorem fixed_rows_example : fixedRows tFwd oFwd = [[pc], [pb], [pb, pb]] := by decide

end Retrodiction

/-! ## A drained forward has no constant row -/

/-- `t : all(a)`. -/
def tAll : Transition :=
  { name := "t"
  , inputs := [{ place := pa, card := .all, guard := none }]
  , inhibitors := [], reads := [], resets := [] }

/-- For every candidate row there is an enabled marking whose timed-out firing deposits a
different count in `b`: the forward of an `All` input deposits the drained batch ([IO-014]),
which no post vector can hold. This is why the linear routes refuse such a net
(`drained_forward`); the graph routes resolve the count per marking (`TransferRows.lean`). -/
theorem drained_forward_has_no_row (r : Deposit) :
    ∃ m : CMarking, enabledC m tAll = true ∧ ∃ d,
      deposit (consumedAt m tAll) oFwd (.timedOut 0) = some d ∧ r.count pb ≠ d.count pb := by
  refine ⟨fun p => if p == pa then List.replicate (r.count pb + 1) 0 else [], ?_,
    List.replicate (r.count pb + 1) pb, ?_, ?_⟩
  · simp [enabledC, tAll, matchCount, pa, Card.required]
  · simp [deposit, oFwd, findTimeout, timeoutDeposits, consumedAt, specAt, tAll, consumeCount,
      Card.consumesAll, matchCount, pa]
  · simp [pb]

/-! ## The fixed rows are exactly the concrete deposits -/

theorem mem_dedupAppend_of_mem : ∀ {acc ds : List Deposit} {r : Deposit},
    r ∈ acc → r ∈ dedupAppend acc ds
  | acc, [], r, h => h
  | acc, d :: ds, r, h => by
    unfold dedupAppend
    apply mem_dedupAppend_of_mem
    split
    · exact h
    · exact List.mem_append_left _ h

/-- Every deposit of `acc ++ ds` has a row of `dedupAppend acc ds` with the same post vector. -/
theorem dedupAppend_covers : ∀ {acc ds : List Deposit} {d : Deposit},
    d ∈ acc ++ ds → ∃ r ∈ dedupAppend acc ds, r.Perm d
  | acc, [], d, h => ⟨d, by simpa [dedupAppend] using h, List.Perm.refl d⟩
  | acc, e :: ds, d, h => by
    unfold dedupAppend
    by_cases hd : d = e
    · subst hd
      split
      · rename_i hany
        obtain ⟨f, hf, hperm⟩ := List.any_eq_true.mp hany
        exact ⟨f, mem_dedupAppend_of_mem hf, List.isPerm_iff.mp hperm⟩
      · exact ⟨d, mem_dedupAppend_of_mem (List.mem_append_right _ (List.mem_singleton_self d)),
          List.Perm.refl d⟩
    · have h' : d ∈ acc ++ ds := by
        simp only [List.mem_append, List.mem_cons] at h ⊢
        rcases h with h | h | h
        · exact Or.inl h
        · exact absurd h hd
        · exact Or.inr h
      apply dedupAppend_covers
      simp only [List.mem_append] at h' ⊢
      split
      · exact h'
      · rcases h' with h' | h'
        · exact Or.inl (List.mem_append_left _ h')
        · exact Or.inr h'

/-- Every row of `dedupAppend acc ds` comes from `acc ++ ds`. -/
theorem dedupAppend_subset : ∀ {acc ds : List Deposit} {r : Deposit},
    r ∈ dedupAppend acc ds → r ∈ acc ++ ds
  | acc, [], r, h => by simpa [dedupAppend] using h
  | acc, e :: ds, r, h => by
    unfold dedupAppend at h
    have := dedupAppend_subset h
    simp only [List.mem_append, List.mem_cons] at this ⊢
    split at this
    · rcases this with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · simp only [List.mem_append, List.mem_singleton] at this
      rcases this with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- The timeout deposits read the consumed counts at forward sources only. -/
theorem timeoutDeposits_congr {f g : PlaceId → Nat} :
    ∀ (c : OutSpec), (∀ src ∈ forwardSources c, f src = g src) →
      timeoutDeposits f c = timeoutDeposits g c
  | .place _, _ => rfl
  | .forward src _, h => by simp [timeoutDeposits, h src (by simp [forwardSources])]
  | .and l r, h => by
    simp only [timeoutDeposits]
    rw [timeoutDeposits_congr l (fun s hs => h s (by simp [forwardSources, hs])),
      timeoutDeposits_congr r (fun s hs => h s (by simp [forwardSources, hs]))]
  | .xor l r, h => by
    simp only [timeoutDeposits]
    rw [timeoutDeposits_congr l (fun s hs => h s (by simp [forwardSources, hs])),
      timeoutDeposits_congr r (fun s hs => h s (by simp [forwardSources, hs]))]
  | .timeout c, h => by
    simp only [timeoutDeposits]
    exact timeoutDeposits_congr c (fun s hs => h s (by simpa [forwardSources] using hs))

/-- The timeout child's forwards are forwards of the spec. -/
theorem forwardSources_findTimeout :
    ∀ {o c : OutSpec}, findTimeout o = some c → ∀ src ∈ forwardSources c, src ∈ forwardSources o
  | .place _, _, h => by simp [findTimeout] at h
  | .forward _ _, _, h => by simp [findTimeout] at h
  | .timeout c', c, h => by
    simp only [findTimeout, Option.some.injEq] at h
    subst h
    intro src hs
    simpa [forwardSources] using hs
  | .and l r, c, h => by
    intro src hs
    simp only [findTimeout] at h
    simp only [forwardSources, List.mem_append]
    cases hl : findTimeout l with
    | some c' =>
      rw [hl] at h
      simp only [Option.some_or, Option.some.injEq] at h
      subst h
      exact Or.inl (forwardSources_findTimeout hl src hs)
    | none =>
      rw [hl] at h
      simp only [Option.none_or] at h
      exact Or.inr (forwardSources_findTimeout h src hs)
  | .xor l r, c, h => by
    intro src hs
    simp only [findTimeout] at h
    simp only [forwardSources, List.mem_append]
    cases hl : findTimeout l with
    | some c' =>
      rw [hl] at h
      simp only [Option.some_or, Option.some.injEq] at h
      subst h
      exact Or.inl (forwardSources_findTimeout hl src hs)
    | none =>
      rw [hl] at h
      simp only [Option.none_or] at h
      exact Or.inr (forwardSources_findTimeout h src hs)

/-- A fixed-count input consumes its required count: `consumedAt = pre` off consume-all places. -/
theorem consumedAt_eq_pre {m : CMarking} {t : Transition} {p : PlaceId}
    (h : consumeAllAt t p = false) : consumedAt m t p = pre t p := by
  unfold consumedAt pre
  unfold consumeAllAt at h
  cases hs : specAt t p with
  | none => rfl
  | some s =>
    rw [hs] at h
    simp [consumeCount, h]

/-- Under `FixedForwards`, the timeout child deposits what the fixed rows say. -/
theorem timeoutDeposits_fixed {m : CMarking} {t : Transition} {o c : OutSpec}
    (hFwd : FixedForwards t o) (hc : findTimeout o = some c) :
    timeoutDeposits (consumedAt m t) c = timeoutDeposits (pre t) c :=
  timeoutDeposits_congr c fun src hs =>
    consumedAt_eq_pre (hFwd src (forwardSources_findTimeout hc src hs))

/-- **Every way a firing can end is a fixed row** (up to order), when every forward draws from
a `One` / `Exactly` input. -/
theorem deposit_mem_fixedRows {m : CMarking} {t : Transition} {o : OutSpec}
    (hFwd : FixedForwards t o) {ch : Choice} {d : Deposit}
    (h : deposit (consumedAt m t) o ch = some d) :
    ∃ r ∈ fixedRows t o, r.Perm d := by
  have hbr : ∀ {d}, d ∈ branches o → ∃ r ∈ fixedRows t o, r.Perm d := by
    intro d hd
    refine ⟨d, ?_, List.Perm.refl d⟩
    unfold fixedRows
    split
    · exact hd
    · exact mem_dedupAppend_of_mem hd
  cases ch with
  | action i => exact hbr (List.mem_of_getElem? h)
  | timedOut j =>
    simp only [deposit] at h
    cases hc : findTimeout o with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      simp only [Option.bind_some] at h
      have hd : d ∈ timeoutDeposits (pre t) c := by
        rw [← timeoutDeposits_fixed hFwd hc]
        exact List.mem_of_getElem? h
      unfold fixedRows
      rw [hc]
      exact dedupAppend_covers (List.mem_append_right _ hd)

/-- **Every fixed row is a way a firing can end**: the rows add no deposit the executor never
makes, when every forward draws from a `One` / `Exactly` input. -/
theorem fixedRows_mem_deposit {m : CMarking} {t : Transition} {o : OutSpec}
    (hFwd : FixedForwards t o) {r : Deposit} (hr : r ∈ fixedRows t o) :
    ∃ ch, deposit (consumedAt m t) o ch = some r := by
  unfold fixedRows at hr
  split at hr
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    exact ⟨.action i, hi⟩
  · rename_i c hc
    rcases List.mem_append.mp (dedupAppend_subset hr) with hb | ht
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
      exact ⟨.action i, hi⟩
    · rw [← timeoutDeposits_fixed (m := m) hFwd hc] at ht
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ht
      exact ⟨.timedOut j, by simp [deposit, hc, hj]⟩

/-! ## Proposition 1 with deposit rows -/

/-- The CHC fire relation with a deposit as the post vector (`firing_conditions`,
`smt_encoder.rs`, `post[i] = d.count i`). -/
def fireAD (a : AMarking) (t : Transition) (d : Deposit) : AMarking :=
  fun p =>
    if t.resets.contains p then d.count p
    else if consumeAllAt t p then d.count p
    else a p - pre t p + d.count p

/-- On a duplicate-free branch the deposit is `Basic.lean`'s `post`. -/
theorem post_eq_count {br : List PlaceId} (h : br.Nodup) (p : PlaceId) :
    post br p = br.count p := by
  unfold post
  by_cases hp : p ∈ br
  · have h1 := (List.nodup_iff_count.mp h) p
    have h2 := List.count_pos_iff.mpr hp
    simp only [hp, List.contains_iff_mem, if_true]
    omega
  · simp [hp, List.count_eq_zero_of_not_mem hp]

/-- `fireAD` is `fireA` on a duplicate-free branch ([IO-011] rejects a place twice in one). -/
theorem fireAD_eq_fireA {br : List PlaceId} (h : br.Nodup) (a : AMarking) (t : Transition) :
    fireAD a t br = fireA a t br := by
  funext p
  simp [fireAD, fireA, post_eq_count h]

/-- An action deposit — one token per claimed place — satisfies `UnitOutput`. -/
theorem action_deposit_is_unit_output {br : List PlaceId} (h : br.Nodup) :
    UnitOutput (fun p => br.count p) br :=
  fun p => (post_eq_count h p).symm

/-- **Proposition 1's step with a deposit as the post vector.** The concrete successor of a
firing that deposits `d` is the abstract firing with post `d`, whatever its multiplicities. -/
theorem prop1_step_deposit (m : CMarking) (t : Transition) (d : Deposit)
    (hGuard : GuardFreeConsumeAll t) (hEn : enabledC m t = true) :
    enabledA (alpha m) t = true ∧
      alphaFireC m t (fun p => d.count p) = fireAD (alpha m) t d := by
  constructor
  · unfold enabledC at hEn
    unfold enabledA
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hEn ⊢
    obtain ⟨⟨hIn, hInh⟩, hRd⟩ := hEn
    exact ⟨⟨fun s hs => Nat.le_trans (hIn s hs) (matchCount_le m s), hInh⟩, hRd⟩
  · funext p
    unfold alphaFireC fireAD
    by_cases hR : t.resets.contains p = true
    · simp only [hR, if_pos]
    · simp only [hR, if_neg, Bool.not_eq_true] at *
      by_cases hCA : consumeAllAt t p = true
      · simp only [hCA, if_pos]
        unfold consumedAt
        unfold consumeAllAt at hCA
        cases hs : specAt t p with
        | none => rw [hs] at hCA; simp at hCA
        | some s =>
          rw [hs] at hCA
          obtain ⟨hmem, hplace⟩ := specAt_sound hs
          have hg : s.guard = none := hGuard s hmem hCA
          have hall : consumeCount m s = (m p).length := by
            simp [consumeCount, hCA, matchCount, hg, hplace]
          show ((m p).length - consumeCount m s) + d.count p = d.count p
          rw [hall, Nat.sub_self, Nat.zero_add]
      · simp only [hCA, if_neg, Bool.not_eq_true]
        simp only [Bool.not_eq_true] at hCA
        rw [consumedAt_eq_pre hCA]
        rfl

/-- **A concrete firing is simulated by a fixed row**, whichever way it ends, when every forward
draws from a `One` / `Exactly` input: `UnitOutput`-style Proposition 1 for timeout outcomes. -/
theorem forward_step_simulated (m : CMarking) (t : Transition) (o : OutSpec)
    (hGuard : GuardFreeConsumeAll t) (hFwd : FixedForwards t o)
    (hEn : enabledC m t = true) {ch : Choice} {d : Deposit}
    (h : deposit (consumedAt m t) o ch = some d) :
    ∃ r ∈ fixedRows t o, enabledA (alpha m) t = true ∧
      alphaFireC m t (fun p => d.count p) = fireAD (alpha m) t r := by
  obtain ⟨r, hr, hperm⟩ := deposit_mem_fixedRows hFwd h
  obtain ⟨hEnA, hFire⟩ := prop1_step_deposit m t d hGuard hEn
  refine ⟨r, hr, hEnA, ?_⟩
  rw [hFire]
  funext p
  simp [fireAD, hperm.count_eq]

/-! ## Proposition 1 over reachability, deposit rows -/

/-- A net of transitions with their output specs. -/
abbrev SpecNet := List (Transition × OutSpec)

/-- One concrete step: an enabled transition fires and ends one of the ways its spec offers,
depositing that outcome's tokens. -/
def StepCD (net : SpecNet) (m m' : CMarking) : Prop :=
  ∃ to ∈ net, enabledC m to.1 = true ∧ ∃ ch d,
    deposit (consumedAt m to.1) to.2 ch = some d ∧
    alpha m' = alphaFireC m to.1 (fun p => d.count p)

/-- The flat net the fixed flattener builds: one row per fixed deposit. -/
def flatRows (net : SpecNet) : List (Transition × Deposit) :=
  net.flatMap fun to => (fixedRows to.1 to.2).map fun r => (to.1, r)

/-- One abstract step of the fixed flat net. -/
def StepAD (rows : List (Transition × Deposit)) (a a' : AMarking) : Prop :=
  ∃ tr ∈ rows, enabledA a tr.1 = true ∧ a' = fireAD a tr.1 tr.2

/-- Abstract reachability over deposit rows: the least fixpoint of the CHC rules with the
integer post vectors `flatten` writes (`post[pid] += n`). -/
def ReachAD (rows : List (Transition × Deposit)) (a0 : AMarking) : AMarking → Prop :=
  Relation.ReflTransGen (StepAD rows) a0

/-- One concrete step that deposits the counts of a row: an enabled row fires and the firing
leaves `tr.2.count p` tokens in each `p`. The row-level form of `StepCD`, and the shape the
named executor step of `Seam/Net.lean` pulls back to. -/
def StepCR (rows : List (Transition × Deposit)) (m m' : CMarking) : Prop :=
  ∃ tr ∈ rows, enabledC m tr.1 = true ∧ alpha m' = alphaFireC m tr.1 (fun p => tr.2.count p)

/-- A concrete step that deposits a row's counts is an abstract step of that row. -/
theorem stepCR_simulated {rows : List (Transition × Deposit)}
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) {m m' : CMarking} (h : StepCR rows m m') :
    StepAD rows (alpha m) (alpha m') := by
  obtain ⟨tr, hmem, hEn, hEff⟩ := h
  obtain ⟨hEnA, hFire⟩ := prop1_step_deposit m tr.1 tr.2 (hG tr hmem) hEn
  exact ⟨tr, hmem, hEnA, by rw [hEff, hFire]⟩

/-- **Proposition 1 over deposit rows.** `α(R) ⊆ R(N̂)` for any rows, with no multiplicity
premise: every consume-all arc unguarded is the only side condition. -/
theorem rows_reachability_simulated {rows : List (Transition × Deposit)}
    (hG : ∀ tr ∈ rows, GuardFreeConsumeAll tr.1) {m0 m : CMarking}
    (h : Relation.ReflTransGen (StepCR rows) m0 m) : ReachAD rows (alpha m0) (alpha m) :=
  Relation.ReflTransGen.lift alpha (fun _ _ hs => stepCR_simulated hG hs) m0 m h

/-- **Every way a firing ends deposits the counts of a fixed row**: a concrete `StepCD` is a
`StepCR` of `flatRows`, when every forward draws from a `One` / `Exactly` input. -/
theorem stepCD_stepCR {net : SpecNet} (hFwd : ∀ to ∈ net, FixedForwards to.1 to.2)
    {m m' : CMarking} (h : StepCD net m m') : StepCR (flatRows net) m m' := by
  obtain ⟨to, hmem, hEn, ch, d, hdep, hEff⟩ := h
  obtain ⟨r, hr, hperm⟩ := deposit_mem_fixedRows (hFwd to hmem) hdep
  have hc : (fun p => d.count p) = fun p => r.count p := funext fun p => (hperm.count_eq p).symm
  exact ⟨(to.1, r), List.mem_flatMap.mpr ⟨to, hmem, List.mem_map.mpr ⟨r, hr, rfl⟩⟩, hEn,
    by rw [hEff, hc]⟩

/-- The rows of `flatRows` carry their spec's transition. -/
theorem flatRows_guardFree {net : SpecNet} (hG : ∀ to ∈ net, GuardFreeConsumeAll to.1) :
    ∀ tr ∈ flatRows net, GuardFreeConsumeAll tr.1 := by
  intro tr htr
  obtain ⟨to, hmem, htr'⟩ := List.mem_flatMap.mp htr
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp htr'
  exact hG to hmem

/-- **Proposition 1 for timeout outcomes.** `α(R(N)) ⊆ R(N̂)` for the fixed rows, with every
forward drawing from a `One` / `Exactly` input and every consume-all arc unguarded: the
composition of `stepCD_stepCR` and `rows_reachability_simulated`. -/
theorem forward_reachability_simulated {net : SpecNet} {m0 m : CMarking}
    (hWF : ∀ to ∈ net, GuardFreeConsumeAll to.1 ∧ FixedForwards to.1 to.2)
    (h : Relation.ReflTransGen (StepCD net) m0 m) :
    Relation.ReflTransGen (StepAD (flatRows net)) (alpha m0) (alpha m) :=
  rows_reachability_simulated (flatRows_guardFree fun to h => (hWF to h).1)
    (Relation.ReflTransGen.lift id
      (fun _ _ hs => stepCD_stepCR (fun to h => (hWF to h).2) hs) m0 m h)

/-- One step over deposit rows with injection: `Retrodict.lean`'s `StepAInjRel` with integer
posts (`encode_injection_rule` / `injection_conditions`, `AlwaysAvailable`). -/
def StepADInj (rows : List (Transition × Deposit)) (envs : List PlaceId) (a a' : AMarking) :
    Prop :=
  StepAD rows a a' ∨ ∃ p ∈ envs, a' = fun q => if q == p then a q + 1 else a q

def ReachADInj (rows : List (Transition × Deposit)) (envs : List PlaceId) (a0 : AMarking) :
    AMarking → Prop :=
  Relation.ReflTransGen (StepADInj rows envs) a0

/-- The env-free relation is the `envs = []` case of the injected one. -/
theorem reachAD_sub_inj {rows : List (Transition × Deposit)} {envs : List PlaceId}
    {a0 a : AMarking} (h : ReachAD rows a0 a) : ReachADInj rows envs a0 a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.tail ih (Or.inl hs)

end Libpetri.Novel.ForwardDeposit
