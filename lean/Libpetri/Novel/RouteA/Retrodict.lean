import Libpetri.Novel.RouteA.Plan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Route A retrodictions: four past wrong `Proven`s

Each witness is a concrete net, a concrete ν run (every step a `NuStep`, or the executor's
actual deposit where it is not one), and a proof that **every** state the name-coloured
encoding reaches has the property the run violates — the wrong `Proven`, derived rather than
asserted. Decisions on concrete data are by `decide` / `rfl`; the claims about the encoding's
whole reachable set are inductions over `ReachE`.

Past (fixed):

* **`667e67d` — the budget-count `k`.** `build_plan` once set `k` to the initial budget count
  and checked budget *direction* only. A join that refunds two budget tokens (one to each of
  two minting budgets) lets the real net hold two live names from a budget of one; the
  one-slot encoding cannot, and proves `a ≤ 1` (`budget_k_false_proven`). The shipped bound
  (`colour_slot_bound`) refuses the net: no non-negative weighting covers the coloured places
  and does not increase along the rows (`inflating_net_has_no_cover`, `inflating_net_refused`).
* **`f52c482` — Route A under injection.** The encoding has no injection rule, so an
  environment place stays at its seed and a transition fed by it never fires: `bad ≤ 0` is
  proven of a net that reaches `bad = 1` once a token is injected
  (`injection_breaks_closed_encoding`). The fix is the guard in `coloured_attempt` that
  declines under any modelled injection (`routeAAdmits`); `ReachNu` is the closed relation.

Fixed on 2026-09-29, after the model found them. Both are derived here from the Lean model of
`build_plan` before the fix (`Plan.lean`, `buildPlanBudget`) and of the encoder's old rules
(`Model.lean`). The shipped `build_plan` refuses the first net (`forward_mint_refused`), and the
shipped encoder nets the second's self-loop (`Shipped.lean`, `selfLoop_premises_shipped`).

* **A coloured output with no coloured input, written by the action, is classified a mint.**
  `t : budget, reqA → xor(okA, timeout(forward(reqA, a)))` and its twin into `b`, with a join on
  `a, b`. The rows depositing into `a` and `b` produce a coloured place, consume no coloured
  place and consume budget, so `build_plan` classifies them `Mint`
  (`forward_rows_classified_mint`). The executor's timeout forwards the consumed request token
  itself ([IO-014]); two requests with one correlation id reach the join under one name, and
  it fires. Two mints take two distinct colours, so the encoding never fires the join and
  proves `done ≤ 0` (`forward_mint_false_proven`). The second forward's deposit is not a
  fresh-name effect (`forward_deposit_not_fresh`): P1 fails. The timeout is only one way in.
  `enumerate_branches` reads the timeout child as the branch `{a}`, so `rFA` is also the row of
  an action that writes `a`, and the same wrong `Proven` follows from any action on that row
  whose payload carries a live name (a `fork()`, a copied request). Classification by
  incidence alone cannot close P1, so the fix reads the source transition: a `Mint` row must
  belong to a declared mint ([NU-010]) whose timeout writes no coloured place. `tA` is
  declared (it consumes the budget), but its timeout writes `a`, so the net is refused.
* **Self-loop coloured consumer.** `spin : a, tick → a, tock` (EXTENDED) is `Class::Consume`
  with `a` among its outputs. `encode_rule` keeps the last write per column, so the rule's `a`
  colour column is `m + 1`, not `m`; the conjoined law `budget + a + done = 1` then makes the
  rule unsatisfiable, `spin` never fires in the encoding, and `tock ≤ 0` is proven of a net that
  reaches `tock = 1` (`self_loop_consume_false_proven`). Every other premise of
  `coloured_simulates` holds of this net (`selfLoop_premises_but_noSelfLoop`). The choice of
  conjoined law does not matter: any valid law with a non-zero weight on `a` blocks `spin`
  (`selfLoop_encoding_tock_empty_of`), and every basis whose span contains `yL`, the default
  semiflow basis included, has such a member (`selfLoop_false_proven_any_basis`). The fix took
  the second of the two options: the `Consume` arm now treats its input like a join key that is
  also a relay target (guard, no update).
-/

namespace Libpetri.Novel.RouteA.Retro

open Libpetri
open Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.LinearBound
open Libpetri.Novel.RouteA

/-! ## Building blocks -/

/-- An unguarded `One` input arc. -/
def inp1 (p : PlaceId) : InSpec := ⟨p, .one, none⟩

/-- A transition consuming one token from each listed place, with no test or reset arc. -/
def mkT (name : String) (ins : List PlaceId) : Transition :=
  { name := name, inputs := ins.map inp1, inhibitors := [], reads := [], resets := [] }

theorem specAt_mkT (name : String) (ins : List PlaceId) (p : PlaceId) :
    specAt (mkT name ins) p = if p ∈ ins then some (inp1 p) else none := by
  unfold specAt mkT
  simp only
  induction ins with
  | nil => simp
  | cons q qs ih =>
    rw [List.map_cons, List.find?_cons]
    by_cases h : q = p
    · subst h
      simp [inp1]
    · have hb : ((inp1 q).place == p) = false := by simp [inp1, h]
      rw [hb]
      simp only
      rw [ih]
      have h' : ¬ p = q := fun e => h e.symm
      simp [List.mem_cons, h']

theorem pre_mkT (name : String) (ins : List PlaceId) (p : PlaceId) :
    pre (mkT name ins) p = if p ∈ ins then 1 else 0 := by
  unfold pre
  rw [specAt_mkT]
  by_cases h : p ∈ ins <;> simp [h, inp1, Card.required]

theorem consumeAllAt_mkT (name : String) (ins : List PlaceId) (p : PlaceId) :
    consumeAllAt (mkT name ins) p = false := by
  unfold consumeAllAt
  rw [specAt_mkT]
  by_cases h : p ∈ ins <;> simp [h, inp1, Card.consumesAll]

theorem alphaFireC_mkT (m : CMarking) (name : String) (ins : List PlaceId) (f : PlaceId → Nat)
    (p : PlaceId) :
    alphaFireC m (mkT name ins) f p = (m p).length - (if p ∈ ins then 1 else 0) + f p := by
  unfold alphaFireC consumedAt
  rw [specAt_mkT]
  by_cases h : p ∈ ins <;>
    simp [h, inp1, mkT, consumeCount, Card.consumesAll, Card.required]

theorem fireAD_mkT (a : AMarking) (name : String) (ins : List PlaceId) (d : Deposit)
    (p : PlaceId) :
    fireAD a (mkT name ins) d p = a p - (if p ∈ ins then 1 else 0) + d.count p := by
  unfold fireAD
  rw [consumeAllAt_mkT, pre_mkT]
  simp [mkT]

theorem guardFree_mkT (name : String) (ins : List PlaceId) :
    GuardFreeConsumeAll (mkT name ins) := by
  intro s hs _
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hs
  rfl

/-- H1 holds of any weighting on an `mkT` row: it has no reset and no consume-all arc. -/
theorem zeroOnNonlinear_mkT (y : Weight) (name : String) (ins : List PlaceId) (n : Nat) :
    ZeroOnNonlinear y (mkT name ins) n := by
  intro p _ h
  rw [consumeAllAt_mkT] at h
  simp [mkT] at h

/-- `NoTestArcs` for any `mkT`. -/
theorem noTestArcs_mkT (C : List PlaceId) (name : String) (ins : List PlaceId) :
    NoTestArcs C (mkT name ins) := fun p _ =>
  ⟨rfl, consumeAllAt_mkT name ins p, List.not_mem_nil, List.not_mem_nil⟩

/-- The count condition of a ν step of an `mkT` row, place by place. -/
theorem counts_mkT {m m' : CMarking} {name : String} {ins : List PlaceId} {d : Deposit}
    (h : ∀ p, (m' p).length = (m p).length - (if p ∈ ins then 1 else 0) + d.count p) :
    alpha m' = alphaFireC m (mkT name ins) (fun p => d.count p) := by
  funext p
  rw [alphaFireC_mkT]
  exact h p

/-- The flat abstraction of an `mkT` row at a place outside its arcs is the identity. -/
theorem uFire_off {C : List PlaceId} {e : EState} {name : String} {ins : List PlaceId}
    {d : Deposit} {p : PlaceId} (hin : p ∉ ins) (hd : d.count p = 0) :
    uFire C e (mkT name ins) d p = e.u p := by
  unfold uFire
  split
  · rfl
  · rw [fireAD_mkT, if_neg hin, hd]
    omega

/-- A concrete marking from a list of place contents (places past the list are empty). -/
def mk (l : List (List Name)) : CMarking := fun p => (l[p]?).getD []

theorem mk_out {l : List (List Name)} {p : PlaceId} (h : l.length ≤ p) : mk l p = [] := by
  unfold mk
  rw [List.getElem?_eq_none h]
  rfl

/-- The count condition of a ν step between concrete markings, reduced to a bounded check that
`decide` evaluates. -/
theorem counts_mk {l l' : List (List Name)} {name : String} {ins : List PlaceId} {d : Deposit}
    (N : Nat) (hl : l.length ≤ N) (hl' : l'.length ≤ N) (hins : ∀ p ∈ ins, p < N)
    (hd : ∀ p ∈ d, p < N)
    (hchk : ∀ p, p < N →
      (mk l' p).length = (mk l p).length - (if p ∈ ins then 1 else 0) + d.count p) :
    alpha (mk l') = alphaFireC (mk l) (mkT name ins) (fun p => d.count p) := by
  refine counts_mkT fun p => ?_
  by_cases hp : p < N
  · exact hchk p hp
  · have hpi : p ∉ ins := fun h => hp (hins p h)
    have hpd : d.count p = 0 := List.count_eq_zero.mpr fun h => hp (hd p h)
    have hpN : N ≤ p := Nat.le_of_not_lt hp
    rw [mk_out (le_trans hl' hpN), mk_out (le_trans hl hpN), if_neg hpi, hpd]
    rfl

/-- `uFire_off` for a row built with `mkT`. -/
theorem uFire_off_row {C : List PlaceId} {e : EState} {r : CRow} {name : String}
    {ins : List PlaceId} (ht : r.t = mkT name ins) {p : PlaceId} (hin : p ∉ ins)
    (hd : r.d.count p = 0) : uFire C e r.t r.d p = e.u p := by
  rw [ht]
  exact uFire_off hin hd

/-! ## `667e67d`: the budget-count `k` -/

section Budget

/-- Places: `0 = B1`, `1 = B2` (two minting budgets), `2 = a`, `3 = b` (the join's keys). -/
def CB : List PlaceId := [2, 3]

def rMA : CRow := ⟨mkT "mintA" [0], [2, 3], .mint [2, 3]⟩
def rMB : CRow := ⟨mkT "mintB" [1], [2, 3], .mint [2, 3]⟩
/-- The join refunds one token to each budget: two for a one-token mint. -/
def rJB : CRow := ⟨mkT "join" [2, 3], [0, 1], .join [2, 3] []⟩

def rowsB : List CRow := [rMA, rMB, rJB]

/-- The executor's initial marking: one token in `B1`. -/
def m0B : CMarking := mk [[0]]

/-- The encoding the pre-`667e67d` `build_plan` produced: `k` = the initial budget count = 1
(any conjoined invariants). -/
def encB (invs : List Weight) : Enc := ⟨CB, 1, 4, rowsB, invs, alpha m0B⟩

/-- Every state of the one-slot encoding holds at most one `a` token. -/
theorem budget_encoding_bounds_a (invs : List Weight) :
    ∀ e, ReachE (encB invs) e → agg CB 1 e 2 ≤ 1 := by
  intro e h
  have hagg : ∀ e : EState, agg CB 1 e 2 = e.s 2 0 := fun e => by simp [agg, CB]
  rw [hagg]
  induction h with
  | refl => simp [e0]
  | tail _ hs ih =>
    obtain ⟨r, hr, hE⟩ := hs
    have hcs := hE.s
    simp only [encB, rowsB, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨c, hc, hfree, hs'⟩ := hcs
      have hc0 : c = 0 := by simp [encB] at hc; omega
      subst hc0
      rw [hs']
      have := hfree 2 (by simp [encB, CB])
      simp [sMint, this]
    · obtain ⟨c, hc, hfree, hs'⟩ := hcs
      have hc0 : c = 0 := by simp [encB] at hc; omega
      subst hc0
      rw [hs']
      have := hfree 2 (by simp [encB, CB])
      simp [sMint, this]
    · obtain ⟨c, _, _, hs'⟩ := hcs
      rw [hs']
      unfold sJoin
      split
      · split
        · omega
        · split <;> simp_all
      · exact ih

/-- The ν run: mint `1`, join it (refunding both budgets), mint `2` from `B1`, mint `3` from
`B2` — two live names. -/
def m1B : CMarking := mk [[], [], [1], [1]]
def m2B : CMarking := mk [[0], [0]]
def m3B : CMarking := mk [[], [0], [2], [2]]
def m4B : CMarking := mk [[], [], [2, 3], [2, 3]]

theorem budget_run : ReachNu CB rowsB m0B m4B := by
  have s1 : NuStep CB rMA m0B m1B :=
    ⟨by decide, counts_mk 4 (by decide) (by decide) (by decide) (by decide) (by decide),
      ⟨1, by decide, by decide⟩⟩
  have s2 : NuStep CB rJB m1B m2B :=
    ⟨by decide, counts_mk 4 (by decide) (by decide) (by decide) (by decide) (by decide),
      ⟨1, by decide, by decide⟩⟩
  have s3 : NuStep CB rMA m2B m3B :=
    ⟨by decide, counts_mk 4 (by decide) (by decide) (by decide) (by decide) (by decide),
      ⟨2, by decide, by decide⟩⟩
  have s4 : NuStep CB rMB m3B m4B :=
    ⟨by decide, counts_mk 4 (by decide) (by decide) (by decide) (by decide) (by decide),
      ⟨3, by decide, by decide⟩⟩
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.tail (Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨rMA, by simp [rowsB], s1⟩)
    ⟨rJB, by simp [rowsB], s2⟩) ⟨rMA, by simp [rowsB], s3⟩) ⟨rMB, by simp [rowsB], s4⟩

/-- **Retrodiction of `667e67d`.** The real net reaches two `a` tokens (two live names); the
one-slot encoding the budget count gave proves `a ≤ 1`. -/
theorem budget_k_false_proven :
    ReachNu CB rowsB m0B m4B ∧ alpha m4B 2 = 2 ∧
      ∀ invs e, ReachE (encB invs) e → agg CB 1 e 2 ≤ 1 :=
  ⟨budget_run, rfl, budget_encoding_bounds_a⟩

/-- **The fix.** No non-negative weighting covers `a` and `b` without increasing along some
row, so `colour_slot_bound` finds no bound. -/
theorem inflating_net_has_no_cover :
    ¬ ∃ y : Weight, (∀ p, p < 4 → 0 ≤ y p) ∧ (∀ p ∈ CB, 1 ≤ y p) ∧
      ∀ r ∈ rowsB, dotIncD y r.flat 4 ≤ 0 := by
  rintro ⟨y, hpos, hcov, hdec⟩
  have hA := hdec rMA (by simp [rowsB])
  have hB := hdec rMB (by simp [rowsB])
  have hJ := hdec rJB (by simp [rowsB])
  simp [dotIncD, isum, Finset.sum_range_succ, CRow.flat, rMA, rMB, rJB, pre_mkT] at hA hB hJ
  have h0 := hpos 0 (by decide)
  have h1 := hpos 1 (by decide)
  have h2 := hcov 2 (by simp [CB])
  have h3 := hcov 3 (by simp [CB])
  omega

/-- Hence the shipped `colour_slot_bound` returns `None` on it, whatever validated laws it is
given — the plan is refused and the flat over-approximation answers. -/
theorem inflating_net_refused {laws : List Law}
    (hv : ∀ l ∈ laws, LawValid (rowsB.map CRow.flat) 4 (alpha m0B) l) :
    colourSlotBound 4 CB laws = none := by
  cases h : colourSlotBound 4 CB laws with
  | none => rfl
  | some k =>
    exfalso
    obtain ⟨y, hpos, hcov, hcol, _⟩ := colourSlotBound_sound (by decide) hv h
    exact inflating_net_has_no_cover
      ⟨y, hpos, hcov, fun r hr => le_of_eq (hcol r.flat (List.mem_map.mpr ⟨r, hr, rfl⟩))⟩

end Budget

/-! ## `f52c482`: Route A under environment injection -/

section Injection

/-- Places: `0 = env` (an environment place), `1 = bad`, `2 = a` (a coloured key). -/
def CI : List PlaceId := [2]
def rI : CRow := ⟨mkT "take" [0], [1], .untouched⟩
def rowsI : List CRow := [rI]

/-- The encoding over the closed net, any slot count and invariants. -/
def encI (k : Nat) (invs : List Weight) : Enc := ⟨CI, k, 3, rowsI, invs, alpha (mk [])⟩

/-- The executor's relation with injection ([VER-006] `AlwaysAvailable`): a firing, or a token
of any payload arriving at an environment place. -/
def StepNuInj (C : List PlaceId) (rows : List CRow) (envs : List PlaceId) (m m' : CMarking) :
    Prop :=
  (∃ r ∈ rows, NuStep C r m m') ∨
    ∃ p ∈ envs, ∃ v, m' = fun q => if q = p then m q ++ [v] else m q

/-- The guard `coloured_attempt` gained in `f52c482`: Route A runs only without modelled
injection (`!env_injection.is_empty()` declines). -/
def routeAAdmits (envs : List PlaceId) : Bool := envs.isEmpty

theorem injection_run :
    Relation.ReflTransGen (StepNuInj CI rowsI [0]) (mk []) (mk [[], [0]]) := by
  have hinj : (fun q => if q = 0 then mk [] q ++ [5] else mk [] q) = mk [[5]] := by
    funext q
    rcases q with _ | q
    · rfl
    · simp [mk]
  have s2 : NuStep CI rI (mk [[5]]) (mk [[], [0]]) :=
    ⟨by decide, counts_mk 3 (by decide) (by decide) (by decide) (by decide) (by decide),
      fun p hp => by
        simp only [CI, List.mem_singleton] at hp
        subst hp
        rfl⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      (Or.inr ⟨0, by simp, 5, hinj.symm⟩))
    (Or.inl ⟨rI, by simp [rowsI], s2⟩)

/-- The closed encoding never leaves its seed: the only row needs an environment token. -/
theorem encI_frozen (k : Nat) (invs : List Weight) :
    ∀ e, ReachE (encI k invs) e → e = e0 (encI k invs) := by
  intro e h
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    obtain ⟨r, hr, hE⟩ := hs
    simp only [encI, rowsI, List.mem_singleton] at hr
    subst hr
    have hg := hE.guard.1 0 (by simp [encI, CI])
    change pre (mkT "take" [0]) 0 ≤ (e0 (encI k invs)).u 0 at hg
    rw [pre_mkT] at hg
    simp [e0, encI, CI, mk, alpha] at hg

/-- **Retrodiction of `f52c482`.** With injection the net reaches `bad = 1`; the name-coloured
encoding, which has no injection rule, proves `bad ≤ 0`. The guard declines exactly then. -/
theorem injection_breaks_closed_encoding (k : Nat) (invs : List Weight) :
    (∃ m, Relation.ReflTransGen (StepNuInj CI rowsI [0]) (mk []) m ∧ alpha m 1 = 1) ∧
      (∀ e, ReachE (encI k invs) e → agg CI k e 1 = 0) ∧
      routeAAdmits [0] = false ∧ routeAAdmits [] = true := by
  refine ⟨⟨_, injection_run, rfl⟩, fun e he => ?_, rfl, rfl⟩
  rw [encI_frozen k invs e he]
  simp [agg, e0, encI, CI, mk, alpha]

end Injection

/-! ## Fixed: a timeout forward into a match key was classified a mint -/

section Forward

/-- Places: `0 = budget`, `1 = reqA`, `2 = reqB`, `3 = a`, `4 = b` (the join's keys),
`5 = done`. -/
def CF : List PlaceId := [3, 4]

/-- The row of `tA : budget, reqA → xor(okA, timeout(forward(reqA, a)))` that deposits into
`a`: the timeout outcome, and equally the action branch `{a}` (`enumerate_branches` reads the
timeout child as a branch, and `branch_outcomes` lists the timeout separately only when it
deposits differently). The `okA` row is omitted: it touches no coloured place. -/
def rFA : CRow := ⟨mkT "tA" [0, 1], [3], .mint [3]⟩
def rFB : CRow := ⟨mkT "tB" [0, 2], [4], .mint [4]⟩
def rFJ : CRow := ⟨mkT "join" [3, 4], [5], .join [3, 4] []⟩
def rowsF : List CRow := [rFA, rFB, rFJ]

/-- The source rows. `tA` and `tB` consume the budget, so `declared_mints` declares them, and
their timeouts forward `reqA` into `a` and `reqB` into `b` (`timeout_writes`). -/
def srcF : List SrcRow :=
  [⟨rFA.t, rFA.d, none, true, [(3, some 1)]⟩, ⟨rFB.t, rFB.d, none, true, [(4, some 2)]⟩,
    ⟨rFJ.t, rFJ.d, some ⟨[3, 4], []⟩, false, []⟩]

/-- Two budget tokens; both requests carry correlation id `7`. -/
def m0F : CMarking := mk [[0, 0], [7], [7]]

/-- The validated semiflows: `reqA + a + done = 1`, `reqB + b + done = 1`,
`budget + a + b + 2·done = 2`. -/
def yFA : Weight := fun p => if p = 1 ∨ p = 3 ∨ p = 5 then 1 else 0
def yFB : Weight := fun p => if p = 2 ∨ p = 4 ∨ p = 5 then 1 else 0
def yFAll : Weight := fun p => if p = 0 ∨ p = 3 ∨ p = 4 then 1 else if p = 5 then 2 else 0
def lawsF : List Law := [⟨yFA, 1⟩, ⟨yFB, 1⟩, ⟨yFAll, 2⟩]

/-- **`build_plan` before the NU-010 fix accepted the net**, classifying both timeout rows as
mints, with `k = 2`: the plan the verifier then reported (`ν-encoding: name-coloured (exact
within budget k=2)`; "exact" and "budget" were the report's words, `k` is the colour-slot bound,
and what holds is inclusion under P1–P6, which this net breaks). -/
theorem forward_rows_classified_mint :
    buildPlanBudget 6 CF false [0] (alpha m0F) lawsF srcF = some (2, rowsF) := by
  rfl

/-- **The shipped `build_plan` refuses the net**: `tA` is a declared mint, but its timeout writes
the coloured place `a`, and a timeout write is never fresh. The net falls back to the
name-blind path, which does not claim the false bound. -/
theorem forward_mint_refused : buildPlan 6 CF false (alpha m0F) lawsF srcF = none := by
  rfl

/-- Every state of that encoding keeps `done` empty: two mints never share a colour, so the
join never fires. -/
theorem forward_encoding_done_empty (invs : List Weight) :
    ∀ e, ReachE ⟨CF, 2, 6, rowsF, invs, alpha m0F⟩ e → agg CF 2 e 5 = 0 := by
  intro e h
  have hagg : agg CF 2 e 5 = e.u 5 := by simp [agg, CF]
  rw [hagg]
  suffices H : (∀ c, e.s 3 c = 0 ∨ e.s 4 c = 0) ∧ e.u 5 = 0 from H.2
  clear hagg
  induction h with
  | refl => exact ⟨fun _ => Or.inl rfl, rfl⟩
  | @tail e1 e2 _ hs ih =>
    obtain ⟨hdis, hu5⟩ := ih
    obtain ⟨r, hr, hE⟩ := hs
    simp only [rowsF, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨c, _, hfree, hs'⟩ := hE.s
      refine ⟨fun c' => ?_, ?_⟩
      · rw [hs']
        unfold sMint
        by_cases hc : c' = c
        · subst hc
          right
          simp [hfree 4 (by simp [CF])]
        · simp only [hc, false_and, if_false]
          exact hdis c'
      · rw [hE.u]
        exact (uFire_off_row (r := rFA) rfl (by decide) (by decide)).trans hu5
    · obtain ⟨c, _, hfree, hs'⟩ := hE.s
      refine ⟨fun c' => ?_, ?_⟩
      · rw [hs']
        unfold sMint
        by_cases hc : c' = c
        · subst hc
          left
          simp [hfree 3 (by simp [CF])]
        · simp only [hc, false_and, if_false]
          exact hdis c'
      · rw [hE.u]
        exact (uFire_off_row (r := rFB) rfl (by decide) (by decide)).trans hu5
    · exfalso
      obtain ⟨c, _, hkeys, _⟩ := hE.s
      have h3 := hkeys 3 (by simp)
      have h4 := hkeys 4 (by simp)
      rcases hdis c with h | h <;> omega

/-- The executor's run: `tA` times out and forwards `reqA`'s token (id 7) into `a`; `tB` times
out and forwards `reqB`'s token (id 7) into `b`; the join matches id 7. -/
def m1F : CMarking := mk [[0], [], [7], [7]]
def m2F : CMarking := mk [[], [], [], [7], [7]]
def m3F : CMarking := mk [[], [], [], [], [], [9]]

/-- The second forward's deposit is **not** a fresh-name mint: its name is live in `a`. -/
theorem forward_deposit_not_fresh : ¬ NameEffect CF (.mint [4]) m1F m2F := by
  rintro ⟨v, hfresh, hm⟩
  have h4 : ([7] : List Name) = [] ++ [v] := hm 4 (by simp [CF])
  simp only [List.nil_append, List.cons.injEq, and_true] at h4
  subst h4
  exact hfresh 3 (by simp [CF]) (by decide)

/-- **Wrong `Proven` before the NU-010 fix (forward into a key).** The executor reaches `done = 1` — each step a
flat step of the plan's rows, each forward depositing the consumed request token, the join a ν
join on id 7 — while every state of the encoding `build_plan` accepted has `done = 0`. -/
theorem forward_mint_false_proven :
    (StepCR (rowsF.map CRow.flat) m0F m1F ∧ m1F 3 = m0F 1) ∧
      (StepCR (rowsF.map CRow.flat) m1F m2F ∧ m2F 4 = m1F 2) ∧
      NuStep CF rFJ m2F m3F ∧ alpha m3F 5 = 1 ∧
      ¬ NameEffect CF (.mint [4]) m1F m2F ∧
      buildPlanBudget 6 CF false [0] (alpha m0F) lawsF srcF = some (2, rowsF) ∧
      ∀ invs e, ReachE ⟨CF, 2, 6, rowsF, invs, alpha m0F⟩ e → agg CF 2 e 5 = 0 := by
  refine ⟨⟨⟨rFA.flat, by simp [rowsF], by decide,
      counts_mk 6 (by decide) (by decide) (by decide) (by decide) (by decide)⟩, rfl⟩,
    ⟨⟨rFB.flat, by simp [rowsF], by decide,
      counts_mk 6 (by decide) (by decide) (by decide) (by decide) (by decide)⟩, rfl⟩,
    ⟨by decide, counts_mk 6 (by decide) (by decide) (by decide) (by decide) (by decide),
      ⟨7, by decide, by decide⟩⟩,
    rfl, forward_deposit_not_fresh, forward_rows_classified_mint,
    forward_encoding_done_empty⟩

/-- **Every plan premise of `coloured_simulates` holds of this net** (through
`buildPlan_premises`, from the plan `build_plan` returns): what fails is P1, the ν semantics of
a mint row — the executor's forward is not a fresh-name effect. -/
theorem forward_premises_hold : Premises ⟨CF, 2, 6, rowsF, [], alpha m0F⟩ m0F := by
  refine buildPlanBudget_premises forward_rows_classified_mint (by decide) (by decide) ?_ ?_
    (by simp) ?_
  · intro l hl
    simp only [lawsF, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;>
    refine ⟨fun tr htr => ?_, ?_⟩ <;>
    first
    | (simp only [srcF, SrcRow.flat, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at htr
       rcases htr with rfl | rfl | rfl <;>
       simp [dotIncD, isum, Finset.sum_range_succ, rFA, rFB, rFJ, pre_mkT, yFA, yFB, yFAll])
    | simp [dot_eq_isum, isum, Finset.sum_range_succ, alpha, m0F, mk, yFA, yFB, yFAll]
  · intro s hs
    simp only [srcF, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> exact guardFree_mkT _ _
  · intro r hr
    simp only [rowsF, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> trivial

end Forward

/-! ## Fixed: a self-loop coloured consumer -/

section SelfLoop

/-- The seed represents itself: with the coloured places empty in `a0`, the aggregates of `e0`
are `a0`. -/
theorem agg_e0 {E : Enc} (h : ∀ p ∈ E.C, E.a0 p = 0) : agg E.C E.k (e0 E) = E.a0 := by
  funext p
  unfold agg e0
  by_cases hp : p ∈ E.C
  · simp [hp, h p hp]
  · simp [hp]

/-- Places: `0 = budget`, `1 = tick`, `2 = tock`, `3 = a`, `4 = b` (the join's keys),
`5 = done`. -/
def CS : List PlaceId := [3, 4]

def rSM : CRow := ⟨mkT "mint" [0], [3, 4], .mint [3, 4]⟩
/-- `spin : a, tick → a, tock`, EXTENDED coloured consumer relaying into its own input. -/
def rSS : CRow := ⟨mkT "spin" [3, 1], [3, 2], .consume 3 [3]⟩
def rSJ : CRow := ⟨mkT "join" [3, 4], [5], .join [3, 4] []⟩
def rowsS : List CRow := [rSM, rSS, rSJ]

/-- The source rows. `mint` consumes the budget, so it is declared; nothing has a timeout. -/
def srcS : List SrcRow :=
  [⟨rSM.t, rSM.d, none, true, []⟩, ⟨rSS.t, rSS.d, none, false, []⟩,
    ⟨rSJ.t, rSJ.d, some ⟨[3, 4], []⟩, false, []⟩]

def m0S : CMarking := mk [[0], [0]]

/-- `budget + a + done = 1` (the report's `I1`) and `budget + b + done = 1`. -/
def yL : Weight := fun p => if p = 0 ∨ p = 3 ∨ p = 5 then 1 else 0
def yLb : Weight := fun p => if p = 0 ∨ p = 4 ∨ p = 5 then 1 else 0
def lawsS : List Law := [⟨yL, 1⟩, ⟨yLb, 1⟩]

/-- The encoding: `k = 2` (the sum branch of `colour_slot_bound`: neither law covers both
keys), the law `yL` conjoined. -/
def encS : Enc := ⟨CS, 2, 6, rowsS, [yL], alpha m0S⟩

/-- **`build_plan` accepted the net in EXTENDED mode** before the NU-010 fix, `spin` classified
`Consume 3 [3]`, `k = 2`, as the report then said (`exact within budget k=2`). -/
theorem selfLoop_plan :
    buildPlanBudget 6 CS true [0] (alpha m0S) lawsS srcS = some (2, rowsS) := by
  rfl

/-- The shipped `build_plan` returns the same plan (the report now says `colour-slot bound
k=2`): the fix of this net is in the encoder, which nets the self-loop to zero
(`RouteA/Shipped.lean`, `selfLoop_premises_shipped`). -/
theorem selfLoop_plan_shipped : buildPlan 6 CS true (alpha m0S) lawsS srcS = some (2, rowsS) := by
  rfl

theorem dot_yL (a : AMarking) : dot yL a 6 = (a 0 : Int) + a 3 + a 5 := by
  rw [dot_eq_isum]
  simp [isum, Finset.sum_range_succ, yL]

/-- The shipped `Consume` rule on the self-loop adds one token to `a`'s colour column. -/
theorem sConsume_selfLoop_sum {c : Nat} (hc : c < 2) (s : PlaceId → Nat → Nat) :
    ∑ c' ∈ Finset.range 2, sConsume 3 [3] c s 3 c' = (∑ c' ∈ Finset.range 2, s 3 c') + 1 := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, sConsume,
    List.mem_singleton, if_true]
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> simp <;> omega

/-- Every state of the encoding keeps `tock` empty: the `spin` rule contradicts the conjoined
law `budget + a + done = 1`. -/
theorem selfLoop_encoding_tock_empty : ∀ e, ReachE encS e → agg CS 2 e 2 = 0 := by
  intro e h
  have hagg : agg CS 2 e 2 = e.u 2 := by simp [agg, CS]
  rw [hagg]
  suffices H : dot yL (agg CS 2 e) 6 = dot yL (alpha m0S) 6 ∧ e.u 2 = 0 from H.2
  clear hagg
  induction h with
  | refl =>
    refine ⟨?_, rfl⟩
    rw [show CS = encS.C from rfl, show (2 : Nat) = encS.k from rfl,
      agg_e0 (E := encS) (by decide)]
    rfl
  | @tail e1 e2 _ hs ih =>
    obtain ⟨hdot, hu2⟩ := ih
    obtain ⟨r, hr, hE⟩ := hs
    have hinv : dot yL (agg CS 2 e2) 6 = dot yL (alpha m0S) 6 := hE.inv yL (by simp [encS])
    simp only [encS, rowsS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨hinv, by
        rw [hE.u]
        exact (uFire_off_row (r := rSM) rfl (by decide) (by decide)).trans hu2⟩
    · exfalso
      obtain ⟨c, hc, _, hs'⟩ := hE.s
      have h0 : agg CS 2 e2 0 = agg CS 2 e1 0 := by
        simp only [agg, CS]
        simp only [List.mem_cons, List.not_mem_nil, or_false, show ¬ (0 = 3 ∨ 0 = 4) by decide,
          if_false]
        rw [hE.u]
        exact uFire_off_row (r := rSS) rfl (by decide) (by decide)
      have h5 : agg CS 2 e2 5 = agg CS 2 e1 5 := by
        simp only [agg, CS]
        simp only [List.mem_cons, List.not_mem_nil, or_false, show ¬ (5 = 3 ∨ 5 = 4) by decide,
          if_false]
        rw [hE.u]
        exact uFire_off_row (r := rSS) rfl (by decide) (by decide)
      have h3 : agg CS 2 e2 3 = agg CS 2 e1 3 + 1 := by
        simp only [agg, CS, List.mem_cons, List.not_mem_nil, or_false, true_or, if_true]
        rw [hs']
        exact sConsume_selfLoop_sum (by simpa [encS] using hc) e1.s
      rw [dot_yL] at hinv hdot
      rw [h0, h5, h3] at hinv
      push_cast at hinv
      omega
    · exact ⟨hinv, by
        rw [hE.u]
        exact (uFire_off_row (r := rSJ) rfl (by decide) (by decide)).trans hu2⟩

/-- The ν run: mint name `1` into `a` and `b`, then `spin` consumes `a`'s token `1` and relays
it back into `a`, depositing into `tock`. -/
def m1S : CMarking := mk [[], [0], [], [1], [1]]
def m2S : CMarking := mk [[], [], [0], [1], [1]]

theorem selfLoop_run : ReachNu CS rowsS m0S m2S := by
  have s1 : NuStep CS rSM m0S m1S :=
    ⟨by decide, counts_mk 6 (by decide) (by decide) (by decide) (by decide) (by decide),
      ⟨1, by decide, by decide⟩⟩
  have s2 : NuStep CS rSS m1S m2S :=
    ⟨by decide, counts_mk 6 (by decide) (by decide) (by decide) (by decide) (by decide),
      ⟨1, by decide, by decide⟩⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨rSM, by simp [rowsS], s1⟩)
    ⟨rSS, by simp [rowsS], s2⟩

/-- The conjoined law passed the exact gate (H1 and a zero column on every row). -/
theorem yL_valid : ∀ r ∈ rowsS, ZeroOnNonlinear yL r.t 6 ∧ dotIncD yL r.flat 6 = 0 := by
  intro r hr
  simp only [rowsS, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
  refine ⟨zeroOnNonlinear_mkT _ _ _ _, ?_⟩ <;>
  simp [dotIncD, isum, Finset.sum_range_succ, CRow.flat, rSM, rSS, rSJ, pre_mkT, yL]

/-- **Any** conjoined law with a non-zero weight on `a` makes the `spin` rule unsatisfiable,
not just `yL`: the rule adds one token to `a`'s aggregate and leaves the rest of the law's sum
as the (zero) column moves it. -/
theorem selfLoop_encoding_tock_empty_of (invs : List Weight) {y : Weight} (hy : y ∈ invs)
    (hcol : dotIncD y rSS.flat 6 = 0) (ha : y 3 ≠ 0) :
    ∀ e, ReachE ⟨CS, 2, 6, rowsS, invs, alpha m0S⟩ e → agg CS 2 e 2 = 0 := by
  intro e h
  have hagg : agg CS 2 e 2 = e.u 2 := by simp [agg, CS]
  rw [hagg]
  suffices H : dot y (agg CS 2 e) 6 = dot y (alpha m0S) 6 ∧ e.u 2 = 0 from H.2
  clear hagg
  have hcol' : y 2 - y 1 = 0 := by
    have := hcol
    simp [dotIncD, isum, Finset.sum_range_succ, CRow.flat, rSS, pre_mkT] at this
    linarith
  induction h with
  | refl =>
    refine ⟨?_, rfl⟩
    rw [show CS = (⟨CS, 2, 6, rowsS, invs, alpha m0S⟩ : Enc).C from rfl,
      show (2 : Nat) = (⟨CS, 2, 6, rowsS, invs, alpha m0S⟩ : Enc).k from rfl,
      agg_e0 (E := ⟨CS, 2, 6, rowsS, invs, alpha m0S⟩) (fun p hp => by
        simp only [CS, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> rfl)]
  | @tail e1 e2 _ hs ih =>
    obtain ⟨hdot, hu2⟩ := ih
    obtain ⟨r, hr, hE⟩ := hs
    have hinv : dot y (agg CS 2 e2) 6 = dot y (alpha m0S) 6 := hE.inv y hy
    simp only [rowsS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨hinv, by
        rw [hE.u]
        exact (uFire_off_row (r := rSM) rfl (by decide) (by decide)).trans hu2⟩
    · exfalso
      obtain ⟨c, hc, _, hs'⟩ := hE.s
      have hg1 : 1 ≤ e1.u 1 := by
        have := hE.guard.1 1 (by simp [CS])
        rw [show rSS.t = mkT "spin" [3, 1] from rfl, pre_mkT] at this
        simpa using this
      have hu : ∀ p, p ∉ CS → e2.u p = e1.u p - (if p ∈ [3, 1] then 1 else 0) +
          ([3, 2] : Deposit).count p := fun p hp => by
        rw [hE.u]
        unfold uFire
        rw [if_neg hp]
        exact fireAD_mkT e1.u "spin" [3, 1] [3, 2] p
      have hoff : ∀ p, p ∉ CS → agg CS 2 e2 p = e2.u p ∧ agg CS 2 e1 p = e1.u p :=
        fun p hp => by simp [agg, hp]
      have h0 : agg CS 2 e2 0 = agg CS 2 e1 0 := by
        rw [(hoff 0 (by decide)).1, (hoff 0 (by decide)).2, hu 0 (by decide)]; simp
      have h5 : agg CS 2 e2 5 = agg CS 2 e1 5 := by
        rw [(hoff 5 (by decide)).1, (hoff 5 (by decide)).2, hu 5 (by decide)]; simp
      have h1 : agg CS 2 e2 1 + 1 = agg CS 2 e1 1 := by
        rw [(hoff 1 (by decide)).1, (hoff 1 (by decide)).2, hu 1 (by decide)]; simp; omega
      have h2 : agg CS 2 e2 2 = agg CS 2 e1 2 + 1 := by
        rw [(hoff 2 (by decide)).1, (hoff 2 (by decide)).2, hu 2 (by decide)]; simp
      have h3 : agg CS 2 e2 3 = agg CS 2 e1 3 + 1 := by
        simp only [agg, CS, List.mem_cons, List.not_mem_nil, or_false, true_or, if_true]
        rw [hs']
        exact sConsume_selfLoop_sum hc e1.s
      have h4 : agg CS 2 e2 4 = agg CS 2 e1 4 := by
        simp only [agg, CS, List.mem_cons, List.not_mem_nil, or_false, or_true, if_true]
        rw [hs']
        simp [sConsume]
      rw [dot_eq_isum] at hinv hdot
      simp only [isum, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hinv hdot
      rw [h0, h2, h3, h4, h5] at hinv
      have h1' : ((agg CS 2 e1 1 : Nat) : Int) = (agg CS 2 e2 1 : Int) + 1 := by
        rw [← h1]; push_cast; ring
      rw [h1'] at hdot
      push_cast at hinv hdot
      apply ha
      linear_combination hinv - hdot - hcol'
    · exact ⟨hinv, by
        rw [hE.u]
        exact (uFire_off_row (r := rSJ) rfl (by decide) (by decide)).trans hu2⟩

/-- A family of weightings whose rational span contains `yL` (some non-zero multiple `N · yL` is
an integer combination) weights `a` somewhere: some member has a non-zero weight on place `3`. -/
theorem span_of_yL_weights_a {B : List (Int × Weight)} {N : Int} (hN : N ≠ 0)
    (hspan : ∀ p, N * yL p = (B.map fun cb => cb.1 * cb.2 p).sum) : ∃ cb ∈ B, cb.2 3 ≠ 0 := by
  by_contra hno
  push Not at hno
  have h3 := hspan 3
  rw [List.sum_eq_zero (fun x hx => by
    obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hx
    rw [hno cb hcb, mul_zero])] at h3
  simp [yL] at h3
  exact hN h3

/-- **The default configuration is affected too.** Whatever basis of laws the verifier
conjoins (by default the semiflow basis `coloured_attempt` validates), if every member passed
the exact gate and `yL` lies in its rational span, some member weights `a` and the `spin` rule
is unsatisfiable: `tock ≤ 0` is proven. The retrodiction does not depend on the choice
`invs = [yL]`. -/
theorem selfLoop_false_proven_any_basis (invs : List Weight) {B : List (Int × Weight)}
    {N : Int} (hN : N ≠ 0) (hspan : ∀ p, N * yL p = (B.map fun cb => cb.1 * cb.2 p).sum)
    (hconj : ∀ cb ∈ B, cb.2 ∈ invs) (hvalid : ∀ cb ∈ B, dotIncD cb.2 rSS.flat 6 = 0) :
    ∀ e, ReachE ⟨CS, 2, 6, rowsS, invs, alpha m0S⟩ e → agg CS 2 e 2 = 0 := by
  obtain ⟨cb, hcb, ha⟩ := span_of_yL_weights_a hN hspan
  exact selfLoop_encoding_tock_empty_of invs (hconj cb hcb) (hvalid cb hcb) ha

/-- **Wrong `Proven` before the self-loop fix (self-loop consumer).** The plan `build_plan` returned, the ν run to
`tock = 1`, the conjoined law is valid — and every state of the encoding has `tock = 0`. The one
premise of `coloured_simulates` that fails is `ConsumeNoSelfLoop`, which nothing checks. -/
theorem self_loop_consume_false_proven :
    buildPlanBudget 6 CS true [0] (alpha m0S) lawsS srcS = some (2, rowsS) ∧
      ReachNu CS rowsS m0S m2S ∧ alpha m2S 2 = 1 ∧
      (∀ r ∈ rowsS, ZeroOnNonlinear yL r.t 6 ∧ dotIncD yL r.flat 6 = 0) ∧
      ¬ ConsumeNoSelfLoop rSS.cls ∧
      ∀ e, ReachE encS e → agg CS 2 e 2 = 0 :=
  ⟨selfLoop_plan, selfLoop_run, rfl, yL_valid, fun h => h (by simp),
    selfLoop_encoding_tock_empty⟩

/-- **Every premise of `coloured_simulates` but `ConsumeNoSelfLoop` holds of this net.** -/
theorem selfLoop_premisesS : PremisesS encS m0S := by
  refine buildPlanG_premisesS selfLoop_plan (by decide) (by decide) ?_ ?_ ?_
  · intro l hl
    simp only [lawsS, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;>
    refine ⟨fun tr htr => ?_, ?_⟩ <;>
    first
    | (simp only [srcS, SrcRow.flat, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at htr
       rcases htr with rfl | rfl | rfl <;>
       simp [dotIncD, isum, Finset.sum_range_succ, rSM, rSS, rSJ, pre_mkT, yL, yLb])
    | simp [dot_eq_isum, isum, Finset.sum_range_succ, alpha, m0S, mk, yL, yLb]
  · intro s hs
    simp only [srcS, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> exact guardFree_mkT _ _
  · intro y hy s hs
    simp only [List.mem_singleton] at hy
    subst hy
    simp only [srcS, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;>
    refine ⟨zeroOnNonlinear_mkT _ _ _ _, ?_⟩ <;>
    simp [dotIncD, isum, Finset.sum_range_succ, SrcRow.flat, rSM, rSS, rSJ, pre_mkT, yL]

/-- Given `ConsumeNoSelfLoop`, `buildPlanBudget_premises` would discharge the rest, and it is
false. -/
theorem selfLoop_premises_but_noSelfLoop
    (hnsl : ∀ r ∈ rowsS, ConsumeNoSelfLoop r.cls) : Premises encS m0S :=
  selfLoop_premisesS.withNoSelfLoop hnsl

/-- Hence no `Premises` for it at all: the self-loop is the whole gap. -/
theorem selfLoop_noSelfLoop_fails : ¬ ∀ r ∈ rowsS, ConsumeNoSelfLoop r.cls :=
  fun h => h rSS (by simp [rowsS]) (by simp)

end SelfLoop

end Libpetri.Novel.RouteA.Retro
