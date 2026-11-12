import Libpetri.Spec.Verifier.Pipeline
import Libpetri.Spec.Verifier.Scg

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# Bridges from the named reference to the flat verifier models (J5, J7, J8)

The verifier blocks read reachability of the **named** verified net (`Reference.Reach`, the
yardstick of [VER-003]) and the executor's timed step (`RefTStep`, the TIME blocks' witness).
The models that prove things about the routes are **flat**: rows of place indices
(`ForwardDeposit.ReachAD`, the CHC and enumeration phases) and the timed semantics `TStep` of
`Novel/TimedScg` (the state-class graph). This file ties the two sides together, with no
premise that a real net fails.

* **Rows by name** (`rowsN`, `expandNet`, finding F2 of the verifier design). A transition's
  outcome rows by place name: its action branches, then its timeout deposits with each forward
  depositing the count its source input requires; one empty row for a transition with no output
  spec (`Reference.deposit none (.action 0) = some []`). Under `FixedFwd` (every forward draws
  from a `One` / `Exactly` input or from no input, as `branch_outcomes::drained_forward`
  requires) every reference firing deposits one of these rows exactly (`fires_mem_rowsN`).
  The expanded net is a `Seam.NNet`, so the flattener of `Seam/Net.lean` (`flatNet` over a
  `PlaceIndex`, any place-name type) applies. `reach_restrict` is `Link.reach_iff_reachAD`'s
  soundness half without its two premises: no `HasOutputs`, and named places through any index
  that holds the names the net uses (`NamesIn`).
* **J5, phases** (`FlatPhaseSound`, `FlatPhaseSound.phaseSound`, `FlatProgSound.progSound`). A
  phase whose `Proven` comes with a flat certificate (no marking of the flat rows reachable from
  the restricted seed is bad, read back by name through `Seam.lift`) keeps VER-003's phase
  contract on the named net (`PhaseSound`, `ProgSound`), when the index covers the initial
  marking (`Seam.Covers`, which VER-001's inert-place rewrite provides). A flat phase block
  proves its flat certificate; this bridge carries it to [VER-003]. `flatCert_of_inj` takes a
  certificate over the rows with injection (`ReachADInj`), the form of the linear-bound and
  state-equation theorems. `demoUnfedPhase` is a small phase decided this way, proved sound end
  to end (`demoUnfedPhase_sound`, `ex_demo_bound`).
* **The timed image** (`flatTNet`): the named timed net as a `TimedScg.TNet`, one entry per
  transition in net order, its arcs through the index, its rows `rowsN` and its interval the
  graph's reading of its timing (`TimedScg.mkT`, milliseconds to seconds).
* **J7, on-time runs** (`OnTimeStep`, `onTime_sim`, `onTime_tReach`, `onTime_graph`). Strong
  urgency is a filter on the executor's runs (ruling D3): no reap, no delay that carries an
  armed transition past its latest bound. Every on-time run of the timed reference `RefTStep`
  is a `TStep` run of the flat image with the same marking (restricted) and, for every enabled
  transition, the clock equal to its elapsed time in seconds. The proof matches
  `refPolicy.keep` with `TimedScg.persists` clock by clock (`keep_eq_persists`), so this
  **discharges premise 9 of `Succ.lean`** ("the executor's clock rule is `persists`") for the
  timed reference, atomic and reap-free: [TIME-012]'s rule as `RefTStep` states it is the rule
  the graph uses. That the runtimes follow `RefTStep` is what the TIME blocks and their tests
  carry, not this file. On a closed graph every on-time run's marking is the marking of a
  stored class (`onTime_graph`), so `SPURIOUS_UNDER_TIMING` holds of `RefTStep`
  (`onTime_safety_closed`).
* **J8, late runs** (`ref_late_sim`, `ref_late_graph`, `ref_rest_reapable`). Every run of
  `RefTStep` (late delays and reaps included) is covered by a `TStep` run of the flat image with
  its upper bounds dropped (`TimedScg.relax`), clocks at least the executor's elapsed times,
  which is `Late.late_sim` at the named level. Where the executor rests with tokens (every enabled
  transition reaped, `RefRests`), the covering class holds only clocks of reapable transitions:
  the reap-aware quiescence of [VER-002] read on the relaxed graph. `LateRelax` lifts
  `Timing.relaxLate` to named timed nets, and its flat image is `relaxMax` of the flat image
  (`flatTNet_lateRelax`), the net `reaping::relax_late` hands Route B's graph.

## What is assumed, and what is not covered

* `FixedFwd`: a forward from an `All` / `AtLeast` input deposits the drained batch, which no
  constant row expresses (premise 3 of `Succ.lean`). The routes refuse such nets
  (`drained_forward`), so the bridges do not lose a decided net.
* `NamesDistinct`: transition names are unique (premise 1 of `Succ.lean`; [TIME-010], ruling
  D10), so a stamp kept by name is the clock of one transition.
* The rows here repeat a row that `branch_outcomes::outcomes` lists once (it skips a deposit
  equal to an earlier one up to order). A repeated row adds no step to `TStep` or `ReachAD`, so
  the run-level bridges are unaffected; a statement about graph edge labels reads the
  deduplicated list of the graph layer instead.
* J7 covers the atomic step (one firing per step, `Reference/Timed.lean`). A firing pass of
  several firings, action duration (`Retrodict.action_duration_escapes`) and the executor
  state of the cycle machine are outside it, as they are outside `RefTStep`.
* J8 lands in the graph of `relax` (every latest bound `⊤`). The Rust graph is `relaxMax`
  (every latest bound `MAX_DURATION_MS`); `Late.capped_run_in_rust_graph` covers the runs whose
  covering clocks stay below 100 years. Carrying the cap to `RefTStep` runs is not done here.
-/

namespace Libpetri.Spec.Verifier.Bridges

open Libpetri Libpetri.Reference Libpetri.Novel.Seam Libpetri.Novel.ForwardDeposit
open Libpetri.Novel.TimedScg (TNet TTrans TState TStep TReach s0 mkT eftT lftT trOf rowsOf eftOf
  lftOf en en_eq en_lt persists survives inter fireAD_eq_inter_add Cls InCls ClsWF initCls Edge
  TimingWF Timing)
open Libpetri.Novel.Dbm (Bound)

variable {N : Type}

/-! ## 1. Rows by name (finding F2) -/

/-- The places a `forward` of an output spec draws from. -/
def fwdSrcs : Out N → List N
  | .place _ => []
  | .forward src _ => [src]
  | .and l r => fwdSrcs l ++ fwdSrcs r
  | .xor l r => fwdSrcs l ++ fwdSrcs r
  | .timeout c => fwdSrcs c

/-- A timeout child's deposits read the consumed counts only at its forward sources. -/
theorem timeoutDeposits_congr {f g : N → Nat} :
    ∀ o : Out N, (∀ s ∈ fwdSrcs o, f s = g s) → o.timeoutDeposits f = o.timeoutDeposits g
  | .place _, _ => rfl
  | .forward src _, h => by
    simp only [Out.timeoutDeposits, h src (by simp [fwdSrcs])]
  | .and l r, h => by
    simp only [Out.timeoutDeposits]
    rw [timeoutDeposits_congr l fun s hs => h s (by simp [fwdSrcs, hs]),
      timeoutDeposits_congr r fun s hs => h s (by simp [fwdSrcs, hs])]
  | .xor l r, h => by
    simp only [Out.timeoutDeposits]
    rw [timeoutDeposits_congr l fun s hs => h s (by simp [fwdSrcs, hs]),
      timeoutDeposits_congr r fun s hs => h s (by simp [fwdSrcs, hs])]
  | .timeout c, h => by
    simp only [Out.timeoutDeposits]
    exact timeoutDeposits_congr c fun s hs => h s (by simpa [fwdSrcs] using hs)

/-- The `Timeout` child's forward sources are forward sources of the spec. -/
theorem fwdSrcs_findTimeout : ∀ {o c : Out N}, o.findTimeout = some c →
    ∀ x ∈ fwdSrcs c, x ∈ fwdSrcs o
  | .place _, _, h, _, _ => by simp [Out.findTimeout] at h
  | .forward _ _, _, h, _, _ => by simp [Out.findTimeout] at h
  | .timeout c', c, h, x, hx => by
    simp only [Out.findTimeout, Option.some.injEq] at h
    subst h; simpa [fwdSrcs] using hx
  | .and l r, c, h, x, hx => by
    simp only [Out.findTimeout] at h
    simp only [fwdSrcs, List.mem_append]
    cases hl : l.findTimeout with
    | some c' =>
      rw [hl, Option.some_or, Option.some.injEq] at h
      subst h; exact Or.inl (fwdSrcs_findTimeout hl x hx)
    | none =>
      rw [hl, Option.none_or] at h
      exact Or.inr (fwdSrcs_findTimeout h x hx)
  | .xor l r, c, h, x, hx => by
    simp only [Out.findTimeout] at h
    simp only [fwdSrcs, List.mem_append]
    cases hl : l.findTimeout with
    | some c' =>
      rw [hl, Option.some_or, Option.some.injEq] at h
      subst h; exact Or.inl (fwdSrcs_findTimeout hl x hx)
    | none =>
      rw [hl, Option.none_or] at h
      exact Or.inr (fwdSrcs_findTimeout h x hx)

section Rows

variable [DecidableEq N]

/-- The count a transition's input arc on `n` requires (`required_count`), `0` without one: what
a forward from `n` deposits in the rows (`fixedRows`' `pre t src`). -/
def nreq (t : NTransition N) (n : N) : Nat :=
  match nspecAt t n with
  | none => 0
  | some s => s.card.required

/-- **Fixed forwards**: every forward of the output spec draws from a `One` / `Exactly` input or
from no input (`ForwardDeposit.FixedForwards`, by name). -/
def FixedFwd (t : Trans N) : Prop :=
  ∀ o, t.out = some o → ∀ src ∈ fwdSrcs o, ∀ s, nspecAt t.core src = some s →
    s.card.consumesAll = false

/-- Every transition of the net has fixed forwards. -/
def FixedFwdNet (net : Reference.Net N) : Prop := ∀ t ∈ net.transitions, FixedFwd t

/-- **The outcome rows of a transition, by name** (`branch_outcomes::outcomes` without its
duplicate skip): one empty row with no output spec; otherwise the action branches, then the
timeout child's deposits with each forward depositing the count its source requires. -/
def rowsN (t : Trans N) : List (List N) :=
  match t.out with
  | none => [[]]
  | some o => o.branches ++
      match o.findTimeout with
      | none => []
      | some c => c.timeoutDeposits (nreq t.core)

/-- Under fixed forwards, a firing consumes from each forward source what the input requires. -/
theorem nconsumed_eq_nreq {t : Trans N} (hF : FixedFwd t) {o : Out N} (ho : t.out = some o)
    (m : N → Nat) {src : N} (hs : src ∈ fwdSrcs o) : nconsumed m t.core src = nreq t.core src := by
  unfold nconsumed nreq
  cases h : nspecAt t.core src with
  | none => rfl
  | some s => simp [hF o ho src hs s h]

/-- **Every firing deposits one of the rows**, and moves the counts as `fireNA` of that row. -/
theorem fires_mem_rowsN {t : Trans N} (hF : FixedFwd t) {m m' : N → Nat} {d : List N}
    (h : Fires t m d m') : d ∈ rowsN t ∧ m' = fireNA m t.core d ∧ enabledNA m t.core = true := by
  obtain ⟨hen, ⟨ch, hd⟩, rfl⟩ := h
  refine ⟨?_, rfl, hen⟩
  unfold rowsN
  cases ho : t.out with
  | none =>
    rw [ho] at hd
    cases ch with
    | action i =>
      cases i with
      | zero => simp only [Reference.deposit, Option.some.injEq] at hd; subst hd; simp
      | succ i => simp [Reference.deposit] at hd
    | timedOut j => simp [Reference.deposit] at hd
  | some o =>
    rw [ho] at hd
    cases ch with
    | action i =>
      simp only [Reference.deposit] at hd
      exact List.mem_append_left _ (List.mem_of_getElem? hd)
    | timedOut j =>
      simp only [Reference.deposit, Option.bind_eq_some_iff] at hd
      obtain ⟨c, hc, hj⟩ := hd
      refine List.mem_append_right _ ?_
      simp only [hc]
      rw [timeoutDeposits_congr (g := nreq t.core) c
        fun s hs => nconsumed_eq_nreq hF ho m (fwdSrcs_findTimeout hc s hs)] at hj
      exact List.mem_of_getElem? hj

/-- **The branch-expanded net**: one named row per outcome of each transition (`Seam.NNet`). -/
def expandNet (net : Reference.Net N) : NNet N :=
  { places := net.places,
    transitions := net.transitions.flatMap fun t => (rowsN t).map fun r => (t.core, r) }

theorem mem_expandNet {net : Reference.Net N} {ft : NFlatTransition N} :
    ft ∈ (expandNet net).transitions ↔ ∃ t ∈ net.transitions, ∃ r ∈ rowsN t, ft = (t.core, r) := by
  simp only [expandNet, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨t, ht, r, hr, rfl⟩; exact ⟨t, ht, r, hr, rfl⟩
  · rintro ⟨t, ht, r, hr, rfl⟩; exact ⟨t, ht, r, hr, rfl⟩

/-- **A reference step is a step of the expanded net**, under fixed forwards. -/
theorem step_expand {net : Reference.Net N} (hF : FixedFwdNet net) {m m' : N → Nat} (h : Reference.Step net m m') :
    StepNARel (expandNet net) m m' := by
  obtain ⟨_, t, ht, -, d, hf⟩ := h
  obtain ⟨hd, rfl, hen⟩ := fires_mem_rowsN (hF t ht) hf
  exact ⟨(t.core, d), mem_expandNet.mpr ⟨t, ht, d, hd, rfl⟩, hen, rfl⟩

/-- **Reference reachability is reachability of the expanded net.** -/
theorem reach_reachNA {net : Reference.Net N} (hF : FixedFwdNet net) {m0 m : N → Nat}
    (h : Reference.Reach net m0 m) : ReachNA (expandNet net) m0 m :=
  Relation.ReflTransGen.lift id (fun _ _ hs => step_expand hF hs) _ _ h

end Rows

/-- Every place name a transition uses: its arc places and the places its output spec names. -/
def transNames (t : Trans N) : List N :=
  t.core.inputs.map NInSpec.place ++ t.core.inhibitors ++ t.core.reads ++ t.core.resets ++
    (t.out.map outPlaces).getD []

/-- **The index holds every name the net uses** (`Seam.ArcsIn` for the unexpanded net). The
flattener's index over the declared places does, since the builder declares every place an arc
or an output spec names. -/
def NamesIn (ix : PlaceIndex N) (net : Reference.Net N) : Prop :=
  ∀ t ∈ net.transitions, ∀ n ∈ transNames t, n ∈ ix.names

section Index

variable [DecidableEq N]

/-- Every name a row deposits into is named by the output spec. -/
theorem rowsN_names {t : Trans N} {r : List N} (hr : r ∈ rowsN t) :
    ∀ n ∈ r, n ∈ (t.out.map outPlaces).getD [] := by
  intro n hn
  unfold rowsN at hr
  cases ho : t.out with
  | none =>
    rw [ho] at hr
    simp only [List.mem_singleton] at hr
    subst hr; exact absurd hn List.not_mem_nil
  | some o =>
    rw [ho] at hr
    simp only [Option.map_some, Option.getD_some]
    rcases List.mem_append.mp hr with hb | ht
    · exact mem_outPlaces_branches o r hb n hn
    · cases hc : o.findTimeout with
      | none => rw [hc] at ht; exact absurd ht List.not_mem_nil
      | some c =>
        rw [hc] at ht
        exact outPlaces_findTimeout hc n (mem_outPlaces_timeout _ c r ht n hn)

/-- One row of a transition whose names are in the index is `Seam.TIn`. -/
theorem tin_row {ix : PlaceIndex N} {t : Trans N} (ht : ∀ n ∈ transNames t, n ∈ ix.names)
    {r : List N} (hr : r ∈ rowsN t) : TIn ix (t.core, r) := by
  simp only [transNames, List.mem_append, List.mem_map] at ht
  exact ⟨fun s hs => ht _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨s, hs, rfl⟩)))),
    fun n hn => ht n (Or.inl (Or.inl (Or.inl (Or.inr hn)))),
    fun n hn => ht n (Or.inl (Or.inl (Or.inr hn))),
    fun n hn => ht n (Or.inl (Or.inr hn)),
    fun n hn => ht n (Or.inr (rowsN_names hr n hn))⟩

omit [DecidableEq N] in
/-- The arcs alone of a transition whose names are in the index (the empty row). -/
theorem tin_arcs {ix : PlaceIndex N} {t : Trans N} (ht : ∀ n ∈ transNames t, n ∈ ix.names) :
    TIn ix (t.core, []) := by
  simp only [transNames, List.mem_append, List.mem_map] at ht
  exact ⟨fun s hs => ht _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨s, hs, rfl⟩)))),
    fun n hn => ht n (Or.inl (Or.inl (Or.inl (Or.inr hn)))),
    fun n hn => ht n (Or.inl (Or.inl (Or.inr hn))),
    fun n hn => ht n (Or.inl (Or.inr hn)),
    fun n hn => absurd hn List.not_mem_nil⟩

theorem arcsIn_expand {ix : PlaceIndex N} {net : Reference.Net N} (h : NamesIn ix net) :
    ArcsIn ix (expandNet net) := by
  intro ft hft n hn
  obtain ⟨t, ht, r, hr, rfl⟩ := mem_expandNet.mp hft
  have hT := tin_row (h t ht) hr
  simp only [arcNames, List.mem_append, List.mem_map] at hn
  rcases hn with (((⟨s, hs, rfl⟩ | hn) | hn) | hn) | hn
  · exact hT.inputs s hs
  · exact hT.inhibitors n hn
  · exact hT.reads n hn
  · exact hT.resets n hn
  · exact hT.branch n hn

/-- **The F2 generalisation of `Link.reach_iff_reachAD` (soundness half).** Every marking the
named net reaches restricts, through any index holding the names the net uses, to a marking the
flat rows reach from the restricted seed. No output spec is required of a transition, and the
place names are any type. -/
theorem reach_restrict {ix : PlaceIndex N} {net : Reference.Net N} (hN : NamesIn ix net)
    (hF : FixedFwdNet net) {m0 m : N → Nat} (h : Reference.Reach net m0 m) :
    ReachAD (flatNet ix (expandNet net)) (restrict ix m0) (restrict ix m) :=
  reachNA_restrict (arcsIn_expand hN) (reach_reachNA hF h)

/-- An index that covers the seed covers every reachable marking. -/
theorem covers_reach {ix : PlaceIndex N} {net : Reference.Net N} (hN : NamesIn ix net)
    (hF : FixedFwdNet net) {m0 m : N → Nat} (h0 : Novel.Seam.Covers ix m0)
    (h : Reference.Reach net m0 m) : Novel.Seam.Covers ix m :=
  covers_reachNA (arcsIn_expand hN) h0 (reach_reachNA hF h)

/-- **Read back by name, a flat reachable marking is the named one** on a covered seed. -/
theorem reach_restrict_lift {ix : PlaceIndex N} {net : Reference.Net N} (hN : NamesIn ix net)
    (hF : FixedFwdNet net) {m0 m : N → Nat} (h0 : Novel.Seam.Covers ix m0)
    (h : Reference.Reach net m0 m) :
    ReachAD (flatNet ix (expandNet net)) (restrict ix m0) (restrict ix m) ∧
      Novel.Seam.lift ix (restrict ix m) = m :=
  ⟨reach_restrict hN hF h, lift_restrict (covers_reach hN hF h0 h)⟩

end Index

/-! ## 2. J5: a flat certificate keeps the phase contract -/

section J5

variable [DecidableEq N]

/-- **A flat certificate** that `bad` holds on no reachable marking of the query's net: an
index that holds every name the net uses and every name the initial marking marks, fixed
forwards, and no marking the flat rows reach from the restricted seed is bad when read back by
name. -/
def FlatCert (ix : PlaceIndex N) (q : Query N) (bad : (N → Nat) → Prop) : Prop :=
  NamesIn ix q.net.net ∧ FixedFwdNet q.net.net ∧ Novel.Seam.Covers ix q.init ∧
    ∀ a, ReachAD (flatNet ix (expandNet q.net.net)) (restrict ix q.init) a →
      ¬ bad (Novel.Seam.lift ix a)

/-- **The certificate holds on the named net**: no reachable marking is bad. -/
theorem flatCert_sound {ix : PlaceIndex N} {q : Query N} {bad : (N → Nat) → Prop}
    (h : FlatCert ix q bad) : ∀ f, Reference.Reach q.net.net q.init f → ¬ bad f := by
  obtain ⟨hN, hF, hC, hR⟩ := h
  intro f hf
  obtain ⟨hr, hl⟩ := reach_restrict_lift hN hF hC hf
  have := hR _ hr
  rwa [hl] at this

/-- A certificate over the rows with injection on any places (`ReachADInj`, the reading of the
linear-bound and state-equation phases) is a certificate: a run without injection is a run with
it (`ForwardDeposit.reachAD_sub_inj`). -/
theorem flatCert_of_inj {ix : PlaceIndex N} {q : Query N} {bad : (N → Nat) → Prop}
    (hN : NamesIn ix q.net.net) (hF : FixedFwdNet q.net.net) (hC : Novel.Seam.Covers ix q.init)
    {envs : List PlaceId}
    (h : ∀ a, ReachADInj (flatNet ix (expandNet q.net.net)) envs (restrict ix q.init) a →
      ¬ bad (Novel.Seam.lift ix a)) : FlatCert ix q bad :=
  ⟨hN, hF, hC, fun a ha => h a (reachAD_sub_inj ha)⟩

/-- **The flat phase contract**: `PhaseSound` with the `Proven` clause carried by a flat
certificate of the violation reading. -/
def FlatPhaseSound (V : SafetyViolRel N) (P : Phase N) : Prop :=
  ∀ o q,
    (∀ meth tr c, P o q = .decided (.proven meth) tr c →
      meth ≠ "" ∧ ∃ ix, FlatCert ix q (V o.assumeNoReaping q.net q.prop)) ∧
    (∀ tr, P o q = .decided .violated tr (some true) →
      ∃ f, Reference.Run q.net.net tr q.init f ∧ V o.assumeNoReaping q.net q.prop f) ∧
    (∀ why tr c, P o q = .decided (.unknown why) tr c → why ≠ "")

/-- **J5.** A phase whose `Proven` carries a flat certificate keeps [VER-003]'s phase contract
on the named verified net. -/
theorem FlatPhaseSound.phaseSound {V : SafetyViolRel N} {P : Phase N}
    (h : FlatPhaseSound V P) : PhaseSound V P := by
  intro o q
  obtain ⟨h1, h2, h3⟩ := h o q
  refine ⟨fun meth tr c hp => ?_, h2, h3⟩
  obtain ⟨hm, ix, hc⟩ := h1 meth tr c hp
  exact ⟨hm, flatCert_sound hc⟩

/-- **The flat contract for a solver-backed phase program**: `ProgSound` with the `Proven`
clause carried by a flat certificate. The solver's soundness goes into the replies `R`. -/
def FlatProgSound (R : String → SolverReply → Prop) (V : SafetyViolRel N)
    (P : Options → Query N → PhaseProg PhaseOut) : Prop :=
  ∀ o q out, Yields R (P o q) out →
    (∀ meth tr c, out = .decided (.proven meth) tr c →
      meth ≠ "" ∧ ∃ ix, FlatCert ix q (V o.assumeNoReaping q.net q.prop)) ∧
    (∀ tr, out = .decided .violated tr (some true) →
      ∃ f, Reference.Run q.net.net tr q.init f ∧ V o.assumeNoReaping q.net q.prop f) ∧
    (∀ why tr c, out = .decided (.unknown why) tr c → why ≠ "")

/-- **J5 for programs.** A phase program whose `Proven` carries a flat certificate keeps the
program contract, so `Pipeline.pipeVerify_VER_003_of` takes it as a step. -/
theorem FlatProgSound.progSound {R : String → SolverReply → Prop} {V : SafetyViolRel N}
    {P : Options → Query N → PhaseProg PhaseOut} (h : FlatProgSound R V P) : ProgSound R V P := by
  intro o q out hy
  obtain ⟨h1, h2, h3⟩ := h o q out hy
  refine ⟨fun meth tr c hp => ?_, h2, h3⟩
  obtain ⟨hm, ix, hc⟩ := h1 meth tr c hp
  exact ⟨hm, flatCert_sound hc⟩

end J5

/-! ## 3. The timed image and the frame of a firing -/

section Image

variable [DecidableEq N]

/-- One transition of the flat timed image: its arcs through the index, its rows through the
index, its interval the graph's reading of its timing (`TimedScg.mkT`). -/
def flatTT (ix : PlaceIndex N) (X : TimedNet N) (t : Trans N) : TTrans :=
  mkT (toFlatT ix t.core) ((rowsN t).map fun r => r.map ix.idx) (X.timing t)

/-- **The flat timed image** of a named timed net: one entry per transition, in net order, so
the transition at position `i` of the net is the graph's transition `i`. -/
def flatTNet (ix : PlaceIndex N) (X : TimedNet N) : TNet := X.net.transitions.map (flatTT ix X)

variable {ix : PlaceIndex N} {X : TimedNet N}

theorem flatTNet_length : (flatTNet ix X).length = X.net.transitions.length := List.length_map _

theorem flatTNet_getElem? {i : Nat} (h : i < X.net.transitions.length) :
    (flatTNet ix X)[i]? = some (flatTT ix X X.net.transitions[i]) := by
  simp [flatTNet, List.getElem?_map, List.getElem?_eq_getElem h]

theorem trOf_flat {i : Nat} (h : i < X.net.transitions.length) :
    trOf (flatTNet ix X) i = toFlatT ix X.net.transitions[i].core := by
  simp [trOf, flatTNet_getElem? h, flatTT, mkT]

theorem rowsOf_flat {i : Nat} (h : i < X.net.transitions.length) :
    rowsOf (flatTNet ix X) i = (rowsN X.net.transitions[i]).map fun r => r.map ix.idx := by
  simp [rowsOf, flatTNet_getElem? h, flatTT, mkT]

theorem eftOf_flat {i : Nat} (h : i < X.net.transitions.length) :
    eftOf (flatTNet ix X) i = eftT (X.timing X.net.transitions[i]) := by
  simp [eftOf, flatTNet_getElem? h, flatTT, mkT]

theorem lftOf_flat {i : Nat} (h : i < X.net.transitions.length) :
    lftOf (flatTNet ix X) i = lftT (X.timing X.net.transitions[i]) := by
  simp [lftOf, flatTNet_getElem? h, flatTT, mkT]

/-- The timing of the net's transition at position `i` (`immediate` past the end). -/
def timingAt (X : TimedNet N) (i : Nat) : Timing :=
  match X.net.transitions[i]? with
  | some t => X.timing t
  | none => .immediate

omit [DecidableEq N] in
theorem timingAt_eq {i : Nat} (h : i < X.net.transitions.length) :
    timingAt X i = X.timing X.net.transitions[i] := by
  simp [timingAt, List.getElem?_eq_getElem h]

/-- The flat intervals are the graph's reading of the net's timings. -/
theorem fromTimings_flat :
    Novel.TimedScg.FromTimings (flatTNet ix X) (timingAt X) := by
  intro i hi
  rw [flatTNet_length] at hi
  rw [eftOf_flat hi, lftOf_flat hi, timingAt_eq hi]
  exact ⟨rfl, rfl⟩

/-- **Premise 6 holds of the flat image** of a net whose timings the shipped constructors
accept. -/
theorem timingWF_flat (hv : ∀ t ∈ X.net.transitions, (X.timing t).Valid) :
    TimingWF (flatTNet ix X) :=
  Novel.TimedScg.timingWF_of_valid_timings fromTimings_flat fun i hi => by
    rw [flatTNet_length] at hi
    rw [timingAt_eq hi]
    exact hv _ (List.getElem_mem hi)

/-- No earliest bound of the flat image is negative. -/
theorem eftOf_flat_nonneg (i : Nat) : 0 ≤ eftOf (flatTNet ix X) i := by
  by_cases hi : i < X.net.transitions.length
  · rw [eftOf_flat hi]; unfold eftT; exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  · have : (flatTNet ix X)[i]? = none :=
      List.getElem?_eq_none (by rw [flatTNet_length]; omega)
    simp [eftOf, this]

/-- An enabled index is a transition of the net. -/
theorem en_flat_lt {a : AMarking} {i : Nat} (h : en (flatTNet ix X) a i = true) :
    i < X.net.transitions.length := by
  have := en_lt h
  rwa [flatTNet_length] at this

/-- **Enablement agrees**: the flat transition `i` is enabled at the restricted marking iff the
net's transition `i` is enabled at the named marking. -/
theorem en_flat (hN : NamesIn ix X.net) {i : Nat} (h : i < X.net.transitions.length)
    (m : N → Nat) : en (flatTNet ix X) (restrict ix m) i = enabledNA m X.net.transitions[i].core := by
  rw [en_eq (by rw [flatTNet_length]; exact h), trOf_flat h]
  exact enabledA_restrict ix (tin_arcs (hN _ (List.getElem_mem h))) m

/-- **The intermediate marking agrees** (`consume_marking` and [TIME-012]'s `mid`). -/
theorem inter_restrict {t : Trans N} (hT : ∀ n ∈ transNames t, n ∈ ix.names) (m : N → Nat) :
    inter (restrict ix m) (toFlatT ix t.core) = restrict ix (mid t m) := by
  have h := fireAD_restrict ix (tin_arcs hT) m
  have e1 : inter (restrict ix m) (toFlatT ix t.core) =
      fireAD (restrict ix m) (toFlatT ix t.core) (List.map ix.idx ([] : List N)) := by
    funext p
    rw [fireAD_eq_inter_add]
    simp
  have e2 : fireNA m t.core [] = mid t m := by
    funext n
    simp [fireNA, mid, fireNC, depProd]
  rw [e1, h, e2]

/-- **The successor marking agrees** for a row of the transition. -/
theorem fireAD_row {t : Trans N} (hT : ∀ n ∈ transNames t, n ∈ ix.names) {r : List N}
    (hr : r ∈ rowsN t) (m : N → Nat) :
    fireAD (restrict ix m) (toFlatT ix t.core) (r.map ix.idx) = restrict ix (fireNA m t.core r) :=
  fireAD_restrict ix (tin_row hT hr) m

end Image

section Frame

variable [DecidableEq N]

/-- A place the firing does not write keeps its count. -/
theorem fireNA_unwritten {t : Trans N} {d : List N} {p : N} (hw : writes t d p = false)
    (m : N → Nat) : fireNA m t.core d p = m p := by
  simp only [writes, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hw
  obtain ⟨⟨hin, hres⟩, hd⟩ := hw
  have hspec : nspecAt t.core p = none := by
    cases h : nspecAt t.core p with
    | none => rfl
    | some s =>
      obtain ⟨hs, hp⟩ := nspecAt_place h
      exact absurd (List.mem_map.mpr ⟨s, hs, hp⟩) hin
  simp [fireNA, fireNC, hres, nconsumed, hspec, depProd, List.count_eq_zero_of_not_mem hd]

/-- **The frame of a firing**: a transition none of whose arc places the firing writes is
enabled after it exactly when it was before. -/
theorem enabled_frame {t u : Trans N} {d : List N} (hw : writesArc t d u = false)
    (m : N → Nat) : enabledNA (fireNA m t.core d) u.core = enabledNA m u.core := by
  have hall : ∀ p ∈ arcPlaces u, fireNA m t.core d p = m p := by
    intro p hp
    apply fireNA_unwritten
    simp only [writesArc, List.any_eq_false] at hw
    simpa using hw p hp
  unfold enabledNA
  have e1 := all_congr_mem (l := u.core.inputs)
    (p := fun s => decide (s.card.required ≤ fireNA m t.core d s.place))
    (q := fun s => decide (s.card.required ≤ m s.place))
    fun s hs => by
      rw [hall s.place (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_map_of_mem hs))))]
  have e2 := all_congr_mem (l := u.core.inhibitors)
    (p := fun p => fireNA m t.core d p == 0) (q := fun p => m p == 0)
    fun p hp => by
      rw [hall p (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hp)))]
  have e3 := all_congr_mem (l := u.core.reads)
    (p := fun p => decide (1 ≤ fireNA m t.core d p)) (q := fun p => decide (1 ≤ m p))
    fun p hp => by rw [hall p (List.mem_append_left _ (List.mem_append_right _ hp))]
  rw [e1, e2, e3]

end Frame

/-! ## 4. J7: on-time runs of the timed reference are runs of `TStep` -/

/-- **Strong urgency** (ruling D3): the steps of `R` an on-time executor takes. No reap, and no
delay that carries an armed transition past its latest bound; every firing `R` allows. It
filters runs and never restricts `R`, so the TIME blocks' `CoversDelay` stays true of the same
witness `RefTStep`. -/
def OnTimeStep (R : TRel N) (X : TimedNet N) (s : TSt N) (l : TLbl N) (s' : TSt N) : Prop :=
  R X s l s' ∧ match l with
    | .delay δ => ∀ t ∈ X.net.transitions, Armed s t → Elapsed s t + δ ≤ (TimingOf X t).latest
    | .reap _ => False
    | .fire _ _ => True

/-- An on-time executor never reaps. -/
theorem onTime_no_reap {R : TRel N} {X : TimedNet N} {s s' : TSt N} {t : Trans N} :
    ¬ OnTimeStep R X s (.reap t) s' := fun h => h.2

section OnTime

variable [DecidableEq N]

/-- An on-time firing of the timed reference is a reference firing (the join to `RefFire`). -/
theorem onTime_fire_projects {X : TimedNet N} {s s' : TSt N} {t : Trans N} {d : List N}
    (h : OnTimeStep RefTStep X s (.fire t d) s') : RefFire t s.m d s'.m :=
  refTStep_projects h.1

/-- The states of the on-time runs of the timed reference from `m0` at clock reading `now0`. -/
def OnTimeReach (X : TimedNet N) (m0 : N → Nat) (now0 : Nat) : TSt N → Prop :=
  Relation.ReflTransGen (fun s s' => ∃ l, OnTimeStep RefTStep X s l s') (TSt.init X m0 now0)

/-- The states of all runs of the timed reference (late delays and reaps included). -/
def RefReach (X : TimedNet N) (m0 : N → Nat) (now0 : Nat) : TSt N → Prop :=
  Relation.ReflTransGen (fun s s' => ∃ l, RefTStep X s l s') (TSt.init X m0 now0)

theorem OnTimeReach.ref {X : TimedNet N} {m0 : N → Nat} {now0 : Nat} {s : TSt N}
    (h : OnTimeReach X m0 now0 s) : RefReach X m0 now0 s :=
  Relation.ReflTransGen.lift id (fun _ _ ⟨l, hl⟩ => ⟨l, hl.1⟩) _ _ h

/-- **The timed reference reaches only markings the untimed reference reaches.** -/
theorem refReach_reach {X : TimedNet N} {m0 : N → Nat} {now0 : Nat} {s : TSt N}
    (h : RefReach X m0 now0 s) : Reference.Reach X.net m0 s.m := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨l, hl⟩ := hs
    have hl' : RefTStepW refPolicy _ _ l _ := hl
    cases hl' with
    | delay => exact ih
    | reap => exact ih
    | fire t d m' ht hf ha hg hx => exact Relation.ReflTransGen.tail ih ⟨_, t, ht, rfl, d, hf⟩

/-- Every stamp is a reading the clock has passed. -/
def StampsLe (s : TSt N) : Prop := ∀ n v, s.stamp n = some v → v ≤ s.now

/-- Every enabled transition of the net is armed: true of every on-time run, where nothing is
reaped. -/
def AllArmed (X : TimedNet N) (s : TSt N) : Prop :=
  ∀ u ∈ X.net.transitions, Enabled u s.m → Armed s u

/-- **The on-time simulation**: the flat marking is the restricted marking, and the `TStep`
clock of every enabled transition is its elapsed time in seconds. -/
def OnTimeSim (ix : PlaceIndex N) (X : TimedNet N) (s : TSt N) (ts : TState) : Prop :=
  ts.m = restrict ix s.m ∧ StampsLe s ∧ AllArmed X s ∧
    ∀ i (h : i < X.net.transitions.length), Enabled X.net.transitions[i] s.m →
      ts.ν i = (Elapsed s X.net.transitions[i] : ℚ) / 1000

variable {ix : PlaceIndex N} {X : TimedNet N}

omit [DecidableEq N] in
/-- The elapsed time of an armed transition grows with a delay. -/
theorem elapsed_delay {s : TSt N} (hS : StampsLe s) {u : Trans N}
    (ha : (s.stamp u.core.name).isSome) (δ : Nat) :
    Elapsed { s with now := s.now + δ } u = Elapsed s u + δ := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ha
  have := hS _ v hv
  simp only [Elapsed, ClockReading, hv, Option.getD_some]
  omega

omit [DecidableEq N] in
/-- With distinct names, two positions carry one name exactly when they are one position. -/
theorem name_bne (hD : NamesDistinct X) {i j : Nat} (hi : i < X.net.transitions.length)
    (hj : j < X.net.transitions.length) :
    (X.net.transitions[j].core.name != X.net.transitions[i].core.name) = (j != i) := by
  have key : X.net.transitions[j].core.name = X.net.transitions[i].core.name ↔ j = i := by
    have h := (List.Nodup.getElem_inj_iff hD (i := j) (j := i)
      (hi := by simpa using hj) (hj := by simpa using hi))
    rwa [List.getElem_map, List.getElem_map] at h
  by_cases hji : j = i
  · subst hji; simp [bne]
  · have : X.net.transitions[j].core.name ≠ X.net.transitions[i].core.name :=
      fun h => hji (key.mp h)
    rw [bne_iff_ne.mpr this, bne_iff_ne.mpr hji]

/-- **The graph's clock rule on the image.** `TimedScg.persists` of the flat transition `j` across
the firing of `i` with a row `d` is: `j` enabled before, a different transition, enabled in the
intermediate marking and enabled after. -/
theorem persists_flat (hN : NamesIn ix X.net) (hD : NamesDistinct X) {i j : Nat}
    (hi : i < X.net.transitions.length) (hj : j < X.net.transitions.length) {d : List N}
    (hd : d ∈ rowsN X.net.transitions[i]) (m : N → Nat) :
    persists (flatTNet ix X) (restrict ix m) i (d.map ix.idx) j =
      (enabledNA m X.net.transitions[j].core &&
        X.net.transitions[j].core.name != X.net.transitions[i].core.name &&
        enabledNA (mid X.net.transitions[i] m) X.net.transitions[j].core &&
        enabledNA (fireNA m X.net.transitions[i].core d) X.net.transitions[j].core) := by
  have hT := hN _ (List.getElem_mem hi)
  unfold persists survives
  rw [trOf_flat hi, fireAD_row hT hd m, inter_restrict hT m, en_flat hN hj, en_flat hN hj,
    en_flat hN hj, name_bne hD hi hj]
  cases enabledNA m X.net.transitions[j].core <;> cases (j != i) <;>
    cases enabledNA (mid X.net.transitions[i] m) X.net.transitions[j].core <;>
    cases enabledNA (fireNA m X.net.transitions[i].core d) X.net.transitions[j].core <;> rfl

omit [DecidableEq N] in
/-- Under `AllArmed`, armed is enabled. -/
theorem armed_eq {s : TSt N} (hA : AllArmed X s) {u : Trans N} (hu : u ∈ X.net.transitions) :
    s.armed u = enabledNA s.m u.core := by
  cases he : enabledNA s.m u.core with
  | false => simp [TSt.armed, he]
  | true => exact (armed_iff s u).mp (hA u hu he)

/-- **Premise 9, clock by clock.** On an on-time state, the reference keeps the stamp of the
net's transition `j` across the firing of transition `i` exactly when the graph's rule
`persists` keeps clock `j`. -/
theorem keep_eq_persists (hN : NamesIn ix X.net) (hD : NamesDistinct X) {s : TSt N}
    (hA : AllArmed X s) {i j : Nat} (hi : i < X.net.transitions.length)
    (hj : j < X.net.transitions.length) {d : List N} (hd : d ∈ rowsN X.net.transitions[i]) :
    refPolicy.keep X s X.net.transitions[i] d (fireNA s.m X.net.transitions[i].core d)
        X.net.transitions[j] =
      persists (flatTNet ix X) (restrict ix s.m) i (d.map ix.idx) j := by
  rw [persists_flat hN hD hi hj hd, ← armed_eq hA (List.getElem_mem hj)]
  rfl

/-- The stamp a firing leaves on the net's transition `u`, under the reference policy. -/
theorem stamp_after (hD : NamesDistinct X) {u : Trans N} (hu : u ∈ X.net.transitions)
    (s : TSt N) (t : Trans N) (d : List N) (m' : N → Nat) :
    restampAll refPolicy X s t d m' u.core.name =
      if refPolicy.keep X s t d m' u then s.stamp u.core.name
      else if refPolicy.rearm X s t d m' u then some s.now else none := by
  rw [restampAll_inNet ((inNet_iff_mem hD u).mpr hu)]
  rfl

/-- After a firing, every stamp is at most the clock reading. -/
theorem stampsLe_fire {s : TSt N} (hS : StampsLe s) (t : Trans N) (d : List N)
    (m' : N → Nat) :
    StampsLe ({ m := m', now := s.now, stamp := restampAll refPolicy X s t d m' } : TSt N) := by
  intro n v hv
  rcases restampAll_cases refPolicy X s t d m' n with h | h | h <;> simp only [h] at hv
  · exact hS n v hv
  · simp only [Option.some.injEq] at hv; subst hv; exact le_refl _
  · exact absurd hv (by simp)

/-- A transition enabled after a firing is re-armed when it does not keep its stamp: either it
was armed (its clock restarts) or, not being enabled before, the firing wrote one of its arc
places. -/
theorem rearm_of_enabled {s : TSt N} (hA : AllArmed X s) {u : Trans N}
    (hu : u ∈ X.net.transitions) (t : Trans N) (d : List N)
    (he : enabledNA (fireNA s.m t.core d) u.core = true) :
    refPolicy.rearm X s t d (fireNA s.m t.core d) u = true := by
  show (enabledNA (fireNA s.m t.core d) u.core && (s.armed u || writesArc t d u)) = true
  rw [he, Bool.true_and]
  cases hw : writesArc t d u with
  | true => simp
  | false =>
    rw [enabled_frame hw] at he
    rw [armed_eq hA hu, he]
    rfl

omit [DecidableEq N] in
/-- The initial state is simulated by `TStep`'s initial state. -/
theorem onTime_init (hD : NamesDistinct X) (m0 : N → Nat) (now0 : Nat) :
    OnTimeSim ix X (TSt.init X m0 now0) (s0 (restrict ix m0)) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro n v hv
    simp only [TSt.init] at hv
    split at hv
    · split at hv
      · simp only [Option.some.injEq] at hv; subst hv; exact le_refl _
      · exact absurd hv (by simp)
    · exact absurd hv (by simp)
  · intro u hu he
    exact ((initArms_init X m0 now0 u ((inNet_iff_mem hD u).mpr hu)).1).mpr he
  · intro i hi he
    have h0 : Elapsed (TSt.init X m0 now0) X.net.transitions[i] = 0 :=
      initArms_elapsed initArms_init (now0 := now0)
        ((inNet_iff_mem hD _).mpr (List.getElem_mem hi)) he
    rw [h0]
    simp [s0]

/-- **One on-time delay** is a `TStep` delay of the image. -/
theorem onTime_delay (hN : NamesIn ix X.net) {s : TSt N} {ts : TState} (hsim : OnTimeSim ix X s ts)
    {δ : Nat}
    (hon : ∀ t ∈ X.net.transitions, Armed s t → Elapsed s t + δ ≤ (TimingOf X t).latest) :
    ∃ ts', TStep (flatTNet ix X) ts ts' ∧ OnTimeSim ix X { s with now := s.now + δ } ts' := by
  obtain ⟨hm, hS, hA, hν⟩ := hsim
  have hδ : (0 : ℚ) ≤ (δ : ℚ) / 1000 := div_nonneg (Nat.cast_nonneg _) (by norm_num)
  refine ⟨_, TStep.delay ts ((δ : ℚ) / 1000) hδ fun j hj => ?_, ?_⟩
  · have hl := en_flat_lt hj
    rw [hm, en_flat hN hl] at hj
    have harm := hA _ (List.getElem_mem hl) hj
    have hle := hon _ (List.getElem_mem hl) harm
    rw [hν j hl hj, lftOf_flat hl]
    unfold lftT
    refine WithTop.coe_le_coe.mpr ?_
    rw [← add_div, div_le_div_iff_of_pos_right (by norm_num)]
    exact_mod_cast hle
  · refine ⟨hm, fun n v hv => ?_, fun u hu he => hA u hu he, fun j hj he => ?_⟩
    · have := hS n v hv; simp only at this ⊢; omega
    · have harm := hA _ (List.getElem_mem hj) he
      simp only
      rw [elapsed_delay hS harm.2 δ, hν j hj he]
      push_cast
      ring

/-- **One on-time firing** is a `TStep` firing of the image, with the row the firing deposits;
the clocks follow `persists` because the reference's `keep` is `persists` (`keep_eq_persists`). -/
theorem onTime_fire (hN : NamesIn ix X.net) (hD : NamesDistinct X) (hF : FixedFwdNet X.net)
    {s : TSt N} {ts : TState} (hsim : OnTimeSim ix X s ts) {t : Trans N} {d : List N}
    {m' : N → Nat} (ht : t ∈ X.net.transitions) (hf : Fires t s.m d m') (hr : Ready X s t) :
    ∃ ts', TStep (flatTNet ix X) ts ts' ∧
      OnTimeSim ix X { m := m', now := s.now, stamp := restampAll refPolicy X s t d m' } ts' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  obtain ⟨hdr, rfl, hen⟩ := fires_mem_rowsN (hF _ ht) hf
  obtain ⟨hm, hS, hA, hν⟩ := hsim
  have hT := hN _ ht
  have hen' : en (flatTNet ix X) ts.m i = true := by rw [hm, en_flat hN hi]; exact hen
  have hready : eftOf (flatTNet ix X) i ≤ ts.ν i := by
    rw [eftOf_flat hi, hν i hi hen]
    unfold eftT
    exact div_le_div_of_nonneg_right (by exact_mod_cast hr.2.1) (by norm_num)
  have hrow : d.map ix.idx ∈ rowsOf (flatTNet ix X) i := by
    rw [rowsOf_flat hi]; exact List.mem_map_of_mem hdr
  refine ⟨_, TStep.fire ts i (d.map ix.idx) hen' hready hrow, ?_, stampsLe_fire hS _ _ _, ?_, ?_⟩
  · simp only
    rw [hm, trOf_flat hi, fireAD_row hT hdr]
  · intro u hu he
    refine ⟨he, ?_⟩
    show (restampAll refPolicy X s _ d _ u.core.name).isSome = true
    rw [stamp_after hD hu]
    split_ifs with hk hra
    · have : s.armed u = true := by
        simp only [refPolicy, Bool.and_eq_true] at hk; exact hk.1.1.1
      exact ((armed_iff s u).mpr this).2
    · rfl
    · exact absurd (rearm_of_enabled hA hu _ d he) hra
  · intro j hj he
    have hu := List.getElem_mem hj
    have hkp := keep_eq_persists hN hD hA hi hj hdr
    simp only [Elapsed, ClockReading]
    rw [stamp_after hD hu, hm, ← hkp]
    by_cases hk : refPolicy.keep X s X.net.transitions[i] d (fireNA s.m X.net.transitions[i].core d)
        X.net.transitions[j] = true
    · rw [if_pos hk, if_pos hk]
      have hej : Enabled X.net.transitions[j] s.m := by
        have : s.armed X.net.transitions[j] = true := by
          simp only [refPolicy, Bool.and_eq_true] at hk; exact hk.1.1.1
        exact ((armed_iff s _).mpr this).1
      rw [hν j hj hej]
      rfl
    · rw [if_neg hk, if_neg hk, if_pos (rearm_of_enabled hA hu _ d he)]
      simp

/-- **J7: every on-time run of the timed reference is a run of `TStep`** on the flat image,
from the restricted initial marking with every clock at `0`, with the restricted marking and,
for every enabled transition, its elapsed time in seconds as its clock. -/
theorem onTime_sim (hN : NamesIn ix X.net) (hD : NamesDistinct X) (hF : FixedFwdNet X.net)
    {m0 : N → Nat} {now0 : Nat} {s : TSt N} (h : OnTimeReach X m0 now0 s) :
    ∃ ts, TReach (flatTNet ix X) (restrict ix m0) ts ∧ OnTimeSim ix X s ts := by
  induction h with
  | refl => exact ⟨_, Relation.ReflTransGen.refl, onTime_init hD m0 now0⟩
  | tail _ hstep ih =>
    obtain ⟨ts, hts, hsim⟩ := ih
    obtain ⟨l, hR, hon⟩ := hstep
    have hR' : RefTStepW refPolicy _ _ l _ := hR
    cases hR' with
    | delay =>
      obtain ⟨ts', hstep', hsim'⟩ := onTime_delay hN hsim hon
      exact ⟨ts', Relation.ReflTransGen.tail hts hstep', hsim'⟩
    | reap => exact hon.elim
    | fire t d m' ht hf ha hg hx =>
      obtain ⟨ts', hstep', hsim'⟩ :=
        onTime_fire hN hD hF hsim ht hf ((ready_iff _ _ t).mpr ⟨ha, hg, hx⟩)
      exact ⟨ts', Relation.ReflTransGen.tail hts hstep', hsim'⟩

/-- J7, the marking: every on-time run's marking, restricted, is the marking of a `TStep` run of
the flat image. -/
theorem onTime_tReach (hN : NamesIn ix X.net) (hD : NamesDistinct X) (hF : FixedFwdNet X.net)
    {m0 : N → Nat} {now0 : Nat} {s : TSt N} (h : OnTimeReach X m0 now0 s) :
    ∃ ts, TReach (flatTNet ix X) (restrict ix m0) ts ∧ ts.m = restrict ix s.m := by
  obtain ⟨ts, hts, hsim⟩ := onTime_sim hN hD hF h
  exact ⟨ts, hts, hsim.1⟩

/-- **J7 on the graph**: on a closed timed class graph of the flat image, every on-time run's
marking, restricted, is the marking of a stored, well-formed class. -/
theorem onTime_graph (hN : NamesIn ix X.net) (hD : NamesDistinct X) (hF : FixedFwdNet X.net)
    (hv : ∀ t ∈ X.net.transitions, (X.timing t).Valid) {eps : ℚ} (heps : 0 ≤ eps)
    {maxClasses : Nat} {cut : Nat → Bool} {fuel : Nat} {m0 : N → Nat}
    {o : Novel.RouteB.Decide.Out Cls}
    (ho : Scg.scgGraph (flatTNet ix X) eps maxClasses cut fuel (restrict ix m0) = some o)
    (hc : o.complete = true) {now0 : Nat} {s : TSt N} (h : OnTimeReach X m0 now0 s) :
    ∃ T ∈ o.cls, T.m = restrict ix s.m ∧ ClsWF (flatTNet ix X) T := by
  obtain ⟨ts, hts, hm⟩ := onTime_tReach hN hD hF h
  obtain ⟨T, hT, hin, hwf⟩ := Scg.scgGraph_covers (timingWF_flat hv) heps ho hc hts
  exact ⟨T, hT, hin.1.symm.trans hm, hwf⟩

/-- **`SPURIOUS_UNDER_TIMING` for the timed reference** ([VER-023]): a marking predicate that no
stored class of the closed timed graph satisfies, read back by name, holds of no on-time run of
`RefTStep`, when the index covers the initial marking. -/
theorem onTime_safety_closed (hN : NamesIn ix X.net) (hD : NamesDistinct X)
    (hF : FixedFwdNet X.net) (hv : ∀ t ∈ X.net.transitions, (X.timing t).Valid) {eps : ℚ}
    (heps : 0 ≤ eps) {maxClasses : Nat} {cut : Nat → Bool} {fuel : Nat} {m0 : N → Nat}
    (hC : Novel.Seam.Covers ix m0) {o : Novel.RouteB.Decide.Out Cls}
    (ho : Scg.scgGraph (flatTNet ix X) eps maxClasses cut fuel (restrict ix m0) = some o)
    (hc : o.complete = true) (bad : (N → Nat) → Prop)
    (hgood : ∀ T ∈ o.cls, ¬ bad (Novel.Seam.lift ix T.m)) {now0 : Nat} {s : TSt N}
    (h : OnTimeReach X m0 now0 s) : ¬ bad s.m := by
  obtain ⟨T, hT, hm, -⟩ := onTime_graph hN hD hF hv heps ho hc h
  have hcov := covers_reach hN hF hC (refReach_reach h.ref)
  have := hgood T hT
  rwa [hm, lift_restrict hcov] at this

end OnTime

/-! ## 5. J8: every run of the timed reference is covered by the relaxed graph -/

section Late

variable [DecidableEq N]

open Libpetri.Novel.TimedScg (relax relaxMax maxLft en_relax trOf_relax rowsOf_relax eftOf_relax
  lftOf_relax persists_relax timingWF_relax timed_run_sound relax_relaxMax)

variable {ix : PlaceIndex N} {X : TimedNet N}

/-- **The late simulation**: the flat marking is the restricted marking, every `TStep` clock is
non-negative, and the clock of every armed transition is at least its elapsed time in seconds. -/
def LateSim (ix : PlaceIndex N) (X : TimedNet N) (s : TSt N) (ts : TState) : Prop :=
  ts.m = restrict ix s.m ∧ StampsLe s ∧ (∀ i, 0 ≤ ts.ν i) ∧
    ∀ i (h : i < X.net.transitions.length), Armed s X.net.transitions[i] →
      (Elapsed s X.net.transitions[i] : ℚ) / 1000 ≤ ts.ν i

/-- A transition that is enabled and holds no clock was reaped, so its timing is reapable. -/
def UnarmedReapable (X : TimedNet N) (s : TSt N) : Prop :=
  ∀ u ∈ X.net.transitions, Enabled u s.m → ¬ Armed s u → Reapable X u

omit [DecidableEq N] in
theorem late_init (hD : NamesDistinct X) (m0 : N → Nat) (now0 : Nat) :
    LateSim ix X (TSt.init X m0 now0) (s0 (restrict ix m0)) ∧
      UnarmedReapable X (TSt.init X m0 now0) := by
  obtain ⟨-, hS, hA, -⟩ := onTime_init (ix := ix) hD m0 now0
  refine ⟨⟨rfl, hS, fun _ => le_refl _, fun i hi ha => ?_⟩, fun u hu he hna => absurd (hA u hu he) hna⟩
  have h0 : Elapsed (TSt.init X m0 now0) X.net.transitions[i] = 0 :=
    initArms_elapsed initArms_init (now0 := now0)
      ((inNet_iff_mem hD _).mpr (List.getElem_mem hi)) ha.1
  rw [h0]
  simp [s0]

/-- `keep` implies `persists`: a stamp the reference keeps is a clock the graph keeps. -/
theorem keep_persists (hN : NamesIn ix X.net) (hD : NamesDistinct X) {s : TSt N} {i j : Nat}
    (hi : i < X.net.transitions.length) (hj : j < X.net.transitions.length) {d : List N}
    (hd : d ∈ rowsN X.net.transitions[i])
    (hk : refPolicy.keep X s X.net.transitions[i] d (fireNA s.m X.net.transitions[i].core d)
      X.net.transitions[j] = true) :
    persists (flatTNet ix X) (restrict ix s.m) i (d.map ix.idx) j = true := by
  rw [persists_flat hN hD hi hj hd]
  simp only [refPolicy, Bool.and_eq_true] at hk ⊢
  obtain ⟨⟨⟨ha, hn⟩, hmid⟩, haft⟩ := hk
  exact ⟨⟨⟨by simp [TSt.armed] at ha; exact ha.1, hn⟩, hmid⟩, haft⟩

/-- **One step of the timed reference** (a delay of any length, a firing, a reap) is matched by
at most one `TStep` of the relaxed image. -/
theorem late_step (hN : NamesIn ix X.net) (hD : NamesDistinct X) (hF : FixedFwdNet X.net)
    {s s' : TSt N} {ts : TState} (hsim : LateSim ix X s ts) (hu : UnarmedReapable X s)
    {l : TLbl N} (hR : RefTStep X s l s') :
    ∃ ts', Relation.ReflTransGen (TStep (relax (flatTNet ix X))) ts ts' ∧ LateSim ix X s' ts' ∧
      UnarmedReapable X s' := by
  obtain ⟨hm, hS, hnn, hν⟩ := hsim
  have hR' : RefTStepW refPolicy X s l s' := hR
  cases hR' with
  | delay δ =>
    have hδ : (0 : ℚ) ≤ (δ : ℚ) / 1000 := div_nonneg (Nat.cast_nonneg _) (by norm_num)
    refine ⟨_, Relation.ReflTransGen.single (TStep.delay ts ((δ : ℚ) / 1000) hδ fun j _ => by
      rw [lftOf_relax]; exact le_top), ⟨hm, fun n v hv => ?_, fun i => ?_, fun j hj ha => ?_⟩,
      fun u hu' he hna => hu u hu' he hna⟩
    · have := hS n v hv; simp only at this ⊢; omega
    · simp only; linarith [hnn i]
    · simp only
      rw [elapsed_delay hS ha.2 δ]
      have := hν j hj ha
      push_cast
      linarith
  | reap t ht hx =>
    refine ⟨ts, Relation.ReflTransGen.refl, ⟨hm, fun n v hv => ?_, hnn, fun j hj ha => ?_⟩, ?_⟩
    · by_cases hn : n = t.core.name
      · simp [hn] at hv
      · simp only [hn, if_false] at hv
        exact hS n v hv
    · have hne : X.net.transitions[j].core.name ≠ t.core.name := by
        intro he; have := ha.2; simp [he] at this
      have ha' : Armed s X.net.transitions[j] := by
        refine ⟨ha.1, ?_⟩
        have := ha.2; simpa [hne] using this
      have := hν j hj ha'
      simpa [Elapsed, ClockReading, hne] using this
    · intro u hu' he hna
      by_cases hne : u.core.name = t.core.name
      · have hut : u = t := by
          have h1 := (inNet_iff_mem hD u).mpr hu'
          have h2 := (inNet_iff_mem hD t).mpr ht
          unfold InNet at h1 h2
          rw [hne] at h1
          rw [h1] at h2
          exact Option.some.inj h2
        subst hut
        have := (expired_iff X s u).mpr hx
        exact this.1
      · refine hu u hu' he fun ha => hna ⟨ha.1, ?_⟩
        have := ha.2; simpa [hne] using this
  | fire t d m' ht hf ha hg hx =>
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨hdr, rfl, hen⟩ := fires_mem_rowsN (hF _ ht) hf
    have hT := hN _ ht
    have hen' : en (relax (flatTNet ix X)) ts.m i = true := by
      rw [en_relax, hm, en_flat hN hi]; exact hen
    have hready : eftOf (relax (flatTNet ix X)) i ≤ ts.ν i := by
      rw [eftOf_relax, eftOf_flat hi]
      have h1 := hν i hi ((armed_iff s _).mpr ha)
      have h2 : (X.timing X.net.transitions[i]).earliest ≤ Elapsed s X.net.transitions[i] :=
        of_decide_eq_true hg
      unfold eftT
      exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h2) (by norm_num)) h1
    have hrow : d.map ix.idx ∈ rowsOf (relax (flatTNet ix X)) i := by
      rw [rowsOf_relax, rowsOf_flat hi]; exact List.mem_map_of_mem hdr
    refine ⟨_, Relation.ReflTransGen.single (TStep.fire ts i (d.map ix.idx) hen' hready hrow),
      ⟨?_, stampsLe_fire hS _ _ _, fun j => ?_, fun j hj haj => ?_⟩, ?_⟩
    · simp only
      rw [trOf_relax, hm, trOf_flat hi, fireAD_row hT hdr]
    · simp only
      split_ifs
      · exact hnn j
      · exact le_refl _
    · have hu' := List.getElem_mem hj
      have hst := haj.2
      simp only [Elapsed, ClockReading]
      simp only at hst
      rw [stamp_after hD hu'] at hst ⊢
      by_cases hk : refPolicy.keep X s X.net.transitions[i] d
          (fireNA s.m X.net.transitions[i].core d) X.net.transitions[j] = true
      · rw [if_pos hk]
        have hp := keep_persists hN hD hi hj hdr hk
        rw [persists_relax, hm, if_pos hp]
        have hak : Armed s X.net.transitions[j] := by
          have : s.armed X.net.transitions[j] = true := by
            simp only [refPolicy, Bool.and_eq_true] at hk; exact hk.1.1.1
          exact (armed_iff s _).mpr this
        exact hν j hj hak
      · rw [if_neg hk]
        rw [if_neg hk] at hst
        by_cases hra : refPolicy.rearm X s X.net.transitions[i] d
            (fireNA s.m X.net.transitions[i].core d) X.net.transitions[j] = true
        · rw [if_pos hra]
          simp only [Option.getD_some, Nat.sub_self, Nat.cast_zero, zero_div]
          split <;> first | exact hnn j | exact le_refl _
        · rw [if_neg hra] at hst; exact absurd hst (by simp)
    · intro u hu' he hna
      have hst : ¬ (restampAll refPolicy X s X.net.transitions[i] d
          (fireNA s.m X.net.transitions[i].core d) u.core.name).isSome = true :=
        fun h => hna ⟨he, h⟩
      rw [stamp_after hD hu'] at hst
      by_cases hk : refPolicy.keep X s X.net.transitions[i] d
          (fireNA s.m X.net.transitions[i].core d) u = true
      · rw [if_pos hk] at hst
        have : s.armed u = true := by
          simp only [refPolicy, Bool.and_eq_true] at hk; exact hk.1.1.1
        exact absurd ((armed_iff s u).mpr this).2 hst
      · rw [if_neg hk] at hst
        by_cases hra : refPolicy.rearm X s X.net.transitions[i] d
            (fireNA s.m X.net.transitions[i].core d) u = true
        · rw [if_pos hra] at hst; exact absurd rfl hst
        · have he' : enabledNA (fireNA s.m X.net.transitions[i].core d) u.core = true := he
          simp only [refPolicy, he', Bool.true_and, Bool.or_eq_true, not_or] at hra
          obtain ⟨hna0, hw⟩ := hra
          have hw' : writesArc X.net.transitions[i] d u = false := by simpa using hw
          have hen0 : enabledNA s.m u.core = true := by rw [← enabled_frame hw']; exact he'
          exact hu u hu' hen0 fun ha0 => hna0 ((armed_iff s u).mp ha0)

/-- **J8: every run of the timed reference is covered by `TStep` on the relaxed image**: the
image with every latest bound dropped, from the restricted initial marking, with the restricted
marking and clocks at least the executor's elapsed times. Late delays, late firings within the
tolerance and reaps are all covered. -/
theorem ref_late_sim (hN : NamesIn ix X.net) (hD : NamesDistinct X) (hF : FixedFwdNet X.net)
    {m0 : N → Nat} {now0 : Nat} {s : TSt N} (h : RefReach X m0 now0 s) :
    ∃ ts, TReach (relax (flatTNet ix X)) (restrict ix m0) ts ∧ LateSim ix X s ts ∧
      UnarmedReapable X s := by
  induction h with
  | refl =>
    obtain ⟨h1, h2⟩ := late_init (ix := ix) hD m0 now0
    exact ⟨_, Relation.ReflTransGen.refl, h1, h2⟩
  | tail _ hstep ih =>
    obtain ⟨ts, hts, hsim, hu⟩ := ih
    obtain ⟨l, hR⟩ := hstep
    obtain ⟨ts', hstep', hsim', hu'⟩ := late_step hN hD hF hsim hu hR
    exact ⟨ts', hts.trans hstep', hsim', hu'⟩

/-- **J8 on the graph**: every state of every run of the timed reference has, restricted, the
marking of a well-formed class that the timed graph of the relaxed image reaches. -/
theorem ref_late_graph (hN : NamesIn ix X.net) (hD : NamesDistinct X) (hF : FixedFwdNet X.net)
    {co : List Nat → Option (List Nat)} (hco : Novel.TimedScg.CoWF co) {eps : ℚ} (heps : 0 ≤ eps)
    {m0 : N → Nat} {C0 : Cls} (h0 : initCls (relax (flatTNet ix X)) co eps (restrict ix m0) = some C0)
    {now0 : Nat} {s : TSt N} (h : RefReach X m0 now0 s) :
    ∃ C, Relation.ReflTransGen (Edge (relax (flatTNet ix X)) co eps) C0 C ∧
      C.m = restrict ix s.m ∧ ClsWF (relax (flatTNet ix X)) C := by
  obtain ⟨ts, hts, hsim, -⟩ := ref_late_sim hN hD hF h
  obtain ⟨C, hreach, hin, hwf, -⟩ :=
    timed_run_sound (timingWF_relax eftOf_flat_nonneg) hco heps h0 hts
  exact ⟨C, hreach, hin.1.symm.trans hsim.1, hwf⟩

/-- The executor rests with tokens: no transition of the net is armed while enabled (every
enabled one was reaped), the `enabled_count() == 0` break of the run loop. -/
def RefRests (X : TimedNet N) (s : TSt N) : Prop :=
  ∀ u ∈ X.net.transitions, Enabled u s.m → ¬ Armed s u

/-- **J8, where the executor rests**: the covering class of the relaxed graph holds only clocks
of reapable transitions. A reap-aware quiescence check must treat such a class as a place the
executor may stop ([VER-002] reap-aware quiescence, `Late.late_quiescence_sound` at the named
level). -/
theorem ref_rest_reapable (hN : NamesIn ix X.net) (hD : NamesDistinct X) (hF : FixedFwdNet X.net)
    {co : List Nat → Option (List Nat)} (hco : Novel.TimedScg.CoWF co) {eps : ℚ} (heps : 0 ≤ eps)
    {m0 : N → Nat} {C0 : Cls} (h0 : initCls (relax (flatTNet ix X)) co eps (restrict ix m0) = some C0)
    {now0 : Nat} {s : TSt N} (h : RefReach X m0 now0 s) (hq : RefRests X s) :
    ∃ C, Relation.ReflTransGen (Edge (relax (flatTNet ix X)) co eps) C0 C ∧
      C.m = restrict ix s.m ∧
      ∀ c ∈ C.cs, ∃ hc : c < X.net.transitions.length, Reapable X X.net.transitions[c] := by
  obtain ⟨ts, hts, hsim, hu⟩ := ref_late_sim hN hD hF h
  obtain ⟨C, hreach, hin, hwf, -⟩ :=
    timed_run_sound (timingWF_relax eftOf_flat_nonneg) hco heps h0 hts
  have hCm : C.m = restrict ix s.m := hin.1.symm.trans hsim.1
  refine ⟨C, hreach, hCm, fun c hc => ?_⟩
  have hen := (hwf.mem c).mp hc
  rw [en_relax] at hen
  have hl := en_flat_lt hen
  rw [hCm, en_flat hN hl] at hen
  exact ⟨hl, hu _ (List.getElem_mem hl) hen (hq _ (List.getElem_mem hl) hen)⟩

/-- `Timing.relaxLate` on every transition: the named net `reaping::relax_late` returns when
every transition with a latest bound is lifted. -/
def LateRelax (X : TimedNet N) : TimedNet N :=
  { X with timing := fun t => Timing.relaxLate true (X.timing t) }

/-- **The flat image of the lifted net is `relaxMax` of the flat image**: the graph Route B
builds (`Late.relaxLate_fromTimings`, at the named level). -/
theorem flatTNet_lateRelax : flatTNet ix (LateRelax X) = relaxMax (flatTNet ix X) := by
  unfold flatTNet relaxMax LateRelax
  rw [List.map_map]
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp, flatTT, mkT, eftT, lftT, Timing.relaxLate_earliest,
    Timing.relaxLate_latest, maxLft]
  rfl

/-- Dropping every latest bound of the lifted net is dropping them of the net. -/
theorem relax_lateRelax : relax (flatTNet ix (LateRelax X)) = relax (flatTNet ix X) := by
  rw [flatTNet_lateRelax, relax_relaxMax]

end Late

/-! ## 6. Worked examples

A J5 demonstration phase decided by a flat certificate (it is not a runtime route), the case
`Link` excluded (a transition without an output spec), and a net that shows the forward premise
is needed. -/

section Examples

variable [DecidableEq N]

/-- `FixedFwd` as a check. -/
def fixedFwdB (t : Trans N) : Bool :=
  match t.out with
  | none => true
  | some o => (fwdSrcs o).all fun src =>
      match nspecAt t.core src with
      | none => true
      | some s => !s.card.consumesAll

theorem fixedFwd_of_B {t : Trans N} (h : fixedFwdB t = true) : FixedFwd t := by
  intro o ho src hs s hspec
  unfold fixedFwdB at h
  rw [ho] at h
  have := List.all_eq_true.mp h src hs
  rw [hspec] at this
  simpa using this

/-- No row of any transition deposits into `p`. -/
def unfedB (net : Reference.Net N) (p : N) : Bool :=
  net.transitions.all fun t => (rowsN t).all fun r => !r.contains p

/-- A place no row deposits into never gains a token along flat rows. -/
theorem reachAD_unfed {rows : List (Transition × Deposit)} {k : PlaceId}
    (hk : ∀ tr ∈ rows, tr.2.count k = 0) {a0 a : AMarking} (h : ReachAD rows a0 a) :
    a k ≤ a0 k := by
  induction h with
  | refl => exact le_refl _
  | tail _ hs ih =>
    obtain ⟨tr, htr, -, rfl⟩ := hs
    rw [fireAD_eq_inter_add, hk tr htr, Nat.add_zero]
    exact (Novel.TimedScg.inter_le _ _ _).trans ih

/-- The index of the demonstration phase: every name the initial marking marks or the net uses. -/
def demoIndex (q : Query N) : PlaceIndex N :=
  flatIndex (q.m0.places ++ q.net.net.transitions.flatMap transNames)

/-- **A demonstration phase decided by a flat certificate** (J5): `PlaceBound(p, k)` is `Proven`
when every forward is fixed, no row deposits into `p` and the initial marking holds at most `k`
in `p`. It is not a runtime route. -/
def demoUnfedPhase : Phase N := fun _ q =>
  match q.prop with
  | .placeBound p k =>
    if q.net.net.transitions.all fixedFwdB && unfedB q.net.net p && decide (q.init p ≤ k) then
      .decided (.proven "unfed place") [] none
    else .aside "the place is fed"
  | _ => .aside "only PlaceBound"

/-- The demonstration phase keeps the flat contract: its `Proven` carries a flat certificate. -/
theorem demoUnfedPhase_flat : FlatPhaseSound refSafetyViol (demoUnfedPhase (N := N)) := by
  intro o q
  refine ⟨fun meth tr c h => ?_, fun tr h => ?_, fun why tr c h => ?_⟩
  · unfold demoUnfedPhase at h
    split at h
    · rename_i p k hp
      split at h
      · rename_i hc
        simp only [PhaseOut.decided.injEq, Verdict.proven.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨hfix, hunfed⟩, hle⟩ := hc
        have hN : NamesIn (demoIndex q) q.net.net := fun t ht n hn => by
          simp only [demoIndex, mem_flatIndex, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨t, ht, hn⟩
        refine ⟨by decide, demoIndex q, hN, fun t ht => fixedFwd_of_B (hfix t ht), ?_, ?_⟩
        · intro n hn
          have : n ∈ q.m0.places := (q.m0.count_ne_zero_iff n).mp hn
          simp only [demoIndex, mem_flatIndex, List.mem_append]
          exact Or.inl this
        · intro a ha
          rw [hp]
          show ¬ k < Novel.Seam.lift (demoIndex q) a p
          unfold Novel.Seam.lift
          split_ifs with hpi
          · have hk : ∀ tr ∈ flatNet (demoIndex q) (expandNet q.net.net),
                tr.2.count ((demoIndex q).idx p) = 0 := by
              intro tr htr
              obtain ⟨ft, hft, rfl⟩ := List.mem_map.mp htr
              obtain ⟨t, ht, r, hr, rfl⟩ := mem_expandNet.mp hft
              show (r.map (demoIndex q).idx).count ((demoIndex q).idx p) = 0
              rw [count_some (demoIndex q) (tin_row (hN t ht) hr).branch
                ((demoIndex q).name?_idx hpi)]
              have := List.all_eq_true.mp (List.all_eq_true.mp hunfed t ht) r hr
              have hnm : p ∉ r := by
                intro hm
                have : r.contains p = true := List.contains_iff_mem.mpr hm
                simp_all
              exact List.count_eq_zero_of_not_mem hnm
            have h1 := reachAD_unfed hk ha
            rw [restrict_idx _ _ hpi] at h1
            omega
          · omega
      · simp at h
    · simp at h
  · unfold demoUnfedPhase at h
    split at h
    · split at h <;> simp at h
    · simp at h
  · unfold demoUnfedPhase at h
    split at h
    · split at h <;> simp at h
    · simp at h

/-- **J5 end to end**: the demonstration phase keeps [VER-003]'s phase contract on the named net. -/
theorem demoUnfedPhase_sound : PhaseSound refSafetyViol (demoUnfedPhase (N := N)) :=
  demoUnfedPhase_flat.phaseSound

end Examples

/-- `go : p0 → p1` at `window(2, 4)`. -/
def exGo : Trans Nat :=
  { core := { name := "go", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1), reapable := true }

/-- `drain`: takes one token from `p2` and has no output spec, so it deposits nothing. -/
def exDrain : Trans Nat :=
  { core := { name := "drain", inputs := [⟨2, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The net `{go, drain}` over places `0, 1, 2`. -/
def exNet : Reference.Net Nat := { places := [0, 1, 2], transitions := [exGo, exDrain] }

/-- The query `PlaceBound(2, 1)` from `{p0: 1, p2: 1}`. -/
def exQuery : Query Nat :=
  { net := { net := exNet, timing := fun _ => .window 2 4, tol := 0 },
    prop := .placeBound 2 1, m0 := ⟨[(0, 1), (2, 1)], by decide, by decide⟩ }

/-- Example: in the net `go : p0 → p1`, `drain : p2 →` (no output spec), from `{p0: 1, p2: 1}`,
no transition deposits into `p2`, and `p2` starts with one token. The demonstration phase proves
`PlaceBound(p2, 1)` from that alone, and J5 makes the proof hold for every marking the named net
reaches. `drain` has no output spec, a transition the earlier flat link excluded; its one row is
empty. -/
theorem ex_demo_proven :
    demoUnfedPhase {} exQuery = .decided (.proven "unfed place") [] none ∧
      rowsN exDrain = [[]] :=
  ⟨rfl, rfl⟩

/-- Example: the proof of `ex_demo_proven` holds on the named net, so no marking reachable from
`{p0: 1, p2: 1}` holds two tokens in `p2`. -/
theorem ex_demo_bound :
    ∀ f, Reference.Reach exQuery.net.net exQuery.init f → ¬ 1 < f 2 :=
  ((demoUnfedPhase_sound {} exQuery).1 _ _ _ ex_demo_proven.1).2

/-- `t : all(p0) → timeout(forward(p0, p1))`: a forward from a drained input. -/
def exDrained : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .all⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.timeout (.forward 0 1)) }

/-- Example: `t` drains `p0` and its timeout forwards the whole batch to `p1`. From three tokens in
`p0` the timeout deposits three tokens in `p1`, a deposit no constant row of `t` holds (the rows
are `[p1]` twice). So a bridge that maps firings to rows needs every forward to draw from a
`One` / `Exactly` input (`FixedFwd`), which the routes require too (`drained_forward`). -/
theorem ex_drained_forward_escapes :
    Fires exDrained (fun p => if p = 0 then 3 else 0) [1, 1, 1]
        (fireNA (fun p => if p = 0 then 3 else 0) exDrained.core [1, 1, 1]) ∧
      [1, 1, 1] ∉ rowsN exDrained ∧ ¬ fixedFwdB exDrained := by
  refine ⟨⟨by decide, ⟨.timedOut 0, by decide⟩, rfl⟩, by decide, by decide⟩

theorem exGo_mem : exGo ∈ exNet.transitions := List.mem_cons_self

/-- The net `{go, drain}` with every transition at `window(2, 4)` and no tolerance. -/
def exX : TimedNet Nat := { net := exNet, timing := fun _ => .window 2 4, tol := 0 }

/-- One token in `p0`. -/
def exM0 : Nat → Nat := fun p => if p = 0 then 1 else 0

/-- The index over the declared places `0, 1, 2`. -/
def exIx : PlaceIndex Nat := flatIndex [0, 1, 2]

/-- The premises of the bridges hold of the example net. -/
theorem ex_premises : NamesIn exIx exX.net ∧ NamesDistinct exX ∧ FixedFwdNet exX.net :=
  ⟨by unfold NamesIn; decide, by unfold NamesDistinct; decide,
    fun t ht => fixedFwd_of_B (by revert t ht; decide)⟩

/-- Example: `go` (window 2 to 4 ms) is armed at time 0 with the token in `p0`. The executor
waits 3 ms, which keeps `go` within its latest bound of 4 ms, then fires `go`: the token is in
`p1`. Both steps are on time. -/
theorem ex_onTime_run : ∃ s, OnTimeReach exX exM0 0 s ∧ s.m 1 = 1 ∧ s.m 0 = 0 := by
  refine ⟨_, Relation.ReflTransGen.tail (Relation.ReflTransGen.single
    ⟨.delay 3, RefTStepW.delay _ _ 3, ?_⟩)
    ⟨.fire exGo [1], RefTStepW.fire _ _ exGo [1] _ exGo_mem
      ⟨?_, ⟨.action 0, rfl⟩, rfl⟩ ?_ ?_ ?_, trivial⟩, ?_, ?_⟩ <;> decide

/-- Example (J7): the on-time run of `ex_onTime_run` is a run of the graph's timed semantics on
the flat image: a `TStep` run from the restricted initial marking ends with the token in `p1`. -/
theorem ex_onTime_tstep :
    ∃ ts, TReach (flatTNet exIx exX) (restrict exIx exM0) ts ∧ ts.m (exIx.idx 1) = 1 := by
  obtain ⟨s, hs, h1, -⟩ := ex_onTime_run
  obtain ⟨ts, hts, hm⟩ := onTime_tReach ex_premises.1 ex_premises.2.1 ex_premises.2.2 hs
  refine ⟨ts, hts, ?_⟩
  rw [hm, restrict_idx _ _ (by decide)]
  exact h1

/-- Example (J8): a late executor waits 10 ms. That delay is a step of the timed reference but
not an on-time step, since `go` passes its latest bound of 4 ms. With no tolerance, `go` is then
expired and is reaped: the executor rests with the token stranded in `p0`, which no on-time run
does. Every clock that J8's covering class can hold belongs to a reapable transition. -/
theorem ex_late_rest :
    ¬ OnTimeStep RefTStep exX (TSt.init exX exM0 0) (.delay 10)
        { TSt.init exX exM0 0 with now := 10 } ∧
      ∃ s, RefReach exX exM0 0 s ∧ RefRests exX s ∧ s.m 0 = 1 := by
  refine ⟨fun h => absurd (h.2 exGo exGo_mem (by decide)) (by decide), ?_⟩
  refine ⟨_, Relation.ReflTransGen.tail (Relation.ReflTransGen.single
    ⟨.delay 10, RefTStepW.delay _ _ 10⟩) ⟨.reap exGo, RefTStepW.reap _ _ exGo exGo_mem ?_⟩,
    ?_, ?_⟩
  · decide
  · unfold RefRests; decide
  · decide

end Libpetri.Spec.Verifier.Bridges
