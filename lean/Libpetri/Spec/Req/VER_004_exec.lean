import Libpetri.Reference.ExecLink
import Libpetri.Spec.Req.VER_004

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# VER-004 block B: the executor's runs with actions in flight (`spec/07-verification.md`)

The third block of VER-004, beside `VER_004_timed` (kind A) and `VER_004_split` (kind F) in
`VER_004.lean`. It is the first statement that spans the executor and the verifier.

`VER_004_exec` is a predicate over a pair `(E, S)`: `E : XRel PlaceId T`, the executor relation
the EXEC, CONC and ENV blocks constrain (witness `RefExec`), and `S : SplitFn PlaceId`, the
in-flight split of `VER_004_split` (witness `Split.refSplit`). Its one line says: when the split
succeeds without the opt-out, every state a run of `E` reaches is covered by the split: the
counts of the state, with each action in flight of a transition the split leaves atomic completed
by one of its rows, are a marking the split net reaches, with the split actions in flight exactly
as in the executor. The split net is read as `Novel.InFlight.SStep` over the split list `S`
returns, gated by the strict stop of [EXEC-042].

The holds theorem (`VER_004_exec_reference`) chains the L5 count projection of
`Reference/ExecLink.lean` (`count_projection`: a `RefExec` run is an `InFlight.XStep` run, the
moved deposits of each firing pass completed at its end) with `InFlight.split_covers_executor`,
whose criterion `refSplit`'s split list meets: a transition `refSplit` leaves atomic has no output
place that a terminal marks or any transition tests by an inhibitor, a reset or a drain
(`ver004b_untested`, `ver004b_live`). It is proved in general: `VER_004_exec_of` derives block B
for every executor meeting the L5 agreement conjunct `CountAgrees` and every split meeting
`VER_004_split`, so the consistency theorem gets block B from those two.

Corollaries from the statement alone: `VER_004_exec_rest` (where nothing is in flight the
executor's counts are a split-net marking with nothing pending, the rest the run loop waits for,
ruling D13) and `VER_004_exec_safety` (a split-net `Proven` of an upward-closed marking property
holds at every executor state, actions in flight included).

Wrong models: the split that never splits (`ver004b_atomicSplit`, AC4's point: the executor marks
`bad` while `t` is in flight, which no atomic run does), the executor that ignores inhibitor
arcs (`ver004b_noInhExec`) and the executor that ignores the terminal stop of [EXEC-042]
(`ver004b_noStopExec`, which the strict-stop gate of the split net rejects).

The line reads only the split list `S` returns, never the verified net: a split that returns the
right list with a wrong net meets block B, and the F block `VER_004_split` rejects it (its line on
the split net pins the net). The two are conjoined in the consistency theorem. The worked example (`VER_004_exec_nonvacuous`) is the [VER-004]
witness net of `InFlight.inflight_witness` run on the reference executor.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Spec.Verifier (Options)
open Libpetri.Spec.Verifier.Split (SplitCfg splits isCompletion outs nonMonotone drainPlaces
  refSplit splitTimed)
open Libpetri.Reference.Link (toTransition)

/-! ## Vocabulary -/

/-- **The rows of a net** (per-run data of the L5 projection): every row is a transition of the
net with a deposit whose places are output places of that transition (in any branch, the
`Timeout` branch included). A failed action's empty row is one. -/
def ExecRows (net : Reference.Net PlaceId) (R : List Novel.InFlight.Row) : Prop :=
  ∀ r ∈ R, ∃ u ∈ net.transitions, r.1 = toTransition u.core ∧ ∀ p ∈ r.2, p ∈ outs u

/-- **No transition is exempt from the split by its shape**: no transition of the net is a
completion step (`Split.isCompletion`) or an environment step of the split configuration. The
executor runs a net of actions; completion steps and environment steps are what a verifier adds. -/
def SplitExemptFree (cfg : SplitCfg PlaceId) (net : Reference.Net PlaceId) : Prop :=
  ∀ u ∈ net.transitions, isCompletion cfg u = false ∧ u.core.name ∉ cfg.envTrans

/-- The split list as a test on transition names. -/
def splitTest (sp : List String) : String → Bool := fun n => decide (n ∈ sp)

/-! ## The block -/

requirement VER_004_exec
  id "VER-004"
  title "Untimed Over-Approximation (the executor's runs with actions in flight)"
  kind B
  scope "the executor's runs on a net the split accepts, read through the count projection L5 of RefExec (SHOULD; the shall sentence binds an implementation that offers verification)"
  source verbatim "spec/07-verification.md"
  quote "*While* `assumeAtomicFiring` is not set and the split succeeds, *where* no firing fails (no action fails, and output validation and the relay check reject no output or timeout outcome), no action publishes an output before it completes and no token is injected, a marking the executor reaches from the initial marking, with each action in flight of a transition that is not split completed with one of its outcomes, *shall* be reachable in the split net from the initial marking, with one token on `inflight:<t>` for each action of a split transition `t` in flight."
        "That is a sound over-approximation for all three."
  reading "For every executor relation E and split S, every executor configuration C, split configuration cfg, options o, rows R, initial marking M0, run of E from the initial state of M0 and completion ds:"
          "if the transition names of C are distinct, no transition of C is a completion step or an environment step of cfg, every terminal place of C is a terminal place of cfg, every row of R is a transition of C's net with a deposit among its output places, every transition has a row in R, o does not set assumeAtomicFiring, S returns the verified net and the split list sp, every commit, timeout deposit and fail of the run deposits a row of R (RowsCover: no publication, no injection), and ds completes each action in flight at the end of the run whose transition is not in sp with one row of it,"
          "then the split net over R with split set sp (InFlight.SStep, every step gated by the strict stop) reaches, from the counts of M0, the counts at the end of the run with ds deposited, with pending exactly the actions in flight whose transition is in sp (as a multiset)."
  assumes "The model is the pair (E, S). E : XRel PlaceId T is the executor relation the EXEC, CONC and ENV blocks constrain, read at flat place names (PlaceId) as the L5 conjunct CountAgrees is; the witness is RefExec. S : SplitFn PlaceId is the split of VER_004_split; the witness is Split.refSplit. The witness pair is (RefExec, refSplit) (VER_004_exec_reference, through VER_004_exec_of: block B holds of every E meeting the L5 conjunct CountAgrees and every S meeting VER_004_split): the L5 count projection (ExecLink count_projection: moving each in-pass deposit behind the last start of its pass makes a RefExec run an InFlight.XStep run with the same counts and the firings in flight pending) followed by InFlight.split_covers_executor, whose criterion refSplit's split list meets (ver004b_untested: an atomic transition's outputs are tested by no inhibitor, reset or drain; ver004b_live: it marks no terminal place)."
          "The split net of the line is the step relation InFlight.SStep over the rows R with split set sp: a transition outside sp fires atomically, one in sp starts (a token on inflight:<t>, the pending list) and later completes with a row, and the strict stop (NoTerm C, the terminal rewrite of EXEC-042) gates every step. The line reads only the split list sp that S returns, not the verified net Y: a split that returns the right list with a wrong net meets this line, and the F block VER_004_split rules it out (its line on the split net pins Y to splitTimed cfg sp X); the consistency theorem conjoins the two. That it is the named net splitTimed cfg sp X of VER_004_split read under Reference.Reach is an open link (the named lift, deferred): it needs every row to be an outcome of its transition at the marking it fires from (a forward reads the consumed count) and has no counterpart for a failed action, whose empty row SStep accepts and no named completion step deposits. So the line covers failed firings in the flat reading, which is more than the quoted sentence asks: the sentence excludes them ('no firing fails': no action fails, and output validation, the relay check of NU-054 and the Java and TypeScript timeout-outcome validation of RD-01 reject nothing), since a named split net has no step that consumes an atomic transition's inputs and deposits nothing. A firing whose action succeeds but whose outcome is rejected fails the same way as one whose action fails: it consumes its inputs and deposits nothing (EVT-008), which the flat line reads as the empty row. For an upward-closed property a failed firing only leaves fewer tokens on places tested monotonically, but a quiescence Proven need not hold of a run in which a firing failed (an open item for AC3 and AC4)."
          "The sentence's 'no action ... publishes an output before it completes' (ruling D28 (a), ctx.flush() in Rust and Python) and 'no token is injected' are the RowsCover hypothesis: a publish step and an inject step make it false, so a run with either is outside the line (InFlight.XStep has no counterpart for them; environment places are VER-006's closure, injections into the executor are ENV's and L8's). The rows are a per-run hypothesis, as OfferedEmission is for L2. ExecRows asks only that a row's places be output places of its transition (a write to an undeclared place fails even with output validation skipped, CONC-026 and CORE-063), not that the row be an outcome: a write of two tokens to a place its branch names once (IO-016 AC4) or a partial write under the CONC-026 skip is a row too, and the flat line covers it. The named split net deposits only outcomes, one token per place of a branch (IO-016), so the deferred named lift needs those runs excluded, as IO-016 excludes them from every analysis. 'Reaches from the initial marking' is a run from xinit M0 r0, the reference initial state."
          "'That is a sound over-approximation for all three.' (ruling D8 (b): whether a transition starts again while an earlier firing of it is in flight is implementation-defined, Cfg.reentrant) is the line for every C, Cfg.reentrant true (Rust, Python) and false (Java, TypeScript) alike: InFlight.SStep lets a split transition start again with inflight:<t> marked, and XStep's pending list is a multiset. The CONC-002 report note and AC8 are report text (kind Q), as VER_004_split's assumes say."
          "Hypotheses that are not in the sentence, and why. Distinct transition names (ruling D10) make the rows' names unique, premise 1 of InFlight. SplitExemptFree: Split.isCompletion and cfg.envTrans exempt a transition from the split by its shape whatever its outputs; an executor net whose own transition looked like a completion step (named complete:<x>, one input one(inflight:<x>)) or was listed as an environment step would keep an action's gap the split does not model, so the line is stated for nets without them (an open item of wave W11). Every terminal place of C counts as a terminal of cfg: the split reads the terminals it is given."
          "AC4 is the line with VER-003's Proven line: a Proven of an upward-closed property on the split net holds at every executor state, actions in flight included (VER_004_exec_safety), and a quiescence Proven covers the executor's rests, where nothing is in flight (VER_004_exec_rest: the run loop waits for its actions in flight before it rests, ruling D13). AC4's example (the AC4 inhibitor net, the executor marks the inhibited output while t is in flight) is VER_004_exec_nonvacuous on the inhibitor net of InFlight.inflight_witness, and ver004b_atomicSplit shows the atomic net does not cover it (AC4's 'Disable the split and confirm each test fails'). That a Violated is not a false alarm is not claimed (completeness, VER-003 and VER-023). The test derivation's AC4 clause (run each net on both executors with an action that sleeps) is this example."
          "Not in the model: ν firings (RefExec has no ν kernel; a matched firing is a count firing of its transition (NuRestrictsTo), so the line reads it as one, and the split refuses a ν-join or a coloured write it would split, as the VER-004 refusal sentence says), timing (InFlight.SStep is untimed; that the timed executor's rests are reap-quiescent is VER_004_timed and ExecLink L6), priorities (the conflict-priority demand of NU-052 only adds split transitions, which the line allows: split_covers_executor holds for every split set meeting the criterion), and the report notes (kind N, Q)."
  signoff "pending"
  statement : ∀ {T : Type}, XRel PlaceId T → SplitFn PlaceId → Prop :=
    fun {T} E S =>
      ∀ (C : Cfg PlaceId T) (cfg : SplitCfg PlaceId) (o : Options) (Y : TimedNet PlaceId)
        (sp : List String) (R : List Novel.InFlight.Row) (M0 : QMarking PlaceId T) (r0 : Nat)
        (tr : List (XStep PlaceId T)) (ds : List Novel.InFlight.Row),
        NamesDistinct C.X → SplitExemptFree cfg C.X.net → (∀ p ∈ C.terminals, p ∈ cfg.terminals) →
        ExecRows C.X.net R → (∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R) →
        o.assumeAtomicFiring = false → S cfg o C.X = .ok (Y, sp) →
        XRun E C (xinit M0 r0) tr → (∀ y ∈ tr, RowsCover R y) →
        Novel.InFlight.Completes R
          ((flNames (XRun.last (xinit M0 r0) tr)).filter fun n => !splitTest sp n) ds →
        ∃ pend, pend.Perm ((flNames (XRun.last (xinit M0 r0) tr)).filter (splitTest sp)) ∧
          Novel.InFlight.SReach R (splitTest sp) (NoTerm C) (qCount M0)
            ⟨Novel.InFlight.addAll (qCount (XRun.last (xinit M0 r0) tr).M) ds, pend⟩

/- The pinned readable form of block B of VER-004: a change to the formula shows up as a diff
here. -/
/--
info: def Libpetri.Spec.VER_004_exec : {T : Type} → XRel PlaceId T → SplitFn PlaceId → Prop :=
fun {T} E S =>
  ∀ (C : Cfg PlaceId T) (cfg : SplitCfg PlaceId) (o : Options) (Y : TimedNet PlaceId) (sp : List String)
    (R : List Novel.InFlight.Row) (M0 : QMarking PlaceId T) (r0 : ℕ) (tr : List (XStep PlaceId T))
    (ds : List Novel.InFlight.Row),
    NamesDistinct C.X →
      SplitExemptFree cfg C.X.net →
        (∀ p ∈ C.terminals, p ∈ cfg.terminals) →
          ExecRows C.X.net R →
            (∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R) →
              o.assumeAtomicFiring = false →
                S cfg o C.X = Except.ok (Y, sp) →
                  XRun E C (xinit M0 r0) tr →
                    (∀ y ∈ tr, RowsCover R y) →
                      Novel.InFlight.Completes R
                          (List.filter (fun n => !splitTest sp n) (flNames (XRun.last (xinit M0 r0) tr))) ds →
                        ∃ pend,
                          pend.Perm (List.filter (splitTest sp) (flNames (XRun.last (xinit M0 r0) tr))) ∧
                            Novel.InFlight.SReach R (splitTest sp) (NoTerm C) (qCount M0)
                              { a := Novel.InFlight.addAll (qCount (XRun.last (xinit M0 r0) tr).M) ds, pend := pend }
-/
#guard_msgs in #print VER_004_exec

/-! ## The reference -/

section Ref

/-- Distinct transition names make the names of a net's rows unique (premise 1 of `InFlight`). -/
theorem ver004b_namesUnique {net : Reference.Net PlaceId} {R : List Novel.InFlight.Row}
    (hD : (net.transitions.map (·.core.name)).Nodup) (hR : ExecRows net R) :
    Novel.InFlight.NamesUnique R := by
  intro r hr r' hr' hn
  obtain ⟨u, hu, hru, -⟩ := hR r hr
  obtain ⟨u', hu', hru', -⟩ := hR r' hr'
  rw [hru, hru'] at hn ⊢
  have : u = u' := List.inj_on_of_nodup_map hD hu hu' hn
  rw [this]

/-- A transition the split leaves atomic has no output place that is tested non-monotonically. -/
theorem ver004b_outs_free {cfg : SplitCfg PlaceId} {net : Reference.Net PlaceId}
    {u : Reference.Trans PlaceId} (hex : SplitExemptFree cfg net) (hu : u ∈ net.transitions)
    (hn : u.core.name ∉ splits cfg net) : ∀ p ∈ outs u, p ∉ nonMonotone cfg net := by
  intro p hp hm
  exact hn ((Verifier.Split.mem_splits cfg net _).mpr
    ⟨u, hu, rfl, (hex u hu).1, (hex u hu).2, Or.inr ⟨p, hp, Or.inl hm⟩⟩)

/-- **The criterion holds of an atomic deposit** (`InFlight.Untested`): a deposit into places
that are not tested non-monotonically is tested by no row of the net with an inhibitor, a reset or
a drain. -/
theorem ver004b_untested {cfg : SplitCfg PlaceId} {net : Reference.Net PlaceId}
    {R : List Novel.InFlight.Row} (hR : ExecRows net R) {d : List PlaceId}
    (hd : ∀ p ∈ d, p ∉ nonMonotone cfg net) : Novel.InFlight.Untested R d := by
  intro w hw p hp
  obtain ⟨w', hw', hwt, -⟩ := hR w hw
  have hnm := hd p (List.count_pos_iff.mp hp)
  have hin : ∀ q ∈ w'.core.inhibitors ++ w'.core.resets ++ drainPlaces w',
      q ∈ nonMonotone cfg net := fun q hq =>
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨w', hw', hq⟩)
  rw [hwt]
  refine ⟨fun hi => hnm (hin p (by simp [toTransition] at hi; simp [hi])), ?_, ?_⟩
  · cases hc : (toTransition w'.core).resets.contains p with
    | false => rfl
    | true =>
      exfalso
      have : p ∈ w'.core.resets := by simpa [toTransition] using hc
      exact hnm (hin p (by simp [this]))
  · unfold consumeAllAt
    rw [Link.specAt_toTransition]
    cases hs : nspecAt w'.core p with
    | none => rfl
    | some s =>
      simp only [Option.map_some, Link.toInSpec]
      cases hca : s.card.consumesAll with
      | false => rfl
      | true =>
        exfalso
        have hmem : s ∈ w'.core.inputs := List.mem_of_find?_eq_some hs
        have hpl : s.place = p := by simpa using List.find?_some hs
        apply hnm (hin p _)
        refine List.mem_append_right _ (List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hmem, hca⟩, hpl⟩)

/-- **An atomic deposit keeps the strict stop**: a deposit into no terminal place of `cfg`, which
holds every terminal of `C`, marks no terminal of `C`. -/
theorem ver004b_live {T : Type} {C : Cfg PlaceId T} {cfg : SplitCfg PlaceId}
    {net : Reference.Net PlaceId} (hterm : ∀ p ∈ C.terminals, p ∈ cfg.terminals)
    {d : List PlaceId} (hd : ∀ p ∈ d, p ∉ nonMonotone cfg net) {a : AMarking}
    (ha : NoTerm C a) : NoTerm C (Novel.InFlight.addD a d) := by
  intro τ hτ
  have h0 : d.count τ = 0 :=
    List.count_eq_zero.mpr fun hm => hd τ hm (List.mem_append_left _ (hterm τ hτ))
  simp [Novel.InFlight.addD, ha τ hτ, h0]

end Ref

/-- **A split that meets the split block splits exactly `splits`** whenever it succeeds without
the opt-out (`VER_004_split` lines 2 to 4: nothing to split, a refusal, the split net). -/
theorem ver004b_split_sp {S : SplitFn PlaceId} {P : SplitPlanFn PlaceId}
    (h : VER_004_split S P) {cfg : SplitCfg PlaceId} {o : Options} {X Y : TimedNet PlaceId}
    {sp : List String} (hat : o.assumeAtomicFiring = false) (hS : S cfg o X = .ok (Y, sp)) :
    sp = splits cfg X.net := by
  by_cases hnil : splits cfg X.net = []
  · rw [h.2.1 cfg o X hat hnil] at hS
    simp only [Except.ok.injEq, Prod.mk.injEq] at hS
    rw [hnil, ← hS.2]
  · cases hr : ver004FirstRefused cfg X.net (splits cfg X.net) with
    | some t =>
      obtain ⟨e, he, -⟩ := h.2.2.1 cfg o X t hat hr
      rw [he] at hS
      exact absurd hS (by simp)
    | none =>
      rw [h.2.2.2.1 cfg o X hat hnil hr] at hS
      simp only [Except.ok.injEq, Prod.mk.injEq] at hS
      exact hS.2.symm

/-- **Block B follows from the L5 conjunct and the split block.** Every executor that meets the
L5 agreement conjunct `CountAgrees` (its runs are `InFlight.XStep` runs by their counts) and every
split that meets `VER_004_split` (with any plan) meet block B: the split's list is `splits`, whose
atomic transitions meet the criterion of `InFlight.split_covers_executor`. So the consistency
theorem gets block B from the two. -/
theorem VER_004_exec_of {T : Type} {E : XRel PlaceId T} {S : SplitFn PlaceId}
    {P : SplitPlanFn PlaceId} (hE : CountAgrees E) (hSP : VER_004_split S P) :
    VER_004_exec E S := by
  intro C cfg o Y sp R M0 r0 tr ds hD hex hterm hrows hR hat hS ht hc hds
  have hsp : sp = splits cfg C.X.net := ver004b_split_sp hSP hat hS
  obtain ⟨pend, hx, hpp⟩ := hE C R hR M0 r0 tr ht hc
  have hfree : ∀ r ∈ R, splitTest sp r.1.name = false →
      ∀ p ∈ r.2, p ∉ nonMonotone cfg C.X.net := by
    intro r hr hn p hp
    obtain ⟨u, hu, hru, hout⟩ := hrows r hr
    have hn' : u.core.name ∉ splits cfg C.X.net := by
      rw [← hsp]
      have : r.1.name = u.core.name := by rw [hru]; rfl
      simpa [splitTest, this] using hn
    exact ver004b_outs_free hex hu hn' p (hout p hp)
  have hcrit : ∀ r ∈ R, splitTest sp r.1.name = false → Novel.InFlight.Untested R r.2 :=
    fun r hr hn => ver004b_untested hrows (hfree r hr hn)
  have hlive : ∀ r ∈ R, splitTest sp r.1.name = false →
      ∀ a, NoTerm C a → NoTerm C (Novel.InFlight.addD a r.2) :=
    fun r hr hn _ ha => ver004b_live hterm (hfree r hr hn) ha
  have hds' : Novel.InFlight.Completes R (pend.filter fun n => !splitTest sp n) ds :=
    ⟨hds.1.trans (hpp.filter _).symm, hds.2⟩
  exact ⟨_, hpp.filter _, Novel.InFlight.split_covers_executor
    (ver004b_namesUnique hD hrows) hcrit hlive hx ds hds'⟩

/-- **The reference executor and the reference split meet block B of VER-004.** Take
`t : p → q` with an asynchronous action and `u : r, inhibitor p, inhibitor q → bad`, from
`{p, r}`. The executor starts `t`, which empties `p` while `q` is still unmarked, and then fires
`u`, so it marks `bad` while `t`'s action still runs. The reference split splits `t`, because an
inhibitor tests its output `q`, and leaves `u` atomic. The split net reaches the same counts, with
one token on `inflight:t` for the action in flight. The same holds for every run of the reference
executor on every net the split accepts. -/
@[evidence holds VER_004_exec]
theorem VER_004_exec_reference {T : Type} :
    VER_004_exec (RefExec (N := PlaceId) (T := T)) (refSplit (K := PlaceId)) :=
  VER_004_exec_of countAgrees_ref (VER_004_split_reference (K := PlaceId))

/-! ## Consequences of the statement -/

/-- **A rest is a split-net marking with nothing pending** ([VER-004] AC4 at a rest, ruling
D13), from the statement alone: where nothing is in flight at the end of a run, the executor's
counts are a marking the split net reaches with no in-flight token, so a quiescence `Proven` of
the split net covers them. -/
theorem VER_004_exec_rest {T : Type} {E : XRel PlaceId T} {S : SplitFn PlaceId}
    (h : VER_004_exec E S) {C : Cfg PlaceId T} {cfg : SplitCfg PlaceId} {o : Options}
    {Y : TimedNet PlaceId} {sp : List String} {R : List Novel.InFlight.Row}
    {M0 : QMarking PlaceId T} {r0 : Nat} {tr : List (XStep PlaceId T)}
    (hD : NamesDistinct C.X) (hex : SplitExemptFree cfg C.X.net)
    (hterm : ∀ p ∈ C.terminals, p ∈ cfg.terminals) (hrows : ExecRows C.X.net R)
    (hR : ∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R)
    (hat : o.assumeAtomicFiring = false) (hS : S cfg o C.X = .ok (Y, sp))
    (ht : XRun E C (xinit M0 r0) tr) (hc : ∀ y ∈ tr, RowsCover R y)
    (hfl : (XRun.last (xinit M0 r0) tr).fl = []) :
    Novel.InFlight.SReach R (splitTest sp) (NoTerm C) (qCount M0)
      ⟨qCount (XRun.last (xinit M0 r0) tr).M, []⟩ := by
  have hn : flNames (XRun.last (xinit M0 r0) tr) = [] := by simp [flNames, hfl]
  obtain ⟨pend, hpp, hx⟩ := h C cfg o Y sp R M0 r0 tr [] hD hex hterm hrows hR hat hS ht hc
    ⟨by simp [hn], fun _ h => absurd h List.not_mem_nil⟩
  rw [hn, List.filter_nil, List.perm_nil] at hpp
  rw [hpp, Novel.InFlight.addAll_nil] at hx
  exact hx

/-- **A safety `Proven` of the split net holds at every executor state** ([VER-004] AC4), from
the statement alone: if the split net never reaches a marking with an upward-closed property
`bad`, no executor state has it, an action in flight or not. -/
theorem VER_004_exec_safety {T : Type} {E : XRel PlaceId T} {S : SplitFn PlaceId}
    (h : VER_004_exec E S) {C : Cfg PlaceId T} {cfg : SplitCfg PlaceId} {o : Options}
    {Y : TimedNet PlaceId} {sp : List String} {R : List Novel.InFlight.Row}
    {M0 : QMarking PlaceId T} {r0 : Nat} {tr : List (XStep PlaceId T)}
    {ds : List Novel.InFlight.Row}
    (hD : NamesDistinct C.X) (hex : SplitExemptFree cfg C.X.net)
    (hterm : ∀ p ∈ C.terminals, p ∈ cfg.terminals) (hrows : ExecRows C.X.net R)
    (hR : ∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R)
    (hat : o.assumeAtomicFiring = false) (hS : S cfg o C.X = .ok (Y, sp))
    (ht : XRun E C (xinit M0 r0) tr) (hc : ∀ y ∈ tr, RowsCover R y)
    (hds : Novel.InFlight.Completes R
      ((flNames (XRun.last (xinit M0 r0) tr)).filter fun n => !splitTest sp n) ds)
    {bad : AMarking → Prop} (hup : Novel.InFlight.UpClosed bad)
    (hproven : ∀ x, Novel.InFlight.SReach R (splitTest sp) (NoTerm C) (qCount M0) x → ¬ bad x.a) :
    ¬ bad (qCount (XRun.last (xinit M0 r0) tr).M) := by
  intro hb
  obtain ⟨pend, -, hx⟩ := h C cfg o Y sp R M0 r0 tr ds hD hex hterm hrows hR hat hS ht hc hds
  exact hproven _ hx (hup _ _ (Novel.InFlight.le_addAll _ ds) hb)

/-! ## The worked example: the inhibitor net of `InFlight.inflight_witness`

Places `p = 0`, `q = 1`, `r = 2`, `bad = 3`. `t : p → q` has an asynchronous action; `u : r,
inhibitor p, inhibitor q → bad`. From `{p, r}` the executor starts `t` (its token leaves `p`, and
`q` is not marked yet), and in the next cycle `u` is enabled and fires: `bad` is marked while `t`
is in flight. -/

/-- `t : p → q`. -/
def ver004b_t : Reference.Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 1) }

/-- `u : r, inhibitor p, inhibitor q → bad`. -/
def ver004b_u : Reference.Trans Nat :=
  { core := { name := "u", inputs := [⟨2, .one⟩], inhibitors := [0, 1], reads := [],
              resets := [] },
    out := some (.place 3) }

/-- The executor configuration: both transitions immediate, no terminal, no environment place,
validation skipped (every emission of the example is valid anyway). -/
def ver004b_C : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3], transitions := [ver004b_t, ver004b_u] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- The initial marking `{p, r}`. -/
def ver004b_M : QMarking Nat Nat := fun p => if p = 0 ∨ p = 2 then [1] else []

/-- From the start of a cycle to its termination test. -/
def ver004b_toTest : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- The first cycle starts `t` asynchronously (firing `0`); in the second, `u` starts
synchronously (firing `1`), writes `7` into `bad` and returns. -/
def ver004b_pre : List (XLbl Nat Nat) :=
  ver004b_toTest ++ [.begin, .start "t" false, .endPass] ++ ver004b_toTest ++
    [.begin, .start "u" true, .write 1 3 7, .ret 1 true]

/-- The run: `u`'s completion is deposited inside its pass. -/
def ver004b_labels : List (XLbl Nat Nat) := ver004b_pre ++ [.commit 1]

/-- The rows: `t` deposits `q`, `u` deposits `bad`. -/
def ver004b_R : List Novel.InFlight.Row :=
  [(toTransition ver004b_t.core, [1]), (toTransition ver004b_u.core, [3])]

/-- Place names of the example; `inflight:t` is place `10`. -/
def ver004b_render : Nat → String
  | 0 => "p" | 1 => "q" | 2 => "r" | 3 => "bad" | 10 => "inflight:t" | _ => "x"

/-- The split configuration: `inflight:<t>` is place `10`, nothing else. -/
def ver004b_cfg : SplitCfg Nat := { inflight := fun _ => 10, render := ver004b_render }

/-- A decided trace that ends with one more label is a trace of the rest followed by one step. -/
theorem ver004b_xtrace_snoc {T : Type} {C : Cfg PlaceId T} {l : XLbl PlaceId T} :
    ∀ {s : XSt PlaceId T} {ls : List (XLbl PlaceId T)} {tr : List (XStep PlaceId T)},
      xtrace C s (ls ++ [l]) = some tr →
      ∃ tr1 s1 s2, tr = tr1 ++ [(s1, l, s2)] ∧ xtrace C s ls = some tr1 ∧ xrun C s ls = some s1
  | s, [], tr, h => by
    simp only [List.nil_append, xtrace] at h
    cases hs : xstep C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some, Option.map_some, Option.some.injEq] at h
      exact ⟨[], s, s', by rw [← h]; rfl, rfl, rfl⟩
  | s, l0 :: ls, tr, h => by
    simp only [List.cons_append, xtrace] at h
    cases hs : xstep C s l0 with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : xtrace C s' (ls ++ [l]) with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        obtain ⟨tr1, s1, s2, rfl, h1, h2⟩ := ver004b_xtrace_snoc ht
        refine ⟨(s, l0, s') :: tr1, s1, s2, by rw [← h]; rfl, ?_, ?_⟩
        · simp [xtrace, hs, h1]
        · simp [xrun, hs, h2]

set_option maxRecDepth 100000 in
/-- The firings in flight before `u`'s completion: `t`, not returned, and `u`, returned with the
token `7` for `bad`. -/
theorem ver004b_pre_fl :
    (xrun ver004b_C (xinit ver004b_M 0) ver004b_pre).map
      (fun s => s.fl.map (fun f => (f.id, f.t, f.out))) =
      some [(0, ver004b_t, none), (1, ver004b_u, some (.ok [(3, 7)]))] := by rfl

/-- **The example run.** It is a trace of the reference executor, its completion deposits `u`'s
row, and it ends with `bad` marked, `p`, `q` and `r` empty and `t` in flight. -/
theorem ver004b_run :
    ∃ tr, xtrace ver004b_C (xinit ver004b_M 0) ver004b_labels = some tr ∧
      (∀ y ∈ tr, RowsCover ver004b_R y) ∧
      flNames (XRun.last (xinit ver004b_M 0) tr) = ["t"] ∧
      qCount (XRun.last (xinit ver004b_M 0) tr).M 0 = 0 ∧
      qCount (XRun.last (xinit ver004b_M 0) tr).M 1 = 0 ∧
      qCount (XRun.last (xinit ver004b_M 0) tr).M 3 = 1 := by
  have h1 : (xtrace ver004b_C (xinit ver004b_M 0) ver004b_labels).isSome = true := by decide
  obtain ⟨tr, ht⟩ := Option.isSome_iff_exists.mp h1
  have hE : ((xrun ver004b_C (xinit ver004b_M 0) ver004b_labels).map fun s =>
      (s.fl.map (·.t.core.name), qCount s.M 0, qCount s.M 1, qCount s.M 3)) =
      some (["t"], 0, 0, 1) := by decide
  rw [xtrace_last ht] at hE
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hE
  obtain ⟨hn, h0, h1', h3⟩ := hE
  refine ⟨tr, ht, ?_, hn, h0, h1', h3⟩
  obtain ⟨tr1, s1, s2, htr, htr1, hs1⟩ := ver004b_xtrace_snoc (l := .commit 1) ht
  have hfl := ver004b_pre_fl
  rw [hs1, Option.map_some, Option.some.injEq] at hfl
  intro y hy
  rw [htr] at hy
  rcases List.mem_append.mp hy with hy | hy
  · have hl : y.2.1 ∈ ver004b_pre := by
      rw [← xtrace_labels htr1]; exact List.mem_map_of_mem hy
    unfold RowsCover
    revert hl
    generalize y.2.1 = l
    intro hl
    cases l <;> simp_all [ver004b_pre, ver004b_toTest]
  · rw [List.mem_singleton] at hy
    subst hy
    intro f hf hfi e he
    have hm : (f.id, f.t, f.out) ∈ s1.fl.map (fun f => (f.id, f.t, f.out)) :=
      List.mem_map_of_mem hf
    rw [hfl] at hm
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨h0, -, -⟩ | ⟨-, hft, hfo⟩
    · simp [hfi] at h0
    · rw [hfo] at he
      simp only [Option.some.injEq, Outcome.ok.injEq, reduceCtorEq, or_false] at he
      subst he
      rw [hft]
      simp [ver004b_R]

/-- The premises of the line that read the net and the split configuration hold of the
example. -/
theorem ver004b_premises :
    NamesDistinct ver004b_C.X ∧ SplitExemptFree ver004b_cfg ver004b_C.X.net ∧
      (∀ p ∈ ver004b_C.terminals, p ∈ ver004b_cfg.terminals) ∧
      ExecRows ver004b_C.X.net ver004b_R ∧
      (∀ u ∈ ver004b_C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ ver004b_R) := by
  refine ⟨by unfold NamesDistinct; decide, ?_, fun _ h => absurd h List.not_mem_nil, ?_, ?_⟩
  · intro u hu
    simp only [ver004b_C, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> exact ⟨by decide, by simp [ver004b_cfg]⟩
  · intro r hr
    simp only [ver004b_R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ver004b_t, by simp [ver004b_C], rfl, by simp [outs, ver004b_t, Verifier.outPlaces]⟩
    · exact ⟨ver004b_u, by simp [ver004b_C], rfl, by simp [outs, ver004b_u, Verifier.outPlaces]⟩
  · intro u hu
    simp only [ver004b_C, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact ⟨[1], by simp [ver004b_R]⟩
    · exact ⟨[3], by simp [ver004b_R]⟩

/-- The split of the example: `u` inhibits `q`, an output of `t`, so `t` splits; `bad` is tested
by nothing, so `u` stays atomic. -/
theorem ver004b_split :
    refSplit ver004b_cfg {} ver004b_C.X = .ok (splitTimed ver004b_cfg ["t"] ver004b_C.X, ["t"]) :=
  rfl

/-- ✓ **AC4, the executor marks `bad` with `t` in flight, and the split net does too.** On
`t : p → q` with an asynchronous action and `u : r, inhibitor p, inhibitor q → bad`, from
`{p, r}`, the reference executor starts `t`, which empties `p` before `q` is marked, then fires
`u`: `bad` is marked while `t`'s action still runs. The reference split splits `t` (an inhibitor
tests its output `q`) and leaves `u` atomic, and the split net reaches the same counts with one
token on `inflight:t`, `t`'s action in flight. -/
@[evidence nonvacuous VER_004_exec]
theorem VER_004_exec_nonvacuous :
    ∃ tr, XRun RefExec ver004b_C (xinit ver004b_M 0) tr ∧ (∀ y ∈ tr, RowsCover ver004b_R y) ∧
      refSplit ver004b_cfg {} ver004b_C.X =
        .ok (splitTimed ver004b_cfg ["t"] ver004b_C.X, ["t"]) ∧
      flNames (XRun.last (xinit ver004b_M 0) tr) = ["t"] ∧
      qCount (XRun.last (xinit ver004b_M 0) tr).M 3 = 1 ∧
      Novel.InFlight.SReach ver004b_R (splitTest ["t"]) (NoTerm ver004b_C) (qCount ver004b_M)
        ⟨qCount (XRun.last (xinit ver004b_M 0) tr).M, ["t"]⟩ := by
  obtain ⟨tr, ht, hc, hn, -, -, h3⟩ := ver004b_run
  obtain ⟨hD, hex, hterm, hrows, hR⟩ := ver004b_premises
  refine ⟨tr, xtrace_run ht, hc, ver004b_split, hn, h3, ?_⟩
  obtain ⟨pend, hpp, hx⟩ := VER_004_exec_reference ver004b_C ver004b_cfg {} _ ["t"] ver004b_R
    ver004b_M 0 tr [] hD hex hterm hrows hR rfl ver004b_split (xtrace_run ht) hc
    ⟨by simp [hn, splitTest], fun _ h => absurd h List.not_mem_nil⟩
  rw [hn] at hpp
  have hpe : pend = ["t"] := by
    have : (List.filter (splitTest ["t"]) ["t"]) = ["t"] := by decide
    rw [this] at hpp
    exact List.perm_singleton.mp hpp
  rw [hpe, Novel.InFlight.addAll_nil] at hx
  exact hx

/-! ## Violations -/

/-- With nothing split, the split net is the atomic net: from `{p, r}` it never marks `bad`,
since `t` puts `p`'s token on `q` in the same step and `u` needs both empty. -/
theorem ver004b_atomic_never :
    ∀ x, Novel.InFlight.SReach ver004b_R (splitTest []) (NoTerm ver004b_C) (qCount ver004b_M) x →
      x.a 0 + x.a 1 = 1 ∧ x.a 3 = 0 ∧ x.pend = [] := by
  intro x hx
  induction hx with
  | refl => exact ⟨by decide, by decide, rfl⟩
  | @tail y z _ hst ih =>
    obtain ⟨h01, h3, hp⟩ := ih
    cases hst with
    | atomic r hr _ _ hen =>
      simp only [ver004b_R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [enabledA_toTransition] at hen
        have hen0 : 1 ≤ y.a 0 := by
          simp only [enabledNA, ver004b_t, Bool.and_eq_true, List.all_eq_true,
            decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hen
          simpa [Card.required] using hen.1.1
        refine ⟨?_, ?_, hp⟩ <;>
          simp [Novel.ForwardDeposit.fireAD, toTransition, ver004b_t, consumeAllAt, pre, specAt,
            Link.toInSpec, Card.consumesAll, Card.required] <;> omega
      · exfalso
        rw [enabledA_toTransition] at hen
        simp only [enabledNA, ver004b_u, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
          beq_iff_eq, List.mem_cons, List.not_mem_nil, or_false] at hen
        have := hen.1.2 0 (Or.inl rfl)
        have := hen.1.2 1 (Or.inr rfl)
        omega
    | start r _ hsp => simp [splitTest] at hsp
    | complete r _ _ hp' => rw [hp] at hp'; exact absurd hp' List.not_mem_nil

/-- The split that never splits: the verified net is always the net itself. -/
def ver004b_atomicSplit : SplitFn PlaceId := fun _ _ X => .ok (X, [])

/-- ✗ **A split that never splits does not cover the executor** ([VER-004] AC4, "Disable the
split and confirm each test fails"). On the example the executor marks `bad` with `t` in flight;
completing `t` gives `{q, bad}`, and the atomic net never marks `bad`. -/
@[evidence forbids VER_004_exec]
theorem VER_004_exec_forbids_atomicSplit :
    ¬ VER_004_exec (RefExec (N := PlaceId) (T := Nat)) ver004b_atomicSplit := by
  intro h
  obtain ⟨tr, ht, hc, hn, -, -, h3⟩ := ver004b_run
  obtain ⟨hD, hex, hterm, hrows, hR⟩ := ver004b_premises
  obtain ⟨pend, -, hx⟩ := h ver004b_C ver004b_cfg {} _ [] ver004b_R ver004b_M 0 tr
    [(toTransition ver004b_t.core, [1])] hD hex hterm hrows hR rfl rfl (xtrace_run ht) hc
    ⟨by simp [hn, splitTest, toTransition, ver004b_t], by simp [ver004b_R]⟩
  have := (ver004b_atomic_never _ hx).2.1
  simp [Novel.InFlight.addAll, h3] at this

/-! ### An executor that ignores inhibitor arcs -/

/-- A transition with its inhibitor arcs dropped. -/
def ver004b_dropInhT (t : Reference.Trans PlaceId) : Reference.Trans PlaceId :=
  { t with core := { t.core with inhibitors := [] } }

/-- A net with every inhibitor arc dropped. -/
def ver004b_dropInhN (net : Reference.Net PlaceId) : Reference.Net PlaceId :=
  { net with transitions := net.transitions.map ver004b_dropInhT }

/-- The configuration with every inhibitor arc dropped. -/
def ver004b_dropInh {T : Type} (C : Cfg PlaceId T) : Cfg PlaceId T :=
  { C with X := { C.X with net := ver004b_dropInhN C.X.net } }

/-- An executor that ignores inhibitor arcs: it runs as the reference does on the net without
them. -/
def ver004b_noInhExec : XRel PlaceId Nat := fun C => RefExec (ver004b_dropInh C)

/-- A run of the reference on the net without inhibitors is a run of `ver004b_noInhExec`. -/
theorem ver004b_noInh_run {C : Cfg PlaceId Nat} :
    ∀ {s : XSt PlaceId Nat} {tr : List (XStep PlaceId Nat)},
      XRun RefExec (ver004b_dropInh C) s tr → XRun ver004b_noInhExec C s tr
  | _, [], _ => trivial
  | _, _ :: _, h => ⟨h.1, h.2.1, ver004b_noInh_run h.2.2⟩

/-- `v : r, inhibitor p → bad`. -/
def ver004b_v : Reference.Trans Nat :=
  { core := { name := "v", inputs := [⟨2, .one⟩], inhibitors := [0], reads := [], resets := [] },
    out := some (.place 3) }

/-- The timed net of `v` alone, immediate. -/
def ver004b_XV : TimedNet Nat :=
  { net := { places := [0, 1, 2, 3], transitions := [ver004b_v] }, timing := fun _ => .immediate,
    tol := 0 }

/-- The configuration of `v` alone. -/
def ver004b_CV : Cfg Nat Nat := { ver004b_C with X := ver004b_XV }

/-- The rows of `v`. -/
def ver004b_RV : List Novel.InFlight.Row := [(toTransition ver004b_v.core, [3])]

/-- The first cycle of `v`'s net starts `v` asynchronously. -/
def ver004b_labelsV : List (XLbl Nat Nat) := ver004b_toTest ++ [.begin, .start "v" false]

/-- From `{p, r}`, `v`'s net reaches nothing new: `p` stays marked, so `v` never fires. -/
theorem ver004b_v_never :
    ∀ x, Novel.InFlight.SReach ver004b_RV (splitTest []) (NoTerm ver004b_CV) (qCount ver004b_M) x →
      x.a = qCount ver004b_M ∧ x.pend = [] := by
  intro x hx
  induction hx with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hst ih =>
    obtain ⟨ha, hp⟩ := ih
    cases hst with
    | atomic r hr _ _ hen =>
      exfalso
      simp only [ver004b_RV, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      rw [enabledA_toTransition, ha] at hen
      revert hen
      decide
    | start r _ hsp => simp [splitTest] at hsp
    | complete r _ _ hp' => rw [hp] at hp'; exact absurd hp' List.not_mem_nil

/-- ✗ **An executor that ignores inhibitor arcs is not covered** (even by the split): on
`v : r, inhibitor p → bad` from `{p, r}` it starts `v` although `p` is marked; completing `v`
marks `bad`, which no run of the net does. -/
@[evidence forbids VER_004_exec]
theorem VER_004_exec_forbids_noInh : ¬ VER_004_exec ver004b_noInhExec (refSplit (K := PlaceId)) := by
  intro h
  have h1 : (xtrace (ver004b_dropInh ver004b_CV) (xinit ver004b_M 0) ver004b_labelsV).isSome =
      true := by decide
  obtain ⟨tr, ht⟩ := Option.isSome_iff_exists.mp h1
  have hE : ((xrun (ver004b_dropInh ver004b_CV) (xinit ver004b_M 0) ver004b_labelsV).map fun s =>
      (s.fl.map (·.t.core.name), qCount s.M 3)) = some (["v"], 0) := by decide
  rw [xtrace_last ht] at hE
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hE
  obtain ⟨hn, h3⟩ := hE
  have hn' : flNames (XRun.last (xinit ver004b_M 0) tr) = ["v"] := hn
  have hc : ∀ y ∈ tr, RowsCover ver004b_RV y := by
    intro y hy
    have hl : y.2.1 ∈ ver004b_labelsV := by
      rw [← xtrace_labels ht]; exact List.mem_map_of_mem hy
    unfold RowsCover
    revert hl
    generalize y.2.1 = l
    intro hl
    cases l <;> simp_all [ver004b_labelsV, ver004b_toTest]
  have hsplit : refSplit ver004b_cfg {} ver004b_CV.X = .ok (ver004b_CV.X, []) := rfl
  obtain ⟨pend, -, hx⟩ := h ver004b_CV ver004b_cfg {} _ [] ver004b_RV ver004b_M 0 tr
    [(toTransition ver004b_v.core, [3])] (by unfold NamesDistinct; decide)
    (fun u hu => by
      simp only [ver004b_CV, ver004b_XV, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst hu; exact ⟨by decide, by simp [ver004b_cfg]⟩)
    (fun _ h => absurd h List.not_mem_nil)
    (fun r hr => by
      simp only [ver004b_RV, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨ver004b_v, by simp [ver004b_CV, ver004b_XV], rfl, by simp [outs, ver004b_v, Verifier.outPlaces]⟩)
    (fun u hu => by
      simp only [ver004b_CV, ver004b_XV, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst hu; exact ⟨[3], by simp [ver004b_RV]⟩)
    rfl hsplit (ver004b_noInh_run (xtrace_run ht)) hc
    ⟨by rw [hn']; simp [splitTest, toTransition, ver004b_v], by simp [ver004b_RV]⟩
  have := congrFun (ver004b_v_never _ hx).1 3
  simp [Novel.InFlight.addAll, h3] at this
  revert this
  decide

/-! ### An executor that ignores the terminal stop -/

/-- An executor that ignores the terminal stop of [EXEC-042]: it runs as the reference does on
the configuration with no terminal place. -/
def ver004b_noStopExec : XRel PlaceId Nat := fun C => RefExec { C with terminals := [] }

/-- A run of the reference without terminal places is a run of `ver004b_noStopExec`. -/
theorem ver004b_noStop_run {C : Cfg PlaceId Nat} :
    ∀ {s : XSt PlaceId Nat} {tr : List (XStep PlaceId Nat)},
      XRun RefExec { C with terminals := [] } s tr → XRun ver004b_noStopExec C s tr
  | _, [], _ => trivial
  | _, _ :: _, h => ⟨h.1, h.2.1, ver004b_noStop_run h.2.2⟩

/-- A decided trace of `ls1 ++ ls2` is a trace of `ls1` followed by a trace of `ls2` from where
`ls1` ends. -/
theorem ver004b_xtrace_append {T : Type} {C : Cfg PlaceId T} :
    ∀ {s : XSt PlaceId T} {ls1 ls2 : List (XLbl PlaceId T)} {tr : List (XStep PlaceId T)},
      xtrace C s (ls1 ++ ls2) = some tr →
      ∃ tr1 tr2 s1, tr = tr1 ++ tr2 ∧ xtrace C s ls1 = some tr1 ∧ xrun C s ls1 = some s1 ∧
        xtrace C s1 ls2 = some tr2
  | s, [], ls2, tr, h => ⟨[], tr, s, rfl, rfl, rfl, by simpa using h⟩
  | s, l :: ls1, ls2, tr, h => by
    simp only [List.cons_append, xtrace] at h
    cases hs : xstep C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : xtrace C s' (ls1 ++ ls2) with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        obtain ⟨tr1, tr2, s1, rfl, h1, h2, h3⟩ := ver004b_xtrace_append ht
        refine ⟨(s, l, s') :: tr1, tr2, s1, by rw [← h]; rfl, ?_, ?_, h3⟩
        · simp [xtrace, hs, h1]
        · simp [xrun, hs, h2]

/-- `t : p → term + q` (`p = 0`, `q = 1`, `bad = 3`, `term = 4`). -/
def ver004b_tS : Reference.Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.and (.place 4) (.place 1)) }

/-- `u : q → bad`. -/
def ver004b_uS : Reference.Trans Nat :=
  { core := { name := "u", inputs := [⟨1, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.place 3) }

/-- The configuration of the stop example: `term` is terminal. -/
def ver004b_CS : Cfg Nat Nat :=
  { ver004b_C with
    X := { net := { places := [0, 1, 3, 4], transitions := [ver004b_tS, ver004b_uS] },
           timing := fun _ => .immediate, tol := 0 },
    terminals := [4] }

/-- The initial marking `{p}`. -/
def ver004b_MS : QMarking Nat Nat := fun p => if p = 0 then [1] else []

/-- The rows: `t` deposits `term` and `q`, `u` deposits `bad`. -/
def ver004b_RS : List Novel.InFlight.Row :=
  [(toTransition ver004b_tS.core, [4, 1]), (toTransition ver004b_uS.core, [3])]

/-- The split configuration of the stop example: `term` is terminal. -/
def ver004b_cfgS : SplitCfg Nat := { ver004b_cfg with terminals := [4] }

/-- Cycle 1 up to `t`'s return: `t` starts synchronously and writes `term` and `q`. -/
def ver004b_labelsS1 : List (XLbl Nat Nat) :=
  ver004b_toTest ++ [.begin, .start "t" true, .write 0 4 7, .write 0 1 7, .ret 0 true]

/-- From the end of cycle 1 to `u`'s return: `u` starts synchronously and writes `bad`. -/
def ver004b_labelsS2 : List (XLbl Nat Nat) :=
  [.endPass] ++ ver004b_toTest ++ [.begin, .start "u" true, .write 1 3 7, .ret 1 true]

set_option maxRecDepth 100000 in
/-- Before `t`'s completion, `t` is in flight, returned with tokens for `term` and `q`. -/
theorem ver004b_flS1 :
    (xrun { ver004b_CS with terminals := [] } (xinit ver004b_MS 0) ver004b_labelsS1).map
      (fun s => s.fl.map (fun f => (f.id, f.t, f.out))) =
    some [(0, ver004b_tS, some (.ok [(4, 7), (1, 7)]))] := by rfl

set_option maxRecDepth 100000 in
/-- Before `u`'s completion, `u` is in flight, returned with a token for `bad`. -/
theorem ver004b_flS2 :
    (xrun { ver004b_CS with terminals := [] } (xinit ver004b_MS 0)
      ((ver004b_labelsS1 ++ [.commit 0]) ++ ver004b_labelsS2)).map
      (fun s => s.fl.map (fun f => (f.id, f.t, f.out))) =
    some [(1, ver004b_uS, some (.ok [(3, 7)]))] := by rfl

/-- In the split net gated by the stop, `bad` stays empty: `q` is marked only together with
`term`, and once `term` is marked nothing fires. -/
theorem ver004b_stop_never :
    ∀ x, Novel.InFlight.SReach ver004b_RS (splitTest ["t"]) (NoTerm ver004b_CS)
        (qCount ver004b_MS) x →
      x.a 3 = 0 ∧ (0 < x.a 1 → 0 < x.a 4) ∧ ∀ n ∈ x.pend, n = "t" := by
  intro x hx
  induction hx with
  | refl => exact ⟨by decide, by decide, fun _ h => absurd h List.not_mem_nil⟩
  | @tail y z _ hst ih =>
    obtain ⟨h3, h14, hp⟩ := ih
    cases hst with
    | atomic r hr hsp hl hen =>
      simp only [ver004b_RS, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp [splitTest, toTransition, ver004b_tS] at hsp
      · exfalso
        rw [enabledA_toTransition] at hen
        have hq : 1 ≤ y.a 1 := by
          simp only [enabledNA, ver004b_uS, Bool.and_eq_true, List.all_eq_true,
            decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hen
          simpa [Card.required] using hen.1.1
        have h4 := h14 hq
        have := hl 4 (by simp [ver004b_CS])
        omega
    | start r hr hsp hl hen =>
      simp only [ver004b_RS, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨?_, ?_, ?_⟩
        · simp [Novel.InFlight.startA, Novel.ForwardDeposit.fireAD, toTransition, ver004b_tS,
            consumeAllAt, pre, specAt, Link.toInSpec, h3]
        · simp [Novel.InFlight.startA, Novel.ForwardDeposit.fireAD, toTransition, ver004b_tS,
            consumeAllAt, pre, specAt, Link.toInSpec]
          exact h14
        · intro n hn
          rcases List.mem_cons.mp hn with rfl | hn
          · rfl
          · exact hp n hn
      · simp [splitTest, toTransition, ver004b_uS] at hsp
    | complete r hr hl hp' =>
      simp only [ver004b_RS, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨?_, ?_, fun n hn => hp n (List.mem_of_mem_erase hn)⟩
        · simp [Novel.InFlight.addD, h3]
        · simp [Novel.InFlight.addD]
      · exfalso
        have := hp _ hp'
        simp [toTransition, ver004b_uS] at this

/-- ✗ **An executor that ignores the terminal stop is not covered** ([EXEC-042]): on `t : p →
term + q` with `term` terminal and `u : q → bad`, from `{p}`, it fires `t`, marking `term` and
`q`, and goes on to fire `u`, marking `bad`. The split net (which splits `t`, since `term` is
terminal) marks `q` only together with `term` and fires nothing once `term` is marked, so it never
marks `bad`. -/
@[evidence forbids VER_004_exec]
theorem VER_004_exec_forbids_noStop :
    ¬ VER_004_exec ver004b_noStopExec (refSplit (K := PlaceId)) := by
  intro h
  have h1 : (xtrace { ver004b_CS with terminals := [] } (xinit ver004b_MS 0)
      ((ver004b_labelsS1 ++ [.commit 0]) ++ ver004b_labelsS2 ++ [.commit 1])).isSome = true := by
    decide
  obtain ⟨tr, ht⟩ := Option.isSome_iff_exists.mp h1
  have hE : ((xrun { ver004b_CS with terminals := [] } (xinit ver004b_MS 0)
      ((ver004b_labelsS1 ++ [.commit 0]) ++ ver004b_labelsS2 ++ [.commit 1])).map fun s =>
      (s.fl.map (·.t.core.name), qCount s.M 3)) = some ([], 1) := by decide
  rw [xtrace_last ht] at hE
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hE
  obtain ⟨hn, h3⟩ := hE
  have hn' : flNames (XRun.last (xinit ver004b_MS 0) tr) = [] := hn
  have hc : ∀ y ∈ tr, RowsCover ver004b_RS y := by
    obtain ⟨trX, s3, s4, htr, htrX, hs3⟩ := ver004b_xtrace_snoc ht
    obtain ⟨trA, trB, s2, hX, htrA, hs2, htrB⟩ := ver004b_xtrace_append htrX
    obtain ⟨trA', s1, s1', hA, htrA', hs1⟩ := ver004b_xtrace_snoc htrA
    have hfl1 := ver004b_flS1
    rw [hs1, Option.map_some, Option.some.injEq] at hfl1
    have hfl3 := ver004b_flS2
    rw [hs3, Option.map_some, Option.some.injEq] at hfl3
    have hother : ∀ y : XStep PlaceId Nat,
        y.2.1 ∈ ver004b_labelsS1 ∨ y.2.1 ∈ ver004b_labelsS2 → RowsCover ver004b_RS y := by
      intro y hl
      unfold RowsCover
      revert hl
      generalize y.2.1 = l
      intro hl
      cases l <;> simp_all [ver004b_labelsS1, ver004b_labelsS2, ver004b_toTest]
    have hcommit : ∀ (s : XSt PlaceId Nat) (s' : XSt PlaceId Nat) (i : Nat) (u : Reference.Trans Nat)
        (e0 : List (PlaceId × Nat)),
        s.fl.map (fun f => (f.id, f.t, f.out)) = [(i, u, some (.ok e0))] →
        (toTransition u.core, e0.map Prod.fst) ∈ ver004b_RS →
        RowsCover ver004b_RS (s, .commit i, s') := by
      intro s s' i u e0 hfl hrow f hf _ e he
      have hm : (f.id, f.t, f.out) ∈ s.fl.map (fun f => (f.id, f.t, f.out)) :=
        List.mem_map_of_mem hf
      rw [hfl] at hm
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      obtain ⟨-, hft, hfo⟩ := hm
      rw [hfo] at he
      simp only [Option.some.injEq, Outcome.ok.injEq, reduceCtorEq, or_false] at he
      subst he
      rw [hft]
      exact hrow
    intro y hy
    rw [htr, hX, hA] at hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with ((hy | rfl) | hy) | rfl
    · exact hother y (Or.inl (by rw [← xtrace_labels htrA']; exact List.mem_map_of_mem hy))
    · exact hcommit _ _ _ _ _ hfl1 (by simp [ver004b_RS])
    · exact hother y (Or.inr (by rw [← xtrace_labels htrB]; exact List.mem_map_of_mem hy))
    · exact hcommit _ _ _ _ _ hfl3 (by simp [ver004b_RS])
  obtain ⟨pend, -, hx⟩ := h ver004b_CS ver004b_cfgS {} _ ["t"] ver004b_RS ver004b_MS 0 tr []
    (by unfold NamesDistinct; decide)
    (fun u hu => by
      simp only [ver004b_CS, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact ⟨by decide, by simp [ver004b_cfgS, ver004b_cfg]⟩)
    (fun p hp => by simpa [ver004b_CS, ver004b_cfgS] using hp)
    (fun r hr => by
      simp only [ver004b_RS, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ver004b_tS, by simp [ver004b_CS], rfl, by simp [outs, ver004b_tS, Verifier.outPlaces]⟩
      · exact ⟨ver004b_uS, by simp [ver004b_CS], rfl, by simp [outs, ver004b_uS, Verifier.outPlaces]⟩)
    (fun u hu => by
      simp only [ver004b_CS, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact ⟨[4, 1], by simp [ver004b_RS]⟩
      · exact ⟨[3], by simp [ver004b_RS]⟩)
    rfl rfl (ver004b_noStop_run (xtrace_run ht)) hc
    ⟨by rw [hn']; rfl, fun _ h => absurd h List.not_mem_nil⟩
  have := (ver004b_stop_never _ hx).1
  simp [Novel.InFlight.addAll, h3] at this

end Libpetri.Spec
