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
in-flight split of `VER_004_split` (witness `Split.refSplit`). It says: when the split succeeds
without the opt-out and every row the run deposits is an outcome of its transition, every state a
run of `E` reaches is covered by the split: the counts of the state, with each action in flight of
a transition the split leaves atomic completed by one of its rows, plus one token on
`inflight:<t>` for each action of a split transition `t` in flight, are a marking the verified net
`Y` that `S` returns reaches under `Reference.Reach` (the first conclusion), and the same counts, with the split
actions pending, are reached in the flat split net `Novel.InFlight.SStep` over the rows, every step
gated by the strict stop of [EXEC-042] (the second conclusion).

The holds theorem (`VER_004_exec_reference`) chains the L5 count projection of
`Reference/ExecLink.lean` (`count_projection`: a `RefExec` run is an `InFlight.XStep` run, the
moved deposits of each firing pass completed at its end) with `InFlight.split_covers_executor`,
whose criterion `refSplit`'s split list meets: a transition `refSplit` leaves atomic has no output
place that a terminal marks or any transition tests by an inhibitor, a reset or a drain
(`ver004b_untested`, `ver004b_live`). The first conclusion is the named lift `ver004b_lift`: a flat split-net
run over outcome rows is a run of the named split net `splitTimed cfg sp X`, the in-flight places
counting the pending starts; `VER_004_split` pins `Y` to that net (`ver004b_split_Y`). It is proved
in general: `VER_004_exec_of` derives block B for every executor meeting the L5 agreement conjunct
`CountAgrees` and every split meeting `VER_004_split`, so the consistency theorem gets block B from
those two.

Corollaries from the statement alone: `VER_004_exec_rest` (where nothing is in flight the
executor's counts are a split-net marking with nothing pending, the rest the run loop waits for,
ruling D13) and `VER_004_exec_safety` (a split-net `Proven` of an upward-closed marking property
holds at every executor state, actions in flight included).

Wrong models: the split that never splits (`ver004b_atomicSplit`, AC4's point: the executor marks
`bad` while `t` is in flight, which no atomic run does), the split that returns the right list with
the unsplit net (`ver004b_wrongNetSplit`: its net never marks `inflight:t`), the executor that
ignores inhibitor arcs (`ver004b_noInhExec`) and the executor that ignores the terminal stop of
[EXEC-042] (`ver004b_noStopExec`, which the strict-stop gate of the second conclusion rejects). The worked example
(`VER_004_exec_nonvacuous`) is the [VER-004] witness net of `InFlight.inflight_witness` run on the
reference executor.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam
open Libpetri.Spec.Verifier (Options)
open Libpetri.Spec.Verifier.Split (SplitCfg splits isCompletion outs nonMonotone drainPlaces
  refSplit splitTimed splitNet startHalf endHalf completionOut fwdSrcs transPlaces allPlaces Fresh
  OneFwd FwdFromInputs firstRefusal firstRefusal_none refusal_none_fresh multiFwd
  multiFwdIn_true_none multiFwdIn_findTimeout fwdSrcs_findTimeout branches_completionOut
  findTimeout_completionOut timeoutDeposits_completionOut mem_splitNet_of reach_run run_frame)
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

/-- **The rows are outcomes** ([IO-016], the reading every analysis uses): every row of `R` is a
transition of the net whose deposit has, place by place, the counts of a deposit its output spec
offers (`Reference.deposit`, one token per place of a branch, or the `Timeout` child's deposit),
at every marking, the consumed counts read there (`Consumes`). A write of two tokens to a place its
branch names once (IO-016 AC4) and a partial write under the CONC-026 skip are not outcomes. A
failed action's empty row is one only where the empty deposit is an outcome. -/
def OutcomeRows (net : Reference.Net PlaceId) (R : List Novel.InFlight.Row) : Prop :=
  ∀ r ∈ R, ∃ u ∈ net.transitions, r.1 = toTransition u.core ∧
    ∀ m : CountMarking PlaceId, ∃ ch d, Reference.deposit (Consumes u m) u.out ch = some d ∧
      SamePerPlace r.2 d

/-- The marking `a` with one more token on `inflight:<t>` for each entry `t` of `L`. -/
def withInflight (cfg : SplitCfg PlaceId) (a : AMarking) (L : List String) : AMarking :=
  fun p => a p + (L.map cfg.inflight).count p

/-! ## The block -/

requirement VER_004_exec
  id "VER-004"
  title "Untimed Over-Approximation (the executor's runs with actions in flight)"
  kind B
  scope "the executor's runs on a net the split accepts, read through the count projection L5 of RefExec (SHOULD; the shall sentence binds an implementation that offers verification)"
  source verbatim "spec/07-verification.md"
  quote "*While* `assumeAtomicFiring` is not set and the split succeeds, *where* no firing fails (no action fails, and output validation and the relay check reject no output or timeout outcome), no action publishes an output before it completes and no token is injected, a marking the executor reaches from the initial marking, with each action in flight of a transition that is not split completed with one of its outcomes, *shall* be reachable in the split net from the initial marking, with one token on `inflight:<t>` for each action of a split transition `t` in flight."
        "That is a sound over-approximation for all three."
  reading "For every executor relation E and split S, every executor configuration C, split configuration cfg, options o, verified net Y, split list sp, rows R, initial marking M0, run of E from the initial state of M0 and completion ds:"
          "if the transition names of C are distinct, no transition of C is a completion step or an environment step of cfg, every terminal place of C is a terminal place of cfg, every forward source of C is an input place of its transition, every row of R is an outcome of a transition of C's net at every marking (OutcomeRows), every transition has a row in R, o does not set assumeAtomicFiring, S returns the verified net Y and the split list sp, every commit, timeout deposit and fail of the run deposits a row of R (RowsCover: no publication, no injection), and ds completes each action in flight at the end of the run whose transition is not in sp with one row of it,"
          "then Y reaches (Reference.Reach), from the counts of M0, the counts at the end of the run with ds deposited and one more token on inflight:<t> for each action in flight whose transition t is in sp,"
          "and the split net over R with split set sp (InFlight.SStep, every step gated by the strict stop) reaches, from the counts of M0, the counts at the end of the run with ds deposited, with pending exactly the actions in flight whose transition is in sp (as a multiset)."
  assumes "The model is the pair (E, S). E : XRel PlaceId T is the executor relation the EXEC, CONC and ENV blocks constrain, read at flat place names (PlaceId) as the L5 conjunct CountAgrees is; the witness is RefExec. S : SplitFn PlaceId is the split of VER_004_split; the witness is Split.refSplit. The witness pair is (RefExec, refSplit) (VER_004_exec_reference, through VER_004_exec_of: block B holds of every E meeting the L5 conjunct CountAgrees and every S meeting VER_004_split): the L5 count projection (ExecLink count_projection: moving each in-pass deposit behind the last start of its pass makes a RefExec run an InFlight.XStep run with the same counts and the firings in flight pending) followed by InFlight.split_covers_executor, whose criterion refSplit's split list meets (ver004b_untested: an atomic transition's outputs are tested by no inhibitor, reset or drain; ver004b_live: it marks no terminal place), and then the named lift ver004b_lift (a flat split-net run over outcome rows is a Reference.Reach run of the named split net, each pending start a token on its in-flight place), with ver004b_split_Y (VER_004_split pins Y: the net itself when nothing is split, splitTimed cfg sp X otherwise)."
          "The split net of the quoted sentence is Y, the verified net S returns, read under Reference.Reach (the third reading line); VER_004_split pins it to splitTimed cfg sp X, and a split that returns the right list with a wrong net fails that line (VER_004_exec_forbids_wrongNet: with the unsplit net, inflight:t is never marked). Reference.Net carries no terminal list, so the terminal rewrite of EXEC-042 that follows the split ('The split comes before the terminal rewrite') is the last line: the flat split net InFlight.SStep over the rows R with split set sp, in which a transition outside sp fires atomically, one in sp starts (the pending list) and later completes with a row, and the strict stop (NoTerm C) gates every step; an executor that ignores the terminal stop fails it (VER_004_exec_forbids_noStop). 'Reaches from the initial marking' is a run from xinit M0 r0, the reference initial state, and the split net's initial marking is the counts of M0 (the split leaves the initial marking as it is, splitAbs)."
          "'No firing fails' (no action fails, and output validation and the relay check of NU-054 reject nothing; a timeout outcome meets only the relay check, ruling D24 (a)) is OutcomeRows together with RowsCover. A firing that fails, or whose outcome is rejected, consumes its inputs and deposits nothing (EVT-008), which RowsCover reads as the empty row, and OutcomeRows accepts the empty row only for a transition whose output spec offers the empty deposit (such as a transition with no output spec), where a failure leaves the marking a successful firing leaves; so the line covers no failed firing the sentence excludes except those, and of them it says what it says of a success. OutcomeRows also excludes the rows output validation rejects (IO-016): a write of two tokens to a place its branch names once (IO-016 AC4) and a partial write under the CONC-026 skip. A row must be an outcome at every marking, its consumed counts read there, because the L5 projection forgets the marking each row was deposited from. A transition the split leaves atomic whose Timeout forwards an all or atLeast input (IO-014) deposits as many tokens as it drained, so no fixed row is an outcome of it at every marking, and a net with one is outside the line (an open item: it needs the projection to carry the marking of each deposit, a change to the shared ExecLink). A split transition with such a forward is refused (the VER-004 refusal sentence). FwdFromInputs (every forward source is an input place of its transition) is the builder's check (IO-014 AC3), true of every built net: a forward from a place that is no input would deposit nothing on a timeout, while its completion step deposits one token."
          "The sentence's 'no action ... publishes an output before it completes' (ruling D28 (a), ctx.flush() in Rust and Python) and 'no token is injected' are the RowsCover hypothesis: a publish step and an inject step make it false, so a run with either is outside the line (InFlight.XStep has no counterpart for them; environment places are VER-006's closure, injections into the executor are ENV's and L8's). The rows are a per-run hypothesis, as OfferedEmission is for L2."
          "'That is a sound over-approximation for all three.' (ruling D8 (b): whether a transition starts again while an earlier firing of it is in flight is implementation-defined, Cfg.reentrant) is the line for every C, Cfg.reentrant true (Rust, Python) and false (Java, TypeScript) alike: InFlight.SStep and the named split net let a split transition start again with inflight:<t> marked, and XStep's pending list is a multiset. The CONC-002 report note and AC8 are report text (kind Q), as VER_004_split's assumes say."
          "Hypotheses that are not in the sentence, and why. Distinct transition names (ruling D10) make the rows' names unique, premise 1 of InFlight. SplitExemptFree: Split.isCompletion and cfg.envTrans exempt a transition from the split by its shape whatever its outputs; an executor net whose own transition looked like a completion step (named complete:<x>, one input one(inflight:<x>)) or was listed as an environment step would keep an action's gap the split does not model, so the line is stated for nets without them, and no block states the split for such nets (an open item). Every terminal place of C counts as a terminal of cfg: the split reads the terminals it is given. FwdFromInputs and OutcomeRows are above."
          "AC4 is the line with VER-003's Proven line: a Proven of an upward-closed property on the split net holds at every executor state, actions in flight included (VER_004_exec_safety), and a quiescence Proven covers the executor's rests, where nothing is in flight (VER_004_exec_rest: the run loop waits for its actions in flight before it rests, ruling D13). AC4's example (the AC4 inhibitor net, the executor marks the inhibited output while t is in flight) is VER_004_exec_nonvacuous on the inhibitor net of InFlight.inflight_witness, where the named split net reaches the executor's counts with one token on inflight:t, and ver004b_atomicSplit shows the atomic net does not cover it (AC4's 'Disable the split and confirm each test fails'). That a Violated is not a false alarm is not claimed (completeness, VER-003 and VER-023). The test derivation's AC4 clause (run each net on both executors with an action that sleeps) is this example."
          "Not in the model: ν firings (RefExec has no ν kernel; a matched firing is a count firing of its transition (NuRestrictsTo), so the line reads it as one, and the split refuses a ν-join or a coloured write it would split, as the VER-004 refusal sentence says), timing (InFlight.SStep and Reference.Reach are untimed; that the timed executor's rests are reap-quiescent is VER_004_timed and ExecLink L6), priorities (the conflict-priority demand of NU-052 only adds split transitions, which the line allows: split_covers_executor holds for every split set meeting the criterion), and the report notes (kind N, Q)."
  signoff "2026-11-13 b40cc4a794c3b2a9 ai"
  statement : ∀ {T : Type}, XRel PlaceId T → SplitFn PlaceId → Prop :=
    fun {T} E S =>
      ∀ (C : Cfg PlaceId T) (cfg : SplitCfg PlaceId) (o : Options) (Y : TimedNet PlaceId)
        (sp : List String) (R : List Novel.InFlight.Row) (M0 : QMarking PlaceId T) (r0 : Nat)
        (tr : List (XStep PlaceId T)) (ds : List Novel.InFlight.Row),
        NamesDistinct C.X → SplitExemptFree cfg C.X.net → (∀ p ∈ C.terminals, p ∈ cfg.terminals) →
        FwdFromInputs C.X.net → OutcomeRows C.X.net R →
        (∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R) →
        o.assumeAtomicFiring = false → S cfg o C.X = .ok (Y, sp) →
        XRun E C (xinit M0 r0) tr → (∀ y ∈ tr, RowsCover R y) →
        Novel.InFlight.Completes R
          ((flNames (XRun.last (xinit M0 r0) tr)).filter fun n => !splitTest sp n) ds →
        Reference.Reach Y.net (qCount M0)
            (withInflight cfg (Novel.InFlight.addAll (qCount (XRun.last (xinit M0 r0) tr).M) ds)
              ((flNames (XRun.last (xinit M0 r0) tr)).filter (splitTest sp))) ∧
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
          FwdFromInputs C.X.net →
            OutcomeRows C.X.net R →
              (∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R) →
                o.assumeAtomicFiring = false →
                  S cfg o C.X = Except.ok (Y, sp) →
                    XRun E C (xinit M0 r0) tr →
                      (∀ y ∈ tr, RowsCover R y) →
                        Novel.InFlight.Completes R
                            (List.filter (fun n => !splitTest sp n) (flNames (XRun.last (xinit M0 r0) tr))) ds →
                          Reach Y.net (qCount M0)
                              (withInflight cfg (Novel.InFlight.addAll (qCount (XRun.last (xinit M0 r0) tr).M) ds)
                                (List.filter (splitTest sp) (flNames (XRun.last (xinit M0 r0) tr)))) ∧
                            ∃ pend,
                              pend.Perm (List.filter (splitTest sp) (flNames (XRun.last (xinit M0 r0) tr))) ∧
                                Novel.InFlight.SReach R (splitTest sp) (NoTerm C) (qCount M0)
                                  { a := Novel.InFlight.addAll (qCount (XRun.last (xinit M0 r0) tr).M) ds,
                                    pend := pend }
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

/-- Outcome rows are rows of the net: an outcome deposits only into output places. -/
theorem ver004b_outcome_exec {net : Reference.Net PlaceId} {R : List Novel.InFlight.Row}
    (h : OutcomeRows net R) : ExecRows net R := by
  intro r hr
  obtain ⟨u, hu, hru, ho⟩ := h r hr
  refine ⟨u, hu, hru, fun p hp => ?_⟩
  obtain ⟨ch, d, hd, hs⟩ := ho (fun _ => 0)
  have hc : 0 < d.count p := by
    have := hs p
    simp only [Deposits, depProd] at this
    rw [← this]
    exact List.count_pos_iff.mpr hp
  obtain ⟨o, hou, hx⟩ := Verifier.mem_deposit hd (List.count_pos_iff.mp hc)
  simp [outs, hou, hx]

end Ref

/-! ## The named lift: a flat split-net run over outcome rows is a run of the split net -/

section Lift

/-- A place a transition does not name is not one of its reset or input places. -/
theorem ver004b_not_arc {u : Reference.Trans PlaceId} {q : PlaceId} (hq : q ∉ transPlaces u) :
    q ∉ u.core.resets ∧ nspecAt u.core q = none := by
  refine ⟨fun hr => hq (by simp [transPlaces, hr]), ?_⟩
  unfold nspecAt
  rw [List.find?_eq_none]
  intro s hs hsq
  exact hq (by
    have : s.place = q := by simpa using hsq
    simp only [transPlaces, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨s, hs, this⟩))))

/-- Extra tokens on places a transition does not name leave its enablement as it is. -/
theorem ver004b_enabledNA_add {m e : PlaceId → Nat} {u : Reference.Trans PlaceId}
    (he : ∀ p ∈ transPlaces u, e p = 0) :
    enabledNA (fun p => m p + e p) u.core = enabledNA m u.core := by
  have hi : ∀ s ∈ u.core.inputs, e s.place = 0 := fun s hs => he _ (by
    simp only [transPlaces, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨s, hs, rfl⟩))))
  have hh : ∀ p ∈ u.core.inhibitors, e p = 0 := fun p hp => he p (by simp [transPlaces, hp])
  have hr : ∀ p ∈ u.core.reads, e p = 0 := fun p hp => he p (by simp [transPlaces, hp])
  unfold enabledNA
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun s hs => ?_, fun p hp => ?_⟩, fun p hp => ?_⟩
    · have := h1 s hs; rw [hi s hs, Nat.add_zero] at this; exact this
    · have := h2 p hp; rw [hh p hp, Nat.add_zero] at this; exact this
    · have := h3 p hp; rw [hr p hp, Nat.add_zero] at this; exact this
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun s hs => ?_, fun p hp => ?_⟩, fun p hp => ?_⟩
    · rw [hi s hs, Nat.add_zero]; exact h1 s hs
    · rw [hh p hp, Nat.add_zero]; exact h2 p hp
    · rw [hr p hp, Nat.add_zero]; exact h3 p hp

/-- Extra tokens on places a transition does not name leave its consumption as it is. -/
theorem ver004b_nconsumed_add {m e : PlaceId → Nat} {u : Reference.Trans PlaceId}
    (he : ∀ p ∈ transPlaces u, e p = 0) :
    nconsumed (fun p => m p + e p) u.core = nconsumed m u.core := by
  funext p
  unfold nconsumed
  cases hs : nspecAt u.core p with
  | none => rfl
  | some s =>
    have hpl : s.place = p := by simpa using List.find?_some hs
    have hmem : s ∈ u.core.inputs := List.mem_of_find?_eq_some hs
    have h0 : e p = 0 := he p (by
      rw [← hpl]
      simp only [transPlaces, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inl ⟨s, hmem, rfl⟩))))
    simp [h0]

/-- Extra tokens on places a transition does not name stay where they are when it fires. -/
theorem ver004b_fireNC_add {m e : PlaceId → Nat} {u : Reference.Trans PlaceId}
    {prod : PlaceId → Nat} (he : ∀ p ∈ transPlaces u, e p = 0) :
    fireNC (fun p => m p + e p) u.core prod = fun p => fireNC m u.core prod p + e p := by
  funext p
  unfold fireNC
  rw [ver004b_nconsumed_add he]
  by_cases hp : e p = 0
  · simp [hp]
  · have hres : p ∉ u.core.resets := fun h => hp (he p (by simp [transPlaces, h]))
    have hin : nconsumed m u.core p = 0 := by
      unfold nconsumed
      cases hs : nspecAt u.core p with
      | none => rfl
      | some s =>
        exfalso
        have hpl : s.place = p := by simpa using List.find?_some hs
        have hmem : s ∈ u.core.inputs := List.mem_of_find?_eq_some hs
        exact hp (he p (by
          rw [← hpl]
          simp only [transPlaces, List.mem_append, List.mem_map]
          exact Or.inl (Or.inl (Or.inl (Or.inl ⟨s, hmem, rfl⟩)))))
    simp only [hres, if_false, hin]
    omega

/-- **The completion step deposits what the transition deposits**, whatever it consumed: an
outcome of `t` is an outcome of `complete:<t>` when every forward of `t`'s `Timeout` is from a
`one` input (`Split.fires_split` read at the deposit alone). -/
theorem ver004b_deposit_endHalf {u : Reference.Trans PlaceId} {m : PlaceId → Nat}
    {ch : Novel.ForwardDeposit.Choice} {d : List PlaceId}
    (hone : ∀ o, u.out = some o → ∀ ch, o.findTimeout = some ch →
      ∀ s ∈ fwdSrcs ch, ∃ spec, nspecAt u.core s = some spec ∧ spec.card = .one)
    (hd : Reference.deposit (nconsumed m u.core) u.out ch = some d) (c' : PlaceId → Nat) :
    ∃ ch', Reference.deposit c' (u.out.map completionOut) ch' = some d := by
  cases hout : u.out with
  | none =>
    rw [hout] at hd
    refine ⟨ch, ?_⟩
    have hfree : ∀ c c' : PlaceId → Nat,
        Reference.deposit c none ch = Reference.deposit c' none ch := by
      intro c c'
      cases ch with
      | action i => cases i <;> rfl
      | timedOut _ => rfl
    exact (hfree _ _).trans hd
  | some o =>
    rw [hout] at hd
    cases ch with
    | action i =>
      refine ⟨.action i, ?_⟩
      simpa [Reference.deposit, branches_completionOut] using hd
    | timedOut j =>
      refine ⟨.timedOut j, ?_⟩
      simp only [Reference.deposit, Option.map_some] at hd ⊢
      rw [findTimeout_completionOut]
      cases hft : o.findTimeout with
      | none => rw [hft] at hd; simp at hd
      | some c =>
        rw [hft] at hd
        simp only [Option.map_some, Option.bind_some] at hd ⊢
        rw [timeoutDeposits_completionOut (nconsumed m u.core) _ c (fun s hs => by
          obtain ⟨spec, hsp, hc⟩ := hone o hout c hft s hs
          simp [nconsumed, hsp, hc, Card.consumesAll, Card.required])]
        exact hd

/-- The in-flight tokens of split transitions of the net lie on no place a transition of the net
names. -/
theorem ver004b_inflight_zero {cfg : SplitCfg PlaceId} {sp : List String}
    {net : Reference.Net PlaceId} (hF : Fresh cfg sp net) {L : List String}
    (hL : ∀ n ∈ L, ∃ u ∈ net.transitions, u.core.name = n ∧ n ∈ sp)
    {u : Reference.Trans PlaceId} (hu : u ∈ net.transitions) :
    ∀ p ∈ transPlaces u, (L.map cfg.inflight).count p = 0 := by
  intro p hp
  rw [List.count_eq_zero]
  intro hm
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hm
  obtain ⟨u', hu', rfl, hsp⟩ := hL n hn
  exact hF u' hu' hsp (List.mem_append_right _ (List.mem_flatMap.mpr ⟨u, hu, hp⟩))

/-- `withInflight` reads its list as a multiset. -/
theorem ver004b_withInflight_perm {cfg : SplitCfg PlaceId} {a : AMarking} {L L' : List String}
    (h : L.Perm L') : withInflight cfg a L = withInflight cfg a L' := by
  funext p
  simp only [withInflight, (h.map cfg.inflight).count_eq p]

/-- **The named lift.** Over rows that are outcomes, every state the flat split net reaches is,
with one token on `inflight:<t>` per pending `t`, a marking the named split net reaches: an atomic
row is a firing of its transition, a start is a firing of the start half (its only output
`inflight:<t>`), a completion a firing of `complete:<t>`. The pending names are split transitions
of the net. `Yn` is any net holding each atomic transition and both halves of each split one. -/
theorem ver004b_lift {cfg : SplitCfg PlaceId} {sp : List String} {net Yn : Reference.Net PlaceId}
    {R : List Novel.InFlight.Row} {live : AMarking → Prop} {a0 : AMarking}
    (hO : OutcomeRows net R)
    (hA : ∀ u ∈ net.transitions, u.core.name ∉ sp → u ∈ Yn.transitions)
    (hS : ∀ u ∈ net.transitions, u.core.name ∈ sp →
      startHalf cfg u ∈ Yn.transitions ∧ endHalf cfg u ∈ Yn.transitions)
    (hF : Fresh cfg sp net) (hone : OneFwd sp net) {x : Novel.InFlight.XState}
    (hx : Novel.InFlight.SReach R (splitTest sp) live a0 x) :
    Reference.Reach Yn a0 (withInflight cfg x.a x.pend) ∧
      ∀ n ∈ x.pend, ∃ u ∈ net.transitions, u.core.name = n ∧ n ∈ sp := by
  induction hx with
  | refl =>
    have h0 : withInflight cfg a0 [] = a0 := by funext p; simp [withInflight]
    exact ⟨by rw [h0]; exact Relation.ReflTransGen.refl, fun _ h => absurd h List.not_mem_nil⟩
  | @tail y z _ hst ih =>
    obtain ⟨hreach, hpend⟩ := ih
    have he := fun {u} (hu : u ∈ net.transitions) => ver004b_inflight_zero hF hpend hu
    cases hst with
    | atomic r hr hsp _ hen =>
      obtain ⟨u, hu, hru, hout⟩ := hO r hr
      have hname : r.1.name = u.core.name := by rw [hru]; rfl
      have hn : u.core.name ∉ sp := by
        intro h; simp [splitTest, hname, h] at hsp
      obtain ⟨ch, d, hd, hsame⟩ := hout (withInflight cfg y.a y.pend)
      have hdp : depProd r.2 = depProd d := funext hsame
      refine ⟨Relation.ReflTransGen.tail hreach
        ⟨_, u, hA u hu hn, rfl, d, ?_, ⟨ch, hd⟩, ?_⟩, hpend⟩
      · show enabledNA (fun p => y.a p + _) u.core = true
        rw [ver004b_enabledNA_add (he hu), ← enabledA_toTransition, ← hru]
        exact hen
      · show (fun p => _ + _) = fireNC (fun p => y.a p + _) u.core (depProd d)
        rw [ver004b_fireNC_add (he hu), ← hdp, ← fireAD_toTransition, ← hru]
    | start r hr hsp _ hen =>
      obtain ⟨u, hu, hru, -⟩ := hO r hr
      have hname : r.1.name = u.core.name := by rw [hru]; rfl
      have hn : u.core.name ∈ sp := by simpa [splitTest, hname] using hsp
      have hq := ver004b_not_arc (fun h => hF u hu hn
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨u, hu, h⟩)))
      have key : ∀ p, fireNC y.a u.core (depProd [cfg.inflight u.core.name]) p =
          fireNC y.a u.core (depProd []) p + (if cfg.inflight u.core.name = p then 1 else 0) := by
        intro p
        unfold fireNC
        by_cases hpq : cfg.inflight u.core.name = p
        · subst hpq
          simp [hq.1, nconsumed, hq.2, depProd]
        · by_cases hres : p ∈ u.core.resets
          · simp [hres, depProd, hpq]
          · simp [hres, depProd, hpq]
      refine ⟨Relation.ReflTransGen.tail hreach
        ⟨_, startHalf cfg u, (hS u hu hn).1, rfl, [cfg.inflight u.core.name], ?_, ⟨.action 0, rfl⟩,
          ?_⟩, ?_⟩
      · show enabledNA (fun p => y.a p + _) u.core = true
        rw [ver004b_enabledNA_add (he hu), ← enabledA_toTransition, ← hru]
        exact hen
      · show (fun p => _ + _) = fireNC (fun p => y.a p + _) u.core _
        rw [ver004b_fireNC_add (he hu)]
        funext p
        simp only [List.map_cons, List.count_cons, hname, beq_iff_eq]
        rw [key p, hru, Novel.InFlight.startA, fireAD_toTransition]
        split_ifs <;> omega
      · intro n hn'
        rcases List.mem_cons.mp hn' with rfl | hn'
        · exact ⟨u, hu, hname.symm, by rw [hname]; exact hn⟩
        · exact hpend n hn'
    | complete r hr _ hp =>
      obtain ⟨u, hu, hru, hout⟩ := hO r hr
      have hname : r.1.name = u.core.name := by rw [hru]; rfl
      obtain ⟨u', hu', hu'n, hn⟩ := hpend _ hp
      rw [hname] at hn hp
      obtain ⟨ch, d, hd, hsame⟩ := hout (withInflight cfg y.a y.pend)
      obtain ⟨ch', hd'⟩ := ver004b_deposit_endHalf (hone u hu hn) hd
        (nconsumed (withInflight cfg y.a y.pend) (endHalf cfg u).core)
      have hperm := ((List.perm_cons_erase hp).map cfg.inflight)
      have hcnt : ∀ p, (y.pend.map cfg.inflight).count p =
          ((y.pend.erase u.core.name).map cfg.inflight).count p +
            (if cfg.inflight u.core.name = p then 1 else 0) := by
        intro p
        rw [hperm.count_eq p, List.map_cons, List.count_cons]
        simp only [beq_iff_eq]
      have h1 : 1 ≤ withInflight cfg y.a y.pend (cfg.inflight u.core.name) := by
        have := hcnt (cfg.inflight u.core.name)
        simp only [if_true] at this
        simp only [withInflight]
        omega
      refine ⟨Relation.ReflTransGen.tail hreach
        ⟨_, endHalf cfg u, (hS u hu hn).2, rfl, d, ?_, ⟨ch', hd'⟩, ?_⟩, ?_⟩
      · simp [endHalf, enabledNA, Card.required]
        exact h1
      · funext p
        have hs := hsame p
        simp only [Deposits, depProd] at hs
        have hc := hcnt p
        simp only [withInflight, Novel.InFlight.addD, fireNC, endHalf, nconsumed, nspecAt,
          List.find?, depProd, hname] at hc ⊢
        by_cases hpq : cfg.inflight u.core.name = p
        · subst hpq
          simp only [List.not_mem_nil, if_false, decide_true, if_true, Card.consumesAll,
            Card.required] at hc ⊢
          simp only [Bool.false_eq_true, if_false] at hc ⊢
          omega
        · simp only [List.not_mem_nil, if_false, hpq, decide_false] at hc ⊢
          omega
      · intro n hn'
        rw [hname] at hn'
        exact hpend n (List.mem_of_mem_erase hn')

end Lift

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

/-- **The split block pins the verified net** whenever the split succeeds without the opt-out:
the net itself with nothing split, or the split net of a refusal-free split list. -/
theorem ver004b_split_Y {S : SplitFn PlaceId} {P : SplitPlanFn PlaceId}
    (h : VER_004_split S P) {cfg : SplitCfg PlaceId} {o : Options} {X Y : TimedNet PlaceId}
    {sp : List String} (hat : o.assumeAtomicFiring = false) (hS : S cfg o X = .ok (Y, sp)) :
    (sp = [] ∧ Y = X) ∨ (firstRefusal cfg X.net sp = none ∧ Y = splitTimed cfg sp X) := by
  by_cases hnil : splits cfg X.net = []
  · rw [h.2.1 cfg o X hat hnil] at hS
    simp only [Except.ok.injEq, Prod.mk.injEq] at hS
    exact Or.inl ⟨hS.2.symm, hS.1.symm⟩
  · cases hr : ver004FirstRefused cfg X.net (splits cfg X.net) with
    | some t =>
      obtain ⟨e, he, -⟩ := h.2.2.1 cfg o X t hat hr
      rw [he] at hS
      exact absurd hS (by simp)
    | none =>
      rw [h.2.2.2.1 cfg o X hat hnil hr] at hS
      simp only [Except.ok.injEq, Prod.mk.injEq] at hS
      obtain ⟨rfl, rfl⟩ := hS
      exact Or.inr ⟨(ver004_firstRefused_none_iff _ _ _).mp hr, rfl⟩

/-- A refusal-free split list of a built net: the in-flight places are fresh and every forward
of a split transition's `Timeout` is from a `one` input (as in `Split.refSplit_run`). -/
theorem ver004b_fresh_one {cfg : SplitCfg PlaceId} {net : Reference.Net PlaceId}
    {sp : List String} (hnone : firstRefusal cfg net sp = none) (hb : FwdFromInputs net) :
    Fresh cfg sp net ∧ OneFwd sp net := by
  have hfr : ∀ t ∈ net.transitions, t.core.name ∈ sp → Verifier.Split.refusal cfg net t = none :=
    fun t ht hn => firstRefusal_none hnone ht hn
  refine ⟨fun t ht hn hm => ?_, fun t ht hn oo ho ch hch s hs => ?_⟩
  · exact (refusal_none_fresh (hfr t ht hn)).1
      (List.mem_append_left _ (List.mem_map_of_mem hm))
  · have hm := (refusal_none_fresh (hfr t ht hn)).2.2
    simp only [multiFwd, ho, Option.bind_some] at hm
    rcases multiFwdIn_true_none (multiFwdIn_findTimeout hm hch) s hs with hn' | hs'
    · obtain ⟨i, hi, hip⟩ := hb t ht oo ho s (fwdSrcs_findTimeout hch s hs)
      have : (nspecAt t.core s).isSome := by
        unfold nspecAt
        rw [List.find?_isSome]
        exact ⟨i, hi, by simp [hip]⟩
      rw [hn'] at this
      exact absurd this (by simp)
    · exact hs'

/-- **Block B follows from the L5 conjunct and the split block.** Every executor that meets the
L5 agreement conjunct `CountAgrees` (its runs are `InFlight.XStep` runs by their counts) and every
split that meets `VER_004_split` (with any plan) meet block B: the split's list is `splits`, whose
atomic transitions meet the criterion of `InFlight.split_covers_executor`, and its net is the named
split net, which the flat split-net run lifts to (`ver004b_lift`). So the consistency theorem gets
block B from the two. -/
theorem VER_004_exec_of {T : Type} {E : XRel PlaceId T} {S : SplitFn PlaceId}
    {P : SplitPlanFn PlaceId} (hE : CountAgrees E) (hSP : VER_004_split S P) :
    VER_004_exec E S := by
  intro C cfg o Y sp R M0 r0 tr ds hD hex hterm hfw hO hR hat hS ht hc hds
  have hrows := ver004b_outcome_exec hO
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
  have hsr := Novel.InFlight.split_covers_executor
    (ver004b_namesUnique hD hrows) hcrit hlive hx ds hds'
  refine ⟨?_, _, hpp.filter _, hsr⟩
  rw [← ver004b_withInflight_perm (hpp.filter _)]
  rcases ver004b_split_Y hSP hat hS with ⟨rfl, rfl⟩ | ⟨hnone, rfl⟩
  · exact (ver004b_lift hO (fun _ hu _ => hu) (fun _ _ hn => absurd hn List.not_mem_nil)
      (fun _ _ hn => absurd hn List.not_mem_nil) (fun _ _ hn => absurd hn List.not_mem_nil)
      hsr).1
  · obtain ⟨hF, hone⟩ := ver004b_fresh_one hnone hfw
    exact (ver004b_lift hO (fun _ hu hn => (mem_splitNet_of hu).1 hn)
      (fun _ hu hn => (mem_splitNet_of hu).2 hn) hF hone hsr).1

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
    (hterm : ∀ p ∈ C.terminals, p ∈ cfg.terminals) (hfw : FwdFromInputs C.X.net)
    (hO : OutcomeRows C.X.net R)
    (hR : ∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R)
    (hat : o.assumeAtomicFiring = false) (hS : S cfg o C.X = .ok (Y, sp))
    (ht : XRun E C (xinit M0 r0) tr) (hc : ∀ y ∈ tr, RowsCover R y)
    (hfl : (XRun.last (xinit M0 r0) tr).fl = []) :
    Reference.Reach Y.net (qCount M0) (qCount (XRun.last (xinit M0 r0) tr).M) ∧
      Novel.InFlight.SReach R (splitTest sp) (NoTerm C) (qCount M0)
        ⟨qCount (XRun.last (xinit M0 r0) tr).M, []⟩ := by
  have hn : flNames (XRun.last (xinit M0 r0) tr) = [] := by simp [flNames, hfl]
  obtain ⟨hY, pend, hpp, hx⟩ := h C cfg o Y sp R M0 r0 tr [] hD hex hterm hfw hO hR hat hS ht hc
    ⟨by simp [hn], fun _ h => absurd h List.not_mem_nil⟩
  rw [hn, List.filter_nil, List.perm_nil] at hpp
  rw [hpp, Novel.InFlight.addAll_nil] at hx
  rw [hn, List.filter_nil, Novel.InFlight.addAll_nil] at hY
  have h0 : withInflight cfg (qCount (XRun.last (xinit M0 r0) tr).M) [] =
      qCount (XRun.last (xinit M0 r0) tr).M := by
    funext p; simp [withInflight]
  rw [h0] at hY
  exact ⟨hY, hx⟩

/-- **A safety `Proven` of the split net holds at every executor state** ([VER-004] AC4), from
the statement alone: if the split net never reaches a marking with an upward-closed property
`bad`, no executor state has it, an action in flight or not. -/
theorem VER_004_exec_safety {T : Type} {E : XRel PlaceId T} {S : SplitFn PlaceId}
    (h : VER_004_exec E S) {C : Cfg PlaceId T} {cfg : SplitCfg PlaceId} {o : Options}
    {Y : TimedNet PlaceId} {sp : List String} {R : List Novel.InFlight.Row}
    {M0 : QMarking PlaceId T} {r0 : Nat} {tr : List (XStep PlaceId T)}
    {ds : List Novel.InFlight.Row}
    (hD : NamesDistinct C.X) (hex : SplitExemptFree cfg C.X.net)
    (hterm : ∀ p ∈ C.terminals, p ∈ cfg.terminals) (hfw : FwdFromInputs C.X.net)
    (hO : OutcomeRows C.X.net R)
    (hR : ∀ u ∈ C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ R)
    (hat : o.assumeAtomicFiring = false) (hS : S cfg o C.X = .ok (Y, sp))
    (ht : XRun E C (xinit M0 r0) tr) (hc : ∀ y ∈ tr, RowsCover R y)
    (hds : Novel.InFlight.Completes R
      ((flNames (XRun.last (xinit M0 r0) tr)).filter fun n => !splitTest sp n) ds)
    {bad : AMarking → Prop} (hup : Novel.InFlight.UpClosed bad)
    (hproven : ∀ m, Reference.Reach Y.net (qCount M0) m → ¬ bad m) :
    ¬ bad (qCount (XRun.last (xinit M0 r0) tr).M) := by
  intro hb
  obtain ⟨hY, -⟩ := h C cfg o Y sp R M0 r0 tr ds hD hex hterm hfw hO hR hat hS ht hc hds
  refine hproven _ hY (hup _ _ (fun p => ?_) hb)
  exact (Novel.InFlight.le_addAll _ ds p).trans (Nat.le_add_right _ _)

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
      FwdFromInputs ver004b_C.X.net ∧ OutcomeRows ver004b_C.X.net ver004b_R ∧
      (∀ u ∈ ver004b_C.X.net.transitions, ∃ d, (toTransition u.core, d) ∈ ver004b_R) := by
  refine ⟨by unfold NamesDistinct; decide, ?_, fun _ h => absurd h List.not_mem_nil, ?_, ?_, ?_⟩
  · intro u hu
    simp only [ver004b_C, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> exact ⟨by decide, by simp [ver004b_cfg]⟩
  · intro u hu o ho s hs
    simp only [ver004b_C, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;>
      · simp only [ver004b_t, ver004b_u, Option.some.injEq] at ho
        subst ho
        simp [fwdSrcs] at hs
  · intro r hr
    simp only [ver004b_R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ver004b_t, by simp [ver004b_C], rfl, fun _ => ⟨.action 0, [1], rfl, fun _ => rfl⟩⟩
    · exact ⟨ver004b_u, by simp [ver004b_C], rfl, fun _ => ⟨.action 0, [3], rfl, fun _ => rfl⟩⟩
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
      Reference.Reach (splitTimed ver004b_cfg ["t"] ver004b_C.X).net (qCount ver004b_M)
        (withInflight ver004b_cfg (qCount (XRun.last (xinit ver004b_M 0) tr).M) ["t"]) ∧
      Novel.InFlight.SReach ver004b_R (splitTest ["t"]) (NoTerm ver004b_C) (qCount ver004b_M)
        ⟨qCount (XRun.last (xinit ver004b_M 0) tr).M, ["t"]⟩ := by
  obtain ⟨tr, ht, hc, hn, -, -, h3⟩ := ver004b_run
  obtain ⟨hD, hex, hterm, hfw, hO, hR⟩ := ver004b_premises
  refine ⟨tr, xtrace_run ht, hc, ver004b_split, hn, h3, ?_⟩
  obtain ⟨hY, pend, hpp, hx⟩ := VER_004_exec_reference ver004b_C ver004b_cfg {} _ ["t"] ver004b_R
    ver004b_M 0 tr [] hD hex hterm hfw hO hR rfl ver004b_split (xtrace_run ht) hc
    ⟨by simp [hn, splitTest], fun _ h => absurd h List.not_mem_nil⟩
  have hf : (List.filter (splitTest ["t"]) ["t"]) = ["t"] := by decide
  rw [hn, hf, Novel.InFlight.addAll_nil] at hY
  rw [hn, hf] at hpp
  have hpe : pend = ["t"] := List.perm_singleton.mp hpp
  rw [hpe, Novel.InFlight.addAll_nil] at hx
  exact ⟨hY, hx⟩

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
  obtain ⟨hD, hex, hterm, hfw, hO, hR⟩ := ver004b_premises
  obtain ⟨-, pend, -, hx⟩ := h ver004b_C ver004b_cfg {} _ [] ver004b_R ver004b_M 0 tr
    [(toTransition ver004b_t.core, [1])] hD hex hterm hfw hO hR rfl rfl (xtrace_run ht) hc
    ⟨by simp [hn, splitTest, toTransition, ver004b_t], by simp [ver004b_R]⟩
  have := (ver004b_atomic_never _ hx).2.1
  simp [Novel.InFlight.addAll, h3] at this

/-- The split that returns the right list with the wrong net: `refSplit`'s split list, but the
net unsplit. -/
def ver004b_wrongNetSplit : SplitFn PlaceId := fun cfg o X =>
  match refSplit cfg o X with
  | .ok (_, sp) => .ok (X, sp)
  | .error e => .error e

/-- ✗ **A split that returns the right list with the unsplit net does not cover the executor**:
on the example it names `t` as split, but its net never marks `inflight:t` (no transition of the
net names place `10`), while the executor has `t` in flight. -/
@[evidence forbids VER_004_exec]
theorem VER_004_exec_forbids_wrongNet :
    ¬ VER_004_exec (RefExec (N := PlaceId) (T := Nat)) ver004b_wrongNetSplit := by
  intro h
  obtain ⟨tr, ht, hc, hn, -, -, -⟩ := ver004b_run
  obtain ⟨hD, hex, hterm, hfw, hO, hR⟩ := ver004b_premises
  have hW : ver004b_wrongNetSplit ver004b_cfg {} ver004b_C.X = .ok (ver004b_C.X, ["t"]) := rfl
  obtain ⟨hY, -⟩ := h ver004b_C ver004b_cfg {} _ ["t"] ver004b_R ver004b_M 0 tr [] hD hex hterm
    hfw hO hR rfl hW (xtrace_run ht) hc
    ⟨by simp [hn, splitTest], fun _ h => absurd h List.not_mem_nil⟩
  obtain ⟨l, hrun⟩ := reach_run hY
  have h10 : (10 : PlaceId) ∉ allPlaces ver004b_C.X.net := by decide
  have := run_frame h10 hrun
  rw [hn] at this
  simp [withInflight, ver004b_cfg, splitTest, qCount, ver004b_M, Novel.InFlight.addAll] at this

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
  obtain ⟨-, pend, -, hx⟩ := h ver004b_CV ver004b_cfg {} _ [] ver004b_RV ver004b_M 0 tr
    [(toTransition ver004b_v.core, [3])] (by unfold NamesDistinct; decide)
    (fun u hu => by
      simp only [ver004b_CV, ver004b_XV, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst hu; exact ⟨by decide, by simp [ver004b_cfg]⟩)
    (fun _ h => absurd h List.not_mem_nil)
    (fun u hu o ho s hs => by
      simp only [ver004b_CV, ver004b_XV, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst hu
      simp only [ver004b_v, Option.some.injEq] at ho
      subst ho
      simp [fwdSrcs] at hs)
    (fun r hr => by
      simp only [ver004b_RV, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨ver004b_v, by simp [ver004b_CV, ver004b_XV], rfl,
        fun _ => ⟨.action 0, [3], rfl, fun _ => rfl⟩⟩)
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
  obtain ⟨-, pend, -, hx⟩ := h ver004b_CS ver004b_cfgS {} _ ["t"] ver004b_RS ver004b_MS 0 tr []
    (by unfold NamesDistinct; decide)
    (fun u hu => by
      simp only [ver004b_CS, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact ⟨by decide, by simp [ver004b_cfgS, ver004b_cfg]⟩)
    (fun p hp => by simpa [ver004b_CS, ver004b_cfgS] using hp)
    (fun u hu o ho s hs => by
      simp only [ver004b_CS, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;>
        · simp only [ver004b_tS, ver004b_uS, Option.some.injEq] at ho
          subst ho
          simp [fwdSrcs] at hs)
    (fun r hr => by
      simp only [ver004b_RS, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ver004b_tS, by simp [ver004b_CS], rfl,
          fun _ => ⟨.action 0, [4, 1], rfl, fun _ => rfl⟩⟩
      · exact ⟨ver004b_uS, by simp [ver004b_CS], rfl,
          fun _ => ⟨.action 0, [3], rfl, fun _ => rfl⟩⟩)
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
