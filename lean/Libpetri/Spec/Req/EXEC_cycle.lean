import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Req.EXEC_010

set_option linter.missingDocs true

/-!
# Executor companions of EXEC-002, EXEC-010, EXEC-013 and EXEC-020 (`spec/04-execution-model.md`)

The Phase 1 blocks of these four requirements are stated over one pass's ready order
(`EXEC_002`) and over the atomic queue firing (`EXEC_010`, `EXEC_013`, `EXEC_020`). Each of them
deferred a part of its section to the executor model of Phase 2 (`RefExec`,
`Reference/Exec.lean`): that a firing pass starts its transitions in the ready order and that one
enablement update gives one stamp (EXEC-002); that consumption and drains take the oldest tokens
of the pass-visible marking, so a same-pass deposit survives them (EXEC-010, EXEC-013); and that a
completion deposits only when it is admitted, never after the run finished, and that a timeout
outcome is deposited under the settle guard and replaces what the action wrote, and that an
accepted completion can be deposited in step 1 (EXEC-020).

The blocks of this file are second blocks with the same spec ID as the Phase 1 blocks (ruling
D33 (a), design NR-1: `<ID>_cycle`). Each is a predicate over an abstract executor
`R : XRel N T` (glossary `GlossaryExec.lean`), checked against the reference executor and against
executors that order, consume, drain or deposit otherwise. The Phase 1 blocks are not changed.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Terms read off a run -/

section Terms

variable {N T : Type}

/-- The step ends the firing pass a `begin` step opened: an `endPass`, or the `begin` of a next
pass. -/
def exec002c_ends : XStep N T → Bool
  | (_, .begin, _) | (_, .endPass, _) => true
  | _ => false

/-- The steps of a trace before its first `endPass` or `begin`: the rest of the pass a `begin`
step opened. -/
def exec002c_pass : List (XStep N T) → List (XStep N T)
  | [] => []
  | st :: rest => if exec002c_ends st then [] else st :: exec002c_pass rest

/-- The name a `start` step starts; nothing for any other step. -/
def exec002c_started : XStep N T → Option String
  | (_, .start n _, _) => some n
  | _ => none

/-- The names the `start` steps of `w` start, in order. -/
def exec002c_starts (w : List (XStep N T)) : List String := w.filterMap exec002c_started

/-- The step from `s` to `s'` newly arms the name `n` with stamp `k`: `n` holds the stamp `k`
after it and did not hold it before (glossary: Armed, "the enablement update that most recently
newly armed it"). A restart is a new arming too ([TIME-012]); an armed name that keeps its stamp
is not newly armed. -/
def exec002c_fresh (s s' : XSt N T) (n : String) (k : Nat) : Prop :=
  stampOf (s'.st n) = some k ∧ stampOf (s.st n) ≠ some k

/-- The labels whose steps may change the marking: a start, the deposit of an admitted
completion (`commit`), the deposit of a timeout outcome (`tdeposit`), the deposit of a
mid-action publication (`publish`), and an injection (`inject`). -/
def exec020c_deposits : XLbl N T → Bool
  | .start _ _ | .commit _ | .tdeposit _ | .publish _ | .inject _ => true
  | _ => false

end Terms

/-! ## EXEC-002, executor companion: the pass starts in the ready order -/

requirement EXEC_002_cycle
  id "EXEC-002"
  title "Priority-Based Firing Order (executor companion)"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  quote "*When* a firing pass starts transitions, the executor *shall* start only transitions of the ready order of that pass, in the order in which that order offers them."
        "*When* an enablement update newly arms several transitions, a restarted transition included ([TIME-012]), it *shall* give all of them one and the same stamp."
        "Equal priority and equal stamp (transitions newly armed by the enablement update of the same orchestrator cycle share one stamp, [TIME-010]): the tie breaks by ascending declaration order, so the order is fully deterministic."
  reading "For every executor R and every configuration C:"
          "in every run of R that opens with a begin step from state s, read up to the end of that pass (the next endPass or begin step), the names of its start steps, in order, are a sublist of the names of the ready order of EXEC-002 at the cycle reading of s (readyOrder C s): the pass starts only transitions of that order, each at most once, in that order;"
          "every update step gives every name it newly arms one and the same stamp: two names that hold, after the step, a stamp they did not hold before it hold the same stamp, a name the step re-stamps with a new value (a restart) included."
  assumes "This is the second block of EXEC-002 (ruling D33 (a), design NR-1). The first block, EXEC_002 (EXEC_002.lean), states the ready order as a pure function of one pass's inputs and is unchanged; this block states the two parts that block deferred to the executor model: 'That a pass starts its firings in this order is a Phase 2 behaviour line over the executor' and 'That transitions newly armed by the enablement update of one cycle share one stamp is TIME-010's stamp rule at the grain of a cycle, deferred to Phase 2 (RefExec)'. The block's kind is B, the kind of a behaviour over an executor; the markdown Kind line of EXEC-002 stays F, the kind of its first block, so the two shall sentences this block quotes are behaviour sentences under a section whose Kind line names the first block's kind (recorded for the scribe and the user)."
          "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A firing pass opens with a begin step, starts or drops (lose) the transitions of its order one at a time, and ends with an endPass step; 'fire' is read as 'start', as in TIME-014 (a firing starts in the pass and settles later, EXEC-001). Line 1 reads the steps of the pass only, from its begin step to its endPass step (or to the next begin step, for a run whose pass never ends); that no start happens outside a pass is EXEC-003's (a start takes the head of the pass's order). The witness is the reference executor RefExec (Reference/Exec.lean), which follows the Rust executor."
          "readyOrder C s is the reference order of EXEC-002 (refReadyOrder, the order the first block's holds theorem checks) over the timed view of s at its cycle reading, the reading the enablement update of the cycle took (R-EXEC-3, ruling D61 (c)); on the all-immediate fast path it is the declaration order (ruling D14 (a)). Line 1 is the first new shall sentence: a pass starts only transitions of that order, and in that order. It adds no constraint beyond other blocks: it is weaker than TIME-014's first line (the names of the start and lose steps are a prefix of the order) together with EXEC-003's first and sixth lines, and follows from them; it is stated here as EXEC-002's own per-ID reading of 'fires first' (ruling D33 (a)). That the pass does not end before it has offered every transition of the order is TIME-014's second line and EXEC-003's, not restated. An executor whose pass offers the ready transitions in descending declaration order (a scan of the enablement bitmap from the top) breaks line 1 (EXEC_002_cycle_forbids_reversedOrder)."
          "Line 2 is the second new shall sentence: one enablement update takes one firing-clock reading and gives it to every transition it newly arms. A restarted transition (TIME-012) counts as newly armed: its stamp changes from the old reading to the new one, which is the glossary entry Armed ('the enablement update that most recently newly armed it') and the sentence's parenthesis. Rust, Java and TypeScript each read the clock once per update (bitmap_backend.rs update_enablement, BitmapNetExecutor.java updateDirtyTransitions, bitmap-net-executor.ts updateDirtyTransitions). Which reading the stamp is, the cycle reading, is TIME-010's companion line, not this block's; this line says only that the stamps are equal, which is what the tie-break of AC3 needs. An executor that reads the clock again for every newly armed transition, so that two transitions armed by one update get different stamps, breaks it (EXEC_002_cycle_forbids_staggered)."
          "The three sentences of the sort list and the four shall sentences of the first block are the first block's subject, at the grain of one pass's inputs; with line 1 they apply to the starts of a pass. AC1 (priority 10 before priority 5) and AC2 (equal priority, the earlier stamp first) are the first block's third line, applied to the starts of the pass by line 1. AC3 (equal priority and equal stamp, ascending declaration order) is the first block's second line for the order, line 2 for 'share one stamp', and line 1 for 'fires': EXEC_002_cycle_nonvacuous shows four transitions of one priority armed by one update at stamp 0 and started in declaration order. AC4 (every backend produces the identical ready order) is the first block's, cited from Sched.lean and Refinement.lean; both backends are runs of RefExec (CONC-020, a later block)."
          "The test derivation (priorities 5, 10, 5, enabled together, fired P10 then P5 then P5) is the first block's example applied to the starts of a pass by line 1. The decided runs here take the all-immediate path, because the kernel does not evaluate the general path's merge sort on two or more ready transitions (as in EXEC-003 and TIME-014); line 1 reads the order through readyOrder whatever path the net takes."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R =>
      (∀ C s s' tr, XRun R C s ((s, .begin, s') :: tr) →
        List.Sublist (exec002c_starts (exec002c_pass tr)) ((readyOrder C s).map (·.core.name))) ∧
      ∀ C, on (fun s s' => R C s .update s'), shall (fun s s' =>
        ∀ n m k k', exec002c_fresh s s' n k → exec002c_fresh s s' m k' → k = k')

/- The pinned readable form of the companion: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_002_cycle : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  (∀ (C : Cfg N T) (s s' : XSt N T) (tr : List (XStep N T)),
      XRun R C s ((s, XLbl.begin, s') :: tr) →
        (exec002c_starts (exec002c_pass tr)).Sublist (List.map (fun x => x.core.name) (readyOrder C s))) ∧
    ∀ (C : Cfg N T),
      on fun s s' => R C s XLbl.update s', shall fun s s' =>
        ∀ (n m : String) (k k' : ℕ), exec002c_fresh s s' n k → exec002c_fresh s s' m k' → k = k'
-/
#guard_msgs in #print EXEC_002_cycle

/-! ## EXEC-010, executor companion: oldest first from the pass-visible marking -/

requirement EXEC_010_cycle
  id "EXEC-010"
  title "FIFO Token Consumption (executor companion)"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  quote "When a transition fires, it consumes tokens from the oldest-first (FIFO) end of each input place's queue."
        "*When* a transition starts in a firing pass, it *shall* remove from each of its input places that is neither a reset place nor a correlated input of its match specification the oldest tokens the place holds, as many as the consumption count of the input arc counted on the pass-visible marking ([EXEC-003])."
        "*When* a transition starts in a firing pass, its action *shall* receive from each of its input places that is not a correlated input of its match specification the oldest tokens the place holds, as many as that consumption count, in queue order."
  reading "For every executor R, every configuration C and every start step of a name n in R, from state s to state s', if the head of the pass's order in s is a transition t named n (the transition the step starts), then:"
          "every input place p of t that is not a reset place of t holds in s' the queue it held in s without its oldest k tokens, where k is the consumption count of t's input arc on p at the pass-visible counts of s (Consumes t (Counts (vis s)) p);"
          "every firing in flight in s' that was not in flight in s is handed, from every input place p of t, the oldest k tokens of p's queue in s, in queue order, for the same k."
  assumes "This is the second block of EXEC-010 (ruling D33 (a), design NR-1). The first block, EXEC_010 (EXEC_010.lean), states FIFO consumption over the atomic queue firing and is unchanged; it deferred same-pass deposits to the executor model: 'Same-pass deposits (EXEC-003 AC5: a draining arc ships the pass-start count, not the live one) need the cycle relation of Phase 2 (RefExec) and are deferred to it'. This block is that executor line."
          "The model is an executor R : XRel N T (glossary GlossaryExec.lean). The witness is the reference executor RefExec (Reference/Exec.lean). 'Fires' is read as 'starts in a firing pass': the start step consumes and hands the action its tokens, and the action runs after it. The started transition is named, not constrained: both lines read 'if the head of the pass's order is t and t is named n', so a start of a transition other than the head is left to EXEC-003's first line (a start takes the head of the order, named n) and TIME-014, which forbid it. Both lines read every start step, while the sentences speak of a start in a firing pass; that a start happens only in a pass is EXEC-001's (step 5 is the firing pass) and EXEC-003's (a start takes the head of the pass's order), so the two readings agree on the runs those blocks allow, and the lines are stronger elsewhere. The pass-visible marking is the derived term vis s (EXEC-003): each queue without the tokens deposited inside the current pass, which sit at its tail (EXEC-020). vis and hid are read off the executor's own record of the same-pass deposits; that the record holds exactly the tokens deposited earlier in the pass is EXEC-003's lines 2, 5 and 8, so the lines mean 'the tokens a synchronous action deposited earlier in the pass' only jointly with EXEC-003."
          "Both lines are consequences of EXEC-003's first two lines, restated per place under ruling D33 (a): EXEC-003's second line fixes the marking after a start to the pass-visible marking with t's consumption applied, followed by the same-pass tail, and the delivery to the pass-visible prefix, and its first line makes t enabled on the pass-visible marking, so the consumption count is at most the pass-visible length. The reference proof (EXEC_010_cycle_reference, exec010c_drop_take and exec010c_take_take) is that derivation. The new sentences repeat EXEC-003's 'consume, drain and hand its action only tokens of the pass-visible marking' at the grain of EXEC-010's oldest-first rule and add no constraint beyond it."
          "Line 1 is the first new shall sentence, and the first quoted sentence at the grain of a pass: the start removes the oldest tokens of the whole queue, so a token deposited earlier in the same pass, which sits at the tail, is not consumed. The count is taken on the pass-visible marking (EXEC-003 AC4 and AC5), so an all() or atLeast(n) input takes the pass-visible tokens only: a start that counts the live marking swallows the deposit (EXEC_010_cycle_forbids_drainSwallows), and one that takes the newest pass-visible tokens breaks the oldest-first rule (EXEC_010_cycle_forbids_newest). A reset place is left to EXEC-013's companion: an input place that is also a reset place keeps only its same-pass tail."
          "Line 2 is the second new shall sentence: what the action receives from each input place is that oldest prefix, in queue order. An executor that removes the right tokens and hands them to the action newest first breaks it (EXEC_010_cycle_forbids_reversedDelivery). Read arcs are EXEC-012's and EXEC-003's line 2 (the delivery is taken on the pass-visible marking). Line 2 holds of a start that puts no new firing in flight, which hands nothing; that a start puts exactly one new firing in flight is CONC-002's second line (the firings in flight after a start are a permutation of the new firing and those before it), not restated."
          "Correlated inputs (ruling D16): the reference start takes no ν-net match specification (Trans has no match-specification field), so every input place is an input that is not a correlated input, as in the first block, and both lines read every input place. The sentences' exemption 'that is not a correlated input of its match specification' therefore has no counterpart here: on the nets this model holds the lines say what the sentences say, and the exemption itself, with the correlated take, is NU-020's (W9), not encoded."
          "AC1 to AC3 (One, Exactly(2) and All on tokens A, B, C) are the first block's examples. At the grain of a pass EXEC_010_cycle_nonvacuous shows an all() input that takes the pass-visible token 3 and leaves the same-pass deposit 8, and an exactly(2) input that takes 10 and 11 of 10, 11, 12, hands the action 10 then 11 and leaves 12. The test derivation is the first block's."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C n sy,
      (on (fun s s' => R C s (.start n sy) s'), shall (fun s s' =>
        ∀ t rest, s.order = t :: rest → t.core.name = n →
          ∀ p ∈ inPlaces t, ¬ ResetArc t p →
            s'.M p = (s.M p).drop (Consumes t (Counts (vis s)) p))) ∧
      (on (fun s s' => R C s (.start n sy) s'), shall (fun s s' =>
        ∀ t rest, s.order = t :: rest → t.core.name = n →
          ∀ f ∈ s'.fl, f ∉ s.fl → ∀ p ∈ inPlaces t,
            f.deliv.inputs p = OldestFirst s.M p (Consumes t (Counts (vis s)) p)))

/- The pinned readable form of the companion: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_010_cycle : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T) (n : String) (sy : Bool),
    (on fun s s' => R C s (XLbl.start n sy) s', shall fun s s' =>
        ∀ (t : Reference.Trans N) (rest : List (Reference.Trans N)),
          s.order = t :: rest →
            t.core.name = n →
              ∀ p ∈ inPlaces t, ¬ResetArc t p → s'.M p = List.drop (Consumes t (Counts (vis s)) p) (s.M p)) ∧
      on fun s s' => R C s (XLbl.start n sy) s', shall fun s s' =>
        ∀ (t : Reference.Trans N) (rest : List (Reference.Trans N)),
          s.order = t :: rest →
            t.core.name = n →
              ∀ f ∈ s'.fl,
                f ∉ s.fl → ∀ p ∈ inPlaces t, f.deliv.inputs p = OldestFirst s.M p (Consumes t (Counts (vis s)) p)
-/
#guard_msgs in #print EXEC_010_cycle

/-! ## EXEC-013, executor companion: the drain at the start, same-pass deposits kept -/

requirement EXEC_013_cycle
  id "EXEC-013"
  title "Reset Arc Execution (executor companion)"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  quote "This happens during the firing step, before the action executes."
        "*When* a transition fires, it *shall* drain each of its reset places ([CORE-034]) before its action starts."
        "A token a synchronous action deposited earlier in the same firing pass survives the drain ([EXEC-003] AC5)."
        "*When* a transition starts in a firing pass, it *shall* drain each of its reset places in that same step, so the place keeps exactly the tokens a synchronous action deposited there earlier in the pass."
  reading "For every executor R, every configuration C and every start step of a name n in R, from state s to state s': if the head of the pass's order in s is a transition t named n (the transition the step starts), then every reset place p of t holds in s' exactly the tokens deposited inside the current pass (the hidden tail hid s p of the pass-visible marking)."
  assumes "This is the second block of EXEC-013 (ruling D33 (a), design NR-1). The first block, EXEC_013 (EXEC_013.lean), states the order of the parts of one atomic queue firing and is unchanged; it deferred 'The body sentence: A token a synchronous action deposited earlier in the same firing pass survives the drain ([EXEC-003] AC5)' and the deposits of an action's publications to the executor model. This block is that executor line."
          "The model is an executor R : XRel N T (glossary GlossaryExec.lean); the witness is the reference executor RefExec (Reference/Exec.lean). 'Fires' is read as 'starts in a firing pass'. The firing step of the first quoted sentence is the start step: the drain happens in it, and the action's steps (write, flush, ret) can only follow it, because the firing is in flight only from its start. So the drain is 'before its action starts' (the first shall sentence) and the action's output, deposited later at the tails (EXEC-020, EXEC-021, CONC-003), is never drained by its own firing. A start that leaves the reset places as they are, deferring the drain past the action's start, breaks the line (EXEC_013_cycle_forbids_drainLate)."
          "The line is the new shall sentence and the third quoted sentence: the drain takes the pass-visible tokens only (EXEC-003 AC5), so the place keeps exactly its same-pass tail; an input place that is also a reset place keeps it too. A start that drains the live marking swallows the deposit (EXEC_013_cycle_forbids_drainSwallows). The tail is the derived term hid s (EXEC-003); outside a firing pass it is empty, and the line says the place ends the start empty."
          "The started transition is named, not constrained, as in EXEC-010's companion: the line reads 'if the head of the pass's order is t and t is named n', and that a start takes the head is EXEC-003's first line. The line reads every start step, while the sentence speaks of a start in a firing pass; a start happens only in a pass by EXEC-001 and EXEC-003. hid is read off the executor's own record of the same-pass deposits, so 'the tokens a synchronous action deposited there earlier in the pass' is the line's meaning only jointly with EXEC-003's lines 2, 5 and 8, which fix how that record evolves. The line is a consequence of EXEC-003's second line (a reset place, which qConsume empties, keeps its same-pass tail), restated for EXEC-013 under ruling D33 (a); it adds no constraint beyond it."
          "The other quoted sentences of the first block (consumption, then read peeks, then draining; the read token of a read and reset place; an unmarked reset place blocks nothing) are its subject, applied by EXEC-003's line 2 to the pass-visible marking; they are not restated. Tokens an action published before it completed land at the tails by a publish step, after the start that drained, and stay whatever happens to the completion (ruling D17): that is CONC-003's second line and EXEC-021's second line, with this line placing the drain before them. The clock restart of AC3 is TIME-012's companion (the restart flag set at the start from the live intermediate marking, ruling D7)."
          "AC1 (five tokens, all removed), AC2 (empty reset place, no error) and AC4 (draining after read peeking) are the first block's. AC3 is TIME-012's. At the grain of a pass EXEC_013_cycle_nonvacuous shows a reset place holding the old token 5 and the same-pass deposit 6: the start drains 5 and keeps 6. The test derivation is the first block's."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C n sy,
      on (fun s s' => R C s (.start n sy) s'), shall (fun s s' =>
        ∀ t rest, s.order = t :: rest → t.core.name = n →
          ∀ p, ResetArc t p → s'.M p = hid s p)

/- The pinned readable form of the companion: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_013_cycle : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T) (n : String) (sy : Bool),
    on fun s s' => R C s (XLbl.start n sy) s', shall fun s s' =>
      ∀ (t : Reference.Trans N) (rest : List (Reference.Trans N)),
        s.order = t :: rest → t.core.name = n → ∀ (p : N), ResetArc t p → s'.M p = hid s p
-/
#guard_msgs in #print EXEC_013_cycle

/-! ## EXEC-020, executor companion: only admitted completions deposit -/

requirement EXEC_020_cycle
  id "EXEC-020"
  title "Output Token Deposition (executor companion)"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  quote "It never admits the completion of a firing that ended with its timeout outcome ([EXEC-022], [IO-013]), that a stop on a terminal place abandoned ([EXEC-042]) or that an immediate termination abandoned ([ENV-015])."
        "*If* the completion of an action is not admitted, or output validation rejects the produced tokens, *then* the executor *shall not* deposit any token the action produced at completion."
        "A publication still queued when a terminal place stops the run ([EXEC-042]) is discarded."
        "*When* the executor deposits the tokens an action produced at completion, it *shall* do so only in the step that admits that completion, while the run is under way and no terminal place is marked, and *shall* add them at the tails of their places' queues in the order the action produced them."
        "The executor *shall* change the marking only when it starts a transition, deposits the tokens of an admitted completion, deposits a timeout outcome ([EXEC-022]), deposits a mid-action publication ([IO-015]) or injects an external event ([ENV-003])."
        "*When* a run has finished ([EXEC-041]), the executor *shall not* change the marking, so a completion, a timeout outcome or a publication that is still in flight or queued deposits nothing."
        "*When* the executor deposits the timeout outcome of a firing ([EXEC-022], [IO-013]), it *shall* do so only in a step in which a completion of that firing would be admitted, while the run is under way and no terminal place is marked, and *shall* add exactly the tokens of that outcome at the tails of their places' queues, in the order of the outcome."
        "*When* the executor admits the completion of an action and output validation does not reject the produced tokens ([EXEC-021], [CONC-026]), the executor *shall* add each produced token at the tail of its place's queue, in the order the action produced the tokens."
  reading "For every executor R and every configuration C:"
          "a commit step of a firing identity i, from state s to state s', settles an admitted completion of i (glossary: Admitted completion: the run is under way, no terminal place is marked, the outcome of i is queued, it returned normally with emission e, and the phase allows it) whose emission output validation accepts, and leaves in s' the marking of s with e appended at the tails, in emission order;"
          "a step whose label is not a start, a commit, a tdeposit, a publish or an inject leaves the marking unchanged;"
          "a step from a state whose run has finished leaves the marking unchanged;"
          "a tdeposit step of i, from s to s', settles a firing of i whose outcome is a timeout outcome e, under the guard every settle shares (canSettle: the run is under way, no terminal place is marked, the outcome of i is queued, and the phase allows settling it), and leaves in s' the marking of s with e appended at the tails, in the order of e;"
          "in step 1 (phase completions), every admitted completion of i with emission e that output validation and the relay check accept can be deposited: R offers a commit step of i."
  assumes "This is the second block of EXEC-020 (ruling D33 (a), design NR-1). The first block, EXEC_020 (EXEC_020.lean), states the tail deposit of the atomic queue firing and is unchanged; it deferred to the executor model the sentence 'If the completion of an action is not admitted, or output validation rejects the produced tokens, then the executor shall not deposit any token the action produced at completion.', AC3 and AC4, and the paragraph on mid-action publications. This block is those executor lines."
          "The model is an executor R : XRel N T (glossary GlossaryExec.lean); the witness is the reference executor RefExec (Reference/Exec.lean). Naming: 'admits the completion' is the glossary term Admitted completion (AdmittedCompletion C s i f e): the executor takes the completion up in step 1, on the wake of the wait (ruling D70 (a)) or, for a synchronous action, inside its firing pass, while the run is under way and no terminal place is marked, and not in step 1 or the wait after an immediate termination (ENV-015). A completion it deposits is a commit step; one it rejects is a fail step (EXEC-021); 'the tokens an action produced at completion' is the emission e the action returned. The outside steps (the action writing, flushing, returning, its budget expiring, a caller's request) are CONC-001's."
          "Line 1 is the first new shall sentence: the deposit happens only in the step that admits the completion and appends the emission at the tails in emission order (the first block's line 1 at this grain). It covers the sentence 'It never admits ...' for the terminal stop and the immediate termination: an executor that deposits a completion while a terminal place is marked breaks it (EXEC_020_cycle_forbids_admitWhenTerminal), and so does one that deposits the emission in reverse order (EXEC_020_cycle_forbids_reversed). Line 1 also requires output validation to accept the emission (the places validation reads, validIn), so the validation half of the deferred shall-not sentence is this block's own: an executor whose commit step deposits an emission validation rejects breaks it (EXEC_020_cycle_forbids_commitUnvalidated). EXEC-021's first line states the same check from validation's side, with the relay check; which tokens the emission holds (those written after the last flush) is CONC-003's first line."
          "The 'only' of the first new shall sentence is lines 1 and 2 together with three blocks that fix what the other marking-changing steps deposit: a start removes and keeps tokens only as EXEC-003's second line says and adds none, a publish deposits exactly the oldest queued batch (CONC-003's first line), and an inject deposits exactly the injected token (ENV-003). Within this block alone an executor whose start, publish or inject step also appended a returned emission would pass lines 1 and 2; those blocks forbid it."
          "Line 2 is the second new shall sentence, the frame of every other step, outside steps included. With line 1 it is the deferred shall-not sentence: a completion that is not admitted or that validation rejects is settled by a fail step or not at all, and no step but a commit deposits its emission. An executor whose fail step deposits the rejected emission anyway breaks it (EXEC_020_cycle_forbids_failDeposits). The queue of publications on a fail step is EXEC-021's second line."
          "Line 3 is the third new shall sentence, and the quoted 'A publication still queued when a terminal place stops the run ([EXEC-042]) is discarded.' after the finish step: once the run has finished (the finish step of EXEC-041; a terminal stop, a quiescent or closed finish, an immediate termination), no step changes the marking, so an action still in flight that returns, a queued completion and a queued publication deposit nothing. An executor that keeps the publication queue across a terminal stop and deposits it afterwards breaks it (EXEC_020_cycle_forbids_publishAfterStop). Between the step that marks a terminal place and the finish step, line 2 still allows a publish step to change the marking; there the quoted sentence is EXEC-042's first line, which forbids every executor step but finish terminal while a terminal place is marked, and line 1 and line 4 keep commit and tdeposit out by their guard. That the finish step itself keeps the marking is EXEC-041's."
          "Line 4 is the fourth new shall sentence, the timeout half of 'It never admits ...': a timeout deposit settles the firing under the guard every settle step shares (canSettle, the guard of an admitted completion: the run is under way, no terminal place is marked, the outcome is queued, the phase allows settling it, and in step 1 or the wait no immediate termination was requested, ENV-015), and deposits exactly the outcome, in its order. An executor that deposits a timeout outcome while a terminal place is marked breaks it (EXEC_020_cycle_forbids_tdepositWhenTerminal); one that merges the action's unpublished writes into the outcome at the deposit breaks it (EXEC_020_cycle_forbids_mergeOnTimeout). The deposit is the outcome recorded on the firing (f.out); that the expiry step records a timeout outcome of the Timeout node and not the action's writes is EXEC-022's first line (exec022_QOutcome) with IO-013 and IO-014 (Cfg.timeoutOut), so 'not what the action wrote after its last publication' (AC3, the test derivation's timeout case) is line 4 together with EXEC-022's first line. The relay check on the outcome is EXEC-021's fifth line; that the expiry is offered only for an asynchronous firing with a Timeout node is EXEC-022's. Line 4 contains EXEC-022's deposit line (the same deposit, stated from the timeout's side) and adds the settle guard."
          "Line 5 is the shall sentence 'When the executor admits the completion of an action and output validation does not reject the produced tokens ..., the executor shall add each produced token ...' at the grain of the executor: lines 1 to 4 constrain the steps that occur, so without line 5 an executor that never deposits an accepted completion would satisfy them, and no line of EXEC-001 or EXEC-040 obliges a step to happen (EXEC-001's assumes: 'nothing here obliges a step to happen'). Line 5 says the commit is offered in step 1 for every admitted completion that validation and the relay check accept; EXEC-001's fourth line (no publication, injection or start before the queued outcome is settled) and EXEC-021's third line (a fail step only for an error, a rejected emission or a rejected relay) then leave the commit as the only way on. It is read in step 1 only: TypeScript settles every firing in step 1 and never inside the pass (EXEC-003), and Rust's settle in the wait goes on to step 1 (ruling D70 (a)), so an offer in the pass or the wait would hold of one runtime and not another. The relay check is NU-054's, carried by EXEC-021; with it accepted, the reference commit rule needs nothing else. An executor that never commits breaks line 5 (EXEC_020_cycle_forbids_neverCommits). That the loop goes on at all is CONC-010's and EXEC-040's."
          "The two sentences of the body before the shall sentences ('After an action completes and the executor admits the completion, ...' and 'Each token is added to the end of the target place's FIFO queue, in the order the action produced it.') and the paragraph defining a completion and admission are the first block's lines and this block's naming; 'A close ([ENV-013]) waits for in-flight actions and admits their completions.' is ENV-013's. The mid-action publication paragraph is CONC-003's (each batch deposited once, oldest first, at the tails, whatever happens to the completion, ruling D17) and line 3 with EXEC-042's first line (discarded at a terminal stop)."
          "AC1 (V at the end of P's queue) and AC2 (several tokens to one place, in order) are lines 1 and 5: EXEC_020_cycle_nonvacuous deposits 30 then 31 into a place holding 40, which ends 40, 30, 31; unlike the first block, the executor model witnesses AC2 in the joint model, because validation reads sets of places (IO-015). AC3 (not admitted: the timeout outcome, or a terminal stop while the action was in flight) is line 4 with EXEC-022's first line and lines 1 and 3 with EXEC-042's first line: the example deposits the timeout outcome 5 and not the 50 the action wrote, and an abandoned firing returns after a terminal stop without a deposit. AC4 (validation fails, nothing deposited) is lines 1 and 2: the example fails a firing whose emission validation rejects and leaves its place empty. The test derivation (three tokens in order; a timeout budget outlived; a write outside the chosen branch) is these examples."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ i, on (fun s s' => R C s (.commit i) s'), shall (fun s s' =>
        ∃ f e, AdmittedCompletion C s i f e ∧ C.validate f.t (validIn f e) = true ∧
          s'.M = qAppend s.M e)) ∧
      (∀ l, exec020c_deposits l = false →
        on (fun s s' => R C s l s'), shall (fun s s' => s'.M = s.M)) ∧
      (on (fun s s' => isExecPhase s.phase = false ∧ ∃ l, R C s l s'),
        shall (fun s s' => s'.M = s.M)) ∧
      (∀ i, on (fun s s' => R C s (.tdeposit i) s'), shall (fun s s' =>
        ∃ f e, s.fl.find? (·.id == i) = some f ∧ f.out = some (.timedOut e) ∧
          canSettle C s i f = true ∧ s'.M = qAppend s.M e)) ∧
      (∀ i s f e, s.phase = .completions → AdmittedCompletion C s i f e →
        C.validate f.t (validIn f e) = true → C.relay f.t f.deliv e = true →
        ∃ s', R C s (.commit i) s')

/- The pinned readable form of the companion: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_020_cycle : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (i : ℕ),
        on fun s s' => R C s (XLbl.commit i) s', shall fun s s' =>
          ∃ f e, AdmittedCompletion C s i f e ∧ C.validate f.t (validIn f e) = true ∧ s'.M = qAppend s.M e) ∧
      (∀ (l : XLbl N T), exec020c_deposits l = false → on fun s s' => R C s l s', shall fun s s' => s'.M = s.M) ∧
        (on fun s s' => isExecPhase s.phase = false ∧ ∃ l, R C s l s', shall fun s s' => s'.M = s.M) ∧
          (∀ (i : ℕ),
              on fun s s' => R C s (XLbl.tdeposit i) s', shall fun s s' =>
                ∃ f e,
                  List.find? (fun x => x.id == i) s.fl = some f ∧
                    f.out = some (Outcome.timedOut e) ∧ canSettle C s i f = true ∧ s'.M = qAppend s.M e) ∧
            ∀ (i : ℕ) (s : XSt N T) (f : Firing N T) (e : List (N × T)),
              s.phase = Phase.completions →
                AdmittedCompletion C s i f e →
                  C.validate f.t (validIn f e) = true → C.relay f.t f.deliv e = true → ∃ s', R C s (XLbl.commit i) s'
-/
#guard_msgs in #print EXEC_020_cycle

/-! ## The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- A step that is not `begin`, `start` or `lose` keeps the pass's order. -/
theorem exec002c_xstepW_order {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hb : l ≠ .begin) (hs : ∀ n sy, l ≠ .start n sy)
    (hl : ∀ n, l ≠ .lose n) : s'.order = s.order := by
  cases l with
  | begin => exact absurd rfl hb
  | start n sy => exact absurd rfl (hs n sy)
  | lose n => exact absurd rfl (hl n)
  | finish c =>
    cases c <;> simp only [xstepW] at h <;> split at h <;> simp at h <;> subst h <;> rfl
  | _ =>
    simp only [xstepW, writeStep, flushStep, retStep, expireStep, requestStep, drainStep,
      closeStep, terminateStep, commitStep, failStep, tdepositStep, depositAt, settle,
      publishStep, injectStep, discardStep, snapshotStep, parkStep, wakeStep, onOpen] at h
    all_goals (repeat' split at h) <;> (try simp at h) <;> (try (subst h; rfl))

/-- In a reference run from `s`, the names the `start` steps before the first `endPass` or
`begin` start are
a sublist of the names of the order of `s`: `start` and `lose` take the head, and no other step
changes the order. -/
theorem exec002c_window {C : Cfg N T} :
    ∀ (tr : List (XStep N T)) (s : XSt N T), XRun RefExec C s tr →
      List.Sublist (exec002c_starts (exec002c_pass tr)) (s.order.map (·.core.name))
  | [], s, _ => by simp [exec002c_pass, exec002c_starts]
  | (s0, l, s1) :: tr, s, hr => by
    obtain ⟨rfl, hs, hr'⟩ := hr
    dsimp only at hs hr'
    have ih := exec002c_window tr s1 hr'
    cases l with
    | begin => simp [exec002c_pass, exec002c_ends, exec002c_starts]
    | endPass => simp [exec002c_pass, exec002c_ends, exec002c_starts]
    | start n sy =>
      obtain ⟨t, rest, ho, -, -, -, hn, -, -, h1⟩ := startStep_some hs
      have h1o : s1.order = rest := by rw [h1]
      rw [h1o] at ih
      subst hn
      simpa [exec002c_pass, exec002c_ends, exec002c_starts, exec002c_started, ho] using ih
    | lose n =>
      obtain ⟨t, rest, ho, -, -, -, hn, -, h1⟩ := loseStep_some hs
      have h1o : s1.order = rest := by rw [h1]
      rw [h1o] at ih
      have := ih.cons t.core.name
      simpa [exec002c_pass, exec002c_ends, exec002c_starts, exec002c_started, ho] using this
    | _ =>
      rw [exec002c_xstepW_order hs nofun nofun nofun] at ih
      simpa [exec002c_pass, exec002c_ends, exec002c_starts, exec002c_started] using ih

/-- The reference update gives every name it newly arms the host reading of the step. -/
theorem exec002c_updSt_fresh {C : Cfg N T} {s : XSt N T} {n : String} {k : Nat}
    (h1 : stampOf (updSt refXPol C s n) = some k) (h2 : stampOf (s.st n) ≠ some k) :
    k = s.now := by
  unfold updSt at h1
  split at h1
  · simp [stampOf] at h1
  · simp only at h1
    split at h1
    · rename_i k0 rs hst
      split at h1
      · split at h1
        · simp [stampOf, refXPol] at h1; omega
        · simp only [stampOf, Option.some.injEq] at h1
          subst h1
          simp [hst, stampOf] at h2
      · simp [stampOf] at h1
    · split at h1
      · simp [stampOf, refXPol] at h1; omega
      · simp [stampOf] at h1
    · simp [refXPol, stampOf] at h1

end Reference

/-- ✓ The reference executor satisfies the executor companion of EXEC-002: its `begin` step sets
the pass's order to `readyOrder` (`xstepW_begin`), its `start` and `lose` steps take the head, no
other step changes the order (`exec002c_window`), and its update stamps every newly armed name
with the one host reading of the step (`exec002c_updSt_fresh`). -/
@[evidence holds EXEC_002_cycle]
theorem EXEC_002_cycle_reference {N T : Type} [DecidableEq N] :
    EXEC_002_cycle (RefExec (N := N) (T := T)) := by
  refine ⟨fun C s s' tr hr => ?_, fun C s s' hs => ?_⟩
  · obtain ⟨-, hb, hr'⟩ := hr
    dsimp only at hb hr'
    have ho : s'.order = readyOrder C s := by rw [(xstepW_begin hb).2.2.2.2]
    have := exec002c_window tr s' hr'
    rwa [ho] at this
  · obtain ⟨-, -, rfl⟩ := xstepW_update hs
    intro n m k k' hn hm
    rw [exec002c_updSt_fresh hn.1 hn.2, exec002c_updSt_fresh hm.1 hm.2]

section Reference2

variable {N T : Type} [DecidableEq N]

omit [DecidableEq N] in
/-- Dropping `k` tokens from a prefix of a queue and keeping the rest of the queue behind it is
dropping `k` tokens from the queue, when the prefix holds at least `k`. -/
theorem exec010c_drop_take {l : List T} {j k : Nat} (h : k ≤ (l.take j).length) :
    (l.take j).drop k ++ l.drop j = l.drop k := by
  conv_rhs => rw [← List.take_append_drop j l]
  rw [List.drop_append_of_le_length h]

omit [DecidableEq N] in
/-- The first `k` tokens of a prefix holding at least `k` are the first `k` of the queue. -/
theorem exec010c_take_take {l : List T} {j k : Nat} (h : k ≤ (l.take j).length) :
    (l.take j).take k = l.take k := by
  rw [List.take_take]
  congr 1
  simp only [List.length_take] at h
  omega

/-- A reference start of the head `t` takes from no input place more than the pass-visible
queue holds. -/
theorem exec010c_le {s : XSt N T} {t : Trans N}
    (he : enabledNA (qCount (vis s)) t.core = true) (p : N) :
    Consumes t (Counts (vis s)) p ≤ (vis s p).length :=
  exec010_consumes_le (t := t) (m := qCount (vis s)) he p

end Reference2

/-- ✓ The reference executor satisfies the executor companion of EXEC-010: its start leaves every
input place that is not reset with the pass-visible queue without its consumed prefix, followed by
the same-pass tail (`liveAfter`), which is the queue without its oldest tokens, and hands the new
firing the consumed prefix (`qDelivered (vis s) t`). -/
@[evidence holds EXEC_010_cycle]
theorem EXEC_010_cycle_reference {N T : Type} [DecidableEq N] :
    EXEC_010_cycle (RefExec (N := N) (T := T)) := by
  intro C n sy
  refine ⟨fun s s' h t' rest' ho' _ p _ hr => ?_, fun s s' h t' rest' ho' _ f hf hnf p _ => ?_⟩
  · obtain ⟨t, rest, ho, -, -, -, -, -, he, rfl⟩ := startStep_some h
    rw [ho] at ho'
    obtain ⟨rfl, rfl⟩ := List.cons.inj ho'
    show liveAfter s t p = _
    have hr' : p ∉ t.core.resets := hr
    simp only [liveAfter, qConsume, if_neg hr', qPostInput]
    exact exec010c_drop_take (exec010c_le he p)
  · obtain ⟨t, rest, ho, -, -, -, -, -, he, rfl⟩ := startStep_some h
    rw [ho] at ho'
    obtain ⟨rfl, rfl⟩ := List.cons.inj ho'
    simp only [List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact absurd hf hnf
    · exact exec010c_take_take (exec010c_le he p)

/-- ✓ The reference executor satisfies the executor companion of EXEC-013: its start drains every
reset place of the head on the pass-visible queue (`qConsume` empties it) and keeps the same-pass
tail behind it (`liveAfter`). -/
@[evidence holds EXEC_013_cycle]
theorem EXEC_013_cycle_reference {N T : Type} [DecidableEq N] :
    EXEC_013_cycle (RefExec (N := N) (T := T)) := by
  intro C n sy s s' h t' rest' ho' _ p hr
  obtain ⟨t, rest, ho, -, -, -, -, -, -, rfl⟩ := startStep_some h
  rw [ho] at ho'
  obtain ⟨rfl, rfl⟩ := List.cons.inj ho'
  have hr' : p ∈ t.core.resets := hr
  show liveAfter s t p = _
  simp [liveAfter, qConsume, hr']

section Reference3

variable {N T : Type} [DecidableEq N]

/-- A reference step whose label is not a start, a commit, a tdeposit, a publish or an inject
leaves the marking unchanged. -/
theorem exec020c_xstepW_M {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') (hl : exec020c_deposits l = false) : s'.M = s.M := by
  cases l with
  | start n sy => simp [exec020c_deposits] at hl
  | commit i => simp [exec020c_deposits] at hl
  | tdeposit i => simp [exec020c_deposits] at hl
  | publish i => simp [exec020c_deposits] at hl
  | inject k => simp [exec020c_deposits] at hl
  | begin => rw [(xstepW_begin h).2.2.2.2]
  | lose n =>
    obtain ⟨t, rest, -, -, -, -, -, -, h1⟩ := loseStep_some h
    rw [h1]
  | endPass => rw [(xstepW_endPass h).2.2.2.2]
  | finish c =>
    cases c <;> simp only [xstepW] at h <;> split at h <;> simp at h <;> subst h <;> rfl
  | _ =>
    simp only [xstepW, writeStep, flushStep, retStep, expireStep, requestStep, drainStep,
      closeStep, terminateStep, failStep, settle, discardStep, snapshotStep, parkStep, wakeStep,
      onOpen] at h
    all_goals (repeat' split at h) <;> (try simp at h) <;> (try (subst h; rfl))

end Reference3

/-- ✓ The reference executor satisfies the executor companion of EXEC-020: its `commit` rule
requires `canSettle` and validation and deposits by `depositAt` (`commitStep_some`), every other
rule but `start`, `tdeposit`, `publish` and `inject` keeps the marking (`exec020c_xstepW_M`),
none of those five is offered once the run has finished, `tdeposit` requires `canSettle` and
deposits the timeout outcome (`tdepositStep_some`), and the `commit` rule fires on every
admitted completion that validation and the relay check accept. -/
@[evidence holds EXEC_020_cycle]
theorem EXEC_020_cycle_reference {N T : Type} [DecidableEq N] :
    EXEC_020_cycle (RefExec (N := N) (T := T)) := by
  intro C
  refine ⟨fun i s s' h => ?_, fun l hl s s' h => exec020c_xstepW_M h hl,
    fun s s' ⟨hph, l, h⟩ => ?_, fun i s s' h => ?_, fun i s f e _ hadm hv hr => ?_⟩
  · obtain ⟨f, e, hf, he, hc, hv, -, rfl⟩ := refExec_commit h
    exact ⟨f, e, ⟨hf, he, hc⟩, hv, rfl⟩
  · cases hd : exec020c_deposits l
    · exact exec020c_xstepW_M h hd
    · cases l with
      | start n sy =>
        obtain ⟨-, -, -, hp, -⟩ := startStep_some h
        simp [hp, isExecPhase] at hph
      | commit i =>
        obtain ⟨f, e, -, -, hc, -⟩ := refExec_commit h
        simp [canSettle, hph] at hc
      | tdeposit i =>
        obtain ⟨f, e, -, -, hc, -⟩ := tdepositStep_some h
        simp [canSettle, hph] at hc
      | publish i =>
        obtain ⟨-, -, -, -, hp, -⟩ := publishStep_some h
        rcases hp with hp | ⟨hp, -⟩ <;> simp [hp, isExecPhase] at hph
      | inject k =>
        obtain ⟨-, -, -, -, -, -, hp, -⟩ := injectStep_some h
        rcases hp with hp | hp <;> simp [hp, isExecPhase] at hph
      | _ => simp [exec020c_deposits] at hd
  · obtain ⟨f, e, hf, he, hc, -, rfl⟩ := tdepositStep_some h
    exact ⟨f, e, hf, he, hc, rfl⟩
  · obtain ⟨hf, he, hc⟩ := hadm
    refine ⟨depositAt C s i e, ?_⟩
    show commitStep refXPol C s i = some _
    simp only [commitStep, hf, he]
    rw [if_pos]
    simp only [Bool.and_eq_true]
    exact ⟨⟨hc, hv⟩, hr⟩

/-! ## Decided runs -/

section Runs

variable {N T : Type}

/-- Run the labels `ls` from `s` with the step function `g`. -/
def execc_run (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (XSt N T)
  | s, [] => some s
  | s, l :: ls => (g C s l).bind fun s' => execc_run g C s' ls

/-- The trace of steps of the labels `ls` from `s` with the step function `g`. -/
def execc_trace (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (execc_trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `execc_trace` builds is a run of the graph of `g`, with the labels it was given. -/
theorem execc_trace_run {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      execc_trace g C s ls = some tr →
        XRun (fun C s l s' => g C s l = some s') C s tr ∧ tr.map (·.2.1) = ls
  | s, [], tr, h => by cases h; exact ⟨trivial, rfl⟩
  | s, l :: ls, tr, h => by
    simp only [execc_trace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : execc_trace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hr, hl⟩ := execc_trace_run ht
        exact ⟨⟨rfl, hs, hr⟩, by simp [hl]⟩

/-- Read a decided check `p` off a pass: run `pre` from `s0`, then trace a `begin` and `body`;
the trace is a run of the graph of `g` that opens with the `begin` step. -/
theorem execc_pass_check (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T))
    {C : Cfg N T} {s0 : XSt N T} {pre body : List (XLbl N T)}
    {p : XSt N T → List (XStep N T) → Bool}
    (h : (execc_run g C s0 pre).bind (fun s => (execc_trace g C s (.begin :: body)).map (p s)) =
      some true) :
    ∃ s s' tr, XRun (fun C s l s' => g C s l = some s') C s ((s, .begin, s') :: tr) ∧
      p s ((s, .begin, s') :: tr) = true := by
  cases h1 : execc_run g C s0 pre with
  | none => simp [h1] at h
  | some s =>
    cases h2 : execc_trace g C s (.begin :: body) with
    | none => simp [h1, h2] at h
    | some tr =>
      simp only [h1, h2, Option.bind_some, Option.map_some, Option.some.injEq] at h
      obtain ⟨hr, hl⟩ := execc_trace_run h2
      match tr, hr, hl, h with
      | (a, l, b) :: rest, hr, hl, h =>
        simp only [List.map_cons, List.cons.injEq] at hl
        obtain ⟨rfl, -⟩ := hl
        obtain ⟨rfl, hb, hr'⟩ := hr
        exact ⟨a, b, rest, ⟨rfl, hb, hr'⟩, h⟩

end Runs

/-! ## Examples: the firing pass (EXEC-002, EXEC-010, EXEC-013)

Places `0` to `4`. Four `Immediate` transitions of one priority (the all-immediate fast path,
declaration order), all enabled at the first update: `a` takes one token from `0`; `b` takes
`all()` from `1`; `c` takes one token from `3` and has a reset arc on `2`; `d` takes `exactly(2)`
from `4`. In the pass, `a` starts synchronously, its action writes `8` to `1` and `6` to `2`,
returns, and is settled inside the pass, so `1` holds the old `3` and the same-pass `8`, and `2`
the old `5` and the same-pass `6`; then `b`, `c` and `d` start. -/

/-- A transition without an output spec: name, input arcs, reset places. -/
def execc_tr (n : String) (ins : List (NInSpec Nat)) (resets : List Nat) : Trans Nat :=
  { core := { name := n, inputs := ins, inhibitors := [], reads := [], resets := resets },
    out := none }

/-- The configuration of the pass examples: no validation to speak of, no terminal places. -/
def execc_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3, 4],
                    transitions := [execc_tr "a" [⟨0, .one⟩] [], execc_tr "b" [⟨1, .all⟩] [],
                      execc_tr "c" [⟨3, .one⟩] [2], execc_tr "d" [⟨4, .exactly 2⟩] []] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true, timeoutOut := fun _ _ _ => false,
    res := 0 }

/-- The initial marking: `7` in `0`, `3` in `1`, `5` in `2`, `4` in `3`, `10, 11, 12` in `4`. -/
def execc_m0 : QMarking Nat Nat := fun p =>
  if p = 0 then [7] else if p = 1 then [3] else if p = 2 then [5] else if p = 3 then [4]
  else if p = 4 then [10, 11, 12] else []

/-- One cycle up to its termination test. -/
def execc_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline []]

/-- The pass up to the in-pass settle of `a`. -/
def execc_body : List (XLbl Nat Nat) :=
  [.start "a" true, .write 0 1 8, .write 0 2 6, .ret 0 true, .commit 0]

/-- The state step function `g` reaches along the cycle, the `begin` and `ls`. -/
def execc_at (g : Cfg Nat Nat → XSt Nat Nat → XLbl Nat Nat → Option (XSt Nat Nat))
    (ls : List (XLbl Nat Nat)) : Option (XSt Nat Nat) :=
  execc_run g execc_cfg (xinit execc_m0 0) (execc_pre ++ .begin :: ls)

/-- The head of the order of `s` satisfies `p`. -/
def execc_head (s : XSt Nat Nat) (p : Trans Nat → Bool) : Bool :=
  match s.order with
  | t :: _ => p t
  | [] => false

/-- Read the head of the order, and `p` of it, off a check. -/
theorem execc_head_some {s : XSt Nat Nat} {p : Trans Nat → Bool} (h : execc_head s p = true) :
    ∃ t rest, s.order = t :: rest ∧ p t = true := by
  cases ho : s.order with
  | nil => simp [execc_head, ho] at h
  | cons t rest => exact ⟨t, rest, rfl, by simpa [execc_head, ho] using h⟩

/-- Every firing with identity `i` in `s` satisfies `p`. -/
def execc_allId (s : XSt Nat Nat) (i : Nat) (p : Firing Nat Nat → Bool) : Bool :=
  s.fl.all fun f => f.id != i || p f

/-- Read `p` off a firing with identity `i`. -/
theorem execc_of_allId {s : XSt Nat Nat} {i : Nat} {p : Firing Nat Nat → Bool}
    (h : execc_allId s i p = true) {f : Firing Nat Nat} (hf : f ∈ s.fl) (hid : f.id = i) :
    p f = true := by
  have := List.all_eq_true.mp h f hf
  simpa [hid] using this

/-! ### EXEC-002: every line exercised -/

/-- Both lines of the executor companion of EXEC-002 are exercised by the reference: the four
transitions are armed by one update, all at stamp `0` (line 2, AC3's "share one stamp"), and the
pass starts them in the ready order, which on this one-priority net is the declaration order
(line 1, AC3's tie-break). -/
@[evidence nonvacuous EXEC_002_cycle]
theorem EXEC_002_cycle_nonvacuous :
    (∃ s s' tr, XRun RefExec execc_cfg s ((s, .begin, s') :: tr) ∧
      exec002c_starts (exec002c_pass tr) = ["a", "b", "c", "d"] ∧
      (readyOrder execc_cfg s).map (·.core.name) = ["a", "b", "c", "d"]) ∧
    (∃ s s', RefExec execc_cfg s .update s' ∧
      exec002c_fresh s s' "a" 0 ∧ exec002c_fresh s s' "d" 0) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, s', tr, hr, hp⟩ := execc_pass_check xstep (C := execc_cfg)
      (s0 := xinit execc_m0 0) (pre := execc_pre)
      (body := execc_body ++ [.start "b" false, .start "c" false, .start "d" false])
      (p := fun s tr => exec002c_starts (exec002c_pass tr.tail) == ["a", "b", "c", "d"] &&
        (readyOrder execc_cfg s).map (·.core.name) == ["a", "b", "c", "d"])
      (by decide +kernel)
    simp only [List.tail_cons, Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', tr, hr, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := execc_cfg)
      (o := execc_run xstep execc_cfg (xinit execc_m0 0)
        [.endCompletions, .endPublications, .endEvents])
      (l := .update)
      (p := fun s s' => stampOf (s'.st "a") == some 0 && stampOf (s.st "a") == none &&
        stampOf (s'.st "d") == some 0 && stampOf (s.st "d") == none)
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
    exact ⟨s, s', hs, ⟨h1, by simp [h2]⟩, ⟨h3, by simp [h4]⟩⟩

/-! ### EXEC-002: a pass that starts against the ready order -/

/-- An executor whose `begin` step sets the pass's order to the ready order reversed: on one
priority level, descending declaration order (a scan of the enablement bitmap from the top). -/
def execc_reversedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .begin => (xstep C s .begin).map fun s₁ => { s₁ with order := (readyOrder C s).reverse }
  | l => xstep C s l

/-- The executor of `execc_reversedStep`. -/
def execc_reversed {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_reversedStep C s l = some s'

/-- ✗ Starting against the ready order violates the executor companion of EXEC-002 (line 1,
AC3): the pass starts `d` and then `c`, although `c` was declared first and both share priority
and stamp. -/
@[evidence forbids EXEC_002_cycle]
theorem EXEC_002_cycle_forbids_reversedOrder :
    ¬ EXEC_002_cycle (execc_reversed (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', tr, hr, hp⟩ := execc_pass_check execc_reversedStep (C := execc_cfg)
    (s0 := xinit execc_m0 0) (pre := execc_pre) (body := [.start "d" false, .start "c" false])
    (p := fun s tr => !(exec002c_starts (exec002c_pass tr.tail)).isSublist
      ((readyOrder execc_cfg s).map (·.core.name)))
    (by decide +kernel)
  have hsub := h.1 execc_cfg s s' tr hr
  rw [← List.isSublist_iff_sublist] at hsub
  simp [hsub] at hp

/-! ### EXEC-002: one reading per newly armed transition -/

/-- An executor whose update reads the clock again for every transition it arms from no clock:
the `i`-th transition of the net is stamped `i` ticks after the update's reading. This is the
status it gives the name `n`, from the reference's new status and the old one. -/
def execc_stagger1 {N T : Type} (C : Cfg N T) (n : String) : Status → Status → Status
  | .armed k r, .off => .armed (k + (C.X.net.transitions.map (·.core.name)).idxOf n) r
  | x, _ => x

/-- The step function of the executor that stamps at one reading per newly armed transition. -/
def execc_staggerStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .update => (xstep C s .update).map fun s₁ =>
      { s₁ with st := fun n => execc_stagger1 C n (s₁.st n) (s.st n) }
  | l => xstep C s l

/-- The executor of `execc_staggerStep`. -/
def execc_stagger {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_staggerStep C s l = some s'

/-- ✗ Stamping the transitions one update arms at different readings violates the executor
companion of EXEC-002 (line 2, AC3's "share one stamp"): `a` is stamped `0` and `b` is stamped
`1` by the same update. -/
@[evidence forbids EXEC_002_cycle]
theorem EXEC_002_cycle_forbids_staggered :
    ¬ EXEC_002_cycle (execc_stagger (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_staggerStep (C := execc_cfg)
    (o := execc_run execc_staggerStep execc_cfg (xinit execc_m0 0)
      [.endCompletions, .endPublications, .endEvents])
    (l := .update)
    (p := fun s s' => stampOf (s'.st "a") == some 0 && stampOf (s.st "a") == none &&
      stampOf (s'.st "b") == some 1 && stampOf (s.st "b") == none)
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  have := h.2 execc_cfg s s' hs "a" "b" 0 1 ⟨h1, by simp [h2]⟩ ⟨h3, by simp [h4]⟩
  omega

/-! ### EXEC-010 and EXEC-013: every line exercised -/

/-- Both lines of the executor companion of EXEC-010 are exercised by the reference: `b`'s
`all()` input takes the pass-visible `3` of place `1` and leaves the same-pass `8` (line 1);
`d`'s `exactly(2)` input takes `10` and `11` of `10, 11, 12`, hands the action `10` then `11` and
leaves `12` (lines 1 and 2, AC2). -/
@[evidence nonvacuous EXEC_010_cycle]
theorem EXEC_010_cycle_nonvacuous :
    (∃ s s', RefExec execc_cfg s (.start "b" false) s' ∧ s.M 1 = [3, 8] ∧ s'.M 1 = [8]) ∧
    (∃ s s', RefExec execc_cfg s (.start "d" false) s' ∧ s'.M 4 = [12] ∧
      ∃ f ∈ s'.fl, f ∉ s.fl ∧ f.deliv.inputs 4 = [10, 11]) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := execc_cfg) (o := execc_at xstep execc_body)
      (l := .start "b" false) (p := fun s s' => s.M 1 == [3, 8] && s'.M 1 == [8])
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := execc_cfg)
      (o := execc_at xstep (execc_body ++ [.start "b" false, .start "c" false]))
      (l := .start "d" false)
      (p := fun s s' => s'.M 4 == [12] && s.fl.all (·.id != 3) &&
        s'.fl.any fun g => g.id == 3 && g.deliv.inputs 4 == [10, 11])
      (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.all_eq_true] at hp
    obtain ⟨⟨h1, h2⟩, g, hg, hid, hin⟩ := hp
    refine ⟨s, s', hs, h1, g, hg, fun hm => ?_, hin⟩
    have := h2 g hm
    simp [hid] at this

/-- The line of the executor companion of EXEC-013 is exercised by the reference: place `2` holds
the old `5` and the same-pass `6` when `c` starts; the reset drains `5` and keeps `6` (AC5 of
EXEC-003, the body sentence). -/
@[evidence nonvacuous EXEC_013_cycle]
theorem EXEC_013_cycle_nonvacuous :
    ∃ s s', RefExec execc_cfg s (.start "c" false) s' ∧ s.M 2 = [5, 6] ∧ s'.M 2 = [6] := by
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := execc_cfg)
    (o := execc_at xstep (execc_body ++ [.start "b" false]))
    (l := .start "c" false) (p := fun s s' => s.M 2 == [5, 6] && s'.M 2 == [6])
    (by decide +kernel)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨s, s', hs, hp⟩

/-! ### EXEC-010 and EXEC-013: a start that counts or drains the live marking -/

/-- An executor whose start consumes and drains the live marking, the same-pass deposits
included. -/
def execc_swallowStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy => (xstep C s (.start n sy)).bind fun s₁ =>
      s.order.head?.map fun t => { s₁ with M := qConsume s.M t }
  | l => xstep C s l

/-- The executor of `execc_swallowStep`. -/
def execc_swallow {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_swallowStep C s l = some s'

/-- ✗ Counting an `all()` input on the live marking violates the executor companion of EXEC-010
(line 1): `b` takes both the pass-visible `3` and the same-pass `8` of place `1`. -/
@[evidence forbids EXEC_010_cycle]
theorem EXEC_010_cycle_forbids_drainSwallows :
    ¬ EXEC_010_cycle (execc_swallow (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_swallowStep (C := execc_cfg)
    (o := execc_at execc_swallowStep execc_body) (l := .start "b" false)
    (p := fun s s' => execc_head s fun t => t.core.name == "b" && decide (1 ∈ inPlaces t) &&
      !decide (1 ∈ t.core.resets) && s'.M 1 != (s.M 1).drop (Consumes t (Counts (vis s)) 1))
    (by decide +kernel)
  obtain ⟨t, rest, ho, hh⟩ := execc_head_some hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, bne_iff_ne, ne_eq] at hh
  obtain ⟨⟨⟨hn, h1⟩, h2⟩, h3⟩ := hh
  exact h3 ((h execc_cfg "b" false).1 s s' hs t rest ho hn 1 h1 h2)

/-- ✗ Draining a reset place on the live marking violates the executor companion of EXEC-013:
`c`'s reset empties place `2`, taking the `6` that `a`'s action deposited in the pass. -/
@[evidence forbids EXEC_013_cycle]
theorem EXEC_013_cycle_forbids_drainSwallows :
    ¬ EXEC_013_cycle (execc_swallow (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_swallowStep (C := execc_cfg)
    (o := execc_at execc_swallowStep (execc_body ++ [.start "b" false])) (l := .start "c" false)
    (p := fun s s' => execc_head s fun t => t.core.name == "c" && decide (2 ∈ t.core.resets) &&
      s'.M 2 != hid s 2)
    (by decide +kernel)
  obtain ⟨t, rest, ho, hh⟩ := execc_head_some hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hh
  obtain ⟨⟨hn, h2⟩, h3⟩ := hh
  exact h3 (h execc_cfg "c" false s s' hs t rest ho hn 2 h2)

/-! ### EXEC-010: the newest tokens consumed -/

/-- The marking after a start of `t` from `s` that removes from every place that is not reset the
newest pass-visible tokens; `s₁` is the reference's state after the start. -/
def execc_newestM {N T : Type} [DecidableEq N] (s s₁ : XSt N T) (t : Trans N) : QMarking N T :=
  fun p => if p ∈ t.core.resets then s₁.M p
    else ((vis s p).reverse.drop (qTake (vis s) t p)).reverse ++ hid s p

/-- An executor whose start removes from every input place that is not reset the newest
pass-visible tokens instead of the oldest; what it hands the action is the reference's. -/
def execc_newestStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy => (xstep C s (.start n sy)).bind fun s₁ =>
      s.order.head?.map fun t => { s₁ with M := execc_newestM s s₁ t }
  | l => xstep C s l

/-- The executor of `execc_newestStep`. -/
def execc_newest {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_newestStep C s l = some s'

/-- ✗ Consuming the newest tokens violates the executor companion of EXEC-010 (line 1, AC2):
`d`'s `exactly(2)` input leaves `10` of `10, 11, 12` instead of `12`. -/
@[evidence forbids EXEC_010_cycle]
theorem EXEC_010_cycle_forbids_newest :
    ¬ EXEC_010_cycle (execc_newest (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_newestStep (C := execc_cfg)
    (o := execc_at execc_newestStep (execc_body ++ [.start "b" false, .start "c" false]))
    (l := .start "d" false)
    (p := fun s s' => execc_head s fun t => t.core.name == "d" && decide (4 ∈ inPlaces t) &&
      !decide (4 ∈ t.core.resets) && s'.M 4 != (s.M 4).drop (Consumes t (Counts (vis s)) 4))
    (by decide +kernel)
  obtain ⟨t, rest, ho, hh⟩ := execc_head_some hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, bne_iff_ne, ne_eq] at hh
  obtain ⟨⟨⟨hn, h4⟩, h5⟩, h6⟩ := hh
  exact h6 ((h execc_cfg "d" false).1 s s' hs t rest ho hn 4 h4 h5)

/-! ### EXEC-010: the consumed tokens handed newest first -/

/-- The firing record `g` with its consumed tokens reversed, if it is the firing `i`. -/
def execc_revFiring {N T : Type} (i : Nat) (g : Firing N T) : Firing N T :=
  if g.id = i then { g with deliv := ⟨fun p => (g.deliv.inputs p).reverse, g.deliv.reads⟩ }
  else g

/-- An executor whose start removes the right tokens but hands them to the action newest
first. -/
def execc_revDeliverStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy => (xstep C s (.start n sy)).map fun s₁ =>
      { s₁ with fl := s₁.fl.map (execc_revFiring s.nextId) }
  | l => xstep C s l

/-- The executor of `execc_revDeliverStep`. -/
def execc_revDeliver {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_revDeliverStep C s l = some s'

/-- ✗ Handing the consumed tokens newest first violates the executor companion of EXEC-010
(line 2): `d`'s action receives `11` then `10`. -/
@[evidence forbids EXEC_010_cycle]
theorem EXEC_010_cycle_forbids_reversedDelivery :
    ¬ EXEC_010_cycle (execc_revDeliver (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_revDeliverStep (C := execc_cfg)
    (o := execc_at execc_revDeliverStep (execc_body ++ [.start "b" false, .start "c" false]))
    (l := .start "d" false)
    (p := fun s s' => execc_head s fun t => t.core.name == "d" && decide (4 ∈ inPlaces t) &&
      s.fl.all (·.id != s.nextId) &&
      s'.fl.any fun g => g.id == s.nextId &&
        g.deliv.inputs 4 != OldestFirst s.M 4 (Consumes t (Counts (vis s)) 4))
    (by decide +kernel)
  obtain ⟨t, rest, ho, hh⟩ := execc_head_some hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, bne_iff_ne, ne_eq] at hh
  obtain ⟨⟨⟨hn, h4⟩, hold⟩, g, hg, hid, hne⟩ := hh
  exact hne ((h execc_cfg "d" false).2 s s' hs t rest ho hn g hg (fun hm => hold g hm hid) 4 h4)

/-! ### EXEC-013: the drain deferred past the start -/

/-- The marking after a start of `t` from `s` that leaves every reset place that is not an input
place as it was; `s₁` is the reference's state after the start. -/
def execc_lateM {N T : Type} [DecidableEq N] (s s₁ : XSt N T) (t : Trans N) : QMarking N T :=
  fun p => if p ∈ t.core.resets ∧ p ∉ inPlaces t then s.M p else s₁.M p

/-- An executor whose start leaves every reset place that is not an input place as it was: the
drain is deferred past the action's start. -/
def execc_drainLateStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .start n sy => (xstep C s (.start n sy)).bind fun s₁ =>
      s.order.head?.map fun t => { s₁ with M := execc_lateM s s₁ t }
  | l => xstep C s l

/-- The executor of `execc_drainLateStep`. -/
def execc_drainLate {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_drainLateStep C s l = some s'

/-- ✗ Draining after the start violates the executor companion of EXEC-013 (the first shall
sentence, "before its action starts"): when `c` starts, place `2` still holds the old `5`. -/
@[evidence forbids EXEC_013_cycle]
theorem EXEC_013_cycle_forbids_drainLate :
    ¬ EXEC_013_cycle (execc_drainLate (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_drainLateStep (C := execc_cfg)
    (o := execc_at execc_drainLateStep (execc_body ++ [.start "b" false])) (l := .start "c" false)
    (p := fun s s' => execc_head s fun t => t.core.name == "c" && decide (2 ∈ t.core.resets) &&
      s'.M 2 != hid s 2)
    (by decide +kernel)
  obtain ⟨t, rest, ho, hh⟩ := execc_head_some hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hh
  obtain ⟨⟨hn, h2⟩, h3⟩ := hh
  exact h3 (h execc_cfg "c" false s s' hs t rest ho hn 2 h2)

/-! ## Examples: deposits (EXEC-020)

Places `0` to `5` and the terminal place `9`. Three `Immediate` transitions of one priority, all
started asynchronously in the first pass: `a` (identity `0`) takes one token from `0`; `b`
(identity `1`) takes one from `1`; `t` (identity `2`) takes one from `3` and has the output spec
`Timeout(d, 2)`, whose timeout outcome is one token in `2`. Validation rejects every produced set
that holds place `4`; place `5` holds `40` from the start. -/

/-- The transition `t`: one token from `3`, output spec `Timeout(d, 2)`. -/
def execc20_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨3, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some (.timeout (.place 2)) }

/-- The configuration of the deposit examples. -/
def execc20_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2, 3, 4, 5, 9],
                    transitions := [execc_tr "a" [⟨0, .one⟩] [], execc_tr "b" [⟨1, .one⟩] [],
                      execc20_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [9], envs := [], reentrant := false,
    validate := fun _ d => !d.contains 4, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ e => e.map Prod.fst == [2], res := 0 }

/-- The initial marking: `7` in `0`, `8` in `1`, `6` in `3`, `40` in `5`. -/
def execc20_m0 : QMarking Nat Nat := fun p =>
  if p = 0 then [7] else if p = 1 then [8] else if p = 3 then [6] else if p = 5 then [40]
  else []

/-- The state step function `g` reaches along the first cycle, its pass starting `a`, `b` and
`t`, and then `ls`. -/
def execc20_at (g : Cfg Nat Nat → XSt Nat Nat → XLbl Nat Nat → Option (XSt Nat Nat))
    (ls : List (XLbl Nat Nat)) : Option (XSt Nat Nat) :=
  execc_run g execc20_cfg (xinit execc20_m0 0)
    (execc_pre ++ [.begin, .start "a" false, .start "b" false, .start "t" false, .endPass] ++ ls)

/-- `a`'s action writes `30` then `31` to `5` and returns. -/
def execc20_two : List (XLbl Nat Nat) := [.write 0 5 30, .write 0 5 31, .ret 0 true]

/-- `b`'s action writes `5` to the terminal place and is settled; then `a`'s action writes `30`
to `5` and returns. -/
def execc20_term : List (XLbl Nat Nat) :=
  [.write 1 9 5, .ret 1 true, .commit 1, .write 0 5 30, .ret 0 true]

/-- `a`'s action writes `9` to `4`, which validation rejects, and returns. -/
def execc20_bad : List (XLbl Nat Nat) := [.write 0 4 9, .ret 0 true]

/-- `a`'s action writes `9` to `5` and publishes it; `b`'s action marks the terminal place and is
settled; the run stops on the terminal place. -/
def execc20_stop : List (XLbl Nat Nat) :=
  [.write 0 5 9, .flush 0, .write 1 9 5, .ret 1 true, .commit 1, .finish .terminal]

/-- `t`'s action writes `50` to `1`; its budget expires with the timeout outcome `5` in `2`. -/
def execc20_timeout : List (XLbl Nat Nat) := [.write 2 1 50, .expire 2 [(2, 5)]]

/-- Every line of the executor companion of EXEC-020 is exercised by the reference: `a`'s
completion deposits `30` then `31` behind the `40` of place `5` (lines 1 and 5, AC1, AC2); `a`'s
completion with `9` in `4`, which validation rejects, is failed and place `4` stays empty (line 2,
AC4); after the terminal stop `a`'s abandoned action returns, its published `9` was discarded, and
place `5` still holds only `40` (line 3, AC3); `t`'s timeout outcome `5` is deposited in `2` and
the `50` its action wrote does not reach `1` (line 4, AC3). -/
@[evidence nonvacuous EXEC_020_cycle]
theorem EXEC_020_cycle_nonvacuous :
    (∃ s s', RefExec execc20_cfg s (.commit 0) s' ∧ s'.M 5 = [40, 30, 31]) ∧
    (∃ s s', RefExec execc20_cfg s (.fail 0) s' ∧ s'.M 4 = []) ∧
    (∃ s s', RefExec execc20_cfg s (.ret 0 true) s' ∧ isExecPhase s.phase = false ∧
      s'.M 5 = [40] ∧ s'.pq = []) ∧
    (∃ s s', RefExec execc20_cfg s (.tdeposit 2) s' ∧ s'.M 2 = [5] ∧ s'.M 1 = []) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := execc20_cfg)
      (o := execc20_at xstep execc20_two) (l := .commit 0)
      (p := fun _ s' => s'.M 5 == [40, 30, 31]) (by decide +kernel)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := execc20_cfg)
      (o := execc20_at xstep execc20_bad) (l := .fail 0)
      (p := fun _ s' => s'.M 4 == []) (by decide +kernel)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := execc20_cfg)
      (o := execc20_at xstep execc20_stop) (l := .ret 0 true)
      (p := fun s s' => !isExecPhase s.phase && s'.M 5 == [40] && s'.pq.isEmpty)
      (by decide +kernel)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_iff] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := execc20_cfg)
      (o := execc20_at xstep execc20_timeout) (l := .tdeposit 2)
      (p := fun _ s' => s'.M 2 == [5] && s'.M 1 == []) (by decide +kernel)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩

/-! ### EXEC-020: depositing while a terminal place is marked -/

/-- An executor that deposits a returned emission whether or not a terminal place is marked. -/
def execc_termAdmitStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i => commitStep refXPol { C with terminals := [] } s i
  | l => xstep C s l

/-- The executor of `execc_termAdmitStep`. -/
def execc_termAdmit {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_termAdmitStep C s l = some s'

/-- ✗ Depositing a completion while a terminal place is marked violates the executor companion of
EXEC-020 (line 1, AC3): `b`'s completion marks the terminal place, and `a`'s completion, which
the stop abandons, is still deposited. -/
@[evidence forbids EXEC_020_cycle]
theorem EXEC_020_cycle_forbids_admitWhenTerminal :
    ¬ EXEC_020_cycle (execc_termAdmit (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_termAdmitStep (C := execc20_cfg)
    (o := execc20_at execc_termAdmitStep execc20_term) (l := .commit 0)
    (p := fun s _ => !liveB execc20_cfg s) (by decide +kernel)
  obtain ⟨f, e, ⟨-, -, hc⟩, -⟩ := (h execc20_cfg).1 0 s s' hs
  simp only [canSettle, Bool.and_eq_true] at hc
  simp [hc.1.1.2] at hp

/-! ### EXEC-020: depositing out of production order -/

/-- The marking after a settle of firing `i` from `s` that deposits its returned emission in
reverse order; `s₁` is the reference's state after the settle. -/
def execc_revM {N T : Type} [DecidableEq N] (s s₁ : XSt N T) (i : Nat) : QMarking N T :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.ok e) => qAppend s.M e.reverse
    | _ => s₁.M
  | none => s₁.M

/-- An executor that deposits a returned emission in reverse order. -/
def execc_revCommitStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i => (xstep C s (.commit i)).map fun s₁ => { s₁ with M := execc_revM s s₁ i }
  | l => xstep C s l

/-- The executor of `execc_revCommitStep`. -/
def execc_revCommit {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_revCommitStep C s l = some s'

/-- ✗ Depositing out of production order violates the executor companion of EXEC-020 (line 1,
AC2): `a`'s action writes `30` then `31` to `5`, and `31` lands first. -/
@[evidence forbids EXEC_020_cycle]
theorem EXEC_020_cycle_forbids_reversed :
    ¬ EXEC_020_cycle (execc_revCommit (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_revCommitStep (C := execc20_cfg)
    (o := execc20_at execc_revCommitStep execc20_two) (l := .commit 0)
    (p := fun s s' => execc_allId s 0 fun f => match f.out with
      | some (.ok e) => qAppend s.M e 5 != s'.M 5
      | _ => false)
    (by decide +kernel)
  obtain ⟨f, e, ⟨hf, he, -⟩, -, hM⟩ := (h execc20_cfg).1 0 s s' hs
  have hg := execc_of_allId hp (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
  rw [he] at hg
  simp [hM] at hg

/-! ### EXEC-020: a failure that deposits -/

/-- The marking after a fail step of firing `i` from `s` that deposits its returned emission
anyway; `s₁` is the reference's state after the fail step. -/
def execc_failM {N T : Type} [DecidableEq N] (s s₁ : XSt N T) (i : Nat) : QMarking N T :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.ok e) => qAppend s.M e
    | _ => s₁.M
  | none => s₁.M

/-- An executor whose fail step deposits the emission validation rejected. -/
def execc_failDepositsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i => (xstep C s (.fail i)).map fun s₁ => { s₁ with M := execc_failM s s₁ i }
  | l => xstep C s l

/-- The executor of `execc_failDepositsStep`. -/
def execc_failDeposits {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_failDepositsStep C s l = some s'

/-- ✗ Depositing a rejected emission at the failure violates the executor companion of EXEC-020
(line 2, AC4): `a`'s action writes `9` to `4`, validation rejects it, and the fail step puts `9`
into `4`. -/
@[evidence forbids EXEC_020_cycle]
theorem EXEC_020_cycle_forbids_failDeposits :
    ¬ EXEC_020_cycle (execc_failDeposits (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_failDepositsStep (C := execc20_cfg)
    (o := execc20_at execc_failDepositsStep execc20_bad) (l := .fail 0)
    (p := fun s s' => s'.M 4 != s.M 4) (by decide +kernel)
  have := (h execc20_cfg).2.1 (.fail 0) rfl s s' hs
  simp [this] at hp

/-! ### EXEC-020: a publication deposited after the stop -/

/-- An executor that keeps the publication queue across a terminal stop and deposits a queued
publication after the run finished. -/
def execc_lateStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .finish .terminal => (xstep C s (.finish .terminal)).map fun s₁ => { s₁ with pq := s.pq }
  | .publish i =>
    if isExecPhase s.phase then xstep C s (.publish i)
    else
      match s.pq with
      | (j, b) :: rest => if j == i then some { s with M := qAppend s.M b, pq := rest } else none
      | [] => none
  | l => xstep C s l

/-- The executor of `execc_lateStep`. -/
def execc_late {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_lateStep C s l = some s'

/-- ✗ Depositing a publication after the run finished violates the executor companion of
EXEC-020 (line 3, "A publication still queued when a terminal place stops the run is
discarded."): `a`'s published `9` lands in `5` after the terminal stop. -/
@[evidence forbids EXEC_020_cycle]
theorem EXEC_020_cycle_forbids_publishAfterStop :
    ¬ EXEC_020_cycle (execc_late (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_lateStep (C := execc20_cfg)
    (o := execc20_at execc_lateStep execc20_stop) (l := .publish 0)
    (p := fun s s' => !isExecPhase s.phase && s'.M 5 != s.M 5) (by decide +kernel)
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hp
  have hM : s'.M = s.M := (h execc20_cfg).2.2.1 s s' ⟨hp.1, _, hs⟩
  exact hp.2 (by rw [hM])

/-! ### EXEC-020: the action's writes merged into the timeout outcome -/

/-- The marking after a timeout deposit of firing `i` from `s` that also deposits what the action
wrote since its last flush; `s₁` is the reference's state after the deposit. -/
def execc_mergeM {N T : Type} [DecidableEq N] (s s₁ : XSt N T) (i : Nat) : QMarking N T :=
  match s.fl.find? (·.id == i) with
  | some f =>
    match f.out with
    | some (.timedOut e) => qAppend s.M (f.buf ++ e)
    | _ => s₁.M
  | none => s₁.M

/-- An executor that merges the action's unpublished writes into the timeout outcome. -/
def execc_mergeStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .tdeposit i => (xstep C s (.tdeposit i)).map fun s₁ => { s₁ with M := execc_mergeM s s₁ i }
  | l => xstep C s l

/-- The executor of `execc_mergeStep`. -/
def execc_merge {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_mergeStep C s l = some s'

/-- ✗ Merging the action's writes into the timeout outcome violates the executor companion of
EXEC-020 (line 4, AC3): `t`'s action wrote `50` to `1` and its budget expired; the `50` lands in
`1` with the timeout outcome. -/
@[evidence forbids EXEC_020_cycle]
theorem EXEC_020_cycle_forbids_mergeOnTimeout :
    ¬ EXEC_020_cycle (execc_merge (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_mergeStep (C := execc20_cfg)
    (o := execc20_at execc_mergeStep execc20_timeout) (l := .tdeposit 2)
    (p := fun s s' => execc_allId s 2 fun f => match f.out with
      | some (.timedOut e) => qAppend s.M e 1 != s'.M 1
      | _ => false)
    (by decide +kernel)
  obtain ⟨f, e, hf, he, -, hM⟩ := (h execc20_cfg).2.2.2.1 2 s s' hs
  have hg := execc_of_allId hp (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
  rw [he] at hg
  simp [hM] at hg

/-! ### EXEC-020: a commit that skips validation -/

/-- An executor whose commit step deposits a returned emission without asking output
validation. -/
def execc_noValidateStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i => commitStep refXPol { C with validate := fun _ _ => true } s i
  | l => xstep C s l

/-- The executor of `execc_noValidateStep`. -/
def execc_noValidate {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_noValidateStep C s l = some s'

/-- ✗ Committing an emission that validation rejects violates the executor companion of EXEC-020
(line 1, AC4): `a`'s action writes `9` to `4`, validation rejects every set holding `4`, and the
commit step deposits it. -/
@[evidence forbids EXEC_020_cycle]
theorem EXEC_020_cycle_forbids_commitUnvalidated :
    ¬ EXEC_020_cycle (execc_noValidate (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_noValidateStep (C := execc20_cfg)
    (o := execc20_at execc_noValidateStep execc20_bad) (l := .commit 0)
    (p := fun s _ => execc_allId s 0 fun f => match f.out with
      | some (.ok e) => !execc20_cfg.validate f.t (validIn f e)
      | _ => false)
    (by decide +kernel)
  obtain ⟨f, e, ⟨hf, he, -⟩, hv, -⟩ := (h execc20_cfg).1 0 s s' hs
  have hg := execc_of_allId hp (List.mem_of_find?_eq_some hf) (by simpa using List.find?_some hf)
  rw [he] at hg
  simp [hv] at hg

/-! ### EXEC-020: a timeout outcome deposited while a terminal place is marked -/

/-- An executor that deposits a timeout outcome whether or not a terminal place is marked. -/
def execc_termTdepStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .tdeposit i => tdepositStep { C with terminals := [] } s i
  | l => xstep C s l

/-- The executor of `execc_termTdepStep`. -/
def execc_termTdep {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_termTdepStep C s l = some s'

/-- `b`'s action marks the terminal place and is settled; then `t`'s budget expires with the
timeout outcome `5` in `2`. -/
def execc20_termTimeout : List (XLbl Nat Nat) :=
  [.write 1 9 5, .ret 1 true, .commit 1, .expire 2 [(2, 5)]]

/-- ✗ Depositing a timeout outcome while a terminal place is marked violates the executor
companion of EXEC-020 (line 4, AC3): `b`'s completion marks the terminal place, and `t`'s timeout
outcome, which the stop abandons, is still deposited. -/
@[evidence forbids EXEC_020_cycle]
theorem EXEC_020_cycle_forbids_tdepositWhenTerminal :
    ¬ EXEC_020_cycle (execc_termTdep (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check execc_termTdepStep (C := execc20_cfg)
    (o := execc20_at execc_termTdepStep execc20_termTimeout) (l := .tdeposit 2)
    (p := fun s _ => !liveB execc20_cfg s) (by decide +kernel)
  obtain ⟨f, e, -, -, hc, -⟩ := (h execc20_cfg).2.2.2.1 2 s s' hs
  simp only [canSettle, Bool.and_eq_true] at hc
  simp [hc.1.1.2] at hp

/-! ### EXEC-020: an accepted completion never deposited -/

/-- An executor that never takes a commit step: it settles nothing that returned normally. -/
def execc_noCommitStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit _ => none
  | l => xstep C s l

/-- The executor of `execc_noCommitStep`. -/
def execc_noCommit {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => execc_noCommitStep C s l = some s'

/-- `s` is in step 1 and the completion of firing `i` is admitted, and validation and the
relay check accept its emission. -/
def execc20_acceptB (s : XSt Nat Nat) (i : Nat) : Bool :=
  decide (s.phase = .completions) &&
    match s.fl.find? (·.id == i) with
    | some f =>
      match f.out with
      | some (.ok e) => canSettle execc20_cfg s i f && execc20_cfg.validate f.t (validIn f e) &&
          execc20_cfg.relay f.t f.deliv e
      | _ => false
    | none => false

/-- ✗ Never depositing an accepted completion violates the executor companion of EXEC-020
(line 5, AC1): in step 1 `a`'s completion with `30, 31` is admitted and validation accepts it,
and the executor offers no commit step. -/
@[evidence forbids EXEC_020_cycle]
theorem EXEC_020_cycle_forbids_neverCommits :
    ¬ EXEC_020_cycle (execc_noCommit (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, -, hp⟩ := step_of_check xstep (C := execc20_cfg)
    (o := execc20_at xstep execc20_two) (l := .commit 0)
    (p := fun s _ => execc20_acceptB s 0) (by decide +kernel)
  simp only [execc20_acceptB, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨hph, hm⟩ := hp
  split at hm
  · rename_i f hf
    split at hm
    · rename_i e he
      simp only [Bool.and_eq_true] at hm
      obtain ⟨⟨hc, hv⟩, hr⟩ := hm
      obtain ⟨s'', hs''⟩ := (h execc20_cfg).2.2.2.2 0 s f e hph ⟨hf, he, hc⟩ hv hr
      simp [execc_noCommit, execc_noCommitStep] at hs''
    · simp at hm
  · simp at hm

end Libpetri.Spec
