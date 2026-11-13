import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec
import Libpetri.Spec.Text.EXEC_021

set_option linter.missingDocs true

/-!
# EXEC-021: Output spec validation (`spec/04-execution-model.md`)

The first requirement block over the executor model (`RefExec`, `Reference/Exec.lean`). A
firing settles in a step after its start: `commit i` deposits the emission the action of firing
`i` returned, `fail i` settles it without a deposit. The requirement is a predicate over an
abstract executor `R : XRel N T` (glossary `GlossaryExec.lean`), checked against the reference
executor, against a mutant that validates the returned tokens only (ruling D27), and against
executors that deposit without validating, deposit a rejected emission when the action returns,
restore the consumed tokens on a failure, withdraw a failed firing's publications, or validate the
timeout outcome (ruling D24, the behaviour RD-01 in `spec/runtime-defects.md` recorded for Java and
TypeScript).

Output validation is two checks of the configuration (`Cfg`): the [IO-015] verdict on the
produced set (`Cfg.validate`), and the join-relay check of [NU-054], which runs "as part of
output validation" (`Cfg.relay`). The [CONC-026] skip turns both off (`Cfg.SkipsValidation`).
The shared validator of [IO-015] enters through `cfgValidate`, and the agreement of the
executor's verdicts with it (`ValidatedBy`) is a conjunct of the consistency theorem
(`ConsistencyExec.lean`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## EXEC-021: Output Spec Validation -/

requirement EXEC_021
  id "EXEC-021"
  title "Output Spec Validation"
  kind B
  scope "all executors"
  source verbatim "spec/04-execution-model.md"
  covers EXEC_021.s1, EXEC_021.s2, EXEC_021.s3, EXEC_021.s4, EXEC_021.s5, EXEC_021.s6, EXEC_021.s7,
        EXEC_021.s8, EXEC_021.s9
  reading "For every executor R, every configuration C whose output verdict reads a set of places, and every firing identity i:"
          "a commit step of i deposits exactly the emission e the action of i returned, each token at the tail of its place in emission order, and only when output validation accepts the places of e followed by the places i has already published, and the join-relay check accepts e;"
          "a fail step of i changes neither the marking nor the queue of publications not yet deposited;"
          "a fail step of i happens only when the action of i failed, or it returned an emission e that output validation (over the same places as in the first line) or the join-relay check rejects, or i ended with a timeout outcome e that the join-relay check rejects;"
          "a step in which the action of i writes a token or returns leaves the marking unchanged;"
          "a step that deposits the timeout outcome e of i happens only when the join-relay check accepts e."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. A firing starts in a firing pass and settles in a later step; the outside steps write, flush and ret are its action writing a token, publishing what it wrote, and returning normally (with what it wrote since the last flush as its emission) or with an error. The witness is the reference executor RefExec (Reference/Exec.lean), the graph of a step function checked rule by rule against the Rust executor."
          "Naming: the markdown's 'admits the completion' is the executor taking the completion up in step 1 or inside the pass (glossary: Admitted completion). The model splits what follows into two labels: commit i, the admitted completion passes validation and is deposited, and fail i, it is rejected (or the action failed, [EXEC-030]). The quoted sentences are read through that split: 'deposits' is a commit step, 'fail the firing' and 'emit a TransitionFailed event' is a fail step."
          "Output validation is two checks of the configuration: C.validate, the IO-015 verdict on a produced set, and C.relay, the join-relay check of NU-054, which the markdown of NU-054 puts 'as part of output validation (IO-015)'. Both are parameters, as the verdict function is IO-015's subject: this block fixes when the executor consults them and what it does with the answer. With the validation skip of CONC-026 both accept everything (Cfg.SkipsValidation), so the quoted 'An executor with the validation skip of [CONC-026] enabled does not validate.' needs no line of its own: under the skip a fail step happens only for an action that failed (theorem EXEC_021_skip). The first quoted sentence is the body's summary of the first shall sentence. A batch the action flushes is checked by the join-relay check when it is flushed (Rust's flush guard): a rejected batch is dropped, and the firing ends with an error whatever its action returns, so its fail step is line 3's first case (exec021_relayBad_fails)."
          "The first shall sentence is lines 1 and 4: a commit step happens only after validation accepted, and the steps in which the action produces its tokens (write, ret) deposit nothing, so no produced token is deposited before the settle step that validates it. Line 1 also says which tokens were validated: exactly the emission the step deposits, at the tails ([EXEC-020]'s deposit, CORE-013), so the check and the deposit are of one set of tokens. An executor that deposits without consulting the validator breaks line 1 (EXEC_021_forbids_ignoreValidate); one that deposits a rejected emission when the action returns, and settles as the reference, breaks only line 4 (EXEC_021_forbids_depositAtReturn)."
          "Validation reads a set of places ([IO-015]; every validator satisfying IO-015 does, IO_015_setOnly), so the lines quantify over configurations whose verdict reads sets (Cfg.SetValidated). The order and repetition of the list validIn builds are then not part of the requirement: an executor validating the published places before the returned ones meets it. The configurations of the examples are of that kind (exec021_cfg_set)."
          "The second shall sentence is lines 1, 2 and 4: a rejected emission is never the emission of a commit step (line 1), its fail step deposits nothing (line 2), and the action's write and return steps deposit nothing (line 4). That no other executor step deposits it is EXEC-020's companion line (deposits of a firing only through commit, tdeposit and publish) and EXEC-022's (tdeposit deposits exactly the timeout outcome), both later blocks over this model. 'Emit a TransitionFailed event' is the event kind the fail label carries (design table R-EXEC-8); the event and its payload are EVT-008's, on the event model of wave W7. That a rejection is in fact settled by a fail step, and not left in the queue, is coverage, stated in the consistency theorem (ValidatedBy), not here."
          "The third shall sentence is line 2: the fail step leaves the marking as it is, so the consumed tokens stay consumed (EXEC_021_forbids_failRestores) and the tokens the action already published stay. A publication still queued when the completion fails is deposited later by its publish step (ruling D17), so line 2 also keeps the publication queue (EXEC_021_forbids_dropPublication)."
          "The fourth shall sentence (ruling D27 (a)) is the places line 1 and line 3 read, validIn f e: the places of the returned emission e followed by the places of every batch firing f flushed. Rust validates the returned outputs together with flushed_places (executor_core/executor.rs output_conforms). A validation over the returned places alone fails a firing that published one child of And(A, B) and returned the other (EXEC_021_mutant_noPub_killed)."
          "The fifth shall sentence is line 3 for a returned emission: a fail step of a firing whose emission passes both checks does not exist. With line 2 it excludes an executor that fails every completion."
          "The timeout sentences (ruling D24 (a)) are line 3's last case: a firing that ended with its timeout outcome is failed only when the join-relay check rejects it, never by the IO-015 verdict. Every runtime skips validation on the timeout path and runs the relay check: Rust in handle_completion (executor_core/executor.rs), Java and TypeScript in processCompletedTransitions of both executors, which run only the relay check when the context was detached for the timeout (isDetachedForTimeout; in the precompiled executors inside the CONC-026 skip). An executor that validates the timeout outcome fails And(A, Timeout(d, B)) on every timeout (EXEC_021_forbids_validateTimeout), the behaviour RD-01 in spec/runtime-defects.md recorded for Java and TypeScript. That the relay check runs on the timeout outcome is NU-054's sentence 'Every token the firing deposits in a relay target is checked, whatever wrote it, including an Out.forwardInput or Out.timeout branch'. Line 5 is the relay half of the sentence: a deposit of the timeout outcome happens only when the relay check accepts it (EXEC_021_forbids_timeoutNoRelay). What the timeout outcome deposits is EXEC-022's and IO-013's subject."
          "Validation reads sets of places (IO-015), so an emission with several tokens in one claimed place passes; a run whose emission is not a deposit the output spec offers is a real run (IO-016 AC4), so a link from this model to the queue firing RefQFire carries the per-run hypothesis OfferedEmission (glossary)."
          "Firing identities are drawn from one supply (XSt.nextId), so 'the firing i' is unique in every reachable state; the lines read 'some firing in flight with identity i', which is the same there."
          "AC1 (And, every child received tokens, valid) is IO-015's verdict; EXEC_021_nonvacuous admits And(1, 2) with child 1 published and child 2 returned."
          "AC2 (Xor, exactly one child selected, overlapping branches without a tie-break) is IO-015's verdict (IO_015_ac9, IO_015_ac10), not restated."
          "AC3 (violation, failure event emitted) is line 1 (a rejected emission has no commit step) with the event kind of the fail label; that the fail step is offered is ValidatedBy in the consistency theorem. EXEC_021_nonvacuous fails Xor(1, 2) written in both branches. The event itself is EVT-008's."
          "AC4 (validation applied by every executor backend a language ships) is about which code paths exist: both backends are runs of RefExec (CONC-020, a later block); not encoded here (test evidence)."
          "AC5 (violation: the event is TransitionFailed, no produced token deposited, consumed tokens not restored, published tokens stay) is lines 1 and 2; EXEC_021_nonvacuous deposits the publication of a failed firing after its fail step."
          "The test derivation (Xor output with tokens to both branches, a violation, neither branch place receives a token) is EXEC_021_nonvacuous's rejection run."
  signoff "2026-11-13 1649f694fa3b896b ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C, C.SetValidated → ∀ i,
      (on (fun s s' => R C s (.commit i) s'), shall (fun s s' =>
        ∃ f ∈ s.fl, f.id = i ∧ ∃ e, f.out = some (.ok e) ∧
          C.validate f.t (validIn f e) = true ∧ C.relay f.t f.deliv e = true ∧
          s'.M = qAppend s.M e)) ∧
      (on (fun s s' => R C s (.fail i) s'), shall (fun s s' => s'.M = s.M ∧ s'.pq = s.pq)) ∧
      (on (fun s s' => R C s (.fail i) s'), shall (fun s _ =>
        ∃ f ∈ s.fl, f.id = i ∧
          (f.out = some .err ∨
            (∃ e, f.out = some (.ok e) ∧
              (C.validate f.t (validIn f e) = false ∨ C.relay f.t f.deliv e = false)) ∨
            (∃ e, f.out = some (.timedOut e) ∧ C.relay f.t f.deliv e = false)))) ∧
      (on (fun s s' => (∃ ok, R C s (.ret i ok) s') ∨ ∃ p x, R C s (.write i p x) s'),
        shall (fun s s' => s'.M = s.M)) ∧
      (on (fun s s' => R C s (.tdeposit i) s'), shall (fun s _ =>
        ∃ f ∈ s.fl, f.id = i ∧ ∃ e, f.out = some (.timedOut e) ∧ C.relay f.t f.deliv e = true))

/- The pinned readable form of EXEC-021: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EXEC_021 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    C.SetValidated →
      ∀ (i : ℕ),
        (on fun s s' => R C s (XLbl.commit i) s', shall fun s s' =>
            ∃ f ∈ s.fl,
              f.id = i ∧
                ∃ e,
                  f.out = some (Outcome.ok e) ∧
                    C.validate f.t (validIn f e) = true ∧ C.relay f.t f.deliv e = true ∧ s'.M = qAppend s.M e) ∧
          (on fun s s' => R C s (XLbl.fail i) s', shall fun s s' => s'.M = s.M ∧ s'.pq = s.pq) ∧
            (on fun s s' => R C s (XLbl.fail i) s', shall fun s x =>
                ∃ f ∈ s.fl,
                  f.id = i ∧
                    (f.out = some Outcome.err ∨
                      (∃ e,
                          f.out = some (Outcome.ok e) ∧
                            (C.validate f.t (validIn f e) = false ∨ C.relay f.t f.deliv e = false)) ∨
                        ∃ e, f.out = some (Outcome.timedOut e) ∧ C.relay f.t f.deliv e = false)) ∧
              (on fun s s' => (∃ ok, R C s (XLbl.ret i ok) s') ∨ ∃ p x, R C s (XLbl.write i p x) s', shall fun s s' =>
                  s'.M = s.M) ∧
                on fun s s' => R C s (XLbl.tdeposit i) s', shall fun s x =>
                  ∃ f ∈ s.fl, f.id = i ∧ ∃ e, f.out = some (Outcome.timedOut e) ∧ C.relay f.t f.deliv e = true
-/
#guard_msgs in #print EXEC_021

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- The lines of EXEC-021 with the places validation reads as a parameter `vin` (the reference
reads `validIn`). -/
def exec021Lines (vin : Firing N T → List (N × T) → List N) (R : XRel N T) : Prop :=
  ∀ C, C.SetValidated → ∀ i,
    (on (fun s s' => R C s (.commit i) s'), shall (fun s s' =>
      ∃ f ∈ s.fl, f.id = i ∧ ∃ e, f.out = some (.ok e) ∧
        C.validate f.t (vin f e) = true ∧ C.relay f.t f.deliv e = true ∧
        s'.M = qAppend s.M e)) ∧
    (on (fun s s' => R C s (.fail i) s'), shall (fun s s' => s'.M = s.M ∧ s'.pq = s.pq)) ∧
    (on (fun s s' => R C s (.fail i) s'), shall (fun s _ =>
      ∃ f ∈ s.fl, f.id = i ∧
        (f.out = some .err ∨
          (∃ e, f.out = some (.ok e) ∧
            (C.validate f.t (vin f e) = false ∨ C.relay f.t f.deliv e = false)) ∨
          (∃ e, f.out = some (.timedOut e) ∧ C.relay f.t f.deliv e = false)))) ∧
    (on (fun s s' => (∃ ok, R C s (.ret i ok) s') ∨ ∃ p x, R C s (.write i p x) s'),
      shall (fun s s' => s'.M = s.M)) ∧
    (on (fun s s' => R C s (.tdeposit i) s'), shall (fun s _ =>
      ∃ f ∈ s.fl, f.id = i ∧ ∃ e, f.out = some (.timedOut e) ∧ C.relay f.t f.deliv e = true))

/-- The executor of any judgement points `P` meets the lines of EXEC-021 over the places `P`
reads: `commit` requires both checks and appends the emission (`commitStep_some`), `fail` is a
`settle`, which keeps the marking and the publication queue, and requires a `failCause`
(`failStep_some`, `failCause_cases`). -/
theorem exec021Lines_xstepW (P : XPol N T) :
    exec021Lines P.validIn (fun C s l s' => xstepW P C s l = some s') := by
  intro C _ i
  refine ⟨fun s s' h => ?_, fun s s' h => ?_, fun s s' h => ?_, fun s s' h => ?_,
    fun s s' h => ?_⟩
  · obtain ⟨f, e, hf, he, -, hv, hr, rfl⟩ := commitStep_some h
    exact ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, e, he, hv, hr, rfl⟩
  · obtain ⟨f, -, -, -, rfl⟩ := failStep_some h
    exact ⟨rfl, rfl⟩
  · obtain ⟨f, hf, -, hc, -⟩ := failStep_some h
    exact ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, failCause_cases hc⟩
  · rcases h with ⟨ok, h⟩ | ⟨p, x, h⟩
    · exact retStep_M h
    · exact writeStep_M h
  · obtain ⟨f, e, hf, he, -, hr, -⟩ := tdepositStep_some h
    exact ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, e, he, hr⟩

end Reference

/-- ✓ The reference executor satisfies EXEC-021: its `commit` rule consults both checks over
`validIn` and appends the returned emission, its `fail` rule is a settle with a `failCause`
(`exec021Lines_xstepW` at `refXPol`). -/
@[evidence holds EXEC_021]
theorem EXEC_021_reference {N T : Type} [DecidableEq N] :
    EXEC_021 (RefExec (N := N) (T := T)) :=
  exec021Lines_xstepW refXPol

/-- Under the validation skip of [CONC-026], an executor satisfying EXEC-021 fails a firing only
when its action failed. -/
theorem EXEC_021_skip {N T : Type} [DecidableEq N] {R : XRel N T} (h : EXEC_021 R)
    {C : Cfg N T} (hC : C.SkipsValidation) {s s' : XSt N T} {i : Nat}
    (hs : R C s (.fail i) s') : ∃ f ∈ s.fl, f.id = i ∧ f.out = some .err := by
  have hS : C.SetValidated := fun t d d' _ => by rw [hC.1]
  obtain ⟨f, hf, hid, hout⟩ := (h C hS i).2.2.1 s s' hs
  obtain ⟨hv, hr⟩ := hC
  refine ⟨f, hf, hid, ?_⟩
  rcases hout with ho | ⟨e, -, hb⟩ | ⟨e, -, hb⟩
  · exact ho
  · simp [hv, hr] at hb
  · simp [hr] at hb

/-! ### Examples

Transitions take one token from place `0`. The validator is the reference validator of IO-015
(`cfgValidate ioRefValidate`). A token value `0` stands for a token without a correlation name:
the relay check of the timeout example rejects it, as NU-054 rejects the unit token of an
`Out.place` in a timeout branch. -/

/-- A transition named `t`: one token from `0`, output spec `o`. -/
def exec021_t (o : Out Nat) : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := some o }

/-- The configuration of the examples for transition `t`: the reference validator, a relay check
that rejects the token `0`, timeout outcomes into place `2`. -/
def exec021_cfg (t : Trans Nat) : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := [t] }, timing := fun _ => .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := cfgValidate ioRefValidate,
    relay := fun _ _ e => e.all (·.2 != 0),
    timeoutOut := fun _ _ e => e.map Prod.fst == [2],
    res := 0 }

/-- `And(1, 2)`. -/
def exec021_cAB : Cfg Nat Nat := exec021_cfg (exec021_t (.and (.place 1) (.place 2)))
/-- `Xor(1, 2)`. -/
def exec021_cX : Cfg Nat Nat := exec021_cfg (exec021_t (.xor (.place 1) (.place 2)))
/-- `And(1, Timeout(d, 2))`. -/
def exec021_cTO : Cfg Nat Nat := exec021_cfg (exec021_t (.and (.place 1) (.timeout (.place 2))))

/-- The configurations of the examples validate sets of places (the reference validator satisfies
IO-015, `IO_015_setOnly`). -/
theorem exec021_cfg_set (t : Trans Nat) : (exec021_cfg t).SetValidated :=
  cfgValidate_setValidated IO_015_reference _ rfl

/-- The initial marking: one token `7` in place `0`. -/
def exec021_m0 : QMarking Nat Nat := fun p => if p = 0 then [7] else []

/-- One cycle up to an asynchronous start of `t`. -/
def exec021_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "t" false]

/-- The reference state after `pre`, then `body`, then the end of the pass. -/
def exec021_at (C : Cfg Nat Nat) (body : List (XLbl Nat Nat)) : Option (XSt Nat Nat) :=
  xrun C (xinit exec021_m0 0) (exec021_pre ++ body ++ [.endPass])

/-- `And(1, 2)`: the action writes `70` to `1` and flushes it, writes `80` to `2` and returns. -/
def exec021_runAB : Option (XSt Nat Nat) :=
  exec021_at exec021_cAB [.write 0 1 70, .flush 0, .write 0 2 80, .ret 0 true]

/-- `And(1, 2)`: the action writes `70` to `1`, flushes it and returns without writing `2`. -/
def exec021_runPubOnly : Option (XSt Nat Nat) :=
  exec021_at exec021_cAB [.write 0 1 70, .flush 0, .ret 0 true]

/-- `Xor(1, 2)`: the action writes to both branches and returns. -/
def exec021_runX : Option (XSt Nat Nat) :=
  exec021_at exec021_cX [.write 0 1 50, .write 0 2 60, .ret 0 true]

/-- `And(1, Timeout(d, 2))`: the budget expires with the timeout outcome `x` in place `2`. -/
def exec021_runTO (x : Nat) : Option (XSt Nat Nat) :=
  exec021_at exec021_cTO [.expire 0 [(2, x)]]

/-- Every firing with identity `0` in `s` satisfies `p`. -/
def exec021_all0 (s : XSt Nat Nat) (p : Firing Nat Nat → Bool) : Bool :=
  s.fl.all fun f => f.id != 0 || p f

/-- Read `p` off every firing with identity `0`. -/
theorem exec021_of_all0 {s : XSt Nat Nat} {p : Firing Nat Nat → Bool}
    (h : exec021_all0 s p = true) {f : Firing Nat Nat} (hf : f ∈ s.fl) (hid : f.id = 0) :
    p f = true := by
  have := List.all_eq_true.mp h f hf
  simpa [hid] using this

/-! ### Mutant: validation over the returned tokens only (ruling D27) -/

/-- The judgement points of an executor that validates only the places of the returned emission,
ignoring what the firing published. -/
def exec021_noPubPol {N T : Type} [DecidableEq N] : XPol N T :=
  { refXPol with validIn := fun _ e => e.map Prod.fst }

/-- The executor with those judgement points. -/
def exec021_noPub {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => xstepW exec021_noPubPol C s l = some s'

/-- Mutant reading of EXEC-021 (ruling D27 (b)): validation reads the places of the returned
emission only. The other parts of the lines are as in EXEC-021. -/
def EXEC_021_mutant_noPub {N T : Type} [DecidableEq N] (R : XRel N T) : Prop :=
  exec021Lines (fun _ e => e.map Prod.fst) R

/-- The executor that validates the returned places only kills the mutant: it satisfies the
mutant reading, but not EXEC-021. With `And(1, 2)`, the action publishes `1` and returns `2`
(`exec021_runAB`): over the returned places `[2]` the firing fails, over `[2, 1]` it is valid,
so the fail step breaks line 3 (IO-015 AC7, ruling D27 (a)). -/
@[evidence mutant EXEC_021]
theorem EXEC_021_mutant_noPub_killed :
    EXEC_021_mutant_noPub (exec021_noPub (N := Nat) (T := Nat)) ∧
      ¬ EXEC_021 (exec021_noPub (N := Nat) (T := Nat)) := by
  refine ⟨exec021Lines_xstepW exec021_noPubPol, fun h => ?_⟩
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check (xstepW exec021_noPubPol) (C := exec021_cAB)
    (o := exec021_runAB) (l := .fail 0)
    (p := fun s _ => exec021_all0 s fun f => match f.out with
      | some (.ok e) => exec021_cAB.validate f.t (validIn f e) && exec021_cAB.relay f.t f.deliv e
      | _ => false)
    (by decide)
  obtain ⟨f, hf, hid, hout⟩ := (h exec021_cAB (exec021_cfg_set _) 0).2.2.1 s s' hs
  have hg := exec021_of_all0 hp hf hid
  rcases hout with ho | ⟨e, ho, hb⟩ | ⟨e, ho, -⟩ <;> rw [ho] at hg
  · simp at hg
  · simp only [Bool.and_eq_true] at hg
    rcases hb with hb | hb <;> simp_all
  · simp at hg

/-! ### Violation: depositing without validating -/

/-- An executor that deposits every returned emission, whatever the configured checks say: it
runs as if the validation skip were enabled. -/
def exec021_ignoreValidate {N T : Type} [DecidableEq N] : XRel N T := fun C s l s' =>
  RefExec { C with validate := fun _ _ => true, relay := fun _ _ _ => true } s l s'

/-- ✗ Depositing without validating violates EXEC-021 (line 1): with `Xor(1, 2)` the action
writes both branches (`exec021_runX`), validation rejects, and the executor admits it. -/
@[evidence forbids EXEC_021]
theorem EXEC_021_forbids_ignoreValidate : ¬ EXEC_021 (exec021_ignoreValidate (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check
    (fun C s l => xstep { C with validate := fun _ _ => true, relay := fun _ _ _ => true } s l)
    (C := exec021_cX) (o := exec021_runX) (l := .commit 0)
    (p := fun s _ => exec021_all0 s fun f => match f.out with
      | some (.ok e) => !exec021_cX.validate f.t (validIn f e)
      | _ => true)
    (by decide)
  obtain ⟨f, hf, hid, e, he, hv, -⟩ := (h exec021_cX (exec021_cfg_set _) 0).1 s s' hs
  have hg := exec021_of_all0 hp hf hid
  rw [he] at hg
  simp [hv] at hg

/-! ### Violation: a failure that restores the consumed tokens -/

/-- An executor whose `fail` step puts the consumed tokens back at the head of their places
(a rollback). -/
def exec021_failRestores {N T : Type} [DecidableEq N] : XRel N T := fun C s l s' =>
  match l with
  | .fail i => ((xstep C s l).bind fun s₁ => (s.fl.find? (·.id == i)).map fun f =>
      { s₁ with M := fun p => f.deliv.inputs p ++ s₁.M p }) = some s'
  | _ => RefExec C s l s'

/-- ✗ A failure with rollback violates EXEC-021 (line 2): with `Xor(1, 2)` written in both
branches (`exec021_runX`), the fail step puts the consumed `7` back into place `0`. -/
@[evidence forbids EXEC_021]
theorem EXEC_021_forbids_failRestores : ¬ EXEC_021 (exec021_failRestores (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check
    (fun C s l => (xstep C s l).bind fun s₁ => (s.fl.find? (·.id == 0)).map fun f =>
      { s₁ with M := fun p => f.deliv.inputs p ++ s₁.M p })
    (C := exec021_cX) (o := exec021_runX) (l := .fail 0)
    (p := fun s s' => s'.M 0 != s.M 0) (by decide)
  have := ((h exec021_cX (exec021_cfg_set _) 0).2.1 s s' hs).1
  simp [this] at hp

/-! ### Violation: a failure that withdraws the firing's queued publications -/

/-- An executor whose `fail` step drops the publications of the failed firing that are still
queued. -/
def exec021_dropPublication {N T : Type} [DecidableEq N] : XRel N T := fun C s l s' =>
  match l with
  | .fail i => ((xstep C s l).map fun s₁ => { s₁ with pq := s₁.pq.filter (·.1 != i) }) = some s'
  | _ => RefExec C s l s'

/-- ✗ Withdrawing a failed firing's publication violates EXEC-021 (line 2): with `And(1, 2)` the
action publishes `1` and returns without `2` (`exec021_runPubOnly`, IO-015 AC7); the firing fails
and its queued publication of `70` is dropped instead of deposited. -/
@[evidence forbids EXEC_021]
theorem EXEC_021_forbids_dropPublication :
    ¬ EXEC_021 (exec021_dropPublication (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check
    (fun C s l => (xstep C s l).map fun s₁ => { s₁ with pq := s₁.pq.filter (·.1 != 0) })
    (C := exec021_cAB) (o := exec021_runPubOnly) (l := .fail 0)
    (p := fun s s' => s'.pq.length != s.pq.length) (by decide)
  have := ((h exec021_cAB (exec021_cfg_set _) 0).2.1 s s' hs).2
  simp [this] at hp

/-! ### Violation: validating the timeout outcome (ruling D24, the reading RD-01 recorded) -/

/-- An executor that validates the timeout outcome against the output spec and fails the
firing when the verdict rejects it (the behaviour RD-01 recorded for Java and TypeScript);
otherwise the reference. -/
def exec021_validateTimeoutStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .fail i =>
    match s.fl.find? (·.id == i) with
    | some f =>
      match f.out with
      | some (.timedOut e) =>
        if canSettle C s i f && !C.validate f.t (e.map Prod.fst) then some (settle s i)
        else xstep C s (.fail i)
      | _ => xstep C s (.fail i)
    | none => none
  | l => xstep C s l

/-- The executor of `exec021_validateTimeoutStep`. -/
def exec021_validateTimeout {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec021_validateTimeoutStep C s l = some s'

/-- ✗ Validating the timeout outcome violates EXEC-021 (line 3, ruling D24 (a)): with
`And(1, Timeout(d, 2))` the budget expires (`exec021_runTO 5`), the timeout outcome `[2]` is not
an output branch, and the executor fails a firing the relay check accepts. -/
@[evidence forbids EXEC_021]
theorem EXEC_021_forbids_validateTimeout :
    ¬ EXEC_021 (exec021_validateTimeout (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec021_validateTimeoutStep
    (C := exec021_cTO) (o := exec021_runTO 5) (l := .fail 0)
    (p := fun s _ => exec021_all0 s fun f => match f.out with
      | some (.timedOut e) => exec021_cTO.relay f.t f.deliv e
      | _ => false)
    (by decide)
  obtain ⟨f, hf, hid, hout⟩ := (h exec021_cTO (exec021_cfg_set _) 0).2.2.1 s s' hs
  have hg := exec021_of_all0 hp hf hid
  rcases hout with ho | ⟨e, ho, -⟩ | ⟨e, ho, hr⟩ <;> rw [ho] at hg
  · simp at hg
  · simp at hg
  · simp [hr] at hg

/-! ### Violation: no join-relay check on the timeout outcome (ruling D24 (a)) -/

/-- An executor that deposits every timeout outcome without the join-relay check; otherwise the
reference. -/
def exec021_timeoutNoRelayStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .tdeposit i => tdepositStep { C with relay := fun _ _ _ => true } s i
  | l => xstep C s l

/-- The executor of `exec021_timeoutNoRelayStep`. -/
def exec021_timeoutNoRelay {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec021_timeoutNoRelayStep C s l = some s'

/-- ✗ Skipping the join-relay check on the timeout outcome violates EXEC-021 (line 5, "the
join-relay check of [NU-054] still runs on it"): with `And(1, Timeout(d, 2))` the budget expires
with the outcome `0` in `2` (`exec021_runTO 0`), which the relay check rejects, and the executor
deposits it. -/
@[evidence forbids EXEC_021]
theorem EXEC_021_forbids_timeoutNoRelay :
    ¬ EXEC_021 (exec021_timeoutNoRelay (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec021_timeoutNoRelayStep
    (C := exec021_cTO) (o := exec021_runTO 0) (l := .tdeposit 0)
    (p := fun s _ => exec021_all0 s fun f => match f.out with
      | some (.timedOut e) => !exec021_cTO.relay f.t f.deliv e
      | _ => true)
    (by decide)
  obtain ⟨f, hf, hid, e, he, hr⟩ := (h exec021_cTO (exec021_cfg_set _) 0).2.2.2.2 s s' hs
  have hg := exec021_of_all0 hp hf hid
  rw [he] at hg
  simp [hr] at hg

/-! ### Violation: depositing produced tokens before validation -/

/-- An executor that deposits a returned emission at the return step, before any validation,
when validation would reject it; it settles as the reference. -/
def exec021_depositAtReturnStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok => (xstep C s (.ret i ok)).map fun s₁ =>
      match s.fl.find? (·.id == i) with
      | some f =>
        if ok && !C.validate f.t (validIn f f.buf) then { s₁ with M := qAppend s₁.M f.buf } else s₁
      | none => s₁
  | l => xstep C s l

/-- The executor of `exec021_depositAtReturnStep`. -/
def exec021_depositAtReturn {N T : Type} [DecidableEq N] : XRel N T :=
  fun C s l s' => exec021_depositAtReturnStep C s l = some s'

/-- ✗ Depositing produced tokens before validating them violates EXEC-021 (line 4, the first and
second shall sentences): with `Xor(1, 2)` the action writes both branches and returns, and the
return step deposits `50` in `1`. Its commit and fail steps are the reference's, so lines 1 to 3
alone do not reject it. -/
@[evidence forbids EXEC_021]
theorem EXEC_021_forbids_depositAtReturn :
    ¬ EXEC_021 (exec021_depositAtReturn (N := Nat) (T := Nat)) := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check exec021_depositAtReturnStep (C := exec021_cX)
    (o := xrun exec021_cX (xinit exec021_m0 0) (exec021_pre ++ [.write 0 1 50, .write 0 2 60]))
    (l := .ret 0 true) (p := fun s s' => s'.M 1 != s.M 1) (by decide)
  have := (h exec021_cX (exec021_cfg_set _) 0).2.2.2.1 s s' (Or.inl ⟨true, hs⟩)
  simp [this] at hp

/-! ### Every line exercised -/

/-- Every line of EXEC-021 is exercised by the reference, transitions taking `7` from place `0`:
with `And(1, 2)`, a firing that published `70` to `1` and returned `80` for `2` is admitted
(validated over `[2, 1]`, AC1) and deposits `80` at `2` (line 1); with `Xor(1, 2)` written in
both branches the firing fails, `1` and `2` stay empty and the consumed `7` is not restored
(lines 2 and 3, AC3, AC5, the test derivation); with `And(1, 2)` and only `1` published, the
firing fails and its publication `70` still lands in `1` (line 2, AC5); with
`And(1, Timeout(d, 2))` the timeout outcome `5` is deposited unvalidated, and the timeout
outcome `0`, which the relay check rejects, fails the firing (line 3, ruling D24 (a)); the
action of a firing returns (the premise of line 4). -/
@[evidence nonvacuous EXEC_021]
theorem EXEC_021_nonvacuous :
    (∃ s s', RefExec exec021_cAB s (.commit 0) s' ∧ s'.M 2 = [80] ∧ s'.pq.length = 1) ∧
    (∃ s s', RefExec exec021_cX s (.fail 0) s' ∧
      s'.M 0 = [] ∧ s'.M 1 = [] ∧ s'.M 2 = []) ∧
    (∃ s s', RefExec exec021_cAB s (.publish 0) s' ∧ s'.M 1 = [70] ∧ s'.M 2 = []) ∧
    (∃ s s', RefExec exec021_cTO s (.tdeposit 0) s' ∧ s'.M 2 = [5]) ∧
    (∃ s s', RefExec exec021_cTO s (.fail 0) s' ∧ s'.M 2 = []) ∧
    (∃ s s', RefExec exec021_cAB s (.ret 0 true) s') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec021_cAB) (o := exec021_runAB) (l := .commit 0)
      (p := fun _ s' => s'.M 2 == [80] && s'.pq.length == 1) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec021_cX) (o := exec021_runX) (l := .fail 0)
      (p := fun _ s' => s'.M 0 == [] && s'.M 1 == [] && s'.M 2 == []) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp.1.1, hp.1.2, hp.2⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec021_cAB)
      (o := (exec021_runPubOnly.bind fun s => xstep exec021_cAB s (.fail 0)).bind
        fun s => xstep exec021_cAB s .endCompletions)
      (l := .publish 0) (p := fun _ s' => s'.M 1 == [70] && s'.M 2 == []) (by decide)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, s', hs, hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec021_cTO) (o := exec021_runTO 5) (l := .tdeposit 0)
      (p := fun _ s' => s'.M 2 == [5]) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, hp⟩ := step_of_check xstep (C := exec021_cTO) (o := exec021_runTO 0) (l := .fail 0)
      (p := fun _ s' => s'.M 2 == []) (by decide)
    exact ⟨s, s', hs, by simpa using hp⟩
  · obtain ⟨s, s', -, hs, -⟩ := step_of_check xstep (C := exec021_cAB)
      (o := xrun exec021_cAB (xinit exec021_m0 0) (exec021_pre ++ [.write 0 1 70, .write 0 2 80]))
      (l := .ret 0 true) (p := fun _ _ => true) (by decide)
    exact ⟨s, s', hs⟩

/-- The relay check on a flushed batch (the reference's `flushStep`, Rust's flush guard): with
`And(1, 2)` the action flushes the token `0` to `1`, which the relay check rejects, then writes
`5` to `1` and `80` to `2` and returns. The batch is dropped, and the firing is failed although
its returned emission passes both checks: its outcome is an error (line 3's first case). -/
theorem exec021_relayBad_fails :
    ∃ s s', RefExec exec021_cAB s (.fail 0) s' ∧ s'.pq = [] ∧ s'.M 1 = [] ∧
      ¬ ∃ s'', RefExec exec021_cAB s (.commit 0) s'' := by
  obtain ⟨s, s', ho, hs, hp⟩ := step_of_check xstep (C := exec021_cAB)
    (o := exec021_at exec021_cAB [.write 0 1 0, .flush 0, .write 0 1 5, .write 0 2 80, .ret 0 true])
    (l := .fail 0) (p := fun _ s' => s'.pq.isEmpty && s'.M 1 == []) (by decide)
  have hc : xstep exec021_cAB s (.commit 0) = none := by
    have h' : (exec021_at exec021_cAB
        [.write 0 1 0, .flush 0, .write 0 1 5, .write 0 2 80, .ret 0 true]).bind
        (fun s => (xstep exec021_cAB s (.commit 0)).isNone) = some true := by decide
    rw [ho] at h'
    simpa using h'
  simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hp
  exact ⟨s, s', hs, hp.1, hp.2, fun ⟨s'', h''⟩ => by
    simp [RefExec, hc] at h''⟩

end Libpetri.Spec
