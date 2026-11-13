import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec

set_option linter.missingDocs true

/-!
# ENV-004: inject() Completion Semantics (`spec/06-environment-places.md`)

A requirement block over the executor model (`RefExec`, `Reference/Exec.lean`). An accepted
injection request queues its event with a ticket drawn from the supply (`XSt.nextId`); the
admission signal of that event (Java's future, TypeScript's promise) is not a field of the state,
so the block reads it off the steps. The signal of ticket `k` completes with **true** at the step
`inject k`, and with **false** at any other step that removes `k` from the event queue: a
`discard k` once the executor is closed or stopped, an immediate termination (`terminateNow`,
which Java answers with false at once), or a `finish` that clears the queue (rulings D44 (a),
D47 (c); design R17). These are exactly the answering steps of ENV-006's line 4: ENV-006's
`answersTicket` and this block's `env004_answers` both read the event queue and are equal on every
step (`env004_answers_eq_answersTicket`, `ConsistencyExec.lean`); on the reference both agree with
the label-based restatement `env004_labelAnswers` (`ENV_004_answers_agree_reference`).

Four lines: the true answer is the step that puts the token at the tail of its place and changes
the marking in no other way (line 1); the false answer leaves the marking unchanged and comes only
once the executor is closed or stopped, or at the end of the run (line 2); along a run, a ticket
is answered at most once (line 3, a trace line read with `at-most-once` of `Ears.lean`); and an
accepted request queues a ticket of its own, never merging into an event already queued (line 4).

Lines 3 and 4 read states whose queued events carry pairwise distinct tickets, each below the
supply (`env004_Fresh`); the initial state has an empty queue, and the reference keeps the
property on every step (`env004_fresh_shape`).
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## Block-local terms -/

section Terms

variable {N T : Type}

/-- The tickets of the events queued in `s`, in queue order. -/
def env004_tickets (s : XSt N T) : List Nat := s.eq.map Prod.fst

/-- The label injects the event with ticket `k`: the admission signal of `k` completes with true. -/
def env004_isInject (k : Nat) : XLbl N T → Bool
  | .inject j => j == k
  | _ => false

/-- The step removes ticket `k` from the event queue without injecting it: the admission signal
of `k` completes with false. -/
def env004_isDrop (k : Nat) (st : XStep N T) : Bool :=
  !env004_isInject k st.2.1 && (env004_tickets st.1).contains k &&
    !(env004_tickets st.2.2).contains k

/-- The step answers the admission signal of ticket `k`, with true (an injection) or with false
(a drop). -/
def env004_answers (k : Nat) (st : XStep N T) : Bool :=
  env004_isInject k st.2.1 || env004_isDrop k st

/-- The queued events of `s` carry pairwise distinct tickets, each one the supply has already
handed out. The initial state has an empty queue, so it holds there. -/
def env004_Fresh (s : XSt N T) : Prop :=
  (env004_tickets s).Nodup ∧ ∀ n ∈ env004_tickets s, n < s.nextId

end Terms

/-! ## ENV-004: inject() Completion Semantics -/

requirement ENV_004
  id "ENV-004"
  title "inject() Completion Semantics"
  kind B
  scope "executors with an admission signal (Java, TypeScript); Rust and Python report acceptance only (ruling D44 (a))"
  source verbatim "spec/06-environment-places.md"
  quote "In Java and TypeScript the inject operation returns a future/promise that completes with true when the token has been added to the marking."
        "In Rust and Python the return value indicates whether the injection was accepted; in Java and TypeScript the future's value indicates whether the token was injected."
        "In Java and TypeScript the future is the admission signal of the accepted event."
        "The orchestrator completes it with true in the external-events step ([EXEC-001] step 2), when it adds the token to the marking."
        "It completes it with false when it discards the event because the executor is closed or stopped ([ENV-013], [ENV-015]), or when the run ends with the event still queued ([EXEC-041], [EXEC-042])."
        "A drain does not discard the events accepted before it: the orchestrator still injects them ([ENV-011]), unless close() is called or the run ends first."
        "Each accepted event has an admission signal of its own: an injection into a place whose earlier event is still queued neither replaces that event nor merges with it ([ENV-003])."
        "*When* the executor accepts an injection request, it *shall* queue the event as a new event, apart from every event already queued."
        "*When* the executor completes the admission signal of an accepted event with true, it *shall*, in the same step, add the event's token at the tail of its place's queue and change no other part of the marking."
        "*If* the executor completes the admission signal of an accepted event with false, *then* it *shall* leave the marking unchanged in that step."
        "*If* a step leaves the executor open or draining and does not end the run, *then* the executor *shall not* complete the admission signal of an accepted event with false in that step."
        "The executor *shall* complete the admission signal of an accepted event at most once."
  reading "For every executor R and every configuration C, and in the first three lines for every ticket k:"
          "an inject step of k (the admission signal of k completes with true) starts in a state whose event queue holds an event with ticket k for some place p and token x, and its marking is the source marking with x appended at the tail of p and no other change;"
          "a step that removes the ticket k from the event queue and is not the inject step of k (the signal completes with false) leaves the marking unchanged, and after it the executor is closed or stopped, or the run has finished;"
          "on every run of R that starts in a state whose queued events carry pairwise distinct tickets, each below the ticket supply, at most one step answers k (injects it, or removes it from the queue otherwise);"
          "an accepted injection request made in a state whose queued events carry pairwise distinct tickets, each below the ticket supply, leaves some ticket queued that was not queued before it."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. An accepted request (request p x accepted, ENV-003, ENV-006) queues the event (k, p, x) in s.eq with the ticket k = s.nextId and advances the supply. The admission signal is not part of the state: the block reads it off the steps. The true answer of ticket k is the label inject k; the false answer is every other step after which k is no longer queued. In the reference those are discard k (once the executor is closed or stopped), terminateNow (ENV-015, ruling D47 (c): Java completes the queued events with false inside terminateNow) and the finish steps that clear the queue (finish closed, stopped or terminal; design R17). The witness is the reference executor RefExec (Reference/Exec.lean)."
          "One signal for ENV-004 and ENV-006. ENV-006's line 4 and this block both name the answering steps by what they do to the queue (the injection of k, or a step that takes the event with ticket k out of the event queue): ENV-006's answersTicket and this block's env004_answers are equal on every step (env004_answers_eq_answersTicket, ConsistencyExec.lean), which is what lets lines 1 and 2 constrain the value and the marking effect of every answer ENV-006 asks for. On every reference step from a state with distinct queued tickets both also agree with a label-based restatement, env004_labelAnswers (the injection or the discard of k, or an immediate termination or a finish while k is queued; ENV_004_answers_agree_reference), so the reference answers one ticket at one step in both blocks."
          "Scope, ruling D44 (a). Only Java and TypeScript have an admission signal, as the first two quoted sentences now say. Rust and Python return, at the call, whether the event was accepted; that reply is the request step's, stated by ENV-006 (and ENV-002 for a place that is not an environment place). The quoted second sentence keeps the two meanings apart: the call's reply says whether the request was accepted (ENV-006's lines 1 and 2), the future's value says whether the token was injected (lines 1 and 2 here), so an accepted event can still be answered false. A run of RefExec in which the close comes after the injections of the events sent before it is Rust's behaviour at a close (ruling D44 (a)), so the shared model holds both. Result-less forms (Java injectAsync, TypeScript injectNoAwait) have no signal to complete and are outside the block."
          "Ruling D44 (a), from env-a ENV-R3: the old clause that the signal completes after enablement has been recalculated is dropped. Java and TypeScript complete the signal inside the external-events step, before the enablement update of step 3, and line 1 reads exactly that step: the inject step is the one that deposits. The quoted first, third and fourth sentences are line 1 for what the answering step changes. Which loop phase the inject step runs in is EXEC-001's subject, not this block's: EXEC-001's line 5 orders the injections of step 2 before the next update, and ruling D70 (a) lets the wait itself inject (Rust, which has no signal; the reference offers inject in the phases events and await). Line 1 therefore has no phase condition, and the step-2 placement in the fourth quoted sentence is checked there."
          "AC1 (true when the token is in the marking) is line 1: the inject step of k appends the event's token at the tail of its place and changes the marking in no other way. An executor that answers true and lands the token later, through another queue, breaks it (ENV_004_forbids_earlyTrue). The first part of ENV_004_nonvacuous is the test derivation: a request is accepted, the event is injected, and after the answer the token is in its place."
          "AC2 has two halves. The call-time half, an inject() call made while the executor is draining, closed or finished is refused and changes nothing, is ENV-006's lines 1 and 2 (ENV_006.lean: Refusing is a mode that is not open, or a finished run, which is where the 'or finished' of AC2 comes from); this block does not restate it. The queued half is line 2 and the quoted fifth sentence: an accepted event is answered false only once the executor is closed or stopped, or when the run ends with the event still queued (ENV_004_nonvacuous parts three and four), and the false answer leaves the marking unchanged (ENV_004_forbids_discardDeposits). AC2's drain clause and the quoted drain sentence are line 2's mode half: while the executor drains and the run goes on, no queued event is answered false. An executor that discards a queued event because the executor is draining when step 2 reaches it breaks that half (ENV_004_forbids_falseWhileDraining), while the reference injects an event accepted before a drain and answers it true (ENV_004_nonvacuous part two). The clause allows a false answer during a drain when the run ends (a terminal place marked, EXEC-042) or close() escalates the drain (ENV-013), which is why AC2 does not promise true for every event queued before a drain. That such an event is in the end injected is ENV-011's and ENV-006's line 4, not this block's."
          "AC3 (at most once) is line 3 and the last quoted sentence. An executor that injects the event but leaves it queued, then discards it at a close, answers it twice (true, then false) and breaks only line 3 (ENV_004_forbids_trueThenDiscard, env004_trueThenDiscard_onlyLine3). The line identifies the event by its ticket. Tickets are drawn once from one supply (the naming convention of the glossary, shared with firing identities), and the premise says that at the start of the run the queued tickets are distinct and below the supply: true at every initial state (the queue is empty) and kept by every reference step (env004_fresh_shape). Without it the reference itself answers a duplicated ticket twice (env004_needs_fresh). An executor that hands out a ticket already queued answers it twice along the run and breaks line 3 as well."
          "Line 4 is the quoted sentence on an admission signal of its own and the EARS sentence on queueing the event as a new event. Without it an executor that keeps the pending injections per place, so that a second accepted request into the same place overwrites the first event's token under the first event's ticket, keeps lines 1 to 3 (env004_coalesce_onlyLine4: no ticket ever leaves the queue without its inject step), yet one of the two callers told accepted never sees its token reach the marking. Line 4 rejects it (ENV_004_forbids_coalesce). ENV-003's line 1 pins the exact ticket (the supply's next one), the place, the token and the FIFO position of the new event (ruling D48 (a)); line 4 keeps only what the signal needs, a ticket of its own."
          "Lines 2 and 3 together say that a token answered false never reaches the marking through its own event: the drop leaves the marking unchanged, and no later inject step answers the same ticket. The quoted sentences on which events a close discards are ENV-013's subject, the FIFO order of injection is ENV-003's (ruling D48 (a)), and that every accepted event is eventually answered is ENV-006's line 4; this block reads only the answering step and what it changes."
          "Out of the model: a deposit that throws, which Java and TypeScript report by completing the signal exceptionally (the model's deposit cannot fail, so line 3 says at most one answer, not exactly one); the TokenAdded event of the injection (the event tier, W7). Java and TypeScript leave the events queued at a close and complete them with false when the loop ends, after the firings in flight; the reference discards them in step 2 of the cycles after the close. Both are after the close and before the end of the run, and line 2 constrains only which step answers false and what it changes, not how long after the close it comes."
  signoff "2026-11-13 7d20bbf9de3d56df ai"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C,
      (∀ k,
        (on (fun s s' => R C s (.inject k) s'),
          shall (fun s s' => ∃ p x, (k, p, x) ∈ s.eq ∧ s'.M = qAppendOne s.M p x)) ∧
        (∀ s l s', R C s l s' → env004_isDrop k (s, l, s') = true →
          s'.M = s.M ∧ (s'.mode.closing = true ∨ isExecPhase s'.phase = false)) ∧
        (∀ s0 tr, env004_Fresh s0 → XRun R C s0 tr → (at-most-once (env004_answers k)) tr)) ∧
      (on (fun s s' => env004_Fresh s ∧ ∃ p x, R C s (.request p x .accepted) s'),
        shall (fun s s' => ∃ j, j ∉ env004_tickets s ∧ j ∈ env004_tickets s'))

/- The pinned readable form of ENV-004: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.ENV_004 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T),
    (∀ (k : ℕ),
        (on fun s s' => R C s (XLbl.inject k) s', shall fun s s' =>
            ∃ p x, (k, p, x) ∈ s.eq ∧ s'.M = qAppendOne s.M p x) ∧
          (∀ (s : XSt N T) (l : XLbl N T) (s' : XSt N T),
              R C s l s' →
                env004_isDrop k (s, l, s') = true →
                  s'.M = s.M ∧ (s'.mode.closing = true ∨ isExecPhase s'.phase = false)) ∧
            ∀ (s0 : XSt N T) (tr : List (XStep N T)),
              env004_Fresh s0 → XRun R C s0 tr → (at-most-once env004_answers k) tr) ∧
      on fun s s' => env004_Fresh s ∧ ∃ p x, R C s (XLbl.request p x Reply.accepted) s', shall fun s s' =>
        ∃ j ∉ env004_tickets s, j ∈ env004_tickets s'
-/
#guard_msgs in #print ENV_004

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- The label is one of the steps that may drop queued events: a discard, an immediate
termination or a finish. -/
def env004_dropLabel {N T : Type} : XLbl N T → Bool
  | .discard _ | .terminateNow | .finish _ => true
  | _ => false

/-- What one step does to the event queue: the queue is kept; or an accepted request appends one
event with the ticket the supply hands out; or the inject step of `j` removes the head event `j`;
or a discard, an immediate termination or a finish shrinks the queue to a suffix with the marking
kept, and after the step the executor is closed or stopped, or the run has finished. In every
case the supply never goes back. -/
def env004_Shape (l : XLbl N T) (s s' : XSt N T) : Prop :=
  s.nextId ≤ s'.nextId ∧
    (s'.eq = s.eq ∨
     (∃ p x, s'.eq = s.eq ++ [(s.nextId, p, x)] ∧ s.nextId < s'.nextId) ∨
     (∃ j p x, l = .inject j ∧ s.eq = (j, p, x) :: s'.eq) ∨
     (s'.eq <:+ s.eq ∧ s'.M = s.M ∧ (s'.mode.closing = true ∨ isExecPhase s'.phase = false) ∧
       env004_dropLabel l = true))

omit [DecidableEq N] in
/-- A step that keeps the queue and does not lower the supply has the shape. -/
theorem env004_shape_same {l : XLbl N T} {s s' : XSt N T} (he : s'.eq = s.eq)
    (hn : s.nextId ≤ s'.nextId) : env004_Shape l s s' :=
  ⟨hn, Or.inl he⟩

omit [DecidableEq N] in
/-- A step that empties the queue, keeps the marking and the supply, and ends the run or leaves the
executor closed or stopped has the shape. -/
theorem env004_shape_clear {l : XLbl N T} {s s' : XSt N T} (he : s'.eq = []) (hM : s'.M = s.M)
    (hn : s'.nextId = s.nextId)
    (hm : s'.mode.closing = true ∨ isExecPhase s'.phase = false)
    (hl : env004_dropLabel l = true) : env004_Shape l s s' :=
  ⟨hn ▸ Nat.le_refl _, Or.inr (Or.inr (Or.inr ⟨he ▸ List.nil_suffix, hM, hm, hl⟩))⟩

/-- Every reference step (at any judgement points `P`) has the shape: only `request` adds an
event, with a fresh ticket; `inject` removes the head; `discard`, `terminateNow` and the `finish`
steps drop events with the marking kept, once the executor is closed or stopped or the run ends;
every other step keeps the queue. -/
theorem env004_shape {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : xstepW P C s l = some s') : env004_Shape l s s' := by
  cases l with
  | delay δ => obtain rfl := xstepW_delay h; exact env004_shape_same rfl (Nat.le_refl _)
  | write i p x =>
    obtain ⟨-, -, -, rfl⟩ := writeStep_some h; exact env004_shape_same rfl (Nat.le_refl _)
  | flush i =>
    obtain ⟨-, -, -, -, -, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ := flushStep_some h
    · exact env004_shape_same rfl (Nat.le_refl _)
    · exact env004_shape_same rfl (Nat.le_refl _)
  | ret i ok =>
    obtain ⟨-, -, -, rfl⟩ := retStep_some h; exact env004_shape_same rfl (Nat.le_refl _)
  | expire i e =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := expireStep_some h
    exact env004_shape_same rfl (Nat.le_refl _)
  | request p x r =>
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact ⟨Nat.le_succ _, Or.inr (Or.inl ⟨p, x, rfl, Nat.lt_succ_self _⟩)⟩
    · exact env004_shape_same rfl (Nat.le_refl _)
  | drain => obtain ⟨-, rfl⟩ := drainStep_some h; exact env004_shape_same rfl (Nat.le_refl _)
  | close => obtain ⟨-, rfl⟩ := closeStep_some h; exact env004_shape_same rfl (Nat.le_refl _)
  | terminateNow =>
    obtain ⟨-, rfl⟩ := terminateStep_some h
    exact env004_shape_clear rfl rfl rfl (Or.inl rfl) rfl
  | commit i =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := commitStep_some h
    exact env004_shape_same rfl (Nat.le_refl _)
  | fail i =>
    obtain ⟨-, -, -, -, rfl⟩ := failStep_some h; exact env004_shape_same rfl (Nat.le_refl _)
  | tdeposit i =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := tdepositStep_some h
    exact env004_shape_same rfl (Nat.le_refl _)
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h
    exact env004_shape_same rfl (Nat.le_refl _)
  | publish i =>
    obtain ⟨-, -, -, -, -, rfl⟩ := publishStep_some h
    exact env004_shape_same rfl (Nat.le_refl _)
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h
    exact env004_shape_same rfl (Nat.le_refl _)
  | inject j =>
    obtain ⟨p, x, rest, he, -, -, -, rfl⟩ := injectStep_some h
    exact ⟨Nat.le_refl _, Or.inr (Or.inr (Or.inl ⟨j, p, x, rfl, he⟩))⟩
  | discard j =>
    obtain ⟨p, x, rest, he, -, hm, -, rfl⟩ := discardStep_some h
    exact ⟨Nat.le_refl _, Or.inr (Or.inr (Or.inr ⟨he ▸ List.suffix_cons _ _, rfl, Or.inl hm, rfl⟩))⟩
  | snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h; exact env004_shape_same rfl (Nat.le_refl _)
  | endEvents =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h; exact env004_shape_same rfl (Nat.le_refl _)
  | update => obtain ⟨-, -, rfl⟩ := xstepW_update h; exact env004_shape_same rfl (Nat.le_refl _)
  | deadline ns =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h; exact env004_shape_same rfl (Nat.le_refl _)
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h
      exact env004_shape_clear rfl rfl rfl (Or.inr rfl) rfl
    | closed =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h
      exact env004_shape_clear rfl rfl rfl (Or.inr rfl) rfl
    | terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
      exact env004_shape_clear rfl rfl rfl (Or.inr rfl) rfl
    | stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h
      exact env004_shape_clear rfl rfl rfl (Or.inr rfl) rfl
  | begin => obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h; exact env004_shape_same rfl (Nat.le_refl _)
  | start n sy =>
    obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := startStep_some h
    exact env004_shape_same rfl (Nat.le_succ _)
  | lose n =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h
    exact env004_shape_same rfl (Nat.le_refl _)
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h; exact env004_shape_same rfl (Nat.le_refl _)
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    exact env004_shape_same rfl (Nat.le_refl _)
  | wake => obtain ⟨-, -, rfl⟩ := wakeStep_some h; exact env004_shape_same rfl (Nat.le_refl _)

omit [DecidableEq N] in
/-- A drop of ticket `k` in a step of that shape keeps the marking and leaves the executor closed
or stopped, or ends the run: the queue can lose `k` without an inject step of `k` only in the
fourth case of the shape. -/
theorem env004_drop_of_shape {k : Nat} {l : XLbl N T} {s s' : XSt N T}
    (hs : env004_Shape l s s') (hd : env004_isDrop k (s, l, s') = true) :
    s'.M = s.M ∧ (s'.mode.closing = true ∨ isExecPhase s'.phase = false) := by
  simp only [env004_isDrop, Bool.and_eq_true, Bool.not_eq_true'] at hd
  obtain ⟨⟨hni, hin⟩, hout⟩ := hd
  have hin' : k ∈ env004_tickets s := by simpa using hin
  have hout' : k ∉ env004_tickets s' := by simpa using hout
  rcases hs.2 with he | ⟨p, x, he, -⟩ | ⟨j, p, x, rfl, he⟩ | ⟨-, hM, hm, -⟩
  · exact absurd (by simpa [env004_tickets, he] using hin') hout'
  · exact absurd (by simp [env004_tickets, he] at hin' ⊢; exact Or.inl hin') hout'
  · have hjk : j ≠ k := by simpa [env004_isInject] using hni
    simp only [env004_tickets, he, List.map_cons, List.mem_cons] at hin'
    rcases hin' with hk | hk
    · exact absurd hk.symm hjk
    · exact absurd hk hout'
  · exact ⟨hM, hm⟩

omit [DecidableEq N] in
/-- The shape keeps `env004_Fresh`: a kept or shrunk queue keeps distinct tickets below the
supply, and an appended event carries the ticket the supply hands out, above every queued one. -/
theorem env004_fresh_shape {l : XLbl N T} {s s' : XSt N T} (hs : env004_Shape l s s')
    (hf : env004_Fresh s) : env004_Fresh s' := by
  obtain ⟨hnd, hlt⟩ := hf
  have up : ∀ n ∈ env004_tickets s, n < s'.nextId := fun n hn =>
    Nat.lt_of_lt_of_le (hlt n hn) hs.1
  rcases hs.2 with he | ⟨p, x, he, hgt⟩ | ⟨j, p, x, -, he⟩ | ⟨hsuf, -, -, -⟩
  · unfold env004_Fresh env004_tickets at *
    rw [he]
    exact ⟨hnd, up⟩
  · unfold env004_Fresh env004_tickets at *
    rw [he, List.map_append]
    refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, ?_⟩, ?_⟩
    · intro a ha b hb he'
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      have := hlt a ha
      omega
    · intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · exact up n hn
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hn
        omega
  · unfold env004_Fresh env004_tickets at *
    rw [he, List.map_cons] at hnd up
    exact ⟨(List.nodup_cons.mp hnd).2, fun n hn => up n (List.mem_cons_of_mem _ hn)⟩
  · have hsm : env004_tickets s' <:+ env004_tickets s := hsuf.map _
    exact ⟨hnd.sublist hsm.sublist, fun n hn => up n (hsm.subset hn)⟩

/-- Ticket `k` was handed out and is no longer queued: its signal has been answered. -/
def env004_Gone (k : Nat) (s : XSt N T) : Prop := k ∉ env004_tickets s ∧ k < s.nextId

omit [DecidableEq N] in
/-- The shape keeps `env004_Gone k`: a kept or shrunk queue gains no ticket, and an appended
event carries the supply's ticket, above `k`. -/
theorem env004_gone_shape {k : Nat} {l : XLbl N T} {s s' : XSt N T}
    (hs : env004_Shape l s s') (hg : env004_Gone k s) : env004_Gone k s' := by
  obtain ⟨hni, hlt⟩ := hg
  refine ⟨fun hk => ?_, Nat.lt_of_lt_of_le hlt hs.1⟩
  rcases hs.2 with he | ⟨p, x, he, -⟩ | ⟨j, p, x, -, he⟩ | ⟨hsuf, -, -, -⟩
  · exact hni (by simpa [env004_tickets, he] using hk)
  · simp only [env004_tickets, he, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_singleton] at hk
    rcases hk with hk | hk
    · exact hni hk
    · omega
  · exact hni (by simp only [env004_tickets, he, List.map_cons]; exact List.mem_cons_of_mem _ hk)
  · exact hni ((hsuf.map Prod.fst).subset hk)

/-- An answer of `k` in a reference step from a fresh state leaves `k` gone: an inject step of
`k` removes the head event, the only one with ticket `k`, and a drop removes `k` by definition. -/
theorem env004_gone_answer {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {k : Nat} (h : xstepW P C s l = some s') (hf : env004_Fresh s)
    (ha : env004_answers k (s, l, s') = true) : env004_Gone k s' := by
  have hs := env004_shape h
  simp only [env004_answers, Bool.or_eq_true] at ha
  rcases ha with hi | hd
  · cases l with
    | inject j =>
      have hjk : j = k := by simpa [env004_isInject] using hi
      subst hjk
      obtain ⟨p, x, rest, he, -, -, -, rfl⟩ := injectStep_some h
      have hnd := hf.1
      have hlt := hf.2 j (by simp [env004_tickets, he])
      simp only [env004_tickets, he, List.map_cons] at hnd
      exact ⟨(List.nodup_cons.mp hnd).1, hlt⟩
    | _ => simp [env004_isInject] at hi
  · simp only [env004_isDrop, Bool.and_eq_true, Bool.not_eq_true'] at hd
    obtain ⟨⟨-, hin⟩, hout⟩ := hd
    exact ⟨by simpa using hout,
      Nat.lt_of_lt_of_le (hf.2 k (by simpa using hin)) hs.1⟩

/-- No reference step answers a gone ticket: an inject step of `k` needs `k` at the head of the
queue, and a drop needs `k` in the queue. -/
theorem env004_noAnswer_gone {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {k : Nat} (h : xstepW P C s l = some s') (hg : env004_Gone k s) :
    env004_answers k (s, l, s') = false := by
  have hdrop : env004_isDrop k (s, l, s') = false := by
    simp only [env004_isDrop, Bool.and_eq_false_iff]
    left; right
    simpa using hg.1
  have hinj : env004_isInject k l = false := by
    cases l with
    | inject j =>
      cases hjk : (j == k) with
      | false => simp [env004_isInject, hjk]
      | true =>
        have : j = k := by simpa using hjk
        subst this
        obtain ⟨p, x, rest, he, -⟩ := injectStep_some h
        exact absurd (by simp [env004_tickets, he]) hg.1
    | _ => rfl
  simp [env004_answers, hdrop, hinj]

/-- The scan of line 3 over a run of the reference step at judgement points `P`: with the
answered memory `b`, every step is accepted, provided the state is fresh and a set memory means
the ticket is gone. -/
theorem env004_scan {P : XPol N T} {C : Cfg N T} {k : Nat} :
    ∀ {s : XSt N T} {tr : List (XStep N T)} (b : Bool),
      XRun (fun C s l s' => xstepW P C s l = some s') C s tr → env004_Fresh s →
      (b = true → env004_Gone k s) →
      (afterNever (env004_answers k) (env004_answers k)).scan b tr = true
  | _, [], _, _, _, _ => rfl
  | s, (s₁, l, s') :: rest, b, ⟨h1, hstep, hrest⟩, hf, hb => by
    simp only at h1
    subst h1
    have hf' := env004_fresh_shape (env004_shape hstep) hf
    have hok : (b && env004_answers k (s₁, l, s')) = false := by
      cases b with
      | false => rfl
      | true => rw [env004_noAnswer_gone hstep (hb rfl)]; rfl
    have hnext : (b || env004_answers k (s₁, l, s')) = true → env004_Gone k s' := by
      intro hn
      cases ha : env004_answers k (s₁, l, s') with
      | true => exact env004_gone_answer hstep hf ha
      | false =>
        rw [ha, Bool.or_false] at hn
        exact env004_gone_shape (env004_shape hstep) (hb hn)
    show (!(b && env004_answers k (s₁, l, s')) &&
      (afterNever (env004_answers k) (env004_answers k)).scan
        (b || env004_answers k (s₁, l, s')) rest) = true
    rw [hok, env004_scan _ hrest hf' hnext]
    rfl

/-- The executor of any judgement points `P` satisfies the lines of ENV-004: its inject step
appends the head event's token (`injectStep_some`); a drop happens only in the fourth case of the
step shape (`env004_drop_of_shape`); and an answered ticket is gone for good
(`env004_scan`). -/
theorem env004_xstepW (P : XPol N T) :
    ENV_004 (fun C s l s' => xstepW P C s l = some s') := by
  intro C
  refine ⟨fun k => ⟨fun s s' h => ?_, fun s l s' h hd => env004_drop_of_shape (env004_shape h) hd,
    fun s0 tr hf hr => env004_scan false hr hf (fun h => absurd h Bool.false_ne_true)⟩, ?_⟩
  · obtain ⟨p, x, rest, he, -, -, -, rfl⟩ := injectStep_some h
    exact ⟨p, x, by simp [he], rfl⟩
  · rintro s s' ⟨hf, p, x, h⟩
    obtain ⟨-, ⟨-, rfl⟩ | ⟨hr, -⟩⟩ := requestStep_some h
    · exact ⟨s.nextId, fun hk => Nat.lt_irrefl _ (hf.2 _ hk), by simp [env004_tickets]⟩
    · exact absurd rfl hr

/-! #### The answering step of ENV-006 -/

/-- A label-based restatement of the answering step of ENV-006's line 4: the injection or the
discard of ticket `k`, or an immediate termination or a finish while `k` is queued. ENV-006's
`answersTicket` reads the event queue instead, as `env004_answers` does; on the reference the
three agree (`ENV_004_answers_agree_reference`, `env004_answers_eq_answersTicket`). -/
def env004_labelAnswers (k : Nat) (e : XStep N T) : Bool :=
  match e.2.1 with
  | .inject j | .discard j => j == k
  | .terminateNow | .finish _ => decide (k ∈ e.1.eq.map (·.1))
  | _ => false

omit [DecidableEq N] in
/-- A step that takes the head event `j` off the queue drops `k` exactly when it is not the inject
step of `k` and `j = k`, provided the queued tickets are distinct. -/
theorem env004_isDrop_cons {k j : Nat} {p : N} {x : T} {l : XLbl N T} {s s' : XSt N T}
    (he : s.eq = (j, p, x) :: s'.eq) (hnd : (env004_tickets s).Nodup) :
    env004_isDrop k (s, l, s') = (!env004_isInject k l && j == k) := by
  have ht : env004_tickets s = j :: env004_tickets s' := by simp [env004_tickets, he]
  rw [ht] at hnd
  have hdef : env004_isDrop k (s, l, s') = (!env004_isInject k l &&
      (j :: env004_tickets s').contains k && !(env004_tickets s').contains k) := by
    simp only [env004_isDrop, ht]
  rw [hdef]
  by_cases hjk : j = k
  · subst hjk
    have h1 : (env004_tickets s').contains j = false := by
      simpa using (List.nodup_cons.mp hnd).1
    have h2 : (j :: env004_tickets s').contains j = true := by simp
    rw [h1, h2, beq_self_eq_true]
    cases env004_isInject j l <;> rfl
  · have h1 : (j :: env004_tickets s').contains k = (env004_tickets s').contains k := by
      rw [List.contains_cons, beq_false_of_ne (Ne.symm hjk), Bool.false_or]
    rw [h1, beq_false_of_ne hjk]
    cases env004_isInject k l <;> cases (env004_tickets s').contains k <;> rfl

omit [DecidableEq N] in
/-- A step that empties the queue drops `k` exactly when it is not the inject step of `k` and `k`
was queued. -/
theorem env004_isDrop_nil {k : Nat} {l : XLbl N T} {s s' : XSt N T} (he : s'.eq = []) :
    env004_isDrop k (s, l, s') = (!env004_isInject k l && (env004_tickets s).contains k) := by
  simp [env004_isDrop, env004_tickets, he]

omit [DecidableEq N] in
/-- A step of the shape whose label neither injects nor may drop keeps every queued ticket. -/
theorem env004_noDrop_of_shape {k : Nat} {l : XLbl N T} {s s' : XSt N T}
    (hs : env004_Shape l s s') (hl : env004_dropLabel l = false) (hi : ∀ j, l ≠ .inject j) :
    env004_isDrop k (s, l, s') = false := by
  rcases hs.2 with he | ⟨p, x, he, -⟩ | ⟨j, p, x, hj, -⟩ | ⟨-, -, -, hd⟩
  · simp [env004_isDrop, env004_tickets, he]
  · simp only [env004_isDrop, env004_tickets, he, List.map_append, Bool.and_eq_false_iff]
    by_cases hk : k ∈ s.eq.map Prod.fst
    · right; simp [hk]
    · left; right; simpa using hk
  · exact absurd hj (hi j)
  · rw [hl] at hd; cases hd

/-- On the reference from a state with distinct queued tickets, a step answers ticket `k` in the
sense of this block (an inject step of `k`, or a step that takes `k` off the queue) exactly when
it answers `k` by the label-based restatement `env004_labelAnswers` of ENV-006's line 4. So the
value lines of ENV-004 and the liveness line of ENV-006 describe one signal. -/
theorem env004_answers_label {P : XPol N T} {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    {k : Nat} (h : xstepW P C s l = some s') (hf : env004_Fresh s) :
    env004_answers k (s, l, s') = env004_labelAnswers k (s, l, s') := by
  have hs := env004_shape h
  cases l with
  | inject j =>
    obtain ⟨p, x, rest, he, -, -, -, rfl⟩ := injectStep_some h
    rw [env004_answers, env004_isDrop_cons he hf.1]
    simp only [env004_isInject, env004_labelAnswers]
    cases j == k <;> rfl
  | discard j =>
    obtain ⟨p, x, rest, he, -, -, -, rfl⟩ := discardStep_some h
    rw [env004_answers, env004_isDrop_cons he hf.1]
    simp only [env004_isInject, env004_labelAnswers]
    cases j == k <;> rfl
  | terminateNow =>
    obtain ⟨-, rfl⟩ := terminateStep_some h
    rw [env004_answers, env004_isDrop_nil rfl]
    simp [env004_isInject, env004_labelAnswers, env004_tickets]
  | finish c =>
    have he : s'.eq = [] := by
      cases c with
      | quiescent => obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h; rfl
      | closed => obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h; rfl
      | terminal => obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h; rfl
      | stopped => obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h; rfl
    rw [env004_answers, env004_isDrop_nil he]
    simp [env004_isInject, env004_labelAnswers, env004_tickets]
  | _ =>
    rw [env004_answers, env004_noDrop_of_shape hs rfl (by intro _ h; cases h)]
    rfl

/-- ✓ On every reference step from a state with distinct queued tickets below the supply, the
answering step of ENV-004 is the answering step of ENV-006 (`env004_answers_label` at
`refXPol`). -/
theorem ENV_004_answers_agree_reference {N T : Type} [DecidableEq N] {C : Cfg N T}
    {s s' : XSt N T} {l : XLbl N T} {k : Nat} (h : RefExec C s l s') (hf : env004_Fresh s) :
    env004_answers k (s, l, s') = env004_labelAnswers k (s, l, s') :=
  env004_answers_label (P := refXPol) h hf

end Reference

/-- ✓ The reference executor satisfies ENV-004 (`env004_xstepW` at `refXPol`). -/
@[evidence holds ENV_004]
theorem ENV_004_reference {N T : Type} [DecidableEq N] :
    ENV_004 (RefExec (N := N) (T := T)) :=
  env004_xstepW refXPol

/-! ### Decided runs of a step function -/

section Runs

variable {N T : Type}

/-- The trace of a label run of step function `g`, if every label is a step. -/
def env004_trace (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (env004_trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `env004_trace` builds is a run of the graph of `g`. -/
theorem env004_trace_run {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      env004_trace g C s ls = some tr → XRun (fun C s l s' => g C s l = some s') C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [env004_trace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : env004_trace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs, env004_trace_run ht⟩

/-- Read a decided check `p` off the trace of a label run: the run exists and `p` holds of it. -/
theorem env004_trace_of_check {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)}
    {C : Cfg N T} {s : XSt N T} {ls : List (XLbl N T)} {p : List (XStep N T) → Bool}
    (h : (env004_trace g C s ls).map p = some true) :
    ∃ tr, XRun (fun C s l s' => g C s l = some s') C s tr ∧ p tr = true := by
  cases ht : env004_trace g C s ls with
  | none => simp [ht] at h
  | some tr =>
    simp only [ht, Option.map_some, Option.some.injEq] at h
    exact ⟨tr, env004_trace_run ht, h⟩

/-- A run of the graph of `g` from a fresh state on which ticket `k` is answered twice refutes
ENV-004 (line 3) for that executor. -/
theorem env004_refuteTwice [DecidableEq N]
    {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} {s : XSt N T}
    {ls : List (XLbl N T)} {k : Nat} (hs : env004_Fresh s)
    (h : (env004_trace g C s ls).map
      (fun tr => !(afterNever (env004_answers k) (env004_answers k)).scan false tr) =
        some true) :
    ¬ ENV_004 (fun C s l s' => g C s l = some s') := by
  intro hR
  obtain ⟨tr, hr, hp⟩ := env004_trace_of_check h
  have : (afterNever (env004_answers k) (env004_answers k)).scan false tr = true :=
    ((hR C).1 k).2.2 s tr hs hr
  simp [this] at hp

end Runs

/-! ### Examples

No transition; place `0` is an environment place, place `1` an environment place that is also
terminal ([EXEC-042]). Every run starts from the empty marking. -/

/-- The configuration of the examples. -/
def env004_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1], transitions := [] }, timing := fun _ => .immediate,
           tol := 0 },
    prio := fun _ => 0, terminals := [1], envs := [0, 1], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- The initial state: nothing marked, nothing queued. -/
def env004_s0 : XSt Nat Nat := xinit (fun _ => []) 0

/-- The initial state is fresh: its queue is empty. -/
theorem env004_s0_fresh : env004_Fresh env004_s0 :=
  ⟨by simp [env004_tickets, env004_s0, xinit],
   fun n hn => by simp [env004_tickets, env004_s0, xinit] at hn⟩

/-- A request into `0` with token `5` is accepted as ticket `0`; the cycle reaches step 2. -/
def env004_toEvents : List (XLbl Nat Nat) :=
  [.request 0 5 .accepted, .endCompletions, .endPublications]

/-! ### Violation: true before the token is in the marking -/

/-- A step function whose `inject` step answers true and hands the event's token to the
publication queue instead of the marking, so that it lands in step 1b of the next cycle (the
acceptance of the event read as its admission, one step too early); otherwise the reference. -/
def env004_earlyTrueStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .inject k => (xstep C s (.inject k)).bind fun s₁ => s.eq.head?.map fun e =>
      { s₁ with M := s.M, pq := s₁.pq ++ [(k, [e.2])] }
  | l => xstep C s l

/-- ✗ An early true answer violates ENV-004 (line 1): the inject step of ticket `0` answers
while place `0` is still empty. -/
@[evidence forbids ENV_004]
theorem ENV_004_forbids_earlyTrue :
    ¬ ENV_004 (N := Nat) (T := Nat) (fun C s l s' => env004_earlyTrueStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env004_earlyTrueStep (C := env004_cfg)
    (o := xrun env004_cfg env004_s0 env004_toEvents) (l := .inject 0)
    (p := fun s s' => decide (s.eq = [(0, 0, 5)]) && s'.M 0 == s.M 0) (by decide)
  obtain ⟨p, x, hmem, hM⟩ := ((h env004_cfg).1 0).1 s s' hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  obtain ⟨he, h0⟩ := hp
  rw [he] at hmem
  simp only [List.mem_singleton, Prod.mk.injEq, true_and] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  have h1 := congrFun hM 0
  simp only [qAppendOne, if_true] at h1
  rw [h0] at h1
  simpa using congrArg List.length h1

/-! ### Violation: a false answer that deposits the token -/

/-- A step function whose `discard` step answers false and still appends the event's token at
the tail of its place (the caller is told the injection failed, and its token is in the net);
otherwise the reference. -/
def env004_discardDepositsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .discard k => (xstep C s (.discard k)).bind fun s₁ => s.eq.head?.map fun e =>
      { s₁ with M := qAppendOne s.M e.2.1 e.2.2 }
  | l => xstep C s l

/-- ✗ A depositing false answer violates ENV-004 (line 2, the marking half): after a close, the
discard of ticket `0` answers false and puts the token `5` into place `0`. -/
@[evidence forbids ENV_004]
theorem ENV_004_forbids_discardDeposits :
    ¬ ENV_004 (N := Nat) (T := Nat)
      (fun C s l s' => env004_discardDepositsStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env004_discardDepositsStep (C := env004_cfg)
    (o := xrun env004_cfg env004_s0
      [.request 0 5 .accepted, .close, .endCompletions, .endPublications])
    (l := .discard 0)
    (p := fun s s' => env004_isDrop 0 (s, .discard 0, s') && s'.M 0 != s.M 0) (by decide)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hp
  exact hp.2 (congrFun (((h env004_cfg).1 0).2.1 s _ s' hs hp.1).1 0)

/-! ### Violation: false while draining (the processing-time reading of AC2) -/

/-- A step function that discards a queued event while the executor is draining, as a closed
executor does (AC2 read when step 2 reaches the event, not when inject() was called); otherwise
the reference. -/
def env004_falseWhileDrainingStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .discard k =>
      if s.mode = .draining then
        (xstep C { s with mode := .closed } (.discard k)).map fun s₁ => { s₁ with mode := .draining }
      else xstep C s (.discard k)
  | l => xstep C s l

/-- ✗ A false answer while draining violates ENV-004 (line 2, the mode half): an event accepted
before the drain is discarded in step 2, and the run goes on with the executor draining. -/
@[evidence forbids ENV_004]
theorem ENV_004_forbids_falseWhileDraining :
    ¬ ENV_004 (N := Nat) (T := Nat)
      (fun C s l s' => env004_falseWhileDrainingStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env004_falseWhileDrainingStep (C := env004_cfg)
    (o := xrun env004_cfg env004_s0
      [.request 0 5 .accepted, .drain, .endCompletions, .endPublications])
    (l := .discard 0)
    (p := fun s s' => env004_isDrop 0 (s, .discard 0, s') && !s'.mode.closing &&
      isExecPhase s'.phase) (by decide)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨hd, hm⟩, hph⟩ := hp
  rcases (((h env004_cfg).1 0).2.1 s _ s' hs hd).2 with h1 | h1
  · rw [hm] at h1; exact Bool.false_ne_true h1
  · rw [hph] at h1; exact Bool.noConfusion h1

/-! ### Violation: true, then false -/

/-- A step function whose `inject` step deposits the token and answers true but leaves the event
queued (it reads the head of the queue without removing it); otherwise the reference. -/
def env004_trueThenDiscardStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .inject k => (xstep C s (.inject k)).map fun s₁ => { s₁ with eq := s.eq }
  | l => xstep C s l

/-- The run of the double answer: ticket `0` is injected, the executor closes, and the still
queued event is discarded. -/
def env004_twiceRun : List (XLbl Nat Nat) := env004_toEvents ++ [.inject 0, .close, .discard 0]

/-- ✗ Answering twice violates ENV-004 (line 3): ticket `0` is answered true by its inject step
and false by the discard after the close. -/
@[evidence forbids ENV_004]
theorem ENV_004_forbids_trueThenDiscard :
    ¬ ENV_004 (N := Nat) (T := Nat)
      (fun C s l s' => env004_trueThenDiscardStep C s l = some s') :=
  env004_refuteTwice (C := env004_cfg) (k := 0) env004_s0_fresh (ls := env004_twiceRun)
    (by decide)

/-- Line 3 is load-bearing: on the double-answer run every inject step of ticket `0` appends its
token (line 1's marking), and every drop of ticket `0` keeps the marking and comes after the
close (line 2), yet ticket `0` is answered twice. -/
theorem env004_trueThenDiscard_onlyLine3 :
    ∃ tr, XRun (fun C s l s' => env004_trueThenDiscardStep C s l = some s') env004_cfg
        env004_s0 tr ∧
      tr.all (fun st => !env004_isInject 0 st.2.1 || st.2.2.M 0 == st.1.M 0 ++ [5]) = true ∧
      tr.all (fun st => !env004_isDrop 0 st ||
        (st.2.2.M 0 == st.1.M 0 && st.2.2.mode.closing)) = true ∧
      (tr.filter (env004_answers 0)).length = 2 := by
  obtain ⟨tr, hr, hp⟩ := env004_trace_of_check (g := env004_trueThenDiscardStep)
    (C := env004_cfg) (s := env004_s0) (ls := env004_twiceRun)
    (p := fun tr =>
      tr.all (fun st => !env004_isInject 0 st.2.1 || st.2.2.M 0 == st.1.M 0 ++ [5]) &&
      tr.all (fun st => !env004_isDrop 0 st ||
        (st.2.2.M 0 == st.1.M 0 && st.2.2.mode.closing)) &&
      (tr.filter (env004_answers 0)).length == 2)
    (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨tr, hr, hp.1.1, hp.1.2, hp.2⟩

/-! ### Violation: an accepted request merged into a queued event -/

/-- A step function that keeps the pending injections per place instead of in a queue: an accepted
request into a place whose earlier event is still queued overwrites that event's token, keeps its
ticket and draws none from the supply (Java `pending.put(place, event)`, a TypeScript map keyed by
place name); otherwise the reference. -/
def env004_coalesceStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .request p x r =>
      if r = replyFor C s p ∧ r = .accepted ∧ s.eq.any (fun e => decide (e.2.1 = p)) = true then
        some { s with eq := s.eq.map (fun e => if e.2.1 = p then (e.1, p, x) else e),
                      parked := false }
      else xstep C s (.request p x r)
  | l => xstep C s l

/-- ✗ Merging an accepted request into a queued event violates ENV-004 (line 4): the second
request into place `0` is accepted, and the queue still holds only ticket `0`. -/
@[evidence forbids ENV_004]
theorem ENV_004_forbids_coalesce :
    ¬ ENV_004 (N := Nat) (T := Nat) (fun C s l s' => env004_coalesceStep C s l = some s') := by
  intro h
  obtain ⟨s, s', -, hs, hp⟩ := step_of_check env004_coalesceStep (C := env004_cfg)
    (o := xrun env004_cfg env004_s0 [.request 0 5 .accepted]) (l := .request 0 6 .accepted)
    (p := fun s s' => env004_tickets s == [0] && s.nextId == 1 && env004_tickets s' == [0])
    (by decide)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨h0, h1⟩, h2⟩ := hp
  have hf : env004_Fresh s :=
    ⟨by rw [h0]; simp, fun n hn => by rw [h0] at hn; simp at hn; omega⟩
  obtain ⟨j, hj, hj'⟩ := (h env004_cfg).2 s s' ⟨hf, 0, 6, hs⟩
  rw [h0] at hj
  rw [h2] at hj'
  exact hj hj'

section Coalesce

variable {N T : Type} [DecidableEq N]

/-- A step of the merging executor is a reference step, or an accepted request that keeps the
queued tickets and the supply. -/
theorem env004_coalesce_cases {C : Cfg N T} {s s' : XSt N T} {l : XLbl N T}
    (h : env004_coalesceStep C s l = some s') :
    xstep C s l = some s' ∨
      ((∃ p x r, l = .request p x r) ∧ env004_tickets s' = env004_tickets s ∧
        s'.nextId = s.nextId) := by
  cases l with
  | request p x r =>
    change (if _ then _ else _) = some s' at h
    split at h
    · right
      injection h with h
      subst h
      refine ⟨⟨p, x, r, rfl⟩, ?_, rfl⟩
      simp only [env004_tickets, List.map_map]
      apply List.map_congr_left
      intro e _
      by_cases hp : e.2.1 = p <;> simp [hp]
    · exact Or.inl h
  | _ => exact Or.inl h

/-- Line 3's scan over a run of the merging executor, as `env004_scan` for the reference. -/
theorem env004_coalesce_scan {C : Cfg N T} {k : Nat} :
    ∀ {s : XSt N T} {tr : List (XStep N T)} (b : Bool),
      XRun (fun C s l s' => env004_coalesceStep C s l = some s') C s tr → env004_Fresh s →
      (b = true → env004_Gone k s) →
      (afterNever (env004_answers k) (env004_answers k)).scan b tr = true
  | _, [], _, _, _, _ => rfl
  | s, (s₁, l, s') :: rest, b, ⟨h1, hstep, hrest⟩, hf, hb => by
    simp only at h1
    subst h1
    have key : env004_Fresh s' ∧ (env004_Gone k s₁ → env004_Gone k s') ∧
        (env004_answers k (s₁, l, s') = true → env004_Gone k s') ∧
        (env004_Gone k s₁ → env004_answers k (s₁, l, s') = false) := by
      rcases env004_coalesce_cases hstep with hx | ⟨⟨p, x, r, rfl⟩, ht, hn⟩
      · exact ⟨env004_fresh_shape (env004_shape hx) hf, env004_gone_shape (env004_shape hx),
          env004_gone_answer hx hf, env004_noAnswer_gone hx⟩
      · have hans : env004_answers k (s₁, .request p x r, s') = false := by
          simp [env004_answers, env004_isInject, env004_isDrop, ht]
        refine ⟨?_, ?_, fun ha => absurd ha (by rw [hans]; decide), fun _ => hans⟩
        · unfold env004_Fresh; rw [ht, hn]; exact hf
        · unfold env004_Gone; rw [ht, hn]; exact id
    obtain ⟨hf', hg, hga, hno⟩ := key
    have hok : (b && env004_answers k (s₁, l, s')) = false := by
      cases b with
      | false => rfl
      | true => rw [hno (hb rfl)]; rfl
    have hnext : (b || env004_answers k (s₁, l, s')) = true → env004_Gone k s' := by
      intro hn
      cases ha : env004_answers k (s₁, l, s') with
      | true => exact hga ha
      | false =>
        rw [ha, Bool.or_false] at hn
        exact hg (hb hn)
    show (!(b && env004_answers k (s₁, l, s')) &&
      (afterNever (env004_answers k) (env004_answers k)).scan
        (b || env004_answers k (s₁, l, s')) rest) = true
    rw [hok, env004_coalesce_scan _ hrest hf' hnext]
    rfl

/-- Line 4 is load-bearing: the merging executor keeps lines 1 to 3. A merging request is
neither an inject step nor a drop (its queue keeps every ticket), and it keeps the tickets and the
supply, so line 3's scan goes through. -/
theorem env004_coalesce_onlyLine4 (C : Cfg N T) :
    ∀ k,
      (on (fun s s' => env004_coalesceStep C s (.inject k) = some s'),
        shall (fun s s' => ∃ p x, (k, p, x) ∈ s.eq ∧ s'.M = qAppendOne s.M p x)) ∧
      (∀ s l s', env004_coalesceStep C s l = some s' → env004_isDrop k (s, l, s') = true →
        s'.M = s.M ∧ (s'.mode.closing = true ∨ isExecPhase s'.phase = false)) ∧
      (∀ s0 tr, env004_Fresh s0 →
        XRun (fun C s l s' => env004_coalesceStep C s l = some s') C s0 tr →
        (at-most-once (env004_answers k)) tr) := by
  intro k
  refine ⟨fun s s' h => ?_, fun s l s' h hd => ?_,
    fun s0 tr hf hr => env004_coalesce_scan false hr hf (fun h => absurd h Bool.false_ne_true)⟩
  · rcases env004_coalesce_cases h with hx | ⟨⟨p, x, r, hl⟩, -⟩
    · exact ((ENV_004_reference C).1 k).1 s s' hx
    · cases hl
  · rcases env004_coalesce_cases h with hx | ⟨-, ht, -⟩
    · exact ((ENV_004_reference C).1 k).2.1 s l s' hx hd
    · simp [env004_isDrop, ht] at hd
      exact absurd hd.1.2 hd.2

end Coalesce

/-! ### The premise of line 3 -/

/-- A state at step 2 whose queue holds ticket `0` twice (a supply that handed it out twice). -/
def env004_dupState : XSt Nat Nat :=
  { env004_s0 with eq := [(0, 0, 5), (0, 0, 6)], nextId := 1, phase := .events }

/-- The premise of line 3 is needed: from a state whose queue holds one ticket twice, the
reference itself injects both events and answers the ticket twice. -/
theorem env004_needs_fresh :
    ¬ env004_Fresh env004_dupState ∧
      ∃ tr, XRun RefExec env004_cfg env004_dupState tr ∧
        ¬ (at-most-once (env004_answers 0)) tr := by
  refine ⟨fun h => ?_, ?_⟩
  · have := h.1
    simp [env004_tickets, env004_dupState] at this
  · obtain ⟨tr, hr, hp⟩ := env004_trace_of_check (g := xstep) (C := env004_cfg)
      (s := env004_dupState) (ls := [.inject 0, .inject 0])
      (p := fun tr => !(afterNever (env004_answers 0) (env004_answers 0)).scan false tr)
      (by decide)
    refine ⟨tr, hr, fun h => ?_⟩
    have : (afterNever (env004_answers 0) (env004_answers 0)).scan false tr = true := h
    simp [this] at hp

/-! ### Nonvacuity -/

/-- The run of AC1 and the test derivation: the event is accepted and injected. -/
def env004_injectRun : List (XLbl Nat Nat) := env004_toEvents ++ [.inject 0]

/-- An event accepted before a drain is injected while the executor drains ([ENV-011]). -/
def env004_drainRun : List (XLbl Nat Nat) :=
  [.request 0 5 .accepted, .drain, .endCompletions, .endPublications, .inject 0]

/-- An event queued at a close is discarded, and the run finishes closed ([ENV-013]). -/
def env004_closeRun : List (XLbl Nat Nat) :=
  [.request 0 5 .accepted, .close, .endCompletions, .endPublications, .discard 0, .endEvents,
    .update, .deadline [], .finish .closed]

/-- The first event marks the terminal place `1`; the second, still queued, is cleared by the
finish of the run while the executor is open ([EXEC-042]). -/
def env004_terminalRun : List (XLbl Nat Nat) :=
  [.request 1 9 .accepted, .request 0 5 .accepted, .endCompletions, .endPublications, .inject 0,
    .finish .terminal]

/-- ENV-004 has teeth on the reference: (1) an accepted request queues the new ticket `0`, the
event is injected, its signal answered true, and the token `5` is then in place `0`; (2) an event accepted before a drain is answered
true while the executor drains; (3) an event queued at a close is answered false, its token never
lands, and the run finishes closed; (4) an event still queued when a terminal place stops the run
is answered false by the finish, with the executor open. Every run answers each ticket once. -/
@[evidence nonvacuous ENV_004]
theorem ENV_004_nonvacuous :
    (∃ tr, XRun RefExec env004_cfg env004_s0 tr ∧
      (tr.any (fun st => !(env004_tickets st.1).contains 0 && (env004_tickets st.2.2).contains 0) &&
        tr.any (fun st => env004_isInject 0 st.2.1) &&
        (XRun.last env004_s0 tr).M 0 == [5] &&
        (tr.filter (env004_answers 0)).length == 1) = true) ∧
    (∃ tr, XRun RefExec env004_cfg env004_s0 tr ∧
      (tr.any (fun st => env004_isInject 0 st.2.1 && st.1.mode == .draining) &&
        (XRun.last env004_s0 tr).M 0 == [5] &&
        (tr.filter (env004_answers 0)).length == 1) = true) ∧
    (∃ tr, XRun RefExec env004_cfg env004_s0 tr ∧
      (tr.any (env004_isDrop 0) && (XRun.last env004_s0 tr).M 0 == [] &&
        (XRun.last env004_s0 tr).phase == .done .closed &&
        (tr.filter (env004_answers 0)).length == 1) = true) ∧
    (∃ tr, XRun RefExec env004_cfg env004_s0 tr ∧
      (tr.any (fun st => env004_isDrop 1 st && st.2.2.mode == .open) &&
        (XRun.last env004_s0 tr).M 0 == [] &&
        (XRun.last env004_s0 tr).phase == .done .terminal &&
        (tr.filter (env004_answers 1)).length == 1) = true) :=
  ⟨env004_trace_of_check (g := xstep) (C := env004_cfg) (s := env004_s0) (ls := env004_injectRun)
      (by decide),
   env004_trace_of_check (g := xstep) (C := env004_cfg) (s := env004_s0) (ls := env004_drainRun)
      (by decide),
   env004_trace_of_check (g := xstep) (C := env004_cfg) (s := env004_s0) (ls := env004_closeRun)
      (by decide),
   env004_trace_of_check (g := xstep) (C := env004_cfg) (s := env004_s0)
      (ls := env004_terminalRun) (by decide)⟩

end Libpetri.Spec
