import Libpetri.Spec.Registry
import Libpetri.Spec.Ears
import Libpetri.Reference.Exec

set_option linter.missingDocs true

/-!
# CONC-003: Happens-before guarantee (`spec/05-concurrency.md`)

A requirement block over the executor model (`RefExec`, `Reference/Exec.lean`). The action of a
firing in flight hands its tokens to the orchestrator at two points: at its return, as the
emission an admitted completion deposits (`commit`), and at a flush, as a batch the executor
queues and deposits when it processes the publication (`publish`, [IO-015] mid-action
publication, ruling D17). The requirement says that what lands is exactly what the action wrote,
in write order: no token missing (a stale read), none added (a token written after the hand-off),
each batch deposited in flush order, and no queued batch withdrawn before it is deposited.

Lines 1 and 2 read runs, not the executor's internal buffers: what the action of firing `i`
wrote is read off the labels of the run (`conc003Log`, a scan of the outside steps `write`,
`flush`, `ret` and `expire` and of the steps that settle, publish or end the run), and each line
compares a deposit with that scan. Line 3 reads the publication queue of the glossary's executor
state (`XSt.pq`), as EXEC-021 does. The memory-visibility edge between threads is a quality of the
runtimes (Rust moves the outputs in the completion message, Java reads them on the orchestrator
after the future completes, TypeScript has one thread), not encoded.
-/

namespace Libpetri.Spec

open Libpetri Libpetri.Reference Libpetri.Novel.Seam

/-! ## What the action wrote, read off the labels of a run (block-local) -/

/-- What the action of one firing has handed over so far, read off the labels of a run
(no glossary entry; block-local). -/
structure Conc003Log (N T : Type) where
  /-- Written since the action's last flush (or its start), while it has not completed. -/
  pending  : List (N × T)
  /-- What was pending when the action returned normally: the tokens of its completion. -/
  returned : Option (List (N × T))
  /-- The action completed: it returned, normally or with an error, or its budget expired. -/
  done     : Bool
  /-- The batches it flushed that no publish step has deposited yet, in flush order. -/
  owed     : List (List (N × T))

/-- The scan before any label: nothing written. -/
def conc003Init {N T : Type} : Conc003Log N T := ⟨[], none, false, []⟩

/-- One label of the scan for firing `i`. Before the action completes, a write extends what is
pending and a flush of something pending closes a batch, which is then owed. A return completes
the action (a normal one freezes what is pending as its emission); so does the expiry of its
budget. A publish of `i` pays the oldest owed batch. A settle of `i` (`commit`, `fail`,
`tdeposit`) ends the firing; a terminal or stopped finish discards every owed batch. Every other
label, and every label of another firing, leaves the scan as it is. -/
def conc003See {N T : Type} (i : Nat) (w : Conc003Log N T) : XLbl N T → Conc003Log N T
  | .write j p x =>
      if j == i && !w.done then { w with pending := w.pending ++ [(p, x)] } else w
  | .flush j =>
      if j == i && !w.done && !w.pending.isEmpty then
        { w with pending := [], owed := w.owed ++ [w.pending] }
      else w
  | .ret j ok =>
      if j == i && !w.done then
        { w with done := true, returned := if ok then some w.pending else none }
      else w
  | .expire j _ => if j == i then { w with done := true } else w
  | .publish j => if j == i then { w with owed := w.owed.tail } else w
  | .commit j | .fail j | .tdeposit j =>
      if j == i then { w with pending := [], returned := none, done := false } else w
  | .finish .terminal | .finish .stopped => { w with owed := [] }
  | _ => w

/-- What the action of firing `i` wrote over the steps `pre` of a run, read off their labels. -/
def conc003Log {N T : Type} (i : Nat) (pre : List (XStep N T)) : Conc003Log N T :=
  pre.foldl (fun w st => conc003See i w st.2.1) conc003Init

/-- The batches of firing `i` in the publication queue of `s`, oldest first. -/
def conc003Q {N T : Type} (s : XSt N T) (i : Nat) : List (List (N × T)) :=
  (s.pq.filter (·.1 == i)).map (·.2)

/-- A step labelled `l` keeps the queued batches `q` of firing `i` as the head of the queue `q'`
after it: a publish of `i` may take the oldest one, a terminal or stopped finish may discard
them all, and no other step removes or reorders any. -/
def conc003Kept {N T : Type} (i : Nat) (q q' : List (List (N × T))) : XLbl N T → Prop
  | .publish j => (if j = i then q.tail else q) <+: q'
  | .finish .terminal | .finish .stopped => True
  | _ => q <+: q'

/-! ## CONC-003: Happens-Before Guarantee -/

requirement CONC_003
  id "CONC-003"
  title "Happens-Before Guarantee"
  kind B
  scope "all executors"
  source verbatim "spec/05-concurrency.md"
  quote "All writes performed by an action (output tokens, side effects) are visible to the orchestrator after the action's future/promise completes."
        "The completion mechanism provides a happens-before edge."
        "*When* the executor deposits the produced tokens of an admitted completion ([EXEC-020]), it *shall* deposit exactly the tokens the action wrote after its last publication, if any ([IO-015]), and before it returned, each at the tail of its place, in the order the action wrote them."
        "*When* the executor deposits a batch an action published before it completed ([IO-015]), it *shall* deposit the earliest publication of that action it has not yet deposited, as exactly the tokens the action wrote before that publication and after the one before it, each at the tail of its place, in the order the action wrote them."
        "The executor *shall* keep the batches an action published queued, in the order the action published them, until it deposits each one, unless a terminal place or an immediate termination stops the run ([EXEC-042], [ENV-015])."
  reading "For every executor R, every configuration C and every firing identity i, on every run of R that starts in a state in which no firing with identity i is in flight and no publication of i is queued:"
          "a commit step of i, taken after the steps pre of the run, happens only when the action of i returned normally in pre, and it appends to the marking, at the tails and in order, exactly the tokens the action wrote after its last flush in pre and before that return;"
          "a publish step of i, taken after the steps pre of the run, appends to the marking, at the tails and in order, exactly the oldest batch of i that pre still owes: a batch is the tokens the action wrote between two consecutive flushes (the first one counted from the action's start) before the action completed, and it is owed from its flush until a publish step of i pays it or a terminal or stopped finish discards it;"
          "and every step of R, from any state, keeps the batches of i in the publication queue, in order, at the head of the queue of i after it, except that a publish step of i may take the oldest one and a terminal or stopped finish may discard them."
  assumes "The model is an executor R : XRel N T (glossary GlossaryExec.lean): R C s l s' says that under configuration C the step labelled l leads from executor state s to s'. The outside steps write, flush, ret and expire are the action of a firing writing a token, publishing what it wrote ([IO-015] mid-action publication), returning, and its budget expiring. The publication queue is the glossary's XSt.pq (flushed batches with their firing's identity, in flush order); conc003Q s i lists the batches of i in it. The witness is the reference executor RefExec (Reference/Exec.lean)."
          "Naming: the markdown's 'visible to the orchestrator' is read as 'deposited by the orchestrator': the executor's only use of an action's output is to deposit it. 'Its last publication' is the action's last flush, 'returned' is a normal return (ret with ok), 'completed' is any return or the expiry of its budget, and an admitted completion whose produced tokens are deposited is a commit step (glossary: Admitted completion; a rejected one is a fail step and deposits nothing, EXEC-021). 'The tokens the action wrote' is read off the labels of the run by conc003Log: a write or a flush of i counts only until the action completes, so a token written or flushed after an error return or after the expiry is no part of any batch or emission. A flush with nothing written since the last one publishes nothing (the reference has no such step). Lines 1 and 2 judge the deposit against that scan, not against any buffer of the executor state."
          "Lines 1 and 2 read runs from a state in which firing i is not in flight and has no queued publication, so every write of i the run deposits is a label of the run. They do not require R to draw fresh identities or to refuse a write of an identity not in flight; the reference does both (one supply, XSt.nextId; writeStep needs firing i in flight with no outcome). The scan counts the writes of i until the action completes and again after a settle of i, so an executor that reuses i is judged as one action per settle: its commit deposits what was written since that settle, and its publications are still deposited in flush order and each once (line 2), so a batch of an earlier firing with identity i can be deposited only as the oldest one still owed, never in place of a later one."
          "Line 1 is the third quoted sentence. It excludes a stale read: an executor that reads the output when the action hands back its handle, before an asynchronous action has written anything, deposits nothing (CONC_003_forbids_startSnapshot); one that deposits a token the action wrote after it returned (CONC_003_forbids_lateWrite); one that deposits the tokens of one place in another order than written (CONC_003_forbids_reversed); one that also deposits at the completion what the action already published (CONC_003_forbids_flushKeeps, the reading 'all writes are visible at completion'); and one that commits, with what its action wrote, a firing whose action returned with an error (CONC_003_forbids_commitAfterError). That a commit needs a normal return is part of line 1 because the emission is what was written before the return; the order of the steps in general is CONC-001's."
          "Each tail placement restates EXEC-020's, which the third and fourth quoted sentences name: the deposit is compared as the whole marking, s'.M = qAppend s.M e, so the step adds exactly these tokens at the tails and changes nothing else in the marking. Under ruling D48 (a), MOD-021 AC9 cites CONC-003 with EXEC-020 for the FIFO of the tokens of merged firings, which this placement supplies."
          "Line 2 is the fourth quoted sentence: a publication deposits exactly the oldest batch still owed. An executor that reads the action's live output when it processes a publication, and so deposits tokens written after the flush, breaks it (CONC_003_forbids_liveRead); so does one that deposits a batch out of write order (CONC_003_forbids_reversedBatch), one that deposits the oldest batch but dequeues the newest, so that its second publication deposits the first batch again and the second batch is lost (CONC_003_forbids_dupBatch; its first publication also breaks line 3), and one that publishes what an action flushed after it returned with an error (CONC_003_forbids_flushAfterError). A batch the join-relay check of NU-054 rejects is dropped at its flush, with every later batch of the firing (EXEC-021, NU-054): the scan still owes it, and no publication of i follows it, which line 2 allows. The scan forgets the owed batches at a terminal or stopped finish: EXEC-020's 'A publication still queued when a terminal place stops the run ([EXEC-042]) is discarded.', and an immediate termination abandons its queue the same way (ENV-015)."
          "Line 3 is the fifth quoted sentence. A queued batch leaves the queue only by a publish step of its firing, which by line 2 deposits it, oldest first, whatever happens to the completion (ruling D17), or by a terminal or stopped finish. An executor whose commit also withdraws the firing's queued publications breaks it (CONC_003_forbids_dropAtCommit); EXEC-021's second line keeps the queue on a fail step only. That the loop processes the queue in every cycle (step 1b) and does not finish quiescent with a publication queued is EXEC-001's and EXEC-040's. That a flush queues its batch unless the join-relay check rejects it is the flush step of the model ([IO-015] mid-action publication, NU-054): the lines catch a batch dropped at its flush once a later batch of the same action is deposited (line 2's order), not a dropped last batch."
          "The first quoted sentence is lines 1 to 3: the tokens of a normal return reach the marking at the commit, every batch flushed before the action completed stays queued until its publish step deposits it, and each hand-off carries exactly what was written before it. A completion that fails or is not admitted deposits none of its own tokens (EXEC-020, EXEC-021, EXEC-030); its published batches still land. 'Side effects' other than output tokens have no reader in the executor and are not encoded. The second quoted sentence, the happens-before edge, is memory visibility across threads (Q): Rust moves the outputs in the completion message, Java reads the output context on the orchestrator after the future completes, TypeScript runs on one thread. The model has one state, so its runs have no stale memory; the lines fix what is read, at which hand-off."
          "Ruling D48 (a): the order in which the executor admits queued completions is not fixed, so the lines say nothing about the order of the commits of distinct firings, nor about how the publications of distinct firings interleave. That validation precedes the deposit is EXEC-021's."
          "The timeout outcome is not what the action wrote: a firing that ends with it is settled by tdeposit or fail (EXEC-022, IO-013), which line 1 does not read. The expiry completes the action for the scan, so what it wrote after its last flush is neither a batch nor an emission; that it is discarded, not merged with the timeout branch, is EXEC-022 AC4 and IO-013 AC5."
          "AC1 (the action writes to the output, the orchestrator reads it after completion, the values are visible) is line 1: the deposit holds every written token with its value. CONC_003_nonvacuous deposits the values 20 and 30 written after a flush at the commit, keeps the flushed 10 queued through that commit, and deposits it at its publication."
          "AC2 (no stale reads) is line 1's 'exactly' (CONC_003_forbids_startSnapshot) for what is read, and Q for memory."
          "The test derivation (a complex object stored in the output, the orchestrator sees the complete object) is line 1 over token values: tokens are of an arbitrary type T and are compared whole."
  signoff "pending"
  statement : ∀ {N T : Type} [DecidableEq N], XRel N T → Prop :=
    fun R => ∀ C i,
      (∀ (s0 : XSt _ _), (∀ f ∈ s0.fl, f.id ≠ i) → (∀ b, (i, b) ∉ s0.pq) →
        ∀ tr, XRun R C s0 tr →
          (∀ pre s s' post, tr = pre ++ (s, .commit i, s') :: post →
            ∃ e, (conc003Log i pre).returned = some e ∧ s'.M = qAppend s.M e) ∧
          (∀ pre s s' post, tr = pre ++ (s, .publish i, s') :: post →
            ∃ b, (conc003Log i pre).owed.head? = some b ∧ s'.M = qAppend s.M b)) ∧
      (∀ s l s', R C s l s' → conc003Kept i (conc003Q s i) (conc003Q s' i) l)

/- The pinned readable form of CONC-003: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.CONC_003 : {N T : Type} → [DecidableEq N] → XRel N T → Prop :=
fun {N T} [DecidableEq N] R =>
  ∀ (C : Cfg N T) (i : ℕ),
    (∀ (s0 : XSt N T),
        (∀ f ∈ s0.fl, f.id ≠ i) →
          (∀ (b : List (N × T)), (i, b) ∉ s0.pq) →
            ∀ (tr : List (XStep N T)),
              XRun R C s0 tr →
                (∀ (pre : List (XStep N T)) (s s' : XSt N T) (post : List (XSt N T × XLbl N T × XSt N T)),
                    tr = pre ++ (s, XLbl.commit i, s') :: post →
                      ∃ e, (conc003Log i pre).returned = some e ∧ s'.M = qAppend s.M e) ∧
                  ∀ (pre : List (XStep N T)) (s s' : XSt N T) (post : List (XSt N T × XLbl N T × XSt N T)),
                    tr = pre ++ (s, XLbl.publish i, s') :: post →
                      ∃ b, (conc003Log i pre).owed.head? = some b ∧ s'.M = qAppend s.M b) ∧
      ∀ (s : XSt N T) (l : XLbl N T) (s' : XSt N T), R C s l s' → conc003Kept i (conc003Q s i) (conc003Q s' i) l
-/
#guard_msgs in #print CONC_003

/-! ### The reference -/

section Reference

variable {N T : Type} [DecidableEq N]

/-- Firing `i`'s record, if it is in flight. -/
def conc003View (s : XSt N T) (i : Nat) : Option (Firing N T) :=
  s.fl.find? (·.id == i)

/-- The scan agrees with the record of firing `i`: no firing, nothing pending and not completed;
an open firing, its buffer pending; a normal return, its emission frozen; any other outcome,
completed. -/
def conc003Agree (w : Conc003Log N T) : Option (Firing N T) → Prop
  | none => w.pending = [] ∧ w.returned = none ∧ w.done = false
  | some f =>
    match f.out with
    | none => w.pending = f.buf ∧ w.returned = none ∧ w.done = false
    | some (.ok e) => w.returned = some e ∧ w.done = true
    | some _ => w.done = true

/-- The invariant of the reference: the scan agrees with firing `i`'s record; the queued batches
of `i` are the oldest owed ones, all of them while the firing is in flight and no batch of it
was dropped by the relay check (or before it starts); and a firing in flight has an identity
drawn from the supply. -/
def Conc003Inv (i : Nat) (s : XSt N T) (w : Conc003Log N T) : Prop :=
  conc003Agree w (conc003View s i) ∧ conc003Q s i <+: w.owed ∧
    (((∃ f, conc003View s i = some f ∧ f.relayBad = false) ∨ s.nextId ≤ i) →
      conc003Q s i = w.owed) ∧
    (conc003View s i ≠ none → i < s.nextId)

omit [DecidableEq N] in
/-- Updating firing `i` with an identity-preserving `h` updates the record `find?` returns. -/
theorem conc003_find_upd_same {h : Firing N T → Firing N T} (hh : ∀ g, (h g).id = g.id)
    (i : Nat) : ∀ l : List (Firing N T),
      (l.map fun g => if g.id == i then h g else g).find? (·.id == i) =
        (l.find? (·.id == i)).map h
  | [] => rfl
  | g :: l => by
    have ih := conc003_find_upd_same hh i l
    by_cases hg : g.id = i
    · have h1 : ((h g).id == i) = true := by simp [hh, hg]
      have h2 : (g.id == i) = true := by simp [hg]
      simp only [List.map_cons, List.find?_cons, h2, if_true, h1, Option.map_some]
    · have h2 : (g.id == i) = false := by simp [hg]
      simp only [List.map_cons, List.find?_cons, h2, Bool.false_eq_true, if_false, ih]

omit [DecidableEq N] in
/-- Updating another firing `j` with an identity-preserving `h` leaves firing `i`'s record. -/
theorem conc003_find_upd_ne {h : Firing N T → Firing N T} (hh : ∀ g, (h g).id = g.id)
    {i j : Nat} (hj : j ≠ i) : ∀ l : List (Firing N T),
      (l.map fun g => if g.id == j then h g else g).find? (·.id == i) = l.find? (·.id == i)
  | [] => rfl
  | g :: l => by
    have ih := conc003_find_upd_ne hh hj l
    by_cases hg : g.id = j
    · have h1 : ((h g).id == i) = false := by simp [hh, hg, hj]
      have h2 : (g.id == i) = false := by simp [hg, hj]
      have h3 : (g.id == j) = true := by simp [hg]
      simp only [List.map_cons, List.find?_cons, h3, if_true, h1, h2, ih]
    · have h3 : (g.id == j) = false := by simp [hg]
      simp only [List.map_cons, List.find?_cons, h3, Bool.false_eq_true, if_false, ih]

omit [DecidableEq N] in
/-- Removing the firings `j` from the list: none left for `j`, the others' records kept. -/
theorem conc003_find_filter (i j : Nat) : ∀ l : List (Firing N T),
    (l.filter (·.id != j)).find? (·.id == i) = if j = i then none else l.find? (·.id == i)
  | [] => by simp
  | g :: l => by
    have ih := conc003_find_filter i j l
    by_cases hg : g.id = j
    · have h3 : (g.id != j) = false := by simp [hg]
      simp only [List.filter_cons, h3, Bool.false_eq_true, if_false, ih]
      by_cases hji : j = i
      · simp [hji]
      · have h2 : (g.id == i) = false := by simp [hg, hji]
        simp [hji, h2]
    · have h3 : (g.id != j) = true := by simp [hg]
      rw [List.filter_cons, h3, if_pos rfl, List.find?_cons, ih]
      by_cases hji : j = i
      · have h2 : (g.id == i) = false := by simp [← hji, hg]
        simp [hji, h2]
      · simp only [hji, if_false, List.find?_cons]

omit [DecidableEq N] in
/-- The record of firing `i` after updating firing `j` with an identity-preserving `h`. -/
theorem conc003_view_upd {s s' : XSt N T} {h : Firing N T → Firing N T}
    (hh : ∀ g, (h g).id = g.id) (i j : Nat) (hfl : s'.fl = updFiring s j h) :
    conc003View s' i = if j = i then (conc003View s i).map h else conc003View s i := by
  unfold conc003View
  rw [hfl]
  unfold updFiring
  split
  · rename_i hji; subst hji; rw [conc003_find_upd_same hh]
  · rename_i hji; rw [conc003_find_upd_ne hh hji]

omit [DecidableEq N] in
/-- The record of firing `i` after settling firing `j`. -/
theorem conc003_view_settle (s : XSt N T) (i j : Nat) :
    conc003View (settle s j) i = if j = i then none else conc003View s i := by
  unfold conc003View settle
  simp only [conc003_find_filter]

omit [DecidableEq N] in
/-- A step that keeps firing `i`'s record and its queued batches, and draws no identity back,
keeps the invariant. -/
theorem conc003Inv_keep {i : Nat} {s s' : XSt N T} {w : Conc003Log N T}
    (hv : conc003View s' i = conc003View s i) (hq : conc003Q s' i = conc003Q s i)
    (hn : s.nextId ≤ s'.nextId) (h : Conc003Inv i s w) : Conc003Inv i s' w := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [hv]; exact h1, by rw [hq]; exact h2, fun hc => ?_, fun hc => ?_⟩
  · rw [hq]
    apply h3
    rcases hc with ⟨f, hf, hb⟩ | hc
    · exact Or.inl ⟨f, by rw [← hv]; exact hf, hb⟩
    · exact Or.inr (Nat.le_trans hn hc)
  · exact Nat.lt_of_lt_of_le (h4 (by rw [← hv]; exact hc)) hn

omit [DecidableEq N] in
/-- A step that keeps the firings, the publication queue and the identity supply keeps the
invariant. -/
theorem conc003Inv_frame {i : Nat} {s s' : XSt N T} {w : Conc003Log N T}
    (hfl : s'.fl = s.fl) (hq : s'.pq = s.pq) (hn : s'.nextId = s.nextId)
    (h : Conc003Inv i s w) : Conc003Inv i s' w :=
  conc003Inv_keep (by unfold conc003View; rw [hfl]) (by unfold conc003Q; rw [hq])
    (Nat.le_of_eq hn.symm) h

omit [DecidableEq N] in
/-- A step that updates the record of firing `i` in flight, keeping its relay flag, its queued
batches, the identity supply and the scan's owed batches, keeps the invariant once the scan
agrees with the new record. -/
theorem conc003Inv_upd {i : Nat} {s s' : XSt N T} {w w' : Conc003Log N T} {f g : Firing N T}
    (hf : conc003View s i = some f) (hv : conc003View s' i = some g)
    (hr : g.relayBad = f.relayBad) (hq : conc003Q s' i = conc003Q s i)
    (hn : s'.nextId = s.nextId) (how : w'.owed = w.owed) (ha : conc003Agree w' (some g))
    (hi : Conc003Inv i s w) : Conc003Inv i s' w' := by
  obtain ⟨-, h2, h3, h4⟩ := hi
  have hlt : i < s.nextId := h4 (by rw [hf]; exact Option.some_ne_none _)
  refine ⟨by rw [hv]; exact ha, by rw [hq, how]; exact h2, fun hc => ?_,
    fun _ => by rw [hn]; exact hlt⟩
  rw [hq, how]
  apply h3
  rcases hc with ⟨g', hg', hb⟩ | hc
  · rw [hv] at hg'
    obtain rfl := Option.some.inj hg'
    exact Or.inl ⟨f, hf, by rw [← hr]; exact hb⟩
  · exact absurd (hn ▸ hc) (Nat.not_le.mpr hlt)

omit [DecidableEq N] in
/-- A settle of firing `j` (removing it) keeps the invariant against the scan of its label. -/
theorem conc003Inv_settle {i j : Nat} {s s' : XSt N T} {w w' : Conc003Log N T}
    (hfl : s'.fl = (settle s j).fl) (hq : s'.pq = s.pq) (hn : s'.nextId = s.nextId)
    (hw : w' = if j == i then { w with pending := [], returned := none, done := false } else w)
    (h : Conc003Inv i s w) : Conc003Inv i s' w' := by
  have hv : conc003View s' i = conc003View (settle s j) i := by
    unfold conc003View; rw [hfl]
  have hQ : conc003Q s' i = conc003Q s i := by unfold conc003Q; rw [hq]
  rw [conc003_view_settle] at hv
  by_cases hji : j = i
  · subst hji
    simp only [beq_self_eq_true, if_true] at hw hv
    subst hw
    obtain ⟨-, h2, h3, -⟩ := h
    refine ⟨by rw [hv]; exact ⟨rfl, rfl, rfl⟩, by rw [hQ]; exact h2, fun hc => ?_,
      fun hc => absurd hv hc⟩
    rw [hQ]
    apply h3
    rcases hc with ⟨f, hf, -⟩ | hc
    · rw [hv] at hf; cases hf
    · exact Or.inr (hn ▸ hc)
  · have : (j == i) = false := by simpa using hji
    simp only [this, hji, if_false, Bool.false_eq_true] at hw hv
    subst hw
    exact conc003Inv_keep hv hQ (Nat.le_of_eq hn.symm) h

omit [DecidableEq N] in
/-- The scan of a label of another firing `j` is unchanged. -/
theorem conc003See_ne {i j : Nat} (hji : j ≠ i) (w : Conc003Log N T) :
    (∀ p x, conc003See i w (.write j p x) = w) ∧ conc003See i w (.flush j) = w ∧
      (∀ ok, conc003See i w (.ret j ok) = w) ∧ (∀ e, conc003See i w (.expire j e) = w) ∧
      conc003See i w (.publish j) = w := by
  have : (j == i) = false := by simpa using hji
  simp [conc003See, this]

/-- Every step of the reference executor keeps the invariant, against the scan of its label. -/
theorem conc003Inv_step {C : Cfg N T} {i : Nat} {s s' : XSt N T} {l : XLbl N T}
    {w : Conc003Log N T} (h : RefExec C s l s') (hi : Conc003Inv i s w) :
    Conc003Inv i s' (conc003See i w l) := by
  have open_ : ∀ {f : Firing N T}, conc003View s i = some f → f.out = none →
      w.pending = f.buf ∧ w.returned = none ∧ w.done = false := by
    intro f hf ho
    have := hi.1
    rw [hf] at this
    simp only [conc003Agree, ho] at this
    exact this
  cases l with
  | delay δ => cases xstepW_delay h; exact hi
  | write j p x =>
    obtain ⟨f, hf, ho, hs'⟩ := writeStep_some h
    have hf' : conc003View s j = some f := hf
    have hq : conc003Q s' i = conc003Q s i := by rw [hs']; rfl
    have hn : s'.nextId = s.nextId := by rw [hs']
    have hv := conc003_view_upd (s' := s') (h := fun g => { g with buf := g.buf ++ [(p, x)] })
      (fun _ => rfl) i j (by rw [hs'])
    by_cases hji : j = i
    · subst hji
      obtain ⟨hp, hr, hd⟩ := open_ hf' ho
      simp only [hf', Option.map_some, if_true] at hv
      have hw : conc003See j w (.write j p x) = { w with pending := w.pending ++ [(p, x)] } := by
        simp [conc003See, hd]
      rw [hw]
      exact conc003Inv_upd (w := w) hf' hv rfl hq hn rfl (by simp [conc003Agree, ho, hp, hr, hd]) hi
    · simp only [hji, if_false] at hv
      rw [(conc003See_ne hji w).1]
      exact conc003Inv_keep hv hq (Nat.le_of_eq hn.symm) hi
  | flush j =>
    obtain ⟨f, hf, ho, -, hne, ⟨hrb, -, hs'⟩ | ⟨-, hs'⟩⟩ := flushStep_some h
    · have hf' : conc003View s j = some f := hf
      have hn : s'.nextId = s.nextId := by rw [hs']
      have hv := conc003_view_upd (s' := s')
        (h := fun g => { g with buf := [], pub := g.pub ++ g.buf.map Prod.fst })
        (fun _ => rfl) i j (by rw [hs'])
      by_cases hji : j = i
      · subst hji
        obtain ⟨hp, hr, hd⟩ := open_ hf' ho
        simp only [hf', Option.map_some, if_true] at hv
        have hE : w.pending.isEmpty = false := by
          rw [hp]; cases hb : f.buf with
          | nil => exact absurd hb hne
          | cons _ _ => rfl
        have hw : conc003See j w (.flush j) =
            { w with pending := [], owed := w.owed ++ [w.pending] } := by
          simp [conc003See, hd, hE]
        rw [hw]
        obtain ⟨-, -, h3, h4⟩ := hi
        have hQ : conc003Q s j = w.owed := h3 (Or.inl ⟨f, hf', hrb⟩)
        have hq' : conc003Q s' j = w.owed ++ [w.pending] := by
          rw [hs', ← hQ, hp]; simp [conc003Q, List.filter_append]
        refine ⟨?_, by rw [hq'], fun _ => hq', fun _ => ?_⟩
        · rw [hv]; simp [conc003Agree, ho, hr, hd]
        · rw [hn]; exact h4 (by rw [hf']; exact Option.some_ne_none _)
      · simp only [hji, if_false] at hv
        rw [(conc003See_ne hji w).2.1]
        have hji' : (j == i) = false := by simpa using hji
        exact conc003Inv_keep hv (by rw [hs']; simp [conc003Q, List.filter_append, hji'])
          (Nat.le_of_eq hn.symm) hi
    · have hf' : conc003View s j = some f := hf
      have hq : conc003Q s' i = conc003Q s i := by rw [hs']; rfl
      have hn : s'.nextId = s.nextId := by rw [hs']
      have hv := conc003_view_upd (s' := s') (h := fun g => { g with buf := [], relayBad := true })
        (fun _ => rfl) i j (by rw [hs'])
      by_cases hji : j = i
      · subst hji
        obtain ⟨hp, hr, hd⟩ := open_ hf' ho
        simp only [hf', Option.map_some, if_true] at hv
        have hE : w.pending.isEmpty = false := by
          rw [hp]; cases hb : f.buf with
          | nil => exact absurd hb hne
          | cons _ _ => rfl
        have hw : conc003See j w (.flush j) =
            { w with pending := [], owed := w.owed ++ [w.pending] } := by
          simp [conc003See, hd, hE]
        rw [hw]
        obtain ⟨-, h2, -, h4⟩ := hi
        have hlt : j < s.nextId := h4 (by rw [hf']; exact Option.some_ne_none _)
        refine ⟨?_, by rw [hq]; exact h2.trans (List.prefix_append _ _), fun hc => ?_,
          fun _ => by rw [hn]; exact hlt⟩
        · rw [hv]; simp [conc003Agree, ho, hr, hd]
        · exfalso
          rcases hc with ⟨g, hg, hb⟩ | hc
          · rw [hv] at hg; cases hg; simp at hb
          · rw [hn] at hc; exact Nat.not_le.mpr hlt hc
      · simp only [hji, if_false] at hv
        rw [(conc003See_ne hji w).2.1]
        exact conc003Inv_keep hv hq (Nat.le_of_eq hn.symm) hi
  | ret j ok =>
    obtain ⟨f, hf, ho, hs'⟩ := retStep_some h
    have hf' : conc003View s j = some f := hf
    have hq : conc003Q s' i = conc003Q s i := by rw [hs']; rfl
    have hn : s'.nextId = s.nextId := by rw [hs']
    have hv := conc003_view_upd (s' := s')
      (h := fun g => { g with out := some (if ok && !g.relayBad then .ok g.buf else .err) })
      (fun _ => rfl) i j (by rw [hs'])
    by_cases hji : j = i
    · subst hji
      obtain ⟨hp, hr, hd⟩ := open_ hf' ho
      simp only [hf', Option.map_some, if_true] at hv
      have hw : conc003See j w (.ret j ok) =
          { w with done := true, returned := if ok then some w.pending else none } := by
        simp [conc003See, hd]
      rw [hw]
      refine conc003Inv_upd (w := w) hf' hv rfl hq hn rfl ?_ hi
      cases ok <;> cases hb : f.relayBad <;> simp [conc003Agree, hp]
    · simp only [hji, if_false] at hv
      rw [(conc003See_ne hji w).2.2.1]
      exact conc003Inv_keep hv hq (Nat.le_of_eq hn.symm) hi
  | expire j e =>
    obtain ⟨f, hf, -, -, -, -, hs'⟩ := expireStep_some h
    have hf' : conc003View s j = some f := hf
    have hq : conc003Q s' i = conc003Q s i := by rw [hs']; rfl
    have hn : s'.nextId = s.nextId := by rw [hs']
    have hv := conc003_view_upd (s' := s')
      (h := fun g => { g with out := some (if g.relayBad then .err else .timedOut e) })
      (fun _ => rfl) i j (by rw [hs'])
    by_cases hji : j = i
    · subst hji
      simp only [hf', Option.map_some, if_true] at hv
      have hw : conc003See j w (.expire j e) = { w with done := true } := by simp [conc003See]
      rw [hw]
      refine conc003Inv_upd (w := w) hf' hv rfl hq hn rfl ?_ hi
      cases hb : f.relayBad <;> simp [conc003Agree]
    · simp only [hji, if_false] at hv
      rw [(conc003See_ne hji w).2.2.2.1]
      exact conc003Inv_keep hv hq (Nat.le_of_eq hn.symm) hi
  | commit j =>
    obtain ⟨f, e, -, -, -, -, -, hs'⟩ := commitStep_some h
    exact conc003Inv_settle (by rw [hs']; rfl) (by rw [hs']; rfl) (by rw [hs']; rfl) rfl hi
  | fail j =>
    obtain ⟨f, -, -, -, hs'⟩ := failStep_some h
    exact conc003Inv_settle (by rw [hs']) (by rw [hs']; rfl) (by rw [hs']; rfl) rfl hi
  | tdeposit j =>
    obtain ⟨f, e, -, -, -, -, hs'⟩ := tdepositStep_some h
    exact conc003Inv_settle (by rw [hs']; rfl) (by rw [hs']; rfl) (by rw [hs']; rfl) rfl hi
  | endCompletions =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endCompletions h
    exact conc003Inv_frame rfl rfl rfl hi
  | publish j =>
    obtain ⟨b, rest, hpq, -, -, hs'⟩ := publishStep_some h
    have hv : conc003View s' i = conc003View s i := by unfold conc003View; rw [hs']
    have hn : s'.nextId = s.nextId := by rw [hs']
    by_cases hji : j = i
    · subst hji
      have hqs : conc003Q s j = b :: conc003Q s' j := by
        rw [hs']; unfold conc003Q; rw [hpq]; simp
      have hw : conc003See j w (.publish j) = { w with owed := w.owed.tail } := by
        simp [conc003See]
      rw [hw]
      obtain ⟨h1, h2, h3, h4⟩ := hi
      refine ⟨by rw [hv]; exact h1, ?_, fun hc => ?_,
        fun hc => by rw [hn]; exact h4 (by rw [← hv]; exact hc)⟩
      · obtain ⟨t, ht⟩ := h2
        rw [hqs] at ht
        exact ⟨t, by rw [← ht]; rfl⟩
      · have hQ := h3 (by
          rcases hc with ⟨g, hg, hb⟩ | hc
          · exact Or.inl ⟨g, by rw [← hv]; exact hg, hb⟩
          · exact Or.inr (by rw [← hn]; exact hc))
        show conc003Q s' j = w.owed.tail
        rw [← hQ, hqs]; rfl
    · have hji' : (j == i) = false := by simpa using hji
      have hq : conc003Q s' i = conc003Q s i := by
        rw [hs']; unfold conc003Q; rw [hpq]; simp [hji']
      rw [(conc003See_ne hji w).2.2.2.2]
      exact conc003Inv_keep hv hq (Nat.le_of_eq hn.symm) hi
  | endPublications =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endPublications h
    exact conc003Inv_frame rfl rfl rfl hi
  | inject k =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := injectStep_some h
    exact conc003Inv_frame rfl rfl rfl hi
  | discard k =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := discardStep_some h
    exact conc003Inv_frame rfl rfl rfl hi
  | snapshot a =>
    obtain ⟨-, -, -, rfl⟩ := snapshotStep_some h
    exact hi
  | endEvents =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_endEvents h
    exact conc003Inv_frame rfl rfl rfl hi
  | update =>
    obtain ⟨-, -, rfl⟩ := xstepW_update h
    exact conc003Inv_frame rfl rfl rfl hi
  | deadline ns =>
    obtain ⟨-, -, -, rfl⟩ := xstepW_deadline h
    exact conc003Inv_frame rfl rfl rfl hi
  | finish c =>
    cases c with
    | quiescent =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishQuiescent h
      exact conc003Inv_frame rfl rfl rfl hi
    | closed =>
      obtain ⟨-, -, -, -, rfl⟩ := xstepW_finishClosed h
      exact conc003Inv_frame rfl rfl rfl hi
    | terminal =>
      obtain ⟨-, -, rfl⟩ := xstepW_finishTerminal h
      obtain ⟨h1, -, -, h4⟩ := hi
      exact ⟨h1, List.prefix_refl _, fun _ => rfl, h4⟩
    | stopped =>
      obtain ⟨-, -, -, rfl⟩ := xstepW_finishStopped h
      obtain ⟨h1, -, -, h4⟩ := hi
      exact ⟨h1, List.prefix_refl _, fun _ => rfl, h4⟩
  | begin =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_begin h
    exact conc003Inv_frame rfl rfl rfl hi
  | start n sy =>
    obtain ⟨t, rest, -, -, -, -, -, -, -, hs'⟩ := startStep_some h
    have hfl : s'.fl = s.fl ++ [⟨s.nextId, t, qDelivered (vis s) t, s.now, sy, [], [], false,
        none⟩] := by rw [hs']
    have hq : conc003Q s' i = conc003Q s i := by rw [hs']; rfl
    have hn : s'.nextId = s.nextId + 1 := by rw [hs']
    show Conc003Inv i s' w
    obtain ⟨h1, h2, h3, h4⟩ := hi
    cases hg : conc003View s i with
    | some g =>
      have hv : conc003View s' i = conc003View s i := by
        unfold conc003View at hg ⊢; rw [hfl, List.find?_append, hg]; rfl
      exact conc003Inv_keep hv hq (by rw [hn]; exact Nat.le_succ _) ⟨h1, h2, h3, h4⟩
    | none =>
      by_cases hni : s.nextId = i
      · have hv : conc003View s' i =
            some ⟨s.nextId, t, qDelivered (vis s) t, s.now, sy, [], [], false, none⟩ := by
          unfold conc003View at hg ⊢; rw [hfl, List.find?_append, hg]; simp [hni]
        have hQ : conc003Q s i = w.owed := h3 (Or.inr (Nat.le_of_eq hni))
        rw [hg] at h1
        refine ⟨by rw [hv]; simpa [conc003Agree] using h1, by rw [hq, hQ],
          fun _ => by rw [hq, hQ], fun _ => by rw [hn]; omega⟩
      · have hv : conc003View s' i = conc003View s i := by
          unfold conc003View at hg ⊢; rw [hfl, List.find?_append, hg]; simp [hni]
        exact conc003Inv_keep hv hq (by rw [hn]; exact Nat.le_succ _) ⟨h1, h2, h3, h4⟩
  | lose n =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := loseStep_some h
    exact conc003Inv_frame rfl rfl rfl hi
  | endPass =>
    obtain ⟨-, -, -, -, rfl⟩ := xstepW_endPass h
    exact conc003Inv_frame rfl rfl rfl hi
  | park tmr =>
    obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := parkStep_some h
    exact conc003Inv_frame rfl rfl rfl hi
  | wake =>
    obtain ⟨-, -, rfl⟩ := wakeStep_some h
    exact conc003Inv_frame rfl rfl rfl hi
  | request p x r =>
    obtain ⟨-, ⟨-, hs'⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact conc003Inv_keep (by unfold conc003View; rw [hs']) (by rw [hs']; rfl)
        (by rw [hs']; exact Nat.le_succ _) hi
    · exact hi
  | drain =>
    obtain ⟨-, rfl⟩ := drainStep_some h
    exact conc003Inv_frame rfl rfl rfl hi
  | close =>
    obtain ⟨-, rfl⟩ := closeStep_some h
    exact conc003Inv_frame rfl rfl rfl hi
  | terminateNow =>
    obtain ⟨-, rfl⟩ := terminateStep_some h
    exact conc003Inv_frame rfl rfl rfl hi

/-- Along a run of the reference, the invariant holds before every step, against the scan of
the steps before it. -/
theorem conc003Inv_run {C : Cfg N T} {i : Nat} :
    ∀ (pre : List (XStep N T)) (s : XSt N T) (w : Conc003Log N T) (st : XStep N T)
      (post : List (XStep N T)), Conc003Inv i s w → XRun RefExec C s (pre ++ st :: post) →
      Conc003Inv i st.1 (pre.foldl (fun w x => conc003See i w x.2.1) w) ∧
        RefExec C st.1 st.2.1 st.2.2
  | [], s, w, st, post, hi, hr => by
    obtain ⟨h1, h2, -⟩ := hr
    exact ⟨h1 ▸ hi, h2⟩
  | x :: pre, s, w, st, post, hi, hr => by
    obtain ⟨h1, h2, h3⟩ := hr
    subst h1
    exact conc003Inv_run pre x.2.2 (conc003See i w x.2.1) st post (conc003Inv_step h2 hi) h3

/-- Every step of the reference keeps the queued batches of firing `i` (line 3): only a flush
adds to the queue, at its end; a publish takes the oldest entry; a terminal or stopped finish
empties it; every other step leaves it. -/
theorem conc003_ref_kept {C : Cfg N T} {i : Nat} {s s' : XSt N T} {l : XLbl N T}
    (h : RefExec C s l s') : conc003Kept i (conc003Q s i) (conc003Q s' i) l := by
  have keep : s'.pq = s.pq → conc003Q s i <+: conc003Q s' i := fun hq => by
    unfold conc003Q; rw [hq]
  cases l with
  | delay δ => exact keep (by rw [xstepW_delay h])
  | write j p x => obtain ⟨_, _, _, hs'⟩ := writeStep_some h; exact keep (by rw [hs'])
  | flush j =>
    obtain ⟨f, _, _, _, _, ⟨_, _, hs'⟩ | ⟨-, hs'⟩⟩ := flushStep_some h
    · show conc003Q s i <+: conc003Q s' i
      rw [hs']; unfold conc003Q
      simp only [List.filter_append, List.map_append]
      exact List.prefix_append _ _
    · exact keep (by rw [hs'])
  | ret j ok => obtain ⟨_, _, _, hs'⟩ := retStep_some h; exact keep (by rw [hs'])
  | expire j e => obtain ⟨_, _, _, _, _, _, hs'⟩ := expireStep_some h; exact keep (by rw [hs'])
  | commit j => obtain ⟨_, _, _, _, _, _, _, hs'⟩ := commitStep_some h; exact keep (by rw [hs']; rfl)
  | fail j => obtain ⟨_, _, _, _, hs'⟩ := failStep_some h; exact keep (by rw [hs']; rfl)
  | tdeposit j => obtain ⟨_, _, _, _, _, _, hs'⟩ := tdepositStep_some h; exact keep (by rw [hs']; rfl)
  | endCompletions => obtain ⟨_, _, _, _, rfl⟩ := xstepW_endCompletions h; exact keep rfl
  | publish j =>
    obtain ⟨b, rest, hpq, _, _, hs'⟩ := publishStep_some h
    show (if j = i then (conc003Q s i).tail else conc003Q s i) <+: conc003Q s' i
    rw [hs']; unfold conc003Q; rw [hpq]
    by_cases hji : j = i
    · subst hji; simp
    · have hji' : (j == i) = false := by simpa using hji
      simp [hji, hji']
  | endPublications => obtain ⟨_, _, _, rfl⟩ := xstepW_endPublications h; exact keep rfl
  | inject k => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := injectStep_some h; exact keep rfl
  | discard k => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := discardStep_some h; exact keep rfl
  | snapshot a => obtain ⟨_, _, _, rfl⟩ := snapshotStep_some h; exact keep rfl
  | endEvents => obtain ⟨_, _, _, rfl⟩ := xstepW_endEvents h; exact keep rfl
  | update => obtain ⟨_, _, rfl⟩ := xstepW_update h; exact keep rfl
  | deadline ns => obtain ⟨_, _, _, rfl⟩ := xstepW_deadline h; exact keep rfl
  | finish c =>
    cases c with
    | quiescent => obtain ⟨_, _, _, rfl⟩ := xstepW_finishQuiescent h; exact keep rfl
    | closed => obtain ⟨_, _, _, _, rfl⟩ := xstepW_finishClosed h; exact keep rfl
    | terminal => trivial
    | stopped => trivial
  | begin => obtain ⟨_, _, _, _, rfl⟩ := xstepW_begin h; exact keep rfl
  | start n sy =>
    obtain ⟨_, _, _, _, _, _, _, _, _, hs'⟩ := startStep_some h; exact keep (by rw [hs'])
  | lose n => obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := loseStep_some h; exact keep rfl
  | endPass => obtain ⟨_, _, _, _, rfl⟩ := xstepW_endPass h; exact keep rfl
  | park tmr => obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := parkStep_some h; exact keep rfl
  | wake => obtain ⟨_, _, rfl⟩ := wakeStep_some h; exact keep rfl
  | request p x r =>
    obtain ⟨_, ⟨_, hs'⟩ | ⟨-, rfl⟩⟩ := requestStep_some h
    · exact keep (by rw [hs'])
    · exact keep rfl
  | drain => obtain ⟨_, rfl⟩ := drainStep_some h; exact keep rfl
  | close => obtain ⟨_, rfl⟩ := closeStep_some h; exact keep rfl
  | terminateNow => obtain ⟨_, rfl⟩ := terminateStep_some h; exact keep rfl

end Reference

/-- ✓ The reference executor satisfies CONC-003. Along every run, the scan of the labels agrees
with the buffer and outcome of firing `i`, and the queued batches of `i` are the oldest owed ones
(`conc003Inv_step`: a write appends to the buffer, a flush queues the buffer as a batch or drops
it under the relay check, a return or expiry sets the outcome, a publish takes the oldest batch,
a settle removes the firing, a terminal or stopped finish empties the queue), so a commit
deposits the frozen emission and a publish deposits the oldest owed batch (lines 1 and 2); only a
flush, a publish and a terminal or stopped finish change the queue (line 3, `conc003_ref_kept`). -/
@[evidence holds CONC_003]
theorem CONC_003_reference {N T : Type} [DecidableEq N] :
    CONC_003 (RefExec (N := N) (T := T)) := by
  intro C i
  refine ⟨fun s0 h0 hq tr hr => ?_, fun s l s' h => conc003_ref_kept h⟩
  have hv0 : conc003View s0 i = none := by
    unfold conc003View
    rw [List.find?_eq_none]
    intro f hf
    simpa using h0 f hf
  have hq0 : conc003Q s0 i = [] := by
    unfold conc003Q
    rw [List.filter_eq_nil_iff.mpr (fun x hx hxi => hq x.2 (by
      simp only [beq_iff_eq] at hxi; rw [← hxi]; exact hx)), List.map_nil]
  have hinit : Conc003Inv i s0 conc003Init :=
    ⟨by rw [hv0]; exact ⟨rfl, rfl, rfl⟩, by rw [hq0]; exact List.prefix_refl _, fun _ => hq0,
      fun hc => absurd hv0 hc⟩
  refine ⟨fun pre s s' post htr => ?_, fun pre s s' post htr => ?_⟩
  · subst htr
    obtain ⟨hi, hs⟩ := conc003Inv_run pre s0 conc003Init (s, .commit i, s') post hinit hr
    change RefExec C s (.commit i) s' at hs
    change Conc003Inv i s (conc003Log i pre) at hi
    obtain ⟨f, e, hf, he, -, -, -, hs'⟩ := commitStep_some hs
    have ha := hi.1
    rw [show conc003View s i = some f from hf] at ha
    simp only [conc003Agree, he] at ha
    exact ⟨e, ha.1, by rw [hs']; rfl⟩
  · subst htr
    obtain ⟨hi, hs⟩ := conc003Inv_run pre s0 conc003Init (s, .publish i, s') post hinit hr
    change RefExec C s (.publish i) s' at hs
    change Conc003Inv i s (conc003Log i pre) at hi
    obtain ⟨b, rest, hpq, -, -, hs'⟩ := publishStep_some hs
    have hqs : conc003Q s i = b :: (rest.filter (·.1 == i)).map (·.2) := by
      unfold conc003Q; rw [hpq]; simp
    obtain ⟨t, ht⟩ := hi.2.1
    refine ⟨b, ?_, by rw [hs']⟩
    rw [← ht, hqs]; rfl

/-! ### Decided runs of any executor given as a step function -/

section Runs

variable {N T : Type}

/-- The step trace of a label run of a step function `g`, if every label is a step. -/
def conc003Trace (g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)) (C : Cfg N T) :
    XSt N T → List (XLbl N T) → Option (List (XStep N T))
  | _, [] => some []
  | s, l :: ls => (g C s l).bind fun s' => (conc003Trace g C s' ls).map ((s, l, s') :: ·)

/-- A trace `conc003Trace` builds is a run of the executor of `g`. -/
theorem conc003Trace_run {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T} :
    ∀ {s : XSt N T} {ls : List (XLbl N T)} {tr : List (XStep N T)},
      conc003Trace g C s ls = some tr → XRun (fun C s l s' => g C s l = some s') C s tr
  | s, [], tr, h => by cases h; trivial
  | s, l :: ls, tr, h => by
    simp only [conc003Trace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : conc003Trace g C s' ls with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs, conc003Trace_run ht⟩

/-- The trace of `ls₁ ++ l :: ls₂` splits at the step labelled `l`: before it, the trace of
`ls₁`. -/
theorem conc003Trace_split {g : Cfg N T → XSt N T → XLbl N T → Option (XSt N T)} {C : Cfg N T}
    {l : XLbl N T} {ls₂ : List (XLbl N T)} :
    ∀ {s : XSt N T} {ls₁ : List (XLbl N T)} {tr : List (XStep N T)},
      conc003Trace g C s (ls₁ ++ l :: ls₂) = some tr →
      ∃ pre s₁ s₂ post, tr = pre ++ (s₁, l, s₂) :: post ∧ conc003Trace g C s ls₁ = some pre ∧
        g C s₁ l = some s₂ ∧ (XRun.last s pre) = s₁
  | s, [], tr, h => by
    simp only [List.nil_append, conc003Trace] at h
    cases hs : g C s l with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : conc003Trace g C s' ls₂ with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        exact ⟨[], s, s', tr', by simp [h], rfl, hs, rfl⟩
  | s, l₀ :: ls₁, tr, h => by
    simp only [List.cons_append, conc003Trace] at h
    cases hs : g C s l₀ with
    | none => simp [hs] at h
    | some s' =>
      simp only [hs, Option.bind_some] at h
      cases ht : conc003Trace g C s' (ls₁ ++ l :: ls₂) with
      | none => simp [ht] at h
      | some tr' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨pre, s₁, s₂, post, rfl, hp, hg, hl⟩ := conc003Trace_split ht
        refine ⟨(s, l₀, s') :: pre, s₁, s₂, post, rfl, ?_, hg, ?_⟩
        · simp [conc003Trace, hs, hp]
        · cases pre with
          | nil => simpa [XRun.last] using hl
          | cons y ys => simpa [XRun.last, List.getLast?_cons] using hl

/-- Every step of a run is a step of its executor. -/
theorem conc003_run_step {R : XRel N T} {C : Cfg N T} :
    ∀ (pre : List (XStep N T)) {s0 s s' : XSt N T} {l : XLbl N T} {post : List (XStep N T)},
      XRun R C s0 (pre ++ (s, l, s') :: post) → R C s l s'
  | [], _, _, _, _, _, hr => hr.2.1
  | _ :: pre, _, _, _, _, _, hr => conc003_run_step pre hr.2.2

/-- Line 3 of CONC-003 for one step, decided. -/
def conc003KeptB [DecidableEq N] [DecidableEq T] (i : Nat) (q q' : List (List (N × T))) :
    XLbl N T → Bool
  | .publish j => decide ((if j = i then q.tail else q) <+: q')
  | .finish .terminal | .finish .stopped => true
  | _ => decide (q <+: q')

/-- The decided form of line 3 holds where line 3 holds. -/
theorem conc003KeptB_of [DecidableEq N] [DecidableEq T] {i : Nat} {q q' : List (List (N × T))}
    {l : XLbl N T} (h : conc003Kept i q q' l) : conc003KeptB i q q' l = true := by
  cases l
  case finish c => cases c <;> first | rfl | exact decide_eq_true h
  all_goals exact decide_eq_true h

/-- The lines of CONC-003 as a check over a trace at the places `ps`: every step keeps the queued
batches of `i`, every commit of `i` deposits the scan's frozen emission, every publish of `i`
deposits the scan's oldest owed batch. -/
def conc003Ok [DecidableEq N] [DecidableEq T] (ps : List N) (i : Nat) :
    Conc003Log N T → List (XStep N T) → Bool
  | _, [] => true
  | w, (s, l, s') :: rest =>
    conc003KeptB i (conc003Q s i) (conc003Q s' i) l &&
    (match l with
     | .commit j => j != i || (match w.returned with
         | some e => ps.all fun p => s'.M p == qAppend s.M e p
         | none => false)
     | .publish j => j != i || (match w.owed.head? with
         | some b => ps.all fun p => s'.M p == qAppend s.M b p
         | none => false)
     | _ => true) && conc003Ok ps i (conc003See i w l) rest

/-- An executor that satisfies CONC-003 passes the check on every run from a state where firing
`i` is not in flight and has no queued publication. -/
theorem conc003Ok_of [DecidableEq N] [DecidableEq T] {R : XRel N T} (h : CONC_003 R)
    {C : Cfg N T} {i : Nat} {s0 : XSt N T} (h0 : ∀ f ∈ s0.fl, f.id ≠ i)
    (hq : ∀ b, (i, b) ∉ s0.pq) {tr : List (XStep N T)} (hr : XRun R C s0 tr) (ps : List N) :
    conc003Ok ps i conc003Init tr = true := by
  obtain ⟨hrun, hk⟩ := h C i
  obtain ⟨hc, hp⟩ := hrun s0 h0 hq tr hr
  suffices key : ∀ (rest pre : List (XStep N T)), tr = pre ++ rest →
      conc003Ok ps i (conc003Log i pre) rest = true from key tr [] rfl
  intro rest
  induction rest with
  | nil => intro _ _; rfl
  | cons x rest ih =>
    intro pre htr
    obtain ⟨s, l, s'⟩ := x
    have hnext := ih (pre ++ [(s, l, s')]) (by simp [htr])
    have hlog : conc003Log i (pre ++ [(s, l, s')]) = conc003See i (conc003Log i pre) l := by
      simp [conc003Log, List.foldl_append]
    rw [hlog] at hnext
    have hstep : R C s l s' := conc003_run_step pre (htr ▸ hr)
    have hkb := conc003KeptB_of (hk s l s' hstep)
    simp only [conc003Ok, hnext, hkb, Bool.and_true, Bool.true_and]
    cases l with
    | commit j =>
      by_cases hj : j = i
      · subst hj
        obtain ⟨e, he, hM⟩ := hc pre s s' rest htr
        simp [he, hM]
      · simp [hj]
    | publish j =>
      by_cases hj : j = i
      · subst hj
        obtain ⟨b, hb, hM⟩ := hp pre s s' rest htr
        simp [hb, hM]
      · simp [hj]
    | _ => rfl

end Runs

/-! ### Examples

One transition `t` takes one token from place `0` and has no output spec; validation and the
join-relay check accept everything. The action of the firing (identity `0`) writes `10` to place
`1` and flushes it, then writes `20` to `1` and `30` to `2`, and returns. -/

/-- The transition of the examples. -/
def conc003_t : Trans Nat :=
  { core := { name := "t", inputs := [⟨0, .one⟩], inhibitors := [], reads := [], resets := [] },
    out := none }

/-- The configuration of the examples. -/
def conc003_cfg : Cfg Nat Nat :=
  { X := { net := { places := [0, 1, 2], transitions := [conc003_t] },
           timing := fun _ => .immediate, tol := 0 },
    prio := fun _ => 0, terminals := [], envs := [], reentrant := false,
    validate := fun _ _ => true, relay := fun _ _ _ => true,
    timeoutOut := fun _ _ _ => false, res := 0 }

/-- The initial state: one token `7` in place `0`, nothing in flight. -/
def conc003_s0 : XSt Nat Nat := xinit (fun p => if p = 0 then [7] else []) 0

/-- One cycle up to an asynchronous start of `t`, which becomes firing `0`. -/
def conc003_pre : List (XLbl Nat Nat) :=
  [.endCompletions, .endPublications, .endEvents, .update, .deadline [], .begin, .start "t" false]

/-- The initial state meets the premises of the lines for firing `0`. -/
theorem conc003_s0_fl : ∀ f ∈ conc003_s0.fl, f.id ≠ 0 := by simp [conc003_s0, xinit]

/-- The initial state has no queued publication. -/
theorem conc003_s0_pq : ∀ b, ((0 : Nat), b) ∉ conc003_s0.pq := by simp [conc003_s0, xinit]

/-- Refute CONC-003 for the executor of `g` from a decided failing check of one label run. -/
theorem conc003_refute {g : Cfg Nat Nat → XSt Nat Nat → XLbl Nat Nat → Option (XSt Nat Nat)}
    {ls : List (XLbl Nat Nat)}
    (hd : (conc003Trace g conc003_cfg conc003_s0 ls).map (conc003Ok [0, 1, 2] 0 conc003Init) =
      some false) :
    ¬ CONC_003 (fun C s l s' => g C s l = some s') := by
  intro h
  cases ht : conc003Trace g conc003_cfg conc003_s0 ls with
  | none => simp [ht] at hd
  | some tr =>
    simp only [ht, Option.map_some, Option.some.injEq] at hd
    have := conc003Ok_of h conc003_s0_fl conc003_s0_pq (conc003Trace_run ht) [0, 1, 2]
    rw [hd] at this
    exact Bool.false_ne_true this

/-! ### Violation: a start-time snapshot (a stale read) -/

/-- An executor that takes the action's output when the action hands back its handle: an
asynchronous action has written nothing then, so its normal return carries an empty emission. -/
def conc003_startSnapshotStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .ret i ok => (xstep C s (.ret i ok)).map fun s₁ =>
      { s₁ with fl := updFiring s₁ i fun g =>
          { g with out := match g.out with
                          | some (.ok _) => some (.ok [])
                          | o => o } }
  | l => xstep C s l

/-- ✗ A start-time snapshot violates CONC-003 (line 1, AC2): the action writes `20` to `1` and
returns, and the commit deposits nothing. -/
@[evidence forbids CONC_003]
theorem CONC_003_forbids_startSnapshot :
    ¬ CONC_003 (fun C s l s' => conc003_startSnapshotStep (N := Nat) (T := Nat) C s l = some s') :=
  conc003_refute (ls := conc003_pre ++ [.write 0 1 20, .ret 0 true, .endPass, .commit 0])
    (by decide)

/-! ### Violation: a token written after the return is deposited -/

/-- An executor that accepts a write after the action returned and adds it to the emission. -/
def conc003_lateWriteStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .write i p x =>
    match s.fl.find? (·.id == i) with
    | some f =>
      match f.out with
      | some (.ok e) => some { s with fl := updFiring s i fun g =>
          { g with out := some (.ok (e ++ [(p, x)])) } }
      | _ => xstep C s (.write i p x)
    | none => none
  | l => xstep C s l

/-- ✗ Depositing a token written after the return violates CONC-003 (line 1): the action writes
`20` to `1`, returns, then writes `99` to `2`, and the commit deposits `99` too. -/
@[evidence forbids CONC_003]
theorem CONC_003_forbids_lateWrite :
    ¬ CONC_003 (fun C s l s' => conc003_lateWriteStep (N := Nat) (T := Nat) C s l = some s') :=
  conc003_refute
    (ls := conc003_pre ++ [.write 0 1 20, .ret 0 true, .write 0 2 99, .endPass, .commit 0])
    (by decide)

/-! ### Violation: the tokens of one place deposited out of write order -/

/-- An executor whose commit deposits the emission in reverse order. -/
def conc003_reversedStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i => (xstep C s (.commit i)).map fun s₁ =>
      match s.fl.find? (·.id == i) with
      | some f =>
        match f.out with
        | some (.ok e) => { s₁ with M := qAppend s.M e.reverse }
        | _ => s₁
      | none => s₁
  | l => xstep C s l

/-- ✗ Depositing out of write order violates CONC-003 (line 1, "in the order the action wrote
them"): the action writes `20` then `21` to `1`, and the commit leaves `[21, 20]` in `1`. -/
@[evidence forbids CONC_003]
theorem CONC_003_forbids_reversed :
    ¬ CONC_003 (fun C s l s' => conc003_reversedStep (N := Nat) (T := Nat) C s l = some s') :=
  conc003_refute
    (ls := conc003_pre ++ [.write 0 1 20, .write 0 1 21, .ret 0 true, .endPass, .commit 0])
    (by decide)

/-! ### Violation: the completion carries every write since the start -/

/-- An executor whose flush queues the batch but keeps it in the buffer, so the completion
carries every token the action wrote (the reading "all writes are visible at completion"). -/
def conc003_flushKeepsStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .flush i => (xstep C s (.flush i)).map fun s₁ =>
      match s.fl.find? (·.id == i) with
      | some f => { s₁ with fl := updFiring s₁ i fun g => { g with buf := f.buf } }
      | none => s₁
  | l => xstep C s l

/-- ✗ Depositing at completion what was already published violates CONC-003 (line 1): the
action writes `10` to `1`, flushes, writes `20` to `1` and returns; the commit deposits `10`
again with `20`. -/
@[evidence forbids CONC_003]
theorem CONC_003_forbids_flushKeeps :
    ¬ CONC_003 (fun C s l s' => conc003_flushKeepsStep (N := Nat) (T := Nat) C s l = some s') :=
  conc003_refute
    (ls := conc003_pre ++ [.write 0 1 10, .flush 0, .write 0 1 20, .ret 0 true, .endPass,
      .commit 0])
    (by decide)

/-! ### Violation: a firing whose action failed is committed -/

/-- An executor that commits a firing whose action returned with an error, depositing what the
action wrote before it failed. -/
def conc003_commitAfterErrorStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i =>
    match s.fl.find? (·.id == i) with
    | some f =>
      match f.out with
      | some .err => some (depositAt C s i f.buf)
      | _ => xstep C s (.commit i)
    | none => none
  | l => xstep C s l

/-- ✗ Committing a firing whose action failed violates CONC-003 (line 1, "before it returned"):
the action writes `20` to `1` and returns with an error, and the commit deposits `20`. -/
@[evidence forbids CONC_003]
theorem CONC_003_forbids_commitAfterError :
    ¬ CONC_003 (fun C s l s' =>
      conc003_commitAfterErrorStep (N := Nat) (T := Nat) C s l = some s') :=
  conc003_refute (ls := conc003_pre ++ [.write 0 1 20, .ret 0 false, .endPass, .commit 0])
    (by decide)

/-! ### Violation: a publication read from the live output -/

/-- An executor that, when it processes a publication, deposits the batch and whatever the
action has written since (it reads the action's live output, not the flushed batch). -/
def conc003_liveReadStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .publish i => (xstep C s (.publish i)).map fun s₁ =>
      match s.fl.find? (·.id == i) with
      | some f => { s₁ with M := qAppend s₁.M f.buf }
      | none => s₁
  | l => xstep C s l

/-- ✗ Reading a publication from the live output violates CONC-003 (line 2): the action writes
`10` to `1` and flushes, then writes `30` to `2`; the publication, processed while the action
is still running, deposits `30` too. -/
@[evidence forbids CONC_003]
theorem CONC_003_forbids_liveRead :
    ¬ CONC_003 (fun C s l s' => conc003_liveReadStep (N := Nat) (T := Nat) C s l = some s') :=
  conc003_refute
    (ls := conc003_pre ++ [.write 0 1 10, .flush 0, .write 0 2 30, .endPass, .endCompletions,
      .publish 0])
    (by decide)

/-! ### Violation: a batch deposited out of write order -/

/-- An executor whose publish deposits the batch in reverse order. -/
def conc003_reversedBatchStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .publish i => (xstep C s (.publish i)).map fun s₁ =>
      match s.pq with
      | (_, b) :: _ => { s₁ with M := qAppend s.M b.reverse }
      | [] => s₁
  | l => xstep C s l

/-- ✗ Depositing a batch out of write order violates CONC-003 (line 2, "in the order the action
wrote them"): the action writes `10` then `11` to `1` and flushes, and the publication leaves
`[11, 10]` in `1`. -/
@[evidence forbids CONC_003]
theorem CONC_003_forbids_reversedBatch :
    ¬ CONC_003 (fun C s l s' =>
      conc003_reversedBatchStep (N := Nat) (T := Nat) C s l = some s') :=
  conc003_refute
    (ls := conc003_pre ++ [.write 0 1 10, .write 0 1 11, .flush 0, .endPass, .endCompletions,
      .publish 0])
    (by decide)

/-! ### Violation: the oldest batch deposited, the newest dequeued -/

/-- An executor whose publish deposits the oldest queued batch but removes the newest entry of
the queue (a TypeScript `queue[0]` read with `queue.pop()`, or a Java `Deque` read with
`peekFirst()` and drained with `pollLast()`). -/
def conc003_dupBatchStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .publish i => (xstep C s (.publish i)).map fun s₁ => { s₁ with pq := s.pq.dropLast }
  | l => xstep C s l

/-- ✗ Depositing the oldest batch and dequeuing the newest violates CONC-003 (line 2, "the
earliest publication of that action it has not yet deposited"): the action writes `10` to `1`
and flushes, writes `11` to `1` and flushes; the second publication deposits `10` again, and `11`
is never deposited. The first publication, which removes the newest batch, also breaks line 3. -/
@[evidence forbids CONC_003]
theorem CONC_003_forbids_dupBatch :
    ¬ CONC_003 (fun C s l s' => conc003_dupBatchStep (N := Nat) (T := Nat) C s l = some s') :=
  conc003_refute
    (ls := conc003_pre ++ [.write 0 1 10, .flush 0, .write 0 1 11, .flush 0, .endPass,
      .endCompletions, .publish 0, .publish 0])
    (by decide)

/-! ### Violation: a flush after an error return is published -/

/-- An executor that still flushes the buffer of an action that returned with an error, and
queues it as a publication. -/
def conc003_flushAfterErrorStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .flush i =>
    match s.fl.find? (·.id == i) with
    | some f =>
      match f.out with
      | some .err =>
        if f.buf.isEmpty then none
        else some { s with pq := s.pq ++ [(i, f.buf)],
                           fl := updFiring s i fun g => { g with buf := [] } }
      | _ => xstep C s (.flush i)
    | none => none
  | l => xstep C s l

/-- ✗ Publishing what an action flushed after it returned with an error violates CONC-003
(line 2, "before it completed"): the action writes `10` to `1` and returns with an error, its
buffer is flushed and the publication deposits `10`. -/
@[evidence forbids CONC_003]
theorem CONC_003_forbids_flushAfterError :
    ¬ CONC_003 (fun C s l s' =>
      conc003_flushAfterErrorStep (N := Nat) (T := Nat) C s l = some s') :=
  conc003_refute
    (ls := conc003_pre ++ [.write 0 1 10, .ret 0 false, .flush 0, .endPass, .fail 0,
      .endCompletions, .publish 0])
    (by decide)

/-! ### Violation: the completion withdraws the firing's queued publications -/

/-- An executor whose commit of firing `i` also removes every queued publication of `i` (a
per-firing cleanup at completion that drops the firing's pending publications). Completions are
settled before publications, so an action that flushes and returns in one cycle loses its
batch. -/
def conc003_dropAtCommitStep {N T : Type} [DecidableEq N] (C : Cfg N T) (s : XSt N T) :
    XLbl N T → Option (XSt N T)
  | .commit i => (xstep C s (.commit i)).map fun s₁ => { s₁ with pq := s₁.pq.filter (·.1 != i) }
  | l => xstep C s l

/-- ✗ Withdrawing a queued publication at the commit violates CONC-003 (line 3, "until it
deposits each one"): the action writes `10` to `1`, flushes and returns, and the commit, which
runs before the publication is processed, removes the batch, so `10` is never deposited. -/
@[evidence forbids CONC_003]
theorem CONC_003_forbids_dropAtCommit :
    ¬ CONC_003 (fun C s l s' => conc003_dropAtCommitStep (N := Nat) (T := Nat) C s l = some s') :=
  conc003_refute
    (ls := conc003_pre ++ [.write 0 1 10, .flush 0, .ret 0 true, .endPass, .commit 0])
    (by decide)

/-! ### Every line exercised -/

/-- The run of the examples on the reference, up to the commit of firing `0`. -/
def conc003_toCommit : List (XLbl Nat Nat) :=
  conc003_pre ++ [.write 0 1 10, .flush 0, .write 0 1 20, .write 0 2 30, .ret 0 true, .endPass]

/-- Every line of CONC-003 applies to a run of the reference: after `10` was written to `1` and
flushed, and `20` to `1` and `30` to `2` were written before the return, the commit of firing `0`
deposits exactly `[(1, 20), (2, 30)]` (line 1, AC1) and keeps the queued batch `[(1, 10)]`
(line 3), and the later publication deposits that batch, the oldest one owed, behind them
(line 2). -/
@[evidence nonvacuous CONC_003]
theorem CONC_003_nonvacuous :
    (∃ tr pre s s' post, XRun RefExec conc003_cfg conc003_s0 tr ∧
      tr = pre ++ (s, .commit 0, s') :: post ∧
      (conc003Log 0 pre).returned = some [(1, 20), (2, 30)] ∧ s'.M 1 = [20] ∧ s'.M 2 = [30] ∧
      conc003Q s 0 = [[(1, 10)]] ∧ conc003Q s' 0 = [[(1, 10)]]) ∧
    (∃ tr pre s s' post, XRun RefExec conc003_cfg conc003_s0 tr ∧
      tr = pre ++ (s, .publish 0, s') :: post ∧
      (conc003Log 0 pre).owed = [[(1, 10)]] ∧ s'.M 1 = [20, 10]) := by
  constructor
  · obtain ⟨tr, htr⟩ : ∃ tr, conc003Trace xstep conc003_cfg conc003_s0
        (conc003_toCommit ++ .commit 0 :: []) = some tr :=
      Option.isSome_iff_exists.mp (by decide)
    obtain ⟨pre, s, s', post, rfl, hp, hs, hl⟩ := conc003Trace_split htr
    have h1 : (conc003Trace xstep conc003_cfg conc003_s0 conc003_toCommit).map
        (fun pre => (conc003Log 0 pre).returned == some [(1, 20), (2, 30)] &&
          conc003Q (XRun.last conc003_s0 pre) 0 == [[(1, 10)]] &&
          ((xstep conc003_cfg (XRun.last conc003_s0 pre) (.commit 0)).map
            fun s' => s'.M 1 == [20] && s'.M 2 == [30] && conc003Q s' 0 == [[(1, 10)]]) ==
              some true) = some true := by
      decide
    rw [hp] at h1
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, beq_iff_eq, hl, hs,
      Option.map_some] at h1
    exact ⟨_, pre, s, s', post, conc003Trace_run htr, rfl, h1.1.1, h1.2.1.1, h1.2.1.2, h1.1.2,
      h1.2.2⟩
  · obtain ⟨tr, htr⟩ : ∃ tr, conc003Trace xstep conc003_cfg conc003_s0
        ((conc003_toCommit ++ [.commit 0, .endCompletions]) ++ .publish 0 :: []) = some tr :=
      Option.isSome_iff_exists.mp (by decide)
    obtain ⟨pre, s, s', post, rfl, hp, hs, hl⟩ := conc003Trace_split htr
    have h1 : (conc003Trace xstep conc003_cfg conc003_s0
        (conc003_toCommit ++ [.commit 0, .endCompletions])).map
        (fun pre => (conc003Log 0 pre).owed == [[(1, 10)]] &&
          ((xstep conc003_cfg (XRun.last conc003_s0 pre) (.publish 0)).map
            fun s' => s'.M 1 == [20, 10]) == some true) = some true := by
      decide
    rw [hp] at h1
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, beq_iff_eq, hl, hs,
      Option.map_some] at h1
    exact ⟨_, pre, s, s', post, conc003Trace_run htr, rfl, h1.1, h1.2⟩

end Libpetri.Spec
