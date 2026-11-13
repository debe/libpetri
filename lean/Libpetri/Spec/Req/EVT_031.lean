import Libpetri.Spec.Registry
import Libpetri.Reference.Subscriptions
import Libpetri.Spec.Text.EVT_031

set_option linter.missingDocs true

/-!
# EVT-031: EventStore Live Subscriptions (`spec/08-events-observability.md`)

A live subscription streams the events appended to a store, filtered and in batches, over a
bounded channel. The requirement is a predicate over an abstract store with live subscriptions,
`S : SubSem E` (`Reference/Subscriptions.lean`): the label sequences the store allows, where a
label is an operation on the store, a subscribe, the start of a receive, a take from the channel,
a returned batch, a reported end of the stream, a close, or the drop of the store. The lines are
stated with the observation functions of that module and the block-local ones below (the labels
of one subscription, receives that return given batches, the events a channel holds, and whether
a subscription has ended), all of which read a label sequence only.

The witness is `evt031PySub`, the reference `refSub` restricted to the subscribe form of the one
implementation (the Python binding's store, rust/libpetri-py/src/events.rs): every channel has a
finite capacity. The reference follows rulings D86 (a) and (d): an append that finds a channel
full ends that subscription and never waits, and a close with no receive pending ends the
stream. The wrong stores are a store whose receive may return an empty batch, which meets every
other line (`EVT_031_mutant_emptyBatch`, over the lines one by one, `evt031_iff`), the switches
of the model (a subscription that replays earlier
events, one that ignores its filter, batches over the batch size, an overflow that drops only the
event that does not fit, back-pressure, a close that does nothing), a store that ignores the
channel capacity, the unbounded channel of the debug stores, a receive that returns an event
before it is appended, stores whose receives do not report the end (after an overflow, after a
close, later after a close, after a drop, after a receive that took part of the channel following
an overflow or a drop), stores whose receives report the end before they have taken what the
channel held (after an overflow, after a drop), and a receive that returns fewer events than it
took.
-/

namespace Libpetri.Spec

open Libpetri.Reference
open scoped List

/-! ## Block-local observations -/

/-- Whether a label is one of subscription `i`'s own: its subscribe, the start of a receive, a
take, a returned batch, a reported end, or a close of `i`. -/
def evt031Own {E : Type} (i : Nat) : SubLbl E → Bool
  | .subscribe j _ _ _ => decide (j = i)
  | .await j => decide (j = i)
  | .pull j => decide (j = i)
  | .recv j _ => decide (j = i)
  | .finish j => decide (j = i)
  | .close j => decide (j = i)
  | _ => false

/-- Whether none of the labels `mid` is one of subscription `i`'s own. -/
def evt031Quiet {E : Type} (i : Nat) (mid : List (SubLbl E)) : Bool :=
  mid.all fun l => !evt031Own i l

/-- Whether a label closes subscription `i`. -/
def evt031CloseOf {E : Type} (i : Nat) : SubLbl E → Bool
  | .close j => decide (j = i)
  | _ => false

/-- Whether none of the labels `mid` closes subscription `i`. -/
def evt031NoClose {E : Type} (i : Nat) (mid : List (SubLbl E)) : Bool :=
  mid.all fun l => !evt031CloseOf i l

/-- The receives that hand subscription `i` the batches `bs`, in order: for each batch, a receive
starts, takes the batch's events from the channel one at a time, and returns the batch. -/
def evt031Recvs {E : Type} (i : Nat) (bs : List (List E)) : List (SubLbl E) :=
  bs.flatMap fun b => .await i :: ((b.map fun _ => .pull i) ++ [.recv i b])

/-- The events the channel of subscription `i` holds after `tr`, read from the labels: the
matching events appended since it subscribed, less as many as its receives took. It is the
content of the channel while the subscription has not ended (`evt031Ended`) and no receive of it
is pending. -/
def evt031Held {E : Type} (i : Nat) (tr : List (SubLbl E)) : List E :=
  (matchingAfter i tr).drop (pulls i tr)

/-- Whether the label `l`, after the labels `p`, ends subscription `i`: an append of an event its
filter matches that finds its channel full (the backlog reached a finite capacity), a close of
`i` made while no receive of `i` is pending, or the drop of the store. -/
def evt031Ends {E : Type} (i : Nat) (p : List (SubLbl E)) : SubLbl E → Bool
  | .op (.append e) =>
    match subParams i p with
    | some (f, some c, _) => f e && decide (c ≤ backlog i p)
    | _ => false
  | .close j => decide (j = i) && !pending i p
  | .drop => true
  | _ => false

/-- After the labels `p`, whether one of the labels `tr` ends subscription `i`. -/
def evt031EndedFrom {E : Type} (i : Nat) : List (SubLbl E) → List (SubLbl E) → Bool
  | _, [] => false
  | p, l :: tr => evt031Ends i p l || evt031EndedFrom i (p ++ [l]) tr

/-- Whether subscription `i` was ended in `tr` (`evt031Ends`). -/
def evt031Ended {E : Type} (i : Nat) (tr : List (SubLbl E)) : Bool := evt031EndedFrom i [] tr

/-! ## EVT-031: EventStore Live Subscriptions -/

requirement EVT_031
  id "EVT-031"
  title "EventStore Live Subscriptions"
  kind B
  scope "the live subscriptions of an event store, where an implementation provides them: the Python binding's InMemoryEventStore (subscribe and subscribe_stream, run on Rust in rust/libpetri-py); Java, TypeScript and the Rust crate's own InMemoryEventStore have none (spec/runtime-defects.md, UB-04)"
  source verbatim "spec/08-events-observability.md"
  covers EVT_031.s1, EVT_031.s2, EVT_031.s3, EVT_031.s4, EVT_031.s5, EVT_031.s6, EVT_031.s7,
        EVT_031.s8
  reading "For every store with live subscriptions S over any event type E (S is the set of label sequences the store allows):"
          "1. at every point of every run of S, what each subscription i has received so far, its batches concatenated, is a sublist of the events appended after i subscribed and before that point that its filter matches;"
          "2. every batch i received in a run of S is non-empty, and i subscribed with a batch size of at least its length;"
          "3. every subscription made in a run of S has a finite channel capacity;"
          "4. if an append of an event that the filter of i matches finds the channel of i full (i subscribed with capacity c, and its backlog, the matching events appended since it subscribed that no receive took, has reached c), then over the whole run i received only matching events appended before that append;"
          "5. after such an append made while no receive of i was pending, followed by any labels after which no receive of i is pending (receives of i that took part of the channel among them), S allows receives of i that return some batches, followed by a receive that reports the end;"
          "6. if moreover i had not ended before that append (by an earlier such append, a close made while no receive of i was pending, or the drop), then whenever a receive of i reports the end after it with no close of i in between, the events i received in between are exactly the events its channel held: the matching events appended since it subscribed, less as many as its receives took;"
          "7. after every run of S in which the store was not dropped, S allows one more append;"
          "8. after a close of a subscription i made before, while no receive of i was pending, i receives nothing;"
          "9. after such a close, followed by any labels none of which is i's own, S allows a receive of i that reports the end;"
          "10. after the drop of the store, for every subscription i made before with no receive pending, followed by any labels after which no receive of i is pending, S allows receives of i that return some batches, followed by a receive that reports the end;"
          "11. if moreover i had not ended before the drop, then whenever a receive of i reports the end after the drop with no close of i in between, the events i received in between are exactly the events its channel held at the drop;"
          "12. at every point of every run of S where no receive of i is pending, what i has received so far, its batches concatenated, is exactly the first of the matching events appended after i subscribed, as many as its receives took from the channel: each receive returns the events it took."
  assumes "The model is the observation of one store with live subscriptions, S : SubSem E (Reference/Subscriptions.lean): the label sequences it allows. A label is a store operation (op), a subscribe with a filter, a channel capacity (none: unbounded) and a batch size, the start of a receive (await), a take of the oldest event from the channel by the pending receive (pull), a returned batch (recv), a reported end of the stream (finish, Python's StopAsyncIteration), a close, or the drop of the store. The observation functions received, batches, subParams, matchingAfter, pulls, backlog and pending, and the block-local evt031Own and evt031Quiet (the labels of a subscription), evt031NoClose, evt031Recvs (receives returning given batches), evt031Held (the events the channel holds, by the labels) and evt031Ended (an overflow, a close with no receive pending, or the drop happened), read the labels only. The event type E is a parameter: the lines say nothing about what an event holds. Lines 1 and 12 are stated at every point of a run, so S need not be closed under prefixes."
          "Filters: a filter is a predicate on events. Which events a filter by type, transition and place matches is the matching rule of [EVT-030]; the Python binding evaluates both with one FilterSpec (rust/libpetri-py/src/events.rs), and this block does not restate the rule. AC1 and the first quoted sentence are line 1: a sublist of the matching events appended after the subscribe is filtered, in append order and at most once, and AC2 (forward-only) is its 'after'. Line 1 is stated at every point of a run, not on whole runs only, so a receive cannot return an event before that event is appended (mutant EVT_031_mutant_early); S need not be closed under prefixes."
          "Batches: AC3 and the second quoted sentence are line 2; a store whose receive may return an empty batch meets every other line and the batch-size half of line 2, and fails it (EVT_031_mutant_emptyBatch); evt031_unary derives one event per batch from a batch size of 1, whatever the timeout, which is the runtime's behaviour (the batch loop runs only when batch_size > 1). The fourth quoted sentence, on how a receive builds its batch, is line 12 for its untimed content: a receive returns the batch of the events it took, so where no receive of i is pending, what i received is the first matching events appended after it subscribed, as many as its receives took (pull takes the oldest event of the channel, which holds the matching events in append order until the subscription ends). A receive that takes two events and returns a batch holding only the first, so that the second is lost although the channel never overflowed, fails line 12 (EVT_031_mutant_lossyBatch); line 1 alone allows it, since a sublist may leave events out, and lines 6 and 11 count every taken event as received. The rest of that sentence is the batch timeout: when a receive stops adding events (batch_size events, batch_timeout_ms elapsed since the first event, or no further event can arrive) and 'flushing early after batch_timeout_ms' in AC3 are kind T on tokio's clock (the receive in rust/libpetri-py/src/events.rs waits with tokio::time::timeout from tokio::time::Instant::now()), which the executor clock seam of [TIME-015] (Python's ExecutorOptions(clock=...)) does not reach: they cannot be tested on virtual time and are not modelled. Its untimed clause, a timeout of 0 adding only the events already in the channel, is not stated either, because the subscribe label carries no timeout. The model lets a receive return a non-empty batch at any moment, which every timeout meets, and lines 5 and 10 allow any batching of what the channel holds, so a receive that takes every buffered event up to batch_size, as the runtime's does, meets them (EVT_031_allows_greedy). A receive that its caller abandons while it is pending (a cancelled Python await) is not a label of the model, so no line speaks of the events such a receive had taken."
          "Capacity: the third quoted sentence is line 3. The witness evt031PySub is the reference with a finite capacity on every subscribe, the form of the Python store, whose channel_capacity is a positive integer. The reference alone also allows an unbounded channel (none), the debug stores' form of [EVT-024], and it violates line 3 (EVT_031_mutant_unboundedChannel)."
          "Overflow (AC4 and ruling D86 (a)): the fifth quoted sentence is lines 4, 5 and 6. Line 4 names the full channel by observations: the backlog of i (matching events appended since it subscribed, less those its receives took) has reached its capacity, and the appended event matches the filter of i. Line 5 says the stream can end, at every later point where no receive of i is pending, rather than hang: right after the overflow (EVT_031_mutant_overflowHangs) and also after receives that took part of the channel (EVT_031_mutant_partialHangs); line 6 says it does not end before the receives have taken what the channel held, which evt031Held reads from the labels while the subscription has not ended. A close of i after the overflow ends the stream at once (lines 8 and 9), which is the clause 'unless the subscription is closed first' and why line 6 has no close of i in between. evt031_overflow_drains derives from lines 5 and 6 that the drain S allows returns exactly what the channel held. A receive pending at the overflowing append is outside the lines, as the qualifier of the sentence says. Python's capacity is always finite; line 4 speaks only of a finite one."
          "Append: the sixth quoted sentence is line 7: S allows an append after every run before the drop, whatever the reason a store might refuse one, and in particular an append does not wait for room in a full channel (ruling D86 (a)). In this label model a refused append and a waiting one look the same, and the Python store refuses an append only after a drop."
          "Close (AC4 and ruling D86 (d)): the seventh quoted sentence is lines 8 and 9, for a subscription that exists. A close made while a receive of the subscription is pending does nothing in Python (close() takes the receiver only when its lock is free; clash evt-c#8), so the pending receive keeps waiting; the lines require no receive pending, and the markdown records the case as not specified ('What a close or an overflow does to a receive that is already pending is not specified.'). Line 9 lets other labels, such as appends, come between the close and the receive. The end of the stream is reported the same way after a close, a drop and an overflow; telling them apart would be a runtime change, so no line does."
          "Drop: the eighth quoted sentence is lines 10 and 11. Line 10 says the stream can end at every later point where no receive of the subscription is pending (EVT_031_mutant_dropHangs, and EVT_031_mutant_dropPartialHangs after a receive that took part of the channel); line 11 says it does not end before the receives have taken what the channel held. For a subscription that ended before the drop, lines 5 and 6 (an overflow) or line 9 (a close) already say when its stream ends. After a drop the store takes no further append or subscribe, which the reference meets (refSub_dropped_no_op) and no line restates. The Python store provides no clear(); the model allows one and it changes no subscription."
          "Liveness is out of scope: no line says that a matching event is eventually received, only what a receive may hand over, that an end can be reached, and what is handed over before it. A store that allows no run at all meets every line; EVT_031_nonvacuous shows the premises of the lines are met by the witness. Configuration is kind N and not a line: Python's defaults (batch_size 64, batch_timeout_ms 10, channel_capacity 4096) and its rejection of a batch_size or channel_capacity of 0 with ValueError, which the model reflects by allowing no such subscribe. subscribe_stream is subscribe with batch size 1 and no list wrapper, so the same lines cover it. Subscriptions are numbered in the order they are made."
          "Status: the requirement is Proposed; Java, TypeScript and the Rust crate have not built it (UB-04). Ruling D47 (c) gives it a block now that D86 fixes the policy; the block binds every implementation that provides live subscriptions. The test derivation is EVT_031_nonvacuous: an event appended before the subscribe and a non-matching one are not delivered, the two matching ones come in one batch of size 2, and a close is followed by the end."
  signoff "2026-11-13 12a76a65a4411764 ai"
  statement : ∀ {E : Type}, SubSem E → Prop :=
    fun S =>
      (∀ tr tr', S (tr ++ tr') → ∀ i, received i tr <+ matchingAfter i tr) ∧
      (∀ tr, S tr → ∀ i b, b ∈ batches i tr →
        b ≠ [] ∧ ∃ f c n, subParams i tr = some (f, c, n) ∧ b.length ≤ n) ∧
      (∀ tr, S tr → ∀ i f c n, subParams i tr = some (f, c, n) → c.isSome = true) ∧
      (∀ pre e suf i f c n, S (pre ++ .op (.append e) :: suf) →
        subParams i pre = some (f, some c, n) → f e = true → c ≤ backlog i pre →
        received i (pre ++ .op (.append e) :: suf) <+ matchingAfter i pre) ∧
      (∀ pre e mid i f c n, S (pre ++ .op (.append e) :: mid) →
        subParams i pre = some (f, some c, n) → f e = true → c ≤ backlog i pre →
        pending i pre = false → pending i (pre ++ .op (.append e) :: mid) = false →
        ∃ bs, S (pre ++ .op (.append e) :: (mid ++ evt031Recvs i bs ++ [.await i, .finish i]))) ∧
      (∀ pre e mid i f c n, S (pre ++ .op (.append e) :: (mid ++ [.finish i])) →
        subParams i pre = some (f, some c, n) → f e = true → c ≤ backlog i pre →
        evt031Ended i pre = false → pending i pre = false → evt031NoClose i mid = true →
        received i mid = evt031Held i pre) ∧
      (∀ tr, S tr → dropped tr = false → ∀ e, S (tr ++ [.op (.append e)])) ∧
      (∀ pre suf i, S (pre ++ .close i :: suf) → (subParams i pre).isSome = true →
        pending i pre = false → received i suf = []) ∧
      (∀ pre mid i, S (pre ++ .close i :: mid) → (subParams i pre).isSome = true →
        pending i pre = false → evt031Quiet i mid = true →
        S (pre ++ .close i :: (mid ++ [.await i, .finish i]))) ∧
      (∀ pre mid i, S (pre ++ .drop :: mid) → (subParams i pre).isSome = true →
        pending i pre = false → pending i (pre ++ .drop :: mid) = false →
        ∃ bs, S (pre ++ .drop :: (mid ++ evt031Recvs i bs ++ [.await i, .finish i]))) ∧
      (∀ pre mid i, S (pre ++ .drop :: (mid ++ [.finish i])) → (subParams i pre).isSome = true →
        evt031Ended i pre = false → pending i pre = false → evt031NoClose i mid = true →
        received i mid = evt031Held i pre) ∧
      (∀ tr tr', S (tr ++ tr') → ∀ i, pending i tr = false →
        received i tr = (matchingAfter i tr).take (pulls i tr))

/- The pinned readable form of EVT-031: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_031 : {E : Type} → SubSem E → Prop :=
fun {E} S =>
  (∀ (tr tr' : List (SubLbl E)), S (tr ++ tr') → ∀ (i : Nat), received i tr <+ matchingAfter i tr) ∧
    (∀ (tr : List (SubLbl E)),
        S tr →
          ∀ (i : Nat) (b : List E),
            b ∈ batches i tr → b ≠ [] ∧ ∃ f c n, subParams i tr = some (f, c, n) ∧ b.length ≤ n) ∧
      (∀ (tr : List (SubLbl E)),
          S tr →
            ∀ (i : Nat) (f : E → Bool) (c : Option Nat) (n : Nat), subParams i tr = some (f, c, n) → c.isSome = true) ∧
        (∀ (pre : List (SubLbl E)) (e : E) (suf : List (SubLbl E)) (i : Nat) (f : E → Bool) (c n : Nat),
            S (pre ++ SubLbl.op (StoreOp.append e) :: suf) →
              subParams i pre = some (f, some c, n) →
                f e = true →
                  c ≤ backlog i pre → received i (pre ++ SubLbl.op (StoreOp.append e) :: suf) <+ matchingAfter i pre) ∧
          (∀ (pre : List (SubLbl E)) (e : E) (mid : List (SubLbl E)) (i : Nat) (f : E → Bool) (c n : Nat),
              S (pre ++ SubLbl.op (StoreOp.append e) :: mid) →
                subParams i pre = some (f, some c, n) →
                  f e = true →
                    c ≤ backlog i pre →
                      pending i pre = false →
                        pending i (pre ++ SubLbl.op (StoreOp.append e) :: mid) = false →
                          ∃ bs,
                            S
                              (pre ++
                                SubLbl.op (StoreOp.append e) ::
                                  (mid ++ evt031Recvs i bs ++ [SubLbl.await i, SubLbl.finish i]))) ∧
            (∀ (pre : List (SubLbl E)) (e : E) (mid : List (SubLbl E)) (i : Nat) (f : E → Bool) (c n : Nat),
                S (pre ++ SubLbl.op (StoreOp.append e) :: (mid ++ [SubLbl.finish i])) →
                  subParams i pre = some (f, some c, n) →
                    f e = true →
                      c ≤ backlog i pre →
                        evt031Ended i pre = false →
                          pending i pre = false → evt031NoClose i mid = true → received i mid = evt031Held i pre) ∧
              (∀ (tr : List (SubLbl E)),
                  S tr → dropped tr = false → ∀ (e : E), S (tr ++ [SubLbl.op (StoreOp.append e)])) ∧
                (∀ (pre suf : List (SubLbl E)) (i : Nat),
                    S (pre ++ SubLbl.close i :: suf) →
                      (subParams i pre).isSome = true → pending i pre = false → received i suf = []) ∧
                  (∀ (pre mid : List (SubLbl E)) (i : Nat),
                      S (pre ++ SubLbl.close i :: mid) →
                        (subParams i pre).isSome = true →
                          pending i pre = false →
                            evt031Quiet i mid = true →
                              S (pre ++ SubLbl.close i :: (mid ++ [SubLbl.await i, SubLbl.finish i]))) ∧
                    (∀ (pre mid : List (SubLbl E)) (i : Nat),
                        S (pre ++ SubLbl.drop :: mid) →
                          (subParams i pre).isSome = true →
                            pending i pre = false →
                              pending i (pre ++ SubLbl.drop :: mid) = false →
                                ∃ bs,
                                  S
                                    (pre ++
                                      SubLbl.drop :: (mid ++ evt031Recvs i bs ++ [SubLbl.await i, SubLbl.finish i]))) ∧
                      (∀ (pre mid : List (SubLbl E)) (i : Nat),
                          S (pre ++ SubLbl.drop :: (mid ++ [SubLbl.finish i])) →
                            (subParams i pre).isSome = true →
                              evt031Ended i pre = false →
                                pending i pre = false →
                                  evt031NoClose i mid = true → received i mid = evt031Held i pre) ∧
                        ∀ (tr tr' : List (SubLbl E)),
                          S (tr ++ tr') →
                            ∀ (i : Nat),
                              pending i tr = false → received i tr = List.take (pulls i tr) (matchingAfter i tr)
-/
#guard_msgs in #print EVT_031

/-! ### Observation lemmas -/

section Observations

variable {E : Type}

theorem evt031EndedFrom_snoc (i : Nat) (l : SubLbl E) :
    ∀ (tr p : List (SubLbl E)),
      evt031EndedFrom i p (tr ++ [l]) = (evt031EndedFrom i p tr || evt031Ends i (p ++ tr) l)
  | [], p => by simp [evt031EndedFrom]
  | x :: tr, p => by
    simp [evt031EndedFrom, evt031EndedFrom_snoc i l tr (p ++ [x]), Bool.or_assoc]

theorem evt031Ended_snoc (i : Nat) (tr : List (SubLbl E)) (l : SubLbl E) :
    evt031Ended i (tr ++ [l]) = (evt031Ended i tr || evt031Ends i tr l) := by
  simpa [evt031Ended] using evt031EndedFrom_snoc i l tr []

/-- A label that is not one of `i`'s own leaves whether a receive of `i` is pending as it was. -/
theorem evt031_lblPend_quiet {i : Nat} {l : SubLbl E} (h : evt031Own i l = false) (p : Bool) :
    lblPend i p l = p := by
  cases l <;> simp_all [evt031Own, lblPend]

theorem evt031_pending_quiet (i : Nat) (tr : List (SubLbl E)) :
    ∀ mid : List (SubLbl E), evt031Quiet i mid = true → pending i (tr ++ mid) = pending i tr
  | [], _ => by simp
  | l :: mid, h => by
    simp only [evt031Quiet, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    have ih := evt031_pending_quiet i (tr ++ [l]) mid h.2
    rw [List.append_assoc, List.singleton_append] at ih
    rw [ih, pending_snoc, evt031_lblPend_quiet h.1]

/-- A subscription receives nothing in labels none of which is its own. -/
theorem evt031_received_quiet (i : Nat) :
    ∀ mid : List (SubLbl E), evt031Quiet i mid = true → received i mid = []
  | [], _ => rfl
  | l :: mid, h => by
    simp only [evt031Quiet, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [received_cons, evt031_received_quiet i mid h.2]
    cases l <;> simp_all [evt031Own, lblBatch]

/-- What the receives `evt031Recvs i bs` hand to subscription `i`: the batches `bs`. -/
theorem evt031_received_recvs (i : Nat) :
    ∀ bs : List (List E), received i (evt031Recvs i bs) = bs.flatten
  | [] => rfl
  | b :: bs => by
    have hp : ∀ xs : List E, received i (xs.map fun _ => (SubLbl.pull i : SubLbl E)) = [] := by
      intro xs; induction xs with
      | nil => rfl
      | cons x xs ih => simpa [received_cons, lblBatch] using ih
    have := evt031_received_recvs i bs
    simp only [evt031Recvs, List.flatMap_cons] at this ⊢
    simp [received_append, received_cons, hp, this, lblBatch]

/-- The receives `evt031Recvs i bs` close nothing. -/
theorem evt031_noClose_recvs (i : Nat) (bs : List (List E)) :
    evt031NoClose i (evt031Recvs i bs) = true := by
  simp [evt031NoClose, evt031Recvs, evt031CloseOf]

/-- Labels none of which is `i`'s own close nothing of `i`. -/
theorem evt031_noClose_quiet {i : Nat} {mid : List (SubLbl E)} (h : evt031Quiet i mid = true) :
    evt031NoClose i mid = true := by
  simp only [evt031Quiet, evt031NoClose, List.all_eq_true] at h ⊢
  intro l hl
  have := h l hl
  cases l <;> simp_all [evt031Own, evt031CloseOf]

/-- The receives that take the events `es` one at a time, each returned as a batch of one. -/
def evt031Drain (i : Nat) (es : List E) : List (SubLbl E) :=
  es.flatMap fun e => [.await i, .pull i, .recv i [e]]

theorem evt031_recvs_single (i : Nat) :
    ∀ es : List E, evt031Recvs i (es.map fun e => [e]) = evt031Drain i es
  | [] => rfl
  | e :: es => by
    have := evt031_recvs_single i es
    simp only [evt031Recvs, evt031Drain, List.map_cons, List.flatMap_cons] at this ⊢
    rw [this]; rfl

end Observations

/-! ### The witness: the reference with a finite capacity on every subscribe -/

/-- Whether a label is a subscribe with a finite channel capacity, or no subscribe. -/
def evt031CapOk {E : Type} : SubLbl E → Bool
  | .subscribe _ _ c _ => c.isSome
  | _ => true

/-- **The Python store** ([EVT-031]): the reference store with live subscriptions, restricted to
the subscribe form of the Python binding, where every channel has a finite capacity. -/
def evt031PySub {E : Type} [DecidableEq E] : SubSem E :=
  fun tr => refSub tr ∧ tr.all evt031CapOk = true

#spec_witness evt031PySub

instance {E : Type} [DecidableEq E] (tr : List (SubLbl E)) : Decidable (evt031PySub tr) :=
  inferInstanceAs (Decidable (refSub tr ∧ tr.all evt031CapOk = true))

section Reference

variable {E : Type} [DecidableEq E]

omit [DecidableEq E] in
theorem evt031_capOk_params {i : Nat} :
    ∀ {tr : List (SubLbl E)}, tr.all evt031CapOk = true → ∀ {f c n},
      subParams i tr = some (f, c, n) → c.isSome = true
  | [], _, _, _, _, h => by simp [subParams] at h
  | l :: tr, ha, f, c, n, h => by
    simp only [List.all_cons, Bool.and_eq_true] at ha
    rw [subParams_cons] at h
    cases l with
    | subscribe j f' c' b' =>
      by_cases hj : j = i
      · simp only [lblParams, hj, if_true, Option.some_or, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -⟩ := h
        simpa [evt031CapOk] using ha.1
      · simp only [lblParams, hj, if_false, Option.none_or] at h
        exact evt031_capOk_params ha.2 h
    | _ => simp only [lblParams, Option.none_or] at h; exact evt031_capOk_params ha.2 h

omit [DecidableEq E] in
theorem evt031_capOk_recvs (i : Nat) (bs : List (List E)) :
    (evt031Recvs i bs).all evt031CapOk = true := by
  simp [evt031Recvs, evt031CapOk]

theorem refSub_prefix {tr tr' : List (SubLbl E)} (h : refSub (tr ++ tr')) : refSub tr := by
  unfold refSub subSem at h ⊢
  rw [run_append] at h
  cases hr : run {} SubSt.init tr with
  | none => simp [hr] at h
  | some s => rfl

omit [DecidableEq E] in
/-- A step on subscription `i` through `modSub`, when `g` allows it. -/
theorem evt031_modSub {s : SubSt E} {i : Nat} {u u' : Reference.Sub E}
    {g : Reference.Sub E → Option (Reference.Sub E)}
    (hu : s.subs i = some u) (hg : g u = some u') :
    modSub s i g = some { s with subs := updSub s.subs i u' } := by
  simp only [modSub, hu, hg, Option.map_some]

/-- One reference step by a label that is not one of `i`'s own, on a subscription that is
unregistered or whose receiver is closed: its channel and receiver stay, and it stays so. -/
theorem evt031_step_other {s s1 : SubSt E} {l : SubLbl E} {i : Nat} {u : Reference.Sub E}
    (h : step {} s l = some s1) (hu : s.subs i = some u) (hl : evt031Own i l = false)
    (hend : u.linked = false ∨ u.rx = false) :
    ∃ u1, s1.subs i = some u1 ∧ u1.chan = u.chan ∧ u1.rx = u.rx ∧
      (u1.linked = false ∨ u1.rx = false) := by
  have other : ∀ j g, j ≠ i → modSub s j g = some s1 →
      ∃ u1, s1.subs i = some u1 ∧ u1.chan = u.chan ∧ u1.rx = u.rx ∧
        (u1.linked = false ∨ u1.rx = false) := by
    intro j g hji hm
    exact ⟨u, by rw [modSub_other hm hji, hu], rfl, rfl, hend⟩
  cases l with
  | op o =>
    simp only [step] at h
    split at h
    · cases h
    · cases o with
      | clear => simp at h; subst h; exact ⟨u, hu, rfl, rfl, hend⟩
      | append e =>
        simp [blocks] at h; subst h
        refine ⟨deliver {} e u, by simp [hu], ?_⟩
        clear other
        unfold deliver Sub.takes
        rcases hend with h' | h' <;> by_cases hf : u.filt e = true <;>
          by_cases hlk : u.linked = true <;> simp_all
  | subscribe j f c b =>
    have hji : j ≠ i := by simpa [evt031Own] using hl
    simp only [step] at h
    split at h
    · simp at h; subst h
      exact ⟨u, by simp [updSub_ne _ _ hji, hu], rfl, rfl, hend⟩
    · cases h
  | await j => exact other _ _ (by simpa [evt031Own] using hl) h
  | pull j => exact other _ _ (by simpa [evt031Own] using hl) h
  | recv j b => exact other _ _ (by simpa [evt031Own] using hl) h
  | finish j => exact other _ _ (by simpa [evt031Own] using hl) h
  | close j => exact other _ _ (by simpa [evt031Own] using hl) h
  | drop =>
    simp only [step] at h
    split at h
    · simp at h; subst h
      exact ⟨{ u with linked := false }, by simp [hu], rfl, rfl, Or.inl rfl⟩
    · cases h

/-- Labels none of which is `i`'s own leave an unregistered or closed subscription's channel and
receiver as they were. -/
theorem evt031_run_other {i : Nat} :
    ∀ {mid : List (SubLbl E)} {s s' : SubSt E} {u : Reference.Sub E},
      run {} s mid = some s' → s.subs i = some u → evt031Quiet i mid = true →
      (u.linked = false ∨ u.rx = false) →
      ∃ u', s'.subs i = some u' ∧ u'.chan = u.chan ∧ u'.rx = u.rx ∧
        (u'.linked = false ∨ u'.rx = false)
  | [], s, s', u, h, hu, _, hend => by
    simp [run] at h; subst h; exact ⟨u, hu, rfl, rfl, hend⟩
  | l :: mid, s, s', u, h, hu, hq, hend => by
    simp only [evt031Quiet, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hq
    simp only [run] at h
    cases h1 : step {} s l with
    | none => simp [h1] at h
    | some s1 =>
      simp only [h1, Option.bind_some] at h
      obtain ⟨u1, hu1, hc1, hr1, hend1⟩ := evt031_step_other h1 hu hq.1 hend
      obtain ⟨u', hu', hc', hr', hend'⟩ := evt031_run_other h hu1 hq.2 hend1
      exact ⟨u', hu', hc'.trans hc1, hr'.trans hr1, hend'⟩

/-- One reference step by a label that is no close of `i`, on a subscription that is unregistered
with its receiver open: it stays so, and what the step returns to it together with what it still
holds is exactly what it held. -/
theorem evt031_step_keep {s s1 : SubSt E} {l : SubLbl E} {i : Nat} {u : Reference.Sub E}
    (hF : Fresh s) (h : step {} s l = some s1) (hu : s.subs i = some u)
    (hl : evt031CloseOf i l = false) (hlk : u.linked = false) (hrx : u.rx = true) :
    ∃ u1, s1.subs i = some u1 ∧ u1.linked = false ∧ u1.rx = true ∧
      (lblBatch i l).getD [] ++ u1.cur ++ u1.chan = u.cur ++ u.chan := by
  have other : ∀ j g, j ≠ i → modSub s j g = some s1 → lblBatch i l = none →
      ∃ u1, s1.subs i = some u1 ∧ u1.linked = false ∧ u1.rx = true ∧
        (lblBatch i l).getD [] ++ u1.cur ++ u1.chan = u.cur ++ u.chan := by
    intro j g hji hm hb
    exact ⟨u, by rw [modSub_other hm hji, hu], hlk, hrx, by simp [hb]⟩
  cases l with
  | op o =>
    simp only [step] at h
    split at h
    · cases h
    · cases o with
      | clear => simp at h; subst h; exact ⟨u, hu, hlk, hrx, by simp [lblBatch]⟩
      | append e =>
        simp [blocks] at h; subst h
        have hd : deliver {} e u = u := by simp [deliver, Sub.takes, hlk]
        exact ⟨u, by simp [hu, hd], hlk, hrx, by simp [lblBatch]⟩
  | subscribe j f c b =>
    simp only [step] at h
    split at h
    · rename_i hc
      simp at hc
      obtain ⟨⟨⟨-, rfl⟩, -⟩, -⟩ := hc
      simp at h; subst h
      have hji : s.n ≠ i := by
        rintro rfl; rw [hF _ (Nat.le_refl _)] at hu; cases hu
      exact ⟨u, by simp [updSub_ne _ _ hji, hu], hlk, hrx, by simp [lblBatch]⟩
    · cases h
  | await j =>
    by_cases hji : j = i
    · subst hji
      obtain ⟨u', hg, hs⟩ := modSub_self h hu
      have : u' = { u with pending := true } := by
        cases hp : u.pending <;> simp_all
      subst this
      exact ⟨_, hs, hlk, hrx, by simp [lblBatch]⟩
    · exact other _ _ hji h (by simp [lblBatch])
  | pull j =>
    by_cases hji : j = i
    · subst hji
      obtain ⟨u', hg, hs⟩ := modSub_self h hu
      split at hg
      · split at hg
        · cases hg
        · rename_i e r hch
          simp at hg; subst hg
          exact ⟨_, hs, hlk, hrx, by simp [lblBatch, hch]⟩
      · cases hg
    · exact other _ _ hji h (by simp [lblBatch])
  | recv j b =>
    by_cases hji : j = i
    · subst hji
      obtain ⟨u', hg, hs⟩ := modSub_self h hu
      split at hg
      · rename_i hc
        simp at hc
        obtain ⟨-, rfl⟩ := hc
        simp at hg; subst hg
        exact ⟨_, hs, hlk, hrx, by simp [lblBatch]⟩
      · cases hg
    · exact other _ _ hji h (by simp [lblBatch, hji])
  | finish j =>
    by_cases hji : j = i
    · subst hji
      obtain ⟨u', hg, hs⟩ := modSub_self h hu
      split at hg
      · simp at hg; subst hg
        exact ⟨_, hs, hlk, hrx, by simp [lblBatch]⟩
      · cases hg
    · exact other _ _ hji h (by simp [lblBatch])
  | close j =>
    have hji : j ≠ i := by simpa [evt031CloseOf] using hl
    exact other _ _ hji h (by simp [lblBatch])
  | drop =>
    simp only [step] at h
    split at h
    · simp at h; subst h
      exact ⟨{ u with linked := false }, by simp [hu], rfl, hrx, by simp [lblBatch]⟩
    · cases h

/-- Labels that close nothing of `i` keep an unregistered subscription with an open receiver so,
and what they return to it together with what it still holds is exactly what it held. -/
theorem evt031_run_keep {i : Nat} :
    ∀ {mid tr : List (SubLbl E)} {s s' : SubSt E} {u : Reference.Sub E},
      Inv tr s → run {} s mid = some s' → s.subs i = some u → evt031NoClose i mid = true →
      u.linked = false → u.rx = true →
      ∃ u', s'.subs i = some u' ∧ u'.linked = false ∧ u'.rx = true ∧
        received i mid ++ u'.cur ++ u'.chan = u.cur ++ u.chan
  | [], tr, s, s', u, _, h, hu, _, hlk, hrx => by
    simp [run] at h; subst h; exact ⟨u, hu, hlk, hrx, by simp [received, batches]⟩
  | l :: mid, tr, s, s', u, hI, h, hu, hn, hlk, hrx => by
    simp only [evt031NoClose, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hn
    simp only [run] at h
    cases h1 : step {} s l with
    | none => simp [h1] at h
    | some s1 =>
      simp only [h1, Option.bind_some] at h
      obtain ⟨u1, hu1, hlk1, hrx1, he1⟩ := evt031_step_keep hI.fresh h1 hu hn.1 hlk hrx
      obtain ⟨u', hu', hlk', hrx', he'⟩ := evt031_run_keep (inv_step hI h1) h hu1 hn.2 hlk1 hrx1
      refine ⟨u', hu', hlk', hrx', ?_⟩
      rw [received_cons, ← he1]
      simp only [List.append_assoc] at he' ⊢
      rw [he']

/-- Labels after a subscription is unregistered or its receiver closed leave it so, whatever they
are. -/
theorem evt031_frame_run {i : Nat} :
    ∀ {mid tr : List (SubLbl E)} {s s' : SubSt E} {u : Reference.Sub E},
      Inv tr s → run {} s mid = some s' → s.subs i = some u →
      (u.linked = false ∨ u.rx = false) →
      ∃ u', s'.subs i = some u' ∧ (u'.linked = false ∨ u'.rx = false)
  | [], _, s, s', u, _, h, hu, hend => by
    simp [run] at h; subst h; exact ⟨u, hu, hend⟩
  | l :: mid, _, s, s', u, hI, h, hu, hend => by
    simp only [run] at h
    cases h1 : step {} s l with
    | none => simp [h1] at h
    | some s1 =>
      simp only [h1, Option.bind_some] at h
      obtain ⟨u1, hu1, hend1, -⟩ := frame_step hI h1 hu hend
      exact evt031_frame_run (inv_step hI h1) h hu1 hend1

/-- After a reference run, an unregistered subscription with an open receiver and no batch under
way, whose next labels close nothing of it and end with a receive reporting the end, received in
those labels exactly what its channel held. -/
theorem evt031_keep_end {tr mid : List (SubLbl E)} {s s' : SubSt E} {i : Nat}
    {u : Reference.Sub E} (hI : Inv tr s) (h : run {} s (mid ++ [.finish i]) = some s')
    (hu : s.subs i = some u) (hn : evt031NoClose i mid = true) (hlk : u.linked = false)
    (hrx : u.rx = true) (hcur : u.cur = []) : received i mid = u.chan := by
  rw [run_append] at h
  cases h2 : run {} s mid with
  | none => simp [h2] at h
  | some s2 =>
    simp only [h2, Option.bind_some, run] at h
    cases h3 : step {} s2 (.finish i) with
    | none => simp [h3] at h
    | some s3 =>
      obtain ⟨u2, hu2, -, hrx2, he⟩ := evt031_run_keep hI h2 hu hn hlk hrx
      obtain ⟨u3, hg, -⟩ := modSub_self h3 hu2
      split at hg
      · rename_i hc
        have h0 : u2.cur = [] ∧ u2.chan = [] := by
          revert hc; cases u2.cur <;> cases u2.chan <;> simp [hrx2]
        rw [h0.1, h0.2, hcur] at he
        simpa using he
      · cases hg

/-- One reference step on a subscription that is registered with an open receiver keeps it so,
unless the label ends it (`evt031Ends`). -/
theorem evt031_live_step {tr : List (SubLbl E)} {s s1 : SubSt E} {l : SubLbl E} {i : Nat}
    {u1 : Reference.Sub E} (hI : Inv tr s) (h : step {} s l = some s1)
    (hu1 : s1.subs i = some u1) (hE : evt031Ends i tr l = false)
    (hlive : ∀ u, s.subs i = some u → u.linked = true ∧ u.rx = true) :
    u1.linked = true ∧ u1.rx = true := by
  have own : ∀ j (g : Reference.Sub E → Option (Reference.Sub E)), modSub s j g = some s1 →
      (∀ u u', j = i → s.subs i = some u → g u = some u' → u'.linked = true ∧ u'.rx = true) →
      u1.linked = true ∧ u1.rx = true := by
    intro j g hm hg
    obtain ⟨u, u', hu, hgu, rfl⟩ := modSub_eq_some hm
    by_cases hji : j = i
    · subst hji
      simp [updSub_self] at hu1; subst hu1
      exact hg u u' rfl hu hgu
    · simp only [updSub_ne _ _ hji] at hu1; exact hlive u1 hu1
  cases l with
  | op o =>
    simp only [step] at h
    split at h
    · cases h
    · cases o with
      | clear => simp at h; subst h; exact hlive u1 hu1
      | append e =>
        simp [blocks] at h; subst h
        simp only [Option.map_eq_some_iff] at hu1
        obtain ⟨u, hu, rfl⟩ := hu1
        obtain ⟨hl, hr⟩ := hlive u hu
        have hJ := hI.some_ i u hu
        by_cases hf : u.filt e = true
        · cases hroom : u.room
          · exfalso
            cases hcap : u.cap with
            | none => simp [Sub.room, hcap] at hroom
            | some c =>
              simp only [Sub.room, hcap, decide_eq_false_iff_not, Nat.not_lt] at hroom
              have heq := hJ.eq hl hr
              have hpl := hJ.pulled
              have hlen := congrArg List.length heq
              simp only [List.length_append] at hlen hpl
              have hb : c ≤ backlog i tr := by
                simp only [backlog, matchingAfter, hJ.params]
                rw [← hlen, ← hpl]; omega
              simp [evt031Ends, hJ.params, hcap, hf, hb] at hE
          · simp [deliver, Sub.takes, hl, hr, hf, hroom]
        · have : deliver {} e u = u := by simp [deliver, Sub.takes, hf]
          rw [this]; exact ⟨hl, hr⟩
  | subscribe j f c b =>
    simp only [step] at h
    split at h
    · simp at h; subst h
      by_cases hji : j = i
      · subst hji; simp [updSub_self] at hu1; subst hu1; simp
      · simp only [updSub_ne _ _ hji] at hu1; exact hlive u1 hu1
    · cases h
  | await j =>
    refine own j _ h fun u u' _ hu hg => ?_
    obtain ⟨hl, hr⟩ := hlive u hu
    cases hp : u.pending <;> simp [hp] at hg
    subst hg; exact ⟨hl, hr⟩
  | pull j =>
    refine own j _ h fun u u' _ hu hg => ?_
    obtain ⟨hl, hr⟩ := hlive u hu
    split at hg
    · split at hg
      · cases hg
      · simp at hg; subst hg; exact ⟨hl, hr⟩
    · cases hg
  | recv j b =>
    refine own j _ h fun u u' _ hu hg => ?_
    obtain ⟨hl, hr⟩ := hlive u hu
    split at hg
    · simp at hg; subst hg; exact ⟨hl, hr⟩
    · cases hg
  | finish j =>
    refine own j _ h fun u u' _ hu hg => ?_
    obtain ⟨hl, hr⟩ := hlive u hu
    split at hg
    · simp at hg; subst hg; exact ⟨hl, hr⟩
    · cases hg
  | close j =>
    refine own j _ h fun u u' hji hu hg => ?_
    subst hji
    obtain ⟨hl, hr⟩ := hlive u hu
    cases hp : u.pending
    · have hpe : pending j tr = false := (hI.some_ j u hu).pend.symm.trans hp
      simp [evt031Ends, hpe] at hE
    · simp [hp] at hg; subst hg; exact ⟨hl, hr⟩
  | drop => simp [evt031Ends] at hE

/-- A subscription that was not ended (`evt031Ended`) in a reference run is still registered
with an open receiver. -/
theorem evt031_live {i : Nat} (pre : List (SubLbl E)) :
    ∀ {s : SubSt E}, run {} SubSt.init pre = some s → evt031Ended i pre = false →
      ∀ u, s.subs i = some u → u.linked = true ∧ u.rx = true := by
  obtain ⟨r, rfl⟩ : ∃ r, pre = r.reverse := ⟨pre.reverse, by simp⟩
  induction r with
  | nil => intro s h _ u hu; simp [run] at h; subst h; simp [SubSt.init] at hu
  | cons l r ih =>
    intro s h hE u hu
    rw [List.reverse_cons] at h hE
    generalize r.reverse = pre at h hE ih
    rw [evt031Ended_snoc, Bool.or_eq_false_iff] at hE
    rw [run_snoc] at h
    cases h0 : run {} SubSt.init pre with
    | none => simp [h0] at h
    | some s0 =>
      simp only [h0, Option.bind_some] at h
      exact evt031_live_step (inv_run h0) h hu hE.2 (ih h0 hE.1)

omit [DecidableEq E] in
/-- While a subscription is registered with an open receiver and no receive of it is pending,
its channel holds exactly `evt031Held`. -/
theorem evt031_held {tr : List (SubLbl E)} {i : Nat} {u : Reference.Sub E} (hJ : InvAt tr i u)
    (hl : u.linked = true) (hr : u.rx = true) (hp : pending i tr = false) :
    u.chan = evt031Held i tr := by
  have hcur : u.cur = [] := hJ.idle (hJ.pend.trans hp)
  have heq := hJ.eq hl hr
  have hpl := hJ.pulled
  rw [hcur, List.append_nil] at heq hpl
  simp only [evt031Held, matchingAfter, hJ.params, ← heq, ← hpl, List.drop_left]

omit [DecidableEq E] in
/-- An append of a matching event that finds the channel of `i` full leaves `i` unregistered,
with its channel as it was. -/
theorem evt031_overflow_deliver {tr : List (SubLbl E)} {i : Nat} {u : Reference.Sub E} {e : E}
    {f : E → Bool} {c n : Nat} (hJ : InvAt tr i u) (hpar : subParams i tr = some (f, some c, n))
    (hf : f e = true) (hc : c ≤ backlog i tr) :
    deliver {} e u = { u with linked := false } ∨ (deliver {} e u = u ∧ u.linked = false) := by
  rw [hJ.params] at hpar
  simp only [Option.some.injEq, Prod.mk.injEq] at hpar
  obtain ⟨rfl, hcap, rfl⟩ := hpar
  rcases deliver_cases e u with ⟨-, hl, -, hr, hroom⟩ | hd | ⟨hd, hn⟩
  · exfalso
    have heq := hJ.eq hl hr
    have hpl := hJ.pulled
    have hlen := congrArg List.length heq
    simp only [List.length_append] at hlen hpl
    simp only [backlog, matchingAfter, hJ.params] at hc
    simp only [Sub.room, hcap, decide_eq_true_eq] at hroom
    omega
  · exact Or.inl hd
  · refine Or.inr ⟨hd, ?_⟩
    cases hl : u.linked
    · rfl
    · have := hn hl; rw [hf] at this; cases this

/-- The drain in the reference: a subscription with no receive pending that is no longer
registered, or whose receiver is closed, can hand over its channel one event at a time and then
report the end. -/
theorem evt031_drain_run {i : Nat} (es : List E) :
    ∀ (s : SubSt E) (u : Reference.Sub E), s.subs i = some u → u.chan = es → u.pending = false →
      u.cur = [] → 0 < u.bsz → (u.linked = false ∨ u.rx = false) →
      (u.rx = false → u.chan = []) →
      (run {} s (evt031Drain i es ++ [.await i, .finish i])).isSome = true := by
  induction es with
  | nil =>
    intro s u hu hc hp hcur _ hend _
    let u1 : Reference.Sub E := { u with pending := true }
    let u2 : Reference.Sub E := { u1 with pending := false }
    let s1 : SubSt E := { s with subs := updSub s.subs i u1 }
    let s2 : SubSt E := { s1 with subs := updSub s1.subs i u2 }
    have h1 : step {} s (.await i) = some s1 := evt031_modSub hu (by simp [hp, u1])
    have h2 : step {} s1 (.finish i) = some s2 := by
      refine evt031_modSub (updSub_self _ _ _) ?_
      rcases hend with hl | hl <;> simp [u1, u2, hcur, hc, hl]
    simp [evt031Drain, run, h1, h2]
  | cons e es ih =>
    intro s u hu hc hp hcur hb hend hcl
    have hrx : u.rx = true := by
      cases h : u.rx
      · have := hcl h; rw [hc] at this; cases this
      · rfl
    have hl : u.linked = false := hend.resolve_right (by simp [hrx])
    let u1 : Reference.Sub E := { u with pending := true }
    let u2 : Reference.Sub E := { u1 with chan := es, cur := u1.cur ++ [e] }
    let u3 : Reference.Sub E := { u2 with cur := [], pending := false }
    let s1 : SubSt E := { s with subs := updSub s.subs i u1 }
    let s2 : SubSt E := { s1 with subs := updSub s1.subs i u2 }
    let s3 : SubSt E := { s2 with subs := updSub s2.subs i u3 }
    have h1 : step {} s (.await i) = some s1 := evt031_modSub hu (by simp [hp, u1])
    have h2 : step {} s1 (.pull i) = some s2 := by
      refine evt031_modSub (updSub_self _ _ _) ?_
      simp [u1, u2, hrx, hcur, hb, hc]
    have h3 : step {} s2 (.recv i [e]) = some s3 := by
      refine evt031_modSub (updSub_self _ _ _) ?_
      simp [u1, u2, u3, hcur]
    have hrun : run {} s (evt031Drain i (e :: es) ++ [.await i, .finish i]) =
        run {} s3 (evt031Drain i es ++ [.await i, .finish i]) := by
      simp [evt031Drain, run, h1, h2, h3]
    rw [hrun]
    exact ih s3 u3 (updSub_self _ _ _) rfl rfl rfl hb (Or.inl hl) (by simp [u3, u2, u1, hrx])

/-- The end in the reference: after a reference run, a subscription with no receive pending that
is no longer registered, or whose receiver is closed, can hand over its channel and then report
the end. -/
theorem evt031_ref_end {tr : List (SubLbl E)} {s : SubSt E} {i : Nat} {u : Reference.Sub E}
    (hs : run {} SubSt.init tr = some s) (hu : s.subs i = some u)
    (hp : pending i tr = false) (hend : u.linked = false ∨ u.rx = false) :
    refSub (tr ++ (evt031Drain i u.chan ++ [.await i, .finish i])) := by
  have hJ := (inv_run hs).some_ i u hu
  have hpu : u.pending = false := hJ.pend.trans hp
  unfold refSub subSem
  rw [run_append, hs, Option.bind_some]
  exact evt031_drain_run u.chan s u hu rfl hpu (hJ.idle hpu) hJ.bsz_pos hend hJ.closed

/-- After a label `l` that leaves subscription `i` unregistered or closed, and any labels after
which no receive of `i` is pending, the receives of `i` can hand over its channel and then report
the end. -/
theorem evt031_ref_end_after {pre mid : List (SubLbl E)} {l : SubLbl E} {s1 s' : SubSt E}
    {i : Nat} {u1 : Reference.Sub E}
    (hs1 : run {} SubSt.init (pre ++ [l]) = some s1) (hrun : run {} s1 mid = some s')
    (hu1 : s1.subs i = some u1) (hend : u1.linked = false ∨ u1.rx = false)
    (hp : pending i (pre ++ l :: mid) = false) :
    ∃ bs, refSub (pre ++ l :: (mid ++ evt031Recvs i bs ++ [.await i, .finish i])) := by
  obtain ⟨u', hu', hend'⟩ := evt031_frame_run (inv_run hs1) hrun hu1 hend
  have hs' : run {} SubSt.init ((pre ++ [l]) ++ mid) = some s' := by
    rw [run_append, hs1, Option.bind_some]; exact hrun
  have hp' : pending i ((pre ++ [l]) ++ mid) = false := by
    simpa [List.append_assoc] using hp
  refine ⟨u'.chan.map fun e => [e], ?_⟩
  have := evt031_ref_end hs' hu' hp' hend'
  rw [evt031_recvs_single]
  simpa [List.append_assoc] using this

/-- Line 5 on the reference: after an append that finds the channel of `i` full, and labels after
which no receive of `i` is pending, the receives of `i` can drain its channel and report the
end. -/
theorem evt031_ref_overflow_end {pre mid : List (SubLbl E)} {i : Nat} {e : E} {f : E → Bool}
    {c n : Nat} (h : refSub (pre ++ .op (.append e) :: mid))
    (hpar : subParams i pre = some (f, some c, n)) (hf : f e = true) (hc : c ≤ backlog i pre)
    (hpm : pending i (pre ++ .op (.append e) :: mid) = false) :
    ∃ bs, refSub (pre ++ .op (.append e) :: (mid ++ evt031Recvs i bs ++ [.await i, .finish i])) := by
  obtain ⟨s, s1, s', hs, hI, h1, hrun⟩ := refSub_split h
  cases hs0 : s.subs i with
  | none => have := (hI.none_ i hs0).1; rw [this] at hpar; cases hpar
  | some u =>
    have hJ := hI.some_ i u hs0
    have hs1 : s1.subs i = some (deliver {} e u) := by
      have h1' := h1
      simp [step, blocks] at h1'
      obtain ⟨-, rfl⟩ := h1'
      simp [hs0]
    have hend : (deliver {} e u).linked = false ∨ (deliver {} e u).rx = false := by
      rcases evt031_overflow_deliver hJ hpar hf hc with hd | ⟨hd, hl⟩
      · rw [hd]; simp
      · rw [hd]; simp [hl]
    have hrun1 : run {} SubSt.init (pre ++ [.op (.append e)]) = some s1 := by
      rw [run_snoc, hs, Option.bind_some]; exact h1
    exact evt031_ref_end_after hrun1 hrun hs1 hend hpm

/-- Line 6 on the reference: after an append that finds the channel of a subscription `i` that
was not ended full, with no receive of `i` pending, a receive of `i` reports the end only once
`i` received, since that append, exactly what its channel held. -/
theorem evt031_ref_overflow_drain {pre mid : List (SubLbl E)} {i : Nat} {e : E} {f : E → Bool}
    {c n : Nat} (h : refSub (pre ++ .op (.append e) :: (mid ++ [.finish i])))
    (hpar : subParams i pre = some (f, some c, n)) (hf : f e = true) (hc : c ≤ backlog i pre)
    (hE : evt031Ended i pre = false) (hp : pending i pre = false)
    (hn : evt031NoClose i mid = true) : received i mid = evt031Held i pre := by
  obtain ⟨s, s1, s', hs, hI, h1, hrun⟩ := refSub_split h
  cases hs0 : s.subs i with
  | none => have := (hI.none_ i hs0).1; rw [this] at hpar; cases hpar
  | some u =>
    have hJ := hI.some_ i u hs0
    obtain ⟨hl, hr⟩ := evt031_live pre hs hE u hs0
    have hheld := evt031_held hJ hl hr hp
    have hd : deliver {} e u = { u with linked := false } := by
      rcases evt031_overflow_deliver hJ hpar hf hc with hd | ⟨-, hl'⟩
      · exact hd
      · rw [hl] at hl'; cases hl'
    have hs1 : s1.subs i = some { u with linked := false } := by
      have h1' := h1
      simp [step, blocks] at h1'
      obtain ⟨-, rfl⟩ := h1'
      simp [hs0, hd]
    have := evt031_keep_end (inv_step hI h1) hrun hs1 hn rfl hr (hJ.idle (hJ.pend.trans hp))
    rw [this]; exact hheld

/-- Line 9 on the reference: after a close of `i` made with no receive of `i` pending, and labels
none of which is `i`'s own, a receive of `i` reports the end. -/
theorem evt031_ref_close_end {pre mid : List (SubLbl E)} {i : Nat}
    (h : refSub (pre ++ .close i :: mid)) (hp : pending i pre = false)
    (hq : evt031Quiet i mid = true) : refSub (pre ++ .close i :: (mid ++ [.await i, .finish i])) := by
  obtain ⟨s, s1, s', hs, hI, h1, hrun⟩ := refSub_split h
  obtain ⟨u, u', hu, hg, hs1⟩ := modSub_eq_some h1
  have hJ := hI.some_ i u hu
  have hpu : u.pending = false := hJ.pend.trans hp
  simp [hpu] at hg; subst hg
  have hu1 : s1.subs i = some { u with rx := false, chan := [] } := by
    rw [hs1]; simp [updSub_self, hpu]
  have hrun1 : run {} SubSt.init (pre ++ [.close i]) = some s1 := by
    rw [run_snoc, hs, Option.bind_some]; exact h1
  have hp1 : pending i (pre ++ [.close i]) = false := by
    rw [pending_snoc]; simpa [lblPend] using hp
  obtain ⟨u2, hu2, hc2, hr2, -⟩ := evt031_run_other hrun hu1 hq (Or.inr rfl)
  have hs' : run {} SubSt.init ((pre ++ [.close i]) ++ mid) = some s' := by
    rw [run_append, hrun1, Option.bind_some]; exact hrun
  have hp' : pending i ((pre ++ [.close i]) ++ mid) = false := by
    rw [evt031_pending_quiet i _ mid hq]; exact hp1
  have := evt031_ref_end hs' hu2 hp' (Or.inr hr2)
  rw [hc2] at this
  simpa [evt031Drain, List.append_assoc] using this

/-- Line 10 on the reference: after the store is dropped, a subscription made before can, after
labels after which no receive of it is pending, drain its channel and report the end. -/
theorem evt031_ref_drop_end {pre mid : List (SubLbl E)} {i : Nat} (h : refSub (pre ++ .drop :: mid))
    (hi : (subParams i pre).isSome = true) (hpm : pending i (pre ++ .drop :: mid) = false) :
    ∃ bs, refSub (pre ++ .drop :: (mid ++ evt031Recvs i bs ++ [.await i, .finish i])) := by
  obtain ⟨s, s1, s', hs, hI, h1, hrun⟩ := refSub_split h
  cases hu : s.subs i with
  | none => have := (hI.none_ i hu).1; rw [this] at hi; cases hi
  | some u =>
    have hu1 : s1.subs i = some { u with linked := false } := by
      simp only [step] at h1
      split at h1
      · simp at h1; subst h1; simp [hu]
      · cases h1
    have hrun1 : run {} SubSt.init (pre ++ [.drop]) = some s1 := by
      rw [run_snoc, hs, Option.bind_some]; exact h1
    exact evt031_ref_end_after hrun1 hrun hu1 (Or.inl rfl) hpm

/-- Line 11 on the reference: after the store is dropped, a subscription that was not ended, with
no receive pending, reports the end only once it received exactly what its channel held. -/
theorem evt031_ref_drop_drain {pre mid : List (SubLbl E)} {i : Nat}
    (h : refSub (pre ++ .drop :: (mid ++ [.finish i]))) (hi : (subParams i pre).isSome = true)
    (hE : evt031Ended i pre = false) (hp : pending i pre = false)
    (hn : evt031NoClose i mid = true) : received i mid = evt031Held i pre := by
  obtain ⟨s, s1, s', hs, hI, h1, hrun⟩ := refSub_split h
  cases hs0 : s.subs i with
  | none => have := (hI.none_ i hs0).1; rw [this] at hi; cases hi
  | some u =>
    have hJ := hI.some_ i u hs0
    obtain ⟨hl, hr⟩ := evt031_live pre hs hE u hs0
    have hs1 : s1.subs i = some { u with linked := false } := by
      simp only [step] at h1
      split at h1
      · simp at h1; subst h1; simp [hs0]
      · cases h1
    have := evt031_keep_end (inv_step hI h1) hrun hs1 hn rfl hr (hJ.idle (hJ.pend.trans hp))
    have hh := evt031_held hJ hl hr hp
    rw [this]; exact hh

/-- In the state `s` after the labels `tr`, what each subscription received, its batch under way
and its channel are a prefix of the matching events appended since it subscribed: nothing is lost
before what the channel still holds. -/
def evt031Pref (tr : List (SubLbl E)) (s : SubSt E) : Prop :=
  ∀ i u, s.subs i = some u →
    received i tr ++ u.cur ++ u.chan <+: (appendsAfter i tr).filter u.filt

omit [DecidableEq E] in
/-- A step that keeps the filter of `i`, and after which what it returns to `i` and what `i` still
holds are a prefix of what `i` held, keeps the prefix of `evt031Pref`. -/
theorem evt031_pref_keep {tr : List (SubLbl E)} {i : Nat} {l : SubLbl E}
    {u u1 : Reference.Sub E} (hJ : InvAt tr i u)
    (hP : received i tr ++ u.cur ++ u.chan <+: (appendsAfter i tr).filter u.filt)
    (hf : u1.filt = u.filt)
    (hl : (lblBatch i l).getD [] ++ u1.cur ++ u1.chan <+: u.cur ++ u.chan) :
    received i (tr ++ [l]) ++ u1.cur ++ u1.chan <+:
      (appendsAfter i (tr ++ [l])).filter u1.filt := by
  rw [received_snoc, appendsAfter_snoc, hJ.params, hf]
  simp only [Option.isSome_some, if_true, List.filter_append]
  have h1 : received i tr ++ ((lblBatch i l).getD [] ++ u1.cur ++ u1.chan) <+:
      received i tr ++ (u.cur ++ u.chan) := (List.prefix_append_right_inj _).mpr hl
  simp only [List.append_assoc] at h1 hP ⊢
  exact h1.trans (hP.trans (List.prefix_append _ _))

/-- One reference step keeps `evt031Pref`. -/
theorem evt031_pref_step {tr : List (SubLbl E)} {s s1 : SubSt E} {l : SubLbl E}
    (hI : Inv tr s) (hP : evt031Pref tr s) (h : step {} s l = some s1) :
    evt031Pref (tr ++ [l]) s1 := by
  intro i u1 hu1
  have keep : ∀ u, s.subs i = some u → u1.filt = u.filt →
      (lblBatch i l).getD [] ++ u1.cur ++ u1.chan <+: u.cur ++ u.chan →
      received i (tr ++ [l]) ++ u1.cur ++ u1.chan <+:
        (appendsAfter i (tr ++ [l])).filter u1.filt :=
    fun u hu hf hl => evt031_pref_keep (hI.some_ i u hu) (hP i u hu) hf hl
  have own : ∀ j (g : Reference.Sub E → Option (Reference.Sub E)), modSub s j g = some s1 →
      (j ≠ i → lblBatch i l = none) →
      (j = i → ∀ u, g u = some u1 → u1.filt = u.filt ∧
        (lblBatch i l).getD [] ++ u1.cur ++ u1.chan <+: u.cur ++ u.chan) →
      received i (tr ++ [l]) ++ u1.cur ++ u1.chan <+:
        (appendsAfter i (tr ++ [l])).filter u1.filt := by
    intro j g hm hb hg
    obtain ⟨u, u', hu, hgu, rfl⟩ := modSub_eq_some hm
    by_cases hji : j = i
    · subst hji
      simp only [updSub_self, Option.some.injEq] at hu1; subst hu1
      obtain ⟨hf, hl⟩ := hg rfl u hgu
      exact keep u hu hf hl
    · simp only [updSub_ne _ _ hji] at hu1
      exact keep u1 hu1 rfl (by simp [hb hji])
  cases l with
  | op o =>
    simp only [step] at h
    split at h
    · cases h
    · cases o with
      | clear =>
        simp at h; subst h
        exact keep u1 hu1 rfl (by simp [lblBatch])
      | append e =>
        simp [blocks] at h; subst h
        simp only [Option.map_eq_some_iff] at hu1
        obtain ⟨u, hu, rfl⟩ := hu1
        have hJ := hI.some_ i u hu
        rcases deliver_cases e u with ⟨hd, hl, hf, hr, -⟩ | hd | ⟨hd, -⟩
        · rw [hd]
          have heq := hJ.eq hl hr
          rw [received_snoc, appendsAfter_snoc, hJ.params]
          simp only [Option.isSome_some, if_true, List.filter_append, ← heq]
          simp [lblBatch, storeOps, lblOp, appended, hf]
        · exact keep u hu (by rw [hd]) (by rw [hd]; simp [lblBatch])
        · exact keep u hu (by rw [hd]) (by rw [hd]; simp [lblBatch])
  | subscribe j f c b =>
    simp only [step] at h
    split at h
    · rename_i hc
      simp at hc
      obtain ⟨⟨⟨-, rfl⟩, -⟩, -⟩ := hc
      simp at h; subst h
      by_cases hji : s.n = i
      · subst hji
        simp [updSub_self] at hu1; subst hu1
        have hn := hI.none_ _ (hI.fresh _ (Nat.le_refl _))
        have hR : received s.n (tr ++ [SubLbl.subscribe s.n f c b]) = [] := by
          rw [received_snoc]; simp [received, hn.2.1, lblBatch]
        rw [hR]; simp
      · simp only [updSub_ne _ _ hji] at hu1
        exact keep u1 hu1 rfl (by simp [lblBatch])
    · cases h
  | await j =>
    refine own j _ h (fun _ => rfl) fun hji u hg => ?_
    subst hji
    cases hp : u.pending <;> simp [hp] at hg
    subst hg; simp [lblBatch]
  | pull j =>
    refine own j _ h (fun _ => rfl) fun hji u hg => ?_
    subst hji
    split at hg
    · split at hg
      · cases hg
      · rename_i e r hch
        simp at hg; subst hg
        simp [lblBatch, hch]
    · cases hg
  | recv j b =>
    refine own j _ h (fun hji => by simp [lblBatch, hji]) fun hji u hg => ?_
    subst hji
    split at hg
    · rename_i hc
      simp at hc
      obtain ⟨-, rfl⟩ := hc
      simp at hg; subst hg
      simp [lblBatch]
    · cases hg
  | finish j =>
    refine own j _ h (fun _ => rfl) fun hji u hg => ?_
    subst hji
    split at hg
    · simp at hg; subst hg; simp [lblBatch]
    · cases hg
  | close j =>
    refine own j _ h (fun _ => rfl) fun hji u hg => ?_
    subst hji
    split at hg
    · simp at hg; subst hg; simp [lblBatch]
    · simp at hg; subst hg; simp [lblBatch]
  | drop =>
    simp only [step] at h
    split at h
    · simp at h; subst h
      simp only [Option.map_eq_some_iff] at hu1
      obtain ⟨u, hu, rfl⟩ := hu1
      exact keep u hu rfl (by simp [lblBatch])
    · cases h

/-- Every reference run keeps `evt031Pref`. -/
theorem evt031_pref_run (tr : List (SubLbl E)) :
    ∀ {s : SubSt E}, run {} SubSt.init tr = some s → evt031Pref tr s := by
  obtain ⟨r, rfl⟩ : ∃ r, tr = r.reverse := ⟨tr.reverse, by simp⟩
  induction r with
  | nil =>
    intro s h i u hu
    simp [run] at h; subst h; simp [SubSt.init] at hu
  | cons l r ih =>
    intro s h
    rw [List.reverse_cons] at h ⊢
    generalize r.reverse = pre at h ih ⊢
    rw [run_snoc] at h
    cases h0 : run {} SubSt.init pre with
    | none => simp [h0] at h
    | some s0 =>
      simp only [h0, Option.bind_some] at h
      exact evt031_pref_step (inv_run h0) (ih h0) h

/-- Line 12 on the reference: where no receive of `i` is pending, what `i` received is the first
matching events appended since it subscribed, as many as its receives took. -/
theorem evt031_ref_taken {tr : List (SubLbl E)} (h : refSub tr) (i : Nat)
    (hp : pending i tr = false) : received i tr = (matchingAfter i tr).take (pulls i tr) := by
  obtain ⟨s, hs, hI⟩ := refSub_run h
  cases hu : s.subs i with
  | none =>
    have hn := hI.none_ i hu
    simp [received, hn.2.1, hn.2.2.1]
  | some u =>
    have hJ := hI.some_ i u hu
    have hcur : u.cur = [] := hJ.idle (hJ.pend.trans hp)
    have hpre := evt031_pref_run tr hs i u hu
    have hpl := hJ.pulled
    rw [hcur, List.append_nil] at hpre hpl
    simp only [matchingAfter, hJ.params]
    rw [← hpl]
    exact List.prefix_iff_eq_take.mp ((List.prefix_append _ _).trans hpre)

end Reference

/-- The witness satisfies EVT-031: it delivers, at every point, only matching events appended
after the subscribe and before that point, in order and once, in non-empty batches within the
batch size, over finite channels; an overflow ends the subscription and its stream, which ends
only after the channel is drained; an append never waits; a close with no receive pending and a
drop end the stream; a receive returns the events it took. -/
@[evidence holds EVT_031]
theorem EVT_031_reference {E : Type} [DecidableEq E] : EVT_031 (evt031PySub (E := E)) := by
  have cap_ext : ∀ {pre mid : List (SubLbl E)} {l : SubLbl E} {bs : List (List E)} {i : Nat},
      (pre ++ l :: mid).all evt031CapOk = true →
      (pre ++ l :: (mid ++ evt031Recvs i bs ++ [.await i, .finish i])).all evt031CapOk = true := by
    intro pre mid l bs i h
    have := evt031_capOk_recvs i bs
    simp only [List.all_append, List.all_cons, Bool.and_eq_true] at h this ⊢
    simp_all [evt031CapOk]
  refine ⟨fun tr _ h i => refSub_received (refSub_prefix h.1) i,
    fun _ h _ _ hb => ?_, fun _ h _ _ _ _ hp => evt031_capOk_params h.2 hp,
    fun _ _ _ _ _ _ _ h hp hf hc => refSub_overflow_ends h.1 hp hf hc,
    fun _ _ _ _ _ _ _ h hp hf hc _ hpm => ?_,
    fun _ _ _ _ _ _ _ h hp hf hc hE hpe hn => evt031_ref_overflow_drain h.1 hp hf hc hE hpe hn,
    fun _ h hd e => ⟨refSub_append_enabled h.1 hd _, by simpa [evt031CapOk] using h.2⟩,
    fun _ _ _ h _ hp => refSub_close_ends h.1 hp,
    fun _ _ _ h _ hp hq => ⟨evt031_ref_close_end h.1 hp hq, ?_⟩,
    fun _ _ _ h hi _ hpm => ?_,
    fun _ _ _ h hi hE hp hn => evt031_ref_drop_drain h.1 hi hE hp hn,
    fun _ _ h i hp => evt031_ref_taken (refSub_prefix h.1) i hp⟩
  · obtain ⟨f, c, n, hp, hne, hle⟩ := refSub_batch h.1 hb
    exact ⟨hne, f, c, n, hp, hle⟩
  · obtain ⟨bs, hb⟩ := evt031_ref_overflow_end h.1 hp hf hc hpm
    exact ⟨bs, hb, cap_ext h.2⟩
  · have := h.2
    simp only [List.all_append, List.all_cons, Bool.and_eq_true] at this ⊢
    simp_all [evt031CapOk]
  · obtain ⟨bs, hb⟩ := evt031_ref_drop_end h.1 hi hpm
    exact ⟨bs, hb, cap_ext h.2⟩

/-! ### Consequences -/

/-- Unary mode (AC3): a subscription made with batch size 1 receives exactly one event per batch,
whatever its timeout. -/
theorem evt031_unary {E : Type} {S : SubSem E} (hS : EVT_031 S) {tr : List (SubLbl E)}
    (h : S tr) {i : Nat} {f : E → Bool} {c : Option Nat} (hp : subParams i tr = some (f, c, 1))
    {b : List E} (hb : b ∈ batches i tr) : b.length = 1 := by
  obtain ⟨hne, f', c', n, hp', hle⟩ := hS.2.1 tr h i b hb
  rw [hp] at hp'
  simp only [Option.some.injEq, Prod.mk.injEq] at hp'
  obtain ⟨-, -, rfl⟩ := hp'
  cases b with
  | nil => exact absurd rfl hne
  | cons x r => simp at hle ⊢; exact hle

/-- Every event a subscription of a store that meets EVT-031 received was appended to the store,
in append order and at most once (the weak form shared with [EVT-024], ruling EVT-C4 (a)). -/
theorem evt031_received_appended {E : Type} {S : SubSem E} (hS : EVT_031 S)
    {tr : List (SubLbl E)} (h : S tr) (i : Nat) : received i tr <+ appended (storeOps tr) :=
  (hS.1 tr [] (by rw [List.append_nil]; exact h) i).trans (matchingAfter_sublist i tr)

/-- After an append that finds the channel of a subscription that had not ended full, with no
receive of it pending, a store that meets EVT-031 allows its receives to return batches that
together are exactly what its channel held (`evt031Held`), and then to report the end (lines 5
and 6). -/
theorem evt031_overflow_drains {E : Type} {S : SubSem E} (hS : EVT_031 S)
    {pre mid : List (SubLbl E)} {e : E} {i : Nat} {f : E → Bool} {c n : Nat}
    (h : S (pre ++ .op (.append e) :: mid)) (hpar : subParams i pre = some (f, some c, n))
    (hf : f e = true) (hc : c ≤ backlog i pre) (hE : evt031Ended i pre = false)
    (hp : pending i pre = false) (hq : evt031Quiet i mid = true) :
    ∃ bs, bs.flatten = evt031Held i pre ∧
      S (pre ++ .op (.append e) :: (mid ++ evt031Recvs i bs ++ [.await i, .finish i])) := by
  obtain ⟨-, -, -, -, l5, l6, -⟩ := hS
  have hpm : pending i (pre ++ .op (.append e) :: mid) = false := by
    have := evt031_pending_quiet i (pre ++ [.op (.append e)]) mid hq
    rw [List.append_assoc, List.singleton_append] at this
    rw [this, pending_snoc]; simpa [lblPend] using hp
  obtain ⟨bs, hb⟩ := l5 pre e mid i f c n h hpar hf hc hp hpm
  refine ⟨bs, ?_, hb⟩
  have hb' : S (pre ++ .op (.append e) :: ((mid ++ evt031Recvs i bs ++ [.await i]) ++
      [.finish i])) := by simpa [List.append_assoc] using hb
  have hn : evt031NoClose i (mid ++ evt031Recvs i bs ++ [.await i]) = true := by
    have h1 := evt031_noClose_quiet hq
    have h2 := evt031_noClose_recvs i bs
    simp only [evt031NoClose, List.all_append, Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨⟨h1, h2⟩, by simp [evt031CloseOf]⟩
  have := l6 pre e _ i f c n hb' hpar hf hc hE hp hn
  rw [received_append, received_append, evt031_received_quiet i mid hq,
    evt031_received_recvs] at this
  simpa [received, batches, lblBatch] using this

/-! ### The lines one by one

The twelve lines of EVT-031 as separate predicates (`evt031_iff`), so that a mutant reading can
name every line but one. -/

section Lines

variable {E : Type}

/-- Line 1: what a subscription received at every point is a sublist of the matching events
appended after it subscribed. -/
def Evt031L1 (S : SubSem E) : Prop :=
  ∀ tr tr', S (tr ++ tr') → ∀ i, received i tr <+ matchingAfter i tr

/-- The half of line 2 on the batch size: every batch is no longer than the batch size. -/
def Evt031L2Bound (S : SubSem E) : Prop :=
  ∀ tr, S tr → ∀ i b, b ∈ batches i tr → ∃ f c n, subParams i tr = some (f, c, n) ∧ b.length ≤ n

/-- Line 2: every batch is non-empty and no longer than the batch size. -/
def Evt031L2 (S : SubSem E) : Prop :=
  ∀ tr, S tr → ∀ i b, b ∈ batches i tr →
    b ≠ [] ∧ ∃ f c n, subParams i tr = some (f, c, n) ∧ b.length ≤ n

/-- Line 3: every channel has a finite capacity. -/
def Evt031L3 (S : SubSem E) : Prop :=
  ∀ tr, S tr → ∀ i f c n, subParams i tr = some (f, c, n) → c.isSome = true

/-- Line 4: after an overflowing append, a subscription receives no later event. -/
def Evt031L4 (S : SubSem E) : Prop :=
  ∀ pre e suf i f c n, S (pre ++ .op (.append e) :: suf) →
    subParams i pre = some (f, some c, n) → f e = true → c ≤ backlog i pre →
    received i (pre ++ .op (.append e) :: suf) <+ matchingAfter i pre

/-- Line 5: after an overflowing append, the stream can end at every later point where no
receive is pending. -/
def Evt031L5 (S : SubSem E) : Prop :=
  ∀ pre e mid i f c n, S (pre ++ .op (.append e) :: mid) →
    subParams i pre = some (f, some c, n) → f e = true → c ≤ backlog i pre →
    pending i pre = false → pending i (pre ++ .op (.append e) :: mid) = false →
    ∃ bs, S (pre ++ .op (.append e) :: (mid ++ evt031Recvs i bs ++ [.await i, .finish i]))

/-- Line 6: after an overflowing append, the stream ends only once the channel is drained. -/
def Evt031L6 (S : SubSem E) : Prop :=
  ∀ pre e mid i f c n, S (pre ++ .op (.append e) :: (mid ++ [.finish i])) →
    subParams i pre = some (f, some c, n) → f e = true → c ≤ backlog i pre →
    evt031Ended i pre = false → pending i pre = false → evt031NoClose i mid = true →
    received i mid = evt031Held i pre

/-- Line 7: until the drop, an append is allowed after every run. -/
def Evt031L7 (S : SubSem E) : Prop :=
  ∀ tr, S tr → dropped tr = false → ∀ e, S (tr ++ [.op (.append e)])

/-- Line 8: after a close with no receive pending, the subscription receives nothing. -/
def Evt031L8 (S : SubSem E) : Prop :=
  ∀ pre suf i, S (pre ++ .close i :: suf) → (subParams i pre).isSome = true →
    pending i pre = false → received i suf = []

/-- Line 9: after such a close, a receive can report the end. -/
def Evt031L9 (S : SubSem E) : Prop :=
  ∀ pre mid i, S (pre ++ .close i :: mid) → (subParams i pre).isSome = true →
    pending i pre = false → evt031Quiet i mid = true →
    S (pre ++ .close i :: (mid ++ [.await i, .finish i]))

/-- Line 10: after the drop, the stream of a subscription with no receive pending can end at
every later point where no receive is pending. -/
def Evt031L10 (S : SubSem E) : Prop :=
  ∀ pre mid i, S (pre ++ .drop :: mid) → (subParams i pre).isSome = true →
    pending i pre = false → pending i (pre ++ .drop :: mid) = false →
    ∃ bs, S (pre ++ .drop :: (mid ++ evt031Recvs i bs ++ [.await i, .finish i]))

/-- Line 11: after the drop, the stream ends only once the channel is drained. -/
def Evt031L11 (S : SubSem E) : Prop :=
  ∀ pre mid i, S (pre ++ .drop :: (mid ++ [.finish i])) → (subParams i pre).isSome = true →
    evt031Ended i pre = false → pending i pre = false → evt031NoClose i mid = true →
    received i mid = evt031Held i pre

/-- Line 12: where no receive is pending, a subscription received exactly the first matching
events, as many as its receives took. -/
def Evt031L12 (S : SubSem E) : Prop :=
  ∀ tr tr', S (tr ++ tr') → ∀ i, pending i tr = false →
    received i tr = (matchingAfter i tr).take (pulls i tr)

/-- EVT-031 is the conjunction of its twelve lines. -/
theorem evt031_iff (S : SubSem E) :
    EVT_031 S ↔ Evt031L1 S ∧ Evt031L2 S ∧ Evt031L3 S ∧ Evt031L4 S ∧ Evt031L5 S ∧ Evt031L6 S ∧
      Evt031L7 S ∧ Evt031L8 S ∧ Evt031L9 S ∧ Evt031L10 S ∧ Evt031L11 S ∧ Evt031L12 S :=
  Iff.rfl

end Lines

/-! ### A store whose receive may return an empty batch (line 2, the non-empty half)

The store allows the witness's runs and one more: a subscription whose receive returns the empty
batch, followed by a pending receive and the drop. Each of the other lines holds of it: the run
holds no append and no close, so lines 4 to 9 have no instance in it, it ends with a drop, so
line 7 has none, the receive is pending at the drop, so line 10 has none, and it reports no end,
so line 11 has none; it receives nothing and takes nothing, so lines 1 and 12 hold, and its one
batch is within the batch size, so the bound of line 2 holds. -/

/-- The run with the empty batch. -/
def evt031EmptyRun : List (SubLbl Nat) :=
  [.subscribe 0 subAll (some 4) 1, .await 0, .recv 0 [], .await 0, .drop]

/-- The witness, and besides its runs the run with the empty batch. -/
def evt031EmptyBatch : SubSem Nat := fun tr => evt031PySub tr ∨ tr = evt031EmptyRun

/-- The mutant reading without the non-empty half of line 2: lines 1 and 3 to 12, and the batch
size bound of line 2. -/
def Evt031NoNonEmpty {E : Type} (S : SubSem E) : Prop :=
  Evt031L1 S ∧ Evt031L2Bound S ∧ Evt031L3 S ∧ Evt031L4 S ∧ Evt031L5 S ∧ Evt031L6 S ∧
    Evt031L7 S ∧ Evt031L8 S ∧ Evt031L9 S ∧ Evt031L10 S ∧ Evt031L11 S ∧ Evt031L12 S

theorem evt031Empty_received (i : Nat) : received i evt031EmptyRun = [] := by
  by_cases h : 0 = i <;> simp [received, batches, lblBatch, evt031EmptyRun, h]

theorem evt031Empty_params (i : Nat) :
    subParams i evt031EmptyRun = if 0 = i then some (subAll, some 4, 1) else none := by
  by_cases h : 0 = i <;> simp [subParams, lblParams, evt031EmptyRun, h]

/-- A label that is not in the run splits it nowhere. -/
theorem evt031Empty_split {l : SubLbl Nat} (hl : l ∉ evt031EmptyRun) {pre suf : List (SubLbl Nat)}
    (h : pre ++ l :: suf = evt031EmptyRun) : False :=
  hl (by rw [← h]; simp)

/-- The run splits at its drop only before its last label. -/
theorem evt031Empty_drop {pre mid : List (SubLbl Nat)}
    (h : pre ++ .drop :: mid = evt031EmptyRun) :
    pre = [.subscribe 0 subAll (some 4) 1, .await 0, .recv 0 [], .await 0] ∧ mid = [] := by
  rcases pre with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨x, pre⟩⟩⟩⟩⟩ <;>
    simp [evt031EmptyRun] at h ⊢ <;> simp_all

/-- ✗ A store whose receive may return an empty batch meets every line but the non-empty half of
line 2, and violates EVT-031 (line 2, 'at least one event'). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_emptyBatch :
    Evt031NoNonEmpty evt031EmptyBatch ∧ ¬ EVT_031 evt031EmptyBatch := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := EVT_031_reference (E := Nat)
  have hmem : ∀ {l : SubLbl Nat} {pre suf : List (SubLbl Nat)},
      l ∉ evt031EmptyRun → evt031EmptyBatch (pre ++ l :: suf) → evt031PySub (pre ++ l :: suf) :=
    fun hl h => h.resolve_right (evt031Empty_split hl)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun h => ?_⟩
  · intro tr tr' h i
    rcases h with h | h
    · exact r1 tr tr' h i
    · have := received_append i tr tr'
      rw [h, evt031Empty_received] at this
      rw [(List.append_eq_nil_iff.mp this.symm).1]
      exact List.nil_sublist _
  · intro tr h i b hb
    rcases h with h | rfl
    · exact (r2 tr h i b hb).2
    · by_cases hi : 0 = i
      · subst hi
        have hb' : b = [] := by simpa [batches, lblBatch, evt031EmptyRun] using hb
        exact ⟨subAll, some 4, 1, rfl, by simp [hb']⟩
      · simp [batches, lblBatch, evt031EmptyRun, hi] at hb
  · intro tr h i f c n hp
    rcases h with h | rfl
    · exact r3 tr h i f c n hp
    · rw [evt031Empty_params] at hp
      by_cases hi : 0 = i
      · simp only [hi, if_true, Option.some.injEq, Prod.mk.injEq] at hp
        rw [← hp.2.1]; rfl
      · simp [hi] at hp
  · intro pre e suf i f c n h
    exact r4 pre e suf i f c n (hmem (by simp [evt031EmptyRun]) h)
  · intro pre e mid i f c n h hp hf hc hpe hq
    obtain ⟨bs, hb⟩ := r5 pre e mid i f c n (hmem (by simp [evt031EmptyRun]) h) hp hf hc hpe hq
    exact ⟨bs, Or.inl hb⟩
  · intro pre e mid i f c n h
    exact r6 pre e mid i f c n (hmem (by simp [evt031EmptyRun]) h)
  · intro tr h hd e
    rcases h with h | rfl
    · exact Or.inl (r7 tr h hd e)
    · exact absurd hd (by decide)
  · intro pre suf i h
    exact r8 pre suf i (hmem (by simp [evt031EmptyRun]) h)
  · intro pre mid i h hp hpe hq
    exact Or.inl (r9 pre mid i (hmem (by simp [evt031EmptyRun]) h) hp hpe hq)
  · intro pre mid i h hp hpe hq
    rcases h with h | h
    · obtain ⟨bs, hb⟩ := r10 pre mid i h hp hpe hq
      exact ⟨bs, Or.inl hb⟩
    · obtain ⟨rfl, rfl⟩ := evt031Empty_drop h
      by_cases hi : 0 = i
      · subst hi
        exact absurd hpe (by decide)
      · simp [subParams, lblParams, hi] at hp
  · intro pre mid i h
    rcases h with h | h
    · exact r11 pre mid i h
    · exfalso
      have : SubLbl.finish i ∈ evt031EmptyRun := by rw [← h]; simp
      simp [evt031EmptyRun] at this
  · intro tr tr' h i hp
    rcases h with h | h
    · exact r12 tr tr' h i hp
    · have hr := received_append i tr tr'
      have hq := pulls_append i tr tr'
      rw [h, evt031Empty_received] at hr
      have h0 : pulls i evt031EmptyRun = 0 := by
        by_cases hi : 0 = i <;> simp [pulls, lblPull, evt031EmptyRun, hi]
      rw [h, h0] at hq
      rw [(List.append_eq_nil_iff.mp hr.symm).1, show pulls i tr = 0 by omega]
      simp
  · have := (h.2.1 evt031EmptyRun (Or.inr rfl) 0 [] (by decide)).1
    exact this rfl

/-! ### Wrong stores, one per line

Each mutant below is a store that allows one concrete run the line it names forbids; unlike
`EVT_031_mutant_emptyBatch`, its reading is that run, not the conjunction of the other lines, so
it shows that the line rejects the store and not that every other line accepts it. -/

/-- A store whose subscribe seeds the channel with the earlier matching events. -/
def evt031Replay : SubSem Nat := subSem { replay := true }

/-- The store allows a subscription to receive an event appended before it subscribed. -/
def Evt031ReceivesEarlier (S : SubSem Nat) : Prop :=
  S [.op (.append 5), .subscribe 0 subAll (some 4) 1, .await 0, .pull 0, .recv 0 [5]]

/-- ✗ A subscription that replays the events appended before it violates EVT-031 (line 1,
forward-only, AC2). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_replay : Evt031ReceivesEarlier evt031Replay ∧ ¬ EVT_031 evt031Replay := by
  refine ⟨subRun_replay, fun h => ?_⟩
  have := h.1 [.op (.append 5), .subscribe 0 subAll (some 4) 1, .await 0, .pull 0, .recv 0 [5]] []
    (by rw [List.append_nil]; exact subRun_replay) 0
  revert this; decide

/-- A store whose delivery ignores the filter. -/
def evt031NoFilter : SubSem Nat := subSem { filters := false }

/-- The store allows a subscription filtered to even events to receive an odd one. -/
def Evt031ReceivesUnmatched (S : SubSem Nat) : Prop :=
  S [.subscribe 0 subEven (some 4) 1, .op (.append 1), .await 0, .pull 0, .recv 0 [1]]

/-- ✗ A subscription that receives an event its filter does not match violates EVT-031 (line 1,
the filter, AC1). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_noFilter :
    Evt031ReceivesUnmatched evt031NoFilter ∧ ¬ EVT_031 evt031NoFilter := by
  refine ⟨subRun_noFilter, fun h => ?_⟩
  have := h.1 [.subscribe 0 subEven (some 4) 1, .op (.append 1), .await 0, .pull 0, .recv 0 [1]]
    [] (by rw [List.append_nil]; exact subRun_noFilter) 0
  revert this; decide

/-- A run in which a receive returns event 5 before 5 is appended. Over the whole run, what the
subscription received is a sublist of the matching events appended after it subscribed. -/
def evt031EarlyRun : List (SubLbl Nat) :=
  [.subscribe 0 subAll (some 4) 1, .await 0, .pull 0, .recv 0 [5], .op (.append 5)]

/-- Line 1 on whole runs only would accept the run above. -/
theorem evt031EarlyRun_whole : received 0 evt031EarlyRun <+ matchingAfter 0 evt031EarlyRun := by
  decide

/-- A store that allows, besides the witness's runs, the run above. -/
def evt031Early : SubSem Nat := fun tr => evt031PySub tr ∨ tr = evt031EarlyRun

/-- The store allows a receive to return an event before it is appended. -/
def Evt031ReturnsBeforeAppend (S : SubSem Nat) : Prop := S evt031EarlyRun

/-- ✗ A receive that returns an event before it is appended violates EVT-031 (line 1, stated at
every point of a run). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_early :
    Evt031ReturnsBeforeAppend evt031Early ∧ ¬ EVT_031 evt031Early := by
  refine ⟨Or.inr rfl, fun h => ?_⟩
  have := h.1 [.subscribe 0 subAll (some 4) 1, .await 0, .pull 0, .recv 0 [5]] [.op (.append 5)]
    (Or.inr rfl) 0
  revert this; decide

/-- A store whose receives take events without the batch-size bound. -/
def evt031Unbounded : SubSem Nat := subSem { bounded := false }

/-- The store allows a subscription with batch size 1 to receive a batch of two. -/
def Evt031OversizeBatch (S : SubSem Nat) : Prop :=
  S [.subscribe 0 subAll (some 4) 1, .op (.append 1), .op (.append 2), .await 0, .pull 0,
    .pull 0, .recv 0 [1, 2]]

/-- ✗ A batch larger than the batch size violates EVT-031 (line 2, AC3). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_oversizeBatch :
    Evt031OversizeBatch evt031Unbounded ∧ ¬ EVT_031 evt031Unbounded := by
  refine ⟨subRun_unbounded, fun h => ?_⟩
  obtain ⟨-, f, c, n, hp, hle⟩ := h.2.1 _ subRun_unbounded 0 [1, 2] (by decide)
  have hp' : subParams 0 ([.subscribe 0 subAll (some 4) 1, .op (.append 1), .op (.append 2),
      .await 0, .pull 0, .pull 0, .recv 0 [1, 2]] : List (SubLbl Nat)) =
      some (subAll, some 4, 1) := rfl
  rw [hp'] at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨-, -, rfl⟩ := hp
  simp at hle

/-- The store allows a subscription with an unbounded channel. -/
def Evt031UnboundedChannel (S : SubSem Nat) : Prop := S [.subscribe 0 subAll none 1]

/-- ✗ The reference without the restriction to finite capacities, which allows the unbounded
channel of the debug stores ([EVT-024]), violates EVT-031 (line 3, 'is bounded'). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_unboundedChannel :
    Evt031UnboundedChannel refSub ∧ ¬ EVT_031 (refSub (E := Nat)) := by
  have hr : Evt031UnboundedChannel refSub := by unfold Evt031UnboundedChannel; decide
  refine ⟨hr, fun h => ?_⟩
  have := h.2.2.1 _ hr 0 subAll none 1 rfl
  cases this

/-- A store whose overflow drops only the event that does not fit; the subscription stays
(ruling D86 (b), the reading of the runtime's docstring). -/
def evt031DropEvent : SubSem Nat := subSem { overflow := .dropEvent }

/-- The store allows a subscription with capacity 1 to receive an event appended after an append
found its channel full. -/
def Evt031SurvivesOverflow (S : SubSem Nat) : Prop :=
  S [.subscribe 0 subAll (some 1) 4, .op (.append 1), .op (.append 2), .await 0, .pull 0,
    .recv 0 [1], .op (.append 3), .await 0, .pull 0, .recv 0 [3]]

/-- ✗ An overflow that drops only the event that does not fit, and keeps the subscription,
violates EVT-031 (line 4, ruling D86 (a)). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_dropEvent :
    Evt031SurvivesOverflow evt031DropEvent ∧ ¬ EVT_031 evt031DropEvent := by
  refine ⟨subRun_dropEvent, fun h => ?_⟩
  have := h.2.2.2.1 [.subscribe 0 subAll (some 1) 4, .op (.append 1)] 2
    [.await 0, .pull 0, .recv 0 [1], .op (.append 3), .await 0, .pull 0, .recv 0 [3]]
    0 subAll 1 4 subRun_dropEvent rfl rfl (by decide)
  revert this; decide

/-- A subscribe that forgets its capacity: the channel is unbounded. -/
def evt031ForgetCap : SubLbl Nat → SubLbl Nat
  | .subscribe i f _ b => .subscribe i f none b
  | l => l

/-- A store that ignores the channel capacity: it allows what the reference allows with every
channel unbounded. -/
def evt031CapIgnored : SubSem Nat := fun tr => refSub (tr.map evt031ForgetCap)

/-- The store allows a subscription with capacity 1 to receive two events in one batch. -/
def Evt031OverCapacity (S : SubSem Nat) : Prop :=
  S [.subscribe 0 subAll (some 1) 4, .op (.append 1), .op (.append 2), .await 0, .pull 0,
    .pull 0, .recv 0 [1, 2]]

/-- ✗ A channel that is not bounded by its capacity violates EVT-031 (line 4, 'is bounded'). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_capIgnored :
    Evt031OverCapacity evt031CapIgnored ∧ ¬ EVT_031 evt031CapIgnored := by
  have hr : Evt031OverCapacity evt031CapIgnored := by
    unfold Evt031OverCapacity evt031CapIgnored; decide
  refine ⟨hr, fun h => ?_⟩
  have := h.2.2.2.1 [.subscribe 0 subAll (some 1) 4, .op (.append 1)] 2
    [.await 0, .pull 0, .pull 0, .recv 0 [1, 2]] 0 subAll 1 4 hr rfl rfl (by decide)
  revert this; decide

/-- Whether the end of the stream is reported only for a subscription closed before, or after
the store was dropped: the closed subscriptions so far, whether the store was dropped, the rest of
the run. -/
def evt031EndCause : List Nat → Bool → List (SubLbl Nat) → Bool
  | _, _, [] => true
  | cl, d, .op _ :: tr => evt031EndCause cl d tr
  | cl, d, .subscribe _ _ _ _ :: tr => evt031EndCause cl d tr
  | cl, d, .await _ :: tr => evt031EndCause cl d tr
  | cl, d, .pull _ :: tr => evt031EndCause cl d tr
  | cl, d, .recv _ _ :: tr => evt031EndCause cl d tr
  | cl, d, .finish i :: tr => (d || cl.contains i) && evt031EndCause cl d tr
  | cl, d, .close i :: tr => evt031EndCause (i :: cl) d tr
  | cl, _, .drop :: tr => evt031EndCause cl true tr

/-- Receives that return batches report no end. -/
theorem evt031EndCause_recvs (cl : List Nat) (d : Bool) (i : Nat) :
    ∀ (bs : List (List Nat)) (r : List (SubLbl Nat)),
      evt031EndCause cl d (evt031Recvs i bs ++ r) = evt031EndCause cl d r
  | [], _ => rfl
  | b :: bs, r => by
    have hp : ∀ (xs : List Nat) (r : List (SubLbl Nat)),
        evt031EndCause cl d ((xs.map fun _ => (SubLbl.pull i : SubLbl Nat)) ++ r) =
          evt031EndCause cl d r := by
      intro xs r
      induction xs with
      | nil => rfl
      | cons x xs ih => simpa only [List.map_cons, List.cons_append, evt031EndCause] using ih
    have ih := evt031EndCause_recvs cl d i bs r
    simp only [evt031Recvs, List.flatMap_cons] at ih ⊢
    simp only [List.append_assoc, List.cons_append, evt031EndCause, hp,
      List.nil_append, ih]

/-- A store whose receives report the end only after a close or a drop: an overflow stops the
delivery but leaves the receiver waiting (the bullet 'terminates cleanly on explicit close or when
the store is dropped' read as the only two ends). -/
def evt031OverflowHangs : SubSem Nat := fun tr => evt031PySub tr ∧ evt031EndCause [] false tr = true

/-- The store allows an append that finds the channel of a subscription full. -/
def Evt031Overflows (S : SubSem Nat) : Prop :=
  S [.subscribe 0 subAll (some 1) 4, .op (.append 1), .op (.append 2)]

/-- ✗ A store whose receives keep waiting after an overflow violates EVT-031 (line 5): the
subscription receives nothing more, but the stream never ends. -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_overflowHangs :
    Evt031Overflows evt031OverflowHangs ∧ ¬ EVT_031 evt031OverflowHangs := by
  have hr : Evt031Overflows evt031OverflowHangs := by
    unfold Evt031Overflows evt031OverflowHangs; decide
  refine ⟨hr, fun h => ?_⟩
  obtain ⟨bs, -, hc⟩ := h.2.2.2.2.1 [.subscribe 0 subAll (some 1) 4, .op (.append 1)] 2 [] 0
    subAll 1 4 hr rfl rfl (by decide) (by decide) (by decide)
  simp only [List.cons_append, List.nil_append, evt031EndCause] at hc
  rw [evt031EndCause_recvs] at hc
  cases hc

/-- The early ends after an overflow: right after an append that finds the channel of a
subscription full (the premises of line 6), a receive reports the end without taking what the
channel holds. This is the likely Java or TypeScript slip in which the store ends an overflowing
subscription through the subscription's own close, which clears its queue. -/
def evt031OverflowDiscards : SubSem Nat := fun tr =>
  evt031PySub tr ∨
    ∃ (pre : List (SubLbl Nat)) (e i : Nat) (f : Nat → Bool) (c n : Nat),
      evt031PySub (pre ++ [.op (.append e)]) ∧ subParams i pre = some (f, some c, n) ∧
      f e = true ∧ c ≤ backlog i pre ∧ pending i pre = false ∧
      tr = pre ++ [.op (.append e), .await i, .finish i]

/-- The store allows a receive to report the end right after an overflow while the channel
holds event 1. -/
def Evt031EndsEarlyAfterOverflow (S : SubSem Nat) : Prop :=
  S [.subscribe 0 subAll (some 1) 4, .op (.append 1), .op (.append 2), .await 0, .finish 0]

/-- The witness forbids that run, and the channel holds event 1 when the overflow happens. -/
theorem evt031OverflowDiscards_facts :
    ¬ evt031PySub [.subscribe 0 subAll (some 1) 4, .op (.append 1), .op (.append 2), .await 0,
      .finish 0] ∧
    evt031Held 0 ([.subscribe 0 subAll (some 1) 4, .op (.append 1)] : List (SubLbl Nat)) = [1] := by
  decide

/-- ✗ A store whose receives report the end after an overflow before they have taken what the
channel held violates EVT-031 (line 6). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_overflowDiscards :
    Evt031EndsEarlyAfterOverflow evt031OverflowDiscards ∧ ¬ EVT_031 evt031OverflowDiscards := by
  have hr : Evt031EndsEarlyAfterOverflow evt031OverflowDiscards :=
    Or.inr ⟨[.subscribe 0 subAll (some 1) 4, .op (.append 1)], 2, 0, subAll, 1, 4, by decide, rfl,
      rfl, by decide, by decide, rfl⟩
  refine ⟨hr, fun h => ?_⟩
  have := h.2.2.2.2.2.1 [.subscribe 0 subAll (some 1) 4, .op (.append 1)] 2 [.await 0] 0 subAll
    1 4 hr rfl rfl (by decide) (by decide) (by decide) rfl
  revert this; decide

/-- A store whose appends wait for room (back-pressure). -/
def evt031Block : SubSem Nat := subSem { overflow := .block }

/-- The store allows an append that fills the channel of a subscription with capacity 1. -/
def Evt031FillsChannel (S : SubSem Nat) : Prop :=
  S [.subscribe 0 subAll (some 1) 4, .op (.append 1)]

/-- ✗ Back-pressure (an append that waits for room in a full channel) violates EVT-031 (line 7,
ruling D86 (a)). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_block : Evt031FillsChannel evt031Block ∧ ¬ EVT_031 evt031Block := by
  have hr : Evt031FillsChannel evt031Block := by
    unfold Evt031FillsChannel evt031Block; decide
  refine ⟨hr, fun h => subRun_block ?_⟩
  exact h.2.2.2.2.2.2.1 _ hr (by decide) 2

/-- A store whose close does nothing. -/
def evt031CloseNoop : SubSem Nat := subSem { closeEnds := false }

/-- The store allows a subscription to receive an event appended after it was closed. -/
def Evt031ReceivesAfterClose (S : SubSem Nat) : Prop :=
  S [.subscribe 0 subAll (some 4) 1, .close 0, .op (.append 1), .await 0, .pull 0, .recv 0 [1]]

/-- ✗ A close that does nothing violates EVT-031 (line 8, AC4 and ruling D86 (d)). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_closeNoop :
    Evt031ReceivesAfterClose evt031CloseNoop ∧ ¬ EVT_031 evt031CloseNoop := by
  refine ⟨subRun_closeNoop, fun h => ?_⟩
  have := h.2.2.2.2.2.2.2.1 [.subscribe 0 subAll (some 4) 1]
    [.op (.append 1), .await 0, .pull 0, .recv 0 [1]] 0 subRun_closeNoop rfl (by decide)
  revert this; decide

/-- Whether the run reports an end of the stream after a label `p` picks: whether such a label was
seen, the rest of the run. -/
def evt031EndsAfter (p : SubLbl Nat → Bool) : Bool → List (SubLbl Nat) → Bool
  | _, [] => false
  | seen, .finish i :: tr => seen || evt031EndsAfter p (seen || p (.finish i)) tr
  | seen, l :: tr => evt031EndsAfter p (seen || p l) tr

/-- Whether a label is a close. -/
def evt031IsClose : SubLbl Nat → Bool
  | .close _ => true
  | _ => false

/-- Whether a label is the drop of the store. -/
def evt031IsDrop : SubLbl Nat → Bool
  | .drop => true
  | _ => false

/-- A store whose close stops delivery but leaves the receiver waiting: no end is reported after
a close. -/
def evt031CloseHangs : SubSem Nat := fun tr => refSub tr ∧ evt031EndsAfter evt031IsClose false tr = false

/-- The store allows a close of a subscription with no receive pending. -/
def Evt031Closes (S : SubSem Nat) : Prop := S [.subscribe 0 subAll (some 4) 1, .close 0]

/-- ✗ A close after which the next receive waits instead of reporting the end violates EVT-031
(line 9, AC4 'ends iteration cleanly'). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_closeHangs :
    Evt031Closes evt031CloseHangs ∧ ¬ EVT_031 evt031CloseHangs := by
  have hr : Evt031Closes evt031CloseHangs := by
    unfold Evt031Closes evt031CloseHangs; decide
  refine ⟨hr, fun h => ?_⟩
  have := h.2.2.2.2.2.2.2.2.1 [.subscribe 0 subAll (some 4) 1] [] 0 hr rfl (by decide) rfl
  revert this; unfold evt031CloseHangs; decide

/-- Whether the run reports an end of the stream after a close followed by an operation on the
store: whether a close was seen, whether an operation followed it, the rest of the run. -/
def evt031LateEnd : Bool → Bool → List (SubLbl Nat) → Bool
  | _, _, [] => false
  | _, o, .close _ :: tr => evt031LateEnd true o tr
  | c, o, .op _ :: tr => evt031LateEnd c (o || c) tr
  | c, o, .finish _ :: tr => o || evt031LateEnd c o tr
  | c, o, _ :: tr => evt031LateEnd c o tr

/-- A store whose receive reports the end right after a close, but waits once an append came
between the close and the receive. -/
def evt031LateCloseHangs : SubSem Nat := fun tr =>
  evt031PySub tr ∧ evt031LateEnd false false tr = false

/-- Right after the close, the store reports the end, as a line that speaks only of the labels
right after the close requires. -/
theorem evt031LateCloseHangs_right_after :
    evt031LateCloseHangs [.subscribe 0 subAll (some 4) 1, .close 0, .await 0, .finish 0] := by
  unfold evt031LateCloseHangs; decide

/-- The store allows an append after a close of a subscription with no receive pending. -/
def Evt031AppendsAfterClose (S : SubSem Nat) : Prop :=
  S [.subscribe 0 subAll (some 4) 1, .close 0, .op (.append 1)]

/-- ✗ A close after which a receive that comes after an append waits instead of reporting the end
violates EVT-031 (line 9, 'its next receive', at any later point). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_lateCloseHangs :
    Evt031AppendsAfterClose evt031LateCloseHangs ∧ ¬ EVT_031 evt031LateCloseHangs := by
  have hr : Evt031AppendsAfterClose evt031LateCloseHangs := by
    unfold Evt031AppendsAfterClose evt031LateCloseHangs; decide
  refine ⟨hr, fun h => ?_⟩
  have := h.2.2.2.2.2.2.2.2.1 [.subscribe 0 subAll (some 4) 1] [.op (.append 1)] 0 hr rfl
    (by decide) rfl
  revert this; unfold evt031LateCloseHangs; decide

/-- Once a label `p` picks has been seen, a run that ends with an end of the stream reports one. -/
theorem evt031EndsAfter_seen (p : SubLbl Nat → Bool) (i : Nat) (ys : List (SubLbl Nat)) :
    evt031EndsAfter p true (ys ++ [.finish i]) = true := by
  induction ys with
  | nil => simp [evt031EndsAfter]
  | cons l ys ih => cases l <;> simp [evt031EndsAfter, ih]

/-- A run with a label `p` picks, followed later by an end of the stream, reports an end after it. -/
theorem evt031EndsAfter_after (p : SubLbl Nat → Bool) {l : SubLbl Nat} (hl : p l = true)
    (i : Nat) (ys : List (SubLbl Nat)) :
    ∀ (xs : List (SubLbl Nat)) (seen : Bool),
      evt031EndsAfter p seen (xs ++ l :: (ys ++ [.finish i])) = true := by
  intro xs
  induction xs with
  | nil =>
    intro seen
    cases l <;> simp [evt031EndsAfter, hl, evt031EndsAfter_seen] <;> simp_all
  | cons x xs ih =>
    intro seen
    cases x <;> simp [evt031EndsAfter, ih]

/-- A store whose drop leaves the receivers waiting: no end is reported after a drop. -/
def evt031DropHangs : SubSem Nat := fun tr => refSub tr ∧ evt031EndsAfter evt031IsDrop false tr = false

/-- The store allows a drop while a subscription holds an event in its channel. -/
def Evt031DropsWithBuffer (S : SubSem Nat) : Prop :=
  S [.subscribe 0 subAll (some 4) 1, .op (.append 1), .drop]

/-- ✗ A drop after which the receives wait instead of reporting the end violates EVT-031
(line 10, 'terminates cleanly ... when the store is dropped'). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_dropHangs :
    Evt031DropsWithBuffer evt031DropHangs ∧ ¬ EVT_031 evt031DropHangs := by
  have hr : Evt031DropsWithBuffer evt031DropHangs := by
    unfold Evt031DropsWithBuffer evt031DropHangs; decide
  refine ⟨hr, fun h => ?_⟩
  obtain ⟨bs, -, hc⟩ := h.2.2.2.2.2.2.2.2.2.1 [.subscribe 0 subAll (some 4) 1, .op (.append 1)] []
    0 hr rfl (by decide) (by decide)
  have := evt031EndsAfter_after evt031IsDrop (l := .drop) rfl 0
    (evt031Recvs 0 bs ++ [.await 0]) [.subscribe 0 subAll (some 4) 1, .op (.append 1)] false
  simp only [List.append_assoc, List.cons_append, List.nil_append] at this hc
  rw [this] at hc
  cases hc

/-- The early ends after a drop: right after the drop, a receive of a subscription made before,
with no receive pending, reports the end without taking what its channel holds. This is the
likely TypeScript slip in which the store's disposal ends each subscription through its own
close, which clears its queue. -/
def evt031DropDiscards : SubSem Nat := fun tr =>
  evt031PySub tr ∨
    ∃ (pre : List (SubLbl Nat)) (i : Nat), evt031PySub (pre ++ [.drop]) ∧
      (subParams i pre).isSome = true ∧ pending i pre = false ∧
      tr = pre ++ [.drop, .await i, .finish i]

/-- The store allows a receive to report the end right after a drop while the channel holds
event 1. -/
def Evt031EndsEarlyAfterDrop (S : SubSem Nat) : Prop :=
  S [.subscribe 0 subAll (some 4) 1, .op (.append 1), .drop, .await 0, .finish 0]

/-- ✗ A store whose receives report the end after a drop before they have taken what the channel
held violates EVT-031 (line 11). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_dropDiscards :
    Evt031EndsEarlyAfterDrop evt031DropDiscards ∧ ¬ EVT_031 evt031DropDiscards := by
  have hr : Evt031EndsEarlyAfterDrop evt031DropDiscards :=
    Or.inr ⟨[.subscribe 0 subAll (some 4) 1, .op (.append 1)], 0, by decide, rfl, by decide, rfl⟩
  refine ⟨hr, fun h => ?_⟩
  have := h.2.2.2.2.2.2.2.2.2.2.1 [.subscribe 0 subAll (some 4) 1, .op (.append 1)] [.await 0] 0 hr
    rfl (by decide) (by decide) rfl
  revert this; decide

/-- A store that allows what the witness allows, except that once the labels `P` have happened
the stream of subscription 0 never reports its end. -/
def evt031HangsAfter (P : List (SubLbl Nat)) : SubSem Nat := fun tr =>
  evt031PySub tr ∧ ∀ X, tr = P ++ X → SubLbl.finish 0 ∉ X

/-- A store that hangs after `P` allows `P` itself when the witness does. -/
theorem evt031HangsAfter_self {P : List (SubLbl Nat)} (h : evt031PySub P) :
    evt031HangsAfter P P := by
  refine ⟨h, fun X hX => ?_⟩
  rw [List.self_eq_append_right.mp hX]
  simp

/-- An overflow at the third append (capacity 2, batch size 4), then a receive that takes one of
the two events the channel holds and returns it: no receive is pending, one event is left. -/
def evt031PartialRun : List (SubLbl Nat) :=
  [.subscribe 0 subAll (some 2) 4, .op (.append 1), .op (.append 2), .op (.append 3), .await 0,
   .pull 0, .recv 0 [1]]

/-- The store allows a receive to take part of the channel after an overflow. -/
def Evt031DrainsPartlyAfterOverflow (S : SubSem Nat) : Prop := S evt031PartialRun

/-- ✗ A store whose stream hangs after a receive took part of the channel following an overflow
violates EVT-031 (line 5, at every later point where no receive is pending). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_partialHangs :
    Evt031DrainsPartlyAfterOverflow (evt031HangsAfter evt031PartialRun) ∧
      ¬ EVT_031 (evt031HangsAfter evt031PartialRun) := by
  have hr : evt031HangsAfter evt031PartialRun evt031PartialRun :=
    evt031HangsAfter_self (by decide)
  refine ⟨hr, fun h => ?_⟩
  obtain ⟨bs, hb⟩ := h.2.2.2.2.1 [.subscribe 0 subAll (some 2) 4, .op (.append 1), .op (.append 2)]
    3 [.await 0, .pull 0, .recv 0 [1]] 0 subAll 2 4 hr rfl rfl (by decide) (by decide) (by decide)
  exact hb.2 (evt031Recvs 0 bs ++ [.await 0, .finish 0]) (by simp [evt031PartialRun]) (by simp)

/-- A drop while the channel holds two events (batch size 2), then a receive that takes one of
them and returns it: no receive is pending, one event is left. -/
def evt031DropPartialRun : List (SubLbl Nat) :=
  [.subscribe 0 subAll (some 4) 2, .op (.append 1), .op (.append 2), .drop, .await 0, .pull 0,
   .recv 0 [1]]

/-- The store allows a receive to take part of the channel after the drop. -/
def Evt031DrainsPartlyAfterDrop (S : SubSem Nat) : Prop := S evt031DropPartialRun

/-- ✗ A store whose stream hangs after a receive took part of the channel following the drop
violates EVT-031 (line 10, at every later point where no receive is pending). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_dropPartialHangs :
    Evt031DrainsPartlyAfterDrop (evt031HangsAfter evt031DropPartialRun) ∧
      ¬ EVT_031 (evt031HangsAfter evt031DropPartialRun) := by
  have hr : evt031HangsAfter evt031DropPartialRun evt031DropPartialRun :=
    evt031HangsAfter_self (by decide)
  refine ⟨hr, fun h => ?_⟩
  obtain ⟨bs, hb⟩ := h.2.2.2.2.2.2.2.2.2.1
    [.subscribe 0 subAll (some 4) 2, .op (.append 1), .op (.append 2)]
    [.await 0, .pull 0, .recv 0 [1]] 0 hr rfl (by decide) (by decide)
  exact hb.2 (evt031Recvs 0 bs ++ [.await 0, .finish 0]) (by simp [evt031DropPartialRun]) (by simp)

/-- A run in which a receive takes two events from the channel and returns a batch holding only
the first: event 2 is appended while the channel has room, taken, and never received, and after
the drop the stream ends without it. -/
def evt031LossyRun : List (SubLbl Nat) :=
  [.subscribe 0 subAll (some 4) 2, .op (.append 1), .op (.append 2), .await 0, .pull 0, .pull 0,
   .recv 0 [1], .drop, .await 0, .finish 0]

/-- The witness, and besides its runs the lossy run. -/
def evt031Lossy : SubSem Nat := fun tr => evt031PySub tr ∨ tr = evt031LossyRun

/-- The store allows a receive to return fewer events than it took. -/
def Evt031LosesTaken (S : SubSem Nat) : Prop := S evt031LossyRun

/-- What the lossy run shows: the witness forbids it, subscription 0 received event 1 only,
although its receive took both matching events, and it had not ended before the drop. -/
theorem evt031LossyRun_facts :
    ¬ evt031PySub evt031LossyRun ∧ received 0 evt031LossyRun = [1] ∧
      matchingAfter 0 evt031LossyRun = [1, 2] ∧ pulls 0 evt031LossyRun = 2 ∧
      evt031Ended 0 (evt031LossyRun.take 7) = false := by
  decide

/-- ✗ A receive that takes an event from the channel and leaves it out of the batch it returns
(an off-by-one in the batch loop) violates EVT-031 (line 12, the fourth quoted sentence). -/
@[evidence mutant EVT_031]
theorem EVT_031_mutant_lossyBatch : Evt031LosesTaken evt031Lossy ∧ ¬ EVT_031 evt031Lossy := by
  refine ⟨Or.inr rfl, fun h => ?_⟩
  have := h.2.2.2.2.2.2.2.2.2.2.2 (evt031LossyRun.take 7) (evt031LossyRun.drop 7)
    (by rw [List.take_append_drop]; exact Or.inr rfl) 0 (by decide)
  revert this; decide

/-! ### The witness: what the lines leave open -/

/-- A drain after an overflow that takes every buffered event up to the batch size in one
receive, as the runtime's receive does. -/
def evt031GreedyRun : List (SubLbl Nat) :=
  [.subscribe 0 subAll (some 2) 4, .op (.append 1), .op (.append 2), .op (.append 3), .await 0,
   .pull 0, .pull 0, .recv 0 [1, 2], .await 0, .finish 0]

/-- The witness allows the greedy drain: after the overflow at the third append, one receive
returns both events the channel held, and the next reports the end (lines 5 and 6 allow any
batching of what the channel held). -/
@[evidence allows EVT_031]
theorem EVT_031_allows_greedy :
    evt031PySub evt031GreedyRun ∧
      evt031GreedyRun = [.subscribe 0 subAll (some 2) 4, .op (.append 1), .op (.append 2)] ++
        .op (.append 3) :: ([] ++ evt031Recvs 0 [[1, 2]] ++ [.await 0, .finish 0]) ∧
      2 ≤ backlog 0 ([.subscribe 0 subAll (some 2) 4, .op (.append 1), .op (.append 2)] :
        List (SubLbl Nat)) ∧
      evt031Held 0 ([.subscribe 0 subAll (some 2) 4, .op (.append 1), .op (.append 2)] :
        List (SubLbl Nat)) = [1, 2] := by
  refine ⟨by decide, rfl, by decide, by decide⟩

/-! ### Non-vacuity: the test derivation on the witness -/

/-- The test derivation on the witness, as a run: an event appended before the subscribe, a
subscription filtered to even events with capacity 4 and batch size 2, an odd and two even
events, one batch, a close and the end. -/
def evt031TestRun : List (SubLbl Nat) :=
  [.op (.append 0), .subscribe 0 subEven (some 4) 2, .op (.append 1), .op (.append 2),
   .op (.append 4), .await 0, .pull 0, .pull 0, .recv 0 [2, 4], .close 0, .await 0, .finish 0]

/-- The test derivation on the witness: the earlier event and the odd one are not delivered, the
two even events come in one batch of two, which is both events the receive took, and the close is
followed by the end. An overflow run
and a drop run meet the premises of lines 4 to 6 and 10 and 11: the backlog reaches the capacity
at the second append of a subscription that has not ended, its channel holds event 1, and the
receives take it before the end. -/
@[evidence nonvacuous EVT_031]
theorem EVT_031_nonvacuous :
    evt031PySub evt031TestRun ∧ appended (storeOps evt031TestRun) = [0, 1, 2, 4] ∧
      matchingAfter 0 evt031TestRun = [2, 4] ∧ batches 0 evt031TestRun = [[2, 4]] ∧
      pending 0 (evt031TestRun.take 9) = false ∧ pulls 0 (evt031TestRun.take 9) = 2 ∧
      evt031PySub subRunOverflow ∧ 1 ≤ backlog 0 (subRunOverflow.take 2) ∧
      evt031Ended 0 (subRunOverflow.take 2) = false ∧
      evt031Held 0 (subRunOverflow.take 2) = [1] ∧ received 0 subRunOverflow = [1] ∧
      evt031PySub subRunDrop ∧ evt031Ended 0 (subRunDrop.take 2) = false ∧
      evt031Held 0 (subRunDrop.take 2) = [1] ∧ received 0 subRunDrop = [1] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

end Libpetri.Spec
