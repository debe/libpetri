import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryStore

set_option linter.missingDocs true

/-!
# RefSub: live subscriptions to an event store

The witness model of the subscription lines of [EVT-024] (the debug stores' live tailing) and
[EVT-031] (live subscriptions with filters, batches and a bounded channel), over the store
vocabulary of `Spec/GlossaryStore.lean`.

## The observation: label sequences

A subscription is observed through the calls a caller makes and what they return, in the order
they happen. Each is a label (`SubLbl E`):

* `op o`: an operation on the store (`StoreOp`: an append, or a clear where the store has one);
  the store's own history is the projection `storeOps`;
* `subscribe i f c b`: a caller subscribes with the filter `f`, the channel capacity `c`
  (`none`: unbounded) and the batch size `b`; subscriptions are numbered `0, 1, 2, …` in the
  order they are made;
* `await i`: a receive on subscription `i` starts (Python's `__anext__` takes the receiver);
* `pull i`: the pending receive takes the oldest event out of the channel into the batch it is
  building (the runtime's `rx.recv()` returning an event);
* `recv i b`: the pending receive returns the batch `b`;
* `finish i`: the pending receive reports the end of the stream (`StopAsyncIteration`);
* `close i`: the caller closes subscription `i`;
* `drop`: the store is dropped.

A store with subscriptions is observed as the set of label sequences it allows, `SubSem E`.
Requirements are predicates over an abstract `S : SubSem E`, stated with the observation
functions below, which read a label sequence only: what subscription `i` received
(`batches`, `received`), the events appended after it subscribed (`appendsAfter`) and those of
them its filter matches (`matchingAfter`), how many events its receives took from the channel
(`pulls`, `backlog`), whether a receive is pending (`pending`), and whether the store was dropped
(`dropped`).

`pull` is a label of its own because the runtime's channel capacity counts only the events not
yet taken by a receive: a batch under construction has already left the channel
(rust/libpetri-py/src/events.rs, `__anext__`). Without it, the overflow condition would fire
earlier in the model than in the runtime.

## The reference (`refSub`)

`step C s l` is the effect of label `l` on the state `s` under the configuration `C`, or `none`
when the label is not possible there. The reference configuration (`SubCfg` with its defaults)
is the Python binding's store (rust/libpetri-py/src/events.rs, the only implementation of
[EVT-031], rulings D86 (a) and (d), D47 (c)):

* **append** never waits. It is delivered, in the store's lock and before the event is stored,
  to every subscription still registered whose filter matches it. A subscription whose channel
  is full, or whose receiver was closed, is unregistered instead (`try_send` fails and `retain`
  removes the sender): an overflow ends that subscription (D86 (a)), and its receiver still
  drains what the channel holds before it reports the end;
* **subscribe** registers an empty channel: no earlier event is delivered (forward-only). Batch
  size 0 and capacity 0 are rejected at the call, so they are not steps;
* **receive** (`await`, then `pull`s, then `recv` or `finish`): a batch is the non-empty run of
  events the receive took, at most `b` of them; the batch timeout decides when a batch with
  room returns, and it is not modelled (any moment is allowed). The receive reports the end once
  its batch is empty and either the receiver was closed or the channel is empty and the
  subscription is no longer registered;
* **close** with no receive pending drops the receiver and the events in its channel, so the next
  receive reports the end (D86 (d)). With a receive pending it changes nothing (the runtime's
  `try_lock` fails; clash evt-c#8), which D86 (d) leaves outside the requirement;
* **drop** unregisters every subscription; each still drains its channel, then reports the end.
  No operation and no subscribe follows a drop.

The debug stores of [EVT-024] (Java, TypeScript and Rust `DebugEventStore`) are the same model
restricted to their one subscribe form: every event matches, the channel is unbounded and each
delivery is one event (`SubLbl.DebugForm`, `refDebugSub`). Their cancel is not modelled: Rust's
`Subscription::cancel` does not unregister (rust/libpetri-debug/src/debug_event_store.rs), and
[EVT-024] has no line on it. Delivery there is one atomic step at the append, the order of
Rust (inside `append`) and TypeScript (the subscriber set taken at `append`); Java's broadcast
task reads the subscriber list later, so a subscriber added between an append and its broadcast
can receive that earlier event, which this model does not allow (ruling EVT-C4 (a) keeps only
the order of appends that do not overlap).

The wrong configurations are one switch each: an overflow that drops only the event that does
not fit (`Overflow.dropEvent`, the docstring's reading, ruling D86 (b)), an append that waits
for room (`Overflow.block`, back-pressure), a subscribe that seeds the channel with the earlier
matching events (`replay`), delivery that ignores the filter (`filters := false`), batches without
the size bound (`bounded := false`), and a close that does nothing (`closeEnds := false`).

## What the reference satisfies

* `refSub_received`: what subscription `i` received is a sublist of the matching events appended
  after it subscribed: in append order, each at most once, no earlier event. A subscription that
  was never made receives nothing (`refSub_batches_none`). The weak form of ruling EVT-C4 (a),
  a sublist of every appended event, is `refSub_received_appended`.
* `refSub_batch`: every batch is non-empty and holds at most the batch size.
* `refSub_overflow_ends`: after an append that finds the channel full (the backlog reached the
  capacity), the subscription receives no event appended from then on.
* `refSub_close_ends`: after a close with no receive pending, the subscription receives nothing.
* `refSub_append_enabled`: an append is always possible until the store is dropped.
* `refSub_dropped_no_op`: nothing is appended and nobody subscribes after a drop.
* Decided runs (`subRunTwo`, `subRunFilter`, `subRunOverflow`, `subRunClose`, `subRunDrop`, each
  with its `_facts`): two debug subscribers that both receive an event; a filtered, batched
  subscription that gets neither an earlier nor a non-matching event; an overflow whose channel
  is still drained before the end; a close followed by the end; a drop followed by the drain and
  the end. One decided run per wrong configuration (`subRun_dropEvent`, `subRun_block`,
  `subRun_replay`, `subRun_noFilter`, `subRun_unbounded`, `subRun_closeNoop`) shows it doing the
  wrong thing, for mutant evidence.

The proofs go through one run invariant (`Inv`, `InvAt`, proved by `inv_step` and `inv_run`) and
one frame lemma for a subscription that is unregistered or closed (`frame_step`, `drain`).
`refSub_split` cuts a reference run at a label. The trace theorems hold for every event type with
decidable equality; `refDebugSub tr` gives `refSub tr` by its first component.
-/

namespace Libpetri.Spec

variable {E : Type}

/-! ## Labels and the abstract observation -/

/-- A label of a run of a store with live subscriptions: a call a caller makes, or what a pending
receive returns. -/
inductive SubLbl (E : Type) where
  /-- An operation on the store: an append, or a clear where the store provides one. -/
  | op (o : StoreOp E)
  /-- Subscribe as subscription `id`, with the filter `filt`, the channel capacity `cap`
  (`none`: unbounded) and the batch size `bsz`. -/
  | subscribe (id : Nat) (filt : E → Bool) (cap : Option Nat) (bsz : Nat)
  /-- A receive on subscription `id` starts. -/
  | await (id : Nat)
  /-- The pending receive on `id` takes the oldest event out of the channel. -/
  | pull (id : Nat)
  /-- The pending receive on `id` returns the batch `batch`. -/
  | recv (id : Nat) (batch : List E)
  /-- The pending receive on `id` reports the end of the stream. -/
  | finish (id : Nat)
  /-- The caller closes subscription `id`. -/
  | close (id : Nat)
  /-- The store is dropped. -/
  | drop

/-- **Glossary: Live subscription semantics** (proposed term). A store with live subscriptions,
observed as the label sequences it allows. -/
abbrev SubSem (E : Type) := List (SubLbl E) → Prop

/-- The subscribe parameters a label gives subscription `i`, if it subscribes it. -/
def lblParams (i : Nat) : SubLbl E → Option ((E → Bool) × Option Nat × Nat)
  | .subscribe j f c b => if j = i then some (f, c, b) else none
  | _ => none

/-- The filter, capacity and batch size subscription `i` was made with in `tr`, if it was. -/
def subParams (i : Nat) (tr : List (SubLbl E)) : Option ((E → Bool) × Option Nat × Nat) :=
  tr.findSome? (lblParams i)

/-- The batch a label returns to subscription `i`, if it is a receive of `i` returning one. -/
def lblBatch (i : Nat) : SubLbl E → Option (List E)
  | .recv j b => if j = i then some b else none
  | _ => none

/-- The batches subscription `i` received in `tr`, in the order they were returned. -/
def batches (i : Nat) (tr : List (SubLbl E)) : List (List E) := tr.filterMap (lblBatch i)

/-- The events subscription `i` received in `tr`: its batches, concatenated. -/
def received (i : Nat) (tr : List (SubLbl E)) : List E := (batches i tr).flatten

/-- Whether a label is a take from the channel of subscription `i`. -/
def lblPull (i : Nat) : SubLbl E → Bool
  | .pull j => decide (j = i)
  | _ => false

/-- How many events the receives of subscription `i` took from its channel in `tr`. -/
def pulls (i : Nat) (tr : List (SubLbl E)) : Nat := tr.countP (lblPull i)

/-- The store operation a label makes, if any. -/
def lblOp : SubLbl E → Option (StoreOp E)
  | .op o => some o
  | _ => none

/-- The history of the store in `tr` (glossary `StoreOp`): its operations, oldest first. -/
def storeOps (tr : List (SubLbl E)) : List (StoreOp E) := tr.filterMap lblOp

/-- The labels of `tr` after the one that subscribes `i`; empty when `i` was not subscribed. -/
def afterSub (i : Nat) : List (SubLbl E) → List (SubLbl E)
  | [] => []
  | .subscribe j _ _ _ :: tr => if j = i then tr else afterSub i tr
  | _ :: tr => afterSub i tr

/-- The events appended after subscription `i` was made, in append order (glossary
`appended`); empty when `i` was not made. -/
def appendsAfter (i : Nat) (tr : List (SubLbl E)) : List E := appended (storeOps (afterSub i tr))

/-- The events appended after subscription `i` was made that its filter matches, in append
order. -/
def matchingAfter (i : Nat) (tr : List (SubLbl E)) : List E :=
  match subParams i tr with
  | some (f, _, _) => (appendsAfter i tr).filter f
  | none => []

/-- The matching events appended after subscription `i` was made that no receive took yet: the
events its channel holds while it is registered and its receiver is open. -/
def backlog (i : Nat) (tr : List (SubLbl E)) : Nat := (matchingAfter i tr).length - pulls i tr

/-- Whether a receive on `i` is pending after the labels so far, given whether it was before. -/
def lblPend (i : Nat) (p : Bool) : SubLbl E → Bool
  | .await j => if j = i then true else p
  | .recv j _ => if j = i then false else p
  | .finish j => if j = i then false else p
  | _ => p

/-- Whether a receive on subscription `i` is pending after `tr`: one started and has not yet
returned a batch or reported the end. -/
def pending (i : Nat) (tr : List (SubLbl E)) : Bool := tr.foldl (lblPend i) false

/-- Whether a label drops the store. -/
def lblDrop : SubLbl E → Bool
  | .drop => true
  | _ => false

/-- Whether the store was dropped in `tr`. -/
def dropped (tr : List (SubLbl E)) : Bool := tr.any lblDrop

/-- The one subscribe form of the debug stores ([EVT-024]): every event matches, the channel is
unbounded and every delivery is one event. Their cancel is not modelled, so no label closes. -/
def SubLbl.DebugForm : SubLbl E → Prop
  | .subscribe _ f c b => (∀ e, f e = true) ∧ c = none ∧ b = 1
  | .close _ => False
  | _ => True

/-! ## Observation lemmas -/

theorem subParams_append (i : Nat) (tr tr' : List (SubLbl E)) :
    subParams i (tr ++ tr') = (subParams i tr).or (subParams i tr') := by
  simp [subParams]

theorem batches_append (i : Nat) (tr tr' : List (SubLbl E)) :
    batches i (tr ++ tr') = batches i tr ++ batches i tr' := by
  simp [batches]

theorem received_append (i : Nat) (tr tr' : List (SubLbl E)) :
    received i (tr ++ tr') = received i tr ++ received i tr' := by
  simp [received, batches_append]

theorem pulls_append (i : Nat) (tr tr' : List (SubLbl E)) :
    pulls i (tr ++ tr') = pulls i tr + pulls i tr' := by
  simp [pulls]

theorem dropped_append (tr tr' : List (SubLbl E)) :
    dropped (tr ++ tr') = (dropped tr || dropped tr') := by
  simp [dropped]

theorem pending_snoc (i : Nat) (tr : List (SubLbl E)) (l : SubLbl E) :
    pending i (tr ++ [l]) = lblPend i (pending i tr) l := by
  simp [pending]

theorem subParams_cons (i : Nat) (l : SubLbl E) (tr : List (SubLbl E)) :
    subParams i (l :: tr) = (lblParams i l).or (subParams i tr) := by
  simp only [subParams, List.findSome?_cons]
  cases lblParams i l <;> rfl

theorem afterSub_none {i : Nat} {tr : List (SubLbl E)} (h : subParams i tr = none) :
    afterSub i tr = [] := by
  induction tr with
  | nil => rfl
  | cons l tr ih =>
    rw [subParams_cons] at h
    cases l with
    | subscribe j f c b =>
      by_cases hj : j = i
      · simp [lblParams, hj] at h
      · simp only [lblParams, hj, if_false, Option.none_or] at h
        simp only [afterSub, hj, if_false]
        exact ih h
    | _ => simp only [lblParams, Option.none_or] at h; exact ih h

theorem afterSub_append (i : Nat) (tr tr' : List (SubLbl E)) :
    afterSub i (tr ++ tr') =
      if (subParams i tr).isSome then afterSub i tr ++ tr' else afterSub i tr' := by
  induction tr with
  | nil => simp [subParams]
  | cons l tr ih =>
    cases l with
    | subscribe j f c b =>
      by_cases hj : j = i
      · simp [afterSub, subParams, lblParams, hj]
      · simpa [afterSub, subParams, lblParams, hj] using ih
    | _ => simpa [afterSub, subParams, lblParams] using ih

theorem appendsAfter_append (i : Nat) (tr tr' : List (SubLbl E)) :
    appendsAfter i (tr ++ tr') =
      if (subParams i tr).isSome then appendsAfter i tr ++ appended (storeOps tr')
      else appendsAfter i tr' := by
  unfold appendsAfter
  rw [afterSub_append]
  split <;> simp [storeOps, appended]

theorem afterSub_suffix (i : Nat) (tr : List (SubLbl E)) : afterSub i tr <:+ tr := by
  induction tr with
  | nil => exact List.suffix_refl _
  | cons l tr ih =>
    cases l with
    | subscribe j f c b =>
      by_cases hj : j = i
      · simp only [afterSub, hj, if_true]; exact List.suffix_cons _ _
      · simp only [afterSub, hj, if_false]; exact ih.trans (List.suffix_cons _ _)
    | _ => exact ih.trans (List.suffix_cons _ _)

/-- The events appended after subscription `i` was made are among the events appended in `tr`,
in the same order. -/
theorem appendsAfter_sublist (i : Nat) (tr : List (SubLbl E)) :
    List.Sublist (appendsAfter i tr) (appended (storeOps tr)) := by
  unfold appendsAfter appended storeOps
  exact (((afterSub_suffix i tr).sublist.filterMap _).filterMap _)

/-- The matching events appended after subscription `i` was made are among the events appended
in `tr`, in the same order. -/
theorem matchingAfter_sublist (i : Nat) (tr : List (SubLbl E)) :
    List.Sublist (matchingAfter i tr) (appended (storeOps tr)) := by
  unfold matchingAfter
  split
  · exact (List.filter_sublist).trans (appendsAfter_sublist i tr)
  · exact List.nil_sublist _

end Libpetri.Spec

namespace Libpetri.Reference

open Libpetri.Spec
open scoped List

variable {E : Type}

/-! ## The reference model -/

/-- What an append does to a registered subscription whose filter matches and whose channel is
full. -/
inductive Overflow where
  /-- The subscription is unregistered: it receives what its channel holds, then the end
  (ruling D86 (a), the reference). -/
  | endSub
  /-- Only the event that does not fit is lost; the subscription stays (ruling D86 (b), wrong). -/
  | dropEvent
  /-- The append waits for room (back-pressure, wrong). -/
  | block
  deriving DecidableEq, Repr

/-- The switches of the model. The defaults are the reference; each other value is one wrong
store. -/
structure SubCfg where
  /-- The overflow policy. -/
  overflow : Overflow := .endSub
  /-- A new subscription starts with the earlier matching events in its channel (wrong). -/
  replay : Bool := false
  /-- The filter decides delivery (`false`: every event is delivered, wrong). -/
  filters : Bool := true
  /-- A receive takes at most the batch size (`false`: no bound, wrong). -/
  bounded : Bool := true
  /-- A close with no receive pending drops the receiver (`false`: a close does nothing,
  wrong). -/
  closeEnds : Bool := true

/-- One subscription of the model. -/
structure Sub (E : Type) where
  /-- The filter. -/
  filt : E → Bool
  /-- The channel capacity (`none`: unbounded). -/
  cap : Option Nat
  /-- The batch size. -/
  bsz : Nat
  /-- The channel: events delivered and not yet taken by a receive, oldest first. -/
  chan : List E
  /-- The batch the pending receive has taken so far. -/
  cur : List E
  /-- The store still holds the subscription's sender (it is registered). -/
  linked : Bool
  /-- The receiver is still there (a close drops it). -/
  rx : Bool
  /-- A receive is pending. -/
  pending : Bool

/-- The state of the model: the store's history (glossary `StoreOp`), whether the store is still
there, the number of subscriptions made, and the subscriptions by number. -/
structure SubSt (E : Type) where
  /-- The store's operations, oldest first. -/
  hist : List (StoreOp E)
  /-- The store has not been dropped. -/
  alive : Bool
  /-- How many subscriptions were made; the next one is number `n`. -/
  n : Nat
  /-- Subscription `i`, if it was made. -/
  subs : Nat → Option (Sub E)

/-- The initial state: an empty store with no subscription. -/
def SubSt.init : SubSt E := ⟨[], true, 0, fun _ => none⟩

/-- Replace the subscription numbered `i`. -/
def updSub (f : Nat → Option (Sub E)) (i : Nat) (v : Sub E) : Nat → Option (Sub E) :=
  fun j => if j = i then some v else f j

/-- Whether the subscription's channel has room for one more event. -/
def Sub.room (u : Sub E) : Bool :=
  match u.cap with
  | none => true
  | some c => decide (u.chan.length < c)

/-- Whether the append of `e` concerns the subscription: it is registered and (with filters on)
its filter matches. -/
def Sub.takes (C : SubCfg) (e : E) (u : Sub E) : Bool := u.linked && (!C.filters || u.filt e)

/-- The append of `e` finds this subscription's open channel full. -/
def Sub.full (C : SubCfg) (e : E) (u : Sub E) : Bool := u.takes C e && u.rx && !u.room

/-- What the append of `e` does to one subscription. A registered subscription that takes it
gets it in its channel when the receiver is open and the channel has room. Otherwise the send
fails: a closed receiver unregisters the subscription, and a full channel applies the overflow
policy. -/
def deliver (C : SubCfg) (e : E) (u : Sub E) : Sub E :=
  if u.takes C e then
    if u.rx && u.room then { u with chan := u.chan ++ [e] }
    else if !u.rx then { u with linked := false }
    else match C.overflow with
      | .endSub => { u with linked := false }
      | .dropEvent => u
      | .block => u
  else u

/-- Apply `g` to subscription `i`, if it was made and `g` allows it. -/
def modSub (s : SubSt E) (i : Nat) (g : Sub E → Option (Sub E)) : Option (SubSt E) :=
  match s.subs i with
  | none => none
  | some u => (g u).map fun u' => { s with subs := updSub s.subs i u' }

/-- Whether the append of `e` would wait under the back-pressure policy: some subscription's open
channel is full. -/
def blocks (C : SubCfg) (s : SubSt E) (e : E) : Bool :=
  C.overflow == .block &&
    (List.range s.n).any fun i => match s.subs i with
      | some u => u.full C e
      | none => false

/-- One step of the model under the configuration `C`: the state after label `l`, or `none` when
`l` is not possible in `s`. -/
def step [DecidableEq E] (C : SubCfg) (s : SubSt E) : SubLbl E → Option (SubSt E)
  | .op o =>
    if !s.alive then none else
    match o with
    | .append e =>
      if blocks C s e then none
      else some { s with hist := s.hist ++ [o], subs := fun i => (s.subs i).map (deliver C e) }
    | .clear => some { s with hist := s.hist ++ [o] }
  | .subscribe i f c b =>
    if s.alive && decide (i = s.n) && decide (0 < b) && decide (c ≠ some 0) then
      some { s with n := s.n + 1,
                    subs := updSub s.subs i
                      ⟨f, c, b, if C.replay then (appended s.hist).filter f else [], [],
                        true, true, false⟩ }
    else none
  | .await i => modSub s i fun u => if u.pending then none else some { u with pending := true }
  | .pull i => modSub s i fun u =>
    if u.pending && u.rx && (!C.bounded || decide (u.cur.length < u.bsz)) then
      match u.chan with
      | [] => none
      | e :: r => some { u with chan := r, cur := u.cur ++ [e] }
    else none
  | .recv i b => modSub s i fun u =>
    if u.pending && !u.cur.isEmpty && decide (b = u.cur) then
      some { u with cur := [], pending := false }
    else none
  | .finish i => modSub s i fun u =>
    if u.pending && u.cur.isEmpty && (!u.rx || (u.chan.isEmpty && !u.linked)) then
      some { u with pending := false }
    else none
  | .close i => modSub s i fun u =>
    if u.pending || !C.closeEnds then some u else some { u with rx := false, chan := [] }
  | .drop =>
    if s.alive then
      some { s with alive := false, subs := fun i => (s.subs i).map fun u => { u with linked := false } }
    else none

/-- Run the labels `tr` from `s`: the state after them, or `none` if one is not possible. -/
def run [DecidableEq E] (C : SubCfg) : SubSt E → List (SubLbl E) → Option (SubSt E)
  | s, [] => some s
  | s, l :: tr => (step C s l).bind fun s' => run C s' tr

/-- The label sequences the model allows under `C`, from the initial state. -/
def subSem [DecidableEq E] (C : SubCfg) : SubSem E := fun tr => (run C SubSt.init tr).isSome

/-- **The reference store with live subscriptions** ([EVT-031], and [EVT-024] through
`refDebugSub`): the model under the reference configuration. -/
def refSub [DecidableEq E] : SubSem E := subSem {}

#spec_witness refSub

instance [DecidableEq E] (C : SubCfg) (tr : List (SubLbl E)) : Decidable (subSem C tr) :=
  inferInstanceAs (Decidable ((run C SubSt.init tr).isSome = true))

instance [DecidableEq E] (tr : List (SubLbl E)) : Decidable (refSub tr) :=
  inferInstanceAs (Decidable (subSem {} tr))

/-- The reference debug store ([EVT-024]): the reference restricted to the debug stores'
subscribe form (every event matches, unbounded channel, one event per delivery, no close). -/
def refDebugSub [DecidableEq E] : SubSem E := fun tr => refSub tr ∧ ∀ l ∈ tr, l.DebugForm

#spec_witness refDebugSub

/-! ## Run lemmas -/

theorem run_append [DecidableEq E] (C : SubCfg) (s : SubSt E) (tr tr' : List (SubLbl E)) :
    run C s (tr ++ tr') = (run C s tr).bind fun s' => run C s' tr' := by
  induction tr generalizing s with
  | nil => simp [run]
  | cons l tr ih =>
    simp only [List.cons_append, run]
    cases step C s l <;> simp [ih]

theorem run_snoc [DecidableEq E] (C : SubCfg) (s : SubSt E) (tr : List (SubLbl E))
    (l : SubLbl E) : run C s (tr ++ [l]) = (run C s tr).bind fun s' => step C s' l := by
  rw [run_append]
  cases run C s tr <;> simp [run]

/-! ## Single-label observation lemmas -/

theorem subParams_snoc (i : Nat) (tr : List (SubLbl E)) (l : SubLbl E) :
    subParams i (tr ++ [l]) = (subParams i tr).or (lblParams i l) := by
  rw [subParams_append, subParams_cons]; simp [subParams]

theorem batches_snoc (i : Nat) (tr : List (SubLbl E)) (l : SubLbl E) :
    batches i (tr ++ [l]) = batches i tr ++ (lblBatch i l).toList := by
  rw [batches_append]; simp only [batches, List.filterMap_cons, List.filterMap_nil]
  cases lblBatch i l <;> rfl

theorem received_snoc (i : Nat) (tr : List (SubLbl E)) (l : SubLbl E) :
    received i (tr ++ [l]) = received i tr ++ (lblBatch i l).getD [] := by
  simp only [received, batches_snoc, List.flatten_append]
  cases lblBatch i l <;> simp

theorem pulls_snoc (i : Nat) (tr : List (SubLbl E)) (l : SubLbl E) :
    pulls i (tr ++ [l]) = pulls i tr + if lblPull i l then 1 else 0 := by
  rw [pulls_append]; simp [pulls, List.countP_cons]

theorem appendsAfter_snoc (i : Nat) (tr : List (SubLbl E)) (l : SubLbl E) :
    appendsAfter i (tr ++ [l]) =
      if (subParams i tr).isSome then appendsAfter i tr ++ appended (storeOps [l]) else [] := by
  rw [appendsAfter_append]
  split
  · rfl
  · cases l <;> simp [appendsAfter, afterSub, storeOps, appended]

theorem received_cons (i : Nat) (l : SubLbl E) (tr : List (SubLbl E)) :
    received i (l :: tr) = (lblBatch i l).getD [] ++ received i tr := by
  rw [show l :: tr = [l] ++ tr from rfl, received_append]
  simp only [received, batches, List.filterMap_cons, List.filterMap_nil]
  cases lblBatch i l <;> simp

/-! ## The invariant of a reference run -/

/-- No subscription is numbered `n` or above. -/
def Fresh (s : SubSt E) : Prop := ∀ k, s.n ≤ k → s.subs k = none

/-- The invariant of a reference run for one subscription, relating its state to the labels. -/
structure InvAt (tr : List (SubLbl E)) (i : Nat) (u : Sub E) : Prop where
  /-- The subscription's parameters are those it subscribed with. -/
  params : subParams i tr = some (u.filt, u.cap, u.bsz)
  /-- The batch size is positive. -/
  bsz_pos : 0 < u.bsz
  /-- What it received, its batch under way and its channel are a sublist of the matching
  events appended since it subscribed. -/
  sub : received i tr ++ u.cur ++ u.chan <+ (appendsAfter i tr).filter u.filt
  /-- While registered with an open receiver, they are exactly those events. -/
  eq : u.linked = true → u.rx = true →
    received i tr ++ u.cur ++ u.chan = (appendsAfter i tr).filter u.filt
  /-- Its receives took exactly the events received and those of the batch under way. -/
  pulled : (received i tr ++ u.cur).length = pulls i tr
  /-- A receive is pending exactly when the labels say so. -/
  pend : u.pending = pending i tr
  /-- No batch is under way without a pending receive. -/
  idle : u.pending = false → u.cur = []
  /-- The batch under way fits the batch size. -/
  curLe : u.cur.length ≤ u.bsz
  /-- Every batch received is non-empty and fits the batch size. -/
  batch : ∀ b ∈ batches i tr, b ≠ [] ∧ b.length ≤ u.bsz
  /-- A closed receiver holds no event. -/
  closed : u.rx = false → u.chan = []

/-- The invariant of a reference run. -/
structure Inv (tr : List (SubLbl E)) (s : SubSt E) : Prop where
  /-- The store is there exactly while it was not dropped. -/
  alive : s.alive = !dropped tr
  /-- No subscription is numbered at or above the count. -/
  fresh : Fresh s
  /-- A subscription not made has no parameters, batches, takes or pending receive. -/
  none_ : ∀ i, s.subs i = none →
    subParams i tr = none ∧ batches i tr = [] ∧ pulls i tr = 0 ∧ pending i tr = false
  /-- Every subscription made meets the invariant `InvAt`. -/
  some_ : ∀ i u, s.subs i = some u → InvAt tr i u

theorem inv_init : Inv ([] : List (SubLbl E)) SubSt.init where
  alive := rfl
  fresh := fun _ _ => rfl
  none_ := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
  some_ := fun _ _ h => by simp [SubSt.init] at h

/-- A label that changes no observation of subscription `i`. -/
structure Quiet (i : Nat) (l : SubLbl E) : Prop where
  /-- It does not subscribe `i`. -/
  params : lblParams i l = none
  /-- It returns no batch to `i`. -/
  batch : lblBatch i l = none
  /-- It takes nothing from the channel of `i`. -/
  pull : lblPull i l = false
  /-- It appends nothing. -/
  ops : appended (storeOps [l]) = []
  /-- It starts and ends no receive of `i`. -/
  pend : ∀ p, lblPend i p l = p

theorem quiet_of_ne {i j : Nat} (h : j ≠ i) :
    ∀ l : SubLbl E, (l = .await j ∨ l = .pull j ∨ (∃ b, l = .recv j b) ∨ l = .finish j ∨
      l = .close j ∨ ∃ f c b, l = .subscribe j f c b) → Quiet i l := by
  intro l hl
  rcases hl with rfl | rfl | ⟨b, rfl⟩ | rfl | rfl | ⟨f, c, b, rfl⟩ <;>
    exact ⟨by simp [lblParams, h], by simp [lblBatch, h], by simp [lblPull, h],
      by simp [storeOps, lblOp, appended], by simp [lblPend, h]⟩

theorem quiet_close (i j : Nat) : Quiet i (SubLbl.close j : SubLbl E) :=
  ⟨rfl, rfl, rfl, by simp [storeOps, lblOp, appended], fun _ => rfl⟩

theorem quiet_drop (i : Nat) : Quiet i (SubLbl.drop : SubLbl E) :=
  ⟨rfl, rfl, rfl, by simp [storeOps, lblOp, appended], fun _ => rfl⟩

theorem quiet_clear (i : Nat) : Quiet i (SubLbl.op .clear : SubLbl E) :=
  ⟨rfl, rfl, rfl, by simp [storeOps, lblOp, appended], fun _ => rfl⟩

theorem invAt_quiet {tr : List (SubLbl E)} {i : Nat} {l : SubLbl E} {u : Sub E}
    (hq : Quiet i l) (h : InvAt tr i u) : InvAt (tr ++ [l]) i u := by
  have hA : appendsAfter i (tr ++ [l]) = appendsAfter i tr := by
    rw [appendsAfter_snoc, h.params, hq.ops]; simp
  have hR : received i (tr ++ [l]) = received i tr := by rw [received_snoc, hq.batch]; simp
  exact {
    params := by rw [subParams_snoc, h.params, hq.params]; rfl
    bsz_pos := h.bsz_pos
    sub := by rw [hA, hR]; exact h.sub
    eq := by rw [hA, hR]; exact h.eq
    pulled := by rw [hR, pulls_snoc, hq.pull, h.pulled]; simp
    pend := by rw [pending_snoc, hq.pend, h.pend]
    idle := h.idle
    curLe := h.curLe
    batch := by rw [batches_snoc, hq.batch]; simpa using h.batch
    closed := h.closed }

theorem none_quiet {tr : List (SubLbl E)} {i : Nat} {l : SubLbl E} (hq : Quiet i l)
    (h : subParams i tr = none ∧ batches i tr = [] ∧ pulls i tr = 0 ∧ pending i tr = false) :
    subParams i (tr ++ [l]) = none ∧ batches i (tr ++ [l]) = [] ∧ pulls i (tr ++ [l]) = 0 ∧
      pending i (tr ++ [l]) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [subParams_snoc, h.1, hq.params]; rfl
  · rw [batches_snoc, h.2.1, hq.batch]; rfl
  · rw [pulls_snoc, h.2.2.1, hq.pull]; rfl
  · rw [pending_snoc, hq.pend, h.2.2.2]

theorem modSub_eq_some {s s' : SubSt E} {j : Nat} {g : Sub E → Option (Sub E)}
    (h : modSub s j g = some s') :
    ∃ u u', s.subs j = some u ∧ g u = some u' ∧
      s' = { s with subs := updSub s.subs j u' } := by
  unfold modSub at h
  split at h
  · cases h
  · rename_i u hu
    cases hg : g u with
    | none => simp [hg] at h
    | some u' => simp [hg] at h; exact ⟨u, u', hu, hg, h.symm⟩

theorem updSub_self (f : Nat → Option (Sub E)) (i : Nat) (v : Sub E) : updSub f i v i = some v := by
  simp [updSub]

theorem updSub_ne (f : Nat → Option (Sub E)) {i j : Nat} (v : Sub E) (h : j ≠ i) :
    updSub f j v i = f i := by
  simp [updSub, Ne.symm h]

/-- A step on subscription `j` through `modSub`: the invariant carries over to every other
subscription, given the invariant of the changed one. -/
theorem inv_modSub {tr : List (SubLbl E)} {s : SubSt E} {j : Nat} {l : SubLbl E}
    {u u' : Sub E} (hI : Inv tr s) (hu : s.subs j = some u)
    (hq : ∀ i, j ≠ i → Quiet i l) (hd : dropped [l] = false)
    (hj : InvAt (tr ++ [l]) j u') :
    Inv (tr ++ [l]) { s with subs := updSub s.subs j u' } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [dropped_append, hd, hI.alive]
  · intro k hk
    have hjk : j ≠ k := by
      rintro rfl; have := hI.fresh j hk; simp [hu] at this
    simp only [updSub_ne _ _ hjk]; exact hI.fresh k hk
  · intro i hi
    by_cases hji : j = i
    · subst hji; simp [updSub_self] at hi
    · simp only [updSub_ne _ _ hji] at hi
      exact none_quiet (hq i hji) (hI.none_ i hi)
  · intro i v hv
    by_cases hji : j = i
    · subst hji; simp [updSub_self] at hv; subst hv; exact hj
    · simp only [updSub_ne _ _ hji] at hv
      exact invAt_quiet (hq i hji) (hI.some_ i v hv)


/-- The three things a reference append does to one subscription. -/
theorem deliver_cases (e : E) (u : Sub E) :
    (deliver {} e u = { u with chan := u.chan ++ [e] } ∧ u.linked = true ∧ u.filt e = true ∧
        u.rx = true ∧ u.room = true) ∨
      deliver {} e u = { u with linked := false } ∨
      (deliver {} e u = u ∧ (u.linked = true → u.filt e = false)) := by
  unfold deliver Sub.takes
  by_cases hl : u.linked = true <;> by_cases hf : u.filt e = true <;>
    by_cases hr : u.rx = true <;> by_cases hm : u.room = true <;> simp_all

theorem invAt_append {tr : List (SubLbl E)} {i : Nat} {u : Sub E} (e : E)
    (h : InvAt tr i u) : InvAt (tr ++ [.op (.append e)]) i (deliver {} e u) := by
  have hA : appendsAfter i (tr ++ [.op (.append e)]) = appendsAfter i tr ++ [e] := by
    rw [appendsAfter_snoc, h.params]; simp [storeOps, lblOp, appended]
  have hR : received i (tr ++ [.op (.append e)]) = received i tr := by
    rw [received_snoc]; simp [lblBatch]
  have base : ∀ v : Sub E, v.filt = u.filt → v.cap = u.cap → v.bsz = u.bsz → v.cur = u.cur →
      v.pending = u.pending → (v.rx = false → v.chan = []) →
      received i tr ++ v.cur ++ v.chan <+ (appendsAfter i tr ++ [e]).filter v.filt →
      (v.linked = true → v.rx = true →
        received i tr ++ v.cur ++ v.chan = (appendsAfter i tr ++ [e]).filter v.filt) →
      InvAt (tr ++ [.op (.append e)]) i v := by
    intro v hf hc hb hcu hp hcl hs heq
    exact {
      params := by rw [subParams_snoc, h.params, hf, hc, hb]; rfl
      bsz_pos := hb ▸ h.bsz_pos
      sub := by rw [hA, hR]; exact hs
      eq := by rw [hA, hR]; exact heq
      pulled := by rw [hR, pulls_snoc, hcu]; simpa [lblPull] using h.pulled
      pend := by rw [pending_snoc, hp, h.pend]; rfl
      idle := by rw [hp, hcu]; exact h.idle
      curLe := by rw [hcu, hb]; exact h.curLe
      batch := by rw [batches_snoc, hb]; simpa [lblBatch] using h.batch
      closed := hcl }
  rcases deliver_cases e u with ⟨hd, hl, hf, hr, -⟩ | hd | ⟨hd, hn⟩ <;> rw [hd]
  · refine base _ rfl rfl rfl rfl rfl (by simp [hr]) ?_ ?_
    · simpa [List.filter_append, hf, List.append_assoc] using h.sub.append (List.Sublist.refl [e])
    · intro _ _; rw [List.filter_append, ← h.eq hl hr]; simp [hf]
  · refine base _ rfl rfl rfl rfl rfl h.closed ?_ (by simp)
    exact h.sub.trans (by simp [List.filter_append])
  · refine base _ rfl rfl rfl rfl rfl h.closed ?_ ?_
    · exact h.sub.trans (by simp [List.filter_append])
    · intro hl hr; rw [List.filter_append, h.eq hl hr]; simp [hn hl]

theorem inv_step [DecidableEq E] {tr : List (SubLbl E)} {s s' : SubSt E} {l : SubLbl E}
    (hI : Inv tr s) (h : step {} s l = some s') : Inv (tr ++ [l]) s' := by
  cases l with
  | await j =>
    obtain ⟨u, u', hu, hg, rfl⟩ := modSub_eq_some h
    have hp : u.pending = false := by
      cases hpu : u.pending <;> simp_all
    have hu' : u' = { u with pending := true } := by simp_all
    subst hu'
    refine inv_modSub hI hu (fun i hji => quiet_of_ne hji _ (Or.inl rfl)) rfl ?_
    have hJ := hI.some_ j u hu
    have hA : appendsAfter j (tr ++ [SubLbl.await j]) = appendsAfter j tr := by
      rw [appendsAfter_snoc, hJ.params]; simp [storeOps, lblOp, appended]
    have hR : received j (tr ++ [SubLbl.await j]) = received j tr := by
      rw [received_snoc]; simp [lblBatch]
    exact {
      params := by rw [subParams_snoc, hJ.params]; rfl
      bsz_pos := hJ.bsz_pos
      sub := by rw [hA, hR]; exact hJ.sub
      eq := by rw [hA, hR]; exact hJ.eq
      pulled := by rw [hR, pulls_snoc]; simpa [lblPull] using hJ.pulled
      pend := by rw [pending_snoc]; simp [lblPend]
      idle := by simp
      curLe := hJ.curLe
      batch := by rw [batches_snoc]; simpa [lblBatch] using hJ.batch
      closed := hJ.closed }
  | pull j =>
    obtain ⟨u, u', hu, hg, rfl⟩ := modSub_eq_some h
    have hJ := hI.some_ j u hu
    split at hg
    · rename_i hc
      simp at hc
      obtain ⟨⟨hp, hrx⟩, hlt⟩ := hc
      split at hg
      · cases hg
      · rename_i e r hch
        simp at hg; subst hg
        refine inv_modSub hI hu (fun i hji => quiet_of_ne hji _ (Or.inr (Or.inl rfl))) rfl ?_
        have hA : appendsAfter j (tr ++ [SubLbl.pull j]) = appendsAfter j tr := by
          rw [appendsAfter_snoc, hJ.params]; simp [storeOps, lblOp, appended]
        have hR : received j (tr ++ [SubLbl.pull j]) = received j tr := by
          rw [received_snoc]; simp [lblBatch]
        have hl : received j tr ++ (u.cur ++ [e]) ++ r = received j tr ++ u.cur ++ u.chan := by
          simp [hch]
        exact {
          params := by rw [subParams_snoc, hJ.params]; rfl
          bsz_pos := hJ.bsz_pos
          sub := by rw [hA, hR]; dsimp only; rw [hl]; exact hJ.sub
          eq := by rw [hA, hR]; dsimp only; rw [hl]; exact hJ.eq
          pulled := by
            rw [hR, pulls_snoc]; simp only [lblPull, decide_true, if_true]
            rw [← hJ.pulled]; simp; omega
          pend := by rw [pending_snoc, ← hJ.pend]; simp [lblPend, hp]
          idle := by simp [hp]
          curLe := by simp; omega
          batch := by rw [batches_snoc]; simpa [lblBatch] using hJ.batch
          closed := by simp [hrx] }
    · cases hg
  | recv j b =>
    obtain ⟨u, u', hu, hg, rfl⟩ := modSub_eq_some h
    have hJ := hI.some_ j u hu
    split at hg
    · rename_i hc
      simp at hc
      obtain ⟨⟨hp, hne⟩, rfl⟩ := hc
      simp at hg; subst hg
      refine inv_modSub hI hu (fun i hji => quiet_of_ne hji _ (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
        rfl ?_
      have hA : appendsAfter j (tr ++ [SubLbl.recv j u.cur]) = appendsAfter j tr := by
        rw [appendsAfter_snoc, hJ.params]; simp [storeOps, lblOp, appended]
      have hR : received j (tr ++ [SubLbl.recv j u.cur]) = received j tr ++ u.cur := by
        rw [received_snoc]; simp [lblBatch]
      exact {
        params := by rw [subParams_snoc, hJ.params]; rfl
        bsz_pos := hJ.bsz_pos
        sub := by rw [hA, hR]; simpa using hJ.sub
        eq := by rw [hA, hR]; simpa using hJ.eq
        pulled := by rw [hR, pulls_snoc]; simpa [lblPull] using hJ.pulled
        pend := by rw [pending_snoc]; simp [lblPend]
        idle := by simp
        curLe := by simp
        batch := by
          rw [batches_snoc]; simp only [lblBatch, if_true, Option.toList_some, List.mem_append,
            List.mem_singleton]
          rintro b (hb | rfl)
          · exact hJ.batch b hb
          · exact ⟨hne, hJ.curLe⟩
        closed := hJ.closed }
    · cases hg
  | finish j =>
    obtain ⟨u, u', hu, hg, rfl⟩ := modSub_eq_some h
    have hJ := hI.some_ j u hu
    split at hg
    · rename_i hc
      simp at hc
      obtain ⟨⟨hp, hc0⟩, -⟩ := hc
      simp at hg; subst hg
      refine inv_modSub hI hu (fun i hji => quiet_of_ne hji _ (Or.inr (Or.inr (Or.inr
        (Or.inl rfl))))) rfl ?_
      have hA : appendsAfter j (tr ++ [SubLbl.finish j]) = appendsAfter j tr := by
        rw [appendsAfter_snoc, hJ.params]; simp [storeOps, lblOp, appended]
      have hR : received j (tr ++ [SubLbl.finish j]) = received j tr := by
        rw [received_snoc]; simp [lblBatch]
      exact {
        params := by rw [subParams_snoc, hJ.params]; rfl
        bsz_pos := hJ.bsz_pos
        sub := by rw [hA, hR]; exact hJ.sub
        eq := by rw [hA, hR]; exact hJ.eq
        pulled := by rw [hR, pulls_snoc]; simpa [lblPull] using hJ.pulled
        pend := by rw [pending_snoc]; simp [lblPend]
        idle := fun _ => hc0
        curLe := hJ.curLe
        batch := by rw [batches_snoc]; simpa [lblBatch] using hJ.batch
        closed := hJ.closed }
    · cases hg
  | close j =>
    obtain ⟨u, u', hu, hg, rfl⟩ := modSub_eq_some h
    have hJ := hI.some_ j u hu
    have hq := quiet_close (E := E)
    refine inv_modSub hI hu (fun i _ => hq i j) rfl ?_
    have h1 := invAt_quiet (hq j j) hJ
    split at hg
    · simp at hg; subst hg; exact h1
    · simp at hg; subst hg
      exact { h1 with
        sub := List.Sublist.trans (by simp) h1.sub
        eq := by simp
        closed := by simp }
  | op o =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i halive
      cases o with
      | clear =>
        simp at h; subst h
        exact ⟨by simp [dropped, lblDrop, hI.alive], hI.fresh,
          fun i hi => none_quiet (quiet_clear i) (hI.none_ i hi),
          fun i u hu => invAt_quiet (quiet_clear i) (hI.some_ i u hu)⟩
      | append e =>
        simp [blocks] at h; subst h
        refine ⟨by simp [dropped, lblDrop, hI.alive], ?_, ?_, ?_⟩
        · intro k hk; simp [hI.fresh k hk]
        · intro i hi
          simp only [Option.map_eq_none_iff] at hi
          have hn := hI.none_ i hi
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [subParams_snoc, hn.1]; rfl
          · rw [batches_snoc, hn.2.1]; rfl
          · rw [pulls_snoc, hn.2.2.1]; rfl
          · rw [pending_snoc, hn.2.2.2]; rfl
        · intro i v hv
          simp only [Option.map_eq_some_iff] at hv
          obtain ⟨u, hu, rfl⟩ := hv
          exact invAt_append e (hI.some_ i u hu)
  | subscribe j f c b =>
    simp only [step] at h
    split at h
    · rename_i hc
      simp at hc
      obtain ⟨⟨⟨halive, rfl⟩, hb⟩, hc0⟩ := hc
      simp at h; subst h
      have hjn : s.subs s.n = none := hI.fresh _ (Nat.le_refl _)
      have hn := hI.none_ _ hjn
      refine ⟨by simp [dropped, lblDrop, hI.alive], ?_, ?_, ?_⟩
      · intro k hk
        simp only at hk
        have : s.n ≠ k := by omega
        simp only [updSub_ne _ _ this]; exact hI.fresh k (by omega)
      · intro i hi
        by_cases hji : s.n = i
        · subst hji; simp [updSub_self] at hi
        · simp only [updSub_ne _ _ hji] at hi
          exact none_quiet (quiet_of_ne hji _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨f, c, b, rfl⟩)))))) (hI.none_ i hi)
      · intro i v hv
        by_cases hji : s.n = i
        · subst hji; simp [updSub_self] at hv; subst hv
          have hR : received s.n (tr ++ [SubLbl.subscribe s.n f c b]) = [] := by
            rw [received_snoc]; simp [received, hn.2.1, lblBatch]
          exact {
            params := by rw [subParams_snoc, hn.1]; simp [lblParams]
            bsz_pos := hb
            sub := by rw [hR]; simp
            eq := by intro _ _; rw [hR, appendsAfter_snoc, hn.1]; simp
            pulled := by rw [hR, pulls_snoc, hn.2.2.1]; simp [lblPull]
            pend := by rw [pending_snoc, hn.2.2.2]; simp [lblPend]
            idle := by simp
            curLe := by simp
            batch := by rw [batches_snoc, hn.2.1]; simp [lblBatch]
            closed := by simp }
        · simp only [updSub_ne _ _ hji] at hv
          exact invAt_quiet (quiet_of_ne hji _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨f, c, b, rfl⟩)))))) (hI.some_ i v hv)
    · cases h
  | drop =>
    simp only [step] at h
    split at h
    · simp at h; subst h
      refine ⟨by simp [dropped, lblDrop], ?_, ?_, ?_⟩
      · intro k hk; simp [hI.fresh k hk]
      · intro i hi
        simp only [Option.map_eq_none_iff] at hi
        exact none_quiet (quiet_drop i) (hI.none_ i hi)
      · intro i v hv
        simp only [Option.map_eq_some_iff] at hv
        obtain ⟨u, hu, rfl⟩ := hv
        have h1 := invAt_quiet (quiet_drop i) (hI.some_ i u hu)
        exact { h1 with eq := by simp }
    · cases h

theorem inv_run_from [DecidableEq E] {pre tr : List (SubLbl E)} {s s' : SubSt E}
    (hI : Inv pre s) (h : run {} s tr = some s') : Inv (pre ++ tr) s' := by
  induction tr generalizing pre s with
  | nil => simp [run] at h; subst h; simpa using hI
  | cons l tr ih =>
    simp only [run] at h
    cases h1 : step {} s l with
    | none => simp [h1] at h
    | some s1 =>
      simp [h1] at h
      simpa using ih (inv_step hI h1) h

theorem inv_run [DecidableEq E] {tr : List (SubLbl E)} {s : SubSt E}
    (h : run {} SubSt.init tr = some s) : Inv tr s := by
  simpa using inv_run_from inv_init h

theorem refSub_run [DecidableEq E] {tr : List (SubLbl E)} (h : refSub tr) :
    ∃ s, run {} SubSt.init tr = some s ∧ Inv tr s := by
  unfold refSub subSem at h
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
  exact ⟨s, hs, inv_run hs⟩

theorem modSub_other {s s' : SubSt E} {j i : Nat} {g : Sub E → Option (Sub E)}
    (h : modSub s j g = some s') (hji : j ≠ i) : s'.subs i = s.subs i := by
  obtain ⟨u, u', -, -, rfl⟩ := modSub_eq_some h
  exact updSub_ne _ _ hji

theorem modSub_self {s s' : SubSt E} {j : Nat} {g : Sub E → Option (Sub E)} {u : Sub E}
    (h : modSub s j g = some s') (hu : s.subs j = some u) :
    ∃ u', g u = some u' ∧ s'.subs j = some u' := by
  obtain ⟨u0, u', hu0, hg, rfl⟩ := modSub_eq_some h
  rw [hu] at hu0; cases hu0
  exact ⟨u', hg, updSub_self _ _ _⟩

/-- One reference step on a subscription that is unregistered or whose receiver is closed: it
stays so, and what the step returns to it together with what it still holds is a sublist of what
it held. -/
theorem frame_step [DecidableEq E] {tr : List (SubLbl E)} {s s' : SubSt E} {l : SubLbl E}
    {i : Nat} {u : Sub E} (hI : Inv tr s) (h : step {} s l = some s')
    (hu : s.subs i = some u) (hend : u.linked = false ∨ u.rx = false) :
    ∃ u', s'.subs i = some u' ∧ (u'.linked = false ∨ u'.rx = false) ∧
      (lblBatch i l).getD [] ++ u'.cur ++ u'.chan <+ u.cur ++ u.chan := by
  -- labels on another subscription leave `i` alone
  have other : ∀ j g, j ≠ i → modSub s j g = some s' → lblBatch i l = none →
      ∃ u', s'.subs i = some u' ∧ (u'.linked = false ∨ u'.rx = false) ∧
        (lblBatch i l).getD [] ++ u'.cur ++ u'.chan <+ u.cur ++ u.chan := by
    intro j g hji hm hb
    exact ⟨u, by rw [modSub_other hm hji, hu], hend, by simp [hb]⟩
  cases l with
  | op o =>
    simp only [step] at h
    split at h
    · cases h
    · cases o with
      | clear => simp at h; subst h; exact ⟨u, hu, hend, by simp [lblBatch]⟩
      | append e =>
        simp [blocks] at h; subst h
        refine ⟨deliver {} e u, by simp [hu], ?_⟩
        rcases deliver_cases e u with ⟨-, hl, -, hr, -⟩ | hd | ⟨hd, -⟩
        · rcases hend with h' | h' <;> simp_all
        · rw [hd]; simp [lblBatch]
        · rw [hd]; simp [lblBatch, hend]
  | subscribe j f c b =>
    simp only [step] at h
    split at h
    · rename_i hc
      simp at hc
      obtain ⟨⟨⟨-, rfl⟩, -⟩, -⟩ := hc
      simp at h; subst h
      have hji : s.n ≠ i := by
        rintro rfl; rw [hI.fresh _ (Nat.le_refl _)] at hu; cases hu
      exact ⟨u, by simp [updSub_ne _ _ hji, hu], hend, by simp [lblBatch]⟩
    · cases h
  | await j =>
    by_cases hji : j = i
    · subst hji
      obtain ⟨u', hg, hs⟩ := modSub_self h hu
      have : u' = { u with pending := true } := by
        cases hp : u.pending <;> simp_all
      subst this
      exact ⟨_, hs, hend, by simp [lblBatch]⟩
    · exact other _ _ hji h (by simp [lblBatch])
  | pull j =>
    by_cases hji : j = i
    · subst hji
      obtain ⟨u', hg, hs⟩ := modSub_self h hu
      split at hg
      · rename_i hc
        simp at hc
        split at hg
        · cases hg
        · rename_i e r hch
          simp at hg; subst hg
          refine ⟨_, hs, by simp_all, ?_⟩
          simp [lblBatch, hch]
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
        exact ⟨_, hs, hend, by simp [lblBatch]⟩
      · cases hg
    · exact other _ _ hji h (by simp [lblBatch, hji])
  | finish j =>
    by_cases hji : j = i
    · subst hji
      obtain ⟨u', hg, hs⟩ := modSub_self h hu
      split at hg
      · simp at hg; subst hg
        exact ⟨_, hs, hend, by simp [lblBatch]⟩
      · cases hg
    · exact other _ _ hji h (by simp [lblBatch])
  | close j =>
    by_cases hji : j = i
    · subst hji
      obtain ⟨u', hg, hs⟩ := modSub_self h hu
      split at hg
      · simp at hg; subst hg
        exact ⟨_, hs, hend, by simp [lblBatch]⟩
      · simp at hg; subst hg
        exact ⟨_, hs, Or.inr rfl, by simp [lblBatch]⟩
    · exact other _ _ hji h (by simp [lblBatch])
  | drop =>
    simp only [step] at h
    split at h
    · simp at h; subst h
      exact ⟨{ u with linked := false }, by simp [hu], Or.inl rfl, by simp [lblBatch]⟩
    · cases h

/-- **Drain.** From a subscription that is unregistered or whose receiver is closed, whatever the
labels that follow, it receives only events it already held (its batch under way and its
channel), in order, each at most once. -/
theorem drain [DecidableEq E] {pre suf : List (SubLbl E)} {s s' : SubSt E} {i : Nat} {u : Sub E}
    (hI : Inv pre s) (h : run {} s suf = some s') (hu : s.subs i = some u)
    (hend : u.linked = false ∨ u.rx = false) :
    ∃ u', s'.subs i = some u' ∧ received i suf ++ u'.cur ++ u'.chan <+ u.cur ++ u.chan := by
  induction suf generalizing pre s u with
  | nil => simp [run] at h; subst h; exact ⟨u, hu, by simp [received, batches]⟩
  | cons l suf ih =>
    simp only [run] at h
    cases h1 : step {} s l with
    | none => simp [h1] at h
    | some s1 =>
      simp [h1] at h
      obtain ⟨u1, hu1, hend1, hsub1⟩ := frame_step hI h1 hu hend
      obtain ⟨u', hu', hsub'⟩ := ih (inv_step hI h1) h hu1 hend1
      refine ⟨u', hu', ?_⟩
      rw [received_cons]
      have := hsub'.append_left ((lblBatch i l).getD [])
      simp only [List.append_assoc] at this hsub1 ⊢
      exact this.trans hsub1

/-! ## What the reference satisfies, over label sequences -/

/-- Split a reference run at a label. -/
theorem refSub_split [DecidableEq E] {pre suf : List (SubLbl E)} {l : SubLbl E}
    (h : refSub (pre ++ l :: suf)) :
    ∃ s s1 s', run {} SubSt.init pre = some s ∧ Inv pre s ∧ step {} s l = some s1 ∧
      run {} s1 suf = some s' := by
  obtain ⟨s', hs', -⟩ := refSub_run h
  rw [run_append] at hs'
  cases hp : run {} SubSt.init pre with
  | none => simp [hp] at hs'
  | some s =>
    simp only [hp, Option.bind_some, run] at hs'
    cases h1 : step {} s l with
    | none => simp [h1] at hs'
    | some s1 =>
      simp only [h1, Option.bind_some] at hs'
      exact ⟨s, s1, s', rfl, inv_run hp, h1, hs'⟩

/-- **Delivery.** What a subscription received is a sublist of the events appended after it
subscribed that its filter matches: in append order, each at most once, none appended before it
subscribed. A subscription never made receives nothing. -/
theorem refSub_received [DecidableEq E] {tr : List (SubLbl E)} (h : refSub tr) (i : Nat) :
    received i tr <+ matchingAfter i tr := by
  obtain ⟨s, -, hI⟩ := refSub_run h
  cases hs : s.subs i with
  | none =>
    have := hI.none_ i hs
    simp [received, this.2.1]
  | some u =>
    have hJ := hI.some_ i u hs
    simp only [matchingAfter, hJ.params]
    exact (List.sublist_append_left _ _).trans ((List.sublist_append_left _ _).trans
      (by simpa [List.append_assoc] using hJ.sub))

/-- **Delivery, the weak form** (ruling EVT-C4 (a)). What a subscription received is a sublist of
the events appended to the store: appended events, in append order, each at most once. -/
theorem refSub_received_appended [DecidableEq E] {tr : List (SubLbl E)} (h : refSub tr)
    (i : Nat) : received i tr <+ appended (storeOps tr) :=
  (refSub_received h i).trans (matchingAfter_sublist i tr)

/-- **Batches.** Every batch a subscription received is non-empty and holds at most the batch
size it subscribed with. -/
theorem refSub_batch [DecidableEq E] {tr : List (SubLbl E)} (h : refSub tr) {i : Nat}
    {b : List E} (hb : b ∈ batches i tr) :
    ∃ f c n, subParams i tr = some (f, c, n) ∧ b ≠ [] ∧ b.length ≤ n := by
  obtain ⟨s, -, hI⟩ := refSub_run h
  cases hs : s.subs i with
  | none => have := hI.none_ i hs; rw [this.2.1] at hb; cases hb
  | some u =>
    have hJ := hI.some_ i u hs
    exact ⟨u.filt, u.cap, u.bsz, hJ.params, hJ.batch b hb⟩

/-- A subscription that was never made received no batch. -/
theorem refSub_batches_none [DecidableEq E] {tr : List (SubLbl E)} (h : refSub tr) {i : Nat}
    (hn : subParams i tr = none) : batches i tr = [] := by
  rcases hb : batches i tr with _ | ⟨b, bs⟩
  · rfl
  · obtain ⟨f, c, n, hp, -⟩ := refSub_batch h (b := b) (by rw [hb]; simp)
    rw [hn] at hp; cases hp

/-- **Overflow ends the subscription** (ruling D86 (a)). After an append of a matching event that
finds the channel full (the backlog of subscription `i` reached its capacity), `i` receives
nothing appended from then on: what it received over the whole run is a sublist of the matching
events appended before that append. -/
theorem refSub_overflow_ends [DecidableEq E] {pre suf : List (SubLbl E)} {i : Nat} {e : E}
    {f : E → Bool} {c b : Nat}
    (h : refSub (pre ++ .op (.append e) :: suf)) (hp : subParams i pre = some (f, some c, b))
    (hf : f e = true) (hc : c ≤ backlog i pre) :
    received i (pre ++ .op (.append e) :: suf) <+ matchingAfter i pre := by
  obtain ⟨s, s1, s', -, hI, h1, hrun⟩ := refSub_split h
  cases hs : s.subs i with
  | none => have := hI.none_ i hs; rw [this.1] at hp; cases hp
  | some u =>
    have hJ := hI.some_ i u hs
    rw [hJ.params] at hp
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, hcap, rfl⟩ := hp
    have hs1 : s1.subs i = some (deliver {} e u) := by
      have h1' := h1
      simp [step, blocks] at h1'
      obtain ⟨-, rfl⟩ := h1'
      simp [hs]
    -- the append does not deliver to `i` and leaves it unregistered
    have hd : deliver {} e u = { u with linked := false } ∨ (deliver {} e u = u ∧ u.linked = false) := by
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
    have hend : (deliver {} e u).linked = false ∨ (deliver {} e u).rx = false := by
      rcases hd with hd | ⟨hd, hl⟩
      · rw [hd]; simp
      · rw [hd]; simp [hl]
    obtain ⟨u', -, hsub⟩ := drain (inv_step hI h1) hrun hs1 hend
    have hcc : (deliver {} e u).cur ++ (deliver {} e u).chan = u.cur ++ u.chan := by
      rcases hd with hd | ⟨hd, -⟩ <;> rw [hd]
    rw [received_append, received_cons]
    simp only [matchingAfter, hJ.params, lblBatch, Option.getD_none, List.nil_append]
    have h2 : received i suf <+ u.cur ++ u.chan :=
      hcc ▸ (List.sublist_append_left _ _).trans ((List.sublist_append_left _ _).trans hsub)
    have := h2.append_left (received i pre)
    exact this.trans (by simpa [List.append_assoc] using hJ.sub)

/-- **Close ends the subscription** (ruling D86 (d)). After a close of subscription `i` made while
no receive of `i` was pending, `i` receives nothing. -/
theorem refSub_close_ends [DecidableEq E] {pre suf : List (SubLbl E)} {i : Nat}
    (h : refSub (pre ++ .close i :: suf)) (hp : pending i pre = false) :
    received i suf = [] := by
  obtain ⟨s, s1, s', -, hI, h1, hrun⟩ := refSub_split h
  obtain ⟨u, u', hu, hg, rfl⟩ := modSub_eq_some h1
  have hJ := hI.some_ i u hu
  have hpu : u.pending = false := hJ.pend.trans hp
  have hcur : u.cur = [] := hJ.idle hpu
  simp [hpu] at hg; subst hg
  obtain ⟨u'', -, hsub⟩ := drain (inv_step hI h1) hrun (updSub_self _ _ _) (Or.inr rfl)
  simp only [hcur, List.append_nil] at hsub
  exact List.eq_nil_of_sublist_nil ((List.sublist_append_left _ _).trans
    ((List.sublist_append_left _ _).trans hsub))

/-- **Append never waits.** Until the store is dropped, an append (or a clear) is always
possible, whatever the subscriptions hold. -/
theorem refSub_append_enabled [DecidableEq E] {tr : List (SubLbl E)} (h : refSub tr)
    (hd : dropped tr = false) (o : StoreOp E) : refSub (tr ++ [.op o]) := by
  obtain ⟨s, hs, hI⟩ := refSub_run h
  have ha : s.alive = true := by rw [hI.alive, hd]; rfl
  unfold refSub subSem
  rw [run_snoc, hs]
  cases o <;> simp [step, ha, blocks]

/-- After a step from a dropped store, the store is still dropped, and the step was neither an
operation nor a subscribe. -/
theorem step_dead [DecidableEq E] {s s' : SubSt E} {l : SubLbl E} (h : step {} s l = some s')
    (hd : s.alive = false) :
    s'.alive = false ∧ lblOp l = none ∧ ∀ i, lblParams i l = none := by
  cases l with
  | op o => simp [step, hd] at h
  | subscribe j f c b => simp [step, hd] at h
  | drop => simp [step, hd] at h
  | _ => obtain ⟨-, -, -, -, rfl⟩ := modSub_eq_some h; exact ⟨hd, rfl, fun _ => rfl⟩

/-- **After a drop**, nothing is appended or cleared and nobody subscribes. -/
theorem refSub_dropped_no_op [DecidableEq E] {pre suf : List (SubLbl E)}
    (h : refSub (pre ++ .drop :: suf)) : storeOps suf = [] ∧ ∀ i, subParams i suf = none := by
  obtain ⟨s, s1, s', -, -, h1, hrun⟩ := refSub_split h
  have hd : s1.alive = false := by
    simp only [step] at h1; split at h1
    · simp at h1; subst h1; rfl
    · cases h1
  clear h1 h
  induction suf generalizing s1 with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | cons l suf ih =>
    simp only [run] at hrun
    cases h2 : step {} s1 l with
    | none => simp [h2] at hrun
    | some s2 =>
      simp [h2] at hrun
      obtain ⟨hd2, hop, hpar⟩ := step_dead h2 hd
      obtain ⟨ih1, ih2⟩ := ih s2 hrun hd2
      refine ⟨?_, fun i => ?_⟩
      · simp [storeOps, hop] at ih1 ⊢; exact ih1
      · rw [subParams_cons, hpar i, ih2 i]; rfl


/-! ## Decided runs

Concrete runs over natural numbers, for the nonvacuous and mutant evidence of the blocks. Each
fact is decided by evaluation. -/

/-- The filter that matches every event. -/
def subAll : Nat → Bool := fun _ => true

/-- The filter that matches the even events. -/
def subEven : Nat → Bool := fun n => n % 2 == 0

/-- Two debug subscribers that both receive the event appended after they subscribed
([EVT-024] AC1 and AC3). -/
def subRunTwo : List (SubLbl Nat) :=
  [.subscribe 0 subAll none 1, .subscribe 1 subAll none 1, .op (.append 7),
   .await 0, .pull 0, .recv 0 [7], .await 1, .pull 1, .recv 1 [7]]

theorem subRunTwo_facts :
    refDebugSub subRunTwo ∧ received 0 subRunTwo = [7] ∧ received 1 subRunTwo = [7] := by
  refine ⟨⟨by decide, ?_⟩, by decide, by decide⟩
  simp only [subRunTwo, List.mem_cons, List.not_mem_nil, or_false]
  rintro l (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [SubLbl.DebugForm, subAll]

/-- A filtered, batched subscription: an earlier event is not delivered, a non-matching one is
not delivered, and the two matching ones come in one batch of size at most 2 ([EVT-031] AC1 to
AC3). -/
def subRunFilter : List (SubLbl Nat) :=
  [.op (.append 0), .subscribe 0 subEven (some 4) 2, .op (.append 1), .op (.append 2),
   .op (.append 4), .await 0, .pull 0, .pull 0, .recv 0 [2, 4]]

theorem subRunFilter_facts :
    refSub subRunFilter ∧ received 0 subRunFilter = [2, 4] ∧
      batches 0 subRunFilter = [[2, 4]] ∧ matchingAfter 0 subRunFilter = [2, 4] := by
  decide

/-- An overflow: capacity 1, the second append finds the channel full and ends the subscription;
the receiver still drains the event its channel holds, then the receive reports the end. -/
def subRunOverflow : List (SubLbl Nat) :=
  [.subscribe 0 subAll (some 1) 4, .op (.append 1), .op (.append 2), .op (.append 3),
   .await 0, .pull 0, .recv 0 [1], .await 0, .finish 0]

theorem subRunOverflow_facts :
    refSub subRunOverflow ∧ received 0 subRunOverflow = [1] ∧
      backlog 0 (subRunOverflow.take 2) = 1 ∧
      ¬ refSub (subRunOverflow.take 7 ++ [.await 0, .pull 0]) := by
  decide

/-- A close with no receive pending: the event the channel held is dropped and the next receive
reports the end. -/
def subRunClose : List (SubLbl Nat) :=
  [.subscribe 0 subAll (some 4) 1, .op (.append 1), .close 0, .await 0, .finish 0]

theorem subRunClose_facts :
    refSub subRunClose ∧ pending 0 (subRunClose.take 2) = false ∧
      ¬ refSub (subRunClose.take 4 ++ [.pull 0]) := by
  decide

/-- A drop: the store accepts no further append, and the subscription drains its channel before
the end. -/
def subRunDrop : List (SubLbl Nat) :=
  [.subscribe 0 subAll (some 4) 1, .op (.append 1), .drop, .await 0, .pull 0, .recv 0 [1],
   .await 0, .finish 0]

theorem subRunDrop_facts :
    refSub subRunDrop ∧ received 0 subRunDrop = [1] ∧
      ¬ refSub (subRunDrop.take 3 ++ [.op (.append 2)]) := by
  decide

/-! ### The wrong stores on concrete runs -/

/-- With the overflow policy that drops only the event that does not fit (D86 (b)), the
subscription survives the overflow and receives an event appended after it. -/
theorem subRun_dropEvent :
    subSem {overflow := .dropEvent}
      ([.subscribe 0 subAll (some 1) 4, .op (.append 1), .op (.append 2), .await 0, .pull 0,
        .recv 0 [1], .op (.append 3), .await 0, .pull 0, .recv 0 [3]] : List (SubLbl Nat)) := by
  decide

/-- With back-pressure, an append that finds a channel full is not possible (it waits). -/
theorem subRun_block :
    ¬ subSem {overflow := .block}
      ([.subscribe 0 subAll (some 1) 4, .op (.append 1), .op (.append 2)] : List (SubLbl Nat)) := by
  decide

/-- With replay, a subscription receives an event appended before it subscribed. -/
theorem subRun_replay :
    subSem {replay := true}
      ([.op (.append 5), .subscribe 0 subAll (some 4) 1, .await 0, .pull 0, .recv 0 [5]] :
        List (SubLbl Nat)) := by
  decide

/-- Without the filter, a subscription receives an event its filter does not match. -/
theorem subRun_noFilter :
    subSem {filters := false}
      ([.subscribe 0 subEven (some 4) 1, .op (.append 1), .await 0, .pull 0, .recv 0 [1]] :
        List (SubLbl Nat)) := by
  decide

/-- Without the batch bound, a subscription with batch size 1 receives a batch of two. -/
theorem subRun_unbounded :
    subSem {bounded := false}
      ([.subscribe 0 subAll (some 4) 1, .op (.append 1), .op (.append 2), .await 0, .pull 0,
        .pull 0, .recv 0 [1, 2]] : List (SubLbl Nat)) := by
  decide

/-- With a close that does nothing, a subscription receives an event after a close made with no
receive pending. -/
theorem subRun_closeNoop :
    subSem {closeEnds := false}
      ([.subscribe 0 subAll (some 4) 1, .close 0, .op (.append 1), .await 0, .pull 0,
        .recv 0 [1]] : List (SubLbl Nat)) := by
  decide

end Libpetri.Reference
