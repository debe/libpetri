import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryStore
import Libpetri.Reference.Subscriptions

set_option linter.missingDocs true

/-!
# EVT-024: DebugEventStore (`spec/08-events-observability.md`)

The debug event store (Java, TypeScript and Rust `DebugEventStore`) keeps a bounded window of
events for a debug UI and tails new events to live subscribers. The requirement has two blocks,
one per observation of the store:

* `EVT_024` (kind F), the capacity line, is a predicate over the capacity `c` and the
  observation of one store, `S : StoreObs E` (glossary `GlossaryStore.lean`): after appends made
  one after the other, `events()` returns the newest `c` of them, in append order. The witness is
  the reference bounded store `refBoundedStore c`, at every capacity. The wrong stores keep the
  oldest events, list the newest ones newest first, never evict (the in-memory store) or empty
  themselves when full.
* `EVT_024_B` (kind B), the subscription lines, is a predicate over a store with live
  subscriptions observed as the label sequences it allows, `S : SubSem E` (RefSub,
  `Reference/Subscriptions.lean`). A debug store subscribes in one form only: every event
  matches, the channel is unbounded, each delivery is one event and the subscription is never
  closed (`SubLbl.DebugForm`). The witness is `refDebugSub`, the reference restricted to that
  form. A new store allows the empty run and an append never waits on a subscriber; the other
  lines are the safety form all three runtimes share (rulings D29 (a) and EVT-C4 (a)): at every
  point of a run, what a subscriber has received is a subsequence of the appends so far; a
  further subscriber can always join while the store is open; and each subscriber can still catch
  up with every event appended since it subscribed, by receives alone while the store stays open,
  whatever the other subscribers have received. That the deliveries do happen is liveness and
  stays under the ideal-run assumption. The wrong stores allow no run, refuse appends once
  someone subscribed, deliver newest first, deliver an event twice, deliver an event before it is
  appended, serve one subscriber at a time, deliver to the first subscriber only, or deliver only
  when the store is closed.

The test derivation (subscribe, append, receive) is `EVT_024_B_nonvacuous`: two subscribers
both receive the event appended after they subscribed.
-/

namespace Libpetri.Spec

open Libpetri.Reference

/-! ## EVT-024: the capacity line -/

requirement EVT_024
  id "EVT-024"
  title "DebugEventStore"
  kind F
  scope "the debug event store (Java DebugEventStore, TypeScript DebugEventStore, Rust libpetri-debug DebugEventStore)"
  source verbatim "spec/08-events-observability.md"
  quote "*When* events have been appended to a debug event store one after the other, a call of `events()` *shall* return the newest of them, as many as the store's capacity allows, in the order they were appended."
  reading "For every capacity c and every store S over any event type E:"
          "after a history of appends only, appending the events es one after the other, a call of events() returns the last c events of es (all of es when es has at most c events), in the order they were appended."
  assumes "The model is the observation of one store, S : StoreObs E (glossary: Event store), and its capacity c, a parameter of the line: the line holds at every capacity, and EVT_024_reference shows the reference bounded store meets it at every capacity. The event type E is a parameter: the line says nothing about what an event holds. The line reads a call of events() at the call (h' = []): whether the returned list is a copy or a live view is not specified (ruling D29 (a), EVT-020); Java returns List.copyOf, Rust a clone, and TypeScript its own array, which a later append changes."
          "AC2 (old events are evicted when capacity is exceeded) is the line. Each part of it is load-bearing: the newest events, not the oldest (EVT_024_mutant_keepOldest); in append order (EVT_024_mutant_newestFirst); old events evicted at all (EVT_024_mutant_unbounded, the in-memory store); and only as many as the capacity requires (EVT_024_mutant_resetWhenFull, a store that empties itself when full). EVT-020's line (a subsequence of the appends) follows at the call (evt024_atCall)."
          "Appends that overlap in time are kind A and outside the line, which speaks of appends made one after the other: a history is one sequence of appends in the order they take effect. Java's store is appended to from several threads (the orchestrator, action log capture, timeout handlers), and its eviction loop is not atomic, so the queue can hold a few events over capacity while appends overlap (DebugEventStore.java class comment). Rust appends under a mutex and TypeScript runs on one thread, so there no two appends overlap."
          "Clear: none of the three debug stores provides clear() (ruling D29 (a): clear() where provided), so a history of appends only is every history a caller can make. Closing the store changes no retained event: Java stops the broadcast, Rust and TypeScript drop the subscribers."
          "The capacity is kind N: it is positive and 10,000 unless the caller gives another (DEFAULT_MAX_EVENTS in all three), and a capacity that is not positive is rejected when the store is created (Java IllegalArgumentException, TypeScript Error, Rust a panic of assert!). The markdown states this without a shall, in the sentence 'A debug event store has a capacity: a positive number of events, 10,000 unless the caller gives another.', which describes the three stores as they are and is not checked by a line: the line holds at every capacity. EVT_024_default is the line at the default capacity."
          "The body bullet 'Session tracking' names the session identifier the store carries; it has no behaviour to state and is kind N. eventCount(), evictedCount(), size() and the replay queries eventsFrom, eventsSince and eventsBetween are not named by the spec and not modelled. The debug-aware stores answer events() from their primary store, not from the debug store, and are outside the line (EVT-020 covers them)."
          "The body bullet 'Subscriptions', AC1, AC3 and the test derivation are the second block of this ID, EVT_024_B. The Python binding has no debug store; its live subscriptions are EVT-031."
  signoff "2026-11-13 546c9502cf8f0fad ai"
  statement : ∀ {E : Type}, Nat → StoreObs E → Prop :=
    fun {E} c S => ∀ es : List E, S.read (es.map StoreOp.append) [] = es.drop (es.length - c)

/- The pinned readable form of EVT-024: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_024 : {E : Type} → Nat → StoreObs E → Prop :=
fun {E} c S => ∀ (es : List E), S.read (List.map StoreOp.append es) [] = List.drop (es.length - c) es
-/
#guard_msgs in #print EVT_024

/-! ### The reference -/

/-- What the reference bounded store returns after a history of appends only. -/
theorem evt024_bounded_appends {E : Type} (c : Nat) (es : List E) :
    (refBoundedStore (E := E) c).read (es.map StoreOp.append) [] = es.drop (es.length - c) := by
  simp [refBoundedStore, retained_appends]

/-- The reference bounded store satisfies EVT-024 at every capacity: after appends only it keeps
the newest `c` of them, in append order. -/
@[evidence holds EVT_024]
theorem EVT_024_reference {E : Type} (c : Nat) : EVT_024 c (refBoundedStore (E := E) c) :=
  evt024_bounded_appends c

/-- The reference bounded store at the debug stores' default capacity of 10,000 satisfies
EVT-024. -/
theorem EVT_024_default {E : Type} : EVT_024 10000 (refBoundedStore (E := E) 10000) :=
  EVT_024_reference 10000

/-! ### Consequences -/

/-- A store that meets EVT-024 returns, after appends only, a subsequence of the appended events
in append order: [EVT-020]'s line at the call. -/
theorem evt024_atCall {E : Type} {c : Nat} {S : StoreObs E} (hS : EVT_024 c S) (es : List E) :
    List.Sublist (S.read (es.map StoreOp.append) []) (appended (es.map StoreOp.append)) := by
  rw [hS es, appended_appends]
  exact List.drop_sublist _ _

/-- A store that meets EVT-024 returns no more events than its capacity, and every event when
there are at most that many. -/
theorem evt024_length {E : Type} {c : Nat} {S : StoreObs E} (hS : EVT_024 c S) (es : List E) :
    (S.read (es.map StoreOp.append) []).length = min c es.length := by
  rw [hS es, List.length_drop]
  omega

/-! ### Wrong stores, one per load-bearing part of the line -/

/-- The mutant reading without "the newest": as many of the appended events as the capacity
allows, in append order. -/
def Evt024AsMany {E : Type} (c : Nat) (S : StoreObs E) : Prop :=
  ∀ es : List E, List.Sublist (S.read (es.map StoreOp.append) []) es ∧
    (S.read (es.map StoreOp.append) []).length = min c es.length

/-- A bounded store that keeps the oldest `c` events and drops every later append. -/
def evt024_keepOldest (c : Nat) : StoreObs Nat where
  enabled := true
  hasClear := false
  read h _ := (retained h).take c

/-- ✗ A store that keeps the oldest events meets the reading without "the newest" and violates
EVT-024: at capacity 2, after appending 1, 2 and 3 it returns `[1, 2]`, not `[2, 3]`. -/
@[evidence mutant EVT_024]
theorem EVT_024_mutant_keepOldest :
    Evt024AsMany 2 (evt024_keepOldest 2) ∧ ¬ EVT_024 2 (evt024_keepOldest 2) := by
  refine ⟨fun es => ?_, fun h => ?_⟩
  · simp only [evt024_keepOldest, retained_appends]
    exact ⟨List.take_sublist _ _, List.length_take⟩
  · have := h [1, 2, 3]
    revert this
    decide

/-- The mutant reading without the order: the newest `c` appended events, in any order. -/
def Evt024AnyOrder {E : Type} (c : Nat) (S : StoreObs E) : Prop :=
  ∀ es : List E, List.Perm (S.read (es.map StoreOp.append) []) (es.drop (es.length - c))

/-- A bounded store that lists its newest `c` events newest first. -/
def evt024_newestFirst (c : Nat) : StoreObs Nat where
  enabled := true
  hasClear := false
  read h _ := ((refBoundedStore c).read h []).reverse

/-- ✗ A bounded store that lists its events newest first meets the reading without the order and
violates EVT-024 ("in the order they were appended"): at capacity 2, after appending 1 and 2 it
returns `[2, 1]`. -/
@[evidence mutant EVT_024]
theorem EVT_024_mutant_newestFirst :
    Evt024AnyOrder 2 (evt024_newestFirst 2) ∧ ¬ EVT_024 2 (evt024_newestFirst 2) := by
  refine ⟨fun es => ?_, fun h => ?_⟩
  · simp only [evt024_newestFirst, evt024_bounded_appends]
    exact List.reverse_perm _
  · have := h [1, 2]
    revert this
    decide

/-- The mutant reading without eviction: the newest `c` appended events end the list, in append
order, and older ones may stay. -/
def Evt024KeepsNewest {E : Type} (c : Nat) (S : StoreObs E) : Prop :=
  ∀ es : List E, List.IsSuffix (es.drop (es.length - c)) (S.read (es.map StoreOp.append) [])

/-- ✗ The in-memory store, which never evicts, meets the reading without eviction and violates
EVT-024 (AC2, old events are evicted): at capacity 1, after appending 1 and 2 it returns
`[1, 2]`, not `[2]`. -/
@[evidence mutant EVT_024]
theorem EVT_024_mutant_unbounded :
    Evt024KeepsNewest 1 (refMemStore (E := Nat)) ∧ ¬ EVT_024 1 (refMemStore (E := Nat)) := by
  refine ⟨fun es => ?_, fun h => ?_⟩
  · simp only [refMemStore, retained_appends]
    exact List.drop_suffix _ _
  · have := h [1, 2]
    revert this
    decide

/-- The mutant reading without "as many as the capacity allows": a suffix of the appended events,
at most `c` of them. -/
def Evt024AtMost {E : Type} (c : Nat) (S : StoreObs E) : Prop :=
  ∀ es : List E, List.IsSuffix (S.read (es.map StoreOp.append) []) es ∧
    (S.read (es.map StoreOp.append) []).length ≤ c

/-- One append on a store of capacity `c` that empties itself when full: the event is added
while there is room, and otherwise replaces everything the store holds. -/
def evt024_resetStep (c : Nat) (acc : List Nat) (e : Nat) : List Nat :=
  if acc.length < c then acc ++ [e] else [e]

/-- A bounded store of capacity `c` that empties itself when full instead of evicting the oldest
event. -/
def evt024_resetWhenFull (c : Nat) : StoreObs Nat where
  enabled := true
  hasClear := false
  read h _ := (appended h).foldl (evt024_resetStep c) []

/-- Appending to the store that empties itself when full keeps a suffix of what it held followed
by the appends, and never more than its capacity. -/
theorem evt024_resetStep_fold (c : Nat) (hc : 0 < c) :
    ∀ (es acc : List Nat), acc.length ≤ c →
      List.IsSuffix (es.foldl (evt024_resetStep c) acc) (acc ++ es) ∧
        (es.foldl (evt024_resetStep c) acc).length ≤ c
  | [], acc, h => ⟨by simp, h⟩
  | e :: es, acc, h => by
    simp only [List.foldl_cons]
    by_cases hl : acc.length < c
    · have hs : evt024_resetStep c acc e = acc ++ [e] := if_pos hl
      rw [hs]
      obtain ⟨h1, h2⟩ := evt024_resetStep_fold c hc es (acc ++ [e]) (by simp; omega)
      exact ⟨by simpa using h1, h2⟩
    · have hs : evt024_resetStep c acc e = [e] := if_neg hl
      rw [hs]
      obtain ⟨h1, h2⟩ := evt024_resetStep_fold c hc es [e] (by simp; omega)
      refine ⟨h1.trans ?_, h2⟩
      exact List.suffix_append acc (e :: es)

/-- ✗ A store that empties itself when full meets the reading without "as many as the capacity
allows" and violates EVT-024: at capacity 2, after appending 1, 2 and 3 it returns `[3]`, not
`[2, 3]`. -/
@[evidence mutant EVT_024]
theorem EVT_024_mutant_resetWhenFull :
    Evt024AtMost 2 (evt024_resetWhenFull 2) ∧ ¬ EVT_024 2 (evt024_resetWhenFull 2) := by
  refine ⟨fun es => ?_, fun h => ?_⟩
  · simp only [evt024_resetWhenFull, appended_appends]
    obtain ⟨h1, h2⟩ := evt024_resetStep_fold 2 (by decide) es [] (by simp)
    exact ⟨by simpa using h1, h2⟩
  · have := h [1, 2, 3]
    revert this
    decide

/-! ### Non-vacuity -/

/-- The line on the reference: at capacity 3, after appending 1 to 5, the bounded store returns
`[3, 4, 5]`, while the in-memory store returns all five events, so the line is not true of every
store. -/
@[evidence nonvacuous EVT_024]
theorem EVT_024_nonvacuous :
    (refBoundedStore (E := Nat) 3).read ([1, 2, 3, 4, 5].map StoreOp.append) [] = [3, 4, 5] ∧
    (refMemStore (E := Nat)).read ([1, 2, 3, 4, 5].map StoreOp.append) [] = [1, 2, 3, 4, 5] := by
  decide

/-! ## EVT-024: the subscription lines

### Reference lemmas

What the reference does for one debug subscriber: while the store is open, every subscription of a
debug-form run stays registered with an open receiver and an unbounded channel
(`evt024_open_run`), so its receives alone can take everything its channel holds
(`evt024_drain`) and bring what it received up to every event appended since it subscribed
(`evt024_catchUp`); and a further subscriber can always join (`evt024_join`). -/

section SubLemmas

variable {E : Type}

/-- A label of a receive on subscription `i`: it starts one, takes an event or returns a batch. -/
def Evt024Recv (i : Nat) (l : SubLbl E) : Prop :=
  l = .await i ∨ l = .pull i ∨ ∃ b, l = .recv i b

/-- The subscriptions of a state are all registered, with an open receiver and an unbounded
channel. -/
def Evt024Open (s : SubSt E) : Prop :=
  ∀ i u, s.subs i = some u → u.linked = true ∧ u.rx = true ∧ u.cap = none

theorem evt024_open_init : Evt024Open (SubSt.init : SubSt E) := by
  intro i u h; simp [SubSt.init] at h

theorem evt024_open_mod {s : SubSt E} {j : Nat} {u0 u' : Reference.Sub E} (hs : Evt024Open s)
    (hu0 : s.subs j = some u0)
    (hf : u'.linked = u0.linked ∧ u'.rx = u0.rx ∧ u'.cap = u0.cap) :
    Evt024Open { s with subs := updSub s.subs j u' } := by
  intro i u hu
  by_cases hji : j = i
  · subst hji
    simp [updSub_self] at hu; subst hu
    obtain ⟨a, b, c⟩ := hs j u0 hu0
    exact ⟨hf.1.trans a, hf.2.1.trans b, hf.2.2.trans c⟩
  · simp only [updSub_ne _ _ hji] at hu
    exact hs i u hu

theorem evt024_open_step [DecidableEq E] {s s' : SubSt E} {l : SubLbl E} (hs : Evt024Open s)
    (hl : l.DebugForm) (hd : lblDrop l = false) (h : step {} s l = some s') : Evt024Open s' := by
  cases l with
  | op o =>
    cases o with
    | append e =>
      simp only [step] at h
      by_cases ha : s.alive = true
      · simp [ha, blocks] at h
        subst h
        intro i u hu
        simp only [Option.map_eq_some_iff] at hu
        obtain ⟨v, hv, rfl⟩ := hu
        obtain ⟨h1, h2, h3⟩ := hs i v hv
        unfold deliver Sub.takes Sub.room
        by_cases hf : v.filt e = true <;> simp [h1, h2, h3, hf]
      · simp [ha] at h
    | clear =>
      simp only [step] at h
      by_cases ha : s.alive = true
      · simp [ha] at h; subst h; exact hs
      · simp [ha] at h
  | subscribe j f c b =>
    simp only [SubLbl.DebugForm] at hl
    obtain ⟨-, rfl, -⟩ := hl
    simp only [step] at h
    split at h
    · simp at h; subst h
      intro i u hu
      by_cases hji : j = i
      · subst hji; simp [updSub_self] at hu; subst hu; simp
      · simp only [updSub_ne _ _ hji] at hu; exact hs i u hu
    · cases h
  | await j =>
    obtain ⟨u0, u', hu0, hg, rfl⟩ := modSub_eq_some h
    refine evt024_open_mod hs hu0 ?_
    split at hg
    · cases hg
    · simp at hg; subst hg; simp
  | pull j =>
    obtain ⟨u0, u', hu0, hg, rfl⟩ := modSub_eq_some h
    refine evt024_open_mod hs hu0 ?_
    split at hg
    · split at hg
      · cases hg
      · simp at hg; subst hg; simp
    · cases hg
  | recv j b =>
    obtain ⟨u0, u', hu0, hg, rfl⟩ := modSub_eq_some h
    refine evt024_open_mod hs hu0 ?_
    split at hg
    · simp at hg; subst hg; simp
    · cases hg
  | finish j =>
    obtain ⟨u0, u', hu0, hg, rfl⟩ := modSub_eq_some h
    refine evt024_open_mod hs hu0 ?_
    split at hg
    · simp at hg; subst hg; simp
    · cases hg
  | close j => exact absurd hl id
  | drop => simp [lblDrop] at hd

theorem evt024_open_run [DecidableEq E] :
    ∀ (tr : List (SubLbl E)) (s s' : SubSt E), run {} s tr = some s' → Evt024Open s →
      (∀ l ∈ tr, l.DebugForm) → dropped tr = false → Evt024Open s'
  | [], s, s', h, hs, _, _ => by simp [run] at h; subst h; exact hs
  | l :: tr, s, s', h, hs, hdf, hd => by
    simp only [run] at h
    cases h1 : step {} s l with
    | none => simp [h1] at h
    | some s1 =>
      simp only [h1, Option.bind_some] at h
      have hd' : lblDrop l = false ∧ dropped tr = false := by
        simpa [dropped] using hd
      exact evt024_open_run tr s1 s' h
        (evt024_open_step hs (hdf l (by simp)) hd'.1 h1)
        (fun l' hl' => hdf l' (by simp [hl'])) hd'.2

/-- The result of a receive-label run: subscription `i` ends idle with an empty channel. -/
def Evt024Drained [DecidableEq E] (i : Nat) (s : SubSt E) (u : Reference.Sub E) (tr' : List (SubLbl E)) : Prop :=
  ∃ s' u', (∀ l ∈ tr', Evt024Recv i l) ∧ run {} s tr' = some s' ∧ s'.subs i = some u' ∧
    u'.cur = [] ∧ u'.chan = [] ∧ u'.linked = u.linked ∧ u'.rx = true

theorem evt024_idle_drain [DecidableEq E] (i : Nat) :
    ∀ (ch : List E) (s : SubSt E) (u : Reference.Sub E), s.subs i = some u → u.chan = ch →
      u.pending = false → u.cur = [] → u.rx = true → 0 < u.bsz →
      ∃ tr', Evt024Drained i s u tr'
  | [], s, u, hu, hch, _, hcur, hrx, _ =>
    ⟨[], s, u, by simp, rfl, hu, hcur, hch, rfl, hrx⟩
  | c :: cs, s, u, hu, hch, hp, hcur, hrx, hb => by
    let u3 : Reference.Sub E := { u with chan := cs, cur := [], pending := false }
    let s3 : SubSt E := { s with subs := updSub s.subs i u3 }
    have h3 : run {} s [.await i, .pull i, .recv i [c]] = some s3 := by
      simp only [run, step, modSub, hu, hp, Bool.false_eq_true, if_false, Option.map_some,
        Option.bind_some, s3]
      simp [hrx, hcur, hch, hb, u3, updSub_self]
      funext k
      by_cases hk : k = i <;> simp [updSub, hk]
    obtain ⟨tr'', s', u', hl, hr, hs', hc, hch', hlk, hrx'⟩ :=
      evt024_idle_drain i cs s3 u3 (by simp [s3, updSub]) rfl rfl rfl hrx hb
    refine ⟨[.await i, .pull i, .recv i [c]] ++ tr'', s', u', ?_, ?_, hs', hc, hch', hlk, hrx'⟩
    · intro l hl'
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hl'
      rcases hl' with rfl | rfl | rfl | hl'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨_, rfl⟩)
      · exact hl l hl'
    · rw [run_append, h3]; simpa using hr

theorem evt024_drained_cons [DecidableEq E] {i : Nat} {s s1 : SubSt E} {u u1 : Reference.Sub E}
    {pre tr' : List (SubLbl E)} (hpre : ∀ l ∈ pre, Evt024Recv i l) (h1 : run {} s pre = some s1)
    (hl : u1.linked = u.linked) (hd : Evt024Drained i s1 u1 tr') :
    Evt024Drained i s u (pre ++ tr') := by
  obtain ⟨s', u', hr, hrun, hs', hc, hch, hlk, hrx⟩ := hd
  refine ⟨s', u', ?_, ?_, hs', hc, hch, hlk.trans hl, hrx⟩
  · intro l hl'
    rcases List.mem_append.1 hl' with h | h
    · exact hpre l h
    · exact hr l h
  · rw [run_append, h1]; simpa using hrun

/-- From any state of subscription `i` with an open receiver, receives on `i` alone take
everything its channel holds and leave it idle. -/
theorem evt024_drain [DecidableEq E] {i : Nat} {s : SubSt E} {u : Reference.Sub E}
    (hu : s.subs i = some u) (hrx : u.rx = true) (hb : 0 < u.bsz)
    (hidle : u.pending = false → u.cur = []) :
    ∃ tr', Evt024Drained i s u tr' := by
  cases hp : u.pending with
  | false =>
    exact evt024_idle_drain i u.chan s u hu rfl hp (hidle hp) hrx hb
  | true =>
    cases hcur : u.cur with
    | cons x xs =>
      let u1 : Reference.Sub E := { u with cur := [], pending := false }
      let s1 : SubSt E := { s with subs := updSub s.subs i u1 }
      have h1 : run {} s [.recv i (x :: xs)] = some s1 := by
        simp [run, step, modSub, hu, hp, hcur, s1, u1]
      obtain ⟨tr', hd⟩ := evt024_idle_drain i u1.chan s1 u1 (by simp [s1, updSub_self]) rfl rfl rfl
        hrx hb
      exact ⟨_, evt024_drained_cons (by simp [Evt024Recv]) h1 rfl hd⟩
    | nil =>
      cases hch : u.chan with
      | nil => exact ⟨[], s, u, by simp, rfl, hu, hcur, hch, rfl, hrx⟩
      | cons c cs =>
        let u1 : Reference.Sub E := { u with chan := cs, cur := [], pending := false }
        let s1 : SubSt E := { s with subs := updSub s.subs i u1 }
        have h1 : run {} s [.pull i, .recv i [c]] = some s1 := by
          simp only [run, step, modSub, hu, hp, s1]
          simp [hrx, hcur, hch, hb, u1, updSub_self]
          funext k
          by_cases hk : k = i <;> simp [updSub, hk]
        obtain ⟨tr', hd⟩ := evt024_idle_drain i u1.chan s1 u1 (by simp [s1, updSub_self]) rfl rfl
          rfl hrx hb
        refine ⟨_, evt024_drained_cons (pre := [.pull i, .recv i [c]]) ?_ h1 rfl hd⟩
        intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- The parameters a debug-form run gives a subscription: every event matches, the channel is
unbounded and every delivery is one event. -/
theorem evt024_params {tr : List (SubLbl E)} (hdf : ∀ l ∈ tr, l.DebugForm) {i : Nat}
    {p : (E → Bool) × Option Nat × Nat} (h : subParams i tr = some p) :
    (∀ e, p.1 e = true) ∧ p.2.1 = none ∧ p.2.2 = 1 := by
  obtain ⟨l, hl, hp⟩ := List.exists_of_findSome?_eq_some h
  cases l with
  | subscribe j f c b =>
    simp only [lblParams] at hp
    split at hp
    · simp at hp; subst hp; exact hdf _ hl
    · cases hp
  | _ => simp [lblParams] at hp

theorem evt024_recv_ops {i : Nat} {tr' : List (SubLbl E)} (h : ∀ l ∈ tr', Evt024Recv i l) :
    storeOps tr' = [] := by
  induction tr' with
  | nil => rfl
  | cons l tr' ih =>
    have := h l (by simp)
    rcases this with rfl | rfl | ⟨b, rfl⟩ <;>
      simpa [storeOps, lblOp] using ih (fun l hl => h l (by simp [hl]))

theorem evt024_recv_params {i : Nat} {tr' : List (SubLbl E)} (h : ∀ l ∈ tr', Evt024Recv i l)
    (k : Nat) : subParams k tr' = none := by
  induction tr' with
  | nil => rfl
  | cons l tr' ih =>
    rw [subParams_cons, ih (fun l hl => h l (by simp [hl]))]
    rcases h l (by simp) with rfl | rfl | ⟨b, rfl⟩ <;> rfl

theorem evt024_recv_debug {i : Nat} {tr' : List (SubLbl E)} (h : ∀ l ∈ tr', Evt024Recv i l) :
    ∀ l ∈ tr', l.DebugForm := by
  intro l hl
  rcases h l hl with rfl | rfl | ⟨b, rfl⟩ <;> trivial

/-- Whether a label only receives, on any subscription: it starts a receive, takes an event from a
channel, returns a batch or reports the end of a stream. A store operation, a subscribe, a close
and the drop of the store are not receives. -/
def evt024Receive : SubLbl E → Bool
  | .await _ | .pull _ | .recv _ _ | .finish _ => true
  | _ => false

theorem evt024_recv_receive {i : Nat} {tr' : List (SubLbl E)} (h : ∀ l ∈ tr', Evt024Recv i l) :
    ∀ l ∈ tr', evt024Receive l = true := by
  intro l hl
  rcases h l hl with rfl | rfl | ⟨b, rfl⟩ <;> rfl

/-- A run of receives drops nothing. -/
theorem evt024_receive_dropped :
    ∀ {tr' : List (SubLbl E)}, (∀ l ∈ tr', evt024Receive l = true) → dropped tr' = false
  | [], _ => rfl
  | l :: tr', h => by
    have hl := h l List.mem_cons_self
    have ih : dropped tr' = false :=
      evt024_receive_dropped (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    simp only [dropped, List.any_cons] at ih ⊢
    rw [ih]
    cases l <;> simp_all [evt024Receive, lblDrop]

/-- A prefix of a reference run is a reference run. -/
theorem evt024_refSub_prefix [DecidableEq E] {a tr : List (SubLbl E)} (h : refSub tr)
    (hp : a <+: tr) : refSub a := by
  obtain ⟨b, rfl⟩ := hp
  unfold refSub subSem at *
  rw [run_append] at h
  cases ha : run {} SubSt.init a with
  | none => simp [ha] at h
  | some s => rfl

/-- What a subscription has received at any point of a reference run is a sublist of the events
appended up to that point. -/
theorem evt024_ref_fifo [DecidableEq E] {tr : List (SubLbl E)} (h : refSub tr) (k i : Nat) :
    List.Sublist (received i (tr.take k)) (appended (storeOps (tr.take k))) :=
  refSub_received_appended (evt024_refSub_prefix h (List.take_prefix k tr)) i

/-- **Catch-up on the reference.** In a debug-form reference run while the store is open, receives
on subscription `i` alone bring what `i` received up to every event appended since it
subscribed. -/
theorem evt024_catchUp [DecidableEq E] {tr : List (SubLbl E)} (h : refSub tr)
    (hdf : ∀ l ∈ tr, l.DebugForm) (hd : dropped tr = false) {i : Nat}
    (hi : (subParams i tr).isSome) :
    ∃ tr', (∀ l ∈ tr', Evt024Recv i l) ∧ refSub (tr ++ tr') ∧
      received i (tr ++ tr') = appendsAfter i tr := by
  obtain ⟨s, hs, hI⟩ := refSub_run h
  cases hsu : s.subs i with
  | none => have := (hI.none_ i hsu).1; rw [this] at hi; cases hi
  | some u =>
    have hJ := hI.some_ i u hsu
    obtain ⟨hlk, hrx, -⟩ := evt024_open_run tr _ _ hs evt024_open_init hdf hd i u hsu
    obtain ⟨tr', s', u', hr, hrun, hs', hc, hch, hlk', hrx'⟩ :=
      evt024_drain hsu hrx hJ.bsz_pos hJ.idle
    have hall : run {} SubSt.init (tr ++ tr') = some s' := by
      rw [run_append, hs]; simpa using hrun
    have href : refSub (tr ++ tr') := by
      unfold refSub subSem; rw [hall]; rfl
    refine ⟨tr', hr, href, ?_⟩
    obtain ⟨s'', hs'', hI'⟩ := refSub_run href
    rw [hall] at hs''; cases hs''
    have hJ' := hI'.some_ i u' hs'
    have heq := hJ'.eq (hlk'.trans hlk) hrx'
    rw [hc, hch] at heq
    simp only [List.append_nil] at heq
    have hpar : subParams i (tr ++ tr') = subParams i tr := by
      rw [subParams_append]
      cases hp : subParams i tr with
      | none => rw [hp] at hi; cases hi
      | some p => rfl
    have hA : appendsAfter i (tr ++ tr') = appendsAfter i tr := by
      rw [appendsAfter_append, if_pos hi, evt024_recv_ops hr]; simp [appended]
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hi
    have hf := (evt024_params hdf hp).1
    have hfu : u'.filt = p.1 := by
      have := hJ'.params; rw [hpar, hp] at this
      simp only [Option.some.injEq] at this; rw [this]
    rw [heq, hA, hfu, List.filter_eq_self.2 (fun e _ => hf e)]

/-- **Joining on the reference.** While the store is open, a new debug subscriber can always
subscribe, under a number not used before. -/
theorem evt024_join [DecidableEq E] {tr : List (SubLbl E)} (h : refSub tr)
    (hd : dropped tr = false) :
    ∃ j, subParams j tr = none ∧ refSub (tr ++ [.subscribe j (fun _ => true) none 1]) := by
  obtain ⟨s, hs, hI⟩ := refSub_run h
  refine ⟨s.n, (hI.none_ s.n (hI.fresh s.n (Nat.le_refl _))).1, ?_⟩
  have ha : s.alive = true := by rw [hI.alive, hd]; rfl
  unfold refSub subSem
  rw [run_snoc, hs]
  simp [step, ha]

end SubLemmas

/-! ### The block -/

requirement EVT_024_B
  id "EVT-024"
  title "DebugEventStore (subscriptions)"
  kind B
  scope "the debug event store's live subscriptions (Java DebugEventStore.subscribe, TypeScript DebugEventStore.subscribe, Rust libpetri-debug DebugEventStore::subscribe)"
  source verbatim "spec/08-events-observability.md"
  quote "*When* an event is appended to an open debug event store, the append *shall* complete without waiting for any subscriber to receive the event."
        "Each subscriber of a debug event store *shall* receive only events appended to the store, each at most once and, for appends that do not overlap in time, in the order they were appended."
        "A subscriber may receive an event after the append that added it has returned."
        "*While* a debug event store is open, a caller *shall* be able to add a further subscriber, whatever subscribers the store already has."
        "*While* a debug event store is open, each subscriber that has not cancelled its subscription *shall* still be able to receive every event appended since it subscribed, whatever the other subscribers have received."
  reading "For every store S with live subscriptions over any event type E, observed as the label sequences it allows:"
          "S allows the empty run (a new store);"
          "in every run in which the store was not dropped, an append of any event can come next;"
          "in every run and at every point of it (every prefix), what each subscription i has received is a sublist of the events appended so far, in append order;"
          "in every run in which the store was not dropped, a debug subscriber (every event matches, unbounded channel, one event per delivery) can subscribe next, under a number no subscription of the run has;"
          "in every run of debug-form labels in which the store was not dropped, every subscription i made in it can go on, with receives only (no store operation, subscribe, close or drop of the store), to a run that S allows in which what i received ends with every event appended since i subscribed."
  assumes "The model is a store with live subscriptions observed as the label sequences it allows, S : SubSem E (RefSub, Reference/Subscriptions.lean): store operations, subscribes numbered 0, 1, 2 in the order made, the start of a receive, a take from the channel, a returned batch, the end of a stream, a close and the drop of the store. A debug store subscribes in one form (SubLbl.DebugForm: every event matches, the channel is unbounded, each delivery is one event, no close label), and the witness is the reference restricted to that form, refDebugSub. Java and TypeScript subscribers are callbacks the store calls; a call delivering one event is read as a receive that returns that event (await, pull, recv). Rust's subscriber reads a crossbeam channel, which the labels describe directly."
          "Line 1 is the start of the observation: a new store allows the empty run. Line 2 is the first quoted sentence: an append never waits on a subscriber, so in every open run an append can come next (Java hands the broadcast to its broadcast thread, TypeScript to a microtask, and Rust sends on unbounded channels inside the store's lock). Without them a store that allows no run, or no append once someone subscribed, would meet the other lines without delivering anything (EVT_024_B_mutant_empty, EVT_024_B_mutant_noLateAppend)."
          "Line 3 is the second quoted sentence, the order per subscriber of rulings D29 (a) and EVT-C4 (a). It compares with every event appended in the run, not only with those appended after the subscriber subscribed, because Java's broadcast task reads the subscriber list when it runs: a subscriber added between an append and its broadcast can receive that earlier event (clash evt-c#4). The reference is forward-only (refSub_received); EVT-031 states the forward-only form for its own store. The line is checked at every prefix of a run, not only on whole runs, because S is any set of label sequences and the glossary does not require it to be closed under prefixes: a store that hands out an event before it is appended is caught at the point of the delivery (EVT_024_B_mutant_early). Each clause of the sentence has its own mutant: delivered before its append, so not yet an appended event (EVT_024_B_mutant_early); delivered twice (EVT_024_B_mutant_twice); delivered newest first (EVT_024_B_mutant_lifo). The third quoted sentence is why no line ties a delivery to its append: Rust delivers inside append, TypeScript in a microtask over the subscribers present at the append, Java on a broadcast thread. Appends that overlap in time are kind A and outside the line, which a run reads in one order: in Java two threads can store e1 and e2 and broadcast e2 before e1, which the clause on overlapping appends excludes. The label model puts every append of a run in one order, so for overlapping appends a Java run is read in the order of their broadcasts; that is a modelling choice, and the only place where line 3 is stricter than the sentence it quotes."
          "Line 4 is the fourth quoted sentence and AC3 (multiple subscribers can be active simultaneously): a store that serves one subscriber at a time meets every other line and fails it (EVT_024_B_mutant_single)."
          "Line 5 is the fifth quoted sentence and AC1 (while the store is open, each subscriber that has not cancelled can receive the events appended since it subscribed, each at most once and, for appends that do not overlap in time, in the order they were appended; with line 3). It is a possibility, not a guarantee: that the deliveries do happen, every event eventually reaching every subscriber that stays subscribed, is liveness and kind A, under the ideal run in which the store's broadcast runs and every subscriber returns. 'Whatever the other subscribers have received' is the quantifier over every run; the continuation may hold other subscribers' receives, since in Java and TypeScript one broadcast calls the subscribers in turn. The continuation holds receives only (evt024Receive: the start of a receive, a take, a returned batch, the end of a stream), so the store stays open while i catches up, as the sentence's While clause requires, and no subscription is added or closed on the way. A store that delivers nothing while open and flushes every subscriber in close() meets lines 1 to 4 and a line 5 whose continuation only excludes store operations, and fails line 5 (EVT_024_B_mutant_flushOnClose). Its conclusion is a suffix, not an equality, for the earlier event line 3 allows in Java. A store that delivers to its first subscriber only meets every other line and fails it (EVT_024_B_mutant_firstOnly)."
          "Cancel is not modelled: the debug form has no close label, and line 5's debug-form premise is the 'has not cancelled' of the sentence. Java and TypeScript Subscription.cancel() remove the subscriber; Rust's Subscription::cancel only drops a sender nobody reads, so a Rust subscriber that cancelled keeps receiving (Subscription::cancel and DebugEventStore::subscribe in rust/libpetri-debug/src/debug_event_store.rs), which no line forbids."
          "Open: the drop label is the store's close(), and the sentence 'A debug event store is open until its close() is called.' defines the open state the lines speak of. Lines 2, 4 and 5 speak of runs before it ('while open'), and line 5's continuation does not close the store. After close() Java still stores events but stops its broadcast (shutdownBroadcast, which waits up to two seconds for pending broadcasts), and Rust and TypeScript remove every subscriber; appends after close() are outside the reference, where no operation follows a drop, and line 3 covers whatever such a store still delivers. A subscriber that throws is caught and the broadcast goes on to the next one in Java and TypeScript; exceptions are not modelled."
          "The test derivation (subscribe to the debug store, append an event, verify that the subscriber receives it) is EVT_024_B_nonvacuous, with two subscribers that both receive the event appended after they subscribed, which is also the AC3 witness. The capacity of the store (AC2) is the first block of this ID, EVT_024. EVT-031 is the Python binding's subscription store over the same model, with filters, bounded channels and batches."
  signoff "2026-11-13 42dcc5c89a1b23fd ai"
  statement : ∀ {E : Type}, SubSem E → Prop :=
    fun S =>
      S [] ∧
      (∀ tr, S tr → dropped tr = false → ∀ e, S (tr ++ [.op (.append e)])) ∧
      (∀ tr, S tr → ∀ k i,
        List.Sublist (received i (tr.take k)) (appended (storeOps (tr.take k)))) ∧
      (∀ tr, S tr → dropped tr = false →
        ∃ j, subParams j tr = none ∧ S (tr ++ [.subscribe j (fun _ => true) none 1])) ∧
      (∀ tr, S tr → (∀ l ∈ tr, l.DebugForm) → dropped tr = false →
        ∀ i, (subParams i tr).isSome = true →
          ∃ tr', (∀ l ∈ tr', evt024Receive l = true) ∧ S (tr ++ tr') ∧
            List.IsSuffix (appendsAfter i tr) (received i (tr ++ tr')))

/- The pinned readable form of EVT-024 (subscriptions): a change to the formula shows up as a
diff here. -/
/--
info: def Libpetri.Spec.EVT_024_B : {E : Type} → SubSem E → Prop :=
fun {E} S =>
  S [] ∧
    (∀ (tr : List (SubLbl E)), S tr → dropped tr = false → ∀ (e : E), S (tr ++ [SubLbl.op (StoreOp.append e)])) ∧
      (∀ (tr : List (SubLbl E)),
          S tr → ∀ (k i : Nat), (received i (List.take k tr)).Sublist (appended (storeOps (List.take k tr)))) ∧
        (∀ (tr : List (SubLbl E)),
            S tr →
              dropped tr = false → ∃ j, subParams j tr = none ∧ S (tr ++ [SubLbl.subscribe j (fun x => true) none 1])) ∧
          ∀ (tr : List (SubLbl E)),
            S tr →
              (∀ (l : SubLbl E), l ∈ tr → l.DebugForm) →
                dropped tr = false →
                  ∀ (i : Nat),
                    (subParams i tr).isSome = true →
                      ∃ tr',
                        (∀ (l : SubLbl E), l ∈ tr' → evt024Receive l = true) ∧
                          S (tr ++ tr') ∧ appendsAfter i tr <:+ received i (tr ++ tr')
-/
#guard_msgs in #print EVT_024_B

/-- Line 1 of EVT-024 (subscriptions) alone: a new store. -/
def Evt024Start {E : Type} (S : SubSem E) : Prop := S []

/-- Line 2 of EVT-024 (subscriptions) alone: an append never waits. -/
def Evt024Append {E : Type} (S : SubSem E) : Prop :=
  ∀ tr, S tr → dropped tr = false → ∀ e, S (tr ++ [.op (.append e)])

/-- Line 3 of EVT-024 (subscriptions) alone: the order per subscriber, at every point of a run. -/
def Evt024Fifo {E : Type} (S : SubSem E) : Prop :=
  ∀ tr, S tr → ∀ k i, List.Sublist (received i (tr.take k)) (appended (storeOps (tr.take k)))

/-- Line 4 of EVT-024 (subscriptions) alone: a further subscriber can join. -/
def Evt024Join {E : Type} (S : SubSem E) : Prop :=
  ∀ tr, S tr → dropped tr = false →
    ∃ j, subParams j tr = none ∧ S (tr ++ [.subscribe j (fun _ => true) none 1])

/-- Line 5 of EVT-024 (subscriptions) alone: every subscriber can catch up, with receives only. -/
def Evt024CatchUp {E : Type} (S : SubSem E) : Prop :=
  ∀ tr, S tr → (∀ l ∈ tr, l.DebugForm) → dropped tr = false →
    ∀ i, (subParams i tr).isSome = true →
      ∃ tr', (∀ l ∈ tr', evt024Receive l = true) ∧ S (tr ++ tr') ∧
        List.IsSuffix (appendsAfter i tr) (received i (tr ++ tr'))

/-- EVT-024 (subscriptions) is its five lines. -/
theorem evt024B_iff {E : Type} (S : SubSem E) :
    EVT_024_B S ↔ Evt024Start S ∧ Evt024Append S ∧ Evt024Fifo S ∧ Evt024Join S ∧
      Evt024CatchUp S :=
  Iff.rfl

/-- The mutant reading without line 1. -/
def Evt024NoStart {E : Type} (S : SubSem E) : Prop :=
  Evt024Append S ∧ Evt024Fifo S ∧ Evt024Join S ∧ Evt024CatchUp S

/-- The mutant reading without line 2. -/
def Evt024NoAppend {E : Type} (S : SubSem E) : Prop :=
  Evt024Start S ∧ Evt024Fifo S ∧ Evt024Join S ∧ Evt024CatchUp S

/-- The mutant reading without line 4. -/
def Evt024NoJoin {E : Type} (S : SubSem E) : Prop :=
  Evt024Start S ∧ Evt024Append S ∧ Evt024Fifo S ∧ Evt024CatchUp S

/-- The mutant reading without line 5. -/
def Evt024NoCatchUp {E : Type} (S : SubSem E) : Prop :=
  Evt024Start S ∧ Evt024Append S ∧ Evt024Fifo S ∧ Evt024Join S

/-! ### The reference -/

/-- A debug-form run followed by receive labels is a debug-form run. -/
theorem evt024_debug_append {E : Type} {i : Nat} {tr tr' : List (SubLbl E)}
    (hdf : ∀ l ∈ tr, l.DebugForm) (hr : ∀ l ∈ tr', Evt024Recv i l) :
    ∀ l ∈ tr ++ tr', l.DebugForm := by
  intro l hl
  rcases List.mem_append.1 hl with h | h
  · exact hdf l h
  · exact evt024_recv_debug hr l h

/-- The debug subscribe label is in the debug form. -/
theorem evt024_debug_subscribe {E : Type} (j : Nat) :
    (SubLbl.subscribe j (fun _ => true) none 1 : SubLbl E).DebugForm :=
  ⟨fun _ => rfl, rfl, rfl⟩

/-- A debug-form run followed by one label in the debug form is a debug-form run. -/
theorem evt024_debug_snoc {E : Type} {tr : List (SubLbl E)} {l : SubLbl E}
    (hdf : ∀ l ∈ tr, l.DebugForm) (hl : l.DebugForm) : ∀ l' ∈ tr ++ [l], l'.DebugForm := by
  intro l' hl'
  rcases List.mem_append.1 hl' with h | h
  · exact hdf l' h
  · simp only [List.mem_singleton] at h; subst h; exact hl

/-- Line 1 on the reference debug store. -/
theorem evt024_refDebug_start {E : Type} [DecidableEq E] : Evt024Start (refDebugSub (E := E)) :=
  ⟨rfl, fun _ h => by cases h⟩

/-- Line 2 on the reference debug store. -/
theorem evt024_refDebug_append {E : Type} [DecidableEq E] :
    Evt024Append (refDebugSub (E := E)) :=
  fun _ h hd e => ⟨refSub_append_enabled h.1 hd (.append e), evt024_debug_snoc h.2 trivial⟩

/-- Line 4 on the reference debug store. -/
theorem evt024_refDebug_join {E : Type} [DecidableEq E] : Evt024Join (refDebugSub (E := E)) := by
  intro tr h hd
  obtain ⟨j, hj, href⟩ := evt024_join h.1 hd
  exact ⟨j, hj, href, evt024_debug_snoc h.2 (evt024_debug_subscribe j)⟩

/-- Line 5 on the reference debug store, with receives on the subscription alone. -/
theorem evt024_refDebug_catchUp {E : Type} [DecidableEq E] {tr : List (SubLbl E)}
    (h : refDebugSub tr) (hd : dropped tr = false) {i : Nat} (hi : (subParams i tr).isSome = true) :
    ∃ tr', (∀ l ∈ tr', Evt024Recv i l) ∧ refDebugSub (tr ++ tr') ∧
      received i (tr ++ tr') = appendsAfter i tr := by
  obtain ⟨tr', hr, href, hrecv⟩ := evt024_catchUp h.1 h.2 hd hi
  exact ⟨tr', hr, ⟨href, evt024_debug_append h.2 hr⟩, hrecv⟩

/-- The reference debug store satisfies EVT-024 (subscriptions): a new store, an append never
waits, what a subscriber receives is a subsequence of the appends, a further subscriber can always
join while the store is open, and each subscriber can catch up with every event appended since it
subscribed. -/
@[evidence holds EVT_024_B]
theorem EVT_024_B_reference {E : Type} [DecidableEq E] : EVT_024_B (refDebugSub (E := E)) := by
  refine ⟨evt024_refDebug_start, evt024_refDebug_append,
    fun tr h k i => evt024_ref_fifo h.1 k i, evt024_refDebug_join, ?_⟩
  intro tr h _ hd i hi
  obtain ⟨tr', hr, href, hrecv⟩ := evt024_refDebug_catchUp h hd hi
  exact ⟨tr', evt024_recv_receive hr, href, by rw [hrecv]; exact List.suffix_refl _⟩

/-! ### Wrong stores, one per line -/

/-- The store that allows no run at all. -/
def evt024_empty : SubSem Nat := fun _ => False

/-- ✗ A store that allows no run meets lines 2 to 5, which speak only of the runs a store allows,
and violates EVT-024 (subscriptions), line 1. -/
@[evidence mutant EVT_024_B]
theorem EVT_024_B_mutant_empty : Evt024NoStart evt024_empty ∧ ¬ EVT_024_B evt024_empty :=
  ⟨⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩,
    fun h => h.1⟩

/-- The store that refuses every append once someone has subscribed: the reference debug store's
runs in which no event is appended after any subscription was made. -/
def evt024_noLateAppend : SubSem Nat := fun tr => refDebugSub tr ∧ ∀ i, appendsAfter i tr = []

/-- No event is appended after any subscription in a run of receive labels on one subscription. -/
theorem evt024_recv_appendsAfter {i k : Nat} {tr' : List (SubLbl Nat)}
    (hr : ∀ l ∈ tr', Evt024Recv i l) : appendsAfter k tr' = [] := by
  unfold appendsAfter
  rw [afterSub_none (evt024_recv_params hr k)]
  rfl

/-- ✗ A store that refuses appends once someone has subscribed meets every line but line 2 and
violates EVT-024 (subscriptions), line 2: after subscription 0 is made, appending 7 is refused. -/
@[evidence mutant EVT_024_B]
theorem EVT_024_B_mutant_noLateAppend :
    Evt024NoAppend evt024_noLateAppend ∧ ¬ EVT_024_B evt024_noLateAppend := by
  refine ⟨⟨⟨evt024_refDebug_start, fun k => rfl⟩,
    fun tr h k i => evt024_ref_fifo h.1.1 k i, fun tr h hd => ?_, ?_⟩, fun h => ?_⟩
  · obtain ⟨j, hj, href⟩ := evt024_refDebug_join tr h.1 hd
    refine ⟨j, hj, href, fun k => ?_⟩
    rw [appendsAfter_snoc, h.2 k]
    split <;> rfl
  · intro tr h _ hd i hi
    obtain ⟨tr', hr, href, hrecv⟩ := evt024_refDebug_catchUp h.1 hd hi
    refine ⟨tr', evt024_recv_receive hr, ⟨href, fun k => ?_⟩,
      by rw [hrecv]; exact List.suffix_refl _⟩
    rw [appendsAfter_append, h.2 k, evt024_recv_ops hr, evt024_recv_appendsAfter hr]
    split <;> rfl
  · let tr0 : List (SubLbl Nat) := [.subscribe 0 (fun _ => true) none 1]
    have hrun : evt024_noLateAppend tr0 := by
      refine ⟨⟨by decide, ?_⟩, fun k => ?_⟩
      · intro l hl
        simp only [tr0, List.mem_singleton] at hl
        subst hl; exact evt024_debug_subscribe 0
      · by_cases hk : k = 0
        · subst hk; decide
        · simp [tr0, appendsAfter, afterSub, storeOps, appended, Ne.symm hk]
    have := (h.2.1 tr0 hrun (by decide) 7).2 0
    revert this
    decide

/-- A subscription that receives nothing in a run receives nothing in any prefix of it. -/
theorem evt024_received_take_nil {i : Nat} {tr : List (SubLbl Nat)} (h : received i tr = [])
    (k : Nat) : received i (tr.take k) = [] := by
  rw [← List.take_append_drop k tr, received_append, List.append_eq_nil_iff] at h
  exact h.1

/-- The mutant reading of line 3 without the order: what a subscription has received at any
point of a run is a rearrangement of a subsequence of the appends so far. -/
def Evt024AnyOrderRecv {E : Type} (S : SubSem E) : Prop :=
  ∀ tr, S tr → ∀ k i, ∃ l, List.Perm l (received i (tr.take k)) ∧
    List.Sublist l (appended (storeOps (tr.take k)))

/-- A run of a store that hands its subscriber the newest event first: after 1 and 2 are
appended, the subscriber receives 2, then 1. -/
def evt024_lifoRun : List (SubLbl Nat) :=
  [.subscribe 0 (fun _ => true) none 1, .op (.append 1), .op (.append 2),
   .await 0, .pull 0, .recv 0 [2], .await 0, .pull 0, .recv 0 [1]]

/-- The store that delivers newest first, as the runs it allows: the prefixes of
`evt024_lifoRun`. -/
def evt024_lifo : SubSem Nat := fun tr => ∃ k, tr = evt024_lifoRun.take k

/-- A subscription other than 0 receives nothing in a prefix of `evt024_lifoRun`. -/
theorem evt024_lifo_other {i : Nat} (hi : i ≠ 0) (k : Nat) :
    received i (evt024_lifoRun.take k) = [] :=
  evt024_received_take_nil (by simp [evt024_lifoRun, received, batches, lblBatch, Ne.symm hi]) k

/-- ✗ A store that delivers newest first meets the reading of line 3 without the order and
violates EVT-024 (subscriptions): after appending 1 and then 2 its subscriber receives `[2, 1]`. -/
@[evidence mutant EVT_024_B]
theorem EVT_024_B_mutant_lifo : Evt024AnyOrderRecv evt024_lifo ∧ ¬ EVT_024_B evt024_lifo := by
  refine ⟨?_, fun h => ?_⟩
  · rintro tr ⟨k', rfl⟩ k i
    rw [List.take_take]
    generalize min k k' = m
    refine ⟨(received i (evt024_lifoRun.take m)).reverse, List.reverse_perm _, ?_⟩
    by_cases hi : i = 0
    · subst hi
      rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | m
      all_goals try decide
      rw [List.take_of_length_le (by simp [evt024_lifoRun])]
      decide
    · rw [evt024_lifo_other hi]
      exact List.nil_sublist _
  · have := h.2.2.1 evt024_lifoRun ⟨9, rfl⟩ 9 0
    revert this
    decide

/-- The mutant reading of line 3 without "each at most once": what a subscription has received at
any point of a run, with repeats removed, is a subsequence of the appends so far. -/
def Evt024RepeatsRecv {E : Type} [BEq E] (S : SubSem E) : Prop :=
  ∀ tr, S tr → ∀ k i,
    List.Sublist (received i (tr.take k)).eraseDups (appended (storeOps (tr.take k)))

/-- A run of a store that hands its subscriber the same event twice: after 7 is appended, the
subscriber receives 7, then 7 again. -/
def evt024_twiceRun : List (SubLbl Nat) :=
  [.subscribe 0 (fun _ => true) none 1, .op (.append 7),
   .await 0, .pull 0, .recv 0 [7], .await 0, .pull 0, .recv 0 [7]]

/-- The store that delivers an event twice, as the runs it allows: the prefixes of
`evt024_twiceRun`. -/
def evt024_twice : SubSem Nat := fun tr => ∃ k, tr = evt024_twiceRun.take k

/-- ✗ A store that delivers one event twice meets the reading of line 3 without "each at most
once" and violates EVT-024 (subscriptions): after appending 7 once its subscriber receives
`[7, 7]`. -/
@[evidence mutant EVT_024_B]
theorem EVT_024_B_mutant_twice : Evt024RepeatsRecv evt024_twice ∧ ¬ EVT_024_B evt024_twice := by
  refine ⟨?_, fun h => ?_⟩
  · rintro tr ⟨k', rfl⟩ k i
    rw [List.take_take]
    generalize min k k' = m
    by_cases hi : i = 0
    · subst hi
      rcases m with _ | _ | _ | _ | _ | _ | _ | _ | m
      all_goals try decide
      rw [List.take_of_length_le (by simp [evt024_twiceRun])]
      decide
    · rw [evt024_received_take_nil
        (by simp [evt024_twiceRun, received, batches, lblBatch, Ne.symm hi]) m]
      exact List.nil_sublist _
  · have := h.2.2.1 evt024_twiceRun ⟨8, rfl⟩ 8 0
    revert this
    decide

/-- The mutant reading of line 3 on whole runs only: what a subscription received in a run the
store allows is a subsequence of the appends of that run. -/
def Evt024FifoWhole {E : Type} (S : SubSem E) : Prop :=
  ∀ tr, S tr → ∀ i, List.Sublist (received i tr) (appended (storeOps tr))

/-- A run of a store that hands its subscriber an event before it is appended: the subscriber
receives 7, and 7 is appended afterwards. -/
def evt024_earlyRun : List (SubLbl Nat) :=
  [.subscribe 0 (fun _ => true) none 1, .await 0, .pull 0, .recv 0 [7], .op (.append 7)]

/-- The store that delivers an event before its append, as the runs it allows: the empty run and
`evt024_earlyRun`, without the prefixes in between. -/
def evt024_early : SubSem Nat := fun tr => tr = [] ∨ tr = evt024_earlyRun

/-- ✗ A store that delivers an event before it is appended, and allows only whole runs in which
the append has caught up, meets the reading of line 3 on whole runs and violates EVT-024
(subscriptions): at the point of the delivery, 7 has not been appended ("only events appended to
the store"). -/
@[evidence mutant EVT_024_B]
theorem EVT_024_B_mutant_early : Evt024FifoWhole evt024_early ∧ ¬ EVT_024_B evt024_early := by
  refine ⟨?_, fun h => ?_⟩
  · rintro tr (rfl | rfl) i
    · exact List.nil_sublist _
    · by_cases hi : i = 0
      · subst hi; decide
      · rw [show received i evt024_earlyRun = [] by
          simp [evt024_earlyRun, received, batches, lblBatch, Ne.symm hi]]
        exact List.nil_sublist _
  · have := h.2.2.1 evt024_earlyRun (Or.inr rfl) 4 0
    revert this
    decide

/-- The store that serves one subscriber at a time: the reference debug store's runs in which no
subscription other than 0 is made. -/
def evt024_single : SubSem Nat := fun tr => refDebugSub tr ∧ ∀ k, k ≠ 0 → subParams k tr = none

/-- ✗ A store that serves one subscriber at a time meets every line but line 4 and violates
EVT-024 (subscriptions), line 4 (AC3): once subscription 0 is made, no further subscriber can
join. -/
@[evidence mutant EVT_024_B]
theorem EVT_024_B_mutant_single : Evt024NoJoin evt024_single ∧ ¬ EVT_024_B evt024_single := by
  refine ⟨⟨⟨evt024_refDebug_start, fun k _ => rfl⟩, fun tr h hd e => ?_,
    fun tr h k i => evt024_ref_fifo h.1.1 k i, ?_⟩, fun h => ?_⟩
  · refine ⟨evt024_refDebug_append tr h.1 hd e, fun k hk => ?_⟩
    rw [subParams_append, h.2 k hk]
    rfl
  · intro tr h _ hd i hi
    obtain ⟨tr', hr, href, hrecv⟩ := evt024_refDebug_catchUp h.1 hd hi
    refine ⟨tr', evt024_recv_receive hr, ⟨href, fun k hk => ?_⟩,
      by rw [hrecv]; exact List.suffix_refl _⟩
    rw [subParams_append, h.2 k hk, evt024_recv_params hr k]
    rfl
  · let tr0 : List (SubLbl Nat) := [.subscribe 0 (fun _ => true) none 1]
    have hrun : evt024_single tr0 := by
      refine ⟨⟨by decide, ?_⟩, fun k hk => ?_⟩
      · intro l hl
        simp only [tr0, List.mem_singleton] at hl
        subst hl; exact evt024_debug_subscribe 0
      · simp [tr0, subParams, lblParams, Ne.symm hk]
    obtain ⟨j, hj, hS⟩ := h.2.2.2.1 tr0 hrun (by decide)
    have hj0 : j ≠ 0 := by
      rintro rfl
      revert hj
      decide
    have := hS.2 j hj0
    rw [subParams_append, hj] at this
    simp [subParams, lblParams] at this

/-- The run in which two debug subscribers subscribe and then one event is appended. -/
def evt024_twoSubs : List (SubLbl Nat) :=
  [.subscribe 0 (fun _ => true) none 1, .subscribe 1 (fun _ => true) none 1, .op (.append 7)]

/-- The store that delivers to its first subscriber only: the reference debug store's runs in
which no subscription other than 0 receives an event. -/
def evt024_firstOnly : SubSem Nat := fun tr => refDebugSub tr ∧ ∀ k, k ≠ 0 → received k tr = []

/-- ✗ A store that delivers to its first subscriber only meets every line but line 5 and violates
EVT-024 (subscriptions), line 5: after two subscribers subscribe and 7 is appended, subscription 1
can never receive 7. -/
@[evidence mutant EVT_024_B]
theorem EVT_024_B_mutant_firstOnly :
    Evt024NoCatchUp evt024_firstOnly ∧ ¬ EVT_024_B evt024_firstOnly := by
  refine ⟨⟨⟨evt024_refDebug_start, fun k _ => rfl⟩, fun tr h hd e => ?_,
    fun tr h k i => evt024_ref_fifo h.1.1 k i, fun tr h hd => ?_⟩, fun h => ?_⟩
  · refine ⟨evt024_refDebug_append tr h.1 hd e, fun k hk => ?_⟩
    rw [received_snoc, h.2 k hk]
    rfl
  · obtain ⟨j, hj, href⟩ := evt024_refDebug_join tr h.1 hd
    refine ⟨j, hj, href, fun k hk => ?_⟩
    rw [received_snoc, h.2 k hk]
    rfl
  · have hrun : evt024_firstOnly evt024_twoSubs := by
      refine ⟨⟨by decide, ?_⟩, fun k _ => ?_⟩
      · intro l hl
        simp only [evt024_twoSubs, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact evt024_debug_subscribe 0
        · exact evt024_debug_subscribe 1
        · trivial
      · simp [evt024_twoSubs, received, batches, lblBatch]
    have hdf : ∀ l ∈ evt024_twoSubs, l.DebugForm := hrun.1.2
    obtain ⟨tr', -, hS, hsuf⟩ := h.2.2.2.2 evt024_twoSubs hrun hdf (by decide) 1 (by decide)
    rw [hS.2 1 (by decide)] at hsuf
    have h7 : appendsAfter 1 evt024_twoSubs = [7] := by decide
    rw [h7] at hsuf
    have := hsuf.length_le
    simp at this

/-! #### A store that delivers only when it is closed

The slip: a broadcaster whose queued deliveries run only in `close()` (Java's `close()` waits for
the pending broadcasts in `shutdownBroadcast`; a batching broadcaster whose last flush is there).
While the store is open no subscriber receives anything; on `close()` every subscriber gets every
event appended since it subscribed, in order. Modelled as the reference debug store with the
`close()` label (`drop`) erased, so that it does not unregister the subscribers, restricted to the
runs in which no receive happens before the store is closed. -/

/-- No receive happens before the first `close()` of the store. -/
def evt024_quietUntilClose : List (SubLbl Nat) → Bool
  | [] => true
  | .drop :: _ => true
  | l :: tr => !evt024Receive l && evt024_quietUntilClose tr

/-- The labels of a run other than the store's `close()`. -/
def evt024_eraseClose (tr : List (SubLbl Nat)) : List (SubLbl Nat) := tr.filter fun l => !lblDrop l

/-- The store that delivers only when it is closed. -/
def evt024_flushOnClose : SubSem Nat :=
  fun tr => refDebugSub (evt024_eraseClose tr) ∧ evt024_quietUntilClose tr = true

theorem evt024_eraseClose_open {tr : List (SubLbl Nat)} (hd : dropped tr = false) :
    evt024_eraseClose tr = tr := by
  unfold evt024_eraseClose
  rw [List.filter_eq_self]
  intro l hl
  have : lblDrop l = false := by
    simp only [dropped, List.any_eq_false] at hd
    simpa using hd l hl
  simp [this]

theorem evt024_eraseClose_append (a b : List (SubLbl Nat)) :
    evt024_eraseClose (a ++ b) = evt024_eraseClose a ++ evt024_eraseClose b := by
  simp [evt024_eraseClose]

theorem evt024_eraseClose_receive {tr' : List (SubLbl Nat)}
    (h : ∀ l ∈ tr', evt024Receive l = true) : evt024_eraseClose tr' = tr' := by
  unfold evt024_eraseClose
  rw [List.filter_eq_self]
  intro l hl
  have := h l hl
  cases l <;> simp_all [evt024Receive, lblDrop]

theorem evt024_quiet_snoc {a : List (SubLbl Nat)} {l : SubLbl Nat} (hd : dropped a = false)
    (hq : evt024_quietUntilClose a = true) (hl : evt024Receive l = false) :
    evt024_quietUntilClose (a ++ [l]) = true := by
  induction a with
  | nil => cases l <;> simp_all [evt024_quietUntilClose, evt024Receive]
  | cons x a ih =>
    cases x <;> simp_all [evt024_quietUntilClose, dropped, lblDrop, evt024Receive]

theorem evt024_quiet_close {a b : List (SubLbl Nat)} (hd : dropped a = false)
    (hq : evt024_quietUntilClose a = true) :
    evt024_quietUntilClose (a ++ .drop :: b) = true := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    cases x <;> simp_all [evt024_quietUntilClose, dropped, lblDrop, evt024Receive]

theorem evt024_received_eraseClose (i : Nat) (tr : List (SubLbl Nat)) :
    received i (evt024_eraseClose tr) = received i tr := by
  induction tr with
  | nil => rfl
  | cons l tr ih =>
    cases l <;> simp_all [evt024_eraseClose, received_cons, lblDrop, lblBatch]

theorem evt024_storeOps_eraseClose (tr : List (SubLbl Nat)) :
    storeOps (evt024_eraseClose tr) = storeOps tr := by
  induction tr with
  | nil => rfl
  | cons l tr ih =>
    cases l <;> simp_all [evt024_eraseClose, storeOps, lblOp, lblDrop]

/-- While the store is open, no subscriber of the store that delivers only when it is closed
receives anything. -/
theorem evt024_flush_nothing (i : Nat) :
    ∀ tr : List (SubLbl Nat), dropped tr = false → evt024_quietUntilClose tr = true →
      received i tr = []
  | [], _, _ => rfl
  | l :: tr, hd, hq => by
    have hl : lblDrop l = false := by
      cases l <;> simp_all [dropped, lblDrop]
    have hd' : dropped tr = false := by
      simp only [dropped, List.any_cons, hl, Bool.false_or] at hd; exact hd
    cases hr : evt024Receive l with
    | true => cases l <;> simp_all [evt024_quietUntilClose, evt024Receive, lblDrop]
    | false =>
      have hq' : evt024_quietUntilClose tr = true := by
        cases l <;> simp_all [evt024_quietUntilClose, evt024Receive, lblDrop]
      have hb : lblBatch i l = none := by
        cases l <;> simp_all [evt024Receive, lblBatch]
      rw [received_cons, hb, evt024_flush_nothing i tr hd' hq']
      rfl

theorem evt024_flush_open {tr : List (SubLbl Nat)} (h : evt024_flushOnClose tr)
    (hd : dropped tr = false) : refDebugSub tr ∧ evt024_quietUntilClose tr = true := by
  have h0 := h
  unfold evt024_flushOnClose at h0
  rwa [evt024_eraseClose_open hd] at h0

/-- The mutant reading of line 5 whose continuation is limited only to holding no store
operation: it may then close the store, close subscriptions or add subscribers. -/
def Evt024CatchUpOps {E : Type} (S : SubSem E) : Prop :=
  ∀ tr, S tr → (∀ l ∈ tr, l.DebugForm) → dropped tr = false →
    ∀ i, (subParams i tr).isSome = true →
      ∃ tr', storeOps tr' = [] ∧ S (tr ++ tr') ∧
        List.IsSuffix (appendsAfter i tr) (received i (tr ++ tr'))

/-- The mutant reading of EVT-024 (subscriptions) with line 5 replaced by
`Evt024CatchUpOps`. -/
def Evt024OpsOnly {E : Type} (S : SubSem E) : Prop :=
  Evt024NoCatchUp S ∧ Evt024CatchUpOps S

/-- ✗ A store that delivers nothing while it is open and every event when it is closed meets
lines 1 to 4 and the reading of line 5 whose continuation may close the store, and violates
EVT-024 (subscriptions), line 5 ("*While* a debug event store is open, ... still be able to
receive"): after subscription 0 is made and 7 is appended, no run of receives while the store is
open brings 7 to subscription 0. -/
@[evidence mutant EVT_024_B]
theorem EVT_024_B_mutant_flushOnClose :
    Evt024OpsOnly evt024_flushOnClose ∧ ¬ EVT_024_B evt024_flushOnClose := by
  refine ⟨⟨⟨⟨⟨by decide, fun l hl => by cases hl⟩, rfl⟩, ?_, ?_, ?_⟩, ?_⟩, fun h => ?_⟩
  · -- line 2
    intro tr h hd e
    have h := evt024_flush_open h hd
    refine ⟨?_, evt024_quiet_snoc hd h.2 rfl⟩
    rw [evt024_eraseClose_append, evt024_eraseClose_open hd]
    exact evt024_refDebug_append tr h.1 hd e
  · -- line 3, at every point of a run
    intro tr h k i
    have hp : refSub (evt024_eraseClose (tr.take k)) := by
      unfold evt024_eraseClose
      exact evt024_refSub_prefix h.1.1 ((List.take_prefix k tr).filter _)
    have := refSub_received_appended hp i
    rwa [evt024_received_eraseClose, evt024_storeOps_eraseClose] at this
  · -- line 4
    intro tr h hd
    have h := evt024_flush_open h hd
    obtain ⟨j, hj, hS⟩ := evt024_refDebug_join tr h.1 hd
    refine ⟨j, hj, ?_, evt024_quiet_snoc hd h.2 rfl⟩
    rw [evt024_eraseClose_append, evt024_eraseClose_open hd]
    exact hS
  · -- line 5 with a continuation that closes the store, then drains
    intro tr h _ hd i hi
    have h := evt024_flush_open h hd
    obtain ⟨tr'', hr, href, hrecv⟩ := evt024_refDebug_catchUp h.1 hd hi
    refine ⟨.drop :: tr'', ?_, ⟨?_, evt024_quiet_close hd h.2⟩, ?_⟩
    · simpa [storeOps, lblOp] using evt024_recv_ops hr
    · rw [evt024_eraseClose_append, evt024_eraseClose_open hd]
      have : evt024_eraseClose (SubLbl.drop :: tr'') = tr'' := by
        rw [show (SubLbl.drop :: tr'' : List (SubLbl Nat)) = [.drop] ++ tr'' from rfl,
          evt024_eraseClose_append, evt024_eraseClose_receive (evt024_recv_receive hr)]
        rfl
      rw [this]; exact href
    · have : received i (tr ++ SubLbl.drop :: tr'') = received i (tr ++ tr'') := by
        simp [received_append, received_cons, lblBatch]
      rw [this, hrecv]
      exact List.suffix_refl _
  · -- line 5 fails
    let tr0 : List (SubLbl Nat) := [.subscribe 0 (fun _ => true) none 1, .op (.append 7)]
    have hdf : ∀ l ∈ tr0, l.DebugForm := by
      intro l hl
      simp only [tr0, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact evt024_debug_subscribe 0
      · trivial
    have h0 : evt024_flushOnClose tr0 := by
      refine ⟨⟨by decide, ?_⟩, by decide⟩
      rw [evt024_eraseClose_open (by decide)]
      exact hdf
    obtain ⟨tr', hr, hS, hsuf⟩ := h.2.2.2.2 tr0 h0 hdf (by decide) 0 (by decide)
    have hd : dropped (tr0 ++ tr') = false := by
      rw [dropped_append, evt024_receive_dropped hr]; decide
    rw [evt024_flush_nothing 0 _ hd hS.2] at hsuf
    have h7 : appendsAfter 0 tr0 = [7] := by decide
    rw [h7] at hsuf
    simpa using hsuf.length_le

/-! ### Non-vacuity: the test derivation on the reference -/

/-- The test derivation on the reference debug store: two subscribers subscribe, 7 is appended,
and each receives `[7]`, every event appended since it subscribed; so lines 3 and 5 are not
vacuous and two subscribers are active at once (AC3). -/
@[evidence nonvacuous EVT_024_B]
theorem EVT_024_B_nonvacuous :
    refDebugSub subRunTwo ∧ received 0 subRunTwo = [7] ∧ received 1 subRunTwo = [7] ∧
      appendsAfter 1 subRunTwo = [7] := by
  obtain ⟨h, h0, h1⟩ := subRunTwo_facts
  exact ⟨h, h0, h1, by decide⟩

end Libpetri.Spec
