import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryStore
import Libpetri.Spec.Req.EVT_022
import Libpetri.Spec.Text.EVT_020

set_option linter.missingDocs true

/-!
# EVT-020: EventStore Interface (`spec/08-events-observability.md`)

The interface every event store meets. Under ruling D29 (a) its one observable promise is the
store law: the list `events()` returns is a subsequence of the events appended to the store, in
append order (`List.Sublist` against the glossary's `appended`). Which appended events a store
leaves out is each store's own requirement (the in-memory store keeps all since the last clear,
[EVT-021]; the noop store none, [EVT-022]; the bounded store the newest ones, [EVT-024]).

Whether the list is a copy or a live view is not specified, so the line reads the list both at
the call and at every later point (`S.read h h'`) and compares it with every append so far
(`appended (h ++ h')`). A copy and a live view both meet that; a live view that later shows the
events out of order (a ring buffer handed out raw) does not, since it is then no view of the
store.

The witnesses are the reference in-memory, noop and bounded stores of `GlossaryStore.lean`. The
wrong stores are a store that lists its events newest first, a decorator that returns two
copies of what it holds and a bounded store that hands out its raw ring buffer; a store that
shows an event nobody appended is forbidden. The live views TypeScript's in-memory and debug
stores hand out meet the line, which is the evidence that the block leaves the copy question
open.

AC3 (the enabled flag decides whether the executor appends any event to the store) is the
glossary fact `storeSink` (design events.md SC-8): a definition, not a constraint on a store.
Its consequence for a store that meets this block is `evt020_sink_disabled`: whatever an
executor emits, a store that reports itself not enabled shows nothing of it.

The line reads both lists through the store's own normalisation `S.norm` (glossary
`StoreObs.norm`): the identity for every store but the Python binding's, which strips some token
payloads before keeping an event, so for it `S.norm` is that strip (the second quoted sentence;
section "The Python binding's store"). `evt020_id_iff` gives the law itself where `S.norm = id`.
-/

namespace Libpetri.Spec

/-! ## Lemmas -/

/-- Folding a history onto `acc` keeps a subsequence of `acc` followed by the history's appends:
an append adds its event at the end, a clear drops everything kept so far. -/
theorem evt020_foldl_sublist {E : Type} (h : List (StoreOp E)) (acc : List E) :
    List.Sublist (h.foldl stepOp acc) (acc ++ appended h) := by
  induction h generalizing acc with
  | nil => simp [appended]
  | cons o h ih =>
    cases o with
    | append e =>
      have := ih (acc ++ [e])
      simpa [List.foldl, stepOp, appended, List.filterMap_cons] using this
    | clear =>
      have := ih []
      simp only [List.nil_append] at this
      have hc : appended (StoreOp.clear :: h) = appended h := by
        simp [appended]
      rw [hc]
      exact this.trans (List.sublist_append_right acc _)

/-- The events a store that keeps every event retains are a subsequence of the appended
events: the appends since the last clear, in append order. -/
theorem evt020_retained_sublist {E : Type} (h : List (StoreOp E)) :
    List.Sublist (retained h) (appended h) := by
  simpa [retained] using evt020_foldl_sublist h []

/-- The events appended by a history followed by further operations are the events the history
appended followed by those the further operations appended. -/
theorem evt020_appended_append {E : Type} (h h' : List (StoreOp E)) :
    appended (h ++ h') = appended h ++ appended h' := by
  simp [appended, List.filterMap_append]

/-- A list that is a subsequence of what a history appended stays one of what the history and
any further operations appended. -/
theorem evt020_sublist_later {E : Type} {l : List E} {h : List (StoreOp E)}
    (hl : List.Sublist l (appended h)) (h' : List (StoreOp E)) :
    List.Sublist l (appended (h ++ h')) := by
  rw [evt020_appended_append]
  exact hl.trans (List.sublist_append_left _ _)

/-! ## EVT-020: EventStore Interface -/

requirement EVT_020
  id "EVT-020"
  title "EventStore Interface"
  kind F
  scope "every event store (the interface: the in-memory, noop, logging, debug and debug-aware stores of Java, TypeScript and Rust, and the Python binding's store)"
  source verbatim "spec/08-events-observability.md"
  covers EVT_020.s1, EVT_020.s2, EVT_020.s3
  reading "For every store S over any event type E, with S.norm the store's own normalisation of an event:"
          "after every history h of appends and clears, the list a call of events() returns, as it shows once any further operations h' have run (S.read h h', the call itself being h' = []), read through S.norm, is a sublist of the events h and h' appended, in append order (appended (h ++ h')), read through S.norm."
  assumes "The normalisation S.norm is part of the store's observation and is fixed by the store and how the caller configured it, not chosen to meet the line (glossary: StoreObs.norm, the identity unless a store says otherwise): it is the identity for every store but the Python binding's in-memory store, so for them the line is the subsequence law itself (evt020_id_iff), and for the binding's store it is the strip of the capture filter the caller gave it as capture_tokens (see below). A normalisation the store's configuration does not declare is no reading of the block: read through a constant, every store would meet the line."
          "The model is the observation of one store, S : StoreObs E (glossary: Event store): its enabled flag, whether it provides clear(), and read h h', the list a call of events() made after the history h shows once the further operations h' have run. The event type E is a parameter: the line says nothing about what an event holds. The first quoted sentence is the line, at the call (h' = []) and at every later point. The second is why the line compares with every append so far (appended (h ++ h')) and not only with the appends before the call: ruling D29 (a) leaves open whether the list is a copy (Java's List.copyOf, the Python binding's new list; Rust lends a borrow that no append can change while it is held) or a live view (TypeScript's in-memory and debug stores return their own array), and both meet the line (EVT_020_reference, EVT_020_bounded, evt020_allows_live, evt020_allows_liveBounded). What the line asks of a live view is that it stays a view of the store, a subsequence of the appends in append order at every later point; a bounded store that hands out its raw ring buffer breaks that (EVT_020_mutant_ringView), and evt020_atCall gives the reading at the call alone."
          "AC2 (events() returns a subsequence of the appended events, in append order; whether that list is a copy or a live view is not specified) is the line, under ruling D29 (a), which words the body bullet and AC2 so (clash evt-b#6): the noop store returns no event (EVT-022) and the bounded debug stores evict the oldest (EVT-024). That the in-memory store returns every event appended since the last clear, as a copy, is EVT-021's."
          "The line compares with every append of the history, clears ignored, so it says nothing about what clear() does: a store whose clear() keeps every event meets it (evt020_allows_keepAcrossClear). What a store shows after clear(), where it provides clear() (ruling D29 (a)), is EVT-021's."
          "AC3 (isEnabled() controls whether the executor appends events to the store) and the body sentence that an executor appends events to a store only while the store reports itself as enabled are the glossary fact storeSink, not a line of this block (design events.md SC-8): what an executor appends to a store is storeSink S tr, every emitted event when S reports itself enabled and nothing otherwise. The markdown words that sentence as a statement of how events reach a store and not as a shall, since no store and no executor model can fail a definition. The flag constrains the executor and not the store: a store that reports itself not enabled and keeps what a caller appends to it directly meets the line (evt020_allows_disabledKeeps), and evt020_sink_disabled shows that a store meeting the line which reports itself not enabled shows nothing an executor emitted. The executor blocks of wave W7 emit through storeSink. Whether an executor builds the event objects of a disabled store at all is kind Q (clash evt-b#12, PERF-010 and ruling D34, EVT-022 AC4): TypeScript and the Java bitmap executor build them and test the flag only when appending."
          "The enabled flag is a constant of the store for a whole run (clash evt-b#11): TypeScript reads isEnabled() once when the executor is built, Java when it is built and again at every emit, Rust fixes it at compile time as the store type's ENABLED constant. A store whose isEnabled() answer changes during a run is outside the model."
          "AC1 (append() is safe to call from any thread) is kind A and has no line, although the requirement as a whole is kind F: a history is one sequence of operations, and appends made at once from several threads are read in the order in which they take effect (Java's in-memory and debug stores append to a ConcurrentLinkedQueue). The obligation has content in Java only, where captured logs and ActionTimedOut are appended from threads other than the orchestrator's; in Rust append takes exclusive access (&mut self), TypeScript runs on one thread, and the Python binding's store appends under a mutex. That no concurrent append is lost is the in-memory store's promise (EVT-021 AC2), not this block's."
          "The three bullets of the body (append, events, isEnabled) name the operations: append is an operation of a history, events() is read, isEnabled() is the enabled flag. size() and isEmpty(), which the runtimes also offer, and the query helpers over events() (EVT-030) are not named by this block. Rust has no isEnabled() method; the store type's associated constant ENABLED plays its part (EventStore::ENABLED in rust/libpetri-event/src/event_store.rs)."
          "Decorators: Java's logging store (EVT-023) and the debug-aware stores of all three runtimes return the list of the store they wrap, so they meet the line whenever the wrapped store does and receives its appends only through the decorator (evt020_forward, which reads the decorator's history as the wrapped store's). Appends made directly to the wrapped store, by a caller that kept a reference to it, are outside the line: they show in the decorator's events() without having been appended to the decorator. Its events() called with filter, limit or offset arguments is a query (EVT-030); the call without them is the events() of this block. The Python run sink's own events() (the trait method) returns the empty list and is never called by the executor."
          "The Python binding's store. The executor writes it through a Rust store, RunStore (rust/libpetri-py/src/events.rs): when capture_tokens is a list of places, RunStore's append strips the token payload of a TokenAdded or TokenRemoved event on a place outside that list (RunStore::filter_payload) and pushes the stripped event into the in-memory store, and the executor attaches payloads at all only because RunStore asks for them (its CAPTURES_TOKENS constant). This block reads that store as the executor sees it, with RunStore in front of it, which is how the second quoted sentence speaks of it: the appended events are the events the executor emits, with their payloads, and S.norm is the capture filter's strip, the normalisation that removes the payload of a token event on a place outside the filter (evt020_pyStrip). EVT-021 reads the same store behind RunStore, where the appended events are the stripped events RunStore pushes, and EVT_021_allows_python shows the two readings are one store: what this block's model of it (evt020_pyStore) shows after a history is what EVT-021's in-memory store without clear() shows after the history with every append stripped. evt020_allows_python shows the binding's store meets the line so read, at every capture filter. Read through the identity, it fails the line (evt020_python_literal), since it shows the stripped event, which the executor never appended. What the line asks of such a store is that what it shows agrees with the strip of the filter it was given: a store given the capture filter of place 0 that applies the inverted strip (it removes the payloads inside the filter and keeps the others) fails it (evt020_python_disagrees). The inverted strip of a filter is the strip of the complementary filter (evt020_pyStripInv_compl), so the same store read through the inverted strip is the binding's store given the complementary filter and meets the line (evt020_python_invCompl): the line constrains which payloads a store removes only relative to the filter it was given, which is why S.norm is fixed by that filter and not by what the store shows. Which places a caller lists in capture_tokens is the caller's choice, and no requirement constrains it. A store meeting the line through the identity meets it through any normalisation (evt020_through_of)."
          "The test derivation (append from several threads; events() returns only appended events, each at most once, in the order the appends took effect, and on the in-memory store all of them) is EVT_020_nonvacuous for the in-memory store: after appends whose order mixes two callers, events() returns all of them in that order, a live view of it still a subsequence after one more append, and the newest-first store fails the line on the same history. That the in-memory store returns every one of them is EVT-021's line, not this block's."
  signoff "2026-11-13 de8415d9c32f1753 ai"
  statement : ∀ {E : Type}, StoreObs E → Prop :=
    fun S => ∀ h h', List.Sublist ((S.read h h').map S.norm) ((appended (h ++ h')).map S.norm)

/- The pinned readable form of EVT-020: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_020 : {E : Type} → StoreObs E → Prop :=
fun {E} S => ∀ (h h' : List (StoreOp E)), (List.map S.norm (S.read h h')).Sublist (List.map S.norm (appended (h ++ h')))
-/
#guard_msgs in #print EVT_020

/-- For a store whose normalisation is the identity, as every store's but the Python binding's
is, EVT-020 is the subsequence law itself. -/
theorem evt020_id_iff {E : Type} (S : StoreObs E) (hn : S.norm = id) :
    EVT_020 S ↔ ∀ h h', List.Sublist (S.read h h') (appended (h ++ h')) := by
  simp [EVT_020, hn]

/-- EVT-020 at the call: the list a call of `events()` returns is a subsequence of the events
appended before the call. -/
theorem evt020_atCall {E : Type} {S : StoreObs E} (hS : EVT_020 S) (hn : S.norm = id)
    (h : List (StoreOp E)) :
    List.Sublist (S.read h []) (appended h) := by
  simpa using (evt020_id_iff S hn).1 hS h []

/-! ### The reference stores -/

/-- The reference in-memory store satisfies EVT-020: it returns a copy of the events appended
since the last clear, in append order. -/
@[evidence holds EVT_020]
theorem EVT_020_reference {E : Type} : EVT_020 (refMemStore (E := E)) :=
  (evt020_id_iff _ rfl).2 fun h h' => evt020_sublist_later (evt020_retained_sublist h) h'

/-- The reference noop store satisfies EVT-020: the empty list is a subsequence of anything. -/
@[evidence holds EVT_020]
theorem EVT_020_noop {E : Type} : EVT_020 (refNoopStore (E := E)) :=
  (evt020_id_iff _ rfl).2 fun _ _ => List.nil_sublist _

/-- The reference bounded store meets EVT-020 at every capacity: the newest `c` retained events
are a suffix of the retained events. -/
theorem evt020_bounded {E : Type} (c : Nat) : EVT_020 (refBoundedStore (E := E) c) :=
  (evt020_id_iff _ rfl).2 fun h h' =>
    evt020_sublist_later ((List.drop_sublist _ _).trans (evt020_retained_sublist h)) h'

/-- The reference bounded store at the debug stores' default capacity of 10,000 satisfies
EVT-020 ([EVT-024]). -/
@[evidence holds EVT_020]
theorem EVT_020_bounded {E : Type} : EVT_020 (refBoundedStore (E := E) 10000) :=
  evt020_bounded 10000

/-! ### Consequences -/

/-- A store that meets EVT-022 (the noop store) meets EVT-020. -/
theorem evt020_of_evt022 {E : Type} {S : StoreObs E} (hS : EVT_022 S) : EVT_020 S := by
  intro h h'
  rw [hS.1 h h']
  exact List.nil_sublist _

/-- A decorator that answers `events()` with the list of a store that meets EVT-020 meets it,
whatever it reports as enabled and whether it provides `clear()`: Java's logging store, the
debug-aware stores. The decorator's history is read as the wrapped store's, so this holds when
the wrapped store receives its appends only through the decorator. -/
theorem evt020_forward {E : Type} {S : StoreObs E} (hS : EVT_020 S) (en hc : Bool) :
    EVT_020 ({ enabled := en, hasClear := hc, read := S.read, norm := S.norm } : StoreObs E) :=
  hS

/-- Every event a store that meets EVT-020 returns was appended to it, and it returns no more
events than were appended. -/
theorem evt020_mem_length {E : Type} {S : StoreObs E} (hS : EVT_020 S) (hn : S.norm = id)
    (h : List (StoreOp E)) :
    (∀ e ∈ S.read h [], e ∈ appended h) ∧ (S.read h []).length ≤ (appended h).length :=
  ⟨fun _ he => (evt020_atCall hS hn h).subset he, (evt020_atCall hS hn h).length_le⟩

/-- AC3 on a store that meets EVT-020: whatever events an executor emits, a store that reports
itself not enabled shows none of them, because the glossary's `storeSink` hands it nothing. -/
@[evidence cites "EVT-020" "AC3: an executor appends nothing to a store that reports itself not enabled, so such a store shows no emitted event (glossary storeSink)"]
theorem evt020_sink_disabled {E : Type} {S : StoreObs E} (hS : EVT_020 S) (hn : S.norm = id)
    (hd : S.enabled = false) (tr : List E) : S.read (storeSink S tr) [] = [] := by
  have := evt020_atCall hS hn (storeSink S tr)
  rw [storeSink_disabled hd tr] at this ⊢
  exact List.eq_nil_of_sublist_nil this

/-- AC3 on a store that meets EVT-020 and reports itself enabled: it shows a subsequence of the
emitted events, in emission order. -/
theorem evt020_sink_enabled {E : Type} {S : StoreObs E} (hS : EVT_020 S) (hn : S.norm = id)
    (he : S.enabled = true) (tr : List E) : List.Sublist (S.read (storeSink S tr) []) tr := by
  have := evt020_atCall hS hn (storeSink S tr)
  rwa [storeSink_enabled he tr] at this

/-! ### What the line leaves open -/

/-- ✓ The live in-memory store meets EVT-020: at the call and at every later point its array
holds the retained events. Ruling D29 (a) leaves the copy unspecified, and the line does not
fix it. -/
@[evidence allows EVT_020]
theorem evt020_allows_live : EVT_020 (liveMemStore (E := Nat)) :=
  (evt020_id_iff _ rfl).2 fun h h' => evt020_retained_sublist (h ++ h')

/-- The live bounded store of capacity `c` (TypeScript `DebugEventStore`,
`append` and `events` in `debug-event-store.ts`): `events()` returns the store's own array, and an append on a full
store removes the oldest event from its front (`shift`). -/
def evt020_liveBounded (c : Nat) : StoreObs Nat where
  enabled := true
  hasClear := false
  read h h' := (refBoundedStore c).read (h ++ h') []

/-- ✓ The live bounded store meets EVT-020 at every capacity: whenever it is looked at, its array
holds the newest retained events in append order. -/
@[evidence allows EVT_020]
theorem evt020_allows_liveBounded : ∀ c, EVT_020 (evt020_liveBounded c) :=
  fun c => (evt020_id_iff _ rfl).2 fun h h' => evt020_atCall (evt020_bounded c) rfl (h ++ h')

/-- A store that keeps every append and ignores `clear()`. -/
def evt020_keepAcrossClear : StoreObs Nat where
  enabled := true
  hasClear := true
  read h h' := appended (h ++ h')

/-- ✓ A store whose `clear()` keeps every event meets EVT-020: what a store shows after
`clear()` is [EVT-021]'s, not this line's. After appending 1 and clearing it still shows `[1]`. -/
@[evidence allows EVT_020]
theorem evt020_allows_keepAcrossClear :
    EVT_020 evt020_keepAcrossClear ∧
      evt020_keepAcrossClear.read [.append 1, .clear] [] = [1] :=
  ⟨(evt020_id_iff _ rfl).2 fun _ _ => List.Sublist.refl _, by decide⟩

/-- ✓ The enabled flag constrains the executor, not the store: a store that reports itself not
enabled and keeps direct appends meets EVT-020, and still shows nothing an executor emitted
(`storeSink` hands it no event). -/
@[evidence allows EVT_020]
theorem evt020_allows_disabledKeeps :
    EVT_020 (disabledKeepStore (E := Nat)) ∧
    (disabledKeepStore (E := Nat)).read [.append 1] [] = [1] ∧
    (disabledKeepStore (E := Nat)).read
      (storeSink (disabledKeepStore (E := Nat)) [1, 2]) [] = [] :=
  ⟨(evt020_id_iff _ rfl).2 fun h h' => evt020_sublist_later (evt020_retained_sublist h) h', by decide,
    by decide⟩

/-! ### Wrong stores, one per load-bearing part of the line -/

/-- The mutant reading without the order: `events()` returns appended events, each append at
most once, in any order (a rearrangement of a subsequence of the appends). -/
def AnyOrder {E : Type} (S : StoreObs E) : Prop :=
  ∀ h, ∃ l, List.Perm l (S.read h []) ∧ List.Sublist l (appended h)

/-- ✗ A store that lists its events newest first meets the reading without order and violates
EVT-020 ("in the order they were appended"): after appending 1 and then 2 it returns `[2, 1]`. -/
@[evidence mutant EVT_020]
theorem EVT_020_mutant_newestFirst :
    AnyOrder (newestFirstStore (E := Nat)) ∧ ¬ EVT_020 (newestFirstStore (E := Nat)) := by
  refine ⟨fun h => ?_, fun hS => ?_⟩
  · exact ⟨retained h, (List.reverse_perm _).symm, evt020_retained_sublist h⟩
  · have := (evt020_id_iff _ rfl).1 hS [.append 1, .append 2] []
    revert this
    decide

/-- The mutant reading without multiplicity: every event `events()` returns was appended (the
membership reading of "snapshot of all events"). -/
def OnlyAppended {E : Type} (S : StoreObs E) : Prop :=
  ∀ h, ∀ e ∈ S.read h [], e ∈ appended h

/-- A debug-aware store that answers `events()` with its primary store's list followed by its
debug store's list, both holding every event appended since the last clear. -/
def evt020_bothLists {E : Type} : StoreObs E where
  enabled := true
  hasClear := true
  read h _ := retained h ++ retained h

/-- ✗ A store that returns every event twice meets the membership reading and violates EVT-020
("each append at most once"): after one append of 7 it returns `[7, 7]`. -/
@[evidence mutant EVT_020]
theorem EVT_020_mutant_bothLists :
    OnlyAppended (evt020_bothLists (E := Nat)) ∧ ¬ EVT_020 (evt020_bothLists (E := Nat)) := by
  refine ⟨fun h e he => ?_, fun hS => ?_⟩
  · have he' : e ∈ retained h := by
      simpa [evt020_bothLists] using he
    exact (evt020_retained_sublist h).subset he'
  · have := (evt020_id_iff _ rfl).1 hS [.append 7] []
    revert this
    decide

/-- The mutant reading at the call only: the list a call of `events()` returns is a
subsequence of the appends at the call, and nothing is asked of what a live view shows later. -/
def AtCall {E : Type} (S : StoreObs E) : Prop :=
  ∀ h, List.Sublist (S.read h []) (appended h)

/-- One operation on a ring buffer as the caller's held array sees it: fill while short of
capacity, then overwrite slot `i` and advance; a clear empties it. -/
def evt020_ringStep (c : Nat) : List Nat × Nat → StoreOp Nat → List Nat × Nat
  | (buf, i), .append e => if buf.length < c then (buf ++ [e], i) else (buf.set i e, (i + 1) % c)
  | _, .clear => ([], 0)

/-- A bounded store of capacity `c` that hands out its raw ring buffer (an O(1)-eviction
rewrite of TypeScript's `DebugEventStore`): `events()` rotates the buffer to start at the oldest
event and returns the buffer itself, and an append on a full buffer overwrites the oldest slot
in place. -/
def evt020_ringView (c : Nat) : StoreObs Nat where
  enabled := true
  hasClear := true
  read h h' := (h'.foldl (evt020_ringStep c) ((refBoundedStore c).read h [], 0)).1

/-- ✗ A bounded store that hands out its raw ring buffer meets the reading at the call (there
it is the reference bounded store) and violates EVT-020 ("in the order they were appended", the
list being "a live view of the store"): after appending 1, 2 and 3 to a store of capacity 3, the
list a call returned shows `[4, 2, 3]` once 4 is appended, while the store holds `[2, 3, 4]`. -/
@[evidence mutant EVT_020]
theorem EVT_020_mutant_ringView : AtCall (evt020_ringView 3) ∧ ¬ EVT_020 (evt020_ringView 3) := by
  refine ⟨fun h => evt020_atCall (evt020_bounded 3) rfl h, fun hS => ?_⟩
  have := (evt020_id_iff _ rfl).1 hS [.append 1, .append 2, .append 3] [.append 4]
  revert this
  decide

/-- A store that shows an event nobody appended: its `events()` starts with a fixed event. -/
def evt020_seeded : StoreObs Nat where
  enabled := true
  hasClear := false
  read h _ := 0 :: retained h

/-- ✗ A store that shows an event nobody appended violates EVT-020 ("only appended events"): on
the empty history it returns `[0]`. -/
@[evidence forbids EVT_020]
theorem EVT_020_forbids_seeded : ¬ EVT_020 evt020_seeded := by
  intro hS
  have := (evt020_id_iff _ rfl).1 hS [] []
  revert this
  decide

/-! ### The Python binding's store -/

/-- A store with the identity normalisation that meets EVT-020 meets it read through any
normalisation. -/
theorem evt020_through_of {E : Type} {S : StoreObs E} (hS : EVT_020 S) (hn : S.norm = id)
    (n : E → E) : EVT_020 { S with norm := n } :=
  fun h h' => ((evt020_id_iff S hn).1 hS h h').map n

/-- A token event as the Python binding's store sees it: its place and an optional payload
(an event of another kind carries no payload). -/
abbrev Evt020PyEv := Nat × Option Nat

/-- The binding store's normalisation (`RunStore::filter_payload`,
`rust/libpetri-py/src/events.rs`): remove the payload of a token event on a place
outside the capture filter `keep`, leave every other event as it is. -/
def evt020_pyStrip (keep : Nat → Bool) (e : Evt020PyEv) : Evt020PyEv :=
  if keep e.1 then e else (e.1, none)

/-- The inverted normalisation: remove the payloads inside the filter, keep the others. -/
def evt020_pyStripInv (keep : Nat → Bool) (e : Evt020PyEv) : Evt020PyEv :=
  if keep e.1 then (e.1, none) else e

/-- The Python binding's in-memory store with capture filter `keep`: it keeps every appended
event after its strip and returns a new list. -/
def evt020_pyStore (keep : Nat → Bool) : StoreObs Evt020PyEv where
  enabled := true
  hasClear := false
  read h _ := (retained h).map (evt020_pyStrip keep)
  norm := evt020_pyStrip keep

/-- A binding store given the capture filter `keep` (its normalisation is that filter's strip)
that applies the inverted strip to what it shows. -/
def evt020_pyStoreInv (keep : Nat → Bool) : StoreObs Evt020PyEv where
  enabled := true
  hasClear := false
  read h _ := (retained h).map (evt020_pyStripInv keep)
  norm := evt020_pyStrip keep

/-- The strip is idempotent. -/
theorem evt020_pyStrip_idem (keep : Nat → Bool) (e : Evt020PyEv) :
    evt020_pyStrip keep (evt020_pyStrip keep e) = evt020_pyStrip keep e := by
  unfold evt020_pyStrip
  by_cases hk : keep e.1 <;> simp [hk]

/-- ✓ The Python binding's store meets EVT-020 read through its own strip, at every capture
filter (the second quoted sentence). -/
@[evidence allows EVT_020]
theorem evt020_allows_python :
    ∀ keep, EVT_020 (evt020_pyStore keep) := by
  intro keep h h'
  show List.Sublist (((evt020_pyStore keep).read h h').map (evt020_pyStrip keep))
    ((appended (h ++ h')).map (evt020_pyStrip keep))
  have hm : ((evt020_pyStore keep).read h h').map (evt020_pyStrip keep) =
      (retained h).map (evt020_pyStrip keep) := by
    simp only [evt020_pyStore, List.map_map]
    congr 1
    funext e
    exact evt020_pyStrip_idem keep e
  rw [hm]
  exact (evt020_sublist_later (evt020_retained_sublist h) h').map _

/-- The capture filter of the examples: place 0 only. -/
def evt020_keep0 (p : Nat) : Bool := p == 0

/-- ✗ A binding store whose events disagree with the strip of the filter it was given fails
EVT-020: given the capture filter of place 0, it applies the inverted strip, so after appending a
token event on the captured place 0 with payload 5 it shows that event without the payload the
filter keeps. -/
@[evidence forbids EVT_020]
theorem evt020_python_disagrees :
    ¬ EVT_020 (evt020_pyStoreInv evt020_keep0) := by
  intro hS
  have := hS [.append (0, some 5), .append (1, some 6)] []
  revert this
  decide

/-- The inverted strip of a filter is the strip of the complementary filter. -/
theorem evt020_pyStripInv_compl (keep : Nat → Bool) :
    evt020_pyStripInv keep = evt020_pyStrip (fun p => !keep p) := by
  funext e
  unfold evt020_pyStripInv evt020_pyStrip
  by_cases hk : keep e.1 <;> simp [hk]

/-- Read through the inverted strip it applies, the store of `evt020_python_disagrees` is the
binding's store given the complementary filter, and meets EVT-020: what the line checks is the
agreement of what a store shows with the filter it was given. -/
theorem evt020_python_invCompl (keep : Nat → Bool) :
    EVT_020 { evt020_pyStoreInv keep with norm := evt020_pyStripInv keep } := by
  intro h h'
  have := evt020_allows_python (fun p => !keep p) h h'
  simpa [evt020_pyStoreInv, evt020_pyStore, evt020_pyStripInv_compl] using this

/-- Read through the identity instead of its own strip, the binding's store fails EVT-020: it shows the event on the
uncaptured place 1 without the payload the executor appended it with. This is why the line
reads that store through its strip. -/
theorem evt020_python_literal : ¬ EVT_020 { evt020_pyStore evt020_keep0 with norm := id } := by
  intro hS
  have := hS [.append (0, some 5), .append (1, some 6)] []
  revert this
  decide

/-! ### Non-vacuity: the test derivation on the reference -/

/-- The test derivation on the reference in-memory store: after appends whose order mixes two
callers (one appends 1 and 3, the other 2), `events()` returns all three in the order they took
effect, which is a subsequence of the appends; the live view of the same store shows
`[1, 2, 3, 4]` after one more append, a subsequence of every append so far; the newest-first
store returns `[3, 2, 1]` on the same history, which is not, and the noop store returns nothing,
which is. -/
@[evidence nonvacuous EVT_020]
theorem EVT_020_nonvacuous :
    (refMemStore (E := Nat)).read [.append 1, .append 2, .append 3] [] = [1, 2, 3] ∧
    List.Sublist ((refMemStore (E := Nat)).read [.append 1, .append 2, .append 3] [])
      (appended [StoreOp.append 1, .append 2, .append 3]) ∧
    (liveMemStore (E := Nat)).read [.append 1, .append 2, .append 3] [.append 4] =
      [1, 2, 3, 4] ∧
    ¬ List.Sublist ((newestFirstStore (E := Nat)).read [.append 1, .append 2, .append 3] [])
      (appended [StoreOp.append 1, .append 2, .append 3]) ∧
    List.Sublist ((refNoopStore (E := Nat)).read [.append 1, .append 2, .append 3] [])
      (appended [StoreOp.append 1, .append 2, .append 3]) := by
  decide

end Libpetri.Spec
