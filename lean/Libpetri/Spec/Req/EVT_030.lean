import Libpetri.Spec.Registry
import Libpetri.Spec.GlossaryStore
import Libpetri.Spec.Req.EVT_021

set_option linter.missingDocs true

/-!
# EVT-030: Event Filtering (`spec/08-events-observability.md`)

The query helpers read the list a call of `events()` returns and answer with part of it: a
filtered and paged query, the failure events, a histogram by event type and a count. The
requirement is a predicate over the helpers of one implementation, `H : QueryHelpers E`, together
with the shape of an event, `sh : E → EventShape`: its type, the transition name it carries (if
any) and the place name it carries (if any). The helpers read nothing else of an event, so the
block quantifies over the event type `E` and its shape; the executor event model of wave W7
takes its events as `E` and its shape function as `sh`.

The witness is `refQueryHelpers sh`: filter, then page; the failure kinds; the histogram over the
event types that occur; the number of events of the given types. The wrong helpers are one per
line: a query that answers nothing once the store holds an event with no transition name (Java's
`transitionEvents`, clash evt-c#13), a transition filter that skips LogMessage events, a query
that combines its filters by "or", a query that pages before it filters, `failures()` without
ActionTimedOut, a histogram that names a type twice, one that lists every type with a zero count,
and a count that reads an empty type set as no filter. The consequences read the acceptance
criteria off the lines: a query with one type or one transition name is Java's and TypeScript's
`eventsOfType` and `transitionEvents` (AC1, AC2), a place query returns token events of the
named places once only token events carry a place name (AC3), the values of the histogram add up
to the number of events (AC5), the count with no type is the number of events and the count by
type is the length of the type query, and on an in-memory store a query reads the appended events
in append order ([EVT-021]).

The runtimes mark the missing transition name of an engine diagnostic by the empty name (Java
also by `null`). Line 1 therefore constrains every query whose transition filter does not name
the empty name, and `EVT_030_allows_emptySentinel` shows that helpers comparing names as they are
meet the requirement under the shape that reads the empty name as no name.

Block-local vocabulary (`EventType`, `EventShape`, `EventQuery`, `QueryHelpers`) lives in this
file. The executor event glossary of wave W7 (`GlossaryEvents`) owns the event kinds; when it
lands, `EventType` and `EventShape` move there, and this block reads them from it.
-/

namespace Libpetri.Spec

/-! ## Block-local vocabulary: event types, event shapes, queries -/

/-- The thirteen event types of the event model ([EVT-002] to [EVT-014]), as a query names them
(`eventsOfType` in Java and TypeScript, the `types` filter and `counters()` in Python). -/
inductive EventType where
  /-- ExecutionStarted ([EVT-002]). -/
  | executionStarted
  /-- ExecutionCompleted ([EVT-003]). -/
  | executionCompleted
  /-- TransitionEnabled ([EVT-004]). -/
  | transitionEnabled
  /-- TransitionClockRestarted ([EVT-005]). -/
  | transitionClockRestarted
  /-- TransitionStarted ([EVT-006]). -/
  | transitionStarted
  /-- TransitionCompleted ([EVT-007]). -/
  | transitionCompleted
  /-- TransitionFailed ([EVT-008]). -/
  | transitionFailed
  /-- TransitionTimedOut ([EVT-009]). -/
  | transitionTimedOut
  /-- ActionTimedOut ([EVT-010]). -/
  | actionTimedOut
  /-- TokenAdded ([EVT-011]). -/
  | tokenAdded
  /-- TokenRemoved ([EVT-012]). -/
  | tokenRemoved
  /-- LogMessage ([EVT-013]). -/
  | logMessage
  /-- MarkingSnapshot ([EVT-014]). -/
  | markingSnapshot
  deriving DecidableEq, Repr

/-- Every event type, once each. -/
def allEventTypes : List EventType :=
  [.executionStarted, .executionCompleted, .transitionEnabled, .transitionClockRestarted,
   .transitionStarted, .transitionCompleted, .transitionFailed, .transitionTimedOut,
   .actionTimedOut, .tokenAdded, .tokenRemoved, .logMessage, .markingSnapshot]

/-- The failure types: TransitionFailed, TransitionTimedOut and ActionTimedOut ([EVT-030] AC4;
the same set as the failure level of [EVT-023]). -/
def EventType.isFailure : EventType → Bool
  | .transitionFailed | .transitionTimedOut | .actionTimedOut => true
  | _ => false

/-- What a query reads of an event: its type, the transition name it carries and the place name
it carries. In every runtime the eight transition kinds carry a transition name field (LogMessage
included), the two token kinds carry a place name, and the other kinds carry neither
(`rust/libpetri-event/src/net_event.rs` `transition_name` and `place_name`). An engine diagnostic
fills the name field with the empty name in all four runtimes (the initial-marking seam), and
with `null` in Java on an interrupted run; whether the shape reads the empty name as no name is
the event model's choice (wave W7), and line 1 holds the same either way
(`EVT_030_allows_emptySentinel`). -/
structure EventShape where
  /-- The event type. -/
  type : EventType
  /-- The transition name the event carries, if any. -/
  transition : Option String := none
  /-- The place name the event carries, if any. -/
  place : Option String := none
  deriving DecidableEq, Repr

/-- A query ([EVT-030]): optional filters by event type, by transition name and by place name,
each a list of the names it accepts (Java and TypeScript name one, Python a set), then an offset
and an optional limit. A filter left out accepts every event. -/
structure EventQuery where
  /-- The event types the query accepts, or every type. -/
  types : Option (List EventType) := none
  /-- The transition names the query accepts, or every event. -/
  transitions : Option (List String) := none
  /-- The place names the query accepts, or every event. -/
  places : Option (List String) := none
  /-- How many matching events the query skips. -/
  offset : Nat := 0
  /-- How many of the rest the query returns at most, or all of them. -/
  limit : Option Nat := none

/-- An event matches a query when it matches every filter the query gives. A filter by
transition name accepts only an event that carries one of its names, so an event with no
transition name matches no such filter (ruling D29 (a), EVT-C10 (a)); likewise for places. -/
def EventQuery.matches (q : EventQuery) (s : EventShape) : Bool :=
  q.types.all (fun ts => ts.contains s.type) &&
  q.transitions.all (fun ns => s.transition.any fun n => ns.contains n) &&
  q.places.all (fun ps => s.place.any fun p => ps.contains p)

/-- The query's transition filter, if it has one, does not name the empty name (the runtimes'
mark for a missing transition name). -/
def EventQuery.namesNoEmpty (q : EventQuery) : Bool :=
  q.transitions.all fun ns => !ns.contains ""

/-- The query with the same filters and no paging. -/
def EventQuery.unpaged (q : EventQuery) : EventQuery := { q with offset := 0, limit := none }

/-- The page a query takes of a list: skip `offset` elements, then keep the first `limit` of the
rest (all of them without a limit). -/
def EventQuery.page {α : Type} (q : EventQuery) (l : List α) : List α :=
  match q.limit with
  | none => l.drop q.offset
  | some n => (l.drop q.offset).take n

/-- The number of events of type `k` in `es`. -/
def countOfType {E : Type} (sh : E → EventShape) (k : EventType) (es : List E) : Nat :=
  es.countP fun e => (sh e).type == k

/-- The query helpers of one implementation, each applied to the list `es` a call of `events()`
returns: `select q es`, the answer to the query `q`; `failures es`; `counters es`, the histogram
as a list of (event type, count) pairs (Python returns a dict); `count ts es`, the number of
events of the types `ts`, or of all events. -/
structure QueryHelpers (E : Type) where
  /-- The answer to a query. -/
  select : EventQuery → List E → List E
  /-- `failures()`. -/
  failures : List E → List E
  /-- `counters()`. -/
  counters : List E → List (EventType × Nat)
  /-- The count: `size()` (no type) in Java, TypeScript and Rust; `len()` and `count(types=...)`
  in Python. -/
  count : Option (List EventType) → List E → Nat

/-! ## The reference helpers -/

/-- The reference histogram: each event type that occurs, with its number of events. -/
def refCounters {E : Type} (sh : E → EventShape) (es : List E) : List (EventType × Nat) :=
  (allEventTypes.map fun k => (k, countOfType sh k es)).filter fun x => x.2 != 0

/-- The reference query helpers: a query filters, then pages; `failures()` keeps the failure
types; `counters()` is `refCounters`; the count counts the events of the given types. The Python
binding's `InMemoryEventStore.events(types=, transitions=, places=, limit=, offset=)` filters and
then skips and takes, and its `count(types=)` counts the events whose type is in the set
(`rust/libpetri-py/src/events.rs`); Java, TypeScript and Rust filter `events()` in order. -/
def refQueryHelpers {E : Type} (sh : E → EventShape) : QueryHelpers E where
  select q es := q.page (es.filter fun e => q.matches (sh e))
  failures es := es.filter fun e => (sh e).type.isFailure
  counters es := refCounters sh es
  count ts es := (es.filter fun e => ts.all fun l => l.contains (sh e).type).length

#spec_witness refQueryHelpers

/-! ## EVT-030: Event Filtering -/

requirement EVT_030
  id "EVT-030"
  title "Event Filtering"
  kind F
  scope "the event query helpers where an implementation provides them (type, transition and failure helpers and the event count in Java and TypeScript; transition and failure helpers and the event count in Rust; every helper in the Python binding)"
  source verbatim "spec/08-events-observability.md"
  quote "*Where* an implementation provides a query over the events of an event store, the query without offset and limit *shall* return exactly the events that `events()` returns and that match every filter the query gives, in the order `events()` returns them, for every query whose transition filter does not name the empty name."
        "A filter by event type *shall* match the events of the given types, a filter by transition name *shall* match the events that carry one of the given transition names, and a filter by place name *shall* match the events that carry one of the given place names."
        "An event that carries no transition name *shall* match no filter by transition name, and its presence in the store *shall not* change which other events such a filter returns."
        "*Where* an implementation provides offset and limit on a query, the query *shall* skip the first `offset` matching events and return the first `limit` of the matching events that follow (all of them when no limit is given), so that the page is taken over the filtered result and not over the store."
        "*Where* an implementation provides `failures()`, it *shall* return exactly the TransitionFailed, TransitionTimedOut and ActionTimedOut events that `events()` returns, in the order `events()` returns them."
        "*Where* an implementation provides `counters()`, it *shall* name each event type that occurs among the events `events()` returns exactly once, with the number of those events of that type, and *shall* name no other event type."
        "*Where* an implementation provides a count of events, the count *shall* be the number of events that `events()` returns whose type is one of the given types, or the number of all of them when no type is given."
  reading "For every event type E, every shape function sh and the helpers H, over every list es of events (the list events() returns):"
          "a query q without paging whose transition filter does not name the empty name returns the events of es that match every filter of q (type among its types, a transition name among its names, a place name among its names), in the order of es;"
          "a query q returns the page of its unpaged answer: it skips the first offset events and keeps the first limit of the rest;"
          "failures() returns the events of es whose type is TransitionFailed, TransitionTimedOut or ActionTimedOut, in the order of es;"
          "counters() names no event type twice;"
          "counters() holds the pair (k, n) exactly when n is the number of events of es of type k and n is not zero;"
          "the count for the types ts is the number of events of es whose type is in ts, and the number of events of es when no type is given."
  assumes "The model is the helpers of one implementation, H : QueryHelpers E, each applied to the list es that a call of events() returns, and the shape of an event, sh : E → EventShape: its type (one of the thirteen of EVT-002 to EVT-014), the transition name it carries and the place name it carries. The helpers read nothing else of an event, so the event type E and its shape are parameters; which kinds carry a name is the event model's (wave W7): the eight transition kinds, LogMessage included, carry a transition name, and only TokenAdded and TokenRemoved carry a place name (net_event.rs transition_name and place_name; net-event.ts eventTransitionName). Events with equal shapes are told apart by position in es, so the lines fix which events a helper returns, not only their shapes."
          "Scope (ruling D20, clash evt-c#16, EVT-C11): the helpers differ per language, and each line constrains a helper only where an implementation provides it. Lines 1 and 2 read only select, line 3 only failures, lines 4 and 5 only counters and line 6 only count, so the lines of a helper an implementation lacks constrain nothing it has. Java and TypeScript provide eventsOfType (a query with one type), transitionEvents (one transition name), failures() and size() (the count with no type); Rust's in-memory store provides transition_events, failures(), size() and a predicate filter, but no type filter; the Python binding provides the full query (sets of types, transitions and places, offset and limit), len(), count(types=...), counters() and failures() (rust/libpetri-py/src/events.rs). The spec edit of this wave adds an implementation-status line that says so."
          "The first three quoted sentences are line 1. Filters given together combine by 'and' (the Python binding's FilterSpec.matches), so a query with both a transition filter and a place filter returns nothing in the current event model; the spec says nothing else, and the line follows the one implementation that offers both. The order is the order of es, which on an in-memory store is append order (evt030_mem_select, through EVT-021)."
          "The empty name: every runtime fills the transition name of an engine diagnostic at the initial-marking seam with the empty name (Java BitmapNetExecutor warnUnknownPlace(..., \"\"), bitmap-net-executor.ts warnUnknownPlace(place, ''), Rust emit_unknown_place_warnings(&dead, \"\")), and EVT-013 reads such an event as one that carries no transition name. A filter for the empty name would then ask for the engine diagnostics, which the spec leaves open; line 1 constrains every query whose transition filter does not name the empty name, as the first quoted sentence and the implementation-status line say. Under that guard the reading of the empty name does not matter: helpers that compare names as they are meet EVT-030 under the shape that reads the empty name as no name (EVT_030_allows_emptySentinel), so the third quoted sentence applies to Rust and Python with the shape EVT-013 describes. A transition named by the empty name is not ruled out by any requirement; its events are told apart from engine diagnostics by no runtime, and a filter for it is outside the line."
          "The third quoted sentence and ruling D29 (a) (EVT-C10 (a)): every helper is a total function, and an event with no transition name matches no transition filter. Java's transitionEvents calls equals on the transition name of every LogMessage and throws on an engine diagnostic whose name is null, which both Java executors emit on an interrupted run (clash evt-c#13); EVT_030_mutant_throwsOnNameless models that call as one that returns nothing, and line 1 rejects it. It is a recorded gap in Java (RD-21 in spec/runtime-defects.md), to be fixed outside this migration; the implementation-status line names it. TypeScript compares an optional name and Rust an Option, and both return the matching events."
          "The fourth quoted sentence is line 2: the page is taken of the filtered answer, which the Python binding does (filter, then skip offset, then take limit). A helper that pages the store and then filters breaks it (EVT_030_mutant_pageFirst)."
          "The fifth quoted sentence is line 3 (AC4). The failure set is the one EVT-023 logs at the failure level (ruling D29 (a), the level table failures first); all four runtimes test the same three kinds (EventStore.java failures, net-event.ts isFailureEvent, net_event.rs is_failure)."
          "The sixth quoted sentence is lines 4 and 5 (AC5). The histogram is a list of pairs whose order is not fixed: Python returns a dict in ascending order of the type name, and the order of a dict is not part of the requirement. A type with no events has no entry, as in Python, whose counters() builds an entry only for a type it meets. evt030_counters_sum derives AC5's 'values sum to the total event count' from lines 4 and 5 for every helper that meets them."
          "The seventh quoted sentence is line 6, the body's 'Count events': the count with no type is size() in Java, TypeScript and Rust and len() or count() in Python; count(types=...) in Python is the count by type, which Python computes on its own path rather than as the length of a query. An empty type set counts no event (EVT_030_mutant_emptyTypesCountsAll). evt030_count_all and evt030_count_select tie the count to the number of events and to the length of the type query."
          "AC1 (eventsOfType(TransitionCompleted) returns only completed events) is line 1 at a query with one type (evt030_eventsOfType); AC2 (transitionEvents returns the events of that transition) is line 1 at a query with one transition name, read as the events that carry that name (ruling D29 (a); the spec edit of this wave rewords AC2 to say so): TokenAdded and TokenRemoved events of the transition's firing carry no transition name and are not returned in any runtime (evt030_transitionEvents); AC3 (place filter, offset and limit) is lines 1 and 2, and its 'only token events' follows once the event model gives only TokenAdded and TokenRemoved a place name (evt030_placeEvents takes that as a premise; wave W7 discharges it when GlossaryEvents lands)."
          "The test derivation (a run with mixed events; each filter, the paging, the histogram and the count give the right subsets and totals) is EVT_030_nonvacuous on a decided list of mixed events."
  signoff "pending"
  statement : ∀ {E : Type}, (E → EventShape) → QueryHelpers E → Prop :=
    fun {E} sh H =>
      (∀ (q : EventQuery) (es : List E), q.namesNoEmpty = true →
        H.select q.unpaged es = es.filter fun e => q.matches (sh e)) ∧
      (∀ (q : EventQuery) (es : List E), H.select q es = q.page (H.select q.unpaged es)) ∧
      (∀ es : List E, H.failures es = es.filter fun e => (sh e).type.isFailure) ∧
      (∀ es : List E, ((H.counters es).map Prod.fst).Nodup) ∧
      (∀ (es : List E) (k : EventType) (n : Nat),
        (k, n) ∈ H.counters es ↔ n = countOfType sh k es ∧ n ≠ 0) ∧
      (∀ (ts : Option (List EventType)) (es : List E),
        H.count ts es = (es.filter fun e => ts.all fun l => l.contains (sh e).type).length)

/- The pinned readable form of EVT-030: a change to the formula shows up as a diff here. -/
/--
info: def Libpetri.Spec.EVT_030 : {E : Type} → (E → EventShape) → QueryHelpers E → Prop :=
fun {E} sh H =>
  (∀ (q : EventQuery) (es : List E),
      q.namesNoEmpty = true → H.select q.unpaged es = List.filter (fun e => q.matches (sh e)) es) ∧
    (∀ (q : EventQuery) (es : List E), H.select q es = q.page (H.select q.unpaged es)) ∧
      (∀ (es : List E), H.failures es = List.filter (fun e => (sh e).type.isFailure) es) ∧
        (∀ (es : List E), (List.map Prod.fst (H.counters es)).Nodup) ∧
          (∀ (es : List E) (k : EventType) (n : Nat), (k, n) ∈ H.counters es ↔ n = countOfType sh k es ∧ n ≠ 0) ∧
            ∀ (ts : Option (List EventType)) (es : List E),
              H.count ts es = (List.filter (fun e => Option.all (fun l => l.contains (sh e).type) ts) es).length
-/
#guard_msgs in #print EVT_030

/-! ### The reference -/

/-- Every event type is in `allEventTypes`. -/
theorem mem_allEventTypes (k : EventType) : k ∈ allEventTypes := by
  cases k <;> decide

/-- `allEventTypes` names every event type once. -/
theorem allEventTypes_nodup : allEventTypes.Nodup := by decide

/-- The reference histogram names no event type twice. -/
theorem refCounters_keys_nodup {E : Type} (sh : E → EventShape) (es : List E) :
    ((refCounters sh es).map Prod.fst).Nodup := by
  have hk : (allEventTypes.map fun k => (k, countOfType sh k es)).map Prod.fst = allEventTypes := by
    simp [List.map_map, Function.comp_def]
  have hsub : ((refCounters sh es).map Prod.fst).Sublist
      ((allEventTypes.map fun k => (k, countOfType sh k es)).map Prod.fst) :=
    List.Sublist.map _ List.filter_sublist
  rw [hk] at hsub
  exact allEventTypes_nodup.sublist hsub

/-- The reference histogram holds `(k, n)` exactly when `n` is the nonzero count of type `k`. -/
theorem mem_refCounters {E : Type} (sh : E → EventShape) (es : List E) (k : EventType) (n : Nat) :
    (k, n) ∈ refCounters sh es ↔ n = countOfType sh k es ∧ n ≠ 0 := by
  simp only [refCounters, List.mem_filter, List.mem_map, Prod.mk.injEq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨⟨k', _, rfl, rfl⟩, hn⟩
    exact ⟨rfl, hn⟩
  · rintro ⟨rfl, hn⟩
    exact ⟨⟨k, mem_allEventTypes k, rfl, rfl⟩, hn⟩

/-- The reference helpers satisfy EVT-030 for every event type and every shape function. -/
@[evidence holds EVT_030]
theorem EVT_030_reference {E : Type} (sh : E → EventShape) : EVT_030 sh (refQueryHelpers sh) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, refCounters_keys_nodup sh,
    mem_refCounters sh, fun _ _ => rfl⟩

/-! ### Consequences -/

/-- AC1 on helpers that meet EVT-030: a query with one type (Java and TypeScript
`eventsOfType`) returns exactly the events of that type, in order. -/
theorem evt030_eventsOfType {E : Type} {sh : E → EventShape} {H : QueryHelpers E}
    (hH : EVT_030 sh H) (k : EventType) (es : List E) :
    H.select { types := some [k] } es = es.filter fun e => (sh e).type == k := by
  have h := hH.1 { types := some [k] } es rfl
  simp only [EventQuery.unpaged] at h
  rw [h]
  congr 1
  funext e
  simp only [EventQuery.matches, Option.all, List.contains, List.elem, Bool.and_true]
  cases (sh e).type == k <;> rfl

/-- AC2 on helpers that meet EVT-030: a query with one transition name that is not the empty
name (`transitionEvents`) returns exactly the events that carry that name, in order; an event
with no transition name is not returned and does not stop the others from being returned. -/
theorem evt030_transitionEvents {E : Type} {sh : E → EventShape} {H : QueryHelpers E}
    (hH : EVT_030 sh H) (n : String) (hn : n ≠ "") (es : List E) :
    H.select { transitions := some [n] } es = es.filter fun e => (sh e).transition == some n := by
  have hq : ({ transitions := some [n] } : EventQuery).namesNoEmpty = true := by
    simp [EventQuery.namesNoEmpty, Option.all, hn]
  have h := hH.1 { transitions := some [n] } es hq
  simp only [EventQuery.unpaged] at h
  rw [h]
  congr 1
  funext e
  cases ht : (sh e).transition with
  | none => simp [EventQuery.matches, Option.all, Option.any, ht]
  | some m =>
    simp only [EventQuery.matches, Option.all, Option.any, ht, List.contains, List.elem,
      Bool.and_true, Bool.true_and]
    by_cases hmn : m = n
    · subst hmn; simp
    · have h₁ : (m == n) = false := beq_eq_false_iff_ne.mpr hmn
      have h₂ : (some m == some n) = false := beq_eq_false_iff_ne.mpr (by simpa using hmn)
      rw [h₁, h₂]

/-- An element of a page is an element of the list it is taken of. -/
theorem EventQuery.mem_of_mem_page {α : Type} (q : EventQuery) {l : List α} {a : α}
    (h : a ∈ q.page l) : a ∈ l := by
  unfold EventQuery.page at h
  split at h
  · exact List.mem_of_mem_drop h
  · exact List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- AC3 on helpers that meet EVT-030, for an event model where only TokenAdded and TokenRemoved
carry a place name: a query with a place filter, paged or not, returns only token events, each
carrying one of the named places. -/
theorem evt030_placeEvents {E : Type} {sh : E → EventShape} {H : QueryHelpers E}
    (hH : EVT_030 sh H)
    (hsh : ∀ e, (sh e).place.isSome → (sh e).type = .tokenAdded ∨ (sh e).type = .tokenRemoved)
    (q : EventQuery) (ps : List String) (hp : q.places = some ps) (hq : q.namesNoEmpty = true)
    (es : List E) (e : E) (he : e ∈ H.select q es) :
    ((sh e).type = .tokenAdded ∨ (sh e).type = .tokenRemoved) ∧
      ∃ p, (sh e).place = some p ∧ p ∈ ps := by
  rw [hH.2.1, hH.1 q es hq] at he
  have hm := (List.mem_filter.mp (q.mem_of_mem_page he)).2
  simp only [EventQuery.matches, hp, Option.all, Bool.and_eq_true] at hm
  obtain ⟨_, hpl⟩ := hm
  cases hpe : (sh e).place with
  | none => simp [hpe] at hpl
  | some p =>
    simp only [hpe, Option.any, List.contains_iff_mem] at hpl
    exact ⟨hsh e (by simp [hpe]), p, rfl, hpl⟩

/-- The histogram of helpers that meet EVT-030 is the reference histogram up to order. -/
theorem evt030_counters_perm {E : Type} {sh : E → EventShape} {H : QueryHelpers E}
    (hH : EVT_030 sh H) (es : List E) : (H.counters es).Perm (refCounters sh es) := by
  have nd₁ : (H.counters es).Nodup :=
    List.Pairwise.of_map Prod.fst (fun a b h e => h (congrArg Prod.fst e)) (hH.2.2.2.1 es)
  have nd₂ : (refCounters sh es).Nodup :=
    List.Pairwise.of_map Prod.fst (fun a b h e => h (congrArg Prod.fst e))
      (refCounters_keys_nodup sh es)
  rw [List.perm_iff_count]
  intro x
  rw [nd₁.count, nd₂.count]
  obtain ⟨k, n⟩ := x
  have key := hH.2.2.2.2.1 es k n
  have key' := mem_refCounters sh es k n
  by_cases hm : (k, n) ∈ H.counters es
  · have hr : (k, n) ∈ refCounters sh es := key'.2 (key.1 hm)
    simp [hm, hr]
  · have hr : (k, n) ∉ refCounters sh es := fun h => hm (key.2 (key'.1 h))
    simp [hm, hr]

/-- Dropping the zero entries of a list of pairs leaves the sum of the second components. -/
theorem sum_snd_filter_ne_zero {α : Type} (l : List (α × Nat)) :
    ((l.filter fun x => x.2 != 0).map Prod.snd).sum = (l.map Prod.snd).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : x.2 = 0
    · simp [h, ih]
    · simp [h, ih]

/-- One event adds one to the count of exactly one event type. -/
theorem sum_indicator_allEventTypes (t : EventType) :
    (allEventTypes.map fun k => if (t == k) = true then 1 else 0).sum = 1 := by
  cases t <;> decide

/-- The sum of a pointwise sum over a list is the sum of the two sums. -/
theorem sum_map_add_nat {α : Type} (l : List α) (f g : α → Nat) :
    (l.map fun k => f k + g k).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]; omega

/-- The counts of all event types add up to the number of events. -/
theorem sum_countOfType {E : Type} (sh : E → EventShape) (es : List E) :
    (allEventTypes.map fun k => countOfType sh k es).sum = es.length := by
  induction es with
  | nil => simp [countOfType]; decide
  | cons e es ih =>
    have : (allEventTypes.map fun k => countOfType sh k (e :: es)) =
        allEventTypes.map fun k =>
          countOfType sh k es + if ((sh e).type == k) = true then 1 else 0 := by
      simp only [countOfType, List.countP_cons]
    rw [this, sum_map_add_nat, ih, sum_indicator_allEventTypes]
    rfl

/-- AC5 on helpers that meet EVT-030: the values of the histogram add up to the number of
events `events()` returns. -/
theorem evt030_counters_sum {E : Type} {sh : E → EventShape} {H : QueryHelpers E}
    (hH : EVT_030 sh H) (es : List E) : ((H.counters es).map Prod.snd).sum = es.length := by
  rw [List.Perm.sum_nat ((evt030_counters_perm hH es).map Prod.snd), refCounters,
    sum_snd_filter_ne_zero, List.map_map]
  exact sum_countOfType sh es

/-- "Count events" on helpers that meet EVT-030: the count with no type is the number of events
`events()` returns (`size()`, `len()`). -/
theorem evt030_count_all {E : Type} {sh : E → EventShape} {H : QueryHelpers E}
    (hH : EVT_030 sh H) (es : List E) : H.count none es = es.length := by
  rw [hH.2.2.2.2.2]
  simp [Option.all]

/-- On helpers that meet EVT-030 the count by type is the length of the answer to the query with
that type filter and nothing else (Python's `count(types=)` and `len(events(types=))`). -/
theorem evt030_count_select {E : Type} {sh : E → EventShape} {H : QueryHelpers E}
    (hH : EVT_030 sh H) (ts : Option (List EventType)) (es : List E) :
    H.count ts es = (H.select { types := ts } es).length := by
  have h := hH.1 { types := ts } es rfl
  simp only [EventQuery.unpaged] at h
  rw [hH.2.2.2.2.2, h]
  congr 2
  funext e
  simp [EventQuery.matches, Option.all]

/-- On a store that meets EVT-021, a query over what `events()` returns after a history of
appends reads the appended events in append order: the matching ones, then the page. -/
theorem evt030_mem_select {E : Type} {sh : E → EventShape} {H : QueryHelpers E}
    {S : StoreObs E} (hH : EVT_030 sh H) (hS : EVT_021 S) (q : EventQuery)
    (hq : q.namesNoEmpty = true) (es : List E) :
    H.select q (S.read (es.map StoreOp.append) []) =
      q.page (es.filter fun e => q.matches (sh e)) := by
  rw [hH.2.1, hH.1 q _ hq, evt021_appends hS]

/-! ### The empty name -/

/-- The shape that reads the empty transition name as no transition name (the reading of
[EVT-013] for an engine diagnostic). -/
def evt030_emptyAsNone (s : EventShape) : EventShape :=
  { s with transition := s.transition.filter (· != "") }

/-- A query whose transition filter does not name the empty name matches an event read with the
empty name as no name exactly when it matches the event as it is. -/
theorem matches_emptyAsNone (q : EventQuery) (hq : q.namesNoEmpty = true) (s : EventShape) :
    q.matches (evt030_emptyAsNone s) = q.matches s := by
  cases hT : q.transitions with
  | none => simp [EventQuery.matches, evt030_emptyAsNone, hT, Option.all]
  | some ns =>
    have hns : ns.contains "" = false := by
      simpa [EventQuery.namesNoEmpty, hT, Option.all] using hq
    cases hs : s.transition with
    | none => simp [EventQuery.matches, evt030_emptyAsNone, hT, hs, Option.all]
    | some n =>
      by_cases hn : n = ""
      · subst hn
        have hns' : "" ∉ ns := by simpa using hns
        simp [EventQuery.matches, evt030_emptyAsNone, hT, hs, Option.all, Option.filter, hns']
      · have hb : (n != "") = true := by simpa using hn
        simp [EventQuery.matches, evt030_emptyAsNone, hT, hs, Option.all, Option.filter, hb]

/-- ✓ Helpers that compare transition names as they are (Java, TypeScript and Rust's
`transitionEvents`, Python's `FilterSpec`) meet EVT-030 under the shape that reads the empty name
as no name: line 1 sets filters for the empty name aside, so the runtimes' mark for a missing
transition name is never read as a name the requirement constrains. -/
@[evidence allows EVT_030]
theorem EVT_030_allows_emptySentinel : EVT_030 evt030_emptyAsNone (refQueryHelpers id) := by
  refine ⟨fun q es hq => ?_, fun _ _ => rfl, fun _ => rfl, refCounters_keys_nodup id,
    fun es k n => mem_refCounters id es k n, fun _ _ => rfl⟩
  show q.unpaged.page (es.filter fun e => q.unpaged.matches e) = _
  show es.filter (fun e => q.matches e) = es.filter fun e => q.matches (evt030_emptyAsNone e)
  congr 1
  funext e
  exact (matches_emptyAsNone q hq e).symm

/-! ### Wrong helpers, one per line -/

/-- The mutant reading without line 1 (the filter): lines 2 to 6 only. -/
def evt030_noFilterLine {E : Type} (sh : E → EventShape) (H : QueryHelpers E) : Prop :=
  (∀ (q : EventQuery) (es : List E), H.select q es = q.page (H.select q.unpaged es)) ∧
  (∀ es : List E, H.failures es = es.filter fun e => (sh e).type.isFailure) ∧
  (∀ es : List E, ((H.counters es).map Prod.fst).Nodup) ∧
  (∀ (es : List E) (k : EventType) (n : Nat), (k, n) ∈ H.counters es ↔ n = countOfType sh k es ∧ n ≠ 0) ∧
  (∀ (ts : Option (List EventType)) (es : List E),
    H.count ts es = (es.filter fun e => ts.all fun l => l.contains (sh e).type).length)

/-- Helpers that answer a query by `answer` (the page of it) and are the reference otherwise. -/
def evt030_withAnswer (answer : EventQuery → List EventShape → List EventShape) :
    QueryHelpers EventShape :=
  { refQueryHelpers id with select := fun q es => q.page (answer q es) }

/-- Lines 2 to 6 hold of reference helpers whose answer reads only the filters of the query. -/
theorem evt030_withAnswer_noFilterLine
    (answer : EventQuery → List EventShape → List EventShape)
    (hA : ∀ q es, answer q.unpaged es = answer q es) :
    evt030_noFilterLine id (evt030_withAnswer answer) := by
  refine ⟨fun q es => ?_, fun _ => rfl, refCounters_keys_nodup id, mem_refCounters id,
    fun _ _ => rfl⟩
  show q.page (answer q es) = q.page (answer q.unpaged es)
  rw [hA]

/-- Java's `transitionEvents` on a store that holds an event with no transition name (clash
evt-c#13): the call throws, which a caller sees as no answer; here, the empty list. -/
def evt030_throwsOnNameless : QueryHelpers EventShape :=
  evt030_withAnswer fun q es =>
    if q.transitions.isSome && es.any (fun s => s.transition.isNone) then []
    else es.filter q.matches

/-- ✗ A transition query that gives no answer once the store holds an event with no transition
name meets lines 2 to 6 and violates EVT-030 (line 1, the third quoted sentence). -/
@[evidence mutant EVT_030]
theorem EVT_030_mutant_throwsOnNameless :
    evt030_noFilterLine id evt030_throwsOnNameless ∧ ¬ EVT_030 id evt030_throwsOnNameless := by
  refine ⟨evt030_withAnswer_noFilterLine _ fun _ _ => rfl, fun h => ?_⟩
  have := h.1 { transitions := some ["t"] }
    [{ type := .transitionStarted, transition := some "t" }, { type := .logMessage }]
    (by decide)
  revert this
  decide

/-- A transition filter that tests the transition kinds only and so skips LogMessage events. -/
def evt030_dropsLog : QueryHelpers EventShape :=
  evt030_withAnswer fun q es =>
    es.filter fun s => q.matches s && (q.transitions.isNone || s.type != .logMessage)

/-- ✗ A transition filter that skips LogMessage events meets lines 2 to 6 and violates EVT-030
(line 1): a log message an action wrote carries its transition's name. -/
@[evidence mutant EVT_030]
theorem EVT_030_mutant_dropsLog :
    evt030_noFilterLine id evt030_dropsLog ∧ ¬ EVT_030 id evt030_dropsLog := by
  refine ⟨evt030_withAnswer_noFilterLine _ fun _ _ => rfl, fun h => ?_⟩
  have := h.1 { transitions := some ["t"] } [{ type := .logMessage, transition := some "t" }]
    (by decide)
  revert this
  decide

/-- A query that returns an event when it matches any one of the filters given. -/
def evt030_anyFilter : QueryHelpers EventShape :=
  evt030_withAnswer fun q es =>
    es.filter fun s =>
      (q.types.isNone && q.transitions.isNone && q.places.isNone) ||
      q.types.any (fun ts => ts.contains s.type) ||
      q.transitions.any (fun ns => s.transition.any fun n => ns.contains n) ||
      q.places.any (fun ps => s.place.any fun p => ps.contains p)

/-- ✗ A query that combines its filters by "or" meets lines 2 to 6 and violates EVT-030 (line
1, "match every filter the query gives"): a started event of `t` is returned by a query for the
started events of `u`. -/
@[evidence mutant EVT_030]
theorem EVT_030_mutant_anyFilter :
    evt030_noFilterLine id evt030_anyFilter ∧ ¬ EVT_030 id evt030_anyFilter := by
  refine ⟨evt030_withAnswer_noFilterLine _ fun _ _ => rfl, fun h => ?_⟩
  have := h.1 { types := some [.transitionStarted], transitions := some ["u"] }
    [{ type := .transitionStarted, transition := some "t" }] (by decide)
  revert this
  decide

/-- The mutant reading without line 2 (paging): lines 1 and 3 to 6 only. -/
def evt030_noPageLine {E : Type} (sh : E → EventShape) (H : QueryHelpers E) : Prop :=
  (∀ (q : EventQuery) (es : List E), q.namesNoEmpty = true →
    H.select q.unpaged es = es.filter fun e => q.matches (sh e)) ∧
  (∀ es : List E, H.failures es = es.filter fun e => (sh e).type.isFailure) ∧
  (∀ es : List E, ((H.counters es).map Prod.fst).Nodup) ∧
  (∀ (es : List E) (k : EventType) (n : Nat), (k, n) ∈ H.counters es ↔ n = countOfType sh k es ∧ n ≠ 0) ∧
  (∀ (ts : Option (List EventType)) (es : List E),
    H.count ts es = (es.filter fun e => ts.all fun l => l.contains (sh e).type).length)

/-- A query that pages the store first and then filters the page. -/
def evt030_pageFirst : QueryHelpers EventShape :=
  { refQueryHelpers id with select := fun q es => (q.page es).filter q.matches }

/-- ✗ A query that pages before it filters meets lines 1 and 3 to 6 and violates EVT-030
(line 2): the first token event is not the first event of the store. -/
@[evidence mutant EVT_030]
theorem EVT_030_mutant_pageFirst :
    evt030_noPageLine id evt030_pageFirst ∧ ¬ EVT_030 id evt030_pageFirst := by
  refine ⟨⟨fun _ _ _ => rfl, fun _ => rfl, refCounters_keys_nodup id, mem_refCounters id,
    fun _ _ => rfl⟩, fun h => ?_⟩
  have := h.2.1 { types := some [.tokenAdded], limit := some 1 }
    [{ type := .transitionStarted }, { type := .tokenAdded }]
  revert this
  decide

/-- The mutant reading without line 3 (failures): lines 1, 2 and 4 to 6 only. -/
def evt030_noFailureLine {E : Type} (sh : E → EventShape) (H : QueryHelpers E) : Prop :=
  (∀ (q : EventQuery) (es : List E), q.namesNoEmpty = true →
    H.select q.unpaged es = es.filter fun e => q.matches (sh e)) ∧
  (∀ (q : EventQuery) (es : List E), H.select q es = q.page (H.select q.unpaged es)) ∧
  (∀ es : List E, ((H.counters es).map Prod.fst).Nodup) ∧
  (∀ (es : List E) (k : EventType) (n : Nat), (k, n) ∈ H.counters es ↔ n = countOfType sh k es ∧ n ≠ 0) ∧
  (∀ (ts : Option (List EventType)) (es : List E),
    H.count ts es = (es.filter fun e => ts.all fun l => l.contains (sh e).type).length)

/-- `failures()` that keeps the two transition failure kinds and leaves out ActionTimedOut. -/
def evt030_failuresNoAto : QueryHelpers EventShape :=
  { refQueryHelpers id with
    failures := fun es => es.filter fun s =>
      s.type == .transitionFailed || s.type == .transitionTimedOut }

/-- ✗ `failures()` without ActionTimedOut meets lines 1, 2 and 4 to 6 and violates EVT-030
(line 3, AC4). -/
@[evidence mutant EVT_030]
theorem EVT_030_mutant_failuresNoAto :
    evt030_noFailureLine id evt030_failuresNoAto ∧ ¬ EVT_030 id evt030_failuresNoAto := by
  refine ⟨⟨fun _ _ _ => rfl, fun _ _ => rfl, refCounters_keys_nodup id, mem_refCounters id,
    fun _ _ => rfl⟩, fun h => ?_⟩
  have := h.2.2.1 [{ type := .actionTimedOut, transition := some "t" }]
  revert this
  decide

/-- The mutant reading without line 4 (no type twice): lines 1 to 3, 5 and 6 only. -/
def evt030_noNodupLine {E : Type} (sh : E → EventShape) (H : QueryHelpers E) : Prop :=
  (∀ (q : EventQuery) (es : List E), q.namesNoEmpty = true →
    H.select q.unpaged es = es.filter fun e => q.matches (sh e)) ∧
  (∀ (q : EventQuery) (es : List E), H.select q es = q.page (H.select q.unpaged es)) ∧
  (∀ es : List E, H.failures es = es.filter fun e => (sh e).type.isFailure) ∧
  (∀ (es : List E) (k : EventType) (n : Nat), (k, n) ∈ H.counters es ↔ n = countOfType sh k es ∧ n ≠ 0) ∧
  (∀ (ts : Option (List EventType)) (es : List E),
    H.count ts es = (es.filter fun e => ts.all fun l => l.contains (sh e).type).length)

/-- A histogram that lists every entry twice. -/
def evt030_dupCounters : QueryHelpers EventShape :=
  { refQueryHelpers id with counters := fun es => refCounters id es ++ refCounters id es }

/-- ✗ A histogram that names a type twice meets lines 1 to 3, 5 and 6 and violates EVT-030
(line 4): its values add up to twice the number of events. -/
@[evidence mutant EVT_030]
theorem EVT_030_mutant_dupCounters :
    evt030_noNodupLine id evt030_dupCounters ∧ ¬ EVT_030 id evt030_dupCounters := by
  refine ⟨⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun es k n => ?_, fun _ _ => rfl⟩,
    fun h => ?_⟩
  · simp only [evt030_dupCounters, List.mem_append, or_self]
    exact mem_refCounters id es k n
  · have := h.2.2.2.1 [{ type := .transitionStarted }]
    revert this
    decide

/-- The mutant reading without line 5 (the histogram counts): lines 1 to 4 and 6 only. -/
def evt030_noHistLine {E : Type} (sh : E → EventShape) (H : QueryHelpers E) : Prop :=
  (∀ (q : EventQuery) (es : List E), q.namesNoEmpty = true →
    H.select q.unpaged es = es.filter fun e => q.matches (sh e)) ∧
  (∀ (q : EventQuery) (es : List E), H.select q es = q.page (H.select q.unpaged es)) ∧
  (∀ es : List E, H.failures es = es.filter fun e => (sh e).type.isFailure) ∧
  (∀ es : List E, ((H.counters es).map Prod.fst).Nodup) ∧
  (∀ (ts : Option (List EventType)) (es : List E),
    H.count ts es = (es.filter fun e => ts.all fun l => l.contains (sh e).type).length)

/-- A histogram that lists all thirteen types, with a zero count for each type that does not
occur. -/
def evt030_zeroCounters : QueryHelpers EventShape :=
  { refQueryHelpers id with
    counters := fun es => allEventTypes.map fun k => (k, countOfType id k es) }

/-- ✗ A histogram with zero entries meets lines 1 to 4 and 6 and violates EVT-030 (line 5,
"name no other event type"): on an empty store it still names ExecutionStarted. -/
@[evidence mutant EVT_030]
theorem EVT_030_mutant_zeroCounters :
    evt030_noHistLine id evt030_zeroCounters ∧ ¬ EVT_030 id evt030_zeroCounters := by
  refine ⟨⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun es => ?_, fun _ _ => rfl⟩,
    fun h => ?_⟩
  · simp only [evt030_zeroCounters, List.map_map, Function.comp_def, List.map_id']
    exact allEventTypes_nodup
  · have := (h.2.2.2.2.1 [] .executionStarted 0).1 (by decide)
    exact this.2 rfl

/-- The mutant reading without line 6 (the count): lines 1 to 5 only. -/
def evt030_noCountLine {E : Type} (sh : E → EventShape) (H : QueryHelpers E) : Prop :=
  (∀ (q : EventQuery) (es : List E), q.namesNoEmpty = true →
    H.select q.unpaged es = es.filter fun e => q.matches (sh e)) ∧
  (∀ (q : EventQuery) (es : List E), H.select q es = q.page (H.select q.unpaged es)) ∧
  (∀ es : List E, H.failures es = es.filter fun e => (sh e).type.isFailure) ∧
  (∀ es : List E, ((H.counters es).map Prod.fst).Nodup) ∧
  (∀ (es : List E) (k : EventType) (n : Nat), (k, n) ∈ H.counters es ↔ n = countOfType sh k es ∧ n ≠ 0)

/-- A count by type that reads an empty type set as no filter (an `if not types:` guard) and so
counts every event where the type query returns none. -/
def evt030_emptyTypesCountsAll : QueryHelpers EventShape :=
  { refQueryHelpers id with
    count := fun ts es => match ts with
      | none | some [] => es.length
      | some l => (es.filter fun s => l.contains s.type).length }

/-- ✗ A count that reads an empty type set as no filter meets lines 1 to 5 and violates EVT-030
(line 6): `count(types=set())` is not the number of events of no type. -/
@[evidence mutant EVT_030]
theorem EVT_030_mutant_emptyTypesCountsAll :
    evt030_noCountLine id evt030_emptyTypesCountsAll ∧ ¬ EVT_030 id evt030_emptyTypesCountsAll := by
  refine ⟨⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, refCounters_keys_nodup id,
    mem_refCounters id⟩, fun h => ?_⟩
  have := h.2.2.2.2.2 (some []) [{ type := .tokenAdded }]
  revert this
  decide

/-! ### Non-vacuity: the test derivation on the reference -/

/-- A decided store of mixed events: a run of `t` (enabled, a token removed from `p`, started, a
token added to `q` and one to `p`, completed, a log message of its action), an engine
diagnostic with no transition name, and a failure and an action timeout of `u`. -/
def evt030_mixed : List EventShape :=
  [{ type := .executionStarted },
   { type := .transitionEnabled, transition := some "t" },
   { type := .tokenRemoved, place := some "p" },
   { type := .transitionStarted, transition := some "t" },
   { type := .logMessage },
   { type := .tokenAdded, place := some "q" },
   { type := .tokenAdded, place := some "p" },
   { type := .transitionCompleted, transition := some "t" },
   { type := .logMessage, transition := some "t" },
   { type := .transitionFailed, transition := some "u" },
   { type := .actionTimedOut, transition := some "u" }]

/-- The test derivation on the reference: each filter returns the right subset in store order
(the type query returns the completed event, the transition query the four events that carry
`t`, the log message included and the nameless diagnostic left out, the place query paged by
offset 1 and limit 1 the second token event of `p` or `q`), `failures()` returns the failure and
the action timeout, the histogram's values add up to the eleven events, the count of all events
is eleven and the count of the token types three; a query that pages before it filters gives
another page. -/
@[evidence nonvacuous EVT_030]
theorem EVT_030_nonvacuous :
    (refQueryHelpers id).select { types := some [.transitionCompleted] } evt030_mixed =
      [{ type := .transitionCompleted, transition := some "t" }] ∧
    (refQueryHelpers id).select { transitions := some ["t"] } evt030_mixed =
      [{ type := .transitionEnabled, transition := some "t" },
       { type := .transitionStarted, transition := some "t" },
       { type := .transitionCompleted, transition := some "t" },
       { type := .logMessage, transition := some "t" }] ∧
    (refQueryHelpers id).select { places := some ["p", "q"], offset := 1, limit := some 1 }
      evt030_mixed = [{ type := .tokenAdded, place := some "q" }] ∧
    (refQueryHelpers id).failures evt030_mixed =
      [{ type := .transitionFailed, transition := some "u" },
       { type := .actionTimedOut, transition := some "u" }] ∧
    (((refQueryHelpers id).counters evt030_mixed).map Prod.snd).sum = 11 ∧
    (refQueryHelpers id).count none evt030_mixed = 11 ∧
    (refQueryHelpers id).count (some [.tokenAdded, .tokenRemoved]) evt030_mixed = 3 ∧
    evt030_pageFirst.select { places := some ["p", "q"], offset := 1, limit := some 1 }
      evt030_mixed = [] := by
  decide

end Libpetri.Spec
