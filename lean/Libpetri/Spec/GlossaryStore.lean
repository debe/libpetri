import Libpetri.Spec.Registry

set_option linter.missingDocs true

/-!
# Store terms: what an event store shows after a history of operations

The vocabulary the event store requirements use ([EVT-020] to [EVT-025], [EVT-030] to
[EVT-032], `spec/08-events-observability.md`). The store tier reads no marking and runs no net:
an event store is observed only through what a call of `events()` returns after the operations
made on it, and through whether it reports itself enabled. So a store requirement is a predicate
over an abstract `StoreObs E`, the observation of one store, and the reference stores below are
its witnesses.

The event type `E` is a parameter. The store requirements say nothing about the content of an
event (that is the executor event model, `RefEvents`, wave W7); a store that only filters or
reads events by kind or transition name takes the event type of that model as `E`.

Ruling D29 (a) fixes what the interface promises: `events()` returns a sublist of the appended
events in append order (`appended`), whether the returned list is a copy is not specified, and
`clear()` exists only where a store provides it (`StoreObs.hasClear`). A store requirement that
holds of one store role is stated on its own store variable: the in-memory store and the noop
store cannot be one store (design events.md, section 3: one store per role).

The executor side is one definition here, `storeSink`: what an executor appends to a store for
the events it emits, decided from the store's enabled flag ([EVT-020] AC3, [PERF-010]). It is a
glossary fact, not a constraint on an executor: the executor model of wave W7 emits events, and
this is how they reach a store.
-/

namespace Libpetri.Spec

variable {E : Type}

/-! ## Operations and histories -/

/-- An operation on an event store: `append e` ([EVT-020] `append(event)`) or `clear`
([EVT-021] `clear()`, offered only where the store provides it, ruling D29 (a)). A history is the
list of the operations made on one store, oldest first. -/
inductive StoreOp (E : Type) where
  /-- `append(event)`: hand one event to the store. -/
  | append (e : E)
  /-- `clear()`: empty the store, where the store provides it. -/
  | clear
  deriving DecidableEq, Repr

/-- **Glossary: Append order** (proposed term). The events a history appended, in the order they
were appended, clears ignored: the list every store's `events()` is a sublist of ([EVT-020],
ruling D29 (a)). -/
def appended (h : List (StoreOp E)) : List E :=
  h.filterMap fun
    | .append e => some e
    | .clear => none

/-- One operation on the list of events a store keeps when it keeps every event: an append adds
the event at the end, a clear empties the list. -/
def stepOp (acc : List E) : StoreOp E → List E
  | .append e => acc ++ [e]
  | .clear => []

/-- **Glossary: Retained events** (proposed term). The events a store that keeps every event
holds after a history: the events appended since the last clear, in append order. -/
def retained (h : List (StoreOp E)) : List E := h.foldl stepOp []

/-! ## The observation of a store -/

/-- **Glossary: Event store** (proposed term). A store, as a caller observes it ([EVT-020]):

* `enabled`: whether the store reports itself enabled (`isEnabled()` in Java and TypeScript;
  the associated constant `ENABLED` of the store type in Rust);
* `hasClear`: whether the store provides `clear()` (ruling D29 (a): where provided);
* `read h h'`: the list a call of `events()` made after the history `h` shows once the further
  operations `h'` have run. With `h' = []` it is the list the call returns. A store that returns
  a copy shows the same list for every `h'`; one that returns its live list (TypeScript's
  in-memory store, clash evt-b#6) shows the later appends too. Ruling D29 (a) leaves which one
  unspecified, so a requirement that does not mean to fix it either reads `h' = []` only or
  reads every `h'` against the appends of the whole history `h ++ h'`, a bound that a copy and
  a live view both meet ([EVT-020]).

A history with a `clear` made on a store without `clear()` is not one a caller can make; a
requirement that quantifies over every history covers it anyway. -/
structure StoreObs (E : Type) where
  /-- Whether the store reports itself enabled. -/
  enabled : Bool
  /-- Whether the store provides `clear()`. -/
  hasClear : Bool
  /-- `read h h'`: what a call of `events()` after `h` shows once `h'` has run. -/
  read : List (StoreOp E) → List (StoreOp E) → List E
  /-- The store's own normalisation of an event, through which [EVT-020] compares what it shows
  with what was appended: the identity for every store but the Python binding's in-memory store,
  which removes the payload of a token event on a place outside its capture filter. -/
  norm : E → E := id

/-- What an executor appends to the store `S` for the events `tr` it emits, in emission order:
every event when `S` reports itself enabled, nothing otherwise ([EVT-020] AC3, [PERF-010]: the
executor decides from the store's enabled flag). Whether an executor builds the event objects
of a disabled store at all is not observable here and is kind Q (ruling D34). -/
def storeSink (S : StoreObs E) (tr : List E) : List (StoreOp E) :=
  if S.enabled then tr.map .append else []

/-! ## Reference stores -/

/-- The reference in-memory store ([EVT-021]; Java `InMemoryEventStore`, TypeScript
`InMemoryEventStore`, Rust `InMemoryEventStore`): enabled, keeps every event appended since the
last clear, in append order, and returns a copy. Java and TypeScript provide `clear()`; the Rust
store does not, which ruling D29 (a) allows ("where provided"). -/
def refMemStore : StoreObs E where
  enabled := true
  hasClear := true
  read h _ := retained h

#spec_witness refMemStore

/-- The reference noop store ([EVT-022]; Java `EventStore.noop()`, TypeScript
`noopEventStore()`, Rust `NoopEventStore`): reports itself not enabled, discards every append and
returns the empty list from every call of `events()`, which no later operation changes (an
immutable `List.of()` in Java, a frozen empty array in TypeScript, the static empty slice in
Rust). None of the three provides `clear()`. -/
def refNoopStore : StoreObs E where
  enabled := false
  hasClear := false
  read _ _ := []

#spec_witness refNoopStore

/-- The reference bounded store of capacity `c` ([EVT-024]'s capacity line; the debug stores):
enabled, keeps the newest `c` of the retained events, in append order, and returns a copy. -/
def refBoundedStore (c : Nat) : StoreObs E where
  enabled := true
  hasClear := false
  read h _ := let l := retained h; l.drop (l.length - c)

#spec_witness refBoundedStore

/-! ## Store variants shared by the evidence of the store blocks

These are not glossary terms: they are the store shapes that more than one block of the store
tier uses as evidence, defined once here. -/

/-- The live in-memory store (TypeScript `InMemoryEventStore`, `event-store.ts:58-60`): the array
`events()` returns is the store's own, so it shows every operation made after the call (its
`clear()` empties that array in place). -/
def liveMemStore : StoreObs E where
  enabled := true
  hasClear := true
  read h h' := retained (h ++ h')

/-- The newest-first store: it keeps the events appended since the last clear and returns them in
reverse append order (last in, first out). -/
def newestFirstStore : StoreObs E where
  enabled := true
  hasClear := true
  read h _ := (retained h).reverse

/-- A store that reports itself not enabled but keeps every event appended to it directly, as an
in-memory store without `clear()` whose only change is an `isEnabled()` that returns false. -/
def disabledKeepStore : StoreObs E where
  enabled := false
  hasClear := false
  read h _ := retained h

/-! ## Lemmas -/

/-- Appending one event adds it at the end of the retained events. -/
theorem retained_append_one (h : List (StoreOp E)) (e : E) :
    retained (h ++ [.append e]) = retained h ++ [e] := by
  simp [retained, List.foldl_append, stepOp]

/-- A clear leaves no retained event. -/
theorem retained_append_clear (h : List (StoreOp E)) :
    retained (h ++ [.clear]) = [] := by
  simp [retained, List.foldl_append, stepOp]

/-- Folding appends only onto `acc` adds them at its end, in order. -/
theorem foldl_stepOp_appends (es acc : List E) :
    (es.map StoreOp.append).foldl stepOp acc = acc ++ es := by
  induction es generalizing acc with
  | nil => simp
  | cons e es ih => simp [stepOp, ih]

/-- A history of appends only retains exactly its events, in order. -/
theorem retained_appends (es : List E) : retained (es.map StoreOp.append) = es := by
  simp [retained, foldl_stepOp_appends]

/-- A history of appends only appended exactly its events, in order. -/
theorem appended_appends (es : List E) : appended (es.map StoreOp.append) = es := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [appended] using ih

/-- A store that reports itself not enabled receives nothing from an executor. -/
theorem storeSink_disabled {S : StoreObs E} (h : S.enabled = false) (tr : List E) :
    storeSink S tr = [] := by
  simp [storeSink, h]

/-- A store that reports itself enabled receives every emitted event, in emission order. -/
theorem storeSink_enabled {S : StoreObs E} (h : S.enabled = true) (tr : List E) :
    appended (storeSink S tr) = tr := by
  simp only [storeSink, h, if_true]
  exact appended_appends tr

end Libpetri.Spec
