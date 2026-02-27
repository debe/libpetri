# 01 — Core Model

This document specifies the foundational model of the CTPN engine: places, tokens, transitions, arcs, net construction, actions, and context.

---

## Places

#### CORE-001: Place Definition

**Priority:** MUST

A place is a named, typed container that holds tokens. Each place has a string name and an associated token value type.

**Acceptance Criteria:**
1. A place can be created with a name and a token type.
2. The name is available for display, debugging, and export.

**Test derivation:** Create a place with name "Ready" and token type String; verify name and type are retrievable.

---

#### CORE-002: Place Identity

**Priority:** MUST

Two places are considered equal if and only if they have the same identity. Identity semantics are implementation-defined (structural equality by name+type, or reference/ID-based equality), but must be consistent within a single implementation.

**Acceptance Criteria:**
1. A place is equal to itself.
2. Two independently constructed places with different names are never equal.
3. Place identity is stable across the lifetime of a net.

**Test derivation:** Create two places with different names; verify inequality. Create one place and reference it twice; verify equality.

---

#### CORE-003: Place Type Safety

**Priority:** MUST

A place only accepts tokens whose values are compatible with the place's declared type. The mechanism of type checking is implementation-defined (compile-time generics, runtime type checks, or both).

**Acceptance Criteria:**
1. Adding a token with a compatible value succeeds.
2. Adding a token with an incompatible value is rejected (compile-time error or runtime error).

**Test derivation:** Create a place of type Integer; add an integer token (succeeds); attempt to add a string token (rejected).

---

## Tokens

#### CORE-010: Token Immutability

**Priority:** MUST

A token is an immutable value object consisting of a typed payload value and a creation timestamp. Once created, neither the value nor the timestamp can be modified.

**Acceptance Criteria:**
1. Token value is accessible after creation and matches the original.
2. Token timestamp is accessible after creation.
3. No API exists to mutate token fields after creation.

**Test derivation:** Create a token with value 42; verify value() returns 42 and timestamp is non-null.

---

#### CORE-011: Token Creation

**Priority:** MUST

Tokens are created via a factory that captures the current time as the creation timestamp.

**Acceptance Criteria:**
1. Creating a token records the current time.
2. Two tokens created sequentially have non-decreasing timestamps.

**Test derivation:** Create two tokens in sequence; verify second timestamp >= first.

---

#### CORE-012: Unit Token

**Priority:** MUST

A unit token is a special token with no meaningful payload value, used for pure control flow signaling. The engine provides a canonical way to create unit tokens.

**Acceptance Criteria:**
1. A unit token can be created.
2. A unit token can be added to a place that accepts the unit type.
3. Unit tokens are identifiable as such.

**Test derivation:** Create a unit token; verify it is recognized as a unit token by the engine.

---

#### CORE-013: Token FIFO Ordering

**Priority:** MUST

Tokens within a place are stored in FIFO (first-in, first-out) order. The oldest token is consumed first when a transition fires.

**Acceptance Criteria:**
1. Adding tokens A, B, C in order, then consuming one, yields A.
2. Consuming again yields B.

**Depends on:** [CORE-001]
**Test derivation:** Add three tokens to a place; remove them one at a time; verify FIFO order.

---

## Transitions

#### CORE-020: Transition Definition

**Priority:** MUST

A transition is a named element that consumes tokens from input places, executes an action, and produces tokens to output places. Each transition has:
- A name (for display/debugging)
- Input specifications with cardinality (see [IO-001])
- An output specification with routing structure (see [IO-010])
- Zero or more inhibitor arcs
- Zero or more read arcs
- Zero or more reset arcs
- A timing specification (see [TIME-001])
- A priority value (integer, higher = fires first)
- An action to execute

**Acceptance Criteria:**
1. A transition can be constructed with all the above fields via a builder pattern.
2. All fields are accessible after construction.

**Test derivation:** Build a transition with inputs, outputs, inhibitors, reads, resets, timing, priority, and action; verify all fields match.

---

#### CORE-021: Transition Identity

**Priority:** MUST

Each transition instance has a unique identity. Two transition instances are never equal, even if they share the same name.

**Acceptance Criteria:**
1. Two transitions built with the same name are not equal (identity-based, not name-based).
2. A transition is equal to itself.

**Test derivation:** Build two transitions with name "Process"; verify they are not equal.

---

#### CORE-022: Transition Enablement

**Priority:** MUST

A transition is **enabled** when ALL of the following conditions hold simultaneously:
1. All input places have at least `requiredCount()` tokens (see [IO-001]–[IO-004])
2. All read places have at least one token
3. No inhibitor place has any tokens
4. If input arcs have guard predicates, at least the required number of tokens pass the guard

When any condition ceases to hold, the transition becomes disabled.

**Acceptance Criteria:**
1. Transition with satisfied inputs, reads present, inhibitors empty → enabled.
2. Missing input tokens → disabled.
3. Missing read tokens → disabled.
4. Inhibitor place has tokens → disabled.
5. Guard predicate filters out all tokens → disabled.

**Depends on:** [IO-001], [CORE-030], [CORE-031], [CORE-032]
**Test derivation:** Systematically toggle each condition and verify enablement changes.

---

## Arc Types

#### CORE-030: Input Arc

**Priority:** MUST

An input arc connects a place to a transition. When the transition fires, it **consumes** one or more tokens from the place according to the input's cardinality specification (see [IO-001]–[IO-004]). An input arc may optionally include a **guard predicate** that filters which tokens are eligible for consumption.

**Acceptance Criteria:**
1. Transition with input arc consumes tokens from the place on firing.
2. With guard: only tokens passing the predicate are eligible.
3. Guarded input with no matching tokens → transition not enabled.

**Test derivation:** Create transition with guarded input; add matching and non-matching tokens; verify only matching tokens consumed.

---

#### CORE-031: Inhibitor Arc

**Priority:** MUST

An inhibitor arc connects a place to a transition as a **negative precondition**. The transition is disabled whenever the inhibitor place contains any tokens. The inhibitor arc does not consume tokens.

**Acceptance Criteria:**
1. Inhibitor place empty → transition enablement unaffected by inhibitor.
2. Inhibitor place has tokens → transition disabled.
3. Tokens in inhibitor place are not consumed when other transitions fire.

**Test derivation:** Create transition with inhibitor; verify disabled when inhibitor place has tokens, enabled when empty.

---

#### CORE-032: Read Arc

**Priority:** MUST

A read arc (test arc) connects a place to a transition, requiring the place to have at least one token for enablement. The token is **not consumed** when the transition fires; its value is available to the action via the transition context.

**Acceptance Criteria:**
1. Read place must have tokens for transition to be enabled.
2. Token remains in place after transition fires.
3. Action receives the read token value.

**Test derivation:** Create transition with read arc; fire transition; verify token still in place after firing.

---

#### CORE-033: Read Arc Multi-Reader

**Priority:** MUST

Multiple transitions can have read arcs to the same place. All such transitions can be enabled simultaneously (no conflict), since read arcs do not consume tokens.

**Acceptance Criteria:**
1. Two transitions with read arcs to the same place are both enabled when the place has tokens.
2. Both can fire without conflict.

**Depends on:** [CORE-032]
**Test derivation:** Two transitions read from the same place; verify both can fire.

---

#### CORE-034: Reset Arc

**Priority:** MUST

A reset arc connects a place to a transition. When the transition fires, **all** tokens are removed from the place. A reset arc does **not** require the place to have any tokens for the transition to be enabled.

**Acceptance Criteria:**
1. Transition with reset arc fires even if the reset place is empty.
2. If the reset place has tokens, all are removed on firing.
3. Reset arc does not contribute to enablement (no token requirement).

**Test derivation:** Fire transition with reset arc on place with 3 tokens; verify all tokens removed. Fire again with empty place; verify no error.

---

#### CORE-035: Output Arc

**Priority:** MUST

An output arc connects a transition to a place. When the transition's action completes, tokens are produced to output places according to the output specification (see [IO-010]–[IO-015]).

**Acceptance Criteria:**
1. After transition fires, produced tokens appear in the output place.
2. Output tokens are created with current timestamp.

**Test derivation:** Fire transition with output; verify token appears in output place.

---

#### CORE-036: Arc Semantics Summary

**Priority:** MUST

The five arc types have the following semantics:

| Arc Type  | Requires Token? | Consumes? | Effect                      |
|-----------|-----------------|-----------|------------------------------|
| Input     | Yes             | Yes       | Token consumed on fire       |
| Output    | No              | No        | Token produced on complete   |
| Inhibitor | No (blocks if present) | No | Disables transition          |
| Read      | Yes             | No        | Token remains; provides value|
| Reset     | No              | Yes (all) | All tokens removed on fire   |

**Acceptance Criteria:**
1. Each arc type behaves exactly as described in the table.

**Test derivation:** One test per arc type verifying semantics.

---

## Net Construction

#### CORE-040: Net Builder

**Priority:** MUST

A Petri net is constructed via a builder pattern. The builder accepts places and transitions and produces an immutable net definition.

**Acceptance Criteria:**
1. Builder can add places and transitions.
2. `build()` produces an immutable net.
3. Places referenced by transitions are auto-collected (implementations that auto-collect from arcs SHOULD do so).

**Test derivation:** Build a net with transitions; verify all places from arcs are present in the net.

---

#### CORE-041: Net Immutability

**Priority:** MUST

After construction, a Petri net definition is immutable. The set of places, transitions, and their connections cannot be modified.

**Acceptance Criteria:**
1. No mutation methods exist on the constructed net.
2. Collections returned by the net are unmodifiable or copies.

**Test derivation:** Build a net; verify no mutation API exists.

---

#### CORE-042: Action Binding Separation

**Priority:** MUST

The net's static structure (places, transitions, arcs, timing, priority) MUST be separable from the runtime behavior (actions). A `bindActions()` operation takes a structure and a mapping of transition names to actions, producing a new net with actions bound.

**Acceptance Criteria:**
1. A net can be created with no actions (all transitions use passthrough).
2. `bindActions(mapping)` produces a new net with actions bound by transition name.
3. The original net is not modified.
4. Unbound transitions retain the passthrough action.

**Test derivation:** Create a net with 3 transitions; bind actions for 2; verify the third still has passthrough.

---

## Actions

#### CORE-050: Transition Action

**Priority:** MUST

A transition action is an asynchronous function that receives a transition context and produces output tokens. The action signature returns a future/promise that resolves when the action completes.

**Acceptance Criteria:**
1. Action receives a context with consumed input tokens and read token values.
2. Action produces output tokens via the context or a return value.
3. Action is asynchronous (returns future/promise/completion stage).

**Test derivation:** Create action that reads input, transforms it, and produces output; verify output tokens.

---

#### CORE-051: Passthrough Action

**Priority:** MUST

A built-in passthrough action that consumes input tokens and produces no output tokens. This is the default action for transitions without explicitly bound actions.

**Acceptance Criteria:**
1. Passthrough action completes immediately.
2. No output tokens are produced.

**Test derivation:** Fire transition with passthrough; verify no output tokens.

---

#### CORE-052: Fork Action

**Priority:** SHOULD

A built-in fork action that copies a single input token value to all declared output places.

**Acceptance Criteria:**
1. Requires exactly one input place.
2. Produces the input value to all output places.
3. Throws/errors if more than one input place is declared.

**Test derivation:** Fork action with 1 input and 3 outputs; verify all 3 receive the same value.

---

#### CORE-053: Transform Action

**Priority:** SHOULD

A built-in transform action that applies a user-provided function to the context, then copies the result to all output places.

**Acceptance Criteria:**
1. Function receives the transition context.
2. Return value is produced to all output places.

**Test derivation:** Transform action doubles an integer input; verify all outputs receive the doubled value.

---

#### CORE-054: Produce Action

**Priority:** SHOULD

A built-in action that produces a fixed value to a specified output place.

**Acceptance Criteria:**
1. The specified place receives a token with the fixed value.

**Test derivation:** Produce action with value "hello" to place P; verify P receives "hello".

---

## Transition Context

#### CORE-060: Context Input Access

**Priority:** MUST

The transition context provides access to consumed input token values. Actions can retrieve single values or lists of values from declared input places.

**Acceptance Criteria:**
1. `input(place)` returns the single consumed value.
2. `inputs(place)` returns all consumed values (for multi-token cardinality).
3. `inputToken(place)` returns the token with metadata (including timestamp).
4. Accessing an undeclared input place results in an error.

**Depends on:** [CORE-050]
**Test derivation:** Fire transition consuming 3 tokens; verify `inputs()` returns 3 values.

---

#### CORE-061: Context Read Access

**Priority:** MUST

The transition context provides access to read (non-consumed) token values from declared read places.

**Acceptance Criteria:**
1. `read(place)` returns the read value without consuming it.
2. Accessing an undeclared read place results in an error.

**Depends on:** [CORE-032]
**Test derivation:** Fire transition with read arc; verify `read()` returns value; verify token still in place.

---

#### CORE-062: Context Output Access

**Priority:** MUST

The transition context provides a way for actions to declare output tokens for production.

**Acceptance Criteria:**
1. `output(place, value)` declares a token to produce.
2. Producing to an undeclared output place results in an error.

**Depends on:** [CORE-035]
**Test derivation:** Action calls `output(place, value)`; verify token appears in place after firing.

---

#### CORE-063: Context Structure Enforcement

**Priority:** MUST

The transition context enforces that actions can only access places declared in the transition's structure. Attempting to access an undeclared place (input, read, or output) results in an error.

**Acceptance Criteria:**
1. Accessing undeclared input → error.
2. Accessing undeclared read → error.
3. Producing to undeclared output → error.

**Test derivation:** Create context with restricted place sets; attempt out-of-bounds access; verify errors.

---

#### CORE-064: Execution Context Injection

**Priority:** SHOULD

The transition context supports injection of external objects (e.g., tracing spans, configuration) that are available to the action during execution. Objects are keyed by type or string key.

**Acceptance Criteria:**
1. External object can be added to the context.
2. Action can retrieve the object by its key/type.
3. Missing object returns null/None.

**Test derivation:** Inject a custom object; verify action can retrieve it.

---

## Marking

#### CORE-070: Marking State

**Priority:** MUST

A marking represents the current distribution of tokens across all places. Internally, each place maps to a FIFO queue of tokens.

**Acceptance Criteria:**
1. Empty marking has zero tokens in all places.
2. Tokens can be added and removed from specific places.
3. Token count per place is queryable.

**Test derivation:** Create empty marking; add 3 tokens to place P; verify count is 3; remove one; verify count is 2.

---

#### CORE-071: Marking Thread Safety

**Priority:** MUST

The marking is accessed only by the orchestrator thread. It is NOT thread-safe. Transition actions must NOT directly access the marking.

**Acceptance Criteria:**
1. No synchronization primitives are used in the marking implementation.
2. Token production from actions goes through the context/output mechanism, not direct marking access.

**Test derivation:** Architectural review; verify marking has no locks/atomics.

---

#### CORE-072: Initial Marking

**Priority:** MUST

An executor can be initialized with an initial marking that pre-populates places with tokens before execution begins.

**Acceptance Criteria:**
1. Initial marking distributes tokens to specified places.
2. Execution begins with these tokens available.

**Test derivation:** Create executor with initial marking {P1: [a, b], P2: [c]}; verify tokens present before first firing.
