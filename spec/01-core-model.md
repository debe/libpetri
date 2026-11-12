# 01 — Core Model

This document specifies the foundational model of the CTPN engine: places, tokens, transitions, arcs, net construction, actions, and context.

---

## Places

#### CORE-001: Place Definition

**Priority:** MUST
**Kind:** Q

A place is a named, typed container that holds tokens. Each place has a string name and an associated token value type.

**Acceptance Criteria:**
1. A place can be created with a name and a token type.
2. The name is available for display, debugging, and export.

**Note:** When a place is part of a subnet body composed into an enclosing net, its observable name is rewritten by prefix concatenation per [MOD-010] (separator `/`). The naming rule is owned by MOD; CORE only requires that *some* string name exists and is stable.

**Test derivation:** Create a place with name "Ready" and token type String; verify name and type are retrievable.

---

#### CORE-002: Place Identity

**Priority:** MUST
**Kind:** F

Two places are the same place exactly when they have the same identity, and an implementation takes a place's identity from its name, or from its name and its token type. It does so the same way throughout the implementation, and never from the object that represents the place. TypeScript, Rust and Python identify a place by its name. Java identifies a place by its name and its token type; a Java place records its token type as a run-time class, so the type arguments of a generic type are not part of it. In TypeScript and Python the language's own equality of place objects is not this identity: two place objects created separately with one name are two objects and one place.

Two places that are the same place *shall* have the same name.

Two places with the same name and the same token type *shall* be the same place.

An implementation *shall* identify a place either by its name, so that two places with the same name are the same place, or by its name and its token type, so that two places that are the same place have the same token type.

**Acceptance Criteria:**
1. A place is the same place as itself.
2. Two independently constructed places with different names are never the same place.
3. Place identity is stable across the lifetime of a net.

**Note:** The naming convention used by modular composition (`prefix/originalName` per [MOD-010]) means that the *same* logical body place, instantiated under two different prefixes, yields two distinct places by this identity rule, which is exactly what per-instance state isolation per [MOD-012] requires.

**Test derivation:** Create two places with different names; verify they are different places. Create one place and reference it twice; verify it is the same place. Create two places separately with the same name and token type and build a net whose transitions use both; verify the engine treats them as one place (the compiled net holds one place of that name). Create two places with the same name and different token types; verify the engine treats them as one place in TypeScript, Rust and Python and as two places in Java.

---

#### CORE-003: Place Type Safety

**Priority:** MUST
**Kind:** A

A place has a declared token type, and a token is compatible with a place when its value is of that type. A token without a value, the unit token ([CORE-012]), is compatible with every place. The engine does not check the type of a token it deposits or a host adds: the net's author and the host keep an action's outputs, a forwarded token ([IO-014]) and an injected token compatible with their places. An implementation that keeps a run-time token type for each place (Java) rejects an initial marking that puts a token with an incompatible value in a place. Where an API call takes a typed place handle (Java, TypeScript and Rust), the compiler rejects a token of another type at that call; this requirement does not rely on it.

*When* a transition fires from a marking in which every token is compatible with its place, nothing else changes the marking between the firing's consumption and its deposit, and every token the firing deposits is compatible with the place it is deposited to, every token a place holds after the firing *shall* be compatible with that place.

*When* a transition fires from a marking in which every token is compatible with its place, every token its action receives from one of its input places or read places *shall* be compatible with that place.

*When* a transition can fire from a marking and deposit tokens to a list of places, it *shall* also be able to fire from that marking, delivering the same tokens to its action, and deposit to the same places, in the same order, any tokens compatible with them.

**Acceptance Criteria:**
1. A firing whose action outputs a token with a compatible value to a place succeeds.
2. In an implementation that keeps a run-time token type for each place, an initial marking that puts a token with an incompatible value in a place is rejected.

**Test derivation:** Create a place of type Integer and a transition that outputs to it; fire it with an action that outputs an integer token (succeeds). In Java, build an executor whose initial marking puts a string token in that place (rejected with an `IllegalArgumentException`).

---

## Tokens

#### CORE-010: Token Immutability

**Priority:** MUST
**Kind:** B

A token is an immutable value object consisting of a typed payload value and a creation timestamp. Once created, neither the value nor the timestamp can be modified.

*When* a transition fires and nothing else changes the marking between the firing's consumption and its deposit, every token a place holds after the firing *shall* be a token the place held before the firing, with the same value and creation timestamp, or a token the action emitted to that place, and the firing *shall* not duplicate any of these tokens.

*When* a transition fires and nothing else changes the marking between the firing's consumption and its deposit, every token that a place without a reset arc of the transition held before the firing *shall* still be in that place after the firing, with the same value and creation timestamp, unless the action received it from that place as a consumed input.

*When* a transition fires, every token its action receives from one of its input places or read places *shall* be a token that place held before the firing, with the same value and creation timestamp, and the action *shall* not receive a consumed token more often than its input place held it.

**Acceptance Criteria:**
1. Token value is accessible after creation and matches the original.
2. Token timestamp is accessible after creation.
3. No API exists to mutate token fields after creation.

**Test derivation:** Create a token with value 42; verify value() returns 42 and timestamp is non-null.

---

#### CORE-011: Token Creation

**Priority:** MUST
**Kind:** F

A host creates a token through a factory; a Python host passes values instead, and the Rust runtime it binds creates their tokens. The default factory stamps the token with the current reading of the host's wall clock. It is called from host code, which no executor's clock reaches, so a clock injected into an executor ([TIME-015]) does not change what it stamps. A second factory takes the timestamp as an argument and keeps it as given, without clamping or rounding it, so that a host can create a token that is the same on every replay or restore one from a snapshot ([CORE-073]); this is the construction at an explicit timestamp that [TIME-015] requires. A helper that seeds a token from a clock's reading is this second factory applied to that reading. The canonical unit token ([CORE-012]) carries the timestamp 0, the start of the epoch. A token the executor creates (an action output written as a value, a token injected as a raw value, the unit token of a timeout outcome) is not made by these factories: it is stamped from the executor's epoch clock ([TIME-015] AC13), and a forwarded token keeps its timestamp ([IO-014]). A token an action builds itself through a factory and outputs as a token (Java, TypeScript) keeps that factory's stamp.

*When* a host creates a token from a value through the default factory, the token *shall* hold that value and carry the reading of the host's wall clock at the call as its creation timestamp, whatever clock an executor runs on ([TIME-015]).

*When* a host creates a token from a value and a timestamp through the explicit-timestamp factory, the token *shall* hold that value and carry that timestamp, whatever the clocks read at the call.

*When* a host creates the canonical unit token, the token *shall* hold no value and carry the timestamp 0, whatever the clocks read at the call.

*When* an action writes a value to an output place, the token the executor creates for it *shall* hold that value and carry the reading of its epoch clock at the write ([TIME-015]).

A Python action's `ctx.output` only buffers the value: its write is made when the action returns or calls `ctx.flush()`, and its token carries the epoch clock's reading at that point.

*When* a host injects a raw value into an environment place, the token the executor creates for it *shall* hold that value and carry the reading of its epoch clock at the call ([TIME-015]).

*When* the budget of a firing runs out, each token the executor mints for the timeout outcome *shall* carry the reading of its epoch clock at that moment, and each token a `ForwardInput` forwards *shall* be the consumed token itself, with its timestamp ([IO-014]).

*When* an action outputs a token it built itself, or a host injects a token it built, the executor *shall* keep that token as it is, with its timestamp.

**Acceptance Criteria:**
1. Creating a token through the default factory yields a token that holds the given value and records the current reading of the host's wall clock.
2. While the host's wall clock does not go back, two tokens created one after the other through the default factory have non-decreasing timestamps.
3. A token created at an explicit timestamp holds the given value and carries that timestamp unchanged, also when the timestamp lies before the epoch or is finer than a millisecond and the implementation's timestamp type can hold it.
4. The canonical unit token holds no value and carries the timestamp 0.
5. While an executor runs on an injected clock, a token created through the default factory carries the reading of the host's wall clock, not the injected clock's.
6. While an executor runs on an injected clock, a token it creates for an action's value write, for a raw-value injection or as a minted timeout output carries the epoch clock's reading at that moment, not the wall clock's; a forwarded token, a token the action built and a token the host built keep their timestamps.

**Test derivation:** Read the host's wall clock, create a token through the default factory and read the wall clock again; verify that the token holds the given value and that its timestamp lies between the two readings. Create two tokens in sequence through the default factory; verify second timestamp >= first. Repeat the first step while an executor runs on an injected clock that reads far from the wall clock; verify that the timestamp still lies between the two wall-clock readings. Create tokens at explicit timestamps, including one before the epoch and one finer than a millisecond where the timestamp type can hold them, and the canonical unit token; verify that each token holds its value (no value for the unit token) and carries its timestamp unchanged (0 for the unit token). Run an executor on an injected clock that reads far from the wall clock: let an action write a value and output a token it built at an explicit timestamp, inject a raw value and a token built at an explicit timestamp, move the clock, and let a firing whose timeout branch mints a unit token and forwards its input time out; verify that the written value, the injected value and the minted unit token carry the injected clock's readings at their steps, and that the forwarded and the built tokens keep their timestamps.

---

#### CORE-012: Unit Token

**Priority:** MUST
**Kind:** Q

A unit token is a special token with no meaningful payload value, used for pure control flow signaling. The engine provides a canonical way to create unit tokens.

**Acceptance Criteria:**
1. A unit token can be created.
2. A unit token can be added to a place that accepts the unit type.
3. Unit tokens are identifiable as such.

**Test derivation:** Create a unit token; verify it is recognized as a unit token by the engine.

---

#### CORE-013: Token FIFO Ordering

**Priority:** MUST
**Kind:** B

Tokens within a place are stored in FIFO (first-in, first-out) order. The oldest token is consumed first when a transition fires, except on a correlated input of a match specification ([NU-020]).

*When* a transition fires and nothing else changes the marking between the firing's consumption and its deposit, each place that is neither one of its input places nor one of its reset places ([CORE-034]) *shall* end the firing holding its whole queue from before the firing, in queue order, followed by the tokens the firing deposited there, in the order the action produced them ([EXEC-020]).

*When* a transition fires and nothing else changes the marking between the firing's consumption and its deposit, its action *shall* receive from each input place that is not a correlated input of its match specification ([NU-020]) the first tokens of the place's queue before the firing, in queue order; unless the place is also one of its reset places, the place *shall* end the firing holding the rest of that queue, in queue order, followed by the tokens the firing deposited there, in the order the action produced them ([EXEC-010], [EXEC-020]).

**Acceptance Criteria:**
1. Adding tokens A, B, C in order, then consuming one, yields A.
2. Consuming again yields B.

**Depends on:** [CORE-001]
**Test derivation:** Add three tokens to a place; remove them one at a time; verify FIFO order.

---

## Transitions

#### CORE-020: Transition Definition

**Priority:** MUST
**Kind:** F

A transition is a named element that consumes tokens from input places, executes an action, and produces tokens to output places. Each transition has:
- A name (identifies the transition, see [TIME-010])
- Input specifications with cardinality (see [IO-001])
- An output specification with routing structure (see [IO-010])
- Zero or more inhibitor arcs
- Zero or more read arcs
- Zero or more reset arcs
- A timing specification (see [TIME-001])
- A priority value (integer, higher = fires first)
- An action to execute

*When* a transition is built, the built transition *shall* carry the name and the output specification it was given, if any, and each of its input, inhibitor, read and reset arc lists exactly as given, in the order given and with its repetitions.

*When* a transition is built with a timing, a priority or an action, the built transition *shall* carry that timing, priority or action.

*When* a transition is built without a priority, the built transition *shall* have priority 0.

Building a transition that has no match specification ([NU-020]) *shall* succeed exactly when its arcs and output specification pass the build-time checks and the timing it is given, if any, is valid ([TIME-001]).

**Acceptance Criteria:**
1. A transition can be constructed with all the above fields via a builder pattern.
2. All fields are accessible after construction.

**Test derivation:** Build a transition with inputs, outputs, inhibitors, reads, resets, timing, priority, and action; verify all fields match.

---

#### CORE-021: Transition Identity

**Priority:** MUST
**Kind:** F

Each transition instance, the result of one build call, has a unique identity. Two transitions built by separate build calls are never equal, even if they share the same name. A copy of a built transition (a Rust clone) is the same instance and is equal to it.

*When* two transitions are built by separate build calls, the two built transitions *shall not* be equal, even if they share the same name or were given the same definition.

Every built transition *shall* be equal to itself.

**Acceptance Criteria:**
1. Two transitions built with the same name are not equal (identity-based, not name-based).
2. A transition is equal to itself.

**Test derivation:** Build two transitions with name "Process"; verify they are not equal.

---

#### CORE-022: Transition Enablement

**Priority:** MUST
**Kind:** B

A transition is **enabled** in a marking when every input place holds at least its required count (see [IO-001]–[IO-004]), every read place is marked and no inhibitor place is marked.
For a transition with a match specification these conditions are the count-level part of enablement: its enablement check also needs a name of which every correlated input holds at least its required count of tokens ([NU-020]).

*While* an input place of a transition holds fewer tokens than its required count, the transition *shall not* fire.

*While* a read place of a transition is unmarked, the transition *shall not* fire.

*While* an inhibitor place of a transition is marked, the transition *shall not* fire.

*While* a transition that has no match specification ([NU-020]) is enabled, the transition *shall* be able to fire.

This requirement concerns transitions that build. A definition that building the transition rejects ([CORE-030], [IO-002], [IO-004], [EXEC-012], [IO-011]–[IO-014]) is not a transition of any net and is never enabled anywhere; in particular an output spec whose alternatives no write can tell apart ([IO-012]) never reaches a marking.

**Acceptance Criteria:**
1. Transition with satisfied inputs, reads present, inhibitors empty → enabled.
2. Missing input tokens → disabled.
3. Missing read tokens → disabled.
4. Inhibitor place has tokens → disabled.

**Depends on:** [IO-001], [CORE-030], [CORE-031], [CORE-032]
**Test derivation:** Systematically toggle each condition and verify enablement changes.

---

## Arc Types

#### CORE-030: Input Arc

**Priority:** MUST
**Kind:** B

An input arc connects a place to a transition.

*When* a transition fires, it *shall* consume from each of its input places that is not also one of its reset places ([CORE-034]) as many tokens as the input arc's consumption count ([IO-001]–[IO-004], [IO-007]), oldest first.

*When* a transition fires, each of its input places that is neither one of its reset places nor one of its output places *shall* end the firing holding exactly the consumption count of its input arc fewer tokens than it held before the firing.

*If* a transition declares two input arcs on the same place, **building the transition** *shall* fail with a descriptive error that names the transition and the place and suggests a single arc with `exactly(n)` / `atLeast(n)` instead. Duplicate input arcs have no coherent consumption semantics: executors, state-class graphs and the flattener would each read them differently. The transition builder is the one construction path every net, subnet body and verification input passes through, so a check there reaches all of them. "The same place" is the implementation's own `Place` equality ([CORE-002]; name-and-type in Java, name-only in TypeScript and Rust).

The executors' compile-time check stays as a backstop, with the same message. Both composition seams reconcile colliding arcs before they rebuild a transition, per the canonical merge table of [MOD-021] (channel composition at compose, fusion at build per [MOD-061]). The one binding that can still collapse two input arcs onto one place — two ports of one instance bound to the same host place — is rejected at compose with its own message ([MOD-020]).

**Acceptance Criteria:**
1. Transition with input arc consumes tokens from the place on firing.
2. Consumed tokens follow FIFO order.
3. Two input arcs declared on the same place → building the transition fails with a
   descriptive error naming the transition and the place. No net, executor, state-class
   graph or verifier ever sees such a transition. The executor compile step keeps the same
   check, and message, as a backstop.

**Implementation notes:**
- Java: `Transition.Builder.build()`; the backstop is `CompiledNet.compile`.
- TypeScript: `TransitionBuilder.build()`; the backstop is `CompiledNet.compile`.
- Rust: `TransitionBuilder::build()`, which panics like the builder's other structural
  checks; the backstop is `CompiledNet::compile`.
- Python: `TransitionBuilder.build()` raises `StructureError`, the class the compile-time check
  raised before, never a Rust panic.

This is a behaviour change: a net that declared a duplicate input arc but was only ever
verified or exported, never executed, used to build. It now fails at the transition.

**Test derivation:** Create transition with input arc; add tokens; verify tokens consumed in FIFO order. Create transition with two `one()` inputs on the same place; verify that building the transition fails and names both the transition and the place.

---

#### CORE-031: Inhibitor Arc

**Priority:** MUST
**Kind:** B

An inhibitor arc connects a place to a transition as a **negative precondition**.

*While* an inhibitor place of a transition is marked, the transition *shall not* fire.

*While* an inhibitor place of a transition is unmarked, the inhibitor arc *shall not* affect whether the transition can fire.

The inhibitor arc does not consume tokens.

**Acceptance Criteria:**
1. Inhibitor place empty → transition enablement unaffected by inhibitor.
2. Inhibitor place has tokens → transition disabled.
3. Firing a transition consumes nothing through its inhibitor arcs; another transition's input arc on the same place consumes as [CORE-030] says.

**Test derivation:** Create transition with inhibitor; verify disabled when inhibitor place has tokens, enabled when empty.

---

#### CORE-032: Read Arc

**Priority:** MUST
**Kind:** B

A read arc (test arc) connects a place to a transition as a **positive precondition**.

*While* a read place of a transition is unmarked, the transition *shall not* fire.

*While* a read place of a transition is marked, the read arc *shall not* affect whether the transition can fire or the marking its firing leaves.

*When* a transition fires, each of its read places on which it has neither an input arc nor a reset arc *shall* end the firing with its token count before the firing plus the tokens the firing deposits there.

The read arc does not consume tokens; the value of a read token is available to the action via the transition context.

A transition has no read arc on a place it has an input arc on: building such a transition fails ([EXEC-012]).

**Acceptance Criteria:**
1. Read place must have tokens for transition to be enabled.
2. Token remains in place after transition fires.
3. Action receives the read token value.

**Test derivation:** Create transition with read arc; fire transition; verify token still in place after firing.

---

#### CORE-033: Read Arc Multi-Reader

**Priority:** MUST
**Kind:** B

Multiple transitions can have read arcs to the same place. *While* a place is marked, a read arc to that place *shall not* stop its transition from firing, so all transitions with read arcs to the place can be enabled simultaneously. *When* a transition with a read arc to a marked place fires, and the transition has no input arc and no reset arc to that place, the read arc of any transition to that place *shall not* stop that transition from firing afterwards (no conflict), since read arcs do not consume tokens.

**Acceptance Criteria:**
1. Two transitions with read arcs to the same place are both enabled when the place has tokens.
2. Both can fire without conflict.

**Depends on:** [CORE-032]
**Test derivation:** Two transitions read from the same place; verify both can fire.

---

#### CORE-034: Reset Arc

**Priority:** MUST
**Kind:** B

A reset arc connects a place to a transition.

*When* a transition fires, each of its reset places *shall* lose every token it held before the firing and end the firing holding exactly the tokens the firing deposited there.

A reset arc *shall not* affect whether its transition can fire, whether the reset place is marked or not.

A reset arc *shall not* change what its transition can deposit: from every marking, the transition and the same transition without its reset arcs *shall* be able to make exactly the same deposits, so a reset arc neither adds a deposit nor removes one.

A reset arc *shall not* change the token count of any place other than its own.

**Acceptance Criteria:**
1. Transition with reset arc fires even if the reset place is empty.
2. If the reset place has tokens, all are removed on firing.
3. Reset arc does not contribute to enablement (no token requirement).
4. From the same marking, a transition with a reset arc and the same transition without it
   make the same deposits, compared per place ([CORE-036]): a reset arc on one of its output
   places neither adds an outcome nor removes one.

**Test derivation:** Fire transition with reset arc on place with 3 tokens; verify all tokens removed. Fire again with empty place; verify no error. Give `t: a → xor(b, c)` a reset arc on `b`; from a marking with 2 tokens in `b`, verify the firings of `t` deposit `{b}` or `{c}`, exactly as `t` without the reset arc does, and that `b` ends holding the deposited token alone.

---

#### CORE-035: Output Arc

**Priority:** MUST
**Kind:** B

An output arc connects a transition to a place.

*When* a transition fires, it *shall* deposit tokens only in its output places, according to its output spec (see [IO-010]–[IO-015]).

*When* a transition fires, the marking the firing leaves *shall* hold every token the firing deposited.

*When* a transition fires, every place that is neither an input place nor a reset place of the transition *shall* change by exactly the tokens the firing deposited there.

**Acceptance Criteria:**
1. After transition fires, produced tokens appear in the output place.
2. Output tokens are created with the current timestamp of the epoch clock ([TIME-015]); a
   token a `ForwardInput` forwards keeps its original `created_at` ([IO-014]).

**Test derivation:** Fire transition with output; verify token appears in output place.

---

#### CORE-036: Arc Semantics Summary

**Priority:** MUST
**Kind:** B

The five arc types have the following semantics:

| Arc Type  | Requires Token? | Consumes? | Effect                      |
|-----------|-----------------|-----------|------------------------------|
| Input     | Yes             | Yes       | Token consumed on fire       |
| Output    | No              | No        | Token produced on complete   |
| Inhibitor | No (blocks if present) | No | Disables transition          |
| Read      | Yes             | No        | Token remains; provides value|
| Reset     | No              | Yes (all) | All tokens removed on fire   |

In EARS form, for every transition:

*While* an input place of the transition holds fewer tokens than the required count of its input arc, the transition *shall not* fire.

*While* a read place of the transition is unmarked, the transition *shall not* fire.

*While* an inhibitor place of the transition is marked, the transition *shall not* fire.

*While* the transition is enabled, it *shall* be able to fire, whatever its output places and reset places hold.

*When* the transition fires, each input place that is not a reset place *shall* lose the consumption count of its input arc, and gain what the firing deposits there.

*When* the transition fires, each place that is neither an input place nor a reset place *shall* lose no tokens, and gain what the firing deposits there.

*When* the transition fires, each reset place *shall* end holding exactly what the firing deposited there.

*When* the transition fires and the firing ends with its action, on an executor with output validation enabled ([CONC-026], the default), the places in which it deposits *shall* be exactly the places of one output branch of its output spec, each receiving one or more tokens.

*When* the transition fires and the firing ends with the timeout outcome, it *shall* deposit in every place as many tokens as the timeout outcome puts there ([IO-013], [IO-014]).

Deposits are compared per place: the order in which a firing deposits its tokens is not normative, and two deposits that put the same number of tokens in every place are the same deposit.

As in [CORE-022], the transitions these sentences describe are transitions that build: a definition that building rejects is not a transition of any net and never fires.

**Acceptance Criteria:**
1. Each arc type behaves exactly as described in the table.
2. An action that writes two tokens into one place of the output branch it satisfies, and one
   token into each other place of that branch, fires; the marking receives all of them
   ([IO-015], [IO-016] AC4).
3. Two firings that deposit the same number of tokens in every place, in different orders,
   deposit the same outcome.

**Test derivation:** One test per arc type verifying semantics. `t: a → and(b, c)` whose action writes `b`, `b`, `c`: verify the firing succeeds and leaves 2 tokens in `b` and 1 in `c`. The same action writing `c`, `b`, `b`: verify the same marking.

---

#### CORE-037: Dead Arc Warning

**Priority:** SHOULD
**Kind:** F

A read, inhibitor or reset arc on place `P` is **dead** when:

- no transition has an input arc on `P`,
- no transition's output spec names `P` anywhere in its tree (every branch of every AND and XOR,
  the `Timeout` child and the `ForwardInput` target included),
- `P` is not an environment place ([ENV-001]), and
- the initial marking holds no token on `P`.

No firing ever puts a token on such a place, and a host injects tokens only into environment
places ([ENV-001]), so a dead read arc means its transition can never be enabled,
a dead inhibitor never blocks and a dead reset clears nothing. Each is legal: a read or
inhibitor on a place the initial marking seeds, or
a reset on a place a host fills through injection, is common and deliberate, which is why the
condition asks about the initial marking and the environment places, and why a dead arc is
**never an error**. But the shape is also what a stale reference looks like: an arc naming a
place that composition renamed away, or a typo, leaves an arc that silently does nothing. The
case that motivated this requirement was a host reset naming a subnet's port place after compose
had bound that port to a host place; [MOD-027] now rejects that case outright, and this warning
covers the rest.

In EARS form, for a net, its initial marking and its environment places, the dead-arc report is
the list of dead arcs an implementation reports:

The dead-arc report *shall* contain a read, inhibitor or reset arc of a transition of the net exactly when no transition has an input arc on the arc's place, no transition's output spec names that place anywhere in its tree (every `And` and `Xor` branch, the `Timeout` child and the `ForwardInput` target included), the place is not an environment place and the initial marking holds no token on it, and *shall* contain nothing else.

The dead-arc report *shall* list each dead arc once, as its own entry (two dead arcs on one place are two entries), in the order the net holds its transitions (the order they were added to the builder) and, within a transition, its read arcs, then its inhibitor arcs, then its reset arcs, each kind in the order the transition declares those arcs.

The warning text of a read, inhibitor or reset arc of a transition *shall* be `<kind> arc of '<transition>' on '<place>': no transition produces into or consumes from it and it starts empty; <effect>.` with `<kind>` the arc's kind (`read`, `inhibitor` or `reset`), `<transition>` the name of the transition that declares the arc, `<place>` the name of its place, and `<effect>` `the transition can never be enabled` for a read arc, `the arc never blocks` for an inhibitor arc and `the arc has no effect` for a reset arc.

An implementation SHOULD report every dead arc, once, where the net meets its initial marking:

- **Executors**, every backend, when the executor is constructed: one log-message event
  ([EVT-013]) per dead arc, through the same mechanism and with the same field shape as the
  unknown-place diagnostic of [CORE-072] AC4: logger `libpetri.runtime` (omitted where the
  log-message event carries no logger field), level `WARN`, transition name = the transition that
  declares the arc, message

  ```
  <kind> arc of '<transition>' on '<place>': no transition produces into or consumes from it and it starts empty; <effect>.
  ```

  with `<kind>` one of `read`, `inhibitor`, `reset` and `<effect>` respectively
  `the transition can never be enabled`, `the arc never blocks`, `the arc has no effect`.
  One message per dead arc, not per place: two dead arcs on one place are two messages. Arcs are
  reported in transition order and, within a transition, read, inhibitor, then reset.
  Like AC4 it is emitted only where events are recorded, and never changes execution.
- **The SMT verifier** ([VER-001]): one report line per dead arc, the same text prefixed with
  `WARNING: `, judged against the verification's own initial marking and environment places, e.g.

  ```
  WARNING: reset arc of 'hub_kill' on 'answer/IN': no transition produces into or consumes from it and it starts empty; the arc has no effect.
  ```

  No result field changes and no verdict depends on it.

In EARS form, for an executor or the SMT verifier that reports dead arcs, with the dead-arc report and the warning text above:

*Where* an executor reports dead arcs, the events that carry the warning text of an arc of the net (its dead-arc events) and that it emits before `ExecutionStarted` *shall* be, in report order, one `WARN` log-message event per entry of the dead-arc report for its net, its environment places and its initial marking, each carrying the name of the transition that declares the arc and the warning text of that arc.

*Where* an executor reports dead arcs, it *shall not* emit a dead-arc event as an engine diagnostic after `ExecutionStarted`.

*Where* an executor reports dead arcs, its other events and its steps *shall* be those of the same executor that does not report dead arcs, as if its dead-arc events had never been emitted.

*Where* the SMT verifier reports dead arcs, the lines of a verification's report that are `WARNING: ` followed by the warning text of an arc of the net (its dead-arc lines) *shall* be, in report order, one line per entry of the dead-arc report for the net as the caller passed it, the verification's initial marking and its environment places, each `WARNING: ` followed by the warning text of that arc.

*Where* the SMT verifier reports dead arcs, its report with the dead-arc lines and the blank line after them left out *shall* be the report of the same verifier that does not report dead arcs, and every other field of its result except the elapsed time *shall* be as it is in that verifier.

**Acceptance Criteria:**
1. A reset arc on a place no transition consumes from or produces into, that is not an
   environment place and that the initial marking leaves empty, produces exactly one `WARN`
   log-message event naming the transition and the place when an executor is constructed, and
   one `WARNING:` line in the verifier's report.
2. The same holds for a read arc (effect: the transition can never be enabled) and an inhibitor
   arc (effect: the arc never blocks).
3. No warning when the initial marking puts a token on the place, when the place is an
   environment place, when any transition has an input arc on it, or when any transition's output
   spec (any branch) contains it.
4. The warning never rejects a net and never changes execution, a verdict or a result field.

**Implementation notes:**
- Java: `BitmapNetExecutor` and `PrecompiledNetExecutor`, beside the [CORE-072] AC4 seam;
  `SmtVerifier.verify()`.
- TypeScript: both executors, beside the [CORE-072] AC4 seam; `SmtVerifier.verify()`.
- Rust: both backends, beside the [CORE-072] AC4 seam; `SmtVerifier::verify()`.
- Python: inherits the Rust executor events and report.

**Depends on:** [CORE-031], [CORE-032], [CORE-034], [CORE-072], [ENV-001], [EVT-013]
**Test derivation:** A net whose transition `kill` resets `x`, where nothing else touches `x`:
construct each executor with an empty initial marking and assert one `WARN` log-message event
naming `kill` and `x`; seed `x` with a token and assert none. Verify any property of the same net
and assert the report line. Repeat with a read arc and an inhibitor arc, and with `x` produced
by another transition's XOR branch (no warning).

---

## Net Construction

#### CORE-040: Net Builder

**Priority:** MUST
**Kind:** F

A Petri net is constructed via a builder pattern. The builder accepts places and transitions and produces an immutable net definition.

The sentences below concern a net builder used without composition ([MOD-020], [MOD-025], [MOD-027]) and without fusion sets ([MOD-060], [MOD-061]), which rewrite arcs, drop places or reject at build under their own requirements.

*When* a net is built from transitions, each added once, whose names are pairwise distinct ([TIME-010]), the net *shall* hold exactly the added transitions, in the order they were added, which is the declaration order of its transitions.

*When* a net is built, every declared place, every declared terminal place ([EXEC-042]), every place that an input, inhibitor, read or reset arc of an added transition names and every place in the `allPlaces` set of the output specification of an added transition ([IO-017]) *shall* be a place of the net.

*When* a net is built, the net *shall not* hold any other place, and *shall not* hold a place twice ([CORE-002]).

Building a net that declares no terminal place ([EXEC-042]) *shall* succeed.

Which nets that declare terminal places build, and which terminal places a built net holds, are stated by [EXEC-042].

**Acceptance Criteria:**
1. Builder can add places and transitions.
2. `build()` produces an immutable net.
3. Places referenced by transitions are auto-collected from arcs of all five kinds: input, inhibitor, read, reset and the output specification.

**Test derivation:** Build a net with transitions; verify all places from arcs are present in the net.

---

#### CORE-041: Net Immutability

**Priority:** MUST
**Kind:** B

After construction, a Petri net definition is immutable. The set of places, transitions, and their connections cannot be modified.

*When* the build call of a net builder used as [CORE-040] describes is made, the call *shall* give the net that [CORE-040] describes, or report the rejection that [EXEC-042] describes, for all the places, transitions and terminal places added to that builder before the call, including those added before an earlier build call.

*When* a net builder used as [CORE-040] describes has built a net and is used again, to add places, transitions or terminal places or to build again, the net it built *shall* keep the places, transitions and terminal places it had when it was built.

**Acceptance Criteria:**
1. No mutation methods exist on the constructed net.
2. Collections returned by the net are unmodifiable or copies.

**Depends on:** [CORE-040], [EXEC-042]
**Test derivation:** Build a net; verify no mutation API exists.

---

#### CORE-042: Action Binding Separation

**Priority:** MUST
**Kind:** F

The net's static structure (places, transitions, arcs, timing, priority) MUST be separable from the runtime behavior (actions). A `bindActions()` operation takes a structure and a mapping of transition names to actions, producing a new net with actions bound.

*When* actions are bound to a net, in either form, the new net *shall* have the name, the places and the terminal places of the original net and, for each transition of the original net, in the same order, a transition with the same name, arcs, output specification, timing and priority.

*When* actions are bound with a resolver that returns an action for a transition's name, the transition *shall* carry that action in the new net.

*When* actions are bound with a resolver that returns no action (`null`/`None`) for a transition's name, the transition *shall* carry in the new net the action it carried before.

*When* actions are bound with a mapping that maps a transition's name to an action, the transition *shall* carry that action in the new net.

*When* actions are bound with a mapping whose values are actions and that does not map a transition's name, the transition *shall* carry in the new net either the passthrough action or the action it carried before, and an implementation makes the same one of these two choices for every transition, every net and every mapping, so a transition that carried passthrough still carries passthrough.

*When* actions are bound to a net, in either form, a transition that has a match specification ([NU-020]) *shall* have the same match specification in the new net.

Binding actions to a net *shall* return a new net for every net and every resolver or mapping, and *shall* leave the original net unchanged.

**Acceptance Criteria:**
1. A net can be created with no actions (all transitions use passthrough).
2. `bindActions(mapping)` produces a new net with actions bound by transition name.
3. The original net is not modified.
4. Unbound transitions retain the passthrough action.

Binding is lazy and total: it never rejects, so a partially bound net is a legitimate intermediate
value and an action MAY be bound after instantiation ([MOD-031] AC7); the declared structure is
reconciled against the bound behaviour at compile time ([CORE-043]). **Divergence:** the map form
substitutes passthrough for every transition the map omits in Java and TypeScript (so a second call
clobbers the first's bindings) but leaves them untouched in Rust; only the resolver form, where a
`null`/`None` result defers a transition, binds in stages identically across implementations.
In Java a mapping may hold a name with a `null` value, and the map form then defers that transition
as the resolver form does; TypeScript substitutes passthrough for a `null` or `undefined` value.

The same operation exists on a subnet definition ([MOD-051]): `SubnetDef.bindActions` takes the
same argument forms, keyed by the definition's unprefixed transition names, treats unnamed
transitions exactly as the net-level form does in the same language, and returns a new definition.

**Test derivation:** Create a net with 3 transitions; bind actions for 2; verify the third still has passthrough.

---

#### CORE-043: Output-Declaring Transitions Must Produce

**Priority:** MUST
**Kind:** F

A transition that declares an output spec MUST NOT carry the built-in passthrough action
([CORE-051]) in a net submitted for execution: compiling *or verifying* such a net MUST fail.
Compilation is where structure and action are both final and is the point every executor passes
through, so one check there covers the builder default, either `bindActions` form ([CORE-042]),
binding on a subnet definition ([MOD-051]), per-instance binding ([MOD-030]) and channel merge
([MOD-021]) alike.

Such a transition can never fire usefully: passthrough produces no tokens while [IO-015] requires
every declared branch, so each firing consumes its input and the declared output never arrives.
Verification does not compensate: state-class and SMT analysis read production from the `Arc.Out`
spec, never from the bound action. The rule is unconditional: under an opt-out from per-firing
output validation the firing may succeed, but the net stays structurally incoherent.

*If* a net holds a transition that declares an output spec, a `Timeout`-only spec included, and carries the built-in passthrough action ([CORE-051]), whether bound explicitly, carried because a `bindActions` mapping omitted it ([CORE-042]), or left in place as the builder default, *then* compiling the net *shall* fail with an error that names the first such transition in declaration order.

*If* no transition of a net both declares an output spec and carries the built-in passthrough action, *then* compiling the net *shall not* fail under this requirement.

*If* a transition declares no output spec, or carries an action other than the built-in passthrough, a `fork()` action ([CORE-052]) or a hand-written action that produces nothing included, *then* compiling the net *shall not* fail under this requirement naming that transition.

*When* a net is submitted to a verification entry point (state-class graph or SMT), under any property and option the entry point accepts, the entry point *shall* fail under this requirement exactly when compiling the submitted net does, with an error that names the same transition.

**Acceptance Criteria:**
1. Compiling a net errors when a transition with a non-empty output spec carries passthrough (bound explicitly, carried because a `bindActions` mapping omitted it, or left in place as the builder default), including a `Timeout`-only spec, whose executor-produced `ForwardInput` branch ([IO-014]) passthrough can never reach.
2. The error names the offending transition, the first one in declaration order when there are several.
3. Submitting the same net to a verification entry point (state-class graph or SMT) fails the same way, so verification cannot green-light a net that will not compile.
4. A transition that declares no output spec (a sink) may carry passthrough; [CORE-042] is untouched.
5. The built-in is recognised by identity, so a hand-written action that happens to produce nothing is not claimed; that stays [IO-015]'s business at run time.

**Test derivation:** Compile a net whose transition declares `Out.place(P)` and carries the builder default, then with passthrough bound explicitly, then omitted from a `bindActions` mapping, then declaring `Out.timeout(d, Out.forwardInput(P, Q))`; verify each is rejected naming the transition, and that a sink, a `fork()`-bound transition and a hand-written no-op all compile.
Verify the same rejection at the state-class-graph and SMT entry points.

---

## Actions

#### CORE-050: Transition Action

**Priority:** MUST
**Kind:** B

A transition action is an asynchronous function that receives a transition context and produces output tokens. The action signature returns a future/promise that resolves when the action completes.

*When* a transition fires, its action *shall* receive a transition context holding the tokens the firing consumed from each input place and the tokens its read arcs read ([EXEC-010], [EXEC-012]).

*When* a firing ends with the completion of its action, the firing *shall* deposit exactly the output tokens the action completed with, whether the action wrote them through the context or returned them.

*If* the executor admits the completion of a firing's action ([EXEC-020]), the transition has no match specification ([NU-020]) and the output tokens fill one output branch ([IO-015]), *then* the firing *shall* end with that completion.

**Acceptance Criteria:**
1. Action receives a context with consumed input tokens and read token values.
2. Action produces output tokens via the context or a return value.
3. Action is asynchronous (returns future/promise/completion stage).

**Test derivation:** Create action that reads input, transforms it, and produces output; verify output tokens.

---

#### CORE-051: Passthrough Action

**Priority:** MUST
**Kind:** F

A built-in passthrough action that consumes input tokens and produces no output tokens. This is the default action for transitions without explicitly bound actions.

The built-in MUST be recognisable by identity, a stable singleton rather than a fresh closure per
call, so that [CORE-043] can reject a net pairing it with a declared output spec without claiming
a user-supplied action that happens to produce nothing.

*When* a transition fires under the built-in passthrough action, the action *shall* complete with no output token and *shall not* fail.

The identity predicate *shall* accept the built-in passthrough action and reject every other action, including `fork()` ([CORE-052]) and a hand-written action that produces no token.

*When* a transition is built without an action, the built transition *shall* carry the built-in passthrough action.

Every retrieval of the built-in passthrough action *shall* yield the same instance, which the identity predicate accepts.

**Acceptance Criteria:**
1. Passthrough action completes immediately.
2. No output tokens are produced.
3. Repeated retrieval of the built-in yields the same instance, and an identity predicate over it accepts the built-in and rejects every other action, including `fork()` ([CORE-052]).

**Test derivation:** Fire a sink transition with passthrough; verify no output tokens. Retrieve the built-in twice; verify identity.

---

#### CORE-052: Fork Action

**Priority:** SHOULD
**Kind:** F

A built-in fork action that copies a single input token value to all declared output places.

*When* the fork action runs for a transition with exactly one input place and the firing consumed exactly one token from that place, the action *shall* complete with one token carrying that token's value in every place the output spec names and with no token in any other place.

*If* the transition does not have exactly one input place, *then* the fork action *shall* fail.

*When* the firing consumed two or more tokens from the single input place, the fork action *shall* either fail or complete with one token carrying the oldest consumed token's value in every place the output spec names and with no token in any other place.

**Divergence:** when the firing consumed two or more tokens from the single input place, the fork action copies the oldest consumed token to every output place in Java, Rust and Python and fails in TypeScript.

**Note:** The fork action writes every place the output spec names, so on an output spec `Xor(a, b)` with two different places it writes both, and an executor with output validation enabled rejects its completion ([IO-015], [EXEC-021]).

**Acceptance Criteria:**
1. Requires exactly one input place.
2. Produces exactly one token carrying the input value in each output place, and no token in any other place.
3. Throws/errors if the transition does not declare exactly one input place (none, or more than one).
4. When the firing consumed two or more tokens from the single input place, either fails or produces the oldest consumed token's value as in criterion 2.

**Test derivation:** Fork action with 1 input and 3 outputs; verify all 3 receive the same value.

---

#### CORE-053: Transform Action

**Priority:** SHOULD
**Kind:** F

A built-in transform action that applies a user-provided function to the context, then copies the result to all output places.

*When* a transition fires under the transform action, the action *shall* call its function with the transition context of that firing, and *shall* complete or fail with the outcome of one such call.

*When* the function returns a value, the transform action *shall* complete with the output tokens the function wrote through the context, followed in every place the output spec names by one token carrying that value.

**Note:** The places the output spec names include every branch of an `Xor` and the child of a `Timeout`, and the transform action puts one copy in each. On an output spec with an `Xor`, that completion fills more than one branch, so output validation ([IO-015]) rejects it.

**Acceptance Criteria:**
1. Function receives the transition context.
2. Return value is produced to all output places.

**Test derivation:** Transform action doubles an integer input; verify all outputs receive the doubled value.

---

#### CORE-054: Produce Action

**Priority:** SHOULD
**Kind:** F

A built-in action that produces a fixed value to a specified output place.

*When* the built-in produce action of a place and a value runs on a transition whose output spec names that place, the action *shall* complete with exactly one output token, which carries that value and goes to that place, and with no output token in any other place.

*If* the built-in produce action of a place and a value runs on a transition whose output spec does not name that place, *then* the action *shall* fail.

**Acceptance Criteria:**
1. The specified place receives a token with the fixed value.

**Test derivation:** Produce action with value "hello" to place P; verify P receives "hello".

---

## Transition Context

#### CORE-060: Context Input Access

**Priority:** MUST
**Kind:** F

The transition context provides access to consumed input token values. Actions can retrieve single values or lists of values from declared input places.

*When* an action calls `inputs(place)` on an input place of its transition, the call *shall* return the values of the tokens the firing consumed from that place, in the order the firing consumed them ([EXEC-010]).

*When* an action calls `input(place)` on an input place from which the firing consumed exactly one token, the call *shall* return the value of that token.

*Where* the transition context gives access to tokens (Java, TypeScript), *when* an action calls `inputToken(place)` on an input place from which the firing consumed exactly one token, the call *shall* return that token, with its creation timestamp.

*If* an action calls `inputs(place)`, `input(place)` or `inputToken(place)` (where it exists) on a place that does not resolve to an input place of its transition ([MOD-031]), *then* the call *shall* report an error ([CORE-063]).

What `input(place)` and `inputToken(place)` return when the firing consumed more than one token from the place is not specified; an action reads a batch with `inputs(place)`.

**Acceptance Criteria:**
1. `input(place)` returns the single consumed value.
2. `inputs(place)` returns all consumed values (for multi-token cardinality).
3. `inputToken(place)` returns the token with metadata (including timestamp).
4. Accessing an undeclared input place results in an error.

**Depends on:** [CORE-050], [EXEC-010]
**Test derivation:** Fire transition consuming 3 tokens; verify `inputs()` returns 3 values.

---

#### CORE-061: Context Read Access

**Priority:** MUST
**Kind:** F

The transition context provides access to read (non-consumed) token values from declared read places.

*When* an action calls `read(place)` on a read place of its transition, the call *shall* return the value of the token the read arc read from that place, the oldest token the place holds ([EXEC-012]).

The call consumes nothing: by [EXEC-012] the firing leaves the read token in the place, unless the transition also has a reset arc there, which drains the place ([EXEC-013]).

*If* an action calls `read(place)` on a place that does not resolve to a read place of its transition ([MOD-031]), *then* the call *shall* report an error, also when the place is an input place of the transition.

**Acceptance Criteria:**
1. `read(place)` returns the read value without consuming it.
2. Accessing an undeclared read place results in an error.

**Depends on:** [CORE-032], [EXEC-012], [EXEC-013]
**Test derivation:** Fire transition with read arc; verify `read()` returns value; verify token still in place.

---

#### CORE-062: Context Output Access

**Priority:** MUST
**Kind:** F

The transition context provides a way for actions to declare output tokens for production, in a single-token form and a bulk-token form.

*When* an action calls `output(place, value)` on an output place of its transition, the call *shall* declare one token carrying `value` on that place, after every token the action declared before.

*When* an action calls the bulk form with a sequence of values on an output place of its transition, the call *shall* declare one token per value on that place, in the order of the sequence, after every token the action declared before.

*When* an action calls the bulk form with no values on an output place of its transition, the call *shall* declare no token and return successfully.

*If* an action calls `output(place, value)` or the bulk form on a place that does not resolve to an output place of its transition ([MOD-031]), *then* the call *shall* report an error and declare no token, also when it passes no values ([CORE-063]).

These four sentences do not govern an output call made after the firing has ended with the timeout outcome ([IO-013]); such a call declares no token that the firing deposits.

**Acceptance Criteria:**
1. `output(place, value)` declares a single token to produce on the given output place.
2. A bulk form accepting multiple values for the same output place in one call is available and produces one token per value in iteration order. Language shapes: Java varargs `output(Place<T>, T...)` plus `output(Place<T>, Iterable<? extends T>)`; TypeScript rest parameters `output<T>(place, ...values: T[])`; Rust `output_many<T>(place_name, impl IntoIterator<Item = T>)`; Python `output_many(place_name, values)` over any iterable.
3. The bulk form validates the output place exactly once and reports an error **before** appending any tokens if the place is not declared, so undeclared-place errors do not leave partial output behind.
4. An empty bulk call (zero values) on a declared output place is a no-op and returns successfully.
5. Producing to an undeclared output place results in an error.

**Depends on:** [CORE-035], [IO-013], [IO-017]
**Test derivation:** Action calls `output(place, value)`; verify token appears in place after firing. Bulk form: action calls the bulk overload with three values; verify all three tokens appear in order. Bulk-undeclared: call bulk overload with a foreign place; verify error raised and no tokens appended.

---

#### CORE-063: Context Structure Enforcement

**Priority:** MUST
**Kind:** F

The transition context enforces that actions can only access places declared in the transition's structure. Attempting to access an undeclared place (input, read, or output) results in an error.

*If* an action calls an input accessor (`inputs(place)`, `input(place)` or, where it exists, `inputToken(place)`) on a place that does not resolve to an input place of its transition ([MOD-031]), *then* the call *shall* report an error.

*If* an action calls `read(place)` on a place that does not resolve to a read place of its transition ([MOD-031]), *then* the call *shall* report an error, also when the place is an input place of the transition.

*If* an action calls `output(place, ...)`, in its single or its bulk form, on a place that does not resolve to an output place of its transition ([MOD-031]), *then* the call *shall* report an error and declare no token, also when it passes no values.

Every executor hands an action consumed tokens only from the input places of its transition ([EXEC-010]) and read tokens only from its read places ([EXEC-012]).

The plural accessors some languages add, such as `reads(place)` and Java's `inputTokens(place)`, are not named by these rules; each implementation guards them with the check of the singular accessor of the same kind.

These rules govern the calls an action makes through its transition context; a token that reaches the executor without passing through the context is the subject of [CORE-072] AC3.

**Acceptance Criteria:**
1. Accessing undeclared input → error.
2. Accessing undeclared read → error.
3. Producing to undeclared output → error.

**Depends on:** [CORE-060], [CORE-061], [CORE-062]
**Test derivation:** Create context with restricted place sets; attempt out-of-bounds access; verify errors.

---

#### CORE-064: ~~Execution Context Injection~~ (Removed)

**Status:** Removed

Host objects in the transition context (a tracing span, configuration) are a convenience of the language bindings, not part of the firing contract: not every implementation has them, and no requirement depends on them. The former text is kept as advice in [Usage guidance (non-normative)](00-index.md#usage-guidance-non-normative).

Retained as a tombstone for traceability; excluded from the active requirement count.

---

## Marking

#### CORE-070: Marking State

**Priority:** MUST
**Kind:** F

A marking represents the current distribution of tokens across all places. Internally, each place maps to a FIFO queue of tokens.

A marking *shall* hold a queue of tokens for each place of its net, oldest token first, and the token count of a place *shall* be the length of its queue.

An empty marking *shall* hold no token in any place.

*When* a token is added to a place, the marking *shall* append it at the tail of that place's queue and leave the queue of every other place unchanged.

*When* the first token of a marked place is removed, the marking *shall* return the head of that place's queue and keep the rest of that queue in order, leaving the queue of every other place unchanged.

*If* the first token of a place that is not marked is removed, *then* the marking *shall* return no token and change no queue.

*When* a token is added to or removed from a marking, the resulting marking *shall* still hold a queue for each place of its net.

**Acceptance Criteria:**
1. Empty marking has zero tokens in all places.
2. Tokens can be added and removed from specific places.
3. Token count per place is queryable.

**Test derivation:** Create empty marking; add 3 tokens to place P; verify count is 3; remove one; verify count is 2.

---

#### CORE-071: Marking Thread Safety

**Priority:** MUST
**Kind:** A

The live marking is mutated only by the orchestrator thread. It is NOT thread-safe. Transition actions must NOT directly access the marking.

An implementation MAY additionally expose a read-only observation path that returns an owned, independent copy of the marking to a non-orchestrator caller (see `marking()` used cross-thread, and [ENV-014]). Such a copy is explicitly best-effort: it is produced without blocking the orchestrator, so places may be captured at different instants and the copy carries no consistency guarantee. It MUST NOT mutate, or force synchronization onto, the live marking, and the live marking itself remains lock-free.

**Acceptance Criteria:**
1. No synchronization primitives are used in the marking implementation.
2. Token production from actions goes through the context/output mechanism, not direct marking access.
3. Any cross-thread observation returns an independent copy; it never hands out the live marking instance while the orchestrator is running.

**Test derivation:** Architectural review; verify marking has no locks/atomics; verify a cross-thread read returns a distinct instance from the live marking.

---

#### CORE-072: Initial Marking

**Priority:** MUST
**Kind:** B

An executor can be initialized with an initial marking that pre-populates places with tokens before execution begins.

*When* an executor is initialized with an initial marking, its marking *shall* hold, before execution begins, exactly the tokens the initial marking puts on each place, whether or not the net declares that place.

*When* execution begins, a transition of the net *shall* be armed exactly when its enablement check passes on the initial marking, with the firing clock's reading at that moment as its stamp, so that its elapsed time starts at 0 ([TIME-010]).

*While* a place is an unknown place, the executor *shall* retain its tokens in the marking, in their order and ahead of any token that reaches the place later, and *shall not* drop any of them.

*While* a place is an unknown place, the executor *shall not* change its tokens when the firing clock advances or when it reaps a transition ([TIME-013]).

**Acceptance Criteria:**
1. Initial marking distributes tokens to specified places.
2. Execution begins with these tokens available.
3. Tokens on places the net does not declare are **retained** in the observable
   marking (inert — no arc can reference them — but never silently dropped).
   This holds for every backend regardless of its internal token storage; the
   same retention applies to any token reaching a backend for an uncompiled
   place through production or injection seams. A transition context never
   produces to such a place, because an output call on a place the transition does
   not declare as an output reports an error ([CORE-063]); the production seam is
   reached only by a token that bypasses the context, such as the internal raw
   output collector (`rawOutput()`) of Java and TypeScript. Verification models such a place
   the same way, as a place with no arcs whose tokens stay ([VER-001]).
4. An implementation SHOULD surface the first write to an undeclared place as an
   observable diagnostic, emitted as the existing log-message event ([EVT-013]) —
   no new event type. Field shape: logger `libpetri.runtime` (omitted where the
   implementation's log-message event carries no logger field), level `WARN`,
   transition name = the producing transition's name, or `""` at the
   initial-marking and injection seams where no transition is firing; message
   `unknown place '<p>': tokens are retained in the marking but inert (the net
   declares no arc on it)`. Emitted once per distinct unknown place per executor,
   not once per token. Retention (AC3) does not depend on the diagnostic.

**Depends on:** [EVT-013]
**Test derivation:** Create executor with initial marking {P1: [a, b], P2: [c]}; verify tokens present before first firing. Include a place unknown to the net; verify its tokens appear unchanged in the final marking, and that exactly one `WARN` log-message event names that place however many tokens land on it.

---

#### CORE-073: Marking Snapshot and Restore

**Priority:** MUST
**Kind:** F

A marking can be captured as a structured snapshot that preserves, for every token, both its
value and its `created_at` timestamp, and restored as the initial marking of a new execution
(a "resume").

*When* a snapshot of a marking is restored, the restored marking *shall* hold on every place exactly the tokens the marking held there, in the same FIFO order, each token unchanged in its value and its `created_at`.

A snapshot an implementation returns to the host *shall* list its places in strictly ascending code-point order of the place name and *shall not* list a place that holds no token.

*When* a snapshot whose place names are pairwise distinct is restored, the restored marking *shall* hold on each place the snapshot names exactly the tokens of that place's entry, in their order, whatever the place name and whether or not the receiving net declares the place.

*When* a snapshot whose place names are pairwise distinct is restored, the restored marking *shall* hold no token on a place the snapshot does not name.

*If* an executor is constructed with a restored marking together with an explicit initial marking that holds a token, *then* the construction *shall* fail with an error to the caller, and the executor *shall not* merge the two markings or keep either one.

*When* an executor is constructed with a restored marking together with an explicit initial marking that names no place, the executor's initial marking *shall* be the restored marking.

*When* an executor is constructed with a restored marking together with an explicit initial marking that holds no token and the construction succeeds, the executor's initial marking *shall* be the restored marking.

*When* a restored marking seeds a new executor, each restored token *shall* keep its value and its `created_at`, whatever the executor's epoch clock ([TIME-015]).

*When* a restored marking seeds a new executor, that executor's initial marking *shall* hold on every place the token count the restored marking holds there, whether or not the net declares the place ([CORE-072]).

*When* execution resumes from a restored marking, each transition of the net that the restored marking enables *shall* be armed with the firing clock's reading at that moment as its stamp, so that its elapsed time starts at 0 whatever the `created_at` of the restored tokens ([TIME-010]).

**The snapshot form is normative, because four implementations inventing four shapes is the whole
problem this requirement exists to prevent.** A snapshot is a mapping from **place name** to an
**ordered sequence** of entries, each carrying a token's `value` and its `created_at`:

- The sequence is the place's **FIFO order** ([CORE-013]), and a restore MUST reproduce it. Token
  order decides which token a firing consumes, so a snapshot that loses it is not a restore.
- A snapshot an implementation **emits** MUST omit a place that holds no tokens, as [EVT-014] AC3
  already requires of the event. A **restore** MUST accept both forms — the place omitted, and the
  place present as an empty sequence — and MUST restore them identically, because a snapshot a
  host authored or edited may carry either. Omission is fixed on the emitting side rather than left
  open because the alternative makes a snapshot a function of *history*: a place that was drained
  and a place that never held a token are the same marking, and a form that tells them apart gives
  two equal markings two different artefacts — between languages, within one language, and even
  between two executors of one implementation that store tokens differently.
- A place name the receiving net does not declare MUST be retained rather than dropped, exactly as
  [CORE-072] requires of any initial marking, so a snapshot survives a round-trip through a net
  that has since gained or lost a place.
- An entry is the implementation's **own token representation**, not a parallel type invented for
  snapshots: a token already *is* a value plus a `created_at`, and a second type carrying the same
  two fields diverges from the language's own model rather than converging on this one. Where the
  form must cross a language boundary, the binding's rendering of that token is the entry.
- **A place name is an arbitrary string, and none of them is reserved.** An implementation MUST NOT
  drop, rename or mangle an entry because its name collides with a construct of the host language
  or of the serialization it happens to use. Names reach this form from wherever the net was built
  — in a compiled workflow they are user input — so a name that happens to match a language's
  special property, a prototype key, a reserved word or a magic method is ordinary data. Losing one
  is silent: the snapshot simply has fewer places than the marking did, with no error to notice.
  The shape to look for is narrower than "anywhere a name is used as a key": it is the
  implementation **writing** a name it did not choose into a container that reserves some — a plain
  object, an attribute set, a keyword-argument expansion. Reading through an entries-style iteration
  is safe, and a container keyed by a closed vocabulary is not at risk at all.
- The form is **structural, not serialized**. The engine MUST NOT impose a value codec and MUST NOT
  require token values to be serializable: the host owns that, because only the host knows what its
  values are. An implementation whose values are already a serializable type MAY expose a
  convenience encoder, but MUST NOT make it the only path.

**Restoring resolves names against the receiving net.** A snapshot carries place *names*, not
places, which is what lets it survive a net that gained or lost one. An implementation whose
marking is keyed by name alone can restore from the snapshot unaided. An implementation whose place
equality is structural over name *and* token type ([MOD-024]) cannot: a place synthesised from a
name has no token type to supply, so it does not compare equal to the receiving net's own place and
the restored tokens land where the executor cannot see them. Such an implementation MUST resolve
each snapshot name against the receiving net's declared places, and its restore operation therefore
takes the net — or its places — as a second input. That is a required consequence of [MOD-024], not
an API divergence to be smoothed away: a signature matched at the cost of a restore that silently
loses its tokens is the worse trade. Names the receiving net does not declare are still retained
per [CORE-072], under whatever placeholder place the implementation can construct.

For the same reason such an implementation MUST **reject** — with an error raised to the caller,
never by keeping one place and dropping the other — a snapshot or a restore over a set of places
in which two share one name: the form is keyed by name alone, so two same-named places of
different token type collapse into one entry on the way out and cannot be told apart on the way
in. The refusal belongs to the host-facing operations, and is raised where the host asked — when
it requests the snapshot, or configures the restore — not later from inside the run. The
marking-snapshot event ([EVT-014]), which the orchestrator emits on its own initiative, MUST NOT
fail a run over it. Whether such a net may be *built* at all is [MOD-024]'s question and is not
changed here.

**A restore and an initial marking are two descriptions of one thing.** Where an executor accepts
both a restored marking and an explicit initial marking, supplying a restored marking together with
an explicit initial marking that holds a token MUST be **rejected** rather than resolved. Merging them invents a state neither caller described; preferring either silently
discards the other's tokens, and the caller who supplied the discarded one has no way to find out.
Rejecting costs one error at construction and removes a class of silent loss. An explicit initial
marking that names no place describes nothing and is accepted alongside a restore; whether one that
names places but holds no token is rejected as well is left to the implementation, but one that is
accepted seeds the restored marking, since it holds no token to keep. An executor whose only
initial marking is the restored marking itself has no second input, and the rule does not apply
to it.

**Place order is not semantic, but it MUST be canonical.** The form is a *mapping*, so a restore
MUST NOT depend on the order places appear in. But a host persists a snapshot, and the moment it
does it will diff, hash or content-address the result — at which point a mapping walked in hash
order produces a different artefact on every run of the same net, for no reason a reader could
guess.

So where an implementation renders a snapshot in any ordered medium, places MUST appear in
**ascending code-point order of the place name** — the same canonical order the verification
encoders already use, and for the same reason ([VER-013]). Merely *deterministic* is not enough:
two implementations each stable in their own order still disagree, and the point of one normative
form is that a snapshot of the same marking lists the same places in the same order in every
language — so a host that serializes it with one codec gets one artefact, **byte for byte**,
whichever implementation took it. Omitting empty places on emission (above) is the other half of
that: order alone does not make two snapshots agree if one of them lists places the other leaves
out.

The trap is that a language's natural string order is usually not this order. Sorting by UTF-16
code unit — Java's `String.compareTo`, JavaScript's `<` — diverges from code-point order wherever a
character above U+FFFF meets one in U+E000–U+FFFF, so a place name outside the Basic Multilingual
Plane is enough to break the comparison. [VER-013] documents the same hazard for script output;
an implementation SHOULD reuse whatever canonical comparator it already has rather than reach for
the default.

**The rule follows the form — as far as the medium can carry an order.** It applies wherever a
marking snapshot is rendered into an ordered medium: not only to the value a host is handed, but
to a snapshot carried on an event ([EVT-014]). An implementation that canonicalises the returned
snapshot and then discards that order on the way into the event has fixed one of the two places a
host takes a snapshot from and left the other arbitrary.

It does **not** reach a JSON session archive or the JSON debug protocol. A JSON object is an
unordered collection, and at least one runtime cannot emit arbitrary keys in a chosen order at all
([EVT-025]), so a code-point-order MUST on those media would be unmeetable there without a change
of wire format and is deliberately not made. Event bodies are in any case per-language and
explicitly not byte-compatible across implementations ([EVT-025]), so cross-language byte equality
was never implied for them. What **is** required of those media is **reproducibility across runs of
the same implementation**: an archive, or a debug-protocol message, written twice from identical
run data MUST NOT differ. Watch for container types whose iteration order is randomised
*per process* rather than merely unspecified — several standard libraries provide one, and they
defeat reproducibility in a way an ordinary hash map does not, because the artefact changes on
every run rather than merely being arbitrary.

An implementation MUST NOT silently re-stamp a restored token's `created_at`. Restoring is the one
path on which the engine hands back a timestamp it did not choose, and re-stamping would make a
resume indistinguishable from a fresh start ([TIME-015]'s token-stamping boundary).

The preserved `created_at` is **token metadata** carried for fidelity (observability, archival,
timed-value inspection). It is independent of the firing clock: when a restored marking seeds a
new executor, every initially-enabled transition's timing clock starts fresh at that executor's
enablement moment, per [TIME-010] / [TIME-011]. Restoring does **not** resume a partially elapsed
firing interval — a token's `created_at` never advances or shortcuts any `Delayed`, `Window`,
`Deadline`, or `Exact` decision.

> **Note (non-normative).** `created_at` does take part in one firing decision that is not a
> timing decision: the [NU-022] tie-break orders eligible correlation names by their oldest
> token's `created_at`. Restored tokens keep the stamps of the clock that made them, while tokens
> the resumed execution produces are stamped from *its* epoch clock ([TIME-015]). A host that
> injects an epoch clock on a resumed execution should therefore seed it at or above the
> snapshot's maximum `created_at`; seeded below it, the two populations sit on unrelated time
> bases and the tie-break order between restored and fresh groups is unspecified. The remedy is
> on the clock, never on the tokens: the engine does not re-stamp (AC9), and the tie-break key
> does not change.

**The fresh clock is safe for lower bounds and unsafe for upper bounds.** Re-waiting a `Delayed`
or `Exact` lower bound after a restore still satisfies it: a bound measured again from zero is
still at least that bound. A `Deadline` or `Window` **upper** bound is not symmetric — it receives
a fresh full budget, so a deadline the net promised to enforce can be silently missed across a
restore, and a `TransitionTimedOut` ([EVT-009]) that would have fired does not. A host that needs
a hard bound to survive a restore MUST NOT express it as net timing: it belongs in the token
payload (an absolute instant the net tests against) or in an action-level timeout ([IO-013]),
which severs the output rather than restarting a clock.

**Soundness is conditional on restore being infrequent.** Every restore restarts every clock
([TIME-011]). A transition whose `Delayed(d)` clock is restarted more often than every `d` never
accumulates `d` and never fires — starvation, not slowdown. This contract is therefore sound for
restore as an *occasional* operation (a suspend boundary, a durable checkpoint, a crash-recovery
point) and unsound for a scheduler that parks and resumes a run as a matter of course. An
implementation offering restore SHOULD state this bound rather than leave it to be discovered.

**A timed proof does not cross a restore.** The state-class construction ([VER-010]) enumerates
classes reachable from the initial marking *and its initial clock valuation*. A restored marking
seeds a new execution with every clock at zero — a different initial state, not necessarily a
class of the original graph — so a timed property proved for the original run says nothing about
the resumed one. Re-verifying with the restored marking as the initial marking covers the resumed
segment exactly. An untimed proof ([VER-004]) is unaffected: it is clock-blind, and a restored
marking that came from a real run, taken at a moment with no work in flight ([ENV-014]), is
reachable by construction. That last clause does not hold for
a hand-authored marking no run produced.

**Acceptance Criteria:**
1. Snapshot → restore round-trips each token's value and `created_at` unchanged.
2. A restored marking pre-populates places exactly like any other initial marking ([CORE-072]).
3. A `Delayed` / `Window` transition enabled by restored tokens waits its full interval measured
   from the resuming executor's enablement, regardless of how old the tokens' `created_at` is.
4. A `Deadline(d)` transition enabled by restored tokens is reaped once its elapsed time, measured
   from the stamp the **resuming** executor gave it, is strictly greater than `d` plus the deadline
   tolerance ([TIME-013]), not measured from the original enablement: the original hard bound does
   not survive the restore, and no `TransitionTimedOut` is emitted for the elapsed original
   budget.
5. Restoring the same marking repeatedly at an interval shorter than `d` never fires its
   `Delayed(d)` transition, demonstrating the frequency bound above.
6. **FIFO order survives.** A place holding tokens A, B, C snapshots and restores to A, B, C, and
   the first firing that consumes one takes A.
7. **Empty and unknown places.** A place present but empty restores identically to one omitted,
   and a snapshot the implementation emits omits empty places — so a drained place and a place
   that never held a token snapshot identically, on every executor. A place name the receiving net
   does not declare is retained in the restored marking ([CORE-072]) rather than dropped.
8. **No codec is imposed.** A token whose value is not serializable by any built-in mechanism —
   a closure, a native handle, an arbitrary host object — snapshots and restores within the
   process without the engine attempting to encode it.
9. **The engine does not re-stamp.** Every restored token's `created_at` equals the value in the
   snapshot, including where the executor was given an injected epoch clock ([TIME-015]).
10. **A restored marking is visible to the executor.** Tokens restored under a snapshot name are
    the tokens the net's own transitions consume — including where place equality is structural and
    the name had to be resolved against the receiving net. Where that resolution is ambiguous
    because two of the places share one name, the snapshot and the restore are rejected to the
    caller rather than resolved in favour of either.
11. **Both is an error.** Constructing an executor with a restored marking *and* an explicit
    initial marking that holds a token is rejected, not merged and not silently resolved in favour
    of either; an explicit initial marking that names no place is accepted, and an executor
    constructed with a restore always starts from the restored marking.
12. **Canonical place order where the medium is ordered.** Snapshotting the same marking twice
    yields the same place order; a restore is unaffected by presenting the places in any other
    order; and the order is ascending code-point order of the place name, so two implementations
    snapshotting the same marking agree key for key — including for a place name above U+FFFF,
    which is where a UTF-16 sort diverges.

**Depends on:** [CORE-010], [CORE-011], [CORE-013], [CORE-072], [TIME-010], [TIME-011], [TIME-013],
[TIME-015], [ENV-014], [EVT-009], [EVT-014], [EVT-025], [IO-013], [MOD-024], [NU-022], [VER-004],
[VER-010], [VER-013]
**Implementation status:** Implemented in all four. **Java** (`Marking.snapshot()` /
`fromSnapshot(snapshot, places)`, the second argument forced by [MOD-024] structural place
equality; two same-named places are rejected by `fromSnapshot`, by the executor's `snapshot()` and
by a builder given `restore(...)`, on the caller's thread), **TypeScript** (`Marking.snapshot()` /
`fromSnapshot()`, name-only equality so it restores unaided), **Rust**
(`MarkingSnapshot = BTreeMap<Arc<str>, Vec<ErasedToken>>`, with `Clone` retained alongside as the
in-process copy it always was) and **Python** (`MarkingView.snapshot()` / `from_snapshot()`). The
entry is each language's existing token type; the key is the place name; every emitted snapshot
omits empty places, on both executors of each implementation.

**Test derivation:** Seed an executor from a restored marking whose token `created_at` is in the
distant past feeding a `Delayed(d)` transition; verify it fires ~`d` after start, not immediately
(the existing `async_delayed_timing` test already exercises an epoch-`created_at` token through a
`delayed(100)` transition).
