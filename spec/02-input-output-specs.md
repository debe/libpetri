# 02 — Input & Output Specifications

This document specifies input cardinality and composite output routing semantics.

---

## Input Cardinality

#### IO-001: Input One

**Priority:** MUST
**Kind:** B

`One(place)` is an input arc whose required count and consumption count are both 1.

*While* the input place of a `One` input arc is unmarked, the transition *shall not* fire.

*While* the input place of a `One` input arc is marked, the arc *shall not* affect whether the transition can fire.

*When* a transition with a `One` input arc fires, it *shall* consume exactly 1 token from the input place.

*When* a transition with a `One` input arc fires, and the input place is neither a reset place nor an output place of the transition, the input place *shall* end the firing holding exactly 1 fewer token than it held before the firing.

- `requiredCount()` returns 1
- `consumptionCount(available)` returns 1

**Acceptance Criteria:**
1. Transition enables when place has >= 1 token.
2. Exactly 1 token consumed on firing (the oldest).
3. Remaining tokens stay in place.

**Depends on:** [CORE-030]
**Test derivation:** Place with 3 tokens; fire transition with One; verify 1 consumed, 2 remain.

---

#### IO-002: Input Exactly

**Priority:** MUST
**Kind:** B

`Exactly(place, n)` is an input arc whose required count and consumption count are both N, where N >= 1.

*While* the input place of an `Exactly(n)` input arc holds fewer than N tokens, the transition *shall not* fire.

*When* a transition with an `Exactly(n)` input arc fires, it *shall* consume exactly N tokens from the input place.

*When* a transition with an `Exactly(n)` input arc fires, and the input place is neither a reset place nor an output place of the transition, the input place *shall* end the firing holding exactly N fewer tokens than it held before the firing.

- `requiredCount()` returns N
- `consumptionCount(available)` returns N (when available >= N)

**Acceptance Criteria:**
1. Construction with N < 1 is rejected (error or panic). Where the language lets the spec be
   written out without the constructor (a public enum variant, an object literal), building
   the transition rejects it.
2. Transition enables only when place has >= N tokens.
3. Exactly N tokens consumed on firing (the N oldest, FIFO).
4. Place with N-1 tokens → transition not enabled.

**Depends on:** [CORE-030]
**Test derivation:** Exactly(5) on place with 7 tokens; verify 5 consumed, 2 remain. Verify disabled with 4 tokens.

---

#### IO-003: Input All

**Priority:** MUST
**Kind:** B

`All(place)` is an input arc that drains its place: its required count is 1 and its consumption count is every token the place holds.

- `requiredCount()` returns 1
- `consumptionCount(available)` returns `available`

*While* the place of an `All` input arc of a transition is unmarked, the transition *shall not* fire.

*While* the place of an `All` input arc of a transition is marked, the `All` input arc *shall not* affect whether the transition can fire.

*When* a transition fires, it *shall* consume every token from the place of each of its `All` input arcs.

*When* a transition fires, the place of each of its `All` input arcs that is not an output place of the transition *shall* end the firing empty.

**Acceptance Criteria:**
1. Transition enables when place has >= 1 token.
2. All tokens consumed on firing (place empty after).
3. Place with 0 tokens → transition not enabled.

**Depends on:** [CORE-030]
**Test derivation:** All on place with 5 tokens; verify all 5 consumed, place empty.

---

#### IO-004: Input AtLeast

**Priority:** MUST
**Kind:** B

`AtLeast(place, minimum)` — waits for at least `minimum` tokens, then drains all when enabled.

- `requiredCount()` returns `minimum`
- `consumptionCount(available)` returns `available` (consumes all when available >= minimum)

*While* the input place of an `AtLeast(place, minimum)` input arc holds fewer than `minimum` tokens, the transition *shall not* fire.

*While* the input place of an `AtLeast(place, minimum)` input arc holds at least `minimum` tokens, the input arc *shall not* affect whether the transition can fire.

*When* a transition with an `AtLeast(place, minimum)` input arc fires, it *shall* consume every token the input place holds.

*When* a transition with an `AtLeast(place, minimum)` input arc fires, and the input place is not an output place of the transition, the input place *shall* end the firing empty.

**Acceptance Criteria:**
1. Construction with minimum < 1 is rejected (error or panic), also when building a
   transition from a spec written out without the constructor, as for [IO-002].
2. Transition enables when place has >= minimum tokens.
3. All tokens consumed on firing (not just minimum).
4. Place with minimum-1 tokens → transition not enabled.

**Depends on:** [CORE-030]
**Test derivation:** AtLeast(3) on place with 7 tokens; verify all 7 consumed. Verify disabled with 2 tokens.

---

#### IO-005: Input AND-Join Semantics

**Priority:** MUST
**Kind:** B

All inputs on a transition are AND-joined: every input arc is a precondition, and all of them must hold in the same marking.

*While* any input place of a transition holds fewer tokens than the required count of its input arc, the transition *shall not* fire.

*While* every input place of a transition holds at least the required count of its input arc, the input arcs *shall not* affect whether the transition can fire.

**Acceptance Criteria:**
1. Transition with 3 inputs enables only when all 3 places have sufficient tokens.
2. If any one input is unsatisfied, the transition is disabled.

**Test derivation:** Transition with 3 inputs; satisfy 2 of 3; verify disabled. Satisfy all 3; verify enabled.

---

#### IO-006: ~~Input Guard Predicate~~ (Removed)

**Status:** Removed

Guard predicates were removed in favor of modeling conditional token selection via multiple conflicting transitions with XOR-on-input semantics. This avoids coupling predicate evaluation to the enablement check and keeps the input specification purely structural.

**Note (ν-matching is not a guard).** The correlated join of [NU-020] is *not* a
reintroduction of guards. A guard evaluates an arbitrary boolean over a single
token's value; a [NU-020] match instead correlates the **name dimension across
places** by equality — the one decidable predicate — which is
composition-structural like cardinality, not a per-token value test. It is
therefore compatible with the structural discipline this requirement preserves.

---

#### IO-007: requiredCount and consumptionCount Contract

**Priority:** MUST
**Kind:** F

Every input cardinality variant exposes two functions:
- `requiredCount()` — the minimum number of (matching) tokens needed for enablement
- `consumptionCount(available)` — the actual number of tokens consumed during firing, given `available` tokens

The required count *shall* be 1 for `One` and `All`, `n` for `Exactly(n)` and `m` for `AtLeast(m)`.

*While* `available` is at least the required count, `consumptionCount(available)` *shall* return 1 for `One`, `n` for `Exactly(n)` and `available` for `All` and `AtLeast(m)`.

*If* `consumptionCount(available)` is called with `available` less than the required count, *then* the call *shall* fail with an error.

| Variant    | requiredCount() | consumptionCount(available) |
|------------|-----------------|------------------------------|
| One        | 1               | 1                            |
| Exactly(n) | n               | n                            |
| All        | 1               | available                    |
| AtLeast(m) | m               | available                    |

**Acceptance Criteria:**
1. Each variant returns the values shown in the table.
2. Calling consumptionCount with insufficient tokens is an error.

**Test derivation:** Verify table for each variant with various available counts.

---

## Output Composition

Building a transition runs the build-time checks of its output spec in this order and fails with the message of the first check that fails: a place named twice in one output branch ([IO-011]), more than one `Timeout` node ([IO-013]), an `Xor` node inside the child of the `Timeout` node ([IO-013]), a `ForwardInput` outside the child of a `Timeout` node ([IO-014]), a `ForwardInput` whose `from` is not an input place ([IO-014] AC3), and two distinct assignments that claim the same set of places ([IO-012]). Every construction path (builders, composition, channel merge, fusion) builds its transitions through these checks, and no executor option skips them ([CONC-026]).

#### IO-010: Output Place (Leaf)

**Priority:** MUST
**Kind:** B

`Place(place)` is a leaf node of an output spec that names a single output place.

*When* a transition whose output spec is `Place(place)` fires, it *shall* deposit one or more tokens in `place`.

*When* a transition whose output spec is `Place(place)` fires, it *shall not* deposit a token in any other place.

*When* a transition whose output spec is `Place(place)` fires, the marking the firing leaves *shall* hold in `place` the tokens the firing deposited there, in addition to the tokens `place` kept through the firing.

This requirement applies to an executor with output validation enabled, which is the default ([CONC-026]).

**Acceptance Criteria:**
1. Output spec declares a single place.
2. Produced tokens appear in the place.

**Test derivation:** Transition with Place output; action produces token; verify it appears.

---

#### IO-011: Output And

**Priority:** MUST
**Kind:** B

`And(children)` is a node of an output spec that represents a parallel fork in which all children are active. *When* a transition whose output spec is `And(children)` fires and its action completes, every child, with nested `And`s flattened, *shall* have received tokens: the produced set contains a place that the child names. The same holds for an `And` nested in the alternative that an inner `Xor` chose: the produced set *shall* equal, on the places the output spec names, one output branch of the output spec. That output branch is unique, because the output branches of a spec that builds are pairwise distinct sets ([IO-012]).

This requirement applies to an executor with output validation enabled, which is the default ([CONC-026]).

**A place at most once per branch.** Outputs are sets of places ([IO-015]), and every analysis models one token per claimed place ([IO-016]), so `And(P, P)` does not mean "two tokens into `P`". *If* a single output branch (one choice at every `Xor`, with nested `And`s flattened) names the same place twice, *then* the output spec *shall* be rejected, with

```
output spec of transition '<t>' names place '<P>' twice in one AND branch; outputs are sets (IO-015) — a weighted output is not supported, add a second place or a follow-up transition
```

**Which place the message names.** *If* the output spec names a place twice in one output branch, *then* `<P>` in the message *shall* be the place that the following walk of the spec reports first, so that every implementation names the same place:

1. A `Place(P)` node and a `ForwardInput(from, P)` node name `P`.
2. A `Timeout` node walks its child and names the places its child names.
3. An `Xor` node walks its children left to right. *If* a child reports a place, *then* the `Xor` *shall* report that place. Otherwise the `Xor` names the places its children name, each once, in the order the walk first meets them.
4. An `And` node walks its children left to right. *If* a child reports a place, *then* the `And` *shall* report that place. Otherwise, *if* a place the child names, taken in the order the walk first met them, is already named by an earlier child, *then* the `And` *shall* report the first such place. Otherwise the `And` names the places its children name, each once, in the order the walk first meets them.

The walk reports a place exactly when some output branch names a place twice, because the alternatives of an `Xor` under an `And` are chosen independently of the `And`'s other children.

The rejection happens when the spec is built if the transition's name is known there, and otherwise when the transition is built; it MUST NOT be bypassable by any construction path (builders, composition, channel merge, fusion). The same place in **different** `Xor` alternatives, such as `Xor(And(P, A), And(P, B))`, is not a duplicate. A composition that produces the duplicate by binding two output ports to one place is rejected with the more specific message of [MOD-020].

**Acceptance Criteria:**
1. Requires at least 1 child.
2. After action completes, ALL children must have received tokens.
3. Validation failure if any child received no tokens.
4. `And(P, P)`, `And(P, And(Q, P))` and `Xor(A, And(P, P))` are rejected with the message above, naming the transition and `P`. `Xor(And(P, A), And(P, B))` is accepted.
5. `And(Xor(A, B), Xor(B, A))` is rejected with the message above, naming the transition and `B`.

**Depends on:** [IO-015], [IO-016]
**Test derivation:** And(P1, P2, P3); action produces to all three; verify success. Action produces to only P1, P2 → validation error. Build a transition with `And(P, P)`, with a nested duplicate, and with the duplicate inside one `Xor` alternative; verify each is rejected with the message; build the two-alternative case and verify it is accepted. Build `And(Xor(A, B), Xor(B, A))` and verify the message names `B`, not `A`.

---

#### IO-012: Output Xor

**Priority:** MUST
**Kind:** B

`Xor(children)` is an output spec node with two or more children; it represents a decision point where the action chooses one child.

*When* a transition whose output spec is `Xor(children)` fires and the firing ends with its action, its produced set *shall* equal, on the places the output spec names, one output branch of the output spec.

*When* a transition whose output spec is `Xor(children)` fires and the firing ends with its action, its produced set *shall not* equal, on the places the output spec names, two output branches that take different children at some `Xor` node.

This requirement applies to an executor with output validation enabled, which is the default ([CONC-026]).

A firing ends with its action when it does not end with the timeout outcome ([IO-013]). Deposits are compared per place ([CORE-036]): a firing whose deposit puts in every place as many tokens as some timeout-outcome deposit of the transition from the same marking may have ended with the timeout outcome, and the two lines above do not constrain it.

**Distinct alternatives.** An *assignment* of an output spec chooses one child at each `Xor` node it reaches ([IO-015]). `Xor` nodes are told apart by their position in the spec, never by what they contain, so `Xor(P, P)` has two assignments. Two assignments are *distinct* when they choose different children at some `Xor` node that both reach. *If* two distinct assignments of a transition's output spec claim the same set of places, at any depth of the spec, *then* building the transition *shall* fail with

```
output spec of transition '<t>' is ambiguous: output branches <i> and <j> both claim {<places>}; no write can tell them apart (IO-012)
```

Every implementation runs the check the same way, so the message is identical in all of them:

1. Enumerate the output branches of the spec per [IO-016], numbered from 0 in enumeration order (the numbering of the virtual transitions `<t>_b<i>` of [VER-001]). The enumeration lists exactly one branch per assignment, so two branches at different indices come from distinct assignments.
2. Read each branch as the set of places it names, a `ForwardInput(from, to)` naming `to`. Two places are the same under the implementation's own `Place` equality, as for [IO-011] ([CORE-002], [MOD-024]).
3. Visit the branches in index order. The first branch `j` whose set equals the set of an earlier branch fails the check, and `i` is the smallest index of such an earlier branch. If no branch fails, the check passes.
4. `<places>` lists the places of branch `i` by name, separated by `, `, in the order the spec as written names them (leaves left to right).

An implementation MAY decide the check without enumerating every branch, provided it reports the same `i`, `j` and `<places>`. The check runs when the transition is built, on every construction path, as the check of [IO-011] does. A composition that binds two output ports in different alternatives to one host place yields a spec that this check rejects.

A transition that builds therefore has pairwise distinct output branches, so at most one output branch equals any produced set, and the second line above holds of every firing of such a transition.

**Acceptance Criteria:**
1. Requires at least 2 children.
2. After action completes, exactly 1 child must have received tokens.
3. Zero branches satisfied → validation error.
4. Two branches whose claims are the same set never reach a firing: building the transition rejects them (AC5). A branch whose claim is a strict subset of what was produced does not satisfy the spec at all, so overlapping branches like `Xor(And(A, B, C), And(A, B))` resolve without a tie-break ([IO-015]).
5. Building a transition fails with the message above, naming the reported pair and places, for:
   `Xor(P, P)` (branches 0 and 1, `{P}`); `Xor(And(A, B), And(B, A))` (0 and 1, `{A, B}`);
   `Xor(A, Xor(A, B))` (0 and 1, `{A}`); `And(Q, Xor(P, P))` (0 and 1, `{Q, P}`);
   `Xor(And(A, Xor(B, C)), And(A, B))` (0 and 2, `{A, B}`); `Xor(P, Timeout(d, P))` (0 and 1,
   `{P}`); and, with `a` an input place, `Xor(B, Timeout(d, ForwardInput(a, B)))` (0 and 1,
   `{B}`). `Xor(And(A, B, C), And(A, B))`, `Xor(And(P, A), And(P, B))` and
   `Xor(A, Timeout(d, B))` build.

**Depends on:** [IO-015], [IO-016]
**Test derivation:** Xor(P1, P2); action produces only to P1 → success. Action produces to both → error. Action produces to neither → error. Build a transition with each rejected spec of AC5 and verify the exact message; build each accepted spec and verify it builds. Repeat one rejected spec through composition (two output ports in different alternatives bound to one host place) and verify the same message.

---

#### IO-013: Output Timeout

**Priority:** MUST
**Kind:** B

`Timeout(duration, child)` is a node of an output spec that gives the action of a firing a budget of `duration` to complete. *If* the action does not complete within `duration`, the firing *shall* end with the timeout outcome: it is abandoned, and it deposits the tokens of `child`. *When* a firing ends with the timeout outcome, it *shall not* deposit any output of the action, so the marking receives the tokens of `child` and nothing else.

**One budget per action.** *If* an output spec holds more than one `Timeout` node, whether one is nested in the child of another or they sit apart, *then* building the transition *shall* fail with

```
output spec of transition '<t>' has <n> Timeout nodes; an output spec has at most one, nested or not (IO-013)
```

where `<n>` is the number of `Timeout` nodes in the spec. The check runs when the transition is built, on every construction path, as the check of [IO-011] does. A transition that builds therefore has at most one timeout outcome, and the `child` of its `Timeout` holds no `Timeout` node.

**One fixed timeout deposit.** The executor, not the action, makes the deposit of the timeout outcome, so nothing chooses among alternatives inside the `Timeout` child. *If* the child of an output spec's `Timeout` node holds an `Xor` node at any depth, *then* building the transition *shall* fail with

```
output spec of transition '<t>' has a Xor node inside the child of its Timeout node; the timeout outcome deposits one fixed set of places (IO-013)
```

The check runs after the `Timeout` count check above, so the spec it sees holds at most one `Timeout` node. The check runs when the transition is built, on every construction path, as the check of [IO-011] does. The timeout outcome of a transition that builds therefore deposits in one fixed set of places: every place the `Timeout` child names.

Whether the abandoned action is actually stopped is implementation-defined and MUST NOT be relied upon. An implementation that cannot cancel the work (for example one that does not own the thread an action runs on) leaves it running to completion; its side effects still happen and only its output is excluded. "Cancellation" is therefore a capability, not a guarantee.

**Acceptance Criteria:**
1. Duration must be positive (> 0).
2. Action completes within duration → normal output validation.
3. Action exceeds duration → every place the timeout child names receives tokens: one minted token for a `Place`, the forwarded tokens for a `ForwardInput` ([IO-014]).
4. An ActionTimedOut event is emitted on timeout.
5. Output the action produced *before* the budget expired is discarded together with the firing: the marking receives the tokens of the timeout child's one fixed set of places and nothing else. In particular a partial write under an `Xor` sibling of the `Timeout` MUST NOT be validated as a second satisfied branch ([EXEC-021], [IO-012]).
6. A `TimeoutException` the action itself raises is an ordinary action failure ([EXEC-030]), not the declared timeout branch: the branch is taken only when the executor's own budget timer fires.
7. `Timeout(d, Timeout(e, P))`, `Xor(Timeout(d, A), Timeout(e, B))` and
   `And(Timeout(d, A), Xor(B, Timeout(e, C)))` are rejected when the transition is built, with
   the message above and `<n>` = 2. `Xor(A, Timeout(d, B))` and `Timeout(d, And(A, B))` build.
8. `Timeout(d, Xor(A, B))` and `Xor(C, Timeout(d, And(A, Xor(B, D))))` are rejected when the
   transition is built, with the `Xor` message above. `Xor(A, Timeout(d, B))` and, with `i` an
   input place, `Timeout(d, And(A, ForwardInput(i, B)))` build.

**Depends on:** [EVT-009]
**Test derivation:** Action sleeps 500ms; timeout at 100ms; verify timeout branch activated and event emitted. Build a transition with each rejected spec of AC7 and AC8 and verify the exact message; build each accepted spec and verify it builds.

---

#### IO-014: Output ForwardInput

**Priority:** MUST
**Kind:** B

`ForwardInput(from, to)` is a node of an output spec that, on the timeout outcome, deposits in `to` the tokens a firing consumed from its input place `from`.

*If* a `ForwardInput` node of an output spec is not inside the child of a `Timeout` node, *then* building the transition *shall* fail with

```
output spec of transition '<t>' uses ForwardInput('<from>', '<to>') outside the child of a Timeout node; a forward deposits only on the timeout outcome (IO-014)
```

naming the first such node in the order the spec is written (pre-order, children left to right). The check runs when the transition is built, on every construction path, as the check of [IO-011] does.

*When* a firing ends with the timeout outcome, every `ForwardInput(from, to)` in the `Timeout` child *shall* deposit in `to` one token for each token the firing consumed from `from`, carrying the token's value, in consumption order.

The count *shall* be the consumption count of the input arc on `from` ([IO-007]): 1 for `One`, `n` for `Exactly(n)`, and the whole drained batch for `All` and `AtLeast(m)`.

*If* a firing consumed more than one token from `from`, *then* the forward *shall not* deposit fewer tokens in `to` than the firing consumed; in particular it *shall not* forward only the first consumed token. Forwarding only the first would silently destroy the remaining consumed tokens on the retry path.

*If* a firing consumed no token from `from`, which a declared input cannot do but a mis-declared spec can, *then* the forward *shall* deposit no token in `to`.

Forwarding is thus multiplicity-preserving, which enables retry patterns without losing tokens.

**What a forwarded token carries.** *When* a `ForwardInput` forwards a consumed token, the token it deposits in `to` *shall* carry the consumed token's `created_at` as well as its value. `ForwardInput` exists so a retry does not lose tokens, and a token's creation time is part of what it keeps: it is provenance across exactly the path a net takes when something went wrong, and the [NU-022] tie-break orders correlation names by it. Forwarding is therefore the one exception to [TIME-015]'s token-stamping rule: a forwarded token is the consumed token itself, not a token the executor mints, so it does not take the injected epoch clock. A *minted* recovery token, such as the unit token of a bare `Place` child, does.

**Acceptance Criteria:**
1. `from` must be a declared input place of the transition (validated at build time).
2. On timeout, one token is produced to `to` for each token consumed from `from`,
   preserving both the original values and their consumption (FIFO) order.
3. Invalid `from` reference → build error.
4. `In.All` or `In.Exactly(n)` on `from` with N tokens consumed → exactly N tokens
   appear in `to`; token count is conserved across the timeout.
5. A forwarded token's `created_at` equals the original's and is **not** re-stamped from the
   epoch clock, while a minted recovery token in the same branch *is*, in every implementation.
6. **Analysis deposits what the executor deposits.** Every analysis that expands output
   branches ([IO-016], [VER-001]) models a timeout forward with the count of AC2: a
   `ForwardInput(from, to)` whose `from` input is `One` or `Exactly(n)` deposits `1` or `n`
   tokens in `to` on the timeout outcome, not one. On `t: exactly(2, a) → xor(c, timeout(50,
   forwardInput(a, b)))` from `{a: 2}`, `PlaceBound(b, 1)` is `Violated` on every route. A
   forward from an `All` / `AtLeast` input deposits the drained batch, a marking-dependent
   count, a transfer: the graph routes, which fire each marking, count it exactly and decide
   the net, while the routes that read the flat net, which no post vector can hold it in,
   refuse it ([VER-001] AC5).

7. A `ForwardInput` outside the child of a `Timeout` node is rejected when the transition is
   built, with the message above: `ForwardInput(a, b)` as the whole spec,
   `Xor(c, ForwardInput(a, b))` and `And(c, Xor(e, ForwardInput(a, b)))`.
   `Timeout(d, ForwardInput(a, b))` and `Xor(c, Timeout(d, And(e, ForwardInput(a, b))))` build.

**Implementation status:** every implementation forwards the consumed token itself and keeps its
`created_at`, with a test pinning the asymmetry against a minted sibling under an injected clock
(Java `AbstractInjectableClockTest`, TypeScript `injectable-clock.test.ts`, Rust
`time015_injectable_clock`, which Python inherits).
**Depends on:** [IO-007], [IO-013], [EXEC-010], [TIME-015]
**Test derivation:** Transition with input P1 and ForwardInput(P1, P2) in timeout; action
times out; verify P2 receives the original P1 values. Repeat with `all()` and
`exactly(3)` on P1 over 3 tokens; verify P2 receives all 3 in order. Under an injected clock,
seed P1 with tokens stamped before the run, time the action out, and verify in every language
that the P2 tokens carry the seed stamps while a sibling `Place` recovery token carries the
clock's. The AC6 net verified at enumeration budgets 0 and the default: `Violated`, with a
one-step trace ending at `{b: 2}`. Build a transition with each rejected spec of AC7 and verify
the exact message; build each accepted spec and verify it builds.

---

#### IO-015: Output Validation

**Priority:** MUST
**Kind:** F

*When* an action completes, an executor with output validation enabled, which is the default
([CONC-026]), *shall* validate its produced set against the transition's output spec. The **produced set** is the places that received at least one
token.

Validation is an **exact-explanation search**. An *assignment* selects exactly one child
at each `Xor` node it reaches; nodes beneath an unselected `Xor` child are never
evaluated. Each assignment *claims* a set of places:

- **Place** — claims that place.
- **ForwardInput** — claims `to`.
- **And** — claims the union of every child's claim. `And` is an **unordered** conjunction:
  its children are a set of obligations, not a sequence, and a verdict MUST NOT depend on
  the order they are declared in.
- **Xor** — claims the selected child's claim.
- **Timeout** — claims its child's claim.

*If* exactly one assignment claims a set *equal* to the produced set, *then* validation
*shall* succeed. *If* no assignment claims a set equal to the produced set, *then*
validation *shall* fail, because nothing explains what was written. *If* two or more
assignments claim a set equal to the produced set, *then* validation *shall* fail, because
the write is genuinely ambiguous. For a transition that builds, no two assignments claim the
same set ([IO-012]), so on a firing this third case does not arise.

The comparison is over **sets of places**: a spec names places, not counts, so an action
that deposits several tokens into one claimed place conforms. Every analysis that enumerates
branches models one token per claimed place ([IO-016]), so such a firing does more than the
analyses explore; the executor reports it ([IO-016] AC4) rather than reject it.

Equality rather than containment is what makes a token written to a declared place
*outside* the selected branch a violation, instead of being silently deposited.

No subsumption rule is needed: `Xor(And(A, B, C), And(A, B))` with A, B and C produced has
exactly one *exact* assignment, because `And(A, B)` claims only `{A, B}`.

*Implementation note (non-normative).* This check runs on every firing of an executor with
output validation enabled ([CONC-026]). A partial claim
that already contains a place outside the produced set can never extend to an exact match,
so pruning there keeps the search linear whenever `Xor` branches are distinguishable by
what was produced; the search need not continue once two exact assignments are found. The
exponential worst case requires several `Xor` children to be simultaneously consistent with
the produced set, which is the ambiguous case that [IO-012] rejects when the transition is built.

Validation failure is treated as a transition failure (error event emitted, tokens not restored).

The *built-in* passthrough ([CORE-051]) never reaches this check: a net pairing it with a
declared output spec is rejected earlier ([CORE-043]). What remains here is the case no
static check can decide — a hand-written action that produces nothing, or produces only on
some paths — which is validated per firing.

**Mid-action publication.** An implementation MAY offer a streaming primitive that
publishes buffered output before the action returns (Rust and Python expose
`ctx.flush()`; Java and TypeScript have no equivalent). Such a primitive is an explicit
atomicity boundary and interacts with this requirement in two ways, both of which an
implementation offering it MUST honour:

1. Places written by a published batch **count towards satisfying the spec**. They left
   the completion's output set, but they were produced, so omitting them would reject
   conforming firings.
2. Published tokens are **already in the marking** and are NOT withdrawn when validation
   later rejects the firing. A violating firing therefore deposits nothing *further*, but
   it does not roll back what was already published — the same guarantee the primitive
   gives for an action that fails outright.

An action that needs all-or-nothing output must not publish mid-action.

**Acceptance Criteria:**
1. Conforming output → success.
2. Non-conforming output → failure event emitted.
3. Consumed input tokens are NOT restored on failure.
4. Zero exact assignments → violation; two or more exact assignments → violation.
5. `Xor(And(A, B, C), And(A, B))` with A, B, C produced → success, because exactly one
   assignment claims exactly `{A, B, C}`. No subsumption rule is involved.
6. A transition declaring an output spec but bound to a hand-written action that produces nothing → validation failure on every firing (the built-in passthrough case is [CORE-043]'s, rejected before execution).
7. Where mid-action publication exists: an action that publishes to `A` then returns having also written `B`, against `And(A, B)` → success. An action that publishes to `A` then returns without writing `B` → violation, and the published `A` token remains in the marking.
8. **`And` is unordered.** Permuting the children of any `And` yields the same verdict for
   the same produced set. In particular `And(A, Xor(D, E))` and `And(Xor(D, E), A)` agree on
   every produced set, including the empty one.
9. **A write outside the selected branch is a violation.** `Xor(And(A, C), B)` with B and C
   produced → violation: no assignment claims exactly `{B, C}`. It is not a success that
   silently deposits C.
10. **An inner `Xor` never pre-empts an outer one.** `Xor(And(A, Xor(D, E)), A)` with only A
    produced → success, selecting the second branch, whose claim is exactly `{A}`.

**Depends on:** [EVT-007], [CORE-051], [CORE-043]
**Test derivation:** Action produces to wrong place; verify failure event. Nested `Xor`
of overlapping `And`s where the wider branch is fully written; verify success. Bind a
hand-written no-op to a transition declaring `Out.place(P)`; verify a failure event
rather than a compile error. Where mid-action publication exists, flush one half of an
`And` and return without the other; verify both the violation event and that the flushed
token survives.

---

#### IO-016: Branch Enumeration

**Priority:** SHOULD
**Kind:** F

The output spec supports static enumeration of all its output branches for structural analysis, its *branch enumeration*.

The branch enumeration of a `Place` node *shall* be one output branch, holding that place.

The branch enumeration of a `ForwardInput(from, to)` node *shall* be one output branch, holding `to`.

The branch enumeration of an `And` node *shall* be the Cartesian product of its children's branch enumerations: one output branch for each choice of one output branch per child, holding the union of the chosen output branches, with the first child's choice varying slowest.

The branch enumeration of an `Xor` node *shall* be the union of its children's branch enumerations: one output branch for each output branch of each child, the first child's output branches first.

The branch enumeration of a `Timeout` node *shall* be its child's branch enumeration.

The enumeration lists one output branch per assignment ([IO-015]). On a spec that builds, the
output branches are pairwise distinct sets ([IO-012]), so no two entries of the list name the
same places.

A branch is a **set** of places: it says which places receive a token when the branch is
taken, not how many tokens each receives. Every analysis built on the enumeration — the
state-class graph's virtual transitions ([VER-010]), the flattener's post vectors behind
the SMT encoding ([VER-001]), the ν fragment check ([NU-051]) — deposits **one** token per
place of a branch the action writes. An action that writes `n > 1` tokens to a place its
branch names once conforms to [IO-015] (which reads the produced set) but is outside what
those analyses explore, in the direction that can make a `proven` false. A net meant to be
verified expresses multiplicity in its topology, and the executor makes the gap visible:
see AC4.

The branches describe what an **action** writes. A firing whose `Timeout` fires ([IO-013])
deposits differently: only the timeout child's places (AC5 of [IO-013]), and one token in a
`ForwardInput`'s `to` per token consumed from its `from` ([IO-014]). The analyses therefore
expand a transition into its branches, in the order above, followed by the **timeout
outcome** when it differs, place by place, from every branch ([VER-001]). On a spec whose timeout child has
no sibling in its branch and forwards at most one token, the list is the branches alone.

**Acceptance Criteria:**
1. `And(P1, P2)` → 1 branch: {P1, P2}
2. `Xor(P1, P2)` → 2 branches: {P1}, {P2}
3. `Xor(And(P1, P2), P3)` → 2 branches: {P1, P2}, {P3}
4. When a validated firing deposited more than one token into a place its matched branch
   names, the executor emits an [EVT-013] log-message event with logger `libpetri.runtime`,
   level `WARN`, the transition's name, and the message
   `'<t>': wrote more than one token to a place its output spec names once (<place>: <n>, …); branch-enumerating analyses model one token per named place, so this firing exceeds what they explore (IO-016)`,
   naming every such place with its count in produced order. The tokens are deposited
   regardless. The event is emitted at most once per transition per execution, so an action
   that fans out on every firing does not flood the store.

**Test derivation:** Enumerate branches for nested structures; verify correct sets. An action
that writes two tokens to the one place its spec names, fired three times: both tokens land
on every firing and exactly one warning is emitted; a spec `And(A, B)` with three tokens to
`A` and two to `B`: one warning naming `(A: 3, B: 2)`; one token per named place: no event.

---

#### IO-017: allPlaces Flattening

**Priority:** MUST

The output specification provides a method to collect all leaf places from the entire tree, regardless of And/Xor/Timeout structure.

**Acceptance Criteria:**
1. `Xor(And(P1, P2), Timeout(5s, P3))` → {P1, P2, P3}
2. ForwardInput(from, to) contributes `to` to the set.

**Test derivation:** Nested output spec; verify allPlaces returns complete set.
