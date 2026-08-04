# 02 — Input & Output Specifications

This document specifies input cardinality and composite output routing semantics.

---

## Input Cardinality

#### IO-001: Input One

**Priority:** MUST

`One(place)` — consumes exactly 1 token from the place.

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

`Exactly(place, n)` — consumes exactly N tokens from the place, where N >= 1.

- `requiredCount()` returns N
- `consumptionCount(available)` returns N (when available >= N)

**Acceptance Criteria:**
1. Construction with N < 1 is rejected (error or panic).
2. Transition enables only when place has >= N tokens.
3. Exactly N tokens consumed on firing (the N oldest, FIFO).
4. Place with N-1 tokens → transition not enabled.

**Depends on:** [CORE-030]
**Test derivation:** Exactly(5) on place with 7 tokens; verify 5 consumed, 2 remain. Verify disabled with 4 tokens.

---

#### IO-003: Input All

**Priority:** MUST

`All(place)` — drains all available tokens from the place, requiring at least 1.

- `requiredCount()` returns 1
- `consumptionCount(available)` returns `available`

**Acceptance Criteria:**
1. Transition enables when place has >= 1 token.
2. All tokens consumed on firing (place empty after).
3. Place with 0 tokens → transition not enabled.

**Depends on:** [CORE-030]
**Test derivation:** All on place with 5 tokens; verify all 5 consumed, place empty.

---

#### IO-004: Input AtLeast

**Priority:** MUST

`AtLeast(place, minimum)` — waits for at least `minimum` tokens, then drains all when enabled.

- `requiredCount()` returns `minimum`
- `consumptionCount(available)` returns `available` (consumes all when available >= minimum)

**Acceptance Criteria:**
1. Construction with minimum < 1 is rejected (error or panic).
2. Transition enables when place has >= minimum tokens.
3. All tokens consumed on firing (not just minimum).
4. Place with minimum-1 tokens → transition not enabled.

**Depends on:** [CORE-030]
**Test derivation:** AtLeast(3) on place with 7 tokens; verify all 7 consumed. Verify disabled with 2 tokens.

---

#### IO-005: Input AND-Join Semantics

**Priority:** MUST

All inputs on a transition are AND-joined: the transition enables only when ALL input specifications are simultaneously satisfied.

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

Every input cardinality variant exposes two functions:
- `requiredCount()` — the minimum number of (matching) tokens needed for enablement
- `consumptionCount(available)` — the actual number of tokens consumed during firing, given `available` tokens

`consumptionCount(available)` MUST only be called when `available >= requiredCount()`.

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

#### IO-010: Output Place (Leaf)

**Priority:** MUST

`Place(place)` — a leaf node representing a single output place. The action produces one or more tokens to this place.

**Acceptance Criteria:**
1. Output spec declares a single place.
2. Produced tokens appear in the place.

**Test derivation:** Transition with Place output; action produces token; verify it appears.

---

#### IO-011: Output And

**Priority:** MUST

`And(children)` — ALL child output specs must receive tokens. This represents a parallel fork where all branches are active.

**Acceptance Criteria:**
1. Requires at least 1 child.
2. After action completes, ALL children must have received tokens.
3. Validation failure if any child received no tokens.

**Test derivation:** And(P1, P2, P3); action produces to all three; verify success. Action produces to only P1, P2 → validation error.

---

#### IO-012: Output Xor

**Priority:** MUST

`Xor(children)` — EXACTLY ONE child receives tokens. This represents a decision point where the action chooses one branch.

**Acceptance Criteria:**
1. Requires at least 2 children.
2. After action completes, exactly 1 child must have received tokens.
3. Zero branches satisfied → validation error.
4. Two or more branches satisfied → validation error, unless exactly one of them subsumes all the others, in which case that branch is selected (the subsumption tie-break of [IO-015]).

**Depends on:** [IO-015]
**Test derivation:** Xor(P1, P2); action produces only to P1 → success. Action produces to both → error. Action produces to neither → error.

---

#### IO-013: Output Timeout

**Priority:** MUST

`Timeout(duration, child)` — if the action does not complete within the specified duration, the firing is abandoned and tokens are produced to the child output specification instead of the action's own output.

Whether the abandoned action is actually stopped is implementation-defined and MUST NOT be relied upon. An implementation that cannot cancel the work (for example one that does not own the thread an action runs on) leaves it running to completion; its side effects still happen and only its output is excluded. "Cancellation" is therefore a capability, not a guarantee.

**Acceptance Criteria:**
1. Duration must be positive (> 0).
2. Action completes within duration → normal output validation.
3. Action exceeds duration → child output receives default/sentinel tokens.
4. An ActionTimedOut event is emitted on timeout.
5. Output the action produced *before* the budget expired is discarded together with the firing: the marking receives the timeout child's tokens and nothing else. In particular a partial write under an `Xor` sibling of the `Timeout` MUST NOT be validated as a second satisfied branch ([EXEC-021], [IO-012]).
6. A `TimeoutException` the action itself raises is an ordinary action failure ([EXEC-030]), not the declared timeout branch: the branch is taken only when the executor's own budget timer fires.

**Depends on:** [EVT-009]
**Test derivation:** Action sleeps 500ms; timeout at 100ms; verify timeout branch activated and event emitted.

---

#### IO-014: Output ForwardInput

**Priority:** MUST

`ForwardInput(from, to)` — used within timeout branches. When the action times out,
**every** token the firing consumed from the `from` place is forwarded (reproduced) to
the `to` place: one output token per consumed token, carrying the original value, in
consumption order. This enables retry patterns without losing tokens.

Forwarding is thus multiplicity-preserving. The count is whatever the input
specification on `from` actually consumed — `consumptionCount(available)` per [IO-007],
so `One` forwards 1 token, `Exactly(n)` forwards n, and `All` / `AtLeast(m)` forward the
whole drained batch. An implementation MUST NOT forward only the first consumed token:
that silently destroys the remaining N−1 tokens on the retry path, and a firing that
consumed nothing from `from` (not possible for a declared input, but reachable through a
mis-declared spec) forwards nothing.

**Acceptance Criteria:**
1. `from` must be a declared input place of the transition (validated at build time).
2. On timeout, one token is produced to `to` for each token consumed from `from`,
   preserving both the original values and their consumption (FIFO) order.
3. Invalid `from` reference → build error.
4. `In.All` or `In.Exactly(n)` on `from` with N tokens consumed → exactly N tokens
   appear in `to`; token count is conserved across the timeout.

**Depends on:** [IO-007], [EXEC-010]
**Test derivation:** Transition with input P1 and ForwardInput(P1, P2) in timeout; action
times out; verify P2 receives the original P1 values. Repeat with `all()` and
`exactly(3)` on P1 over 3 tokens; verify P2 receives all 3 in order.

---

#### IO-015: Output Validation

**Priority:** MUST

After an action completes, the executor validates that produced tokens conform to the declared output specification. Validation walks the spec tree over the set of places that received at least one token, and each node yields the set of places its subtree *claims*:
- **Place** — satisfied iff the place received tokens; claims that place.
- **ForwardInput** — satisfied iff the `to` place received tokens; claims `to`.
- **And** — satisfied iff **all** children are satisfied; claims the union of their claims.
- **Xor** — satisfied iff **exactly one** child is satisfied; claims that child's claims. Zero satisfied children is a violation, and so is more than one — except under the subsumption tie-break below.
- **Timeout** — delegates to its child.

**Xor subsumption tie-break.** Overlapping branches are legal, so more than one branch
can be satisfied by a single conforming write. When two or more children are satisfied
and exactly one of them **subsumes** every other satisfied child — its claimed place set
is a superset of each of theirs — that most specific branch is selected and validation
succeeds. For example `Xor(And(A, B, C), And(A, B))` with A, B and C all produced selects
`And(A, B, C)`; the `And(A, B)` match is an artifact of it being a strict subset, not a
second distinct branch. If no single satisfied branch subsumes all the others (e.g. two
disjoint branches both produced), the output is genuinely ambiguous and the firing is a
violation.

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
4. `Xor` with zero satisfied branches → violation; with two disjoint satisfied branches → violation.
5. `Xor(And(A, B, C), And(A, B))` with A, B, C produced → success (the subsuming branch is selected), not a multiple-branch violation.
6. A transition declaring an output spec but bound to a hand-written action that produces nothing → validation failure on every firing (the built-in passthrough case is [CORE-043]'s, rejected before execution).
7. Where mid-action publication exists: an action that publishes to `A` then returns having also written `B`, against `And(A, B)` → success. An action that publishes to `A` then returns without writing `B` → violation, and the published `A` token remains in the marking.

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

The output specification supports static enumeration of all possible output branches for structural analysis:
- **And**: Cartesian product of child branches (single branch containing all places)
- **Xor**: Union of child branches (one branch per alternative)
- **Place**: Single branch containing the place
- **Timeout**: Delegates to child branches

**Acceptance Criteria:**
1. `And(P1, P2)` → 1 branch: {P1, P2}
2. `Xor(P1, P2)` → 2 branches: {P1}, {P2}
3. `Xor(And(P1, P2), P3)` → 2 branches: {P1, P2}, {P3}

**Test derivation:** Enumerate branches for nested structures; verify correct sets.

---

#### IO-017: allPlaces Flattening

**Priority:** MUST

The output specification provides a method to collect all leaf places from the entire tree, regardless of And/Xor/Timeout structure.

**Acceptance Criteria:**
1. `Xor(And(P1, P2), Timeout(5s, P3))` → {P1, P2, P3}
2. ForwardInput(from, to) contributes `to` to the set.

**Test derivation:** Nested output spec; verify allPlaces returns complete set.
