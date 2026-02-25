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

#### IO-006: Input Guard Predicate

**Priority:** SHOULD

An input specification may include an optional guard predicate that filters which tokens are eligible for consumption. The guard is a function from token value to boolean.

**Acceptance Criteria:**
1. Only tokens passing the guard are eligible for consumption.
2. If no tokens pass the guard, the transition is not enabled (for that input).
3. Guard is evaluated during enablement check, not during action execution.
4. Token consumption follows FIFO order among guard-passing tokens.

**Test derivation:** Input with guard `x > 10`; add tokens [5, 15, 3, 20]; verify transition consumes 15 (first matching).

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
4. Two or more branches satisfied → validation error.

**Test derivation:** Xor(P1, P2); action produces only to P1 → success. Action produces to both → error. Action produces to neither → error.

---

#### IO-013: Output Timeout

**Priority:** MUST

`Timeout(duration, child)` — if the action does not complete within the specified duration, the action is cancelled and tokens are produced to the child output specification instead.

**Acceptance Criteria:**
1. Duration must be positive (> 0).
2. Action completes within duration → normal output validation.
3. Action exceeds duration → child output receives default/sentinel tokens.
4. An ActionTimedOut event is emitted on timeout.

**Depends on:** [EVT-009]
**Test derivation:** Action sleeps 500ms; timeout at 100ms; verify timeout branch activated and event emitted.

---

#### IO-014: Output ForwardInput

**Priority:** MUST

`ForwardInput(from, to)` — used within timeout branches. When the action times out, the consumed input token value from the `from` place is forwarded (reproduced) to the `to` place. This enables retry patterns.

**Acceptance Criteria:**
1. `from` must be a declared input place of the transition (validated at build time).
2. On timeout, the original input value is produced to `to`.
3. Invalid `from` reference → build error.

**Test derivation:** Transition with input P1 and ForwardInput(P1, P2) in timeout; action times out; verify P2 receives original P1 value.

---

#### IO-015: Output Validation

**Priority:** MUST

After an action completes, the executor validates that produced tokens conform to the declared output specification:
- **And**: all children satisfied
- **Xor**: exactly one child satisfied
- **Place**: place received tokens

Validation failure is treated as a transition failure (error event emitted, tokens not restored).

**Acceptance Criteria:**
1. Conforming output → success.
2. Non-conforming output → failure event emitted.
3. Consumed input tokens are NOT restored on failure.

**Depends on:** [EVT-007]
**Test derivation:** Action produces to wrong place; verify failure event.

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
