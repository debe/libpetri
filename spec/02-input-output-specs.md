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

#### IO-010: Output One (Leaf)

**Priority:** MUST

`One(place)` — a leaf node representing a single output place that receives exactly 1 token in the formal model. Mirrors `In.One` on the input side. The action emits one or more tokens to this place at runtime; the spec asserts the structural contract that the place receives at least one token.

**Acceptance Criteria:**
1. Output spec declares a single place.
2. Produced tokens appear in the place.
3. In branch enumeration, an `One(P)` leaf contributes count = 1 to `P` in the resulting multiset (see IO-019).

**Test derivation:** Transition with `One(P)` output; action produces a token to P; verify it appears.

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
- **One**: place received tokens
- **Exactly(p, n)**: place received tokens (multiplicity is verification-only metadata; the runtime checks set-membership only — see IO-018)

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

The output specification supports static enumeration of all possible output branches for structural analysis. **Branches are multisets** (place → integer count), not sets — see IO-019 for the multiset algebra. Returns `List<Map<Place, Integer>>` (or the language-equivalent multiset representation).

- **One(P)**: Single branch with `{P → 1}`
- **Exactly(P, N)**: Single branch with `{P → N}`
- **And(...)**: Cartesian product of child branches; on key collision, **counts sum**
- **Xor(...)**: List-concatenation of child branches (one branch per alternative)
- **Timeout**: Delegates to child branches
- **ForwardInput(from, to)**: Single branch with `{to → 1}`

**Acceptance Criteria:**
1. `And(One(P1), One(P2))` → 1 branch: `{P1→1, P2→1}`
2. `Xor(One(P1), One(P2))` → 2 branches: `{P1→1}`, `{P2→1}`
3. `And(One(P), One(P), One(P))` → 1 branch: `{P→3}` (counts sum on collision)
4. `And(Exactly(P, 2), One(P))` → 1 branch: `{P→3}`
5. `Xor(And(One(P1), One(P2)), Exactly(P3, 5))` → 2 branches: `{P1→1, P2→1}`, `{P3→5}`

**Test derivation:** Enumerate branches for nested structures; verify correct multisets.

---

#### IO-017: allPlaces Flattening

**Priority:** MUST

The output specification provides a method to collect all leaf places from the entire tree, regardless of And/Xor/Timeout structure. Returns a `Set<Place>` (no multiplicity — for multiplicity-aware enumeration, see IO-016).

**Acceptance Criteria:**
1. `Xor(And(One(P1), One(P2)), Timeout(5s, One(P3)))` → `{P1, P2, P3}`
2. `Exactly(P, 5)` contributes `{P}` to the set (count is irrelevant for `allPlaces`).
3. `ForwardInput(from, to)` contributes `to` to the set.

**Test derivation:** Nested output spec; verify `allPlaces` returns complete set.

---

#### IO-018: Output Exactly (Leaf)

**Priority:** MUST

`Exactly(place, n)` — a leaf node representing a single output place that receives exactly N tokens in the formal model, where N >= 1. Mirrors `In.Exactly` on the input side. Multiplicity is **verification-only metadata**: the runtime continues to use set-membership for structural validation (the action determines actual token production via `TokenOutput.add()` calls).

**Acceptance Criteria:**
1. Construction with `n < 1` is rejected (error or panic).
2. In branch enumeration, `Exactly(P, N)` contributes count = N to P in the resulting multiset (see IO-019).
3. The runtime validator treats `Exactly(P, N)` identically to `One(P)` — checks that P received at least one token, not that it received exactly N.
4. `allPlaces` includes the place (without multiplicity).

**Depends on:** [IO-010, IO-016, IO-019]
**Test derivation:**
- `Exactly(P, 3).enumerateBranches()` → `[{P→3}]`.
- Construction with `n = 0` or `n = -1` raises an error.
- Net with `Exactly(P, 5)` produces `postVector[idx(P)] == 5` in the flat-net encoding.
- SMT verification: net firing transition `T` with `Exactly(P, 3)` proves `placeBound(P, 2)` is violated and `placeBound(P, 3)` holds.

---

#### IO-019: Multiset Branch Algebra

**Priority:** MUST

Branch enumeration (IO-016) treats output branches as multisets `Map<Place, Integer>` rather than sets. The algebra is:

- **Leaf `One(P)`** contributes `{P → 1}`.
- **Leaf `Exactly(P, N)`** contributes `{P → N}`.
- **Leaf `ForwardInput(from, to)`** contributes `{to → 1}`.
- **Composer `And(c1, c2, ...)`** is the Cartesian product of children's branch lists. When merging two branches into one (cross-product step), **counts sum on shared keys**:
  - `merge({P→2, Q→1}, {P→3, R→1})` = `{P→5, Q→1, R→1}`
- **Composer `Xor(c1, c2, ...)`** is the list-concatenation of children's branches. Each child's branches appear independently in the result list, indexed by branch position.
- **Composer `Timeout(d, child)`** delegates: `enumerateBranches(Timeout(d, c)) = enumerateBranches(c)`.

**Acceptance Criteria:**
1. Leaves return single-branch lists with correct counts.
2. AND merges by addition on collision (NOT max, NOT min, NOT union-set).
3. XOR preserves branch indexing for downstream `XorBranchInfo` analysis.
4. Nested compositions follow the algebra recursively.

**Examples:**
- `And(Exactly(P, 2), Exactly(P, 3))` → `[{P→5}]` (sum on AND)
- `Xor(One(P), Exactly(P, 3))` → `[{P→1}, {P→3}]` (XOR enumerates by branch index)
- `And(Xor(One(P), One(Q)), Xor(One(P), One(R)))` → `[{P→2}, {P→1, R→1}, {P→1, Q→1}, {Q→1, R→1}]` (cross-product where matching `P` choice in both XOR branches sums)

**Test derivation:** Construct each example above and verify the multiset output matches.

---

#### IO-020: Output Cardinality Over-Approximation Idiom

**Priority:** MAY

When a transition's actual token production is **non-deterministic** (e.g., the action emits a variable number of tokens to a place depending on runtime input), users can over-approximate the production count using `Out.Exactly(N)` or repeated `One` leaves under `And`. This is sound for **monotone bounded properties** only.

**Sound use cases:**
- **Upper-bound proofs (`M[P] ≤ K`)**: model the worst-case production as `Exactly(P, N_max)`. If the property holds under maximum production, it holds under any lower production.
- **Lower-bound proofs (`M[P] ≥ K`)**: model the least-favorable production as `Exactly(P, N_min)`.

**Unsound use cases (require true non-determinism, see Phase B / future spec entries):**
- Deadlock-freedom under variable production (a deadlock may exist only at intermediate token counts).
- Mutual exclusion proofs that depend on non-monotone interactions with token counts.
- Exact reachability of specific markings.

**Acceptance Criteria:**
1. The library does NOT enforce monotonicity automatically — users are responsible for choosing a sound over-approximation.
2. The spec documents the technique with an example (e.g., reask-budget over-approximation modeled as `Exactly(REASK_BUDGET, 3)` instead of variable runtime production).

**Test derivation:** This is a documentation requirement. Demonstrate via example test that an over-approximated net proves the upper-bound property.
