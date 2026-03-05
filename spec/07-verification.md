# 07 — Verification

This document specifies formal verification capabilities: SMT/IC3 safety proofs, state class graph analysis, and structural analysis.

---

## SMT Safety Verification

#### VER-001: SMT Verification Pipeline

**Priority:** SHOULD

The engine supports safety property verification using SMT solvers via the IC3/PDR (Property Directed Reachability) algorithm. The verification pipeline is:

1. **Flatten XOR** — expand XOR output branches into virtual transitions
2. **Structural pre-check** — attempt to prove properties via P-invariants alone
3. **P-invariant computation** — derive place invariants from the incidence matrix
4. **SMT encoding** — encode the Petri net as CHC (Constrained Horn Clauses)
5. **IC3 query** — invoke Z3 Spacer engine for reachability analysis
6. **Decode result** — extract verdict, counterexample, or inductive invariant

**Acceptance Criteria:**
1. Pipeline accepts a net, initial marking, and property.
2. Returns a verdict (Proven, Violated, or Unknown) with supporting evidence.

**Implementation notes:**
- Java: Full pipeline with Z3 Spacer
- TypeScript: Full pipeline with z3-solver WASM
- Rust: Not yet implemented

**Test derivation:** Simple mutual exclusion net; verify Proven verdict for mutual exclusion property.

---

#### VER-002: Safety Properties

**Priority:** SHOULD

The following safety properties can be verified:

- **DeadlockFree** — no reachable marking exists where no transition is enabled.
  Optionally, the verifier accepts **sink places**: expected terminal places where
  deadlock is permitted. The error condition becomes: (all transitions disabled) ∧
  (no sink place has a token). This models nets that naturally terminate.
- **MutualExclusion(p1, p2)** — places p1 and p2 never both have tokens simultaneously
- **PlaceBound(place, k)** — place never has more than k tokens
- **Unreachable(places)** — the given set of places is never all simultaneously non-empty

**Acceptance Criteria:**
1. Each property can be constructed and passed to the verifier.
2. Properties are verified against the net's reachable state space.

**Test derivation:** For each property type: construct net where property holds → Proven; construct net where property is violated → Violated.

---

#### VER-003: Verification Result

**Priority:** SHOULD

The verification result includes:

- **Verdict**: Proven (with proof method and optional inductive invariant), Violated (with counterexample), or Unknown (with reason)
- **P-Invariants**: Place invariants discovered during analysis
- **Counterexample trace**: Sequence of markings and transitions leading to violation
- **Statistics**: Number of places, transitions, invariants found, elapsed time

**Acceptance Criteria:**
1. Proven verdict includes the proof method.
2. Violated verdict includes a counterexample trace of markings and transitions.
3. Unknown verdict includes a reason (e.g., timeout, solver limit).

**Test derivation:** Verify a violated property; inspect counterexample trace for validity.

---

#### VER-004: Untimed Over-Approximation

**Priority:** SHOULD

SMT verification operates on untimed Petri net semantics (marking projection, integer token counts). Since timing only restricts behavior (fewer enabled states), a proof on the untimed net is sound for the timed net: if a property holds without timing constraints, it holds with them.

Guard predicates are over-approximated (assumed to always pass), which is also sound for safety properties.

**Acceptance Criteria:**
1. Verification ignores timing constraints.
2. Verification over-approximates guards.
3. A Proven verdict on the untimed net implies the property holds for all timed executions.

**Test derivation:** Net with timing constraints; verify property on untimed model; verify same property holds in timed execution.

---

#### VER-005: P-Invariant Computation

**Priority:** SHOULD

The verifier computes place invariants (P-invariants) from the net's incidence matrix. A P-invariant is a weight vector `w` such that `w · M = constant` for all reachable markings M.

P-invariants provide structural proofs that do not require state enumeration.

**Acceptance Criteria:**
1. P-invariants are computed from the incidence matrix.
2. Each invariant satisfies `sum(weights[i] * marking[i]) = constant` for all reachable markings.
3. Invariants are reported in the verification result.

**Test derivation:** Net with known invariant (e.g., token conservation); verify invariant is discovered.

---

#### VER-006: Environment Analysis Mode

**Priority:** SHOULD

The verifier supports configurable treatment of environment places during analysis:

- **AlwaysAvailable** — environment places are assumed to always have tokens (unbounded external input)
- **Bounded(k)** — environment places have at most k tokens
- **Ignore** — environment places are not modeled

**Acceptance Criteria:**
1. Each mode is selectable via the verifier configuration.
2. AlwaysAvailable allows broader reachability (more states).
3. Bounded limits the state space.

**Test derivation:** Same net with different environment modes; verify different verdicts where applicable.

---

## State Class Graph

#### VER-010: State Class Graph Analysis

**Priority:** MAY

The engine may support state class graph construction using the Berthomieu-Diaz (1991) algorithm. State classes combine a marking with a Difference Bound Matrix (DBM) representing timing constraints on enabled transitions.

**Acceptance Criteria:**
1. State class graph enumerates reachable (marking, timing zone) pairs.
2. Successor computation correctly handles transition firing and clock updates.
3. XOR outputs are expanded into virtual transitions for branch analysis.

**Implementation notes:**
- Java: Full implementation
- TypeScript: Full implementation
- Rust: Not implemented

**Test derivation:** Small timed net; construct state class graph; verify reachable classes match expected.

---

#### VER-011: DBM Zone Representation

**Priority:** MAY

Timing constraints within a state class are represented as a Difference Bound Matrix (DBM), encoding constraints of the form `θᵢ - θⱼ ≤ cᵢⱼ` where θᵢ is the firing clock of transition i.

**Acceptance Criteria:**
1. DBM encodes lower and upper bounds for each transition clock.
2. Zone emptiness is detectable (unsatisfiable constraints).
3. Successor DBM is computed correctly after transition firing.

**Implementation notes:**
- Java: Full implementation
- TypeScript: Full implementation
- Rust: Not implemented

**Test derivation:** Create DBM for 3 timed transitions; fire one; verify successor zone constraints.

---

## Structural Analysis

#### VER-020: Siphon and Trap Analysis

**Priority:** MAY

The engine may support structural analysis of siphons (sets of places that, once empty, stay empty) and traps (sets of places that, once marked, stay marked).

**Acceptance Criteria:**
1. Siphons and traps are identified from the net structure.
2. Results inform deadlock analysis (every siphon containing a marked trap ensures liveness).

**Test derivation:** Net with known siphon/trap structure; verify identification.

---

#### VER-021: XOR Branch Analysis

**Priority:** SHOULD

The verifier supports analysis of XOR output branches to identify unreachable branches via state space exploration. Each XOR branch is expanded into a virtual transition for analysis.

**Acceptance Criteria:**
1. XOR branches are expanded into separate virtual transitions.
2. Unreachable branches (those that can never fire given the net structure and initial marking) are identified.

**Depends on:** [IO-012], [IO-016]
**Test derivation:** Net with XOR output where one branch is structurally unreachable; verify identification.
