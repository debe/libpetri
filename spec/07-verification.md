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
- All implementations: full pipeline; the CHC system is emitted as SMT-LIB2 text and solved by
  the `z3` executable with `fp.engine=spacer` through the one solver transport of [VER-013].
- Rust: behind the `z3` feature. Python exposes the Rust pipeline via the PyO3 binding (wheel
  built with the `z3` feature).

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

The encoding is additionally **value-blind**: it carries token counts, not token values. Every value-dependent choice — which XOR branch an action writes to, which token a correlated input picks — is therefore over-approximated as freely available, which is also sound for safety properties. (There is no value-predicate construct left to approximate: guards were removed in [IO-006].)

**ν-net carve-out.** The over-approximation is relaxed for the one *decidable*
predicate. A matched transition's name equality ([NU-020]) MAY be encoded
**exactly** as equality over an uninterpreted name sort (EUF) while token counts
stay in linear integer arithmetic — see [NU-050]. This removes spurious
counterexamples that would require two distinct correlation names to be equal,
without sacrificing soundness, and is the one place the untimed encoder reasons
about token *identity* rather than only token *counts*.

**Acceptance Criteria:**
1. Verification ignores timing constraints.
2. Verification is value-blind — value-dependent branch and correlation choices are
   over-approximated (except the [NU-020] name-equality carve-out of [NU-050], when
   implemented).
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
- **Bounded(k)** — environment places have at most k tokens per firing
- **Ignore** — environment places are not modeled

In `AlwaysAvailable` and `Bounded(k)` the verifier MUST **model external injection**: a
transition gated on an environment place becomes reachable (the SMT encoding emits an
injection rule that produces tokens into each environment place; under `Bounded(k)` injection
is capped). Equivalently, the environment place is treated as an inexhaustible (or k-capped)
external source rather than a column that starts empty and can only be consumed. Conservation
laws (P-invariants) derived from the closed net MUST NOT be applied to injected environment
places, since injection breaks closed-net conservation.

Because `Ignore` does not model injection, a safety property that holds **only** because
environment-gated transitions never fire is vacuous. When environment places are registered and
the mode does not model injection (`Ignore`), the verifier MUST NOT return `Proven` for such a
property — it reports `Unknown` (with a reason) instead of silently certifying.

This binds **every route that can return `Proven`**, not only the SMT encoding. An
implementation that decides some properties structurally — the name-partition state-class graph
of [NU-050], say — reaches a verdict without ever building an encoding, and a structural
exploration under `Ignore` treats an environment place as an ordinary place that simply starts
empty. The bound it certifies then holds for exactly the reason this requirement rejects. Only
`Proven` is refused: a `Violated` under `Ignore` is a real counterexample in a strictly smaller
reachable set, so it is a fortiori a counterexample in the injected one.

**Acceptance Criteria:**
1. Each mode is selectable via the verifier configuration.
2. `AlwaysAvailable` allows broader reachability (more states): for a net `env IN → T → OUT`,
   `PlaceBound(OUT, k)` is `Violated` for every finite k (OUT is reachable and unbounded).
3. `Bounded(k)` limits the state space: a transition requiring more than k tokens from an
   environment place per firing is never enabled.
4. `Ignore` with registered environment places never returns `Proven` (reports `Unknown`).
5. AC4 holds on every route the implementation offers, including any structural or state-class
   route that returns a verdict without invoking the solver.

**Test derivation:** Same net (`env IN → T → OUT`) with different environment modes; verify
`AlwaysAvailable` → `Violated`, `Bounded(k)` gates by per-firing multiplicity, `Ignore` → `Unknown`.
For AC5, a ν-net with an environment place and no declared budget place (which routes to the
state-class graph rather than the solver) under `Ignore`: a bound that is unreachable only because
injection was not modelled reports `Unknown`, not `Proven`.

---

#### VER-007: Invariant Strengthening from P-Semiflows

**Priority:** SHOULD

The verifier's encoders conjoin every accepted conservation law `y·M = y·M0` into the
transition-rule bodies of the CHC/IC3 encoding ([VER-004], [VER-005]). A law is accepted only
by the **exact gate**: `y·C = 0` against the incidence matrix and `y·M0 = c` are re-checked in
exact (overflow-checked) integer arithmetic, and `y` MUST carry zero weight on every place a
transition consumes with `all()` / `atLeast(n)` or clears with a reset arc, because the
encoder's fire relation is not linear there (Lean `Strengthening.lean`, hypotheses H1/H2;
injected environment places are covered by [VER-006], H3'). A law that fails the gate is
dropped from the encoding and listed in the report.

Two sources feed the gate. The null-space basis of [VER-005] is one basis of many: Gaussian
elimination returns mixed-sign rows (discarded as not semi-positive) and rows that fold a reset
place into a chain whose other combinations avoid it (dropped by the gate). On a net with a
handful of reset arcs this can lose every law of the chains those arcs touch, and IC3 then has
to rediscover each conservation law itself, which on a net of a hundred places it does not do
within any practical budget. The non-negative **P-semiflows** (`y ≥ 0`, `y·C = 0`, the minimal
laws of the net, computed by the Farkas / Colom-Silva enumeration that [NU-053] already uses
for the colour-slot bound) are the missing laws.

An implementation SHOULD therefore offer an option that unions the gate-validated semiflows
into the invariant list the encoders receive. The option is **off by default** so that reports
stay byte-identical across releases. It is pure strengthening (Lean `Semiflow.lean`,
`semiflow_union_sound`: conjoining any list of gate-validated laws preserves the abstract
reachable set), so enabling it can never turn a `Violated` into a `Proven`.

"The encoders" is both of them. The strengthened list reaches the **name-coloured** encoder of
[NU-050] exactly as it reaches the flat one — a coloured place's term becomes the sum over its
colour slots, its aggregate count, so one law stays one equation — and the option is at its most
decisive there: a coloured query already carries the
colour layer's cost, so the laws IC3 would otherwise have to rediscover are the ones it can
least afford to. The trigger is worth stating plainly, because it is the common shape rather
than an exotic one: **a net with even one `all()` / `atLeast(n)` or reset arc on a busy place
loses every basis row whose support touches that place**, so the encoder runs on a deficient
invariant set with nothing in the report to say a law is missing beyond the `Dropped` lines.
Draining an input queue is the everyday case. The option does not rescue those rows — semiflows
face the same gate and a law whose support touches the place is dropped either way. It supplies
the *other* laws: the minimal ones that avoid the place entirely, which elimination had folded
away.

**Acceptance Criteria:**
1. Semiflows are re-validated by the same exact gate as the basis rows before use; a semiflow
   that fails it is dropped with a `Dropped semiflow:` report line and is never encoded.
2. With the option disabled (the default) the semiflows do not reach the encoders and the
   report is byte-identical to a build without the feature.
3. With the option enabled the report carries `  Semiflows encoded as invariants: N`, where
   `N` counts the semiflows added after deduplication against the basis rows, and the result's
   invariant count and list include them.
4. `Proven` is never weakened: where the certificate check applies (the flat encoding) it
   receives the strengthened list and re-proves every law's initiation and consecution against
   the unstrengthened step relation before the verdict is reported.
5. A genuine violation stays `Violated` with the option enabled.
6. The strengthened list reaches the name-coloured encoder ([NU-050]) as well as the flat one:
   there is a net on the coloured path whose encoded script differs between the option's two
   states. (Not every such net — a semiflow already present in the basis dedups away, and AC3
   admits `N = 0`, in which case the two scripts are identical.) This is about what the encoder
   receives, not about certification — AC4's certificate check is flat-path only, and a coloured
   `Proven` reports `  Certificate check: not applicable (name-coloured encoding)`.

**Implementation notes:**
- Java: `SmtVerifier.semiflowInvariants(boolean)`.
- TypeScript: `SmtVerifier.semiflowInvariants(enabled)`.
- Rust: `SmtVerifier::semiflow_invariants(bool)`.
- Python: `verify(..., semiflow_invariants=True)`.

**Depends on:** [VER-004], [VER-005], [VER-006], [NU-050], [NU-053]

**Test derivation:** a budgeted work loop with one reset arc on a side place, whose null-space
basis folds the reset place into the loop's law: a `placeBound` on the loop is proven only with
the option; a bound the loop genuinely exceeds stays `Violated` with it. For AC6, the same loop
beside a budget-declared ν-net, with the reset arc on the uncoloured half (the coloured encoder
refuses a reset on a coloured place, and the net would silently fall back to the flat encoding):
the encoded script must report itself coloured and must differ between the option's two states.

---

#### VER-013: Solver Transport

**Priority:** SHOULD

The SMT pipeline ([VER-001]) reaches the solver through one transport in every implementation:
each query is one `z3` process. The process is started with the argument list

```
z3 -smt2 -in -t:<timeout_ms> -T:<ceil((timeout_ms + 1000) / 1000)>
```

plus `fp.engine=spacer` for the HORN query, is fed the complete SMT-LIB2 script on stdin in a
single write, and then has its stdin closed so it sees end-of-file. Both output streams are
drained concurrently from the start, so a reply larger than a pipe buffer cannot stall the
solver, and a wall-clock watchdog at `timeout_ms + 2000` milliseconds kills a process that
ignored both timeouts. The process is killed and reaped on every exit path. No solver state
survives a query: concurrent verifications in one host process are independent, and a solver
crash is a verdict, never a crashed host. The timeout is per invocation; the HORN query, the
certificate script and its detail re-run each receive the full budget.

The executable is `z3` on `PATH` unless the environment variable `LIBPETRI_Z3` names another
one. It is probed once per verification with `--version` and refused below **4.8.0**. Setting
`LIBPETRI_SMT_DUMP` to a directory keeps every script and reply there as `NNN-<phase>.smt2`,
`NNN-<phase>.out` and, when stderr was not empty, `NNN-<phase>.err`, with `NNN` a zero-padded
counter and the phase one of `horn`, `horn-coloured`, `certificate`, `certificate-detail`.

**Reply classification.** The verdict is the first stdout line equal to `sat`, `unsat` or
`unknown`, wherever it appears: a build may print a warning first, and the HORN script's paired
`(get-proof)` / `(get-model)` always yields one `(error …)` line. Under the HORN query
`(assert (not Error))`, `sat` is `Proven` and `unsat` is `Violated`. Without a verdict line the
`Unknown` reason is, in this order: the `timeout` line printed by the `-T` backstop; the watchdog
kill; the first `(error …)` line on stdout, then on stderr; any other stderr text; the unexpected
stdout itself. The certificate script requires exactly three positional answers; an `(error …)`
on either stream, a `timeout` line, a kill or a non-zero exit makes the check inconclusive and
withholds `Proven`.

**Script determinism.** For the same net, initial marking, property and options every
implementation MUST emit byte-identical HORN and certificate scripts: places in Unicode
code-point order of their names; flat transitions in net order with XOR branches in enumeration
order ([IO-016]); environment-injection rules, sink conjuncts and the property's place lists in
place-index order; invariants in `(support, weights, constant)` order after the [VER-007] union;
lines joined with `\n`; no rule names. The certificate is the `(define-fun …)` block of the
`(get-model)` reply pasted verbatim, and a counterexample is the set of ground `Reachable` facts
in the `(get-proof)` reply, ordered only by the replay ([VER-003]).

**Acceptance Criteria:**
1. The same net, marking, property and options produce byte-identical HORN and certificate
   scripts in every implementation (the golden scripts under
   `spec/verification-fixtures/scripts/`).
2. A missing executable yields `Unknown` with a reason naming the command tried and
   `LIBPETRI_Z3`; no exception escapes and the host process survives.
3. An executable below 4.8.0, or one whose `--version` reports no version, yields `Unknown`
   naming both versions (or the reply).
4. A `timeout` reply, an `(error …)` on either stream, a non-zero exit and a process that never
   exits each yield `Unknown` with a distinct reason and leave no solver process behind.
5. A reply preceded by a banner of arbitrary size on either stream is classified by its verdict
   line.
6. The report carries `  Solver: z3 <version>` in its solver phase, or
   `  Solver: z3 unavailable (<reason>)` followed by the implementation's `UNKNOWN` result
   line naming the same reason when no solver resolved.

**Implementation notes:**
- Rust: `libpetri-verification` `z3_process` (`Z3Solver::resolve` / `Z3Solver::run`);
  stub-solver scenarios in `tests/stub_z3.rs`, CI gate in `tests/z3_gate.rs`.
- Python: inherits the Rust transport; `libpetri.z3_available()` reports whether a usable
  executable resolves (`HAS_Z3` is the compile feature only).
- Java: `org.libpetri.smt.z3.Z3Process` / `Z3Solver`; `SmtVerifier.z3Available()`.
- TypeScript: `verification/z3/z3-process` (`resolveZ3` / `runZ3Text`); `z3Available()`.
- AC1 is checked without a solver: `SmtVerifier::encode_scripts` (Rust), `encodeScripts()`
  (Java, TypeScript) and `libpetri.encode_smt_scripts` (Python) return the HORN script and,
  for the flat encoding, the certificate script around the placeholder certificate
  `(define-fun Reachable (…) Bool true)`; the goldens under
  `spec/verification-fixtures/scripts/<id>/` are written by the Rust verifier
  (`scripts/smt-script-parity.py --update`) and diffed by every implementation's
  script-parity test.

**Depends on:** [VER-001], [VER-003], [VER-007], [IO-016]

**Test derivation:** a stub `z3` shell script named by `LIBPETRI_Z3` that answers `--version`
and then replays a scripted reply: a banner before `unsat`; an `(error …)` on stderr during the
certificate check; a `timeout` line; a script that never exits; a two-megabyte banner on each
stream; a version below the floor; a missing executable. Plus the golden-script diff over the
shared verdict-parity fixtures.

---

## State Class Graph

#### VER-010: State Class Graph Analysis

**Priority:** MAY

The engine may support state class graph construction using the Berthomieu-Diaz (1991) algorithm. State classes combine a marking with a Difference Bound Matrix (DBM) representing timing constraints on enabled transitions.

**Acceptance Criteria:**
1. State class graph enumerates reachable (marking, timing zone) pairs.
2. Successor computation correctly handles transition firing and clock updates. The
   number of tokens a firing removes from each input place MUST be the canonical
   `consumptionCount(available)` of [IO-007] — the same function the executor uses —
   and not the enablement threshold `requiredCount()`. In particular `All` and
   `AtLeast(m)` drain the place.
3. XOR outputs are expanded into virtual transitions for branch analysis.

**Depends on:** [IO-007], [EXEC-010]

**Implementation notes:**
- Java: Full implementation
- TypeScript: Full implementation
- Rust: Full implementation (`libpetri-verification` `state_class_graph`)

**Test derivation:** Small timed net; construct state class graph; verify reachable
classes match expected. Regression: a transition with an `all(p)` input followed by a
transition inhibited on `p` — the inhibited successor MUST be reachable, since `p` is
drained; an `atLeast(2, p)` input over 5 tokens MUST leave `p` empty.

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
- Rust: Full implementation (`libpetri-verification` `dbm`)

**Test derivation:** Create DBM for 3 timed transitions; fire one; verify successor zone constraints.

---

#### VER-012: Name-Aware State Class Graph (ν-Partition Quotient)

**Priority:** MAY

The state class graph ([VER-010]) MAY be made **ν-aware** to decide [NU-020] join
correlation *exactly* — the [NU-050] **Route B** carve-out. Each correlation
token carries an abstract, interchangeable name-symbol; a matched (ν-join)
transition is enabled only when one symbol is shared by every correlated input
(not merely when the token counts allow); a minting fork introduces a
globally-fresh symbol; and the graph is quotiented under name-permutation
symmetry (its dedup key abstracts the symbol identities). The timed firing domain
([VER-011]) is carried unchanged alongside the name partition, so the analysis is
exact over **name × time**, and quiescence ([NU-050]) is decided over the
name-aware terminal classes.

**Acceptance Criteria:**
1. A ν-join fires in the graph only on a name shared by all correlated inputs; a
   marking reachable only by equating two distinct names is *not* reachable
   (NU-050 #1), with no budget place required.
2. Two markings differing only by a permutation of name-symbols are the same
   state class (the quotient is finite when the live-name pool is structurally
   bounded).
3. **Conditional on an executor-faithful consumption model** (see below): when the
   graph closes within the class bound the verdict is exact (sound and complete) for
   reachability-safety and quiescence; otherwise it truncates and the verdict is
   `Unknown` (NU-050 #2 — undecidability surfaces as truncation).
4. `All` and `AtLeast(m)` inputs drain their place in the graph exactly as they do at
   run time: after a successor step the source place holds no residue, so an inhibitor
   arc on that place is satisfied in the successor class.

**Exactness precondition (consumption model).** The exactness of criterion 3 is not
unconditional — it holds only while the graph's successor relation removes the *same*
tokens the executor would. The successor step MUST derive each input's token count from
the canonical `consumptionCount(available)` of [IO-007] (so `All` and `AtLeast(m)`
consume **all** available tokens, not merely `requiredCount()`), in the [EXEC-010] FIFO
order. A successor relation that consumes a *minimum* instead leaves phantom residue in
the source place; that residue keeps inhibitor arcs on the place unsatisfied and
suppresses successor classes, so a genuinely reachable marking is reported unreachable —
an **unsound** `Proven`, not a conservative one. Implementations therefore MUST delegate
to the same cardinality contract the executor uses rather than restating it.

**Implementation notes:**
- Rust: Full implementation (`libpetri-verification` `name_state_class_graph` /
  `nu_scg_verifier`); the canonical name-partition key format is shared verbatim.
- Java: Full implementation (`org.libpetri.analysis.NameStateClassGraph` /
  `org.libpetri.smt.NuScgVerifier`).
- TypeScript: Full implementation (`verification/analysis/name-state-class-graph`
  / `verification/nu-scg-verifier`).
- Python: inherits the Rust analysis through `verify`.
- Memory: an implementation MAY intern (hash-cons) the base class and the name layer
  between state classes. The base intern key MUST include the class-relative
  earliest-ready times alongside the marking and zone, because the [NU-052] prune reads
  them while class equality does not. Class identity MUST carry them too: the graph's
  dedup key is the pair of intern ids (base, name layer), not the class object, so two
  arrivals that agree on marking, zone and name layer but disagree on the earliest-ready
  times stay two classes and each keeps its own prune input. Interning is semantics-free by key-equivariance of
  the successor step (Lean `Interning.lean`, `interned_keys_eq`): the reachable quotient
  and the verdict are unchanged; class indices and the reported counterexample trace may
  differ from a non-interned build.
- Solver-free (no Z3); the verifier prefers Route A's bounded name-colouring for
  budget-declared untimed reachability-safety and uses this route for quiescence,
  budget-less, and timed ν-nets.

**Depends on:** [VER-010], [VER-011], [NU-020], [NU-050], [IO-007]

**Test derivation:** Two independent mints feeding one join with no budget place;
verify the join output is unreachable (NU-050 #1); a same-mint variant reaches it;
an ever-minting net truncates to `Unknown`.

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
