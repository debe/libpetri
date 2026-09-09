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

- **DeadlockFree** — no reachable marking exists where no transition is enabled and a
  token is stranded. Optionally, the verifier accepts **sink places**: expected terminal
  places where coming to rest is permitted. The error condition is: (all transitions
  disabled) ∧ (some marked place is not a declared sink). A quiescent marking violates
  exactly when it leaves a token outside the declared terminals — workflow-net proper
  completion. With no sinks declared this degenerates to: any quiescent marking still
  holding a token.
- **TerminatesAtSink** — every reachable quiescent marking has at least one declared sink
  marked. The error condition is: (all transitions disabled) ∧ (no sink place has a token).
  This asks the weaker question "did the net come to rest at a declared terminal at all",
  and says nothing about tokens left elsewhere. It is meaningful only when at least one
  sink is declared; with none, every quiescent marking violates vacuously.
- **MutualExclusion(p1, p2)** — places p1 and p2 never both have tokens simultaneously
- **PlaceBound(place, k)** — place never has more than k tokens
- **Unreachable(places)** — the given set of places is never all simultaneously non-empty

The two sink-sensitive properties are not ordered by strength; they **invert on the empty
marking**. A quiescent `{done:1, stuck:1}` with `done` a sink violates DeadlockFree (it
strands `stuck`) but satisfies TerminatesAtSink. The fully drained marking `{}` satisfies
DeadlockFree (nothing is stranded) but violates TerminatesAtSink (no sink was reached).
Neither subsumes the other, which is why both exist.

**Acceptance Criteria:**
1. Each property can be constructed and passed to the verifier.
2. Properties are verified against the net's reachable state space.
3. **DeadlockFree** reports a violation for a quiescent marking that marks a declared sink
   while also holding a token in a non-sink place.
4. **DeadlockFree** reports no violation for the empty quiescent marking, whether or not
   sinks are declared. A net that drains completely has stranded nothing.
5. **TerminatesAtSink** reports no violation for a quiescent marking that marks any
   declared sink, regardless of tokens held elsewhere.
6. **TerminatesAtSink** reports a violation for the empty quiescent marking when at least
   one sink is declared.
7. Every route that decides these properties decides the **same** predicate: the SMT route
   ([VER-001]) and the ν name-partition state-class graph route ([VER-012]) return the same
   verdict for every marking both can classify.

**Test derivation:** For each property type: construct net where property holds → Proven; construct net where property is violated → Violated.

---

#### VER-003: Verification Result

**Priority:** SHOULD

The verification result includes:

- **Verdict**: Proven (with proof method and optional inductive invariant), Violated (with counterexample), or Unknown (with reason)
- **Route**: which route decided the verdict — the SMT pipeline, bounded enumeration
  ([VER-017]), the ν name-partition graph ([VER-012]), a structural proof, or none. The graph
  routes compute no P-invariants, so a consumer reading the result's fields rather than its
  report MUST be able to tell "not computed on this route" from "the net has none". The rule
  is about the **empty** case only: an empty list off the SMT route means "not computed", while
  a non-empty list is real whatever the route reports — a run that found no usable solver still
  carries the invariants the pipeline computed before it gave up.
- **P-Invariants**: Place invariants discovered during analysis
- **Counterexample trace**: Sequence of markings and transitions leading to violation
- **Statistics**: Number of places, transitions, invariants found, elapsed time

**Acceptance Criteria:**
1. Proven verdict includes the proof method.
2. Violated verdict includes a counterexample trace of markings and transitions.
3. Unknown verdict includes a reason (e.g., timeout, solver limit).
4. The result names the deciding route, so an empty invariant list from a graph route is
   distinguishable from a net that genuinely has none. A non-empty list is valid on every
   route, including one that ended without a solver.
5. A property naming a place the net does not declare is refused with `Unknown` **before any
   route runs**. Every route answers such a property vacuously and each in its own way — the
   flat encoder emits a violation term of `false`, which proves anything; a linear bound drops
   the unresolved conjunct and separates a strictly stronger demand; an enumeration finds no
   class marking a place that cannot be marked — so a refusal placed inside one route is not a
   refusal at all. It MUST precede the ν route, the structural routes and the encoders alike.

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

**The mirror-image vacuity.** Under `AlwaysAvailable` (and under `Bounded(k)` whenever the
demand is met) an environment-gated transition is enabled in *every* marking, so **no marking
is quiescent** and every quiescence property — `DeadlockFree`, `TerminatesAtSink`,
`JoinedOrDeadLettered` — is unviolatable. The `Proven` this yields is correct and carries no
information about the net: an open net with an always-available source never comes to rest, so
"no reachable quiescent marking strands a token" holds whatever the net does. Unlike the
`Ignore` case this is not refused, because the verdict is true; but an implementation MUST
report it, so a caller cannot read the empty claim as a guarantee about their workflow.

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
6. When injection makes some transition enabled in every marking, a quiescence property is
   reported as vacuously true: the verdict stands, and the report names the reason.

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

**The enumeration is expensive and MUST be skipped when nothing will read it.** The minimal
semiflows of a net are worst-case exponential in its branching: `k` independent diamonds in
series have `2^k` of them, measured at 2 048 for eleven and past the implementation's backstop
beyond thirteen. Computing them for a caller who enabled neither this option nor the [NU-053]
colour-slot bound is a large unforced cost — 27 s of preprocessing on a 24-layer net before the
solver sees anything — and on a wide net an **uncatchable** one, since the heap it exhausts
aborts the process rather than returning a verdict. An implementation MUST compute semiflows
only when the option is enabled or a coloured plan needs the bound.

An implementation SHOULD therefore offer an option that unions the gate-validated semiflows
into the invariant list the encoders receive, and SHOULD offer an **`auto`** setting that
applies the condition above on the caller's behalf: compute and union the semiflows exactly
when the basis lost a law to the H1 guard, and skip them otherwise. That is decidable in one
pass, because the drops are known before the semiflows are needed. It is the setting to prefer
**for verification**: the two useful cases are told apart by a fact the pipeline already has, and
leaving that to the caller has a poor record — the option's unqualified reputation as "the
biggest lever" has led a consumer to enable it globally and then build a size ceiling around its
cost.

**What `auto` does not decide.** It answers whether the semiflows would add information to the
**encoding**, not whether they would appear in the result for a caller who *inspects* the
invariant list. A complete basis spans every conservation law, so a semiflow it spans constrains
nothing further and the solver gains nothing — but the basis is the *signed* null-space, and a
law it spans need not appear in it in **non-negative** form. Only the Farkas enumeration produces
that form. A caller looking for a law by its shape — "a non-negative law weighting the budget
place and every running place positively" — can therefore find nothing on a net that plainly has
such a law, because `auto` correctly skipped an enumeration that would have added no constraint.
Such a caller MUST request the union explicitly. The two claims are both true and easily
confused: `auto` is right about strengthening and says nothing about presentation. The option is **off by default** so that reports
stay byte-identical across releases. It is pure strengthening (Lean `Semiflow.lean`,
`semiflow_union_sound`: conjoining any list of gate-validated laws preserves the abstract
reachable set), so enabling it can never turn a `Violated` into a `Proven`.

**What enabling it does and does not promise.** It is a *strength* option, not a
*correctness* one, and on a branchy net the distinction is sharp. An implementation caps the
rows that survive each elimination round, so where the minimal set is exponential the semiflows
that reach the encoders are an **arbitrary truncation** of it: a proof that needs one particular
law can miss it even though the phase ran to completion and reported no drop. Enabling the
option therefore means "try harder", never "this answer is now trustworthy" — a `Proven` is
equally sound either way, and an `Unknown` with the option on is not evidence that no such law
exists. Implementations SHOULD report the truncation when it binds.

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
2. With the option disabled (the default) the semiflows do not reach the encoders, are not
   computed at all unless a coloured plan needs the bound, and the report is byte-identical to
   a build without the feature.
3. Under `auto` the report says which way it went and why, the union happens only when a law
   was dropped, and the verdict never differs from whichever explicit setting `auto` chose. The
   report's "off" wording MUST say that the skipped semiflows add no *constraint*, not that they
   would add nothing, so a caller reading the invariant list is not misled about their absence.
4. With the option enabled the report carries `  Semiflows encoded as invariants: N`, where
   `N` counts the semiflows added after deduplication against the basis rows, and the result's
   invariant count and list include them.
5. `Proven` is never weakened: where the certificate check applies (the flat encoding) it
   receives the strengthened list and re-proves every law's initiation and consecution against
   the unstrengthened step relation before the verdict is reported.
6. A genuine violation stays `Violated` with the option enabled.
7. The strengthened list reaches the name-coloured encoder ([NU-050]) as well as the flat one:
   there is a net on the coloured path whose encoded script differs between the option's two
   states. (Not every such net — a semiflow already present in the basis dedups away, and AC3
   admits `N = 0`, in which case the two scripts are identical.) This is about what the encoder
   receives, not about certification — AC4's certificate check is flat-path only, and a coloured
   `Proven` reports `  Certificate check: not applicable (name-coloured encoding)`.

**Implementation notes:**
- Java: `SmtVerifier.semiflowInvariants(boolean)`.
- TypeScript: `SmtVerifier.semiflowInvariants(enabled | 'auto')`.
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
counter and the phase one of `bound` ([VER-015]), `horn`, `horn-coloured`, `certificate`,
`certificate-detail`.

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

#### VER-014: Conditional Sink Places (Designed Terminals)

**Priority:** SHOULD

`DeadlockFree` ([VER-002]) reads a quiescent marking against the places where a token may
rest. Besides the unconditional **sink places**, the verifier accepts **conditional sink
places**: a set of places where a token may rest **while a marker place holds a token**,
declared as `sinkPlacesWhen(marker, places…)`. A marked marker is a *designed terminal* — a
halted or paused run, a cancelled batch — under which the work it interrupted legitimately
stays where it was delivered. The marker itself is at rest whenever it is marked, so
`sinkPlacesWhen(marker)` with no further places excuses exactly the marker.

Declarations union. A token in place `p` of a quiescent marking `M` is **stranded** iff `p`
is not a declared sink, `p` is not a marker, and no conditional set naming `p` has its
marker marked in `M`. The `DeadlockFree` error condition becomes: (all transitions disabled)
∧ (some marked place is stranded). Repeated declarations for one marker accumulate;
declarations for different markers are independent, so a place excused by two markers is
stranded only when both are unmarked. `TerminatesAtSink` is unaffected and reads the
unconditional sinks only. An unresolved marker or place contributes nothing, as an
unresolved sink does: a mistyped marker makes the property stricter, never laxer.

**Encoding.** In the flat and name-coloured CHC encodings the stranded disjunction of
[VER-002] gains, for each place `p` excused by markers `k₁ < … < kₙ` (flat indices), the
disjunct `(and (>= m_p 1) (= m_k₁ 0) … (= m_kₙ 0))` in place of `(>= m_p 1)`; declared sinks
and markers contribute no disjunct. Scripts without a conditional declaration are
byte-identical to those of [VER-002]. The report renders the declarations after the property
as `(sinks: a, b; when h: c, d; when p)`, in declaration order.

**Acceptance Criteria:**
1. A quiescent marking that marks a marker and holds tokens only in declared sinks, in the
   marker, and in that marker's conditional places is not a `DeadlockFree` violation.
2. A quiescent marking that holds a token in a conditional place whose marker is **unmarked**
   is a violation, exactly as without the declaration.
3. The marker needs no self-listing: `sinkPlacesWhen(p)` excuses a quiescent marking holding
   only `p`.
4. `TerminatesAtSink` ignores conditional declarations: a quiescent marking that marks a
   marker but no declared sink violates it.
5. Every route that decides `DeadlockFree` — the flat encoder, the name-coloured encoder, the
   certificate check's safety condition, the abstract counterexample replay and the ν
   name-partition graph ([VER-012]) — reads the same rest set; the four implementations emit
   byte-identical scripts for the same declarations ([VER-013] AC1).

**Implementation notes:**
- Java: `SmtVerifier.sinkPlacesWhen(Place<?> marker, Place<?>... places)`.
- TypeScript: `SmtVerifier.sinkPlacesWhen(marker, ...places)`; `verification/rest-set`
  (`strandingExcuses`, `strandsToken`, `describeSinks`).
- Rust: `SmtVerifier::sink_places_when(marker, places)`.
- Python: `verify(..., sink_places_when={marker: [places…]})`.
- Fixtures: `sinkPlacesWhen` in `spec/verification-fixtures/fixtures.json`
  (`sink-partial-terminal-conditional-proven`, `dead-end-chain-marker-proven`,
  `dead-end-chain-unmarked-marker-violated`, `nu-mixed-terminal-route-b-conditional-proven`).

**Depends on:** [VER-002], [VER-012], [VER-013]

**Test derivation:** a fork whose one arm may halt while the other's token is still in
flight, with the halt marker inhibiting the second arm: `deadlockFree` with the halt as a
plain sink is violated (the in-flight token is stranded); with the in-flight place declared
under the halt marker it is proven; with the marker alone it stays violated; `terminatesAtSink`
with the same declarations is violated. A chain whose marker is consumed before quiescence
(AC2), and the same net with the resting place as its own marker (AC3).

---

#### VER-015: Linear State-Equation Bound

**Priority:** SHOULD

Before the fixpoint query, a **reachability-safety** property (`PlaceBound`,
`BranchPlaceBound`, `MutualExclusion`, `Unreachable`) is tried against the **state
equation**: every abstract-reachable marking satisfies `M = M0 + C·σ` for some firing count
vector `σ ≥ 0`, so for any weighting `y ≥ 0` with `y·C ≤ 0` on every transition,
`y·M ≤ y·M0` on every reachable marking — a *decreasing* conservation law, where the
P-invariants of [VER-005] are the equalities. The violation of such a property is a lower
demand `d` on some places (`m_p ≥ 1` for each place of an `Unreachable` or `MutualExclusion`,
`m_p ≥ k+1` for a bound `k`); if `y·d > y·M0` for some such `y`, no reachable marking meets
the demand and the property is **proven structurally**, without IC3.

The weighting is found by one `QF_LIA` query through the solver transport of [VER-013]
(phase `bound`): variables `y_p ≥ 0` per flat place, `y_p = 0` on every consume-all / reset
place (H1) and every injected environment place (H3'), one row `Σ_p C[p][t]·y_p ≤ 0` per flat
transition, and `Σ_p d_p·y_p ≥ 1 + Σ_p M0_p·y_p`. A `sat` model is **re-checked in exact
integer arithmetic** (`y ≥ 0`, the zero weights, every row, the demand) before it is
believed; a model that fails the check is discarded. `unsat`, `unknown` and any transport
failure hand over to the fixpoint query. The phase is skipped under `Ignore` with
environment places registered ([VER-006] AC4) and for the quiescence properties, whose
violation is not a linear demand. A ν-net's verdict receives the [NU-050] over-approximation
note like any other flat proof.

This closes the class of proofs IC3 does not find on pipeline-shaped nets: an *ordering*
argument — "both join slots armed means every upstream stage has run, so no halt is still
possible" — is a weighted count bound, which Spacer's lemma generalisation does not invent
over fifty variables but a linear solver finds in milliseconds. A net that answered `unknown`
after 300 s answers `proven` in under a second.

**Acceptance Criteria:**
1. A reachability-safety property whose violating markings exceed some `y·M ≤ y·M0`
   (`y ≥ 0`, `y·C ≤ 0`) is `Proven` with method `structural`, without a fixpoint query, and
   the report names the bound and the demand:
   `  Linear state-equation bound: 2*p0 + a + b <= 2; violation needs a + b + halt >= 3`.
2. A property whose violation the state equation admits (`unsat` from the query) proceeds to
   the fixpoint query with the report line `  Linear state-equation bound: none separates the violation`.
3. The bound is re-proven in exact integer arithmetic; a model that fails it is reported
   `inconclusive (solver model failed the exact re-check)` and the fixpoint query runs.
4. The `bound` script is byte-identical across implementations ([VER-013] AC1) and is
   reported by `encodeScripts()` (`null` for a quiescence property).
5. A genuine violation is never masked: the phase can only return `Proven`.

The phase runs on the flat path only; a net on the exact name-coloured encoding ([NU-053])
keeps that route. It is on by default and MAY be disabled (`linearBound(false)`) to force
the fixpoint path — for its certificate, or to exercise the engine itself.

**Implementation notes:**
- TypeScript: `verification/z3/linear-bound` (`encodeLinearBound`, `decodeLinearBound`,
  `checkLinearBoundExact`); `SmtVerifier.linearBound(enabled)`.
- Java: `org.libpetri.smt.z3.LinearBound`; `SmtVerifier.linearBound(boolean)`.
- Rust: `libpetri-verification` `linear_bound`; `SmtVerifier::linear_bound(bool)`.
- Python: `verify(..., linear_bound=True)`.

**Depends on:** [VER-001], [VER-004], [VER-005], [VER-006], [VER-013]

**Test derivation:** a fork that may halt instead (`p0 → f → AND(a, b) | halt`, arms
`a → ra`, `b → rb`, join `ra + rb → done`): `unreachable{ra, rb, halt}` has no equality law
excluding it (the halt branch turns two units into one) and is proven by the bound
`2·p0 + a + b + 2·done + halt + ra + rb ≤ 2`; `mutualExclusion(ra, rb)` is reachable and hands
over to the fixpoint query, which reports `violated` with a confirmed replay.

---

#### VER-016: State-Equation Strengthening with Firing Counters

**Priority:** SHOULD

The flat CHC encoding ([VER-001]) MAY carry the **state equation** itself. With the option
enabled the state is `(M, n)` — one firing counter `n_t` per flat transition after the
places — the initial fact has `n = 0`, transition `t`'s rule sets `n'_t = n_t + 1` and copies
every other counter, an environment-injection rule copies them all, and every transition
rule's body conjoins `n' ≥ 0` and, for each place `p` whose column is exact (no
consume-all / reset arc on `p`, `p` not injected), `m'_p = M0_p + Σ_t C[p][t]·n'_t` over the
transitions with a non-zero effect on `p`, in transition order. The error rule quantifies the
counters and constrains the marking only.

Every linear consequence of the marking equation — the equality laws of [VER-005] and
[VER-007], the decreasing laws of [VER-015], and the mixed-sign inequalities
(`y·C ≥ 0 ⇒ y·M ≥ y·M0`) that express *ordering* between the stages of a pipeline — is then a
fact in every rule body rather than a lemma Spacer has to generalise to, and it comes at no
enumeration cost: the cone of inequality laws of a fifty-place net has too many extreme rays
to list, but its defining system has one row per place. This is what a **quiescence** proof
on a workflow net needs and [VER-015] cannot give it (a `DeadlockFree` violation is not a
linear demand): proper completion of a 50-place agent-dispatch net under conditional sinks
([VER-014]) went from `unknown` at 120 s to `proven` in 1.5 s with this as the only change.

The option is **off by default** so scripts and reports stay byte-identical; a genuinely
violated property is still found, about 1.5× slower on the nets above. Soundness follows
the shape of [VER-005]'s strengthening (Lean `Strengthening.lean`): the counters are exact
bookkeeping, so the equation holds on every reachable augmented state and conjoining it
removes none. The **certificate check** ranges over `(M, n)`: the candidate conjoins the
P-invariants, `n ≥ 0` and the marking equation, and re-proves them against the raw step
relation, whose only counter knowledge is the increment. The counterexample decoder reads a
fact's marking from its leading `P` arguments. The option does not apply to the
name-coloured encoding ([NU-050]) or to Route B ([VER-012]); the report says so when both
are requested.

**Acceptance Criteria:**
1. With the option disabled the scripts and reports are byte-identical to a build without it.
2. With the option enabled `Reachable` has arity `P + T`, the initial fact ends in `T` zeros,
   transition `t`'s rule contains `(= n_tp (+ n_t 1))` and `(= n_jp n_j)` for every `j ≠ t`,
   and every transition rule contains the marking equation of every exact place over the
   primed variables; consume-all, reset and injected places carry none.
3. A `Proven` verdict passes the certificate check (`init, consecution, safety`) with the
   equation in the candidate; a genuine violation stays `Violated` and its counterexample
   replays.
4. The report carries `  State equation: encoded over T firing counters (VER-016)` when the
   option applied, and `  State equation: not applied (name-coloured encoding)` when it was
   requested on the coloured path.
5. The HORN and certificate scripts with the option enabled are byte-identical across the four
   implementations ([VER-013] AC1).

**Implementation notes:**
- Java: `SmtVerifier.stateEquation(boolean)`.
- TypeScript: `SmtVerifier.stateEquation(enabled)`; `encodeNet(…, { stateEquation })`.
- Rust: `SmtVerifier::state_equation(bool)`.
- Python: `verify(..., state_equation=True)`.

**Depends on:** [VER-001], [VER-004], [VER-005], [VER-013], [VER-015]

**Test derivation:** the fork-that-may-halt net of [VER-015] under `deadlockFree` with
`done` and `halt` as sinks: proven, certificate check passed, report names five counters;
with `halt` not a sink: violated with a confirmed replay ending in a halted marking. The
`unreachable{ra, rb, halt}` script has arity `7 + 5`, `(= m4p (+ 1 (- n0p) (- n1p)))` in each
of its five rules, and no equation for a consume-all place on a net that has one.

---

#### VER-017: Bounded State-Space Enumeration Route

**Priority:** SHOULD

Before the SMT pipeline ([VER-001]), an implementation SHOULD try to decide the property by
**enumerating the state-class graph** ([VER-010]) up to a class budget. When the graph closes
within the budget the verdict is read off it directly and no solver runs; when it does not, the
route declines and the SMT pipeline runs unchanged.

The motivation is a shape the fixpoint engine handles badly and enumeration handles trivially.
IC3/PDR is built for state spaces that are wide and shallow; a workflow net is the opposite,
narrow and deep. A forty-node pipeline has fewer than two thousand reachable classes, but its
*diameter* is the length of the pipeline, so the search needs a frame per stage and its cost
climbs with roughly the cube of the length. Enumeration is linear in the reachable state space.
Measured on a compiled forty-node linear workflow (370 places, 163 transitions, 1 967 classes):
**410 s on the fixpoint path, 0.11 s here**; at 160 nodes (1 450 places) enumeration takes 5.5 s
while the fixpoint path is far beyond any practical budget.

**When the route applies.** All four conditions, so that its verdict is interchangeable with the
one it replaces:

1. The net declares **no match (ν-join) transitions** — a ν-net has its own exact route
   ([VER-012], Route B), which subsumes this one.
2. **No environment places** are registered. The graph does not model injection ([VER-006]), so
   a verdict about an open net would not mean what the encoders' does.
3. The net is **untimed** — every transition `immediate`. The graph carries firing domains, so on
   a timed net it would explore only the runs the timing admits and its `proven` would be the
   weaker *timed* claim; [VER-004] fixes the untimed proof as the stronger one, and a route MUST
   NOT quietly return a weaker claim than the route it replaced. On an untimed net no domain
   excludes anything, so the graph explores exactly the untimed reachable set.
4. The class budget is positive. Setting it to `0` disables the route.

**What the verdict means.** Exact — sound *and* complete. A `violated` is a real firing sequence
with the shortest witnessing path from the initial class, not a possibly-spurious
over-approximation, so it needs no replay confirmation ([VER-003]); implementations report
`counterexampleConfirmed` as "not applicable" for it, as they do for Route B. A `proven` is the
same claim the encoders make, decided by enumeration rather than by search. The route decides the
**same predicate** as every other route ([VER-002] AC7, [VER-014]); implementations MUST share
one predicate implementation between this route and [VER-012]'s rather than restate it.

The route can only add verdicts, never remove them: on truncation the SMT pipeline runs exactly
as before, so no query that the solver could decide becomes `unknown`.

**Acceptance Criteria:**
1. On an untimed net whose state-class graph closes within the budget, the property is decided
   without invoking a solver: the report names the route and its class count, and carries no
   solver phase.
2. A violated verdict carries a counterexample trace whose transition sequence is a real firing
   sequence from the initial marking to the witnessing class, reported as **confirmed**: the
   graph path is a firing sequence, so it is ordered by construction and there is nothing to
   replay. A consumer keying "are these steps ordered" off that field is correct without
   special-casing the route.
3. The result names this route and reports that P-invariants were not computed, so an empty
   invariant list is not mistaken for "the net has none".
4. Exceeding the budget produces a report line naming the budget and falls through to the SMT
   pipeline, whose behaviour is unchanged.
5. The route is skipped for a ν-net, for a net with environment places, for a timed net, and
   when the budget is `0`; in each case the report shows the SMT pipeline ran.
6. Where both routes can answer, they return the same verdict for the same net and property.

**Implementation notes:**
- TypeScript: `verification/scg-verifier` (`verifyViaStateClassGraph`, `isUntimed`);
  `SmtVerifier.enumerationMaxClasses(max)`, default 50 000. The shared predicate is
  `verification/graph-decision` (`decideOverClasses`), used by [VER-012]'s route as well.
- Java: `org.libpetri.smt.ScgVerifier`; `SmtVerifier.enumerationMaxClasses(int)`.
- Rust: `libpetri-verification` `scg_verifier`; `SmtVerifier::enumeration_max_classes(usize)`.
- Python: `verify(..., enumeration_max_classes=50_000)`.

**Depends on:** [VER-002], [VER-004], [VER-006], [VER-010], [VER-012], [VER-014]

**Test derivation:** a pipeline `p0 → t0 → p1 → … → pn`, untimed: `deadlockFree` with `pn` a sink
is proven by enumeration with `n+1` classes and no solver phase; without the sink it is violated
with the firing sequence `t0 … t(n-1)`. The same net with a class budget below the graph size
reports truncation and is answered by the SMT pipeline; with the budget `0` the route never runs.
A `delayed` variant of the same net is skipped as timed. For AC5, the same query with and without
the route returns the same verdict.

---

## State Class Graph

#### VER-010: State Class Graph Analysis

**Priority:** MAY

The engine may support state class graph construction using the Berthomieu-Diaz (1991) algorithm. State classes combine a marking with a Difference Bound Matrix (DBM) representing timing constraints on enabled transitions.

**Acceptance Criteria:**
1. State class graph enumerates reachable (marking, timing zone) pairs. A class's identity is
   its marking and its **full** firing domain, independent of the order in which its
   transitions became enabled: the successor step lays clocks out persistent-then-newly-
   enabled, which is path-dependent, so implementations MUST put every class's clocks in one
   canonical order (ascending transition name) and key on the complete difference-bound
   matrix ([VER-011]), not on the per-clock projections alone. Two arrivals at the same
   marking and zone by different interleavings are one class; two zones that agree on every
   projection but differ in a difference constraint are two. On an untimed workflow net the
   order-sensitive key inflated the class count 1.5× (one marking held by fourteen classes);
   the projection-only key merges classes whose successors differ, which can lose a
   reachable marking.
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
4. The zone exposes a dedup key over its full canonical matrix (every `θᵢ - θⱼ` bound, not
   only the diagonal projections), and a permutation of its clocks that reorders the matrix
   with them; equality is positional over the canonical order ([VER-010] AC1).

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

**Commoner's theorem governs ORDINARY nets only.** The siphon and trap fixpoints are computed
from the pre/post vectors, so they model a net in which the sole reason a transition is disabled
is an input place holding too few tokens. A read arc, an inhibitor arc, a reset arc, a
consume-all input or an arc weight above one is a disablement the fixpoints do not see, and
dropping it yields a strictly **more permissive** net — the wrong direction for a deadlock
proof. An implementation that converts a siphon/trap result into a `Proven` verdict MUST
therefore refuse to do so for any net carrying one of them, exactly as it already refuses when
sinks are declared or environment places are registered. Three witnesses, each a net that is
dead at its initial marking and was reported deadlock-free before the restriction:
`t1: one(a) read(g) → g` with `t2: one(g) → a` from `{a:1}`; `t: exactly(2, a) → a` from
`{a:1}`; `t: one(a) inhibitor(b) → a` from `{a:1, b:1}`.

**Acceptance Criteria:**
1. Siphons and traps are identified from the net structure.
2. Results inform deadlock analysis (every siphon containing a marked trap ensures liveness).
3. A structural `Proven` is offered only for a net with no read, inhibitor or reset arc, no
   consume-all input and no arc weight above one. Each of the three witnesses above returns a
   verdict from a route that models what disables them, never a structural proof.

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
