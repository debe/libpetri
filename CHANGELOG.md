# Changelog

## Java 4.1.0 / TypeScript 4.1.0 / Rust 4.2.0 / Python 3.2.0 — 2026-09-04

**A subnet can be proven again, and [VER-006] now binds every route.** Both reported downstream against the 4.0.0 wave.

- **Fixed — `SubnetDef.verify()` can prove a subnet with an input port** ([MOD-051]). It allocates an environment place per input and in-out port but never chose an environment mode, so it inherited `ignore()` — under which [VER-006] refuses every proof. `verify` now takes the mode as a parameter: a Java overload, `verify_subnet_with_mode` in Rust, an optional parameter in TypeScript, `environment_mode=` in Python. `VerificationHarness` is unchanged in all four.
- **Fixed — [VER-006] binds Route B, not just the solver path.** The ν name-partition state-class graph returned its verdict without passing the vacuity guard, so an unbudgeted ν-net with an environment place under `ignore()` could report `Proven` for exactly the reason the guard exists to refuse. **Such a `Proven` from Java 4.0.0 / TypeScript 4.0.0 / Rust 4.1.0 / Python 3.1.0 was unsound.** Both routes now share one guard; new AC5.
- **Changed — one environment-mode default across the four.** Java, Rust and Python now default to `alwaysAvailable()`, matching TypeScript, which had defaulted that way alone. Verdicts change for nets with environment places: an `Unknown` becomes a real answer, and a query that returned a fast `Unknown` may now run to its timeout instead. Pass `ignore()` explicitly to keep the old treatment.
- **Changed — [VER-007] documents its reach and its trigger.** The strengthened invariant list has always reached the name-coloured encoder; only the flat path said so, and Java's javadoc said the opposite. New AC6, and all four API docs name the trigger: one `all()` / `atLeast(n)` or reset arc on a busy place drops every basis row whose support touches it, so draining an input queue is enough to leave IC3 without the net's conservation laws.
- **Internal** — `verify()` and `encodeScripts()` now reach the coloured encoder through one call site, and a shared fixture pins [VER-007] byte-for-byte across the four implementations.

Requirement count unchanged at 210.

---

## Java 4.0.0 / TypeScript 4.0.0 / Rust 4.1.0 / Python 3.1.0 — 2026-09-03

**One solver transport, verifier reach, ν-graph memory, and the proofs behind them.** Every verifier now runs the `z3` executable and sends it the same script, byte for byte; IC3 can be handed the net's minimal conservation laws, the ν state-class graph interns its two layers, and a zero colour budget is decided instead of declined. Each proof-backed change is proved in Lean before it is ported; Java, TypeScript and Rust carry the same tests, Python runs them through the binding.

---

### Executor

#### Fixed — an expired window no longer parks the executor (TypeScript)

`awaitWork()` read `millisUntilNextTimedTransition() === 0` as "no timer needed"
rather than "a boundary is already due", so it scheduled nothing. With no action
in flight the wait then held only the external wake-up promise, which a net with
no environment places has nobody to resolve: instead of reaping the expired
window on the next cycle, the executor slept until its run budget expired and
`run(ms)` rejected with `Execution timed out`. A `window()` whose deadline passed
while the event loop was blocked hit exactly this, so the symptom was
load-dependent. Both TypeScript executors were affected; Rust and Java already
returned immediately on a due boundary, and Python inherits the Rust behaviour.

---

### Verification

#### Changed — one solver transport: every verifier runs the `z3` executable (Rust, Python, Java, TypeScript)

The Java verifier no longer binds Z3 through JNI and the TypeScript verifier no longer loads the `z3-solver` WASM. Like Rust and Python they start one `z3` process per query, hands it the SMT-LIB2 script on stdin and reads the reply: no native library to put on `java.library.path`, no solver state shared between concurrent verifiers, a solver crash is an `Unknown`, and a wedged solver is killed by a watchdog. The `javasmt-solver-z3` dependency is gone; a `z3` executable (4.8.0 or newer, on `PATH` or named by `LIBPETRI_Z3`) is required at run time and `SmtVerifier.z3Available()` says whether one resolves. `LIBPETRI_SMT_DUMP` keeps every script and reply. **Breaking for Java** (4.0): `SpacerRunner`, `SmtEncoder`, `NameColouredEncoder`, `CertificateChecker` and `CounterexampleDecoder` now emit and read text; IC3 level invariants and the derivation-order counterexample listing are gone (the replay-ordered trace stays); the `Solver:` line is new in the report. **Breaking for TypeScript** (4.0): the 32 MB `z3-solver` dependency is gone and a `z3` executable is required at run time; `runZ3Spacer`, `encode`, `encodeColoured`, `checkCertificate` and `decode` are text-based and `createSpacerRunner` is removed; a solve no longer occupies the event loop or serialises behind a module mutex; with the replay disabled no proof is requested, so the violated result carries no trace. New requirement [VER-013].

The Rust transport, now the reference, gained what it lacked: a kill-on-drop guard, concurrent stdout/stderr drains, a wall-clock watchdog, a soft `-t:<ms>` budget with the `-T` backstop, the `timeout` reply classified, a version floor, and the two environment variables. Python gains `libpetri.z3_available()`; `HAS_Z3` only ever said the wheel was built with the SMT surface.

Scripts are byte-identical across the implementations, and the Java and TypeScript ports are checked against goldens the Rust verifier wrote. Making them identical surfaced three divergences in Java and the same three in TypeScript, all fixed: the name-coloured deadlock predicate excused a quiescent marking only when *every* marked place was a declared sink, where [VER-002] and the Rust encoder excuse it when *any* declared sink holds a token (one test had declared its dead-letter place a sink to compensate); the null-space basis dropped every mixed-sign conservation law, which the exact gate accepts and IC3 wants; and a property naming a place outside the net now refuses with `Unknown` on the flat path as it already did on the coloured one, instead of encoding a vacuous predicate.

#### Added — the scripts are a gate (Java, TypeScript, Rust, Python)

`encodeScripts()` (`encode_scripts` in Rust, `libpetri.encode_smt_scripts` in Python) returns the HORN and certificate scripts a verification would send to z3, without a solver. The scripts for every shared verdict-parity fixture are pinned under `spec/verification-fixtures/scripts/` (written by Rust, `scripts/smt-script-parity.py --update`) and every implementation diffs its own output against them byte for byte; a diff is a parity finding in whichever emitter drifted. A new fixture puts the name-coloured encoder under the same gate (`budgetPlaces` is a fixture field now).

#### Added — semiflow invariants for IC3, opt in (Java, TypeScript, Rust, Python)

The null-space basis is one basis of many: elimination folds a reset place into a chain's conservation law, the exact gate drops it, and on a reset-heavy net IC3 is left to rediscover every such law itself, which on a hundred-place net it does not do within any budget. `semiflowInvariants(true)` (`semiflow_invariants=True` in Python) unions the gate-validated P-semiflows, the net's minimal laws, into what the encoders and the certificate check receive; the report says how many with `  Semiflows encoded as invariants: N`. On the net that surfaced this, eight reachability queries that timed out at 120 s close in about a second. Off by default so reports stay byte-identical. Pure strengthening: a `Violated` can never become `Proven` (`semiflow_union_sound`), and the semiflows pass the same gate as the basis rows because semi-positivity alone is not enough (`semiflow_gate_is_necessary`). New requirement [VER-007].

#### Fixed — a zero colour budget is decided, not declined (Java, TypeScript, Rust, Python)

A ν-net marking with no budget token has a covering semiflow with initial sum 0, and the coloured encoder refused it, so quiescence fell back to the name-blind encoding and downgraded to `Unknown`. No coloured token can ever exist there, every mint, join and coloured consumer is dead, and the zero-slot plan is exact (`vacuous_colour_layer`), so it is now taken. The colour-slot bound also lets zero-constant semiflows cover their places before any positive law is summed, which tightens `k` on nets where a conserved counter happens to touch a coloured place. [NU-053] AC6.

#### Changed — the ν state-class graph interns its base class and name layer (Java, TypeScript, Rust, Python)

A Route B class cost about 4 KB, most of it a map of maps and a key string that millions of classes repeated; a medium ν-net exhausted 20 GB before it closed. Classes now share one base object per (marking, zone, earliest-ready times) and one name layer per canonical key. The reachable quotient and the verdict are unchanged (`interned_keys_eq`); class indices, and which of several violating classes a counterexample trace reports, may differ from a non-interned build. The intern key carries the earliest-ready times on purpose: `StateClass` equality ignores them but the conflict-priority prune reads them, and sharing across that difference would have changed prune decisions. Class identity is the pair of intern ids for the same reason, so two arrivals that agree on marking, zone and name layer but disagree on those times stay two classes. Two regression tests in each language pin it.

---

### Lean

`Semiflow.lean` and `Interning.lean` are new. The semiflow union is sound for any list of gate-validated laws; at `k = 0` every transition touching a covered place is dead, so dropping them reaches the same markings; exploring a worklist from key-preserving representatives reaches the same keys and edges provided the successor step is key-equivariant, with a witness that a step reading past the key loses a class, which is the exact shape of the earliest-ready hole above. Forty-six theorems are gated in CI; 24 of 210 requirements carry a proof fragment.

---

### Spec

[VER-007] Invariant Strengthening from P-Semiflows is new and is the first spec statement of the exact invariant gate; [NU-053] gains AC6; [VER-012] records the interning contract; [VER-013] Solver Transport is new: one `z3` process per query, the reply contract, and byte-identical scripts across implementations. 208 → 210 active requirements.

---

## Java 3.0.1 / TypeScript 3.0.1 / Rust 4.0.1 / Python 3.0.1 — 2026-08-20

**Three fix sets on top of 3.0.0.** A fifth executor divergence is closed and the rule behind it now covers token counts and consumption, not just presence. And the verifier stops taking the solver's word for it: every `Proven` discharges its own certificate, every `Violated` replays its own counterexample, and untrustworthy invariants are dropped before they reach the encoder. And the diagram pipeline stops drifting: the published TypeDoc plugin no longer embeds a viewer one build behind the one it ships beside, a failed mount says so instead of leaving an empty box, and every port now fails its build when its copy of the viewer bundle goes stale. Java, TypeScript and Rust are covered; Python inherits every Rust fix through the PyO3 bindings.

---

### Executor

#### Fixed — a transition's own output no longer revives its competitors mid-pass (Java, Rust, Python)

Within one firing pass, tokens produced by a synchronous action were visible to the enablement recheck of transitions still waiting to fire in that same pass. A higher-priority transition that drained a place and refilled it from its own output therefore let a lower-priority competitor through, where the reference executor kept it disabled until the next cycle. Outputs deposit in step 1 and firing is step 5, so the pass judges losers against consumption alone ([EXEC-001], [EXEC-003] AC3).

```java
// t_high (priority 1): consumes one(a), resets b, action produces one token to b
// t_low  (priority 0): consumes one(a), reads b
// marking: a = 3 tokens, b = 1 token

// before (compiled executors): t_high, t_low, t_high   ← t_low saw the refill
// now  (every executor):       t_high, t_high, t_high  ← t_low starves, as intended
```

Final markings were identical either way, so only firing order and starvation changed — which is why marking-based assertions never caught it. **In Java both compiled executors were affected, including `BitmapNetExecutor`**, the reference the other is checked against. TypeScript was already correct on both executors.

The rule governs token *counts*, not just presence ([EXEC-003] AC4): an `exactly(n)` or `atLeast(n)` gate re-evaluated during the pass no longer counts a same-pass deposit either, and a ν-correlated join whose input place received one waits for the next cycle. The first fix only hid the presence bit, so a place that already held a token still leaked its refill to a cardinality gate.

It also governs *consumption* ([EXEC-003] AC5). A draining arc — `all()`, `atLeast(n)`, or a reset — firing later in the same pass takes only the tokens the pass started with; a token deposited during the pass survives it and is there next cycle. Otherwise a gate that correctly refused to count a same-pass deposit would still swallow it. Deposits land at the tail of the FIFO queue, so the tokens taken are exactly the head prefix.

The visible case is a reset racing a producer in one pass:

```python
# emit: one(seed) -> data, action deposits three tokens
# reset_data: one(trigger), reset(data) -> cleared
# both are enabled at the start, so both fire in the first pass

# before (Java, Rust, Python): data == 0   ← the reset swallowed tokens it could not see
# now  (every implementation):  data == 3   ← they land next cycle, as TypeScript always did
```

TypeScript is unchanged here and always reported `3`: its outputs resolve on a promise, so they were never in the place when the reset ran. If you relied on a same-pass reset clearing a producer's output, put the reset in a later cycle.

If a net of yours depends on a competitor running in the same pass as the transition that refilled its place, it now waits one cycle.

---

### Verification

#### Fixed — invariants that cannot be trusted are no longer used (Java, TypeScript, Rust, Python)

**Re-run any proof you rely on.** The P-invariants the verifier computes are conjoined into the solver query to narrow its search, so a wrong one removes reachable states and manufactures a proof. Two ways that happened:

- The computation ran in floating point (TypeScript) or unchecked integers (Java, Rust). Every invariant is now re-derived in exact arithmetic and dropped if it does not check out. This caught a live Java defect where an unchecked `int` cast emitted corrupted weights once the true weight exceeded 32 bits.
- The incidence matrix linearises `all()` and `atLeast()` and omits reset drains entirely, so an invariant could be numerically perfect and still wrong about what firing does. Invariants carrying weight on a consume-all, at-least, or reset place are now rejected outright.

Dropped invariants are named in the report with the reason. Dropping only costs the solver a hint; it can never change a correct verdict.

#### Added — `Proven` is now a checked certificate, `Violated` a replayed trace (Java, TypeScript, Rust, Python)

The inductive invariant returned by IC3 used to be printed and otherwise ignored. It is now discharged against three conditions — initiation, consecution, and safety — before the verdict is returned, with the P-invariants re-proven as part of the candidate rather than assumed. Counterexamples are replayed against the net's own semantics, so a trace is reported in firing order instead of solver traversal order, and carries a confirmation flag.

Anything that fails downgrades to `Unknown` naming the condition, rather than reporting a verdict nobody checked:

```
=== RESULT ===
UNKNOWN: certificate check failed: consecution (VC2) was not UNSAT - solver returned
SATISFIABLE (witness: p0=2, p1=1); the IC3 certificate could not be independently
re-validated against the unstrengthened step relation, so PROVEN is withheld
```

The downgrade wording, the dropped-invariant reasons and the replay search are the same in all four implementations — literally the same text, so a disagreement between them is greppable rather than a matter of interpretation.

Both are on by default. `certificateCheck(false)` and `counterexampleReplay(false)` opt out per verifier (`certificate_check=False` / `counterexample_replay=False` on Python's `verify_net`); the cost is a few extra solver queries on an already-slow path.

**Source break (Rust, Python).** The replay is now the only source of a counterexample trace. The old decoder turned the solver's answer into an unordered pile of markings and labelled it a trace; it is gone, so with `counterexample_replay(false)` the trace comes back empty rather than arbitrarily ordered.

A shared fixture set (`spec/verification-fixtures/`) pins twelve net-and-property pairs to an expected verdict, so the four implementations cannot quietly disagree about an answer. Each language builds the nets from the same JSON contract and asserts the same verdict, Python included.

**Source break (Rust).** `VerificationResult` and `VerificationStatistics` gained fields and are now `#[non_exhaustive]`, so construct them from the verifier rather than by struct literal. `counterexample_confirmed` is `Option<bool>`: `None` when replay did not apply, `Some(false)` when it ran without confirming.

#### Fixed — `deadlock-free` with sink places follows the spec (Rust, Python)

[VER-002] defines the error condition as "(all transitions disabled) ∧ (no sink place has a token)". Java and TypeScript encoded exactly that. Rust encoded the opposite reading — a violation whenever some *non*-sink place still holds a token — in its SMT encoder, its ν-aware coloured encoder, and its counterexample replay. The two answers differ on a quiescent marking holding tokens in both a sink and a non-sink (Rust called it a violation; the spec does not) and on a net that drains completely (the spec calls it a violation; Rust did not). No fixture declared sink places, which is why nothing caught it. Two now do, in all four implementations.

---

### Lean

Since extended to the ν-match cache (`match_cache_lockstep`), the deadline-reap disagreement between the two backends, and the soundness of invariant strengthening — that last one is where the `all()` / `atLeast()` guard above came from: the proof would not close without a hypothesis the code never enforced. Thirty-seven theorems are gated in CI through `#print axioms`.

Two supporting artefacts ship with it. `lean/fidelity.toml` pins every shipped Rust function the proofs model, and CI fails when one changes until the model is re-checked, so a proof cannot quietly stop describing the code. `spec/coverage-matrix.md` is generated per requirement and states plainly what is proven, what is only mentioned, and what is merely tested — 21 of 208 requirements carry a machine-checked fragment today, each with a note saying what it does not claim.

---

### Diagrams

#### Fixed — the published TypeDoc plugin shipped a viewer one build behind (TypeScript)

`tsup`'s `onSuccess` copied the doclet's viewer resources into `dist/` before it built the IIFE bundle, so every published build paired a current viewer with a plugin embedding the previous one. `dist/` is what npm ships, so the lag was permanent rather than local. The copy now comes from the freshly built bundle.

#### Fixed — a failed diagram mount left an empty box (Java, TypeScript)

The init snippets wrapped an async `mount()` in a synchronous `try`/`catch`, so a rejection went unhandled and the page showed nothing at all. All three doc generators now paint a visible `.libpetri-diagram-error` message, bound their wait for the viewer bundle, and record which bundle drew the page in `data-libpetri-viewer` on the diagram container. Rust also stopped sharing one `var` binding across its mount loop, which sent every diagram's handle to the last container.

#### Changed — `libpetri/render-dom` renders through the canonical viewer (TypeScript)

`renderDotToContainer()` pinned Graphviz `engine: 'dot'` and drew diagonal spline edges while every first-party surface drew orthogonal ones. It now delegates to `mount()`, with the same signature and return shape. `dotToSvg()` from `libpetri/doclet` and a raw `dotExport()` piped to your own `dot` stay stock Graphviz by design; the README now states which path yields which.

The viewer's ELK stage is loaded on demand, so `mount(dot, el, { layout: 'graphviz' })` genuinely works without `elkjs` installed. Under the previous static import the whole module failed to load and the documented fallback was unreachable.

#### Added — drift gate on the mirrored viewer bundle (Java, TypeScript, Rust)

`scripts/build-viewer.sh` records the bundle digests in `spec/viewer-bundle.sha256`, and each port tests its own copy of `petrinet-diagrams.{js,css}` against them. A mirror left on an older bundle now fails that port's build instead of quietly rendering a stale viewer.

---

### Spec

`EXEC-003` gains AC3, AC4 and AC5: a loser is judged against the marking as consumed by earlier firings in the pass but before any tokens their synchronous actions produced; the rule governs token counts, not only presence; and a draining arc takes only the pass-start prefix. No requirement ID is added — the count stays 208.

---

## Java 3.0.0 / TypeScript 3.0.0 / Rust 4.0.0 / Python 3.0.0 — 2026-08-17

**A major version on every channel.** Three sets of changes land together. The production executor now behaves exactly like the reference executor: four divergences the differential suite never reached are closed. The verifier no longer returns `Proven` for nets it was analysing unsoundly. And two long-deprecated surfaces are gone: input guards in TypeScript and Rust, and Java's `NetExecutor`. Java, TypeScript and Rust are all covered; Python inherits every Rust fix through the PyO3 bindings.

Every channel carries at least one break, which is why all four take a major bump rather than the minor these waves usually get. If you only read one section, read *Verification* below: a `Proven` result from an earlier version may not hold.

---

### Executor — the production backend now matches the reference

The `PrecompiledNetExecutor` must be behaviorally identical to the `BitmapNetExecutor` reference. It wasn't, in four places. Each divergence is fixed, covered by new differential tests, pinned by new spec acceptance criteria, and retrodicted as a machine-checked counterexample in `lean/`.

#### Fixed — same-priority firing order now follows enablement time (Java, TypeScript*, Rust, Python)

When two transitions with equal priority were enabled in *different* cycles and became ready together, the precompiled executor fired them in declaration order instead of enablement order (EXEC-002: earliest enabled fires first). The per-priority ready queues now sort their occupied slice by `(enablement time, declaration order)` before draining. The fast path for all-immediate single-priority nets is untouched — it fires in declaration order on every backend, by design, and EXEC-002 AC4 now says so. The general path adds only an in-place sort of the few concurrently-ready transitions. *TypeScript already ordered correctly and is unchanged.

#### Fixed — a `read` arc sharing a place with a `reset` arc now sees the token (Java, TypeScript, Rust, Python)

The precompiled executor drained reset arcs before peeking read arcs, so a transition with both on one place found the place already empty and the firing failed. Reads now peek between input consumption and reset draining, matching the reference (EXEC-013 AC4):

```ts
Transition.builder('t')
  .input(one(trigger))
  .read(read(status))    // now observes the pre-reset front token
  .reset(reset(status))  // then drains
```

#### Breaking — two input arcs on one place are rejected at compile time (Java, TypeScript, Rust, Python)

`.input(one(p)).input(one(p))` never had coherent semantics: the reference executor silently under-consumed, and the precompiled executor corrupted its token rings (Rust panicked). Compilation now fails with a descriptive error (CORE-030). Use a single arc with `exactly(n)` / `atLeast(n)` instead.

Arcs that collide only because a fusion set merged their places or channel composition merged their transitions still merge, so nets that built before still build:

```
one        + one         →  exactly(2)
one        + exactly(n)  →  exactly(n + 1)
exactly(n) + exactly(m)  →  exactly(n + m)
all        + all         →  all
atLeast(n) + atLeast(m)  →  atLeast(max(n, m))
```

Anything else (`one` + `all`, `exactly` + `atLeast`) is rejected at build, naming the seam, both cardinalities and the place:

```
Fusion set 'limiter': input arcs one() and all() collide on place 'slots' and have no
additive merge (MOD-021 rule (c)). Use a single arc with exactly(n) / atLeast(n).
```

#### Breaking — channel composition rejects mismatched arc kinds on one place (Java, TypeScript, Rust, Python)

Merging a caller transition with an instance channel used to union the two arc sets blindly, so a caller `input(P)` meeting an instance `read(P)` — or worse, `reset(P)` — produced a transition with no coherent firing semantics. MOD-021 rule (d) has always called that a conflict; nothing enforced it. Now it throws:

```
Channel composition 'attempt': conflicting arc kinds on place 'slots' — caller-side
[input] vs instance-side [read]. Different arc types on one place cannot be merged
(MOD-021 rule (d)). Resolve explicitly.
```

Sides that declare the *same* set of kinds on a place are unaffected — those reconcile pairwise as before. If a composition of yours built before this release and now throws, one side is testing a place the other consumes; give them separate places.

#### Fixed — tokens on places the net doesn't declare are no longer lost (Java, TypeScript, Rust, Python)

Three seams can hand an executor a token for a place the compiled net doesn't know about, and all three behaved differently. An **initial marking** naming an undeclared place lost those tokens on the precompiled executor while the reference kept them; on the **produce** and **inject** seams the reference executor *threw* `Unknown place`. All three seams now retain the tokens in the observable marking on every backend (CORE-072): inert — no arc can touch them — but never dropped and never fatal.

The first token to reach a given undeclared place is reported once per executor, as a `WARN` log-message event on logger `libpetri.runtime`, so retention is not silent.

#### Lean — the engine hot loop is now formalized

`lean/` grew a second axis beyond verifier-abstraction soundness: the flat ring-buffer token pool at full fidelity. It proves `token_conservation` — every pre-fire token is delivered, reset-destroyed, or surviving, as an order-preserving list equality — plus dirty-set soundness (CONC-005), the Bitmap/Precompiled refinement on the immediate fragment, and the ready-ordering theorem behind the firing-order fix. All four pre-fix divergences ship as `decide`-checked witnesses. Every definition names the shipped Rust function it models. `lake build` stays dependency-free and CI-gated (`sorry` grep + `#print axioms`).

---

### Verification — no more false `Proven`

#### Fixed — false `Proven` on `all()` / `atLeast()` inputs (Java, TypeScript, Rust, Python)

If you use `lp.verify(...)` / `Verifier` / `verify()` on nets with `all()` or `atLeast()` inputs, re-run your proofs — a `Proven` result from an earlier version may not hold.

**The state-class graph consumed one token where the executor drains the place.** `all()` and `atLeast()` inputs take every matching token when they fire, but the state-class graph subtracted a single token from the successor marking. Every state reached *after* such a firing was therefore computed against a marking that still held tokens the executor had already consumed — so a downstream inhibitor arc looked permanently blocked, and states the executor really reaches were reported unreachable.

```java
// p holds 3 tokens; t drains it
Transition.builder("t").input(In.all(p)).output(Out.place(q)).build()
// after firing: executor leaves p empty, the SCG used to leave 2 tokens in p
// → any transition inhibited by p was pruned from the graph
```

This affected timed reachability (`StateClassGraph`, `VER-010`) and the ν-partition quotient (`VER-012`) in all three implementations. All three now route the successor computation through the single `consumptionCount` definition of `IO-007`.

#### Breaking — input guards removed (TypeScript, Rust, Python)

Input arcs no longer carry a per-token value predicate. `IO-006` removed guards from the specification in February; Java had already dropped them, while TypeScript and Rust kept shipping them — this release finishes that change.

The removed surface:

```rust
// Rust — gone
one_guarded(&p, |v: &Msg| v.ready)
exactly_guarded(2, &p, ...)
all_guarded(&p, ...)
at_least_guarded(2, &p, ...)
```

```ts
// TypeScript — the optional second/third guard argument is gone
one(p, (v) => v.ready)
exactly(2, p, (v) => v.ready)
all(p, (v) => v.ready)
atLeast(2, p, (v) => v.ready)
```

`In::has_guard()` / `In::guard()` and the `GuardFn` type are removed in Rust; the `guard` field is removed from every input-spec variant in both languages, and TypeScript's `GuardSpec` is renamed `PredicateSpec`.

**Why.** A guarded `all()` consumed only the matching tokens, but the SMT encoder never inspected guards and emitted "place emptied" for every consume-all input. The abstract successor was *smaller* than the concrete one — an under-approximation, which is exactly how a place-bound query returns a false `Proven`. Guards were unsound in combination with verification and had no encoder-side fix that preserved them.

**Migrating.** There is no drop-in replacement — this is deliberate ([NU-021]). Filter inside the action and re-emit, or model the distinction structurally:

```ts
// before
.input(one(inbox, (m) => m.priority === 'high'))

// after — route at the producer, so the net structure carries the distinction
.input(one(highPriorityInbox))
```

On correlated (ν) inputs, name equality remains the per-token filter and is unaffected.

#### Breaking — output specs are enforced at runtime (Rust, Python)

`IO-015` validation now runs on every firing. Java and TypeScript already did this; Rust (and therefore Python) treated the output spec as documentation.

```python
.output(lp.and_(lp.out(a), lp.out(b)))   # declares BOTH
# action writes only to `a`:
#   before → accepted, one token lands in a
#   now    → firing fails, NOTHING is deposited, inputs stay consumed
```

A violation emits `TransitionFailed` carrying the diagnostic — `[IO-015] 't': output does not satisfy declared spec (expected and('a', 'b'), produced ["a"])`. Under the default no-op event store it is silent, exactly as an action that raises is silent; pass an event store to observe it.

Validation is by *place*, not by token count: `out(P)` still permits an action to emit any number of tokens to `P`.

The most common way to trip this — declaring an output and never binding an action — is already a compile error as of [CORE-043] in the previous release. What this check adds is the case no static analysis can decide: a hand-written action that produces nothing, or produces on only some paths.

**`ctx.flush()` is an atomicity boundary** (Rust and Python only; Java and TypeScript have no equivalent). Places written by a published batch count towards satisfying the spec — a streaming action that flushes its `chunk` branch and writes `done` at completion satisfies `and(chunk, done)`. But published tokens are *not* withdrawn when validation later rejects the firing: flush one half of an `and` and return without the other, and the violation is reported while the flushed token stays in the marking. This was previously unspecified; [IO-015] now states it (AC7). An action needing all-or-nothing output must not flush.

To keep the previous behaviour:

```python
lp.run_sync(net, options=lp.ExecutorOptions(skip_output_validation=True))
```

which brings us to —

#### Fixed — `skip_output_validation` was inert (Rust, Python)

The builder accepted the flag and dropped it, so the documented escape hatch did nothing, in both `PrecompiledExecutorBuilder` and Python's `ExecutorOptions`. Java and TypeScript honoured it throughout. It now works everywhere.

#### Fixed — `Out.ForwardInput` forwarded one token (Java, TypeScript)

A batched input paired with `forwardInput` re-emitted a single token instead of one per token consumed, silently destroying the rest. Rust was already correct.

```java
.input(In.all(p))            // consumes 3 tokens
.output(Out.forwardInput(p, q))
// before: q receives 1 token   now: q receives 3, in consumption order
```

#### Fixed — XOR branch ambiguity resolved consistently (TypeScript)

When several `Out.Xor` branches match and one subsumes all the others — `and(a, b, c)` against `and(a, b)` — the most specific branch is selected rather than the firing being rejected. Java already did this and Rust gained it here; TypeScript was the outlier. Genuinely overlapping branches (`and(a, b)` vs `and(b, c)`) remain a violation.

#### Added — `lean/`, a machine-checked soundness development

A dependency-free Lean 4 development (`lake build`, no Mathlib) proving **Proposition 1** — `α(R(N)) ⊆ R(N̂)`, that the verifier's untimed abstraction really over-approximates the executor — with decidable counterexamples showing the side conditions cannot be dropped, and models retrodicting two historical false-`Proven` defects. CI builds it and rejects `sorry`/`admit`.

---

### Java — `NetExecutor` removed

`NetExecutor`, deprecated in 2.13.0 with `forRemoval = true`, is deleted. It walked the `PetriNet`
directly instead of compiling it, so it was the one Java executor whose firing path was not covered
by the bitmap/precompiled differential suite, the same suite that found the four divergences above.

Replace it with `PrecompiledNetExecutor` (production) or `BitmapNetExecutor` (reference). Both carry
the same `create(...)` / `builder(...)` surface, so the migration is a type rename:

```java
// before
try (var executor = NetExecutor.create(net, initial)) { ... }

// after
try (var executor = PrecompiledNetExecutor.create(net, initial)) { ... }
```

The JMH suite loses its `ref_*` benchmark arms and the report's `Reference` column with it.

---

### Spec

209 → 208 active requirements. `EXEC-011` (Guarded Token Consumption) tombstoned alongside `IO-006`. `NU-021` retitled *Match as the Sole Per-Token Filter*, fixing the composition order should a unary filter ever return. `IO-014`, `IO-015`, `VER-004`, `VER-010` and `VER-012` amended; `CONC-007` / `CONC-008` retargeted.

The executor fixes added acceptance criteria only — no new requirement IDs, so the count is unchanged. `EXEC-002` AC3/AC4 pin the cross-backend ready order and carve out the all-immediate fast path (mirrored in `CONC-023` AC4); `EXEC-013` AC4 pins read-before-reset; `CORE-030` AC3 pins duplicate-input rejection; `CORE-072` AC3/AC4 pin unknown-place retention and its `WARN` diagnostic. `MOD-021` now carries the canonical input-arc merge table, which `CORE-030` and `MOD-061` reference instead of restating.

## Java 2.14.0 / TypeScript 2.13.0 / Rust 3.7.0 / Python 2.16.0 — 2026-08-03

**A transition that declares an output but can never produce one now fails to compile ([CORE-043], new).**

Originally reported and prototyped by [@mpetris](https://github.com/mpetris) in #55.

The builder's default action is `passthrough()`, which produces nothing, so a transition declaring
`Arc.Out` that never binds an action consumes its input and produces nothing on every firing — and
verification never caught it, because the state-class graph and SMT encoding read production from
the `Arc.Out` spec, not from the bound action. Compiling *or verifying* such a net now fails,
naming the transition: bind an action that produces the output (`fork()` moves the input token
across), or drop the spec if the transition is a sink. The check is unconditional, so this is a
deliberate break for nets that ran under `skipOutputValidation`.

Also in this release:

- `TransitionAction.passthrough()` (Java) returns a singleton, and `isPassthrough(action)` is now
  public in Java, TypeScript and Rust (Python has no such predicate; the check runs Rust-side).
- Java's subnet channel merge collapses `passthrough()` instead of wrapping it, matching TypeScript
  and Rust, so a merged transition that produces nothing stays recognisable.
- **Fixed:** three Rust benchmarks (`single_passthrough`, `precompiled_single_passthrough`,
  `owned_single_passthrough`) declared an output while bound to `passthrough()`, so they measured
  the validation-failure path rather than the minimum-overhead path they name.

## TypeScript 2.12.1 — 2026-07-26

**Executor hardening: failure containment + timeout output isolation (ports the Java fixes).**

- **Failure containment.** A synchronous failure during a firing — a throwing `EventStore.append`, an action that throws before returning its promise, or one returning a non-thenable — now fails only that transition (emitting `transition-failed`) instead of unwinding the orchestrator loop and rejecting `run()`. Event emission is swallowed at a single guarded choke point so a throwing store cannot escape.
- **Timeout output isolation.** `Out.Timeout` now detaches the action's context and produces the timeout branch into a fresh collector, so output the action wrote before the budget expired is discarded rather than merged with the timeout branch (previously a spurious `Xor` "multiple branches" violation, or a doubled token under `And`). Applies to `BitmapNetExecutor` and `PrecompiledNetExecutor`.

Closes the [EXEC-030] / [IO-013] divergence tracked in `spec/00-index.md`; the lifecycle surface ([ENV-015]/[ENV-016]) remains a Java-only follow-up.

## Java 2.13.0 — 2026-07-26

**Executor hardening: failure containment, timeout isolation, observable lifecycle, safe cross-thread `marking()`.**

Three defects could kill or corrupt a running net, all reachable without concurrency. Actions are invoked inline on the orchestrator thread (the javadoc, `README.md` and `CLAUDE.md` had claimed a task pool); the fixes and doc corrections apply to `BitmapNetExecutor`, `PrecompiledNetExecutor` and `NetExecutor`. Spec updated: [IO-013], [EXEC-022], [CONC-002], [CORE-071] amended and [ENV-015]/[ENV-016] added; the TypeScript port of the containment and timeout fixes is tracked in `spec/00-index.md` as a follow-up.

Fixes:

- **Failure containment.** An unchecked throw from a firing (a synchronous action throw, a `null` return, a `CancellationException` that `join()` rethrows unwrapped, a throwing `EventStore.append`) now fails just that transition instead of unwinding the loop. Consumed tokens are lost per [EXEC-031], the transition is marked dirty, and both the presence bitmap and the ν fast-path match cache are reconciled so a throw mid-consume cannot leave a phantom token or a desynced correlation matcher (which would otherwise silently wedge a ν join into false quiescence). `Error` (OOM, `StackOverflowError`) is repaired and rethrown to terminate the run rather than being retried. Termination bookkeeping runs in a `finally` and completes even if the final event emit throws, so `awaitTermination` cannot hang.
- **Timeout isolation.** `Out.Timeout` detaches the action's `TransitionContext` and harvests a fresh collector the action cannot reach, so a late write from an abandoned action can no longer surface in the next firing (previously reachable on the pooled `PrecompiledNetExecutor` context). Timeout transitions get a fresh context per firing; everything else keeps the zero-allocation path. The budget branch is selected by provenance, so a `TimeoutException` the action itself raises is an ordinary failure, not the declared branch. The timer arms a `copy()` of the action's future, never the caller's, and no longer calls `cancel(true)` (which did nothing).
- **`marking()` cross-thread.** Reading `marking()` from a monitoring thread while the loop ran corrupted the live net (`PrecompiledNetExecutor` cleared and rebuilt the shared marking off-thread). The orchestrator now publishes an owned best-effort snapshot for foreign readers; on its own thread, or once stopped, `marking()` returns the exact live marking as before. `Marking.copy()` is orchestrator-only.
- **`inject()` / lifecycle.** `inject()` after termination completes `false` rather than hanging; the post-enqueue recovery no longer discards already-queued events under a concurrent `drain()` ([ENV-011]). `close()` shuts down the `ExecutorService` only when the executor created it.

New API (all `PetriNetExecutor` additions are `default`):

- `Builder.uncaughtActionHandler(ActionFailureHandler)` on every executor: an out-of-band sink for action failures, since the default `EventStore.noop()` makes the `TransitionFailed` event (and the token loss) silent. libpetri logs at WARNING only when no store actually recorded the failure; a configured handler is always invoked, and one that throws is swallowed.
- `run(Duration, RunTimeoutPolicy)` (`ABANDON` keeps the historical behaviour and is the default; `CLOSE` stops the loop), `awaitTermination(Duration)`, and `terminateNow()` (stop without waiting for in-flight actions; an explicit escape hatch from [ENV-013], never invoked by `close()`).

Deprecations:

- `Builder.executor(ExecutorService)` renamed to `orchestratorExecutor(ExecutorService)` on `BitmapNetExecutor`/`PrecompiledNetExecutor` (the old name delegates; `NetExecutor.Builder.executor` keeps its name with corrected docs). It hosts the loop, not action dispatch.
- `NetExecutor` (superseded by `PrecompiledNetExecutor` and `BitmapNetExecutor`), `TransitionAction.withTimeout` (cannot stop an action; use `Arc.Out.timeout`), and `BitmapNetExecutor.create(net, initial, eventStore, executor)` (use the builder), all `forRemoval` in 3.0. `TransitionContext.scopedValue()` is deprecated (it exposes `ScopedValue` in the signature) but not yet `forRemoval`, pending a libpetri-owned carrier.

Cleanups: removed the write-only `AtomicLongArray markedPlaces` and the per-poll `CompletableFuture.anyOf` (completion already signals via the lock-free queue plus semaphore); corrected three bogus `@SuppressWarnings("deprecation")`; added the first `Out.Timeout` JMH benchmarks.

## Java 2.12.0 / TypeScript 2.12.0 / Rust 3.6.0 / Python 2.15.0 — 2026-07-14

**Feature: scalable exact ν-net deadlock-freedom (NU-052 + NU-053), with full-precision soundness**

Two opt-in additions to ν-net verification, plus the soundness hardening that makes them exact. Rust is the source of truth; Java and TypeScript port it byte-faithfully and Python inherits it through the Rust runtime. Defaults are unchanged.

- **NU-052 — conflict-only priority for the name state-class graph (Route B).** An opt-in `PrioritySemantics{NONE,CONFLICT}` prunes the interleavings the eager, priority-ordered executor never produces, so Route B stops reporting spurious drain-steal stalls. `NONE` stays the default and reproduces prior behaviour byte-for-byte. Pruning is DBM-precise: it fires only when the higher-priority transition is ready no later than the lower in the class's zone (`readyEarliest[H] <= readyEarliest[L]`), and only under real token competition on a shared consumed input.
- **NU-053 — EXTENDED-coloured quiescence in the Route A SMT/IC3 encoder.** `DeadlockFree` / `JoinedOrDeadLettered` are decided by a colour-aware deadlock predicate over the EXTENDED fragment (coloured relays/drains and carrier places), with XOR output branches classified independently. The verifier defers to Route A when Route B truncates, and does not downgrade an exact coloured verdict.
- **Structural colour bound (soundness).** The colour-slot count is now a non-negative P-semiflow bound (`Σ coloured M ≤ y·M0`) rather than the raw initial budget, so a fork whose colour outlives its refunded budget can no longer under-approximate into a false `Proven`. A net with no covering semiflow (a genuinely unbounded colour leak) falls back to the sound over-approximation.
- **Fixes:** an unresolved property place now reports `Unknown` instead of a vacuous `Proven`; the conflict-priority guard no longer prunes a name-disabled join or a non-competing shared place.

## Java 2.11.0 / TypeScript 2.11.0 / Rust 3.5.0 / Python 2.14.0 — 2026-07-09

**Feature: opt-in EXTENDED ν-net fragment (drain/relay + fork-threaded co-mint) (NU-051)**

The Route B name-partition quotient ([NU-050] / [VER-012]) gains an opt-in EXTENDED mode that decides two further ν-net shapes exactly, without weakening its soundness. BASE stays the default and reproduces the shipped mint → matched-join behaviour. Rust is the source of truth; Java and TypeScript port it byte-faithfully and Python inherits it through the Rust runtime.

- **Coloured consumer (drain/relay):** a non-match transition may consume a coloured place, relaying the correlation name into its coloured outputs or draining it (dead-letter). It is admitted only when it consumes a single coloured input at count exactly one, and the role carries just the input place name.
- **Carrier places:** authors may declare intermediate places that thread a fork-minted name to a ν-join input (`carrierPlaces` / `carrier_place(s)`); the mint co-mints one fresh name into them. An unknown carrier name fails loudly (builder rejection or `Unknown` with a reason) instead of silently producing a spurious deadlock.
- **Sound by construction:** the relay emits exactly one symbol per coloured output, matching the base marking's one-token-per-output rule, so the name layer never over-counts or equates two distinct names into a false PROVEN. The consumer is admitted only at count exactly one, so no base-enabled firing is dropped.
- **Reset/read/inhibitor-on-coloured tightening now applied in BASE too:** a net with a reset, read, or inhibitor arc on a coloured place is rejected to the sound over-approximation in both modes, closing a pre-existing name-layer drift.
- When EXTENDED is requested but the net falls outside the fragment, the verifier surfaces a short "EXTENDED declined" note rather than falling back silently.

## Java 2.10.5 / TypeScript 2.10.5 / Rust 3.4.5 — 2026-07-08

**Viewer: orthogonal (right-angle) edge routing**

The canonical Petri-net viewer now draws its own orthogonal edge routes rather than letting Graphviz route them. It renders the pinned graph with engine `nop2` and supplies each edge's ELK route as a `pos=` spline clipped to the visual node boundary, so edges turn at right angles on a net of any size. This replaces the prior `nop1` mode (curved edges): Graphviz's own `splines=ortho` router is avoided because its maze allocator overruns the @viz-js/viz wasm heap and hard-crashes on large nets.

- Arcs sharing an endpoint bundle into a common trunk (`elk.layered.mergeEdges`) so dense fan-in/out reads as one labelled bus. Accepted trade-off (EXP-004): collinear arcs over-paint along the shared trunk, while arrowheads and labels keep each arc type distinct at the endpoints.
- The shared `petrinet-diagrams.js` bundle (Java taglet, Rust `libpetri-docgen`, TS doclet) is rebuilt from the pinned toolchain; no mapper-DOT or spec change.

## Java 2.10.4 / TypeScript 2.10.4 / Rust 3.4.4 / Python 2.13.2 — 2026-07-02

**Fix: ν-net join match dropped by `bindActions` (NU-030)**

Follow-up to 2.10.3, which fixed the composition drop sites (`mergeTransitions`, `rebuild_with_name`) but missed a third: binding actions rebuilds every transition (`rebuildWithAction` / `rebuild_with_action`) to attach its action, and the Java and TypeScript path never carried `matchSpec` forward. A net composed with an intact ν-net join lost its correlation the moment actions were bound, reverting a correlated join-by-id to a plain FIFO AND join at runtime (pairing tokens by arrival order across overlapping fork/join generations, a stale cross-group result). A bind renames no places, so the match is carried as-is, unlike the compose/rename rebuild.

- **Java / TypeScript:** the action-bind rebuild now carries the transition's `matchSpec`. Rust already carried it, so this locks the behaviour in with tests; Python inherits through the Rust runtime.
- Regression tests added across all four languages: a structural check that a bound transition keeps its match, and a behavioral check that a bound matched join pairs by name, not FIFO (both executor backends where applicable).

## Java 2.10.3 / TypeScript 2.10.3 / Rust 3.4.3 / Python 2.13.1 — 2026-07-01

**Fix: ν-net join match dropped during modular composition (NU-030 / NU-060)**

Composition could silently drop a ν-net join's correlation (`matchSpec` / `match_spec`), reverting a correlated join-by-id to a plain FIFO AND join. At runtime that pairs tokens by arrival order instead of by name, so an overlapping fork/join could serve a stale cross-group result.

- **Rust / Python:** the rename/substitute rebuild (`rebuild_with_name`) never carried `match_spec`, so any ν-net join inside a port-composed or instantiated subnet lost its match (a violation of the NU-030 MUST). The match now follows the same place rewrite the arcs do. Python inherits the fix through the Rust runtime.
- **Java / TypeScript / Rust:** the channel-merge path (`mergeTransitions` / `merge_transitions`) dropped the match on fusion. It now carries a surviving one-sided match forward, and rejects a merge where both sides carry a match rather than silently dropping one (NU-060). The MOD-031 declared-to-actual place map is carried through the merge too, so a merged transition's composed action still resolves its declared place constants.
- Regression tests added across Java, TypeScript, Rust, and Python, including a behavioral test that a composed matched join pairs by name, not FIFO.

## Java 2.10.2 / TypeScript 2.10.2 / Rust 3.4.2 — 2026-06-26

**Fix: bundled viewer WASM rendered blank in rustdoc-embedded diagrams**

The doc generators inline `petrinet-diagrams.js` as a `<script>` inside a Markdown doc comment. @viz-js/viz embeds the Graphviz WASM as a string whose bytes include raw newlines; when the doc comment isn't a clean leading HTML block (e.g. it has preceding `///` prose), rustdoc's Markdown renderer collapsed those newlines, dropping WASM bytes and producing `CompileError: signature index out of range` in every browser.

- The viewer bundle is now built with esbuild template-literal lowering + `lineLimit`, so no raw newline lands inside a string literal and lines stay short (rustdoc no longer scans multi-megabyte lines). The bundle is pure ASCII and survives Markdown inlining unchanged.
- `check-viewer-wasm.mjs` gains a Markdown-resilience gate: it re-validates the embedded WASM after a newline-collapse pass, so a regression that reintroduces raw newlines fails the build.
- Verified by regenerating the downstream consumer's rustdoc page with the rebuilt asset: the diagram renders in Chrome 145 with no errors.

## Java 2.10.1 / TypeScript 2.10.1 / Rust 3.4.1 — 2026-06-26

**Doc-generator viewer bundle: WASM validation + anti-drift CI gate**

The baked Graphviz-WASM in the shared `petrinet-diagrams.js` (Java taglet, Rust `libpetri-docgen`, TS doclet) is now validated before it can ship — closing the gap where a corrupt bake renders blank docs but passes all unit tests (which mock `@viz-js/viz`).

- **Build gate:** `npm run build:viewer` now runs `check-viewer-wasm.mjs`, which `WebAssembly.validate`s the WASM embedded in the built IIFE and renders a graph through `@viz-js/viz`. `scripts/build-viewer.sh` inherits it, so a bad bundle can't reach the resource dirs.
- **CI:** new `viewer` job builds the bundle, runs a headless-Chromium render smoke test (`smoke:viewer`, asserts an `<svg>` appears), and fails on viewer-asset drift (`git diff --exit-code`) — the committed assets must be the reproducible output of the locked toolchain.
- **Pinned + rebuilt:** `@viz-js/viz` (`3.28.0`) and `esbuild` (`0.27.3`) are exact-pinned so the bundle is reproducible; dependabot bumps are now gated by the checks above. The three resource bundles are rebuilt on the pinned toolchain, resolving prior 3.27/3.28 drift. No viewer behaviour change.

## Java 2.10.0 / TypeScript 2.10.0 / Rust 3.4.0 / Python 2.13.0 — 2026-06-11

**Amortised O(1) ν-join addition (monotonic FIFO fast-path)**

The `IncrementalMatcher` (ν-join correlation, both executors and all four bindings) now keeps ready names in a FIFO deque while they arrive in non-decreasing `(oldest-ts, name)` order, which is the canonical fork/join case and any time-ordered seed, making `add`/`consume` amortised **O(1)** (previously O(log n) on the heap insert). It migrates to the lazy-deletion min-heap on the first out-of-order push and re-enters the fast path once fully drained, so `best()` stays byte-identical to `selectMatchName` (NU-022) on arbitrary inputs. Semantics unchanged; Python inherits via the Rust runtime.

## Java 2.9.0 / TypeScript 2.9.0 / Rust 3.3.0 / Python 2.12.0 — 2026-06-10

**Incremental ν-join matcher: O(N²) → O(N log N) drain (NU-022)**

The correlated-join matcher no longer rebuilds a full name index over every token on each enablement check. For One/Exactly correlated inputs an `IncrementalMatcher` maintains, per input, a `MinQueue` (two-stack amortized-O(1)-min FIFO) of timestamps-per-name plus a lazy-deletion `(oldest_ts, name)` min-heap, so `add`/`consume` are O(log n) and `best()` is an O(1) read. Draining N ready correlation groups drops from O(N²) to O(N log N). Purely additive and semantics-preserving across all four bindings and both executors (bitmap + precompiled); AtLeast/All correlated inputs keep the reference `selectMatchName` path.

- **Determinism is now normative ([NU-022]):** the `(oldest-ts, then NameId)` tie-break is byte-identical across implementations, and the incremental `best()` returns byte-identical results to `selectMatchName`, verified by per-language 400-seed differential tests (`MatchEngineIncrementalTest`, `incremental_matches_select_byte_for_byte`, `incremental-matcher.test.ts`).
- **Benchmarks:** firing-check benchmarks (depth 10–500, arity 2–8, guarded, scatter-gather, budgeted, plus a plain-join baseline) added in Java (JMH), Rust (criterion), TypeScript (vitest), and Python (pytest-benchmark).
- Spec: new **NU-022** (Deterministic Match Selection) in `spec/12-nu-nets.md`, registered in the index.

## Java 2.8.0 / TypeScript 2.8.0 / Rust 3.2.0 / Python 2.11.0 — 2026-06-09

**ν-nets — correlated fork / join by identity (NU-001..060)**

A transition can mint an opaque correlation **name** (`ctx.freshName()` / `ctx.fresh_name()`) on a fork and **join by name equality**, re-merging exactly the sibling tokens of one forked unit of work — no correlation smuggled through mutable external state. Identity is a *projection of the token payload* (a `MatchSpec` declares a `value → NameId` key), so `Token`, the event log, and the v3 session-archive formats are unchanged — purely additive across all four bindings and both executors (bitmap + precompiled).

- **Model:** new `NameId` (opaque, equality-only) and `MatchSpec` (name correlation over a subset of a transition's input places). A transition with no match spec keeps the existing fast path, gated on a per-transition flag. The firing tie-break (`selectMatchName` / `select_match_name`) is byte-identical across languages.
- **Decidability ledger (NU-040):** a typed `Budget` place bounds live correlation groups — "≤ k live groups" is a structural `PlaceBound(Budget, k)` checkable with the existing LIA encoder. Safety/coverability is decidable; unbounded fresh names make reachability/liveness undecidable, stated honestly in-spec.
- **Verification (NU-050):** the SMT verifier is ν-aware. New `BranchPlaceBound` / `JoinedOrDeadLettered` properties; a budget-place declaration (`budgetPlaces(...)` / `budget_places=`) asserts the bounded fragment. The name-blind baseline over-approximates matched transitions (sound for `Proven` on reachability-safety bounds); on top of it all four bindings decide ν-join correlation **exactly** by two routes:
  - **Route A** (NU-050 #1): bounded name-colouring (`k` = budget) for budget-declared, untimed reachability-safety. Budget must be conserved across a mint→join pair; a budget-inflating net falls back to the over-approximation.
  - **Route B** (VER-012): a solver-free **name-aware state-class-graph name-partition quotient** for the cases Route A can't reach — quiescence, budget-less but structurally name-bounded nets, and name × time. Returns `Unknown` only on genuine unboundedness (graph truncation), never an unsound verdict. New `nuMaxClasses` / `nu_max_classes` knob.
- **Visualization (EXP-018):** correlated input edges render teal with a `⟨n⟩` name label alongside the cardinality label; identical across the three doc generators and debug-ui.
- **Python:** `verify(...)` gains an `initial_marking=` argument (the binding previously had no way to seed initial tokens).
- Spec: new `spec/12-nu-nets.md` (NU-001..060, with NU-050 Route A + Route B), new **VER-012** (name-aware state-class graph), plus index, I/O, verification, and export edits.

## Java 2.7.1 / TypeScript 2.7.1 / Rust 3.1.1 / Python 2.10.0 — 2026-06-05

**`bindActions` preserves the MOD-031 place correspondence (MOD-031 ∩ CORE-042)**

- Binding a transition's action *after* `instantiate` — the structure-only subnet + late-binding idiom (`instantiate(prefix).bindActions({…})`, then `compose(bindPort(…))`) — now keeps the declared→actual place correspondence established at instantiation. A hardcoded-constant action bound this way resolves its declared places and fires under composition, matching the baked-into-the-def path. The action-swap rebuild previously dropped the correspondence.
- **Java / TypeScript / Rust:** the action-rebind seam (`rebuildWithAction` / `rebuild_with_action`) now carries the correspondence (`placeAlias` / `local_name_map`) forward. No-op for hand-written / directly-composed transitions.
- **Python:** new `Instance.bind_actions(mapping)` (MOD-030) plus `NetBuilder.compose_instance(instance, bindings)` to compose a pre-bound instance — actions bound after `instantiate` resolve their author-local place names after the merge.
- Spec: **MOD-031** strengthened with an explicit binding-preservation requirement and acceptance criterion (`spec/11-modular-composition.md`).

## Java 2.7.0 / TypeScript 2.7.0 — 2026-06-05

**Action place resolution under composition (MOD-031)**

- A transition action MAY reference places by their **declared** (pre-instantiation, pre-port-binding) identity. After `instantiate(prefix)` and/or `compose(bindPort(...))`, the action-facing context (`input`/`inputs`/`read`/`output`) resolves a declared place to the actual composed place via a per-transition declared→actual correspondence. Hardcoded-constant actions — including `Out.xor` branch selection — now work unchanged under composition, where previously only port-agnostic (`ctx.inputPlaces()`) actions did. Place-set discovery (`inputPlaces`/`outputPlaces`) still returns the actual composed places.
- **Java / TypeScript:** new. `Transition` carries the correspondence (Java `placeAlias: Map<Place,Place>`; TS name-keyed), populated by the subnet rewriter — chaining correctly through nested instantiation ([MOD-013]) — and consulted by `TransitionContext`.
- **Rust / Python:** already shipped the mechanism (`Transition::local_name_map` + pyo3 adapter); MOD-031 formalises it in the spec and adds conformance tests.
- Spec: new requirement **MOD-031** in `spec/11-modular-composition.md` (Action Binding). Not consulted by enablement, firing, the verifier, the exporter, or events — [MOD-023] structural equivalence is unaffected.

## Java 2.6.1 / TypeScript 2.6.0 / Rust 3.1.0 / Python 2.9.0 — 2026-06-03

SMT verification is now sound on nets with environment places (VER-006), across all four bindings. TypeScript, Rust and Python additionally ship the `exact()` timing + deadline-tolerance fix here; Java shipped that in 2.6.0, so its 2.6.1 carries only the env-place fix.

**SMT verification — sound on environment places (VER-006)**

- **Environment injection in the SMT encoding.** Previously the CHC encoding never produced tokens into environment places, so env-gated transitions could never fire, the reachable set froze at the initial marking, and safety bounds (e.g. `placeBound`) were vacuously reported `proven`. The encoder now emits an injection rule per environment place — unbounded under `AlwaysAvailable`, capped under `Bounded(k)` — and P-invariant computation is made env-aware (injector columns added to the incidence matrix) so closed-net conservation laws are not misapplied to injectable places.
- **No silent vacuous proofs.** With environment places registered under `Ignore` (the Java/Rust default), a would-be `proven` is downgraded to `unknown` with guidance to use `AlwaysAvailable`/`Bounded(k)`. The structural siphon/trap deadlock shortcut is skipped when environment places are modeled, and the deadlock check treats injectable env inputs as satisfiable (a reactive net merely waiting for input is no longer reported as deadlocked).
- **TypeScript:** the SMT verifier's environment mode is unified with the spec's three modes — `alwaysAvailable()` / `bounded(k)` / `ignore()` (replacing the prior `unbounded()` / `bounded()`); the default is `alwaysAvailable()`. **Breaking** for code importing `unbounded` from the verification entrypoint.
- **Python:** `verify(...)` gains an `environment_mode=` argument with `always_available()` / `bounded(k)` / `ignore()` constructors (previously the mode could not be selected and silently defaulted to `Ignore`).
- **Rust:** the `z3`-feature SMT pipeline now produces correct verdicts (the SMT-LIB2 query and the sat/unsat→verdict mapping were corrected).
- Verdicts on env-place nets may legitimately change from `proven` to `violated` or `unknown` — this reflects the soundness fix, not a regression. Spec VER-006 amended.

**Timing — reliable `exact()` + configurable deadline tolerance** (TypeScript, Rust, Python; Java shipped this in 2.6.0)

- **`exact()` enforced softly (TIME-006).** A zero-width `exact(at)` window can't be hit exactly under wall-clock execution, so it was being force-disabled whenever the executor observed the clock a hair late (and systematically so since adaptive timer polling). It now fires at the first opportunity at/after `at` — like `delayed(at)` — and is never reaped. Hard `deadline()` / `window()` semantics are unchanged; `exact()` keeps its precise `[at, at]` interval for verification/simulation.
- **Configurable deadline tolerance (TIME-013).** New per-executor option — `deadlineTolerance(Duration)` (Java), `deadlineToleranceMs` (TS), `deadline_tolerance_ms` (Rust builder / Python `ExecutorOptions`) — widens the grace band before a hard deadline force-disables; default 5ms, `0` for strict. Java had no tolerance band at all before; the 5ms default is now matched across all four implementations.
- Spec TIME-006 / TIME-013 amended.

## 2.6.0 (Java) — 2026-06-02

Reliable `exact()` timing + configurable deadline tolerance (Java only — the TypeScript, Rust and Python counterparts ship in the release above). See TIME-006 / TIME-013.

## 2.8.0 (Python) — 2026-06-01

Six additive binding improvements; no API removed.

- **Subnet local-name remap.** `ctx.input("LOCAL")` / `ctx.output("LOCAL", v)`
  inside a subnet action resolve against author-local names after
  `compose(...)` rewrites the arcs to host places. Lookups try the
  literal name first, then fall back through the new
  `Transition::local_name_map` (populated by the rewriter; chained
  compose keeps only author-original keys, no intermediate-pass leak).
- **Async-action helpers.** `lp.action_gather(*coros)` and
  `lp.action_to_thread(fn, *args, **kw)` schedule on the asyncio loop
  captured at `run_async` / `start_async`, giving real `asyncio.gather`
  parallelism from inside an action on a tokio worker thread (three
  concurrent 300 ms sleeps finish in ~300 ms). `lp.captured_event_loop()`
  exposes the captured loop; the coroutine driver uses `coro.throw(exc)`
  for awaited-future errors; `await asyncio.sleep(0)` yields
  cooperatively to the executor. Concurrent `run_async` on two
  different asyncio loops in one process is detected and rejected
  with `RuntimeError` instead of silently routing helpers to the
  wrong loop.
- **`ctx.flush()` for mid-action streaming.** Buffered outputs publish
  immediately through a per-firing flush channel; downstream
  transitions can fire on the deposited tokens while the upstream
  action is still running. Already-flushed tokens stay even if the
  action later raises. Raises `RuntimeError` under sync execution.
- **Streaming subscribe.** `store.subscribe_stream(...)` yields a single
  `NetEvent` per `__anext__` (no `PyList[1]` wrapper). Unary delivery
  ~30 k events/sec; `subscribe(batch_size=256)` reaches ~950 k
  events/sec. See [`python/docs/perf-subscribe.md`](python/docs/perf-subscribe.md).
- **Batched env-place injection.** `handle.inject_many(place, iterable)`
  crosses the FFI once for any number of tokens via a new
  `ExecutorSignal::EventBatch` variant; the executor processes one
  batch atomically. ~8–9% end-to-end throughput improvement at
  N ≥ 1000.
- **Output-spec validation pinned.** The runtime enforces only the
  declared-place rule today; cardinality, AND-completeness,
  XOR-exclusivity, and `skip_output_validation` are documentation-only.
  See [`python/docs/output-spec.md`](python/docs/output-spec.md) and
  `python/tests/test_output_validation.py`.

**Known limitations (planned for 2.9.0 / next Rust major).**

- `ctx.flush()` deposits emit `TokenAdded` events identical to those
  from action completion; subscribers cannot currently distinguish
  flushed tokens from completion-deposited ones. A dedicated
  `ActionFlushed` event variant is planned for the next Rust major
  (adding it now requires `#[non_exhaustive]` on `NetEvent`, itself a
  breaking change).
- Cancelling the asyncio task that awaits `run_async` aborts the
  surrounding future but does not currently throw `CancelledError`
  into in-flight Python coroutines, so `try/except CancelledError:
  cleanup()` inside an action will not run. The proper fix (Drop guard
  that synchronously injects `CancelledError`) lands in 2.9.0.

## 3.0.0 (Rust) / 2.7.0 (Python) — 2026-06-01

**Executor backend seam (Rust).** The two Rust executors now share one
6-phase CTPN loop. `BitmapNetExecutor` and `PrecompiledNetExecutor` are type
aliases over a single generic `Executor<S, E>` that drives an internal
`ExecutorBackend` trait (bitmap vs. precompiled storage). Fully monomorphised —
the precompiled hot path stays within ±2% of the pre-refactor benchmarks (most
`precompiled_*` cases improved 1–9%); firing order, event semantics, and net
structure are unchanged.

- **Breaking (Rust)**: `marking()` returns `Cow<'_, Marking>` on both executors
  (was `&Marking` / owned `Marking`); `run_sync` / `run_async` likewise. Use
  `.into_owned()` for an owned copy.
- **`Out::Timeout` in the async path**: an async action that exceeds its budget
  now produces the timeout branch's outputs, emits an `ActionTimedOut` event, and
  forwards consumed inputs under a `ForwardInput` child — full `IO-013`/`EXEC-022`
  conformance matching Java/TS, closing two previously-ignored tests.
- Sync executor tests unified behind a `for_each_backend!` suite, so every CTPN
  semantic runs against both backends from a single source.

**Python bindings: cross-language parity.** Closes four gaps versus
Java/TypeScript/Rust — implementations stay on the Rust side per the
`feedback_pyo3_gil_cold` rule (no per-event Python callbacks; filtered,
batched GIL crossings via the existing `action.rs` coroutine pattern).

- **Marking snapshot/restore preserves `Token.created_at`.** `MarkingView.snapshot()` /
  `MarkingView.from_snapshot()` round-trips per-token timestamps; passing a
  view as `initial=` to `run_sync` / `run_async` resumes a timed net without
  clock loss. Mid-execution snapshot via `ExecutorHandle.snapshot()` (powered
  by a new `ExecutorSignal::Snapshot` upstream); `Marking` now derives `Clone`.
- **EventStore + NetEvent surface (Tier A/B/C, Rust-side).** `InMemoryEventStore`
  handle attaches via `event_store=` on `run_sync` / `start_async`. Tier A:
  filtered `store.events(types=..., transitions=..., places=..., limit=..., offset=...)`.
  Tier B: `async for batch in store.subscribe(...)` — bounded `tokio::mpsc`
  channel, Rust-evaluable filters, configurable batching with a `batch_size=1,
  batch_timeout_ms=0` unary mode for low-latency streaming. Tier C: `counters()`,
  `failures()` Rust aggregates. `NetEvent` is a frozen pyclass with lazy
  attribute getters.
- **Session Archive v3 (EVT-025).** `SessionArchiveWriter.write_from_store(...)` /
  `SessionArchiveReader.read(...)` — gzip-compressed, wire-compatible with the
  TypeScript / Rust readers. Writer consumes the `EventStore` handle directly;
  events never round-trip through Python. New `archive` Cargo feature flag and
  `HAS_ARCHIVE` runtime constant.
- **MarkingCache.** `MarkingCache(...).compute_at(store, event_index)` returns
  a `ComputedState` (marking, enabled transitions, in-flight transitions) by
  replaying from the nearest cached snapshot — backs debug-protocol seek/step
  from Python. No Python public API removed; the bindings changes are additive.

## 2.6.0

**Python bindings.** New `libpetri` PyPI package via PyO3 + maturin. Full surface
parity with Java/TS/Rust (runtime, verification, composition, debug, export),
ships with `.pyi` stubs + `py.typed` and 45 tests covering the same arc /
timing / cardinality / output semantics as the Java and Rust suites. Tokens are
untyped `Py<PyAny>` across the FFI — net structure is type-checked, runtime
token types are not (intentional cross-language divergence; validate at your
boundary if needed).

- `OwnedPrecompiledNet`: owned, `'static`-safe entry to the precompiled runtime;
  borrowed `PrecompiledNetExecutor<'p>` path preserved with no hot-path regression.
- `TransitionContext::{input_tokens_raw, read_tokens_raw}` accessors for FFI bridges.
- Built-in `lp.fork` / `lp.passthrough` actions for callback-free pass-throughs.
- `python` CI job + `scripts/release-python.sh` (mirrors the Rust release flow,
  including the documented Cargo.lock-resync gotcha).
- Async-callback perf: manual coroutine driver; `bench_chain_async_callback[100]`
  3536 µs → 750 µs (−78.8%). Sync chain −12% (LTO, `Arc<str>` keys).

## 2.5.0

**Subnet clustering for direct composition.** `compose(SubnetDef)` now records
which subnet each place/transition came from, and the DOT exporter renders
`subgraph cluster_<subnetName>` blocks from that metadata — so a directly-composed
net (no `prefix/` names) still groups each subnet visually. Strictly additive: a
net not built via direct composition exports byte-identically to before.

- **API**: `PetriNet.subnetMembership()` — `node-name → subnet-name` map
  (`subnet_membership()` in Rust). New `ExportConfig.ClusterSource`
  (`AUTO` | `METADATA` | `PREFIX` | `NONE`); `AUTO` (default) uses metadata when
  present and falls back to instance-prefix detection.
- **Viewer**: cluster discovery recovers membership by geometric containment, so
  directly-composed clusters report correct member counts in javadoc, rustdoc and
  the debug UI.
- New requirement **MOD-026** (SHOULD); **MOD-040** / **EXP-016** amended. No API removed.

## 2.4.0

**Direct subnet composition.** A new mode composes a `SubnetDef` into a host
net *without* instantiation/prefix-renaming — body places and transitions keep
their original names and merge by name. Unlike the auto-compose body-inference
fallback (MOD-024) it is order-independent. `instantiate(prefix)` + instance
composition is unchanged, and remains the path for independent copies.

- **API**: `compose(SubnetDef)` overload (Java/TS); `compose_direct(&SubnetDef)`
  in Rust (no overloading).
- A body transition name that collides with the host, or a subnet declaring a
  channel, is rejected at compose time.
- New requirement **MOD-025** (MUST). Strictly additive — no API removed, no
  core type changed.

## 2.3.2

*Released 2026-05-20*

**Configurable ELK layout for the canonical viewer, with side-effect-leaf
packing on by default.** The viewer's ELK placement stage gains an
`ElkLayoutConfig` — a per-subnet algorithm (`clusterLayout`) and side-effect-leaf
packing (`leafPacking`). A subnet dominated by "side-effect leaf" places (places
whose only intra-cluster arcs are reset/read) now packs those leaves into a
compact grid sub-block instead of stringing them into one wide row, so a
transition with many reset arcs lays out far more readably. Packing is enabled
by default, so every doc-generated diagram — Java javadoc, Rust `libpetri-docgen`,
and the TypeScript doclet — inherits the improvement through the regenerated
`petrinet-diagrams.js` bundle. Cross-generator parity is unchanged: all three
embed the same bundle and mount it with the same defaults.

### Added

- **TypeScript viewer**: `ElkLayoutConfig` (`clusterLayout: 'layered' |
  'rectpacking'`, `leafPacking: boolean | LeafPackingOptions`), surfaced through
  `MountOptions` and the `renderDotToSvgWithElkLayout` render entry. The render
  cache key now incorporates the layout config.
- **debug-ui**: the "Flat View" control is wired to the viewer's subnet
  visibility toggle; a Playwright layout-regression suite (`debug-ui/e2e/`) is
  added as a local dev tool — it is not run in CI.

### Compatibility

`build-viewer.sh` still installs byte-identical `petrinet-diagrams.{js,css}` to
all three doc-generator resource dirs. The Java jar's bundled debug-ui is
refreshed. No API is removed; `ElkLayoutConfig` is additive and every field is
optional.

## 2.3.1

*Released 2026-05-19*

**Doc generators consolidate on the client-side viewer.** The Java taglet, the
Rust `libpetri-docgen` crate, and the TypeScript doclet plugin all stop trying
to render DOT → SVG at build time and instead embed the DOT source in a
`data-dot` attribute. The bundled `LibpetriViewer` IIFE (Graphviz WASM baked
in) renders client-side on first view. Doc-generation hosts no longer need
`dot` or Node installed, and the per-tag subprocess overhead is gone.

### Removed

- **Java taglet**: subprocess machinery (`tryDotRender`, `tryC0Prerender`,
  `runSubprocessRenderer`, the per-DOT SVG caches, the `dotAvailable`
  cache-poison flag, and the `LIBPETRI_PRERENDER_SCRIPT` /
  `-Dlibpetri.prerender.script` env-var integration). `DiagramRenderer`
  loses its `renderSvg` / `renderSubnetSvg` paths and the `Body` switching
  record.
- **Rust `libpetri-docgen`**: the `dot` CLI fallback (`dot_to_svg`,
  `try_dot_command`, `find_attr`) and the `strip_dimensions` builder option.
- **TypeScript viewer**: `viewer-static.iife.js` (the slim ~26 KB bundle that
  stubbed Graphviz WASM), `index-static.ts`, and `render-stub.ts`. The
  remaining `mount(dotSource, …)` signature drops its `null` overload — the
  static-adopt branch is gone.
- **Build artifacts**: `scripts/prerender-c0.mjs` (Node prerender CLI) and the
  slim-bundle copy step in `scripts/build-viewer.sh`.

### Breaking — TypeScript `libpetri` npm package

- The `libpetri/viewer/layout` subpath export is **removed**. It existed only
  to serve the prerender CLI and the Java taglet's hybrid path, both of which
  are gone. The underlying `preprocess` / `elk-place` modules are still
  available internally and via direct dist imports if needed.

### Spec

- `spec/09-export.md` EXP-011 and EXP-015 reworded: implementation notes now
  describe DOT-in-`data-dot` embedding for all three generators; EXP-015
  acceptance criteria assert DOT content (extracted from `data-dot`) instead
  of rendered SVG shape.

### Compatibility

`build-viewer.sh` still installs byte-identical `petrinet-diagrams.{js,css}`
to all three doc-generator resource dirs; the invariant is unchanged. The
viewer's ESM entry (`libpetri/viewer`) and IIFE entry (`libpetri/viewer/iife`)
keep their public shape. Only consumers reaching into `libpetri/viewer/layout`
need to migrate.

## 2.3.0

*Released 2026-05-19*

**libpetri 2.3 adds identity-default auto-composition (MOD-024) to the
modular-composition layer across all three languages.** A single-argument
`compose(instance)` overload auto-binds every declared interface port to
the host place carried on its declaration, eliminating the boilerplate of
`compose(instance, b -> b.bindPort("name", host))` when the subnet's
interface already states the host wiring.

Released across Java, Rust, and TypeScript at 2.3.0. Rust and TypeScript
skip the 2.2.0 number — that section's content (the viewer subnet-visibility
toggle) shipped only in Java 2.2.0 to Maven Central; the same toggle code
is present in this Rust/TypeScript 2.3.0 release alongside MOD-024.

### `PetriNet.Builder.compose(Instance)` — auto-compose (MOD-024)

```java
// Before — explicit per-port wiring repeated at every call site:
host.compose(producer.instantiate("p1"),
             b -> b.bindPort("output", sharedQueue));

// After — port.place() carries the host wiring; auto-compose trusts it:
host.compose(producer.instantiate("p1"));
```

- Every declared port auto-binds to its own `port.place()` (the `Place` the
  `SubnetDef` builder declared via `.inputPort(name, hostPlace)` /
  `outputPort` / `inoutPort`).
- When the subnet declares **no** interface ports, body places are matched
  against the host builder's place set by `Place` record equality
  (`(name, tokenType)` in Java); matches merge, the rest stay private under
  their prefixed names per MOD-010 / MOD-012.
- Channels are **not** auto-bound. A subnet that declares any channel makes
  `compose(instance)` throw `IllegalStateException` naming the channels and
  pointing at the `compose(Instance, Consumer)` overload — transition
  identity is too delicate for inference.
- The auto-compose path shares the rewrite pipeline (`applyComposition`)
  with the explicit overloads, so the resulting flat net is structurally
  identical to a hand-written `compose(instance, bindings)` call per
  MOD-023.

### Spec

- New requirement **MOD-024** (`spec/11-modular-composition.md`) —
  Identity-Default Port Inference (auto-compose), SHOULD-level.
- `spec/00-index.md` summary updated: SHOULD count 43 → 44.

### Cross-language `Place` equality — divergence note

`compose(instance)` uses the implementation's existing `Place` equality:

- **Java** (this release): `Place` is a record `(name, tokenType)` — dedupes
  by both fields. Two same-named different-typed places do **not** merge.
- **TypeScript / Rust** (unreleased; equivalent overload present): `Place`
  equality is **name-only**, so same-named different-typed places would
  merge. This is the spec's "permissive matching" carve-out (MOD-024 last
  paragraph).

A future TS/Rust 3.0 release will close this gap by adding a token-type tag
to `Place` and tightening equality.

### Compatibility

`libpetri 2.3.0` is a strict additive extension of the prior published
versions (Java 2.2.0, Rust 2.1.0, TypeScript 2.1.0). No public API was
removed; behaviour for callers that don't invoke the new overload is
unchanged. The new method is one overload on `PetriNet.Builder` /
`PetriNetBuilder`; pre-existing overloads keep their signatures.

For TypeScript and Rust, this release also brings to npm/crates.io the
**viewer subnet-visibility toggle** documented in the `## 2.2.0` section
below (already in `main` since 2026-05-19 but never published to those
registries). Java had that release on its own; this release reunifies the
three languages on the same version number.

## 2.2.0

*Released 2026-05-19*

**libpetri 2.2 adds a runtime subnet-visibility toggle to the canonical viewer.**
Every diagram surface — debug-ui, dev-preview, Javadoc, Rustdoc, TypeDoc — now
exposes a chrome button that flips between the clustered (post-2.1) view and
the flat pre-subnets view without leaving the page.

### Viewer — clustered ↔ flat toggle

The viewer's chrome strip grows a **Flat view / Subnets view** button next to
**Reset** and **Fullscreen**. Clicking it re-mounts the diagram with the
alternate variant: in flat mode the `subgraph cluster_*` wrappers and their
`ltail`/`lhead` cross-cluster references are stripped, so Graphviz lays the
graph out without visual groupings. Same nodes, same edges, no clusters.

New on the public viewer API (`typescript/src/viewer/`):

- `MountOptions.subnets?: 'show' | 'hide'` — initial mode. Defaults to
  `'show'`; inherits from `previousHandle` when omitted so live re-renders
  preserve the user's choice.
- `ViewerHandle.subnets` — current mode (read-only).
- `ViewerHandle.setSubnets(mode)` / `toggleSubnets()` — programmatic switch.
  Returns the new handle (the toggle triggers an internal re-mount because
  Graphviz lays out cluster boundaries during layout).
- `libpetri-viewer:remount` CustomEvent dispatched on the host container
  whenever an internal re-mount happens. Consumers that cache the handle
  (e.g. debug-ui) can listen and update their reference.
- `flattenClusters(dot)` exported from `libpetri/viewer` — pure function
  for callers who want to derive flat DOT directly.

### Distribution

The new viewer bundle is synced byte-identically to all three doclet
destinations (`java/src/main/resources/javadoc/`, `rust/libpetri-docgen/resources/`,
`typescript/src/doclet/resources/`). No changes to `DotExporter` / export
APIs in any language — the toggle is purely a viewer-layer concern.

### Compatibility

`libpetri 2.2.0` is a strict superset of `2.1.0`: no public API was removed,
no behaviour changed for callers that don't opt into the new options.
Diagrams mount in clustered mode by default. The toggle button is rendered
but disabled on the pre-rendered-SVG mount path (`mount(null, …)`) because
no DOT is available for the alternate render.

## 2.1.0

*Released 2026-05-19*

**libpetri 2.1 is about visual coherence at scale.** Composed nets with many
subnets now lay out cleanly in DOT/Graphviz, and the canonical viewer gains a
production-grade C0 layout pipeline shared across debug-ui, the Javadoc taglet,
Rustdoc, and TypeDoc.

### Spec — EXP-017: compound cluster layout hints

The DOT export sets `compound="true"` unconditionally on the digraph and emits
*invisible ghost edges* connecting clusters bridged by single-hop orphan paths.
Graphviz uses the `ltail`/`lhead` hints on those ghost edges to keep
cluster-to-cluster flow direction stable while the visible edges still pass
through the real orphan transitions.

The synthesis is deterministic across Java, Rust, and TypeScript exporters:
ghost-edge anchors are the first-witness `(a → o, o → b)` pair encountered in
input iteration order, ordered cluster pairs `(X, Y)` collapse to one ghost edge
each, and `X == X` or single-neighbour orphans produce nothing. Eight
acceptance criteria are codified in `spec/09-export.md` and mirrored in
`ClusterBuilderTest` in all three languages.

### Viewer — canonical C0 layout pipeline

`typescript/src/viewer/layout/` is now the single source of truth for the
multi-cluster layout flow used by every documentation surface:

1. `parseLibpetriDot(dot)` — typed graph model from libpetri-exported DOT
2. `foldOrphans(graph, 0.7)` — adopt orphan nodes into their dominant cluster
   when ≥70 % of their edges point there
3. `replicateShared(graph)` — clone shared places into every foreign cluster
   they touch, redirect edges to local copies (`p_${id}__rep__${cluster}`
   naming is load-bearing — downstream overlays key off it)
4. `elkLayout(graph)` — ELK placement; orphans are wrapped in a synthetic
   `cluster_orchestrator` so they pack alongside real subnets
5. `writeBack(graph, layout)` — re-emit DOT with `pos="x,y!"` pins and
   cluster `bb="…"` so Graphviz `neato -n` produces the final SVG

Around the rendered SVG the viewer ships four idempotent overlays:

- **`c0-annotations.ts`** — `data-id` / `data-src` / `data-dst` / `data-instance`
  injection plus `intra-cluster` / `cross-cluster` edge classes
- **`replica-tagging.ts`** — `.petri-replica` + `data-replica-of` on every clone
  of a shared place, plus the ⇄ glyph for visual identification
- **`highlight.ts`** — click-to-highlight that walks through junctions and
  surfaces every real neighbour; highlighting a shared place highlights every
  copy together
- **`visibility.ts`** — directed-reachability orphan visibility that hides
  unrelated orphan chains when only a subset of clusters is shown

The new `chrome/sidebar.ts` replaces the legacy legend + filter strip with a
cluster-chip sidebar: plain-click toggles, shift-click isolates, ctrl/cmd-click
multi-selects, plus show-all / hide-all and a highlight-mode toggle.

`mount()` returns two new C0-only methods: `handle.highlight(nodeId)` and
`handle.setVisibility(state)`. Both are gated on `layout: 'elk'` (the new
default); pass `layout: 'graphviz'` for the plain pre-2.1 rendering.

A 16-entry LRU cache in `render.ts` (keyed on FNV-1a of the DOT source) makes
re-mounts on identical DOT skip the entire pipeline.

### Doclet — opt-in Node-CLI pre-render for Javadoc

`PetriNetTaglet` now tries a Node-CLI pre-render path before falling back to
`dot -Tsvg`. Set `LIBPETRI_PRERENDER_SCRIPT` (or `-Dlibpetri.prerender.script=…`
to survive the Gradle daemon's env capture) to the path of
`typescript/scripts/prerender-c0.mjs` and the taglet pipes DOT to Node, runs the
full C0 pipeline, and embeds the resulting SVG inline. ~1 second per 14-subnet
diagram; cached per-DOT-source for the lifetime of the doc build.

Both render paths share a single `runSubprocessRenderer` driver with a typed
`SubprocessRendererConfig` record — concurrent stdout/stderr drain to avoid the
OS pipe-fill deadlock, per-renderer timeout, cache-poison hook on missing or
wedged binaries. ~120 LOC of duplication is gone.

### Distribution

The canonical viewer bundle (`viewer.iife.js`, `viewer.css`) is built once from
`typescript/src/viewer/` and synced byte-identically to all three doclet
destinations (`java/src/main/resources/javadoc/`, `rust/libpetri-docgen/resources/`,
`typescript/src/doclet/resources/`). The viewer's public ESM surface gains
`libpetri/viewer/layout` so the Node prerender script and any external tooling
can drive the C0 pipeline directly.

### Performance

- Cluster building is O(N + E + O·I·G) with no hidden O(n²); ghost-edge dedup
  is O(1) per ordered pair.
- The C0 overlays batch DOM mutations after computing target state — no
  interleaved getBBox / setAttribute, no layout thrash.
- ELK runs once per unique DOT input; downstream overlays are O(N + E) walks
  with map-backed lookups.

### Compatibility

`libpetri 2.1.0` is a strict superset of `2.0.0`: no public API was removed,
no behaviour changed for nets that don't compose subnets. Consumers that
explicitly want the pre-2.1 viewer behaviour can pass `layout: 'graphviz'`
to `mount()`. The Javadoc taglet's legacy `dot -Tsvg` path still runs when
the C0 env var / sysprop is unset.

## 2.0.0

*Released 2026-05-18*

**libpetri 2.0 is about modular composition.** You can now build large
Petri nets the way you build large programs — by writing small reusable
pieces and snapping them together. Producer, buffer, consumer, rate
limiter: each becomes a self-contained subnet with a typed interface,
and the composition machinery wires them up.

Everything from 1.x still works. The 2.0 surface is additive — your
existing builders, runtime, events, exports, and verification code
compile unchanged.

### Subnets and instances

Define a reusable fragment as a `SubnetDef`. It looks like a normal net,
but its boundary is declared as an `Interface` with two kinds of names:

- **Ports** — boundary places that a host net can wire into its own
  places. Typed by token type.
- **Channels** — boundary transitions that fuse with host transitions
  when composed, giving you synchronous coupling between subnets.

A `SubnetDef` is a template. Call `def.instantiate("p1", params)` to get
an `Instance`, which is the same net with everything renamed to
`p1/<originalName>`. Instantiate it twice and you get two independent
copies that won't collide. Instances also inherit shared default
actions from the def, and you can override per-instance with
`bindActions(...)` — the rest of the instance keeps the shared
reference, so changing the def's action propagates to every instance
that didn't override it.

You can retrofit an existing 1.x `PetriNet` as a subnet via
`SubnetDef.fromNet(net, iface)` without rewriting it.

### Composing with the builder

The new `PetriNet.builder().compose(instance, bindings)` method weaves
an instance into the enclosing net:

```java
var producer = SubnetDef.<Void>builder("Producer")…build();
var buffer   = SubnetDef.<Integer>builder("Buffer")…build();

var system = PetriNet.builder("Pipeline")
    .compose(producer.instantiate("p"), b ->
        b.bindPort("output", hostInput))
    .compose(buffer.instantiate("b", 4), b ->
        b.bindPort("in", hostInput).bindChannel("backpressure", limiter))
    .build();
```

What this does:

- **Port bindings** rewrite every arc on the instance so the port place
  becomes the host place. After `build()` the two places are the same
  place.
- **Channel bindings** merge the instance's boundary transition with a
  host transition: arc union, timing intersection, caller-wins
  priority, sequential action composition.

`build()` returns a flat `PetriNet`. The executor, exporter, verifier,
and event store see no difference from a hand-written net.

### FusionSet — shared places across instances

When two instances need to share state — a single rate limiter across
three workers, one bounded buffer feeding two consumers — declare a
`FusionSet` of equivalent places:

```java
.fuse(FusionSet.of("limiter",
    workerA.port("slots", Integer.class),
    workerB.port("slots", Integer.class),
    workerC.port("slots", Integer.class)))
```

At `build()`, the non-canonical members are substituted away. Fusion is
orthogonal to composition: declare it before or after your `compose(...)`
calls — same result.

### Better visualization for composed nets

DOT exports now emit one `subgraph cluster_*` per instance prefix, with
nested instances producing nested clusters. Output is byte-identical to
1.x for any net that doesn't use composition. The Java doclet picks up
the same data: a new `@SubnetStructure` annotation and the
`{@subnet Name}` inline tag let you point at subnet defs from doc
comments, and `SubnetDotExport` renders compact interface-only diagrams
(ports and channels, no internals) for API reference pages.

### Debug protocol speaks subnets

The debug-ui has a new subnet panel. The wire protocol's `Subscribed`,
`PlaceInfo`, and `TransitionInfo` responses now carry instance
descriptors so the UI can walk composed nets by prefix and let you
drill in.

### Verifying a subnet on its own

You can now prove properties about a subnet in isolation, before you
compose it into anything:

```java
var result = bufferDef.verify(
    VerificationHarness.<Integer>builder(4)
        .input("in", () -> Token.of(...))
        .property(new PlaceBound("items", 4))
        .build());
```

The harness wraps the subnet in a synthetic enclosing net, feeds the
declared input ports from environment generators, and runs the standard
Z3/SMT verifier. You get back a `VerificationResult` with per-property
outcomes plus `allHold()` / `firstFailure()` shortcuts. Verifying an
already-composed flat net works exactly like 1.x — no API change there.

### Faster doc pages: pre-rendered SVG

The Java javadoc taglet now pre-renders each diagram at doc-generation
time when `dot` is on `PATH`, embedding the resulting SVG directly and
shipping a slim `viewer-static.iife.js` bundle (~26KB) that drops the
inlined Graphviz WASM. Page-load latency drops dramatically on doc
pages with many `{@petrinet ...}` references. When `dot` isn't
available the taglet transparently falls back to client-side rendering
with the full bundle — no configuration needed.

The viewer's `mount()` now accepts `null` as the DOT source (adopts an
existing `<svg>` child), and gains a `fit()` method plus built-in
Reset and Fullscreen chrome buttons when `chrome:true`.

### Migration from 1.x

No code changes needed. Update your dependency to `2.0.0` and existing
code keeps working. The new modular-composition APIs are available
under:

- **Java** — `org.libpetri.core.{SubnetDef, Instance, Interface, FusionSet, ComposeBindings, Subnet}` plus `org.libpetri.verification.VerificationHarness`.
- **TypeScript** — re-exported from `libpetri`: `SubnetDef`, `Instance`, `Interface`, `FusionSet`, `ComposeBindings`, `VerificationHarness`.
- **Rust** — new modules in `libpetri-core` (`subnet`, `compose`, `fusion`, `interface`, `instance`); `libpetri-verification` gains the harness; `libpetri-export` gains cluster output.

For a complete worked example see the **Modular Composition** section
in the top-level README. The full formal contract lives in
`spec/11-modular-composition.md` (22 new requirements, MOD-001..061);
spec totals are now 183 across 11 documents.

## 1.8.5

### Fix: doc-viewer zoom cap raised from 5x to 1000x

`petrinet-diagrams.js` (the small pan/zoom/fullscreen helper inlined into
Javadoc and TypeDoc HTML) clamped wheel zoom to `Math.min(5, ...)`, hitting
a hard ceiling at 500%. Bumped to `Math.min(1000, ...)` and floor lowered
from `0.1` to `0.02`, matching the bounds the live debug-ui and dev-preview
viewers already use via `libpetri/render-dom` (panzoom defaults). Java and
TypeScript ship parallel copies of this asset; both are updated and now
carry a sync-reminder comment to keep them byte-identical.

No Rust change — `libpetri-docgen` does not ship this JS asset.

## 1.8.4

### Feat: XOR/AND junction nodes + combined reset+output edges

New visualization rules in `spec/09-export.md` (EXP-012, EXP-013, EXP-014,
EXP-015), implemented identically in Java/TypeScript/Rust mappers:

- **EXP-012** — Every `Out.Xor` / `Out.And` group with two or more children
  now becomes a synthetic *diamond junction node* between the transition and
  its children. The discriminator is an inline heavy glyph: `✕` (U+2715) for
  XOR, `✚` (U+271A) for AND. Single-child groups still collapse to a direct
  edge — no orphan junctions. New style categories `xor-junction` and
  `and-junction` (shape `diamond`, fill `#FFFFFF`, stroke `#333333`,
  width/height `0.3`, fontsize `14`, `fixedsize="true"`).
- **EXP-013** — When a transition outputs to place `P` and resets `P`, the
  separate output and reset edges collapse into one edge labelled `"reset+out"`,
  styled as the new `reset-output` category (color `#fd7e14`, style `bold`,
  penwidth `2.0`). The rule applies whether the output leaf is direct from the
  transition or nested under a junction.
- **EXP-014** — Junction IDs follow `j_<sanitizedTransition>__<kind>_<idx>`,
  where `<idx>` is a flat depth-first pre-order counter starting at 0. Same
  numbering scheme in all three languages, so DOT output is byte-identical
  across implementations for the same input net. New round-trip stability
  tests in each language assert that two consecutive exports produce
  byte-equal DOT.
- **EXP-015** — Compile-time doc generators (Javadoc taglet, `cargo doc`
  build script, TypeDoc plugin) all delegate to their language's mapper, so
  the new junction nodes and combined edges show up in generated SVGs without
  any doc-generator-specific code.

### Refactor: `EmitCtx` threaded through Out-tree emission

Java `JunctionCtx`, Rust `EmitCtx<'_>`, and TypeScript `EmitCtx` bundle the
mutable per-transition state (counter, reset-place set, combined accumulator,
node + edge sinks) into a single value passed by the recursive emitter. The
public mapper API is unchanged; internal helpers drop from nine arguments
each to four (`out`, `parentId`, `branchLabel`, `ctx`). On the Java side this
also retires the `int[] counter = { 0 }` mutable-array idiom; on the Rust
side it lets `#[allow(clippy::too_many_arguments)]` go away.

### New: `libpetri/render-dom` browser package entry

A new TypeScript package entry exports `renderDotToContainer(dot, container,
opts)` — a small wrapper around `@viz-js/viz` (Graphviz WASM) and `panzoom`
that pins the `dot` engine for layout stability and disposes prior panzoom
instances on re-render. The debug-ui (`debug-ui/src/net/actions/diagram.ts`)
now imports this entry instead of bootstrapping viz.js + panzoom inline,
deleting ~140 lines of duplicated setup. A new Vite-based `dev-preview/`
sandbox uses the same module against the new `sample.dot` golden file for
local visual iteration. The script `npm run regenerate-sample` reproduces
that file deterministically from the TS mapper; it exercises every rule above.

## 1.8.3

### Fix: archive header `eventCount` matches body length

The session archive writer (Java/TS/Rust) populated header `eventCount` from
`DebugEventStore.eventCount()` — the **lifetime cumulative append counter** that
never decrements on eviction — while iterating the body from the live event queue.
After any eviction, the header overstated the body by exactly the eviction count,
breaking the `archive.eventCount() == archive.events().size()` round-trip
invariant.

A second, Java-only failure mode: header `eventCount`,
`SessionMetadata.computeFrom(...)`, and the body loop were three separate reads of
the concurrent `ConcurrentLinkedQueue`. A producer thread appending between any
two reads desynchronised them.

Fix: every writer entry-point now takes a single immutable snapshot of the event
store and derives header `eventCount`, V2/V3 metadata, and the body iteration from
that one list. Identical pattern across all three languages. Wire format is
unchanged — old archives remain readable, new archives remain readable by older
1.8.x readers (the field is canonical content, not wire layout).

Codified as new acceptance criterion **EVT-025 #8**. Regression tests added in
all three implementations: eviction round-trip in Java/TS/Rust, plus a virtual-thread
concurrent-producer stress test on Java where `ConcurrentLinkedQueue` makes the race
observable.

## 1.8.2

### Revert `splines=curved`

`splines=curved` from 1.8.1 produced overly wavy edge routing on dense nets — in
practice noticeably worse than Graphviz's default B-spline routing. Removed.

`outputorder=edgesfirst` is kept — that one is still the right fix for the
label-under-edge overlap problem from 1.8.0.

## 1.8.1

### Debug-UI diagram readability

Two graph attributes added to the DOT output produced by `PetriNetGraphMapper`
(all three languages) so the rendered debug-ui diagram is easier to read on dense
nets:

- **`outputorder=edgesfirst`** — Graphviz draws edges first and nodes (including
  `xlabel` place names) on top. Edge lines no longer slice through place labels.
- **`splines=curved`** — softer curved edge routing instead of the default
  spline style. Noticeably cleaner on graphs with many crossings.

The spec file `spec/petri-net-styles.json` is the single source of truth; the
Java/TS/Rust style constants are regenerated by `scripts/generate-styles.sh`.

The debug-ui (`debug-ui/src/net/actions/diagram.ts`) now pins the viz.js layout
engine to `dot` explicitly. libpetri servers emit byte-stable DOT (Java uses
`LinkedHashMap` in `PlaceAnalysis`; TS/Rust iterate ordered collections), and the
`dot` engine produces identical layout for identical input — so diagrams are
deterministic across debug-ui reloads. Pinning guards against future viz.js
default changes to force-directed engines.

## 1.8.0

### Archive format v3 (all three languages)

`SessionArchive` gains a third variant (`V3`). The v3 header is structurally identical to
v2 — same `endTime`, `tags`, pre-computed `metadata` — but the version bump signals that
the event body format now carries **structured token payloads** alongside the legacy
display string. See [EVT-025](spec/08-events-observability.md) for the full contract.

Default writer output is now v3:

- **Java**: `SessionArchiveWriter.write` emits v3. Tokens serialize as
  `{valueType: <FQN>, v: <structured JSON>, createdAt}` with `{valueType, text}` fallback
  for values Jackson cannot structure and `{valueType: "void"}` for unit tokens. The
  reader resolves `valueType` via `Class.forName` — classes on the current classpath
  hydrate with their original type; missing classes degrade to `Token<JsonNode>`
  preserving the payload tree.
- **TypeScript**: `SessionArchiveWriter.write` emits v3. `TokenInfo.structured` carries
  the JSON projection (`JSON.parse(JSON.stringify(v))` with empty-object / symbol /
  function filtering). `Token<T>` gains an optional `structured?` field that
  `SessionArchiveReader.readFull` populates on replay — live tokens leave it undefined
  and the runtime ignores it.
- **Rust**: `SessionArchiveWriter::write_with_registry` emits v3 via a user-supplied
  [`TokenProjectorRegistry`](rust/libpetri-debug/src/token_projector_registry.rs).
  Replay hydrates each `TokenAdded` / `TokenRemoved` event with a `ReplayedTokenPayload
  { type_name_str, value_json }` implementing the same `TokenPayload` trait as live
  `ErasedToken`, so consumers treat live and replayed tokens uniformly. Executors only
  attach the payload when `EventStore::CAPTURES_TOKENS = true`, so `NoopEventStore`
  builds monomorphize the capture branch to dead code — zero overhead in production.

### Backward compatibility

- Readers in all three languages still accept v1 and v2 archives. Unknown versions are
  rejected with an error naming the observed version and the supported range.
- `writeV1` / `writeV2` (`write_v1` / `write_v2` in Rust) still exist, but note: the
  writer no longer produces byte-for-byte 1.7.x event bodies — it always emits v3 token
  shapes regardless of the header version. Consumers pinned to a 1.7.x reader may choke
  on the extra `structured` field; either upgrade the reader or consume archives
  produced by a 1.7.x writer.

### Breaking changes

- **Rust**: `NetEvent::TokenAdded` and `NetEvent::TokenRemoved` gain a third struct field
  (`token: Option<Arc<dyn TokenPayload>>`). Both variants are now `#[non_exhaustive]`;
  downstream pattern matches must use `{ place_name, timestamp, .. }` or explicitly
  destructure `token`. Use the new `NetEvent::token_added(...)` /
  `token_added_with(...)` constructors to build events (they keep the variant fields
  private-by-convention and survive future field additions).
- **Rust**: `libpetri-core` now depends on `libpetri-event` so that `ErasedToken` can
  implement `TokenPayload`. This is a workspace-internal change; downstream crates pick
  it up automatically via `libpetri` umbrella.
- **TypeScript**: `Token<T>` gains an optional `structured?: unknown` field. Additive —
  existing `{ value, createdAt }` literals remain valid. Consumers destructuring via
  `{ value, createdAt, ...rest }` will pick up the extra field.
- **Java**: No source-breaking changes. The serialized `NetEvent` JSON now emits tokens
  in the new v3 shape — any hand-rolled Jackson deserializer for `Token` must understand
  the v3 format (or use `NetEventSerializer` which does).

### Security

Archive deserialization is a trust boundary in all three languages — Java because
`Class.forName` on an archive-supplied FQN triggers static initializers, TypeScript
because a hostile `toJSON()` override could return misleading data, Rust because a
hostile `type_name` string could misattribute a payload. Do not deserialize archives
from untrusted network sources without a guard. See EVT-025 security note.

## 1.7.0

### Archive format v2 (all three languages)

`SessionArchive` is now a sealed hierarchy (`V1` / `V2`) — Java sealed interface + records,
TypeScript discriminated union keyed on `version: 1 | 2`, Rust enum. The v2 header adds:

- `endTime` — the `complete()` timestamp, preserving session duration across archival.
- `tags` — the user-defined tag snapshot at write time.
- `metadata` (new `SessionMetadata`) — single-pass aggregates: event-type histogram
  (PascalCase keys, alphabetical, identical wire format across languages), first/last event
  times, and `hasErrors` (true for any `TransitionFailed`, `TransitionTimedOut`,
  `ActionTimedOut`, or `LogMessage` at level `ERROR`, case-insensitive).

v2 lets listing/sampling tools answer "which sessions had errors" or "how many events of
type X" without decompressing the body. Per-event wire format is identical to v1.

### Backward compatibility

- Readers peek `version` via a probe DTO and deserialize into the matching variant. v1
  archives from libpetri ≤ 1.6.1 remain fully readable; mixed v1/v2 buckets coexist.
- v2-only accessors (`tags()`, `endTime()`, `metadata()`) return safe defaults on v1 archives.
- `writeV1()` / `write_v1()` escape hatch for producing archives consumable by older readers.
  Default `write()` emits v2.
- Shared metadata helpers usable on live sessions or v1 reads:
  Java `SessionMetadata.fromEvents`, TypeScript `computeMetadata`, Rust `compute_metadata`.
- Rust adds `NetEvent::has_error_signal()` — superset of `is_failure()` that also catches
  `LogMessage` at `ERROR`. `is_failure()` is unchanged.

### Performance

- v2 overhead vs v1: **+0.8%** on a 1000-event session (20,872 vs 20,703 bytes LZ4).
  LZ4/gzip frame dedup absorbs the repeated header strings; v2's value is at read time, not
  on disk.

### Compatibility

- **Java** binary-incompatible for code pattern-matching on the old `SessionArchive` record —
  recompile against 1.7.0.
- **Rust** `imported.metadata.session_id` (field) → `session_id()` (method). No in-workspace
  consumers affected.
- **TypeScript** source-compatible; the discriminated union narrows existing
  `version === CURRENT_VERSION` checks.
- Archive envelopes still differ by language (Java LZ4, TS/Rust gzip; Java/TS ISO-8601,
  Rust u64-ms). Cross-language read is future work.
- No spec changes for the archive format — it is implementation-defined.

### Bulk token output on `TransitionContext` (all three languages)

Transition actions can now push multiple tokens to the same output place in one call,
avoiding the `for v in values { ctx.output(...) }` loop that previously incurred per-element
place-declaration validation:

- **Java**: `@SafeVarargs public final <T> TransitionContext output(Place<T>, T...)` and
  `<T> TransitionContext output(Place<T>, Iterable<? extends T>)`. Strict-match overload
  resolution (JLS §15.12.2.5) keeps the existing single-value `output(Place<T>, T)` call
  path unchanged.
- **TypeScript**: `ctx.output<T>(place, ...values: T[])` and
  `ctx.outputToken<T>(place, ...tokens)` now accept rest parameters. Single-arg call sites
  continue to type-check.
- **Rust**: new `ctx.output_many<T>(place_name, impl IntoIterator<Item = T>)`. Accepts
  arrays, `Vec`, slice iterators, and iterator adaptors. The existing single-value
  `output()` is untouched.

All three implementations validate the output place **once** before iterating, share a
single timestamp across the produced tokens (matching "fired at time T" semantics), and
fail fast on undeclared places without leaving partial output. See [CORE-062].

### Spec Changes

- **CORE-062 updated.** Extended the acceptance criteria to cover the bulk-form API, the
  validate-once-fail-fast contract, and the empty-bulk-is-a-no-op degenerate case.

## 1.6.1

### Session tags (all three languages)

`DebugSessionRegistry` sessions now carry arbitrary `Map<String,String>` tags
(e.g. `{channel: "voice", env: "staging"}`). Storage lives on the `DebugSession` itself —
no shadow map, no cleanup coordination. Java uses `ConcurrentHashMap` for lock-free updates;
TS/Rust mutate in place. New APIs across languages: `register(id, net, tags)`,
`tag(id, key, value)`, `tagsFor(id)`, and an optional `tagFilter` on `listSessions` /
`listActiveSessions`.

### Session endTime

`complete(sessionId)` stamps an `endTime` once (first-completion semantics). `duration()`
returns `Optional<Duration>` / `undefined | number` / `Option<u64>` ms.

### Wire protocol

- `DebugResponse.SessionSummary` adds optional `tags`, `endTime`, `durationMs`. Older clients
  tolerate the new fields.
- `registerImported` overload accepts `endTime` + `tags` for archive round-trips.

### Breaking changes (Rust internal wire format)

- `DebugCommand` / `DebugResponse` inline enum-variant fields now serialize in **camelCase**
  to match Java/TypeScript (`sessionId`, `activeOnly`, `tagFilter`, `netName`, `dotDiagram`,
  `eventCount`, `startIndex`, `hasMore`, `currentMarking`, `enabledTransitions`,
  `inFlightTransitions`, `currentIndex`, `breakpointId`, `eventIndex`, `fromIndex`, `fileName`,
  `storageAvailable`). Previously snake_case, which prevented the TypeScript debug-ui from
  connecting to a Rust backend. Inner struct types were already correct. Update any Rust-only
  client code that hardcoded JSON keys.

### Compatibility

Otherwise additive and source-compatible. Archive v1 format untouched; v2 with tags +
histograms ships in 1.7.0. No spec changes.

## 1.5.3

### Dependency Updates

- **lz4-java**: changed groupId from `org.lz4` to `at.yawk.lz4` (upstream artifact relocation).

## 1.5.2

### Bug Fixes

- **Fixed CPU spin in `drain()` with enabled timed transitions (Java, Rust).** Calling `drain()`
  on an executor with environment places while timed transitions were enabled but not yet ready
  (nothing in-flight) caused the orchestrator to spin at 100% CPU. In Java, `awaitWork()` fell
  through without blocking because `hasEnvironmentPlaces && !draining.get()` was false and no
  other branch applied. In Rust, the same condition caused premature termination (dropping
  enabled timed transitions). With 20 concurrent nets on 4 cores, total CPU burned was ~5,600ms
  for a 400ms wall-clock window. Affects `BitmapNetExecutor` and `NetExecutor` (Java),
  `BitmapNetExecutor` and `PrecompiledNetExecutor` (Rust async). Java `PrecompiledNetExecutor`
  and TypeScript were already correct. Regression introduced in 1.5.0.

## 1.5.1

### Bug Fixes

- **Fixed CPU spin in `close()` with in-flight async actions (Java).** Calling `close()` while
  async transition actions were running caused the orchestrator thread to spin at 100% CPU until
  those actions completed. The `awaitCompletionOrEvent()` poll loop now blocks with 50ms polling
  intervals instead of exiting immediately when `closed` is set. Affects all three Java executors:
  `BitmapNetExecutor`, `NetExecutor`, `PrecompiledNetExecutor`. TypeScript and Rust were not
  affected (event-driven architectures). Regression introduced in 1.5.0.

## 1.5.0

### Breaking Changes

- **Removed `longRunning` flag.** Long-running behavior is now implicit when environment places
  are registered — no explicit flag needed. Remove `.longRunning(true)` / `long_running: true`
  from all executor builders/options.

- **`close()` is now immediate shutdown (ENV-013).** Queued events are discarded; in-flight
  actions complete; executor terminates. Use the new `drain()` for graceful behavior.

- **Rust: channel type `ExternalEvent` → `ExecutorSignal`.** The async channel now carries
  lifecycle signals (`Drain`, `Close`) alongside events. Wrap events:
  `tx.send(ExecutorSignal::Event(event))`.

### New Features

- **`drain()` — graceful shutdown (ENV-011).** Rejects new `inject()` calls, processes
  queued events, completes in-flight actions, terminates at quiescence.

- **`close()` — immediate shutdown (ENV-013).** Discards queued events, completes in-flight,
  terminates. `close()` after `drain()` escalates from graceful to immediate.

- **Rust: `ExecutorHandle`** — RAII lifecycle wrapper with typed `inject()`/`drain()`/`close()`
  and auto-drain on drop. Re-exported from umbrella crate under `tokio` feature.

### Spec Changes

| Requirement | Change |
|---|---|
| ENV-006 | Reject `inject()` on closed **or draining** executor |
| ENV-010 | Rewritten: implicit long-running from environment places |
| ENV-011 | Rewritten: graceful `drain()` (was "explicit close") |
| ENV-013 | **New**: immediate `close()` |
| Total | 155 → 156 requirements |
