# Verification reference

How to make a net provable, which route proves what, and what silently destroys a proof.

## Contents

1. [What is checkable](#1-what-is-checkable)
2. [The two routes](#2-the-two-routes)
3. [P-invariants and semiflows: why proofs scale](#3-p-invariants-and-semiflows-why-proofs-scale)
4. [Environment modes and the vacuity guard](#4-environment-modes-and-the-vacuity-guard)
5. [What makes a net unprovable](#5-what-makes-a-net-unprovable)
6. [Design choices that keep proofs cheap](#6-design-choices-that-keep-proofs-cheap)
7. [Reading a verdict](#7-reading-a-verdict)
8. [Wiring proofs into the build](#8-wiring-proofs-into-the-build)
9. [Verifier knobs and what they promise](#9-verifier-knobs-and-what-they-promise)
10. [Assertion discipline](#10-assertion-discipline)
11. [When a query does not close](#11-when-a-query-does-not-close)
12. [Whole net versus slices](#12-whole-net-versus-slices)
13. [State-class analysis: what is sound under a cap](#13-state-class-analysis-what-is-sound-under-a-cap)
14. [Proofs do not test action code](#14-proofs-do-not-test-action-code)

---

## 1. What is checkable

| Property | Question it answers |
|---|---|
| `DeadlockFree` | can the net reach a quiescent marking that still holds a token outside the declared sinks? |
| `TerminatesAtSink` | does every quiescent marking have at least one declared sink marked? |
| `MutualExclusion(places)` | can two of these places hold tokens at the same time? |
| `PlaceBound(place, k)` | can this place ever hold more than k tokens? |
| `Unreachable(places)` | can all of these be non-empty simultaneously? |
| `BranchPlaceBound(place, k)` | ν: can more than k tokens of one correlation name pile up here? |
| `JoinedOrDeadLettered(pending)` | ν: is every forked name eventually joined or dead-lettered? |

A result carries a verdict (`Proven` with proof method and inductive invariant, `Violated` with a counterexample trace of markings and transitions, or `Unknown` with a reason), the discovered P-invariants, and statistics (VER-002, VER-003).

### The two stop-condition properties (VER-002, changed in the 5.0 wave)

`DeadlockFree` is **strict**: the error condition is *quiescent* and *some marked place is not a
declared sink*. It answers "is anything stranded". Before the 5.0 wave the condition was
*quiescent* and *no sink holds a token*, so a single token resting in any one declared sink
excused every other token in the marking, which is the opposite of what the name promises. That
older, permissive predicate still exists under its own name, `TerminatesAtSink`: *every quiescent
marking has at least one declared sink marked*.

**The two are not ordered by strength. They invert on the empty marking**, which is why both
exist and why neither could be dropped:

| quiescent marking | `DeadlockFree` | `TerminatesAtSink` |
|---|---|---|
| `{done:1, stuck:1}`, `done` a sink | violated | proven |
| `{}`, fully drained | proven | violated |

So a net that drains completely is deadlock-free, and a net that parks one token in a terminal
place while another sits stranded upstream is not. Pick the one that states your intent, and say
which. If you are reading an older net or an older set of notes and the claim was "a token in a
terminal place is a legitimate stop", that claim is `TerminatesAtSink` now, and it is the drop-in
if you want the previous behaviour:

```java
SmtVerifier.forNet(net).property(SmtProperty.terminatesAtSink())        // Java
```
```ts
SmtVerifier.forNet(net).property(terminatesAtSink()).sinkPlaces(done)   // TypeScript
```
```rust
SmtProperty::terminates_at_sink()                                       // Rust
```
```python
lp.terminates_at_sink()                                                 # Python
```

**Declare sink places for a net that is meant to terminate**, and declare *every* intended
terminal place, not a representative one. Under the strict reading the list is load bearing in
both directions: a terminal place you forget to declare is reported as stranded, and a place you
declare that is not really terminal excuses a token that should have moved on. With no sinks
declared at all, `DeadlockFree` degenerates to "any quiescent marking still holding a token",
which is what most closed nets already assumed.

Expect the change to surface real bugs on nets that verified clean before. Every new violation is
a token stranded outside your declared terminals, which is the thing you wanted found.

## 2. The two routes

### Route A: SMT, IC3/PDR over an untimed abstraction (VER-001, VER-004)

Pipeline: flatten `Xor` into virtual transitions (VER-021), run the structural pre-check, compute P-invariants from the incidence matrix, encode as constrained Horn clauses, hand to Z3 Spacer, decode.

- **Untimed.** Timing only restricts behaviour, so `Proven` on the untimed net holds for the timed net. Nothing proved here is *about* time.
- **Value-blind.** Every value-dependent choice (which `Xor` branch the action writes, which token a correlated input picks) is over-approximated as freely available.
- Therefore `Proven` is trustworthy, `Violated` on the over-approximating path may be spurious, and `Unknown` is common.
- Transport (VER-013): one `z3` process per query, SMT-LIB2 on stdin, `fp.engine=spacer`. `z3` on `PATH` or `LIBPETRI_Z3`, 4.8.0 or newer. All four languages emit byte-identical scripts. `LIBPETRI_SMT_DUMP=<dir>` keeps every script and reply of a run, which is the fastest way to see what the encoder actually asked.

### Route B: state-class graph, Berthomieu-Diaz (VER-010, VER-011, VER-012)

State classes are (marking, DBM zone over firing clocks). Solver-free, no Z3.

- **This is the only route that reasons about time.** Timed reachability, "can this deadline be missed", lives here.
- For ν-nets it is the name-partition quotient (NU-050 Route B): correlation tokens carry interchangeable abstract name symbols, quotiented under name-permutation symmetry, which is what keeps the graph finite even without a budget. Exact over name and time, and it is the route that decides quiescence.
- Undecidability surfaces as truncation into `Unknown`, never as an unsound verdict.

### Which route runs

A ν-net asking about quiescence, or one with no declared budget place, goes to Route B first. If Route B truncates on a bounded quiescence query, the verifier defers to the scalable coloured Route A encoder (NU-053). Budget-declared untimed safety stays on Route A, where IC3 scales.

## 3. P-invariants and semiflows: why proofs scale

A P-invariant is a weight vector `y` with `y·M = c` for every reachable marking. It is a proof that needs no state enumeration, and libpetri conjoins the discovered ones into the transition rules of the encoding so IC3 does not have to rediscover them.

**The exact gate (VER-007) is the single most important cost fact in the whole system.** A candidate law is accepted only if `y·C = 0` and `y·M0 = c` re-check in exact overflow-checked integer arithmetic **and** `y` carries zero weight on every place consumed with `all()` / `at_least(n)` or cleared by a reset arc, because the encoder's fire relation is not linear there.

The consequence in plain terms: one draining arc or reset arc on a busy place kills every basis row whose support touches that place. IC3 then has to rediscover those conservation laws on its own, which on a hundred-place net it will not do inside any practical budget. Draining an input queue is an everyday modelling choice, not an exotic one, so this bites normal designs.

**The semiflow option** (`semiflowInvariants` / `semiflow_invariants`) unions gate-validated non-negative semiflows (the minimal laws, from Farkas and Colom-Silva) into the invariant list. It is off by default so reports stay byte-identical across runs and languages. It is pure strengthening: it can close a proof IC3 could not, and it can never turn a `Violated` into a `Proven`. It does not rescue rows whose support touches an offending place (they fail the same gate); it supplies the *other* minimal laws that avoid the place entirely, which Gaussian elimination had folded away.

**Turn it on when a `PlaceBound` or deadlock query on a loop containing a reset or draining arc comes back `Unknown`.** That is exactly the shape it was built for.

**Siphons and traps (VER-020).** A siphon is a place set that stays empty once empty; a trap stays marked once marked. Commoner's condition (every minimal siphon contains a marked trap) is a cheap structural deadlock pre-check, run for nets up to roughly 50 places, that can settle deadlock-freedom before any solver starts. When it fires, you get an answer in milliseconds. A siphon reported by the analysis is also the best debugging artefact you will get: it names the exact set of places that can drain and never refill, which is usually the bug.

## 4. Environment modes and the vacuity guard (VER-006)

| Mode | Meaning |
|---|---|
| `AlwaysAvailable` | unbounded external source, injection modelled. The sane default. |
| `Bounded(k)` | the environment supplies at most k tokens per firing. Use it to state what you know. |
| `Ignore` | injection not modelled at all. |

`Ignore` with registered environment places can never return `Proven`. It returns `Unknown`, because a property that holds only because env-gated transitions never fire is vacuous. This binds every route that can return `Proven`, including the solver-free structural ones. A `Violated` under `Ignore` is still real.

Practical consequence: under `AlwaysAvailable`, a bare `env -> T -> OUT` makes `PlaceBound(OUT, k)` `Violated` for every finite k. That is the correct answer. An unbounded external source really is unbounded. If you want a bound, put a permit or budget place in front of the consuming transition, which is what a real system does anyway.

## 5. What makes a net unprovable

1. **Unbounded places.** Every one is an infinite dimension. No permit place in front of a producer means `PlaceBound` is genuinely violated and IC3 has nothing to converge on.
2. **Unbounded fresh names.** A ν-net with no budget place and no structural bound the permutation quotient can find is `Unknown` by construction.
3. **Draining and reset arcs on invariant-bearing places** (VER-007). Silent, common, and the difference between seconds and never.
4. **Value-dependent safety.** If the property holds only because "the action never routes to branch B when x < 0", it is not provable. Make it structural: a place, a token, an inhibitor arc.
   **The same, one step harder: anything held outside the net.** A flag on a service, a row in a database, a cache entry, a counter in a closure, an actor's field. The verifier reads places, arcs, cardinalities, timing and name equality, and nothing else, so a property resting on any of those cannot be proven now or later. This is a permanent limit, not a solver budget. The fix is always the same: move the fact into the marking, then prove it.
5. **Inhibitor-heavy models.** Inhibitor arcs are what make the formalism Turing-complete. Use them where they express the domain, and expect the decidable fragment to shrink as you add more.
6. **Heavy independent-branch parallelism under Route B.** The name-partition graph has no partial-order reduction and will truncate. Fixes: declare a budget so the coloured Route A encoder can take the query, reduce places shared between parallel branches, or push independent work into separate subnet instances.
7. **Multi-token production into one output place in one firing.** The proved over-approximation fixes the abstract gain at one token per branch place. Producing several is outside the proof and is a live route to a false `Proven` on `PlaceBound`.
8. **A terminating net with an incomplete sink list.** Under the strict `DeadlockFree` every
   terminal place you failed to declare reads as a stranded token. The failure is loud and the
   fix is to finish the list, but it will look like a design bug until you do.
9. **Priority-dependent safety.** The SMT encoder never encodes priorities and Route B is priority-blind unless you opt into `CONFLICT` semantics (NU-052). If your argument is "the high-priority transition always wins", either opt in or make the exclusion structural.

## 6. Design choices that keep proofs cheap

- **Bound everything structurally.** A permit place consumed on entry and returned on exit *is* a P-invariant (`inFlight + permits = k`) and hands you a `PlaceBound` for free.
- **Prefer `one()` and `exactly(n)`.** Reserve `all()` and `at_least(m)` for places whose counts no proof depends on. If you must drain a queue, drain it into a place that no invariant needs to weigh.
- **Keep reset arcs on scratch and side places**, never on resource-counting places.
- **Declare sink places** for every intended terminal state.
- **Declare environment places to the verifier** and pick a mode that models injection.
- **Declare the ν budget place** and keep the mint-to-join fragment clean (see `nu-nets.md`).
- **Use subnet instances rather than one shared place set** to keep interleavings and name pools apart. Isolation by renaming is free at run time and much cheaper to verify.
- **Verify subnets in isolation first** (MOD-051 wraps each input port in an environment place), then re-verify the flat composed net. Composition guarantees the flat result matches a hand-written equivalent (MOD-050), so an isolated proof is real evidence, not a rehearsal.
- **Turn on the semiflow option** when a bound on a loop with a reset arc comes back `Unknown`.
- **Enable `CONFLICT` priority semantics only when a spurious stall traces to priority blindness.** Its side conditions matter: strictly higher priority, real competition for a shared consumed place (a place holding enough tokens for both demands is not a conflict), ready no later by class-relative readiness, and the higher-priority transition must actually be able to fire, so a name-disabled join must not pre-empt a drain.

## 7. Reading a verdict

**`Proven`** means the *model* has the property under the stated hypotheses. It is not a claim about your action code, and it never will be. What connects model to executor is a separate, machine-checked argument (see `lean/README.md` in the repo) covering the untimed abstraction, token conservation in one precompiled firing, backend refinement in the immediate fragment, and ready-queue ordering. That argument deliberately does not yet cover real-valued time, the async action plumbing, or the full ν match cache.

**`Violated`** on Route A may be spurious, because the abstraction is value-blind. Read the counterexample trace before believing it. Ask: does this trace require an action to route somewhere it never routes? If yes, the model is under-specified. Fix the model (usually by making the choice structural), do not argue with the verifier.

And say which of the three you have. A property you did not run is "not checked", not "fine". A net nobody proved anything about is unverified, however carefully it was read: that is the whole reason this machinery exists.

**`Unknown`** is information, not failure. Read the reason. The three common ones map to fixes: truncation (bound something, split the net, or declare a budget), vacuity (`Ignore` mode with env places registered), and a lost invariant (turn on semiflows, or move the draining arc).

## 8. Wiring proofs into the build

Treat a property as a test, from the first commit, not as a milestone at the end.

- **Prove subnets in isolation as they are written.** Fast, and the failure names one component.
- **Prove the whole net too.** Composition can create deadlocks that neither part had, which is the entire reason composed systems are hard.
- **Assert the verdict, not the absence of an exception.** A test that passes on `Unknown` proves nothing, and it will pass forever after a change silently destroys an invariant. Assert `Proven` explicitly.
- **Give each query a solver budget and treat a timeout as a red test**, then fix it by changing the net, not by raising the budget. A proof that needs 15 seconds today needs forever after the next feature.
- **Keep the counterexample.** When a property first fails, the trace is the design review.
- **Re-prove on every change to the net.** Nets are code. The proof is the test suite for the part of the behaviour tests cannot cover: the interleavings you did not think of.

## 9. Verifier knobs and what they promise

Every one of these changes what a verdict *means*. Set them explicitly, never by inheriting a default.

**`semiflowInvariants`.** The single largest lever available. In one production net, the same query with the same encoding went from 50 minutes to `Unknown` to **15 seconds to `Proven`** when it was turned on, and safety queries went from 50 seconds to about 1 second. The reason is mechanical: without it the encoder sees only the null-space basis, and the exact gate had dropped most of the conservation laws because their support touched a consume-all or reset place. Diagnose by grepping the report for lines saying a semiflow was dropped because its support intersects a consume-all or reset place. Off by default so reports stay byte-identical.

**`sinkPlaces`.** This is the design surface of a deadlock-freedom claim: what you list is what
you are promising is a legitimate place to stop. Write the list before you write the assertion.
It helps to split it into "state that outlives a unit of work" and "terminal outcomes of a unit
of work", because the second group is the one that changes when you add a feature. Since the 5.0
wave the list binds both ways under `DeadlockFree`: an undeclared terminal place is a violation,
and an over-declared one silently excuses a token. It is read by `TerminatesAtSink` too, with the
opposite polarity, so never copy a sink list between the two properties without re-reading it.

**`budgetPlaces`.** Name every place whose consumption gates a fresh-name mint. It is **not validated**: a name that fails to resolve silently degrades the verdict to `Unknown`, which is indistinguishable from an honest one unless you check the route.

**`carrierPlaces`.** Validated, and it throws. It names the intermediate places threading a minted name through to the join, so the branches share one colour instead of each minting independently. Keep the list in one constant and filter it against the net's places so that slice nets still work.

**`environmentMode`.** Always set it. `bounded(k)` is sound and states what you know; `alwaysAvailable` is the honest default for an open input; `ignore` with declared environment places is refused as vacuous. Defaults have changed between releases, and inheriting one silently changes what your verdict means.

**`nuMaxClasses`** is a route selector as much as a cap. A large cap lets the state-class route run to exhaustion (and can take the process with it). A deliberately tiny cap makes it truncate at once so the verifier defers to the coloured IC3 route, which is sometimes exactly what you want for a whole-net quiescence query.

**Conflict priority semantics** prunes interleavings where a low-priority drain steals from a high-priority consumer. Reach for it only when a spurious stall traces to priority blindness, and remember that priority blindness is a *feature* for quiescence: admitting more behaviour than the executor is what makes the proof carry.

## 10. Assertion discipline

**Never write `assertFalse(result.isViolated())`.** It is false for `Unknown` too, so a proof lost to a timeout passes silently and the test becomes vacuous forever after. Write a small assertion helper and use it everywhere:

- `assertProven(result, message)` fails on `Violated` **and** on every undetermined verdict, with a message naming the two real remedies: raise the budget, or reduce the net.
- When the exact route matters (because a budget-place typo would otherwise degrade to a plausible-looking `Unknown`), also assert that the report names the exact route.
- `assertProvenOrDeferred(result, allowedReason, message)` accepts an `Unknown` only when the reason string contains a specific named deferral, so a timeout cannot masquerade as an expected limitation.

**The ratchet pattern**, for a property that is architecturally undecidable today: assert both directions. Fail on `Violated`. Fail on `Proven` with a message saying "promote this to a real proof and delete this ratchet". Accept only `Unknown`. Its lifecycle is the point: in the system these notes come from, a ratchet existed, fired when a later library release made the property decidable, the claim was promoted, and the ratchet was deleted.

**When a claim is still undecided, delete the test and write down what remains unproven and why it is not load-bearing.** Two such claims survived in that system, both relational with no separating linear law. The documentation records that neither can cause a deadlock: what is unproven is the correctness of a choice, not liveness.

**Budgets are ceilings, not costs.** A converging proof spends only what it needs, so a generous timeout is free in the green case. Size it from the *contended* worst case: one proof measured 7 seconds in isolation on four cores and 284 seconds inside the full suite on the same four cores, a 38x amplification from competing solver processes. Leave roughly a quarter of the cores idle, and cap the processor count each fork sees so it does not size its garbage collector from all of them. Heap matters for solver convergence, not only for state spaces: a query that converged in 7 to 17 seconds with a 4 GB heap blew a 60 second budget with 2 GB.

**Never judge a verification change by pass or fail alone.** Diff the per-query durations and treat "converged at almost exactly the timeout" as a regression, even on a green build.

## 11. When a query does not close

Work down this ladder, in order. The early rungs are cheap and the later ones are honest.

1. Turn on semiflow invariants.
2. **Fix the net, not the query.** Most of the hard-won fixes in `patterns.md` section 15 came from this rung: a fake `Xor` decided by hidden action state, a consumer-less marker accumulating one token per miss, a correlation name taken from a read arc.
3. Force a different route (the class cap, or declaring a budget so the coloured route can take the query).
4. Shrink the net to a slice. Declare the interface place as a sink in the producing slice and as a seed in the consuming slice.
5. Raise the timeout or the heap.
6. Delete the test and document the gap.

## 12. Whole net versus slices

Slices are fast, local signal. Build them from the *same* subnet composition calls as production, so they cannot drift.

**Do not present chained slice proofs as the guarantee.** The system these notes come from tried, then retracted it in its own documentation, for reasons that generalise: the slices were not a partition (one orchestrator subnet sat in two of them), around thirty places appeared in two slices outside the declared interface, each proof started from a hand-written marking rather than from every reachable state, and every slice net was closed. A concrete leak: one place was a declared sink in two slices while its only drain lived in a third.

**The whole-net proof from the production start marking is the guarantee.** Phase-scoped claims are useful, but nothing proves that a set of phase entry states covers every reachable session state.

## 13. State-class analysis: what is sound under a cap

- "A goal marking was reached" is sound at **any** cap: a witness found is a real witness.
- "The graph is complete" (boundedness) is sound: exceeding the cap returns incomplete and fails loudly.
- **Universal claims over the enumerated classes are unsound under a binding cap.** Use the SMT route for those.
- A goal place list is a **disjunction**. A conjunctive claim needs you to walk the graph yourself.
- The state-class graph is priority-blind and name-blind. On a correlated net, the name-blind graph is a sound instrument for boundedness (it over-approximates, so boundedness there implies boundedness in reality), but name-blind deadlock freedom on a correlated net is **not** sound.
- Its environment handling never consumes environment tokens, so it cannot prove that an environment cell clears. Use the SMT route with a bounded environment mode for that.

## 14. Proofs do not test action code

A proof verifies topology. It never executes an action. Two guards close that gap:

- **A missing output write for a newly added arc is a runtime violation, not a test failure.** Treat adding an arc and updating the action as one atomic change.
- **A failed transition is logged, not thrown.** Every executor-level test should collect the net's events and assert that no transition failed, otherwise an assertion can pass green while an action blew up and its branch silently defaulted.

Two smaller habits worth copying: match transition names by suffix in tests, because composition prefixes them; and assert relative rather than adjacent ordering, because concurrency makes interleaving legitimate. Also add one configuration-sanity test asserting that every declared environment place resolves to a place in the composed net. Otherwise injection succeeds, the token lands nowhere, and the feature stops working with no error at all.
