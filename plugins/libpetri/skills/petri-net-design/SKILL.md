---
name: petri-net-design
description: >-
  Design, review and debug Coloured Time Petri Nets with libpetri (Java, TypeScript, Rust,
  Python) so they stay provable as they grow: data in tokens, decisions in topology, budgets as
  places, reusable subnets, correlated fork/join. Use when modelling a workflow, agent, protocol,
  pipeline or session lifecycle as a Petri net, adding places or transitions, debugging a net that
  deadlocks, stalls or never fires, bounding retries or concurrency, joining parallel work by
  identity, or explaining a verification that returned Unknown or a surprising Violated. Also for:
  libpetri, places, tokens, transitions, markings, firing, inhibitor/read/reset arcs, subnets,
  compose, nu-nets, ν-nets, state-class graphs, P-invariants, semiflows, siphons, traps,
  deadlock freedom, Z3. In a libpetri project, "model this flow" or "orchestrate these steps"
  means this skill.
---

# Designing provable Petri nets with libpetri

You are helping someone model a real system as a Coloured Time Petri Net and keep it provable while it grows. The net is not a diagram of the program. The net **is** the program: places hold typed data, transitions do work, arcs declare flow, timing makes deadlines part of the model, and the marking is the state.

## The one rule everything else follows

**If the net must reason about it, it has to be structural.** A place, an arc, a cardinality, a name equality. Anything else (a field in an action, a map on the side, a boolean in a session object) is invisible to the firing rule and invisible to the verifier, so it can neither coordinate correctly nor be proved.

Almost every bad libpetri design is one of two moves:

1. State escaped the marking, so a race came back.
2. A decision escaped the topology, so the verifier cannot see it.

When you review a net, look for those two first.

## The design loop

Work in this order. It is much cheaper than reordering later.

1. **Name the domain concepts and give each one a typed place.** `Place<Order>`, `Place<DraftReply>`, `Place<ToolCall>`. One concept per place.
2. **Draw the world boundary.** Everything entering from outside arrives by injection into an environment place. Everything leaving is read from an output place or observed through the event store. There is no third door.
3. **Make every decision topology.** A branch is competing transitions or an `Xor` output spec, never an `if` inside an action that the model cannot see.
4. **Bound everything that can grow.** Retries, in-flight work, concurrency limits, correlation groups: each becomes a place with a fixed number of tokens, not a counter.
5. **Say where the net may rest.** Declare the sink places of every legitimate resting state, and conditional sinks for designed halts, before you write the first stop property.
6. **Factor repeated shapes into subnets** with named ports, and instantiate them per use.
7. **Reach for correlation by identity only when several groups really are in flight at once** over shared places.
8. **Write the proof with the net, not after it.** A deadlock-freedom assertion on the subnet you just wrote costs seconds and catches the interleaving you did not imagine.

Then iterate: each new feature is new places and transitions, and the proofs you already wrote tell you immediately when it broke something.

## Habits that make nets work

### The marking is the only state, and a read outside it is a race

The marking is owned by one logical orchestrator thread, without locks. Actions never touch it: an action reads its consumed inputs and read-arc values from the context and declares outputs through the context. A transition's preconditions are checked and consumed in one indivisible step, which is the whole point.

Anywhere else you can store state, you can read it, and that read happens outside the indivisible step. A session object, a context bag, a cache, a static field, an actor's instance state, a database row, "just this one flag" on the service: each is a check-then-act gap, the exact bug you adopted a Petri net to remove. So:

- **If the net needs to know it, it is a token.** If the net never reads it back, keep it out. A value the net branches on must be a token; if an action fetches it, no proof can mention it.
- **Session data belongs in places.** A per-session net holds its conversation, config, phase and budgets as tokens in session-scoped places, read with read arcs, not as a `session.state` map that actions poke at.
- **External stores are write-only from the net.** Persist by firing a transition that writes. Read only at startup, to seed the initial marking.
- **Counters, budgets, phases, mutexes and permits are places, not token fields.** An integer inside a token is invisible to the verifier. A place holding k tokens is a P-invariant.
- **A transition calling an HTTP client or a model provider is ordinary implementation**, not an integration seam. The integration seams are environment places in and output places or event-store subscriptions out; there are no callbacks into transitions and no privileged side channel.

The tell in review: if you can describe a bug as "we checked X and by the time we acted on it, X had changed", X was in a store and belonged in a place.

### Colour the places by domain concept

Typed places are the only compose-time contract you get: they let the compiler catch a mis-wired composition, and they make the exported diagram read as a process rather than plumbing. A single untyped everything-bag place threaded through the net throws both away.

Colour describes *what the work is*. It is not a coordination mechanism: verification is value-blind, so nothing that depends on a token's value can be proved.

### Decisions are topology, not code

There are no guards and no per-token value predicate anywhere in the model, deliberately. Model a decision as either

- **competing transitions** consuming the same token, distinguished by their other preconditions (an inhibitor arc, a permit, a read arc on a mode place), or
- **an `Xor` output spec** on the producing transition, where the action picks a branch and the verifier sees every branch as a possibility.

The verifier reads production from the output spec, never from the action. If the action can write somewhere the spec does not declare, the model is a lie about the program and a `Proven` on it is worth nothing.

### Bounded resources are places, not counters

The most reusable pattern in this document:

- A budget place seeded with N unit tokens by the transition that starts a unit of work. That transition also carries a reset arc on the budget place, so a new request clears any stale allowance before seeding.
- The retrying transition consumes one budget token per attempt, at high priority.
- A low-priority fallback with an **inhibitor arc** on the budget place fires only when the budget is empty and emits the terminal outcome (escalate, canned answer, give up).

No action ever asks "do I have budget left". The decision lives in the marking, so it is race-free and checkable: `PlaceBound(budget, N)` is provable, and so is "the fallback is reachable".

The same shape covers concurrency limits (a permit place with N tokens, consumed on start and returned on completion, which gives `inFlight + permits = N` for free), mutexes (N=1), pool capacity and rate limits. Prefer it over any runtime concurrency-limit option: a limit the verifier can see is worth more than one it cannot. A leaky-bucket rate limiter is a permit place plus a timed refill:

```
PERMITS        seeded with `burst` unit tokens
CALL:    In.one(REQUEST), In.one(PERMITS)          -> IN_FLIGHT
DONE:    In.one(IN_FLIGHT)                         -> RESULT
REFILL:  read(BUCKET_TICK), delayed(interval)      -> PERMITS      (up to `burst`)
REJECT:  In.one(REQUEST), inhibitor(PERMITS)       -> THROTTLED
```

Make it a subnet with `REQUEST`, `ADMITTED` and `THROTTLED` as ports; instantiate it per dependency with its own rate, or fuse the permit places of several instances when the quota is shared. `references/composition.md` works both cases.

### Failure is a token, not an exception

There is no rollback. When an action fails, its consumed tokens are gone. Any failure the system must react to is an explicit `Xor` branch into a failure place; "the exception propagates" is not a design. Decide per transition whether a failure needs a retry path, a dead-letter place or a compensating transition, and if so, put it in the output spec.

A timeout branch **excludes the late output, it does not cancel the work**. Side effects of an abandoned action still happen. If cancellation matters, model it (an inhibitor arc on a cancel place), do not hope for it.

### Every token needs a consumer, in every reachable state

A token nobody can consume is a hang in production and an unbounded place in the model, and unbounded places stop proofs from closing. Whenever you add a place, answer: who consumes this, and are they enabled in every state where this token can exist?

- **Every "nothing happened" branch needs a consumer.** An `Xor` leg emitting "no result this time" is still a token. Give it a drain, even a no-op one, or it accumulates one token per miss for the life of the net.
- **Every exit path emits its completion marker**, including the error, discard and drain paths. A branch that forgets its marker hangs whatever joins on it; a branch that emits two lets two units of work run at once.

### Make the structural branches equal the runtime outcomes

- **Model `Xor` of `And`, not `And` of `Xor`.** Two independent `Xor` outputs can produce a combination your code never produces, and the analysis will treat it as reachable. One `Xor` whose legs are complete output sets makes structural branches exactly the runtime outcomes.
- **There is no optional output.** Write `xor(realOutput, voidSink)` and give the sink a drain. Validation succeeds only when **exactly one** branch of the spec claims exactly the set of places the action wrote; an extra write into a declared place that the selected branch did not ask for is a violation. `And` is unordered.
- **An `Xor` leg chosen by hidden action state is unprovable.** If the action decides "is this the last result", the analysis will take the other leg on the last result and strand the batch. The provable encoding is a pending-marker place per outstanding job plus an inhibitor arc on it.
- **"Optionally use X" is not `read(X)`.** A read arc is a precondition: when X is empty, usually the normal case, the transition never fires. Use a pair: consume X at high priority, inhibited by X at low priority.

### Decide, then emit

The executor consumes inputs before the action runs, does not restore them on failure, and commits outputs only on normal completion. So split each action into a part that computes and may throw but writes nothing, and a part that writes the complete output set once and cannot throw. An action that writes in a `try` and again in the `catch` produces duplicate tokens and both legs of an `Xor`, invisible to any proof. Wrap the whole body, including metrics and logging: an unguarded observability call between consume and write destroys the token when it throws.

### Cancellation, barge-in and staleness are arcs

- A **read arc plus an inhibitor arc**: the streaming transition reads the generation or session token and is inhibited by a barge-in place. Injecting into the barge-in place stops further firing immediately, with no flag to observe at the wrong moment.
- **Reset arcs clear stale state** at the boundary: the transition that accepts new input resets the in-flight places, so leftovers from the interrupted unit cannot combine with the new one.

A cancellation flag read inside an action is the classic stall: the action returns early, tokens sit in the in-flight place forever, and the marking never learned about the cancellation.

### Observability rides the event store

Tracing, logs, metrics, audit and live debugging all hang off an event-store decorator wrapping the net's event stream. Do not wrap actions or invent an execution-context hook for observation. Events are an observation channel, never a data-flow channel: if a downstream step needs a value, it travels as a token.

### When something "cannot be done", find the structure first

With inhibitor arcs this model is Turing-complete. Almost every "libpetri cannot express X" is "I have not found the places yet". Work the topology before proposing a new API or escape hatch:

| "I need..." | Structure |
|---|---|
| streaming output | per-chunk injection into an environment place, read arc on the generation token for staleness |
| cancel mid-flight | inhibitor arc on a cancel place, reset arcs for cleanup |
| pause and resume | an urgent transition blocked on a resume place |
| bounded retry | budget place plus inhibitor fallback |
| rate limit or mutex | permit place with N tokens |
| a time window | window timing plus a read arc on the state that must hold |
| fan out and rejoin | N transitions plus a cardinality join, or ν correlation when groups overlap |
| a tool or external service | its own subnet with typed ports; dependencies are shared places wired at composition |
| per-step observation | event-store decorator |

Genuine gaps are limited to observation and persistence seams that do not change firing semantics. A helper that lets an action emit tokens mid-flight outside the output spec is not a gap; it is the hole this model exists to close. A flat list of tool calls dispatched inside one action discards every reason to use this model.

## The modelling vocabulary, and how each piece is misused

### Arcs

| Arc | Requires | Consumes | Use it for | Classic misuse |
|---|---|---|---|---|
| input | yes | yes | ownership transfer: this work is mine now | draining with `all()` when `one()` would do |
| output | no | produces | the declared effect surface the verifier reads | declaring outputs the action only sometimes writes |
| inhibitor | absence | no | negative precondition: pause, kill switch, not yet | using it as a mutex where a permit token is the honest model |
| read | yes | no | shared state many transitions consult | expecting it to serialise (readers never conflict) or to see every token (it peeks the front) |
| reset | no | yes, all | cleanup, cancel, purge stale state | putting it on a place that carries a conservation law |

Consumption is the only ownership primitive, and it is race-free because the match is part of the firing rule. **If two things must not happen at once, make them consume the same token, not read the same flag.** Two input arcs on the same place are rejected; use one arc with a cardinality.

Prefer `one()` and `exactly(n)` over `all()` and `at_least(n)`. Draining arcs destroy the linear conservation laws that make proofs converge (see `references/verification.md`). Drain only when the domain means "take everything", and into a place no invariant needs to weigh.

### Timing

| Timing | Interval | Enforcement |
|---|---|---|
| `immediate` | `[0, inf)` | fires as soon as enabled |
| `delayed(d)` | `[d, inf)` | lower bound only |
| `deadline(by)` | `[0, by]` | **hard**: force-disabled past the bound plus a tolerance (default 5 ms, configurable, `0` is strict), emits a timed-out event |
| `window(e, l)` | `[e, l]` | **hard**, same reaping |
| `exact(at)` | `[at, at]` | **soft**: never force-disabled, fires at the first opportunity at or after the target |

The clock starts at enablement and restarts on re-enablement; partial elapsed time is discarded. That includes the gap inside one firing: when another transition takes a token this one consumes or reads and puts one back, or drains the place with a reset arc, the clock restarts unless the place kept enough tokens. Good for refresh and cancel semantics, a trap for deadline modelling. To keep a clock running while another transition uses a shared token, let that transition read it instead of consuming it.

`exact()` is a logical instant for simulation and proof, not a real-time guarantee. For a wall-clock lower bound use `delayed`; for a hard bounded window use `window`.

The clock is injectable per executor (TIME-015), and the injected clock owns the wait as well as `now`, so timed nets test deterministically under virtual time and run inside a host that drives time itself (a durable workflow runtime, a replay). Action `timeout(...)` is the exception: it elapses in real time, so a net that relies on it is not fully virtualizable.

The primary-and-fallback idiom is timing plus priority: primary at high priority and immediate, fallback at low priority and delayed. The fallback is ready only if the primary did not take the token first. Use it for silence recovery, escalation and slow paths.

### Priority

Ready order is priority descending, then enablement time, then declaration order. Priority is a scheduling policy, and by default **no analysis sees it**. If a safety argument depends on "the high-priority transition always wins", make the exclusion structural (inhibitor arc or permit) or opt into conflict-aware priority semantics explicitly.

### Environment places

An environment place marks the world boundary. Injection is thread-safe from anywhere and wakes an idle orchestrator immediately.

- **Registering any environment place makes the executor long-running**, because the world can always inject more. There is no separate flag. A net with no environment places ends at quiescence.
- **An unbounded external source really is unbounded.** A bare `env -> transition -> place` chain makes any bound on that place genuinely violated. Put a permit place in front of the consuming transition, as a real system would.

### The execution loop, and the trap inside it

Each cycle: process completions, process external events, update enablement, enforce deadlines, fire ready transitions, await work.

**Deposits made during a pass are not visible to firing in that same pass.** If a high-priority transition consumes a token and its synchronous action refills the place immediately, a lower-priority transition waiting on that place stays disabled until the next cycle. This binds counts as well as presence, and draining arcs too: a drain firing later in the same pass takes only what was there when the pass began. When a net behaves one cycle later than you expected, this is usually why.

## Verification: start on day one, not at the end

Treat properties as tests. Write the first one with the first subnet.

What you can check: deadlock freedom, termination at a sink, mutual exclusion, place bounds, unreachability, and for correlated nets the branch-place bound and "every fork is eventually joined or dead-lettered".

The two stopping properties are different claims. `DeadlockFree` is strict: it fails on a quiescent marking that holds a token **outside** the declared sink places, so it answers "is anything stranded". `TerminatesAtSink` fails when a quiescent marking has **no** declared sink marked. They invert on the empty marking: a fully drained net is deadlock-free and does not terminate at a sink. Declare every place where the net legitimately rests, because one you leave off reads as a stranded token. For a designed halt or pause marker, under which interrupted work legitimately stays where it was, declare conditional sinks (`sinkPlacesWhen(marker, ...places)`).

Facts that shape designs (details, numbers and flags in `references/verification.md`):

1. **The SMT route is untimed and value-blind.** `Proven` holds for the timed net too; `Violated` there can be spurious, because the abstraction lets an action route anywhere its spec allows. Read the counterexample before believing it.
2. **An ordinary untimed net is usually decided by enumeration of the state-class graph**, exactly and with a real firing sequence as counterexample, orders of magnitude faster than IC3 on pipelines. It is skipped for timed nets, ν-nets and nets with environment places. `result.route` says which route answered.
3. **The state-class route is the only one that reasons about time.** For correlated nets, quiescence is decided by the name-partition state-class route first and, for budget-declared nets where that truncates, by coloured IC3/PDR; the over-approximation fallback never proves it.
4. **P-invariants make proofs converge**, and one draining or reset arc on a busy place destroys every invariant whose support touches it.
5. **`Unknown` is information, and the timeout is the first suspect.** Raise it before concluding anything. Then read the report before reaching for a flag: `Dropped invariant:` / `Dropped semiflow:` lines naming a draining or reset place point at `semiflowInvariants`; a quiescence proof on a pipeline points at `stateEquation(true)`; otherwise bound something, declare the budget place, declare sinks, or move a draining arc.

### Say proven, or say untested

There are only three honest statements about a property, in code comments, commits, design documents and conversation:

- **"Proven"**, naming the property, the initial marking, the environment mode and the route, because a verdict without those is not reproducible.
- **"Violated"**, with the counterexample trace, the most useful artefact in this system.
- **"Not checked"** or **"came back Unknown"**. Both are fine. Neither is "it is correct".

Never call a net correct, safe, race-free or deadlock-free because you read it and it looked right; that is the failure mode this model exists to replace. In tests, never assert `assertFalse(isViolated())`: it is also true for `Unknown`, so a proof lost to a timeout passes silently. Assert `Proven`.

Two limits belong in the same breath:

- **A proof is about the model, not your action code.** It says nothing about whether an action writes what its spec declares, throws halfway, or calls a service that is down. Executor-level tests cover that half and are not optional.
- **Anything outside the net is outside the proof, permanently.** The verifier reads places, arcs, cardinalities, timing and name equality. A flag in a service, a database row, a counter in a closure or a branch picked on a value are invisible to it. Wanting to prove something the model cannot see is the design telling you the fact belongs in the net: make it a place, a token, an inhibitor arc, then prove it.

Read `references/verification.md` before tuning anything: the route split, the exact-gate rule that decides proof cost, the semiflow option, siphons and traps, environment modes and the vacuity guard, open-net contracts, and wiring proofs into a build.

## Where to read more

The files below sit next to this `SKILL.md`; read them from this skill's own directory.

| Read this | When |
|---|---|
| `references/verification.md` | any proof question: what is checkable, why a query is `Unknown`, keeping proofs cheap, open-net contracts, CI wiring |
| `references/composition.md` | building or reusing subnets, ports versus channels, instantiate versus compose, fusion, the cross-language place-equality divergence |
| `references/nu-nets.md` | correlating parallel work by identity: minting, matching, the tie-break, the budget place, the fragment rules the exact routes require |
| `references/patterns.md` | worked topologies from a production system: per-session nets, turn handling, barge-in, budgets, queue draining, and changes that made real nets provably deadlock-free |
| `references/lang-java.md` and the other `lang-*.md` | the per-language facts that change a design decision: API spellings, snapshot/restore, threading |

libpetri's requirement specification is the normative source for semantics; its registry is `spec/00-index.md`, at `<repo-root>/spec/00-index.md` inside a libpetri checkout, otherwise https://github.com/debe/libpetri/blob/main/spec/00-index.md. Cite requirement IDs (`VER-013`, `NU-024`, `MOD-041`) when you claim something about semantics, and read the index rather than trusting a remembered count. If you can open neither, say the claim is unverified rather than inventing an ID.

## Anti-patterns worth naming out loud

- A flag, counter, map, session object, cache or static field outside the net that a transition depends on, or that an action reads.
- An action that writes to a place its output spec does not declare, or outside the branch its spec selected, or a transition that both declares outputs and keeps the built-in passthrough.
- A single untyped payload place threaded through the whole net.
- A retry counter inside a token.
- Relying on a timeout branch to cancel work, or expecting rollback when an action fails.
- Draining or reset arcs on the places that carry your invariants.
- A net verified with an incomplete sink list, or with `DeadlockFree` asserted where "some sink got marked" (`TerminatesAtSink`) was meant.
- Verifying with environment injection ignored while environment places are registered: it can never return `Proven`.
- A correlation map in a join action instead of correlation in the firing rule, or a match spec on a net where only one group is ever live.
- A read arc meaning "use this if it happens to be there".
- An `Xor` leg whose choice lives in action state the model cannot see.
- A "nothing happened" marker with no consumer.
- A test that passes on `Unknown`, or a net called correct on the strength of having read it.
- `/` inside a place, transition or subnet name.
- Auto-translating another orchestrator's graph into a net: you inherit its shape without inhibitor, read, reset, timing or priority arcs, so it is no more verifiable than what you started with. Migration means redesign.

## Decision checklist

Run this before calling a net design done.

- [ ] Every domain concept has its own typed place; no untyped catch-all payload.
- [ ] Every value a transition depends on arrives as a token or a read arc; no fact the net branches on lives in any store outside it.
- [ ] Every branch an action can take is declared, each `Xor` leg is a complete output set, and every action decides before it emits its output set exactly once.
- [ ] Every failure path that matters is a place, not an exception.
- [ ] Every unbounded thing (retries, in-flight work, concurrency, correlation groups) is bounded by a place with a fixed token count.
- [ ] Every token has an enabled consumer in every reachable state, including every "nothing happened" marker.
- [ ] Cancellation and staleness are inhibitor and reset arcs, not flags.
- [ ] Repeated structure is a subnet with named ports, instantiated per use, with port names exported rather than duplicated as strings.
- [ ] Correlation by identity is used only where several groups are live over shared places, and every minting net declares a budget place.
- [ ] Draining and reset arcs stay off the places whose counts a proof depends on.
- [ ] Sink places are declared for every resting state (conditional sinks for halts), and the stop property asserted states the intent (`DeadlockFree` for "nothing stranded", `TerminatesAtSink` for "we reached a sink").
- [ ] Environment places are registered with the verifier under a mode that models injection.
- [ ] At least one property per subnet and one on the composed net, each asserting `Proven`, and every correctness claim names property, verdict and marking.
- [ ] No design decision rests on priority alone, on same-pass deposits, or on a timeout cancelling work.
