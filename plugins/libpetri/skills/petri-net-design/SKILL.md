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

Your job is to keep every fact the system depends on inside that structure, because that is what makes concurrency safe and what makes proofs possible.

## The one rule everything else follows

**If the net must reason about it, it has to be structural.** A place, an arc, a cardinality, a name equality. Anything else (a field in an action, a map on the side, a boolean in a session object) is invisible to the firing rule and invisible to the verifier, so it can neither coordinate correctly nor be proved.

Almost every bad libpetri design is one of these two moves:

1. State escaped the marking, so a race came back.
2. A decision escaped the topology, so the verifier cannot see it.

When you review a net, look for those two first.

## The design loop

Work in this order. It is much cheaper than reordering later.

1. **Name the domain concepts and give each one a typed place.** `Place<Order>`, `Place<DraftReply>`, `Place<ToolCall>`. One concept per place. Resist the single wide payload that gets threaded everywhere: the place type is the only compose-time contract you get, and a readable net is one you can point at during an incident.
2. **Draw the world boundary.** Everything entering from outside arrives by injection into an environment place. Everything leaving is read from an output place or observed through the event store. There is no third door.
3. **Make every decision topology.** A branch is competing transitions or an `Xor` output spec, never an `if` inside an action that the model cannot see.
4. **Bound everything that can grow.** Retries, in-flight work, concurrency limits, correlation groups: each becomes a place with a fixed number of tokens, not a counter.
5. **Factor repeated shapes into subnets** with named ports, and instantiate them per use.
6. **Reach for correlation by identity only when several groups really are in flight at once** over shared places.
7. **Write the proof with the net, not after it.** A deadlock-freedom assertion on the subnet you just wrote costs a few seconds and catches the interleaving you did not imagine.

Then iterate: each new feature is new places and transitions, and the proofs you already wrote tell you immediately when it broke something.

## Habits that make nets work

### Data flows as tokens. Nothing bypasses the marking.

The marking is the state. It is owned by one logical orchestrator thread, without locks, and actions never touch it: an action reads its consumed inputs and read-arc values from the context, and declares outputs through the context.

So:

- **Never read external mutable state inside an action.** Not a session store, not a database row, not a cache. That reintroduces exactly the check-then-act race the model exists to remove. External stores are write-only exports from the net.
- **If the net needs to know it, it is a token.** If the net never reads it back, keep it out.
- **The only way in is injection into an environment place; the only way out is an output place or an event-store subscription.** No bridges, no callbacks into transitions, no privileged side channel. A transition action calling an HTTP client or a model provider is ordinary implementation, not an integration seam.
- **Counters, budgets, phases, mutexes and permits belong in places, not in token fields.** An integer inside a token is invisible to the verifier. A place holding k tokens is a P-invariant.

### Anywhere you can store state, you can read it, and the read is the race

Watch for the store. A session object, a context bag, a cache, a static field, an actor's instance
state, a "just this one flag" on the service: every one of them is a place to put something, which
makes it a place to read something, and the read is where the race lives. The whole point of this
model is that a transition's preconditions are checked and consumed in one indivisible step. A read
of a store inside an action happens outside that step, so it is a check-then-act gap, and you have
reintroduced exactly the bug you adopted a Petri net to remove.

The rule is not "avoid mutable state". The rule is that the marking **is** the mutable state, and
there is only one of it:

- **Session data belongs in places.** A per-session net holds its conversation, its config, its
  phase and its budgets as tokens in session-scoped places, read with read arcs. It does not hold a
  `session.state` map that actions poke at.
- **External stores are write-only from the net's point of view.** Persist by firing a transition
  that writes. Never read back mid-execution. Read at startup only, to seed the initial marking.
- **A value the net branches on must be a token.** If an action fetches it, the model cannot see it
  and no proof can mention it.

There is a tell for this in review. If you can describe a bug as "we checked X and by the time we
acted on it, X had changed", X was in a store and belonged in a place.

### Colour the places by domain concept

Typed places are what let the compiler catch a mis-wired composition, and they are what makes the exported diagram readable as a process rather than as plumbing. A single untyped everything-bag place throws that away and takes the diagram with it.

Colour describes *what the work is*. It is not a coordination mechanism: verification is value-blind, so nothing that depends on a token's value can be proved. Coordination must be topology.

### Decisions are topology, not code

There are no guards. There is no per-token value predicate anywhere in the model, deliberately: it was specified, then removed.

Model a decision as either

- **competing transitions** consuming the same token, distinguished by their other preconditions (an inhibitor arc, a permit, a read arc on a mode place), or
- **an `Xor` output spec** on the producing transition, where the action picks a branch and the verifier sees every branch as a possibility.

The verifier reads production from the output spec, never from the action. If the action can write somewhere the spec does not declare, your model is a lie about your program, and a `Proven` on it is worth nothing. Declare every alternative.

### Bounded resources are places, not counters

The pattern, in full, because it is the most reusable thing in this document:

- A budget place seeded with N unit tokens by the transition that starts a new unit of work. That starting transition also carries a reset arc on the budget place, so a new request clears any stale allowance before seeding.
- The retrying transition consumes one budget token per attempt, at high priority.
- A low-priority fallback transition with an **inhibitor arc** on the budget place fires only when the budget is empty, and emits the terminal outcome (escalate, canned answer, give up).

No action ever asks "do I have budget left". The decision lives in the marking, which means it is race-free and it is checkable: `PlaceBound(budget, N)` is provable, and so is "the fallback is reachable".

The same shape covers concurrency limits (a permit place with N tokens, consumed on start and returned on completion, which gives you the invariant `inFlight + permits = N` for free), mutexes (the N=1 case), rate limits, and pool capacity. Prefer it over any runtime concurrency-limit option, because a limit the verifier can see is worth more than one it cannot.

The same shape covers rate limiting, and a rate limiter is the component most worth building once.
A leaky bucket is a permit place plus a timed refill transition:

```
PERMITS        seeded with `burst` unit tokens
CALL:    In.one(REQUEST), In.one(PERMITS)          -> IN_FLIGHT
DONE:    In.one(IN_FLIGHT)                         -> RESULT
REFILL:  read(BUCKET_TICK), delayed(interval)      -> PERMITS      (up to `burst`)
REJECT:  In.one(REQUEST), inhibitor(PERMITS)       -> THROTTLED
```

Everything is in the marking: the tokens available now, the ones in flight, the refill clock, and
the "no permit left" decision. Nothing asks a limiter object how many calls it has seen. Make it a
subnet with `REQUEST`, `ADMITTED` and `THROTTLED` as ports, and you instantiate it per dependency
with its own rate, or fuse the permit places of several instances when the quota is actually shared.
`references/composition.md` works that example through both cases.

### Failure is a token, not an exception

There is no rollback. When an action fails, its consumed tokens are gone permanently. That is deliberate: rollback needs compensation logic and conflicts with async actions.

So any failure the system must react to has to be an explicit `Xor` branch into a failure place. "The exception propagates" is not a design. Decide, per transition: does a failure here need a retry path, a dead-letter place, a compensating transition? If yes, it is a branch in the output spec.

Timeouts follow the same logic and one extra rule: a timeout branch **excludes the late output, it does not cancel the work**. Side effects of an abandoned action still happen. If cancellation matters, model it (an inhibitor arc on a cancel place that the slow work checks structurally), do not hope for it.

### Every token needs a consumer, in every reachable state

**Every token must have an enabled consumer in every reachable guard state.** A token nobody can consume is a hang in production and an unbounded place in the model, and unbounded places are what stop a proof from ever closing. Whenever you add a place, answer immediately: who consumes this, and are they enabled in every state where this token can exist?

Two consequences that catch most real bugs:

- **Every "nothing happened" branch needs a consumer.** An `Xor` leg emitting a marker that means "no result this time" is still a token. Give it a drain transition, even a no-op one. Left alone it accumulates one token per miss for the life of the net.
- **Every exit path emits its completion marker**, including the error path, the discard path and the drain path. A branch that forgets its marker hangs whatever joins on it. A branch that emits two lets two units of work run at once.

### Make the structural branches equal the runtime outcomes

Three shapes, all learned from real hangs:

- **Model `Xor` of `And`, not `And` of `Xor`.** Two independent `Xor` outputs can produce a combination your code never produces, and the analysis will find it and treat it as reachable. One `Xor` whose legs are complete output sets makes the structural branches exactly the runtime outcomes.
- **There is no optional output.** An unconditional `And` for something the action sometimes cannot produce is a runtime violation and a deadlock in the model. Write `xor(realOutput, voidSink)`, and give the sink a drain. The reverse is now equally strict: validation succeeds only when **exactly one** branch of the spec claims exactly the set of places the action wrote, so an extra write into a declared place that the selected branch did not ask for is a violation rather than a silent deposit. `And` is genuinely unordered, so declaration order no longer changes the verdict.
- **An `Xor` leg chosen by hidden action state is unprovable.** If the action decides "is this the last result", the analysis will take the other leg on the last result and strand the batch. The provable encoding of the same idea is a pending-marker place per outstanding job plus an inhibitor arc on it.

And one that looks harmless and is not: **"optionally use X" is not `read(X)`.** A read arc is a precondition. When the place is empty, which is usually the normal case, the transition never becomes enabled, and the channel deadlocks for every user. The correct shape is a pair of transitions: consume X at high priority, inhibited by X at low priority.

### Decide, then emit

The executor consumes inputs before the action runs, does not restore them on failure, and commits outputs only on normal completion. So:

- Split the action into a part that computes and may throw but writes nothing, and a part that writes the complete output set and cannot throw. An action that writes inside a `try` and writes again in the `catch` produces duplicate tokens and both legs of an `Xor`, and no bound proof can see it, because the proof reads the declared arcs and not the method body.
- Wrap the whole body, including the metrics and logging calls. An unguarded observability call sitting between consuming the input and writing the output destroys the token when it throws, and no drain can dead-letter what the transition already consumed.

### Cancellation, barge-in and staleness are arcs

The pattern that replaces a cancelled flag:

- A **read arc plus an inhibitor arc** as a pair: the streaming transition reads the generation or session token and is inhibited by a barge-in place. Injecting into the barge-in place stops further firing immediately, with no flag for anyone to observe at the wrong moment.
- **Reset arcs clear stale state** at the boundary: the transition that accepts new input resets the in-flight places, so leftovers from the interrupted unit of work cannot combine with the new one.

A cancellation flag read inside an action is the classic stall: the action returns early, tokens sit in the in-flight place forever, and nothing fires. The marking never learned about the cancellation.

### Observability rides the event store

Tracing spans, structured logs, metrics, audit trails and live debugging all hang off an event-store decorator wrapping the net's event stream. Do not wrap actions, do not instrument bytecode, and do not invent an execution-context hook for observation. Ambient-context propagation into action threads is a different concern with a different mechanism.

This matters for design, not just tidiness: events are an observation channel, never a data-flow channel. If a downstream step needs a value, that value travels as a token.

### When something "cannot be done", find the structure first

This model with inhibitor arcs is Turing-complete. Almost every "libpetri cannot express X" is really "I have not found the places yet". Before proposing a new API, a new binding, or an escape hatch, work the topology:

| "I need..." | Structure |
|---|---|
| streaming output | per-chunk injection into an environment place, with a read arc on the generation token for staleness |
| cancel mid-flight | inhibitor arc on a cancel place, reset arcs for cleanup |
| pause and resume | an urgent transition blocked on a resume place |
| bounded retry | budget place plus inhibitor fallback |
| rate limit or mutex | permit place with N tokens |
| a time window | window timing plus a read arc on the state that must hold |
| fan out and rejoin | N transitions plus a cardinality join, or nu correlation when groups overlap |
| per-step observation | event-store decorator |

Genuine gaps are limited to observation and persistence seams that do not change firing semantics. A helper that lets an action emit tokens mid-flight outside the output spec is not a gap, it is the hole this model exists to close.

### Tools and external services are subnets, not leaf actions

Give each external capability its own subnet with typed input and output ports. Then dependencies between them are shared places wired at composition, rate limits are permit places, mutual exclusion is a permit place with one token, time windows are timing plus a read arc, and preconditions are read arcs. A flat list of calls dispatched inside one action discards every reason to be using this model.

## The modelling vocabulary, and how each piece is misused

### Arcs

| Arc | Requires | Consumes | Use it for | Classic misuse |
|---|---|---|---|---|
| input | yes | yes | ownership transfer: this work is mine now | draining with `all()` when `one()` would do |
| output | no | produces | the declared effect surface the verifier reads | declaring outputs the action only sometimes writes |
| inhibitor | absence | no | negative precondition: pause, kill switch, not yet | using it as a mutex where a permit token is the honest model |
| read | yes | no | shared state many transitions consult | expecting it to serialise (readers never conflict) or to see every token (it peeks the front) |
| reset | no | yes, all | cleanup, cancel, purge stale state | putting it on a place that carries a conservation law |

Consumption is the only ownership primitive, and it is what makes coordination race-free: there is no check-then-act gap because the match is part of the firing rule. **If two things must not happen at once, make them consume the same token, not read the same flag.**

Prefer `one()` and `exactly(n)` over `all()` and `at_least(n)`. Draining arcs are the most expensive modelling choice available to you: they destroy the linear conservation laws that make proofs converge (see `references/verification.md`). Drain when the domain really means "take everything", and drain into a place no invariant needs to weigh.

### Timing

| Timing | Interval | Enforcement |
|---|---|---|
| `immediate` | `[0, inf)` | fires as soon as enabled |
| `delayed(d)` | `[d, inf)` | lower bound only |
| `deadline(by)` | `[0, by]` | **hard**: force-disabled past the bound, emits a timed-out event |
| `window(e, l)` | `[e, l]` | **hard**, same reaping |
| `exact(at)` | `[at, at]` | **soft**: never force-disabled, fires at the first opportunity at or after the target |

The clock starts at enablement and restarts on re-enablement; partial elapsed time is discarded. A reset arc on a place another transition depends on restarts that transition's clock, which is a feature for cancel semantics and a trap for deadline modelling.

`exact()` is a logical instant for simulation and proof, not a real-time guarantee. For a wall-clock lower bound use `delayed`; for a hard bounded window use `window`.

The primary-and-fallback idiom is timing plus priority: primary at high priority and immediate, fallback at low priority and delayed. The fallback becomes ready only if the primary did not take the token first. Use it for silence recovery, escalation and slow-path handling.

### Priority

Ready order is priority descending, then enablement time, then declaration order. Priority is a scheduling policy, and by default **no analysis sees it**. If a safety argument depends on "the high-priority transition always wins", either make the exclusion structural (inhibitor arc or permit) or opt into conflict-aware priority semantics explicitly.

### Environment places

An environment place marks the world boundary. Injection is thread-safe from anywhere and wakes an idle orchestrator immediately.

Two consequences worth planning for:

- **Registering any environment place makes the executor long-running.** There is no separate flag. A net with no environment places terminates at quiescence.
- **An unbounded external source really is unbounded.** A bare `env -> transition -> place` chain makes any bound on that place genuinely violated. Put the permit place in front of the consuming transition, which is what a real system does anyway.

### The execution loop, and the trap inside it

Each cycle: process completions, then process external events, then update enablement, then enforce deadlines, then fire ready transitions, then await work.

**Deposits made during a pass are not visible to firing in that same pass.** Outputs land in the completion phase and firing happens later, so if a high-priority transition consumes a token and its synchronous action refills the place immediately, a lower-priority transition waiting on that place stays disabled until the next cycle. This binds counts as well as presence, and it binds draining arcs too: a drain firing later in the same pass takes only what was there when the pass began.

Never design as if a synchronous action's output is available to another transition in the same pass. When a net behaves one cycle later than you expected, this is usually why.

## Verification: start on day one, not at the end

Treat properties as tests. Write the first one with the first subnet.

What you can check: deadlock freedom, termination at a sink, mutual exclusion, place bounds, unreachability, and for correlated nets the branch-place bound and the "every fork is eventually joined or dead-lettered" property.

Two of those are about stopping, and they are not the same claim. `DeadlockFree` is strict: it fails on a quiescent marking that still holds a token **outside** the places you declared as sinks, so it answers "is anything stranded". `TerminatesAtSink` is the permissive one: it fails when a quiescent marking has **no** declared sink marked. They invert on the empty marking, so a fully drained net is deadlock-free and does not terminate at a sink. Declare your sink places either way, and declare all of them: under the strict reading a terminal place you forgot to list reads as a stranded token.

Five facts that shape designs:

1. **The SMT route is untimed and value-blind.** `Proven` holds for the timed net too. `Violated` there can be spurious, because the abstraction lets an action route anywhere its spec allows. Read the counterexample before believing it.
2. **An ordinary untimed net is usually decided by enumeration, not by the solver.** The state-class graph is built up to a class budget and, if it closes, the verdict is read straight off it — exact, and with a counterexample that is a real firing sequence. It is on by default and skipped for timed nets, ν-nets and nets with environment places. This is the difference between 0.11 s and 410 s on a forty-node workflow: IC3 needs a frame per pipeline stage, enumeration is linear in the state space. Past its budget it declines and the solver answers, so it can never cost you a verdict. Read `result.route` to see which one answered.
3. **The state-class route is the only one that reasons about time**, and the only one that decides quiescence for correlated nets.
4. **P-invariants are what make proofs converge**, and one draining or reset arc on a busy place destroys every invariant whose support touches it. This is the difference between a proof that takes seconds and one that never lands.
5. **`Unknown` is information.** First raise the timeout: a proof that needs four minutes reports the same `Unknown` as one that needs forever, so vary the budget before concluding anything about a net. Then: bound something, declare the budget place, declare sink places (and conditional sinks for designed terminals such as a halt or pause marker: `sinkPlacesWhen`), move a draining arc, or — for a quiescence proof on a pipeline-shaped net — turn on the state equation (`stateEquation(true)`).

Two habits pay for themselves immediately. **When a query does not close, read the report before reaching for a flag.** `Dropped invariant:` / `Dropped semiflow:` lines naming a draining or reset place mean the encoder is missing most of the net's conservation laws, and `semiflowInvariants` is then the biggest lever there is: one production net went from 50 minutes to `Unknown` to 15 seconds to `Proven` on that flag alone. With no such lines and a branchy net it is the whole bill and buys nothing — measured at 130 seconds of a 132-second run on an 81-node workflow, for one extra invariant that moved no verdict. And **never assert `assertFalse(isViolated())`**: it is false for `Unknown` too, so a proof lost to a timeout passes silently and the test is vacuous from then on. Assert `Proven` explicitly.

### Say proven, or say untested

Be strict about what you claim, in code comments, in commit messages, in a design document and in
what you tell a colleague. There are only three honest statements about a property:

- **"Proven"**, and then you name the property, the initial marking, the environment mode and the
  route, because a verdict without those is not reproducible.
- **"Violated"**, and then you have a counterexample trace, which is the most useful artefact in
  this whole system.
- **"Not checked"**, or **"came back Unknown"**. Both are fine to say. Neither is "it is correct".

Never call a net correct, safe, race-free or deadlock-free because you read it and it looked right.
Reading a concurrent system and believing it is the failure mode this entire model exists to
replace. If you have not run the property, say you have not run it.

Two limits belong in the same breath, every time:

**A proof is about the model, not about your action code.** `Proven` means the topology has the
property under the stated hypotheses. It says nothing about whether an action writes the tokens its
spec declares, whether it throws halfway, or whether the service it calls is down. Executor-level
tests cover that half, and they are not optional.

**Anything outside the net is outside the proof, permanently.** This is not a gap that a better
solver closes. The verifier reads places, arcs, cardinalities, timing and name equality. A flag in a
service, a row in a database, a counter in a closure and a branch an action picks on a value are all
invisible to it, so no property that depends on them can ever be proven, and any confidence you have
about them is unfounded. When you catch yourself wanting to prove something the model cannot see,
that is not a verification problem. It is the design telling you the fact belongs in the net: make
it a place, a token, an inhibitor arc, then prove it.

Read `references/verification.md` before you tune anything: for the route split, the exact-gate rule that decides proof cost, the semiflow option, siphons and traps as a fast structural pre-check, environment modes and the vacuity guard, and how to wire proofs into a build so they stay honest.

## Where to read more

The files below sit next to this `SKILL.md`; read them from this skill's own directory.

| Read this | When |
|---|---|
| `references/verification.md` | any proof question: what is checkable, why a query is `Unknown`, how to keep proofs cheap, wiring proofs into CI |
| `references/composition.md` | building or reusing subnets, ports versus channels, instantiate versus direct compose, fusion, the cross-language place-equality divergence |
| `references/nu-nets.md` | correlating parallel work by identity: minting, matching, the tie-break, the budget place, the fragment rules the exact proof routes require |
| `references/patterns.md` | worked topologies from a production system: per-session nets, turn handling, barge-in, budgets, queue draining, and the changes that made real nets provably deadlock-free |
| `references/lang-java.md` and the other `lang-*.md` | the handful of per-language facts that change a design decision |

libpetri's requirement specification is the normative source for semantics, and its registry is
`spec/00-index.md`: at `<repo-root>/spec/00-index.md` when you are working inside a libpetri
checkout, otherwise at https://github.com/debe/libpetri/blob/main/spec/00-index.md. Cite
requirement IDs (`VER-013`, `NU-024`, `MOD-041`) when you make a claim about semantics, and read
the index for the current set rather than trusting a remembered count. If you can open neither,
say the claim is unverified rather than inventing an ID.

## Anti-patterns worth naming out loud

- A flag, counter or map outside the net deciding whether a transition should proceed.
- Reading a database, cache or session object inside an action.
- An action that writes to a place its output spec does not declare, or a transition that both declares outputs and keeps the built-in passthrough.
- A single untyped payload place threaded through the whole net.
- A retry counter inside a token.
- Two input arcs on the same place (use one arc with a cardinality).
- Relying on a timeout branch to cancel work.
- Expecting rollback when an action fails.
- Draining or reset arcs on the places that carry your invariants.
- A terminating net verified with an incomplete sink list, so every terminal place left off it reads as a stranded token.
- Assuming `DeadlockFree` still means "some sink got marked". That is `TerminatesAtSink` now, and the two invert on a drained net.
- An action that writes to a declared place outside the branch its output spec selected. It used to be deposited silently; it is a violation now.
- Verifying with environment injection ignored while environment places are registered: it can never return `Proven`.
- A correlation map in a join action instead of correlation in the firing rule.
- A read arc used to mean "use this if it happens to be there".
- An `Xor` leg whose choice lives in action state the model cannot see.
- A "nothing happened" marker with no consumer, quietly accumulating for the life of the session.
- A test that passes on `Unknown`.
- Calling a net deadlock-free, safe or race-free on the strength of having read it.
- Storing anything a transition later needs in a session object, a cache or a static field.
- Declaring a match spec on a net where only one group is ever live.
- `/` inside a place, transition or subnet name.
- Auto-translating another orchestrator's graph into a net: you inherit its shape without inhibitor, read, reset, timing or priority arcs, so it is no more verifiable than what you started with. Migration means redesign.

## Decision checklist

Run this before calling a net design done.

- [ ] Every domain concept has its own typed place, and no place carries an untyped catch-all payload.
- [ ] Every value a transition depends on arrives as a token or a read arc, and no action reads external mutable state.
- [ ] Every branch an action can take is declared in an output spec.
- [ ] Every failure path that matters is a place, not an exception.
- [ ] Every unbounded thing (retries, in-flight work, concurrency, correlation groups) is bounded by a place with a fixed token count.
- [ ] Cancellation and staleness are modelled with inhibitor and reset arcs, not with flags.
- [ ] Repeated structure is a subnet with named ports, instantiated per use, with port names exported rather than duplicated as strings.
- [ ] Correlation by identity is used only where several groups are live over shared places, and every minting net has a declared budget place.
- [ ] Draining and reset arcs are kept off the places whose counts a proof depends on.
- [ ] Sink places are declared for every intended terminal state, and the stop-condition property asserted is the one that states the intent (`DeadlockFree` for "nothing stranded", `TerminatesAtSink` for "we reached a terminal").
- [ ] Environment places are registered with the verifier under a mode that models injection.
- [ ] At least one property is asserted per subnet and one on the whole composed net, and each test asserts `Proven` rather than merely not throwing.
- [ ] Every token has an enabled consumer in every reachable state, including every "nothing happened" marker.
- [ ] Every branch of every `Xor` is a complete output set, so the structural branches equal the runtime outcomes.
- [ ] Every action decides before it emits, and emits its complete output set exactly once.
- [ ] No fact the net branches on lives in a session object, a cache, a static field or any other store.
- [ ] Every correctness claim made about this net names a property, a verdict and the marking it was proved from; nothing is called correct because it was read and looked right.
- [ ] Anything that must be provable is inside the net, since nothing outside it can ever be proven.
- [ ] No design decision rests on priority alone, on same-pass deposits, or on a timeout cancelling work.
