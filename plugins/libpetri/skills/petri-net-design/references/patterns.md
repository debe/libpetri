# Pattern reference: topologies that survived production

Every pattern here comes from a long-lived, formally verified production system: two per-session nets (roughly 100 places and 100 transitions each, assembled from 16 to 18 subnets), both carrying a whole-net deadlock-freedom proof. The system is described generically on purpose. What matters is the shape.

## Contents

1. [Liveness: the rule underneath all of them](#1-liveness-the-rule-underneath-all-of-them)
2. [The long-lived session net](#2-the-long-lived-session-net)
3. [Admission tokens and turn lifetime](#3-admission-tokens-and-turn-lifetime)
4. [Draining a queue into one unit of work](#4-draining-a-queue-into-one-unit-of-work)
5. [Fan-out and join with pending markers](#5-fan-out-and-join-with-pending-markers)
6. [The monitor token](#6-the-monitor-token)
7. [Routing a correlation name around a lossy region](#7-routing-a-correlation-name-around-a-lossy-region)
8. [Barge-in, cancellation and the read/inhibitor pair](#8-barge-in-cancellation-and-the-readinhibitor-pair)
9. [Timers as places](#9-timers-as-places)
10. [Debounce, and the escalation ladder](#10-debounce-and-the-escalation-ladder)
11. [Staleness: stamp, carry, compare at commit](#11-staleness-stamp-carry-compare-at-commit)
12. [Two kinds of discard](#12-two-kinds-of-discard)
13. [Subnet layering and naming](#13-subnet-layering-and-naming)
14. [Action discipline inside a transition](#14-action-discipline-inside-a-transition)
15. [The changes that made these nets provable](#15-the-changes-that-made-these-nets-provable)

---

## 1. Liveness: the rule underneath all of them

**Every token must have an enabled consumer in every reachable guard state.**

That single sentence generated most of the fixes in section 15. A token with no consumer in some reachable state is a hang in production and an unbounded place in the model, and unbounded places are what stop a proof from ever closing. When you add a place, ask immediately: who consumes this, and is that consumer enabled in every state where this token can exist?

Two corollaries you will use constantly:

- **Every "nothing happened" branch needs a consumer.** An `Xor` leg that emits a marker meaning "no result this time" is still a token. Give it a drain transition, even a no-op one. Left alone it accumulates one token per miss per session, which is behaviourally harmless and fatal to verification.
- **Every exit path emits its completion marker.** Including the error path, the discard path and the drain path. A branch that forgets its marker hangs whatever joins on it. A branch that emits two lets two units of work run at once.

## 2. The long-lived session net

- **One executor per session.** The net runs until a terminal token stops it, then drains.
- **The topology is a compile-time constant.** Build the structure once as a static value by composing subnets. Per-session work is only binding actions to it, which is linear in the number of transitions and cheap enough for a connection handshake.
- **There is no IDLE place.** Idle is simply the marking where only session-scoped tokens remain. Nothing can be stuck waiting for idle, and quiescence becomes a real state rather than a state you have to reach.
- **The initial marking is a named function shared by production, replay harnesses and every proof.** Each verification test mirrors it place for place, so drift between what runs and what is proved is visible in a diff. Document what happens if a token is missing from it: a net that silently accepts input and never starts work is a very expensive five minutes.

Initial markings are tiny, and their tokens have three roles:

| Role | Behaviour |
|---|---|
| shared read-only context | never consumed, only read |
| monitor or mutex token | circulates: consumed and re-emitted by each holder |
| admission, timer or watchdog token | consumed by one transition, refunded by another |

## 3. Admission tokens and turn lifetime

The single most valuable structure in the system:

```
INPUT (In.all) + TURN_BUDGET (In.one)  --ForkWork [mint name]-->  three branch inputs
BRANCH_A_DONE + BRANCH_B_DONE + BRANCH_C_DONE  --CloseWork-->  TURN_BUDGET
```

One admission token, seeded with a single token, consumed when a unit of work starts and refunded exactly once when every branch has reported done.

What it buys:

- **Backpressure for free.** The next unit of work waits, structurally. No queue object, no semaphore, no debounce timer.
- **A lifetime for correlation names.** A correlation colour must never outlive the budget token that admitted it. When that holds, per-unit places are provably empty at the commit point, and the reset arcs that used to clean them up become provable no-ops that you can delete. That deletion is what moves a coloured net into the decidable fragment.
- **A written exemption at every join.** Joins that do not correlate by identity are safe *because* the admission token bounds the net to one live unit of work. Say so in a comment at each such join, because a reader cannot tell by looking.

**Prefer one admission token over per-hop correlation.** An earlier attempt in the same system correlated each forwarding hop by identity. It reduced nightly failures from 46 to 40 to 24 and never closed, because the forwarding chain had too many hops. Whole-unit admission fixed it in one change and removed the need for correlation at most hops entirely.

**Exactly-once accounting is what makes the refund correct.** In that system one done marker had six emitters, another six, another three. Every one of them was audited. Do the same audit whenever you add an exit path.

## 4. Draining a queue into one unit of work

```
inputs: In.all(INPUT_QUEUE), In.one(WORK_BUDGET)
action: coalesce every queued item into one request
```

A client that sends faster than it receives fills the queue while work is in flight. Consume-all plus a coalescing function plus the admission token is the entire backpressure story: nothing is dropped, nothing is queued outside the net, and everything the client said gets one answer.

This is also one of the rare safe uses of a draining arc: consume-all on an environment place touches no conservation law, because the place was never bounded to begin with.

## 5. Fan-out and join with pending markers

The provable encoding of "have all N results arrived", where N is data-dependent and unknown at build time:

```
REQUEST --Route [mint round name]--> ROUTING_DONE
                                   + xor( and(JOB_REQUEST, JOB_PENDING), nothing )   per job family
                                   + one empty result store per family

JOB_RESULT + JOB_PENDING + RESULTS_STORE  --StoreResult (high priority)-->  RESULTS_STORE
ROUTING_DONE, inhibitor(JOB_PENDING)      --ResolveAxis (low priority)-->   AXIS_RESOLVED
```

One pending token per dispatched job, consumed as its result lands. The resolver is inhibited by that place, so it fires exactly when the last result has been folded in. Priority orders store before resolve.

**Never decide "is this the last one" inside an action and expose it as an `Xor`.** The analysis will take the "not last" branch on the last result, strand the batch, and no proof can pass through. The pending marker plus inhibitor is the provable encoding of the same idea.

**The join is the unit of commit, and it consumes rather than reads.** Correlate *every* input on the round name, not just the interesting ones: keying only some inputs leaves a hole where an abandoned round's stragglers can join name-consistently against the next round's fresh empty stores. Consuming rather than reading means there is no marking in which some of a round's results are committed and others are not.

## 6. The monitor token

```
READY + COLLECTOR --Spawn--> N x JOB + N x JOB_PENDING + BATCH_OPEN + COLLECTOR
JOB               --Execute (fires N times in parallel)--> RESULT
RESULT + JOB_PENDING + COLLECTOR --Collect--> COLLECTOR
BATCH_OPEN + COLLECTOR, inhibitor(JOB_PENDING) --Finish--> SELECTION_READY + COLLECTOR
```

A single circulating token acts as a mutex over shared batch state, so collection is serialised while the jobs themselves run in parallel. N strategies are N instances of one action parameterised by an enum, not N action classes.

## 7. Routing a correlation name around a lossy region

A region that folds N tokens into one is not token-conservative, so no semiflow covers it and a correlation colour cannot travel through it.

The fix: emit a routing token carrying the name **in parallel with** the region, keep the region itself colourless, and rejoin using a pending marker plus an inhibitor arc.

```
Route --> and( ROUTING_DONE(name), pipeline entry )      // pipeline stays colourless
ROUTING_DONE, inhibitor(PIPELINE_PENDING) --Resolve--> AXIS_RESOLVED(name)
```

Generalised: when a region is not token-conservative, do not thread the correlation name through it. Route the name around it and rejoin.

## 8. Barge-in, cancellation and the read/inhibitor pair

```
                  ACTIVITY_WINDOW_OPEN          (a Void place used as a boolean)
                    read |        | inhibitor
INTERRUPT --Accept ------+        +------ Ignore--> INTERRUPT_DISCARDED
      `--> INTERRUPT_SENT
```

Both transitions consume the same interrupt token, so exactly one fires. The loser stops being enabled the instant the winner consumes. Read and inhibitor on the same place are complementary guards, so **no priority is needed** and no ordering assumption is made.

**The ignore branch is not optional.** Without it the interrupt token sits there forever: unbounded place, no finite state-class graph, no proof.

This is also the answer to the classic stall: a cancellation flag checked inside an action leaves tokens in the in-flight place and nothing to consume them. Cancellation belongs in the marking.

## 9. Timers as places

**A timer is a token in a place plus a timed transition that consumes it. The clock starts when the token arrives.**

| Operation | Structure |
|---|---|
| start or restart | `reset(TIMER)` plus an output to `TIMER` on one transition |
| restart a running timer | `In.one(TIMER)` plus an output to `TIMER`: the token is conserved, so the P-invariant survives |
| cancel | `reset(TIMER)` alone |
| expire | the timed transition consuming `TIMER` fires |

```
ResetInactivityTimer:  In.one(USER_ACTIVITY), reset(TIMER_PENDING) --> TIMER_PENDING
CloseOnInactivity:     In.one(TIMER_PENDING), exact(45s)           --> CLOSED_INACTIVITY
```

Both restart forms work because a firing that takes the timer token restarts the clock even when it puts one back in the same step. A transition that only reads `TIMER` leaves the clock running.

**Funnel all activity sources into one activity place.** Several producers write it, only the timer reads it. Adding a new activity source is then a one-arc change and the timer subnet never grows.

## 10. Debounce, and the escalation ladder

**Debouncing a high-frequency stream into a boolean:**

```
Open:    In.all(STREAM), inhibitor(WINDOW_OPEN), reset(stale markers)
         --> and(WINDOW_OPEN, SILENCE_PENDING)
Refresh: In.all(STREAM), read(WINDOW_OPEN), reset(SILENCE_PENDING)
         --> SILENCE_PENDING
Close:   In.one(SILENCE_PENDING), delayed(1000ms), reset(WINDOW_OPEN)
```

Consume-all drains a whole burst per firing, which is what keeps the environment place bounded. Open versus refresh is again inhibitor versus read on the same window place. Put the reason for the delay constant in a comment next to it: it is calibrated to something real (a client buffer size, an upstream idle timeout) and the next person will not guess.

**An escalation ladder** is a chain of (place holding retry context) to (timed transition inhibited by the thing you are waiting for) to (next place):

```
AWAITING --Nudge (delayed 3s, inhibitor ACTIVITY_OPEN)--> RECOVERY_PENDING
RECOVERY_PENDING --Recover (delayed 3s, inhibitor ACTIVITY_OPEN)--> reconnect
```

Each rung carries the payload needed to retry. Each rung also resets and re-emits the session-level inactivity timer, so a recovery attempt cannot have the session close underneath it. Cancellation is a reset arc at every place where the awaited event actually lands.

## 11. Staleness: stamp, carry, compare at commit

1. The fork mints the stamp: `reset(LATEST_STAMP)` plus emit, so the cell holds exactly one.
2. The stamp rides **inside the token types** down the whole pipeline, never in session storage.
3. The commit compares with a **read** arc (many results, one latest) and branches:

```
Commit: In.one(RESULT), read(LATEST_STAMP) --> xor(VALIDATED, DISCARDED_STALE)
```

The discard branch is a real place, for observability and for boundedness.

Two rules learned the hard way:

- **A stale-skip must still emit its completion marker**, or its sink becomes unreachable and the net loses liveness.
- **The freshness stamp must travel with the datum that won.** A real bug: the action took the timestamp from one candidate slot and the payload from another, so a mixed result passed the freshness check.

## 12. Two kinds of discard

They look similar and are not interchangeable.

**Immediate, guarded, matched-pair discard.** The token is **contended**: a happy-path transition also wants it. The discard must beat it deterministically and immediately, gated by a verdict place. A timer here opens a window in which the wrong outcome leaks to the user.

**Delayed, ungated dead-letter drain.** The token is **uncontended**: once its required read place is gone, nothing competes for it, so the drain only needs to fire eventually. Delayed timing plus the lowest priority guarantees that a slow but live consumer is never pre-empted.

**A dead-letter drain depends on nothing but the token and a timer.** No read arc, no inhibitor: those are exactly what stranded the token in the first place.

**Derive the drain delay by expression from the consumer's timeout ceiling**, and pin it with a test:

```
MAX_CONSUMER_LATENCY = <the upstream read timeout>
STALE_DRAIN_DELAY    = MAX_CONSUMER_LATENCY + 3s
// invariant test: STALE_DRAIN_DELAY > max(read timeout, guard timeout)
```

A literal constant drifted once and produced a real production deadlock.

## 13. Subnet layering and naming

**Three layers, strictly one-directional:**

```
Places layer      places, timings, environment places, initialMarking. Depends on nothing.
   ^
Subnet layer      the subnet definition, transition-name constants, stateless actions, bindings.
   ^
Config layer      the composed structure, the per-session factory.
```

Keeping the vocabulary in a leaf module with no dependencies is what lets subnets reference place constants from their own definitions without a circular initialization. In Java this is not a style preference: a cycle here yields nulls at class-initialization time and then a cascade of confusing errors. A nested holder class is a workaround; extracting the vocabulary is the fix.

**Subnet anatomy: static only, no instance state.** A transition-name constants block, private stateless actions, the definition, a stateless binding map, and one function that merges session-dependent bindings on top. Pure token plumbing binds inside the subnet, next to the arcs it plumbs. Service-dependent actions bind from outside.

**Wrap lenient binding in a strict check.** Action binding substitutes a passthrough for any transition you forgot and ignores any key that matches no transition. Both are silent. Forty lines that diff declared transition names against the binding keys, and throw naming the subnet plus the missing and extra sets, convert a silently wrong net into a startup exception. Write those forty lines.

**Naming conventions that carry meaning:**

| Kind | Convention |
|---|---|
| place constant | `SCREAMING_SNAKE` mapping to a `PascalCase` net name |
| environment place | the place name plus an `_ENV` suffix, wrapping an existing place |
| transition | `PascalCase` verb phrase |
| subnet | camelCase, channel-prefixed |

**The verb encodes the topological role**, and this is the most portable convention of all:

`Fork` fan out. `Route` classify into `Xor` branches. `Store` fold a result and consume a pending marker. `Resolve` emit the join token once the pending markers are gone. `Join` correlated multi-input commit. `Discard` immediate guarded discard of a contended token. `Drain` delayed ungated dead-letter of an uncontended token. `Close` refund the budget. `Pass` and `Suppress` forwarding gates. `Spawn`, `Collect`, `Finish` the monitor batch.

**Parameterise a subnet only for structural timings**, and say why in a comment: changing them alters firing intervals and requires re-verification, which is exactly why they are not runtime configuration.

**Gotcha:** a subnet definition silently ignores reset and read arcs on places it does not declare. No error, no warning. The symptom is a test that stays stubbornly at the pre-change numbers.

## 14. Action discipline inside a transition

The executor consumes inputs **before** the action runs, does not restore them on failure, and commits outputs only on normal completion. Three rules follow.

**Decide, then emit.** Split the action into a step that computes and may throw but writes nothing, and a step that writes the complete output set and cannot throw. An action that writes tokens inside a `try` and writes them again in the `catch` produces two tokens per store and both legs of an `Xor`, and no bound proof can see it, because the proof reads the declared arcs and not the method body.

**Wrap the whole body, including observability, and produce output from a `finally`.** An unguarded metrics call between consuming the input and writing the output destroyed the token when the metrics backend threw, and no drain could dead-letter what the transition had already consumed.

**Catching is not always right.** At a join with many already-consumed inputs, catching and still emitting is correct. At a resolver that must emit a correlated name, catching would only let it emit an invented name that the join's match can never accept, which guarantees the hang the catch was supposed to prevent. Decide per transition, and write down which case it is.

## 15. The changes that made these nets provable

Each of these is a real fix, with the shape it replaced. This is the fastest way to learn what "provable" costs.

1. **Move the budget refund to the end of the unit of work.** Refunding at an early join let a later unit reset a place mid-round and block both consumers of it. Symptom: a multi-minute client timeout.
2. **Delete every reset, read and inhibitor arc on a coloured place.** Made possible by (1), and each deletion pinned by an unreachability proof so it stays deleted.
3. **Take the correlation name from the token you consume, never from a read arc.** A read arc on a coloured place puts the net outside the decidable fragment.
4. **Replace a "fake `Xor`" with a pending marker plus inhibitor.** An `Xor` whose leg is chosen by hidden action state is unprovable.
5. **Drain consumer-less markers.** Harmless at run time, fatal to verification: they made the net unbounded across rounds, which stopped the exact state-class graph from ever closing.
6. **Model `Xor` of `And`, not `And` of `Xor`.** Two independent `Xor`s can produce a combination your code never produces, and the analysis will find it. One `Xor` whose legs are complete output sets makes the structural branches exactly the runtime outcomes.
7. **There is no optional output.** An unconditional `And` for something the action sometimes cannot produce is a runtime violation and a deadlock in the model. Write `xor(realOutput, voidSink)`. Since the 5.0 wave the check is an exact-explanation search (IO-015): exactly one branch of the spec must claim exactly the set of places written, so an over-write into a declared place outside the selected branch fails too, where it used to land silently. `And` is unordered, so `and(a, xor(d, e))` and `and(xor(d, e), a)` can no longer disagree on the same output.
8. **"Optionally use X" is not `read(X)`.** A read arc is a precondition: when the place is empty, which is the normal case, the transition never becomes enabled and the whole channel deadlocks for every user. The correct shape is a pair: consume X at high priority, inhibit X at low priority.
9. **Every consumable request place needs an exhaustive transition set over the guard space.** One missing case ("there is no product at all") hung every session that hit it, because the upstream caller blocks until its call is answered.
10. **Clear a latch in its own transition, gated on a completion token.** Clearing it inside the producing transition is a race.
11. **Reset arcs are name-blind, so they are wrong under concurrency.** A campaign replaced 18 of 34 reset arcs with four idioms: reset becomes consumption when an invariant guarantees the token is present; a capacity-one conflict pair (an empty-cell variant with an inhibitor and an occupied-cell variant consuming the token, both triggered by the same token so exactly one fires); a read-gated canceller as a separate consume-only transition; and a three-variant conflict fork with the fourth corner proven unreachable. The other 16 were correct bounded latches and stayed. **Reset count is not the goal. A correct, bounded, verified net is.**
12. **When you cannot make a race impossible, bound its blast radius and prove the bound.** One place deliberately has no reset arc, and a test asserts the stranded token stays one-bounded, so the race can cost at most one unit of work.
13. **Priority-blind, untimed analysis found two real bugs the executor never showed.** Both were fixed at the net level rather than by teaching the analysis about priorities. Over-approximation cuts the right way: it admits more behaviour than the executor, so a proof over it carries to the real thing.
