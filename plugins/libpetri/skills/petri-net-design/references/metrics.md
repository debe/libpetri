# Measuring net designs: gates, sensors, and what not to count

How to tell a better net from a worse one when several designs satisfy the same contract. Every rule here comes from a controlled experiment: single-mechanism mutations checked by the verifier, human-labelled production fixes, and scale-ups to 200 transitions. The evidence log is `research/net-metrics/lab/JOURNAL.md` inside a libpetri checkout.

The harness in `harness/` next to this file computes all of it. `harness.md` describes the workflow.

## Contents

1. [The order: gates, then sensors](#1-the-order-gates-then-sensors)
2. [Gate 0: lint](#2-gate-0-lint)
3. [Gate 1: small scope](#3-gate-1-small-scope)
4. [Gate 2: one subnet at a time](#4-gate-2-one-subnet-at-a-time)
5. [Sensors that rank correct designs](#5-sensors-that-rank-correct-designs)
6. [What not to count](#6-what-not-to-count)
7. [Resets, precisely](#7-resets-precisely)

---

## 1. The order: gates, then sensors

**No metric can rank a net that is wrong.** In every experiment where a buggy and a correct design were compared, the structural metrics preferred the buggy one: fewer transitions, fewer inhibitors, better invariant coverage. Correctness usually costs structure, such as a consumer for every place under cancellation, a pending marker per job, or the second transition of a conflict pair. So the order is fixed:

1. **Lint.** Microseconds. Named arcs to fix.
2. **Small-scope gate.** Milliseconds. Exact, with counterexample traces.
3. **Compositional gate.** Tens of milliseconds per subnet.
4. **Sensors.** These rank the designs that passed. The output is a profile across axes, never a single score.

Whole-net verification of a large composed net is **not** a gate. At 100–150 transitions a correct design still proved in under a second, but a buggy one came back `Unknown` after five minutes instead of `Violated`. A design loop cannot wait for that. Run whole-net proofs as an overnight regression.

## 2. Gate 0: lint

Each finding names a transition and a place.

| Rule | Severity | Why |
|---|---|---|
| Reset, read or inhibitor arc on a place nothing produces into or consumes from | error | Usually an instance-prefixed name that composition bound to a different place. The arc silently does nothing, and the bug it was meant to prevent happens. |
| Two input arcs on the same place | error | Rejected by the executor, and it can crash analysis. Use one arc with a cardinality. |
| ν join fed through relays without declared carrier places | error | Each relay then mints a fresh name, the join can never match, and the verifier returns a *correct* `Violated` for a model you did not mean. |
| Reset from outside a subnet into one of its internal places | warning | Hidden coupling. It blocks compositional proof, and every feature change has to edit it. |
| Any arc from outside a subnet into an internal place | warning | Same reason, without the reset. |
| Reset on a place downstream of a declared event source | warning | Can destroy an event in flight. The accounting property will fail; see §7. |

## 3. Gate 1: small scope

Enumerate the design exhaustively at **k = 1 and k = 2**: one and two units, events, sessions or copies, whatever the contract scales. Every bug found in the experiments appeared at k = 1 in at most 4 ms, including the ones that became five-minute `Unknown`s at k = 4. Name-blind resets need k = 2, because two concurrent units have to share a place.

Check two properties on every candidate, whatever else the contract says.

- **Strict `DeadlockFree` with every resting place declared as a sink.** This catches stranded tokens: a late draft after a cancelled turn, the other leg of a fake `Xor`, the case nobody handled.
- **Accounting: at quiescence, outcomes equal what the sources supplied.** Model event arrival through an arrival generator (a supply place with n tokens and an `arrive` transition) so the count is known, then assert `quiescentCount(outcomePlaces, n, n)`. This catches lost events, which `DeadlockFree` cannot see. A reset that swallows an event leaves the net resting cleanly with one outcome missing. With a raw environment place the count is unknown and the property cannot be stated, so verify open nets through a generator harness.

Mark properties that only hold under timing, for example "the answer beats the watchdog". The untimed routes return `Violated` for them, with `counterexampleConfirmed=true`, which only means the trace replays when time is ignored. Only the timed state-class graph decides them, and its cost grows roughly as (n+1)! in the number of clocks running concurrently. Keep every timing-dependent argument inside one small component.

## 4. Gate 2: one subnet at a time

Prove each subnet on its own with `SubnetDef.verify` and a verification harness (MOD-051). Then prove the glue against the subnets' contracts (VER-022). In the experiments each subnet proof took 25–80 ms, where the whole net timed out.

This gate only works when the glue talks to subnets **through their ports**. A host transition that resets or reads a subnet's internal place creates a dependency no subnet contract can express. The subnets prove individually and the bug stays in the glue. In the experiment, both versions of a subnet proved fine; only the hub reaching into it was wrong. **An encapsulation violation is therefore a verifiability defect.** A design with any must either be fixed or accept whole-net verification cost.

Budget the gate as a total wall-clock time: `SmtVerifier.totalBudget(ms)` plus `signal(abortSignal)`. `timeout(t)` alone applies to each `z3` process, and one query starts several, so it can run about 7.5 × t plus the graph routes, which no timeout bounds.

**Identical units sharing resources** (one subnet instance per session, sharing permits) do not yet have a sound compositional check in the harness. An assume-guarantee rule was built and withdrawn after an adversarial review found it unsound. Whole-net checking at two or more units multiplies the state space, so keep the per-unit design small, check the smallest scale that exercises the sharing, and report the rest as unchecked.

## 5. Sensors that rank correct designs

Each sensor detects a specific mechanism and moves only when that mechanism changes. That was tested by adding one mechanism at a time to six unrelated base nets.

| Axis | Sensor | Reads | Fix when high |
|---|---|---|---|
| Encapsulation | cross-subnet resets; encapsulation violations | arcs from outside a subnet into its non-port places | give the subnet a cancel/reset input port and clean up locally (`patterns.md` §8, §13) |
| Concurrency safety | **multi-token resets** | resets on places that reachably hold more than one token (checked at k = 2) | replace them with the §15.11 idioms: consumption where an invariant guarantees presence, a read-gated consume-only canceller, a conflict pair |
| Decidability | essential power arcs; bounded fraction | reset or inhibitor arcs on places no sub-invariant bounds | bound the place with a permit or budget. The sensor also counts a latch whose every producer consumes the place as bounded; a producer guarded only by an inhibitor does not count (§7) |
| Maintainability | reset blast (places per resetting transition), reset reach (transitions coupled through resets), change impact (existing transitions edited per added feature) | how far one change travels | move cleanup next to the state it cleans; a reset hub grows linearly in every one of these |
| Proof cost | route eligibility (ordinary? enumerable? ν fragment?); per-unit state multiplier; timed width | which cheap route survives, how the state space composes, how many clocks run together | keep designs enumerable at small scale; one non-ordinary arc closes the structural route for sink-free queries |
| Folding hint | undeclared symmetry | exact hand-copied twins outside subnet instances | turn the copies into tokens in one place, a ν join with a budget, or subnet instances. Read it as a hint and keep it out of any score: correct designs sometimes need per-stage copies |

Report the profile. Do not sum it. Thresholds are deliberately absent until they have been calibrated on production nets.

## 6. What not to count

These were tested and failed. Size, CNC and cyclomatic number got **every** human-labelled production fix wrong (0 of 15), because every fix added structure.

- **Size**: places, transitions, arcs. Show it as context only.
- **Density measures**: coefficient of network complexity, cyclomatic number, Cardoso control-flow complexity.
- **Invariant coverage**: resets are invisible to it, and it preferred a buggy hub.
- **Raw state-space size**: it measures information content and says nothing about quality.
- **Naive coupling**: it counts declared ports, the *good* coupling.
- **Drain count**: a single drain transition can replace a fan-out of drains, and the fan-out is the worse design.
- **Raw reset count**: right 87 % of the time, and wrong exactly where one atomic local reset replaces a fan-out of drains.

## 7. Resets, precisely

"Fewer resets" is the wrong rule. A reset is fine when it is **local, atomic, and clears tokens that are present now, on a place that holds at most one**: the correct bounded latch. It is a defect when it:

- **crosses a subnet boundary.** It blocks compositional proof, and the hub gets edited on every feature.
- **sits on a place downstream of an event source.** It loses events, and only accounting sees it.
- **clears a place that can hold tokens of several concurrent units.** Reset arcs are name-blind, so one unit's cleanup destroys another's state.
- **re-seeds a bound fed from an unbounded source.** Linear analysis then loses the bound, and the proof falls off the structural route.
- **only clears what is present, when later arrivals must also be cancelled.** A turn arriving after the reset sails through. Cancellation needs a standing marker (read plus inhibitor) *and* a consumer for every late arrival at every entry point. Local cleanup inside each subnet provides both.

The verifier splits every transition that deposits into a place some reset or inhibitor arc tests into a start and a completion step (`verification.md` §2a), because the reset can fire while that transition's action runs. A producer that writes a ν-coloured place cannot be split, and the verdict is `Unknown` naming it.

**An inhibitor on a transition's own output is no mutex.** `start: req + inhibitor(busy) → busy` looks like one-at-a-time. The executor consumes `req` when the action starts and deposits `busy` when it completes, so the guard stays open while the action runs:

- **Rust** starts `start` again in that gap, so two requests put two tokens in `busy`.
- **Java and TypeScript** never start a transition again while it is in flight, so one guarded transition is safe there. Two different transitions guarded by the same `busy` both start, on every executor.

The verifier models the gap, so `placeBound(busy, 1)` is `Violated` with the trace `start, start, complete:start, complete:start`; for a single guarded transition the report adds the CONC-002 note that the trace may be a false alarm on Java and TypeScript. Model the latch as a token consumed at start instead:

```
FREE            seeded with one unit token
start:  req + FREE  -> busy
finish: busy        -> FREE
```

That is a permit with the P-invariant `FREE + busy = 1`. It proves `placeBound(busy, 1)` on every executor, and nothing is split.
