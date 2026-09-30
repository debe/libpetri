# The design harness: find the net before you write the code

Design the net in a sandbox first: write several candidates in TypeScript, check them, measure them, show them to the developer, and iterate. Only after a candidate is chosen do you implement it in the project's language. Then prove the implementation is the same net as the design.

The harness lives in `harness/` next to this skill. It depends on the libpetri TypeScript package of this repository (`"libpetri": "file:../../../../../typescript"` in `harness/package.json`), so build that package first (`cd typescript && npm install && npm run build`); `npm install` in `harness/` links it. The small-scope gate, lint and most sensors need nothing else. Per-subnet IC3 proofs and exact boundedness need the `z3` executable on `PATH` (or `LIBPETRI_Z3`); without it the harness reports what it skipped instead of failing.

```bash
cd <skill-dir>/harness && npm install        # once
npm run design -- evaluate --contract my/contract.ts --candidates my/a.ts my/b.ts --out out/
npm run design -- compare --design out/<candidate>.dot --impl impl.dot
```

Candidate and contract files are ES modules. Put a `package.json` containing `{ "type": "module" }` in the directory that holds them, and make sure `libpetri` resolves from there (a `node_modules` symlink to the harness's is enough). Otherwise the harness cannot load them.

`references/metrics.md` explains what the checks and sensors mean. This file is the workflow.

## Contents

1. [The loop](#1-the-loop)
2. [Write the contract first](#2-write-the-contract-first)
3. [Write candidates that differ on purpose](#3-write-candidates-that-differ-on-purpose)
4. [Evaluate, then feed the diagnostics back](#4-evaluate-then-feed-the-diagnostics-back)
5. [Show the developer: the artifact](#5-show-the-developer-the-artifact)
6. [Implement in the project language](#6-implement-in-the-project-language)
7. [Prove the implementation is the design](#7-prove-the-implementation-is-the-design)

---

## 1. The loop

```
contract ─► candidates ─► lint ─► small scope (k=1,2) ─► per-subnet proofs ─► sensors
   ▲                                                                              │
   └──────────── counterexamples + named arcs back into the next candidates ◄─────┘
                                           │
                        artifact: candidates side by side, live while iterating
                                           │  developer picks
                                           ▼
          implement in the project language ─► DOT equals the design ─► re-prove there
```

Stop iterating when at least one candidate passes every gate and the developer has chosen. Do not keep iterating to improve sensor numbers nobody asked about.

## 2. Write the contract first

The contract says what the net must do, independent of any design. It is the one input the agent must not weaken. A candidate that fails a property is fixed, never the property. Write it with the developer or from their specification, show it, and get it approved before generating candidates.

```ts
import type { Contract } from '../src/types.js';

export default {
  name: 'guarded-answer',
  intent: 'Each customer message is answered once; an input-guard violation refuses the turn instead.',
  sources: ['SOURCE'],                         // arrival generator supply: declared, never inferred
  sinks: ['SENT', 'REFUSED', 'TURN_PERMIT'],   // every place the net may rest in
  scales: [1, 2],
  properties: [
    { name: 'nothing stranded', spec: { kind: 'deadlockFree' } },
    { name: 'every message ends in an outcome', spec: { kind: 'accounting', outcomes: ['SENT', 'REFUSED'] } },
    { name: 'one turn at a time', spec: { kind: 'placeBound', place: 'TURN_PERMIT', bound: 1 } },
  ],
} satisfies Contract;
```

- **Always include `deadlockFree` and `accounting`.** The first catches stranded tokens, the second lost events. Neither implies the other.
- **Model arrivals with a generator** (a supply place with k tokens plus an `arrive` transition) and list the supply place in `sources`. Accounting is only expressible when the number of inputs is known.
- Mark properties that only hold under timing with `timingDependent: true`. The untimed routes cannot prove them (`metrics.md` §3). For such a property the harness turns on libpetri's timed counterexample check (VER-023): when the untimed route says `Violated` and the timed state-class graph closes with no violation, the result is `proven` with route `timed-scg`, a claim about the timed net only; a truncated timed graph leaves it `violated`.
- Translate the developer's business requirements into properties one by one, and keep the requirement ID in the property name, so the artifact shows which requirement each proof covers.
- **Most design defects come from the contract.** In a controlled design-loop experiment, every design passed its gates, and the remaining defects were all intent the contract never stated. Before generating candidates, check each sentence of the intent:
  - "Never combine two requests" is **not** checked by accounting, because the verifier ignores token values. Express it structurally, with ν correlation or one subnet instance per unit, and name it as a design constraint.
  - "Nothing is sent after a refusal": state it as a property, for example mutual exclusion or unreachability on the places involved.
  - Declare **every** legitimate resting place as a sink, including leftover permits and slots. An incomplete sink list pushes designers into adding transitions whose only job is to satisfy the contract.
- **Set `scales` to the number of units that interact.** Two events are needed to barge in, and three for a double barge-in. `[1, 2]` is only the default.

## 3. Write candidates that differ on purpose

Write two to four candidates per contract. Each should take a different design decision the contract leaves open. Variants of one decision teach little. Typical axes:

- cancellation: local cleanup behind a standing marker vs a consume-per-stage canceller;
- correlation: ν join with a budget place vs one subnet instance per unit;
- concurrency: permit place vs sequential turns;
- where a retry budget lives.

```ts
import { PetriNet, Transition, one, outPlace, and } from 'libpetri';
import type { Candidate } from '../src/types.js';

export default {
  name: 'gate',
  rationale: 'Answer subnet cancelled through a port; consume-only refusal paths.',
  build(k) {
    // real libpetri builder API; actions may be omitted
    return { net, marking: new Map([['SOURCE', k], ['TURN_PERMIT', 1]]) };
  },
  subnets: [{ def: answerDef, inputs: ['in', 'cancel'], properties: [/* local properties */] }],
} satisfies Candidate;
```

- `build(k)` must scale the thing the contract counts (units, events, copies). The small-scope gate calls it with 1 and 2.
- Use the real builder API: `SubnetDef`, `instantiate`, ports, `MatchSpec`, timing. The harness binds structure-only actions itself.
- Declare subnets you want proved in isolation in `subnets`. A candidate with encapsulation violations cannot use this gate.
- **A ν candidate must declare `nu: { budgets, mints, carriers }`.** The verifier cannot tell from an action whether it writes a fresh name or copies one it received, so it reads a write of a join key as a fresh name only for a declared mint (NU-010): a transition listed in `mints`, or one that consumes a place listed in `budgets`. A transition that writes a key without consuming a name and is not declared keeps the net off both ν routes, and every quiescence property comes back `unknown`. A relay that copies a name from an upstream place needs that place listed in `carriers`. Lint fails a correlated net with no budget, any undeclared mint, and any producer of a join key whose inputs are neither declared carriers nor budgets. A join that hands its matched name on to a later join, or writes it back onto its own key, declares that output as a relay target on its match spec (NU-054, `relayKey` in TypeScript); the harness then verifies in the `EXTENDED` fragment automatically. For a ν subnet in `subnets`, give the `SubnetCheck` the same `nu` field, with names as the subnet body spells them. Without it, the subnet comes back `unknown`.
- **Subnets are proved under `bounded(1)` and `bounded(2)`** (each input port topped up forever) except in two cases, which get `arrivals(≤1)` and `arrivals(≤2)` and say so in the note: a subnet that writes an in-out port, where `bounded(k)` would answer `unknown` for every property (VER-006 AC3), and a ν subnet, whose endless inputs would leave endless names in flight. Accounting always uses arrivals. A token resting in an output or in-out port counts as delivered for `deadlockFree`.
- **Accounting on a subnet is exact when the subnet has one input port**: exactly k inputs arrive and k outcomes are required. A subnet with several input ports, such as a cancel port, is checked only for the upper bound, and the small-scope gate covers "none lost".
- **Many identical units (sessions, tenants, workers) sharing resources:** build them as instances of one `SubnetDef` that touch each other only through conserved shared places. Whole-net checking at two or more units multiplies the state space and may not finish. An assume-guarantee rule for this shape exists in the harness but is **off by default and must not be relied on**: an adversarial review found it unsound. Check the smallest scales that exercise the interaction, and state what was not checked.
- Use typed places such as `Place<Order>` (avoid `Place<Object>`), for the port to typed languages. The folding sensor cannot use them: TypeScript places carry no runtime token type, so it may flag structurally identical branches that do different work. Treat it as a hint.

## 4. Evaluate, then feed the diagnostics back

`evaluate` writes `out/report.json`, `out/design.html`, one `out/<candidate>.dot` per candidate, and appends to `out/history.json`. It prints a compact summary.

Read the report as diagnostics. The numbers are not scores:

- **Lint finding**: fix the named arc. `build-error` means libpetri refused to build the candidate. Newer versions reject some defects outright, such as an arc on a port place that composition bound away. The builder's message names the problem.
- **`violated` with a trace**: replay the trace against the candidate, find the missing consumer or the wrong arc, and fix the design. Never touch the property.
- **`unknown` / budget exhausted**: the design is too large to decide at this scale. Make it more compositional (subnets with ports) rather than raising the budget.
- **Sensors**: use them only to choose among passing candidates, as explained in `metrics.md` §5. They also point at what to change in the next iteration, for example "multi-token reset on X" or "encapsulation violation from T into S".

Pass `--iteration n` so the history, and the live artifact, can show what changed between rounds.

## 5. Show the developer: the artifact

`out/design.html` is a self-contained page. It shows the contract; every candidate rendered with the libpetri viewer, clusters included; gate results with counterexample traces; the sensor profile grouped by axis; a side-by-side comparison; and, from the second iteration on, a timeline.

- **Publish it as an artifact and keep republishing to the same page** while the loop runs, so the developer watches candidates improve instead of waiting for the end. This is the default whenever the developer is present.
- Lead the summary in chat with the decision the developer has to make: which passing candidate, and the trade-off between them in one sentence each. The page carries the evidence.
- Never present a candidate that has not passed the gates as a recommendation. Show it as a rejected alternative, with the reason.

## 6. Implement in the project language

Once the developer has chosen, implement that net in the project's language (Java, TypeScript, Rust, or Python on the Rust runtime) with the same place and transition names, the same subnets and ports, the same arcs and timing. Real actions replace the structure-only stubs, and each action must write exactly one of the branches its output spec declares (SKILL.md, "Decide, then emit").

Keep the contract's properties as verification tests in the project, asserting `Proven` (never "not violated"). The SMT scripts are identical across languages (VER-013), so the verdicts carry over, but the project's own build should prove them too.

## 7. Prove the implementation is the design

A proof about the TypeScript candidate says nothing about a hand-written Java net until the two are shown to be the same net. DOT export is byte-identical across languages for the same net (EXP-014). So export the implemented net's DOT in the project (`docs/equivalence.md` under `harness/` lists the call per language) and compare:

```bash
npm run design -- compare --design out/gate.dot --impl build/gate.dot
```

Anything other than equal means the implementation drifted: a missing arc, a renamed place, a transition in the wrong subnet. Fix the implementation, or take the change back through the harness as a new candidate. Put this comparison in the project's CI next to the verification tests, so later edits cannot drift from the design without noticing.
