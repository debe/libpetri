# Conformance corpus — nets as data, verdicts from the verified Lean reference

Every language's verifier is checked against one **executable, machine-checked reference**
written in Lean (`lean/Libpetri/Reference/`, binary `lake exe reference`). The reference is
derived from the spec (CORE / IO / EXEC rules), not from any implementation, and is proved to
compute exactly the reachable markings of the untimed semantics and to decide each property by
its meaning. The corpus and its expected verdicts live here; expected verdicts are **written by
the Lean binary, never by hand** (compare `spec/verification-fixtures/scripts/`, written by Rust).

Scope, version 1: closed nets (no environment places), no ν / match specs. Priorities and
transition timing are allowed in the data; the reference ignores priorities and reads timing only
for reapability (clarification 7), as every untimed route does (VER-004). Terminal places
(EXEC-042) are out of scope in v1.

## Files

- `nets/<id>.json` — one net per file, schema below.
- `expected/<id>.json` — the reference's verdict per property, written by `lake exe reference`.
- `corpus.json` — the index: ids, generator seed, reference version.

## Net schema (`nets/<id>.json`)

```json
{
  "id": "gen-000123",
  "places": ["a", "b", "c"],
  "marking": { "a": 2, "z": 1 },
  "transitions": [
    {
      "name": "t",
      "inputs":    [ { "place": "a", "kind": "one" },
                     { "place": "b", "kind": "exactly", "n": 2 },
                     { "place": "c", "kind": "all" },
                     { "place": "d", "kind": "atLeast", "n": 1 } ],
      "inhibitors": ["x"],
      "reads":      ["y"],
      "resets":     ["w"],
      "output": { "type": "xor", "children": [
                  { "type": "place", "place": "c" },
                  { "type": "and", "children": [ { "type": "place", "place": "b" } ] },
                  { "type": "timeout", "afterMs": 50,
                    "child": { "type": "forward", "from": "a", "to": "b" } } ] },
      "priority": 0,
      "timing": { "kind": "window", "earliestMs": 3, "latestMs": 5 }
    }
  ],
  "properties": [
    { "id": "p0", "type": "deadlock-free", "sinks": ["c"] },
    { "id": "p1", "type": "terminates-at-sink", "sinks": ["c"] },
    { "id": "p2", "type": "place-bound", "place": "b", "bound": 1 },
    { "id": "p3", "type": "mutual-exclusion", "places": ["a", "b"] },
    { "id": "p4", "type": "unreachable", "places": ["a", "c"] },
    { "id": "p5", "type": "quiescent-count", "places": ["c"], "min": 1, "max": 1 }
  ]
}
```

- `places` are the **declared** places. Arcs may name places not listed (they are places of the
  net by use); `marking` may name places no arc touches and that are not declared (inert places,
  CORE-072 / VER-003) — this is deliberate, it is how the stray-token bug hid.
- `inputs[].kind`: `one` | `exactly` (with `n ≥ 1`) | `all` | `atLeast` (with `n ≥ 1`) — IO-001..004.
  At most one input arc per place per transition (CORE-030).
- `output`: `place` | `and` | `xor` | `timeout` (`afterMs`, `child`) | `forward` (`from` must be an
  input place of the transition, `to` a place) — IO-011..016; `null` / absent = no output.
  A `forward` deposits one token per consumed token of `from` (IO-014).
- `timing` (optional; absent = `immediate`): `{"kind": k, "earliestMs": e, "latestMs": l}` with
  the bounds the kind takes (TIME-002..006): `immediate` / `unconstrained` none, `deadline`
  `latestMs` (> 0), `delayed` `earliestMs`, `window` both (`e ≤ l`), `exact` `earliestMs`
  (`latestMs`, if given, equal to it). Any other key or a missing bound makes the net invalid.
  `deadline` and `window` are **reapable** (TIME-013).
- `unreachable.places`: the property is violated by a reachable marking that marks **all** listed
  places (VER-002).
- `mutual-exclusion.places` (two or more): violated by a reachable marking that marks **two** of
  the listed entries (pairwise, VER-002).
- `quiescent-count`: at every quiescent marking, the total tokens across `places` lies in
  `[min, max]` (`max` may be omitted = unbounded).
- `deadlock-free` / `terminates-at-sink`: VER-002 sink semantics; `sinks` may be empty.
- "Quiescent" is **reap-quiescent** (VER-002): every enabled transition is reapable. On a net
  without reapable timing that is "no transition enabled".

## Clarifications (v1, fixed 2026-09-28)

1. **mutual-exclusion** takes two or more places and is **pairwise** (VER-002 AC10): violated iff
   two entries of the list, at different positions, are marked at once. Two places are
   `MutualExclusion(p1, p2)`; a place listed twice pairs with itself. The reference rejects a list
   of fewer than two as out of scope. Java and TypeScript take exactly two places, so their
   runners skip (and count) a property over three or more — an API limit, not a
   non-conformance; Rust and Python check it.
2. **Conditional sinks** (`sinkPlacesWhen`) and **quiescent-count waivers** (`waivedBy`) are out of
   scope in v1.
3. **`reference`** in expected files is the SHA-256 of the concatenated sources of
   `lean/Libpetri/Reference/*.lean` in path order (a content hash, stable across commits).
4. **Replay:** a trace is a list of transition names. A step replays if the transition is enabled
   and *some* outcome of it (IO-013..016) lets the rest of the trace replay and end in a marking
   violating the property. An empty trace means the initial marking violates.
5. **Outcomes of a transition** (the analysis abstraction every untimed route uses, VER-004):
   when the action completes, each Xor branch of the output (with `timeout` nodes contributing
   their child's claim) deposits **one token per claimed place** — the documented unit-output
   convention, including a `forward` claimed by a completing action; when the timeout fires, the
   timeout child's places receive their deposit, and a `forward` there deposits the **consumed
   count** of `from` (IO-014): `n` for `exactly(n)`, 1 for `one`, and the number actually removed
   for `all` / `atLeast` (a transfer). The timeout outcome is a distinct outcome only when it differs
   from every completion branch.
6. A language reporting `violated` must report a trace; an initial-marking violation is the
   empty trace `[]` (VER-003 AC8), which the reference replays. A `violated` with no trace at all
   fails rule 3. (Until 2026-09-28 every language's IC3 route reported 29 initial-marking
   violations without one, and the runners counted them instead.)

7. **Timing** (added 2026-09-28). The reference explores the untimed net: every enabled
   transition may fire whatever its timing, since timing only restricts firing (VER-004). Timing
   matters in one place: a `deadline` / `window` transition can be reaped by a late executor
   (TIME-013), which then rests with it still enabled, so the quiescence properties
   (`deadlock-free`, `terminates-at-sink`, `quiescent-count`) are read at **reap-quiescent**
   markings (VER-002). `lean/Libpetri/Novel/ReapAware.lean` proves this sound for every timed
   execution (`rest_sound`, `reap_aware_ac3`); the reference's `verdict_proven_iff` holds with the
   reap-aware `Violates`. Languages verify these nets with their default reap-aware reading
   (no `assumeNoReaping`). About 20% of the generated nets carry timing, drawn from a stream of
   its own so the untimed nets are unchanged; `reap-*` are the named reaping cases.

## Expected verdict schema (`expected/<id>.json`)

```json
{ "id": "gen-000123", "reference": "<lean git hash>", "classes": 47, "complete": true,
  "results": [ { "property": "p0", "verdict": "violated", "trace": ["t", "u"] },
               { "property": "p2", "verdict": "proven" },
               { "property": "p4", "verdict": "unknown", "reason": "cap" } ] }
```

- `proven` only when the state space was explored completely; `violated` always with a firing
  sequence from the initial marking that the reference replays; `unknown` for "cap reached" or
  "out of v1 scope" (with `reason`).
- A `forward` from an `all` / `atLeast` input is explored exactly by the reference (transfer
  semantics). The languages' graph routes (enumeration, Route B) count the drained batch the same
  way and decide it; their linear routes refuse it (`unknown`), which is conforming but
  incomplete — so with the enumeration off (the `smt+lb`, `smt-lb` and `ic3` setups) these
  queries stay `unknown`.

## Conformance rule (what every language's test asserts)

For every net, property and verifier route:
1. never `proven` where the reference says `violated`;
2. never `violated` where the reference says `proven` — unless the language's counterexample
   replays under the reference firing rule, which would falsify the reference (then fail loudly);
3. every `violated` trace a language reports must replay under the reference firing rule;
4. `unknown` is always allowed (incompleteness is not non-conformance), but counts are reported.

Every language runs each route twice. The **atomic pass** sets `assumeAtomicFiring`, so the
verifier reads each firing as one step, as the reference does, and all four rules apply.

The **default pass** leaves the in-flight split on ([VER-004]). The split net has more runs than
the reference, so rule 2 does not apply: a `violated` where the reference says `proven` is counted
and reported, and is expected when an action in flight changes the outcome. Rules 1, 3 and 4 still
apply. A trace over a split net contains `complete:<t>` steps the reference firing rule does not
know, so it is confirmed by the verifier's abstract replay on the split net and not replayed by the
reference.
