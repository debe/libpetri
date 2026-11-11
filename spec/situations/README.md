# Situations: small nets played step by step, replayed by the verified Lean reference

A situation is a small net with a short story: a list of steps, each naming a transition to
fire. The spec site (https://libpetri.org/spec/) draws the net and plays the steps back. For
every situation that the untimed reference can replay, the marking after each step, and the
reason a step cannot fire, come from the machine-checked Lean reference
(`lean/Libpetri/Reference/Situation.lean`), never from hand-written data.

## Files

- `<slug>.json`: one situation per file, schema below. The slug is the file name without
  `.json`; use lowercase words joined by `-`.
- `expected/<slug>.json`: the replay of the situation, written by
  `lake exe reference situations`. Never edit these by hand.

```bash
python3 scripts/situations.py --update   # replay every situation into expected/
python3 scripts/situations.py --check    # re-derive into a temp dir and diff (CI, conformance job)
```

Both need the reference built (`cd lean && lake build reference`). `--check` ignores the
`reference` field, as `scripts/conformance-corpus.py --check` does.

## Situation schema (`<slug>.json`)

```json
{
  "title": "A held lock keeps the gate shut",
  "group": "Firing",
  "text": "Plain-words explanation shown above the player.",
  "cites": ["CORE-022", "CORE-031"],
  "replay": true,

  "places": ["job", "lock", "done"],
  "marking": { "job": 3 },
  "transitions": [
    { "name": "take",
      "inputs": [ { "place": "job", "kind": "one" } ],
      "inhibitors": ["lock"],
      "output": { "type": "place", "place": "lock" } },
    { "name": "release",
      "inputs": [ { "place": "lock", "kind": "one" } ],
      "output": { "type": "place", "place": "done" } }
  ],

  "steps": [
    { "fire": "take", "text": "`lock` is empty, so `take` fires and marks it." },
    { "fire": "release" },
    { "fire": "take", "branch": 0 },
    { "fire": "take", "expect": "blocked" }
  ]
}
```

**Situation keys** (removed before the net is loaded):

| Key | Type | Meaning |
|---|---|---|
| `title` | string, optional | Short title of the situation card. |
| `group` | string, optional | Group on the home page, e.g. `Firing`, `Outputs`, `Time`, `Running`, `Correlation`, `Composition`, `Verification`, `Export`. |
| `text` | string, optional | Plain-words explanation, Markdown inline (`code`, *emphasis*). Write place, transition and API names in backticks and start sentences with a capital. |
| `cites` | array of spec IDs, optional | Requirements the situation shows, e.g. `"CORE-031"`. |
| `replay` | boolean, optional, default `true` | `false` for a situation the untimed reference cannot replay (timing, environment places, ν / match specs, composition, export, verification). Such a file gets no expected file and is not loaded by Lean at all, so it may carry any other keys the site needs. |
| `steps` | array, required when `replay` is not `false` | The steps, in order. |

**Net keys**: exactly the corpus net schema of
[`spec/verification-fixtures/conformance/README.md`](../verification-fixtures/conformance/README.md)
(`places`, `marking`, `transitions` with `name`, `inputs`, `inhibitors`, `reads`, `resets`,
`output`, `priority`, `timing`), read by the same loader (`lean/Libpetri/Reference/Load.lean`).
`id` and `properties` are accepted and ignored. Any other key, and every check the builders make
(two input arcs on one place, an input and a read arc on one place, two transitions with one
name, invalid output specs, invalid timing), makes the reference refuse the situation: the
binary exits 1 and names the file. Priorities and timing are read but play no part in the
replay: every enabled transition may fire, as in the untimed semantics ([VER-004]).

**Step keys** (any other key is refused):

| Key | Type | Meaning |
|---|---|---|
| `fire` | string, required | Name of the transition to fire. |
| `branch` | non-negative integer, optional, default `0` | The output branch the action writes, numbered from 0 in the order [IO-016] enumerates the branches: an `xor` lists its children's branches in order, an `and` is the cross product with the first child varying slowest, a `timeout` node contributes its child's branches. A transition without an output spec has the one branch `0`, which deposits nothing. |
| `timeout` | boolean, optional, default `false` | `true` ends the firing with the timeout outcome ([IO-013]) instead of an action branch: the timeout child's places get one token each, and a `forward(from, to)` puts in `to` one token per token consumed from `from` ([IO-014]). `branch` then selects among the timeout outcomes, of which a spec has at most one, so only `0` can fire; any other is reported as `noSuchBranch`. |
| `text` | string, optional | Caption the player shows for the step; ignored by Lean. Write place, transition and API names in backticks. |
| `expect` | `"fired"` or `"blocked"`, optional, default `"fired"` | What the author says the step does; ignored by Lean. The spec site's build fails when the replay of a step has another outcome, and a `"blocked"` step must be the last one. This is what makes "Lean replay agrees" on the page a check rather than a restatement. |

## The replay

The reference fires the steps in order from `marking` with the reference firing rule
(`lean/Libpetri/Reference/Semantics.lean`, `Fires`): consumption per input cardinality
([IO-001]–[IO-004], [IO-007]), reset places end holding exactly what the firing deposits
([CORE-034]), read and inhibitor places are not consumed. It stops at the first step that cannot
fire. The reasons, checked in this order, and the requirement each cites:

| `reason.kind` | Fields | When | `requirement` |
|---|---|---|---|
| `unknownTransition` | | the net has no transition named `fire` | `CORE-020` |
| `inputShort` | `place`, `arc` (`{"kind", "n"?}` as in the net schema), `need`, `have` | the first input arc, in declaration order, whose place holds `have` < `need` tokens | `IO-001` (one), `IO-002` (exactly), `IO-003` (all), `IO-004` (atLeast) |
| `inhibitorMarked` | `place`, `count` | the first inhibitor place holding `count` > 0 tokens | `CORE-031` |
| `readEmpty` | `place` | the first read place that is empty | `CORE-032` |
| `noSuchBranch` | `branch`, `timeout`? | the transition is enabled but its output spec has no such branch, or no timeout | `IO-016` (branch), `IO-013` (timeout) |

Inputs come first, then inhibitors, then reads, as [CORE-022] defines enablement. Reset arcs
never block.

**What is proved** (`replaySituation_sound`, in the CI axiom check): on a net with unique
transition names (the loader refuses any other), every fired step is a firing of the reference
semantics of the named transition with the chosen outcome, from the previous marking to the
marking reported; for a blocked step the reason is true of the marking, the named transition has
no firing with the chosen outcome, and for every reason but `noSuchBranch` no step of the
semantics carries the transition's name at all. `Replays.run`: when every step fired, the steps
are a firing sequence of the semantics from `marking` to the last marking.

## Expected file schema (`expected/<slug>.json`)

```json
{
  "slug": "inhibitor-blocks",
  "reference": "<sha256 of lean/Libpetri/Reference/*.lean>",
  "initial": {"job": 3},
  "complete": false,
  "steps": [
    { "index": 0, "fire": "take", "branch": 0, "fired": true, "marking": {"job": 2, "lock": 1} },
    { "index": 3, "fire": "take", "branch": 0, "blocked": true,
      "reason": {"kind": "inhibitorMarked", "place": "lock", "count": 1},
      "requirement": "CORE-031",
      "message": "'take' is not enabled: inhibitor place 'lock' holds 1 token" }
  ]
}
```

- `initial` and every `marking`: token counts by place name, keys sorted, **places holding no
  token left out**.
- `steps`: one entry per step up to and including the first blocked one; later steps are not
  replayed and have no entry. Each entry repeats `index` (0-based), `fire`, `branch`, and
  `"timeout": true` when the step chose the timeout outcome. A fired entry has
  `"fired": true` and `marking`; a blocked entry has `"blocked": true`, `reason`,
  `requirement` and a one-sentence `message`.
- `complete`: `true` when every step fired.
- `reference`: the content hash of the reference sources, as in the conformance corpus.
