# Transition output spec — what's enforced, what isn't

The output spec attached to a transition (`lp.out`, `lp.and_`, `lp.xor`,
`lp.timeout`, `lp.forward_input`) declares the *shape* of outputs the
action may produce. Since [IO-015] the Rust runtime the binding rides on
enforces that shape at runtime; per-place multiplicity remains a
declaration for documentation, visualization, and formal verification —
one the runtime warns about when a firing exceeds it ([IO-016] AC4).

## What is enforced when the transition is built

`Transition(...).build()` (and every composition that rebuilds a
transition) raises `StructureError` for an output spec no firing could
honour. The checks run in this order and the first failing one reports:

1. A place named twice in one AND branch ([IO-011]), e.g. `lp.and_(P, P)`.
2. More than one `lp.timeout`, nested or not ([IO-013]):
   `output spec of transition 't' has 2 Timeout nodes; an output spec has at most one, nested or not (IO-013)`.
3. An `lp.forward_input` outside the child of an `lp.timeout` ([IO-014]):
   a forward deposits only on the timeout outcome.
4. An `lp.forward_input` whose source is not an input place ([IO-014]).
5. Two branches claiming the same set of places ([IO-012]), such as
   `lp.xor(P, P)` or `lp.xor(P, lp.timeout(ms, P))`: no write could tell
   them apart.

   ```python
   lp.Transition("t").input(lp.one(a)).output(lp.xor(p, p)).build()
   # StructureError: output spec of transition 't' is ambiguous: output
   #   branches 0 and 1 both claim {P}; no write can tell them apart (IO-012)
   ```

No executor option skips these checks.

## What is enforced at runtime

1. **Declared-place rule.** `ctx.output(name, ...)` and
   `ctx.output_many(name, ...)` raise `ValueError` if `name` is not a
   place mentioned anywhere in the transition's output spec. This one
   fires eagerly, inside the action.

   ```python
   t = (lp.Transition("t").input(...).output(lp.out(out_p)).action(...)
        .build())
   # Inside action: ctx.output("other_p", v) → ValueError
   ```

2. **Shape conformance ([IO-015]).** When the action completes, the set
   of places it wrote to must satisfy the declared spec:

   - `lp.out(P)` requires at least one write to `P`.
   - `lp.and_(A, B)` requires *both* children satisfied.
   - `lp.xor(A, B)` requires *exactly one*, neither zero nor both. The
     written set must equal one branch's places exactly, so with `A`, `B`
     and `C` written, `xor(and_(A, B, C), and_(A, B))` matches the first
     branch only.
   - `lp.timeout(ms, child)` validates `child`. The timeout branch itself
     is exempt: those outputs are synthesized by the runtime and satisfy
     the timeout child by construction.

   A violating firing **deposits nothing at all** — not even the places
   that were written — and its consumed input tokens are **not**
   restored. It surfaces as a `TransitionFailed` event whose error names
   `[IO-015]` and the mismatch:

   ```python
   store = lp.InMemoryEventStore()
   lp.run_sync(net, initial=..., event_store=store)
   for e in store.events():
       if e.type == "TransitionFailed":
           print(e.payload()["error"])
   # [IO-015] 't': output does not satisfy declared spec
   #          (expected and('a', 'b'), produced ["a"])
   ```

   With the default `event_store=None` the executor uses a no-op store,
   so a violation is silent — exactly as an action that raises is silent
   under a no-op store. Pass an event store (or subscribe) if you need to
   observe firing failures.

3. **`skip_output_validation` on `ExecutorOptions`.** Set it to `True` to
   turn rule 2 off for the whole run ([CONC-026]); every firing's output is
   then accepted, a single `lp.out(P)` leaf included, and the [NU-054]
   relay check and the [IO-016] multiplicity warning are off too. Rule 1
   still applies, timeout outcomes deposit as usual, and the build-time
   checks above still run. Matches Java's `Builder.skipOutputValidation`
   and TypeScript's `skipOutputValidation`.

   ```python
   lp.run_sync(net, options=lp.ExecutorOptions(skip_output_validation=True))
   ```

## What is *not* enforced at runtime

4. **Multiplicity.** `lp.out(P)` declares that `P` is written — it does
   not constrain *how many* tokens land there. Validation is by place,
   not by count, so a single firing may emit any number:

   ```python
   .output(lp.out(out_p))  # spec says "P is a written output"
   # Inside action:
   ctx.output("P", a)       # ok
   ctx.output("P", b)       # also ok — two tokens land in P
   ctx.output_many("P", xs) # also ok — N tokens land in P
   ```

   This is intentional for streaming actions. Note that SMT verification
   models each output place as gaining exactly one token per firing, so a
   multi-token action is outside what the verifier proves about the net.

   The runtime says so rather than leaving you to notice ([IO-016] AC4):
   the first firing that writes more than one token to a place its spec
   names emits one `LogMessage` at `WARN` for that transition, naming the
   places and their counts. The tokens are deposited either way — it is a
   diagnostic, not a rule:

   ```python
   # 't': wrote more than one token to a place its output spec names once
   #      (out_p: 2); branch-enumerating analyses model one token per named
   #      place, so this firing exceeds what they explore (IO-016)
   ```

## Where the output spec *also* matters

- **Visualization.** `dot_export` renders the AND/XOR/Timeout structure
  visually so the diagram matches the intended semantics.
- **Verification.** SMT property checking (`lp.verify(...)`,
  `lp.verify_subnet(...)`) consumes the output spec to encode the
  transition's transfer relation.

## Recommendation

Write the output spec to match the *intended* semantics: the runtime now
holds you to it, the diagram stays truthful, and the verification harness
reasons about the same shape.

```python
.output(
    lp.and_(
        lp.out(host.HISTORY),         # always emitted
        lp.xor(                        # exactly one branch:
            lp.out(host.TOOL_CALLS),   #   either tool dispatch …
            lp.out(host.EVENT_OUT),    #   … or terminal response
        ),
    )
)
```
