# Transition output spec — what's enforced, what isn't

The output spec attached to a transition (`lp.out`, `lp.and_`, `lp.xor`,
`lp.timeout`, `lp.forward_input`) declares the *shape* of outputs the
action may produce. Since [IO-015] the Rust runtime the binding rides on
enforces that shape at runtime; per-place multiplicity remains a
declaration for documentation, visualization, and formal verification.

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
   - `lp.xor(A, B)` requires *exactly one* — neither zero nor both. If
     several branches match and one subsumes all the others (as
     `and_(A, B, C)` subsumes `and_(A, B)`), the most specific branch is
     selected rather than rejected.
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
   turn rule 2 off for the whole run; every firing's output is then
   accepted. Rule 1 still applies. Matches Java's
   `Builder.skipOutputValidation` and TypeScript's
   `skipOutputValidation`.

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
