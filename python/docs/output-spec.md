# Transition output spec — what's enforced, what isn't

The output spec attached to a transition (`lp.out`, `lp.and_`, `lp.xor`,
`lp.timeout`, `lp.forward_input`) declares the *shape* of outputs the
action may produce. The Python binding enforces one rule strictly and
leaves the others as declarations for documentation, visualization, and
formal verification.

## What is enforced at runtime

1. **Declared-place rule.** `ctx.output(name, ...)` and
   `ctx.output_many(name, ...)` raise `ValueError` if `name` is not a
   place mentioned anywhere in the transition's output spec.

   ```python
   t = (lp.Transition("t").input(...).output(lp.out(out_p)).action(...)
        .build())
   # Inside action: ctx.output("other_p", v) → ValueError
   ```

## What is *not* enforced at runtime

2. **Cardinality.** `lp.out(P)` declares that the action *may* write to
   `P` — it does not require exactly one write. Actions can emit zero,
   one, or many tokens to `P` from a single firing:

   ```python
   .output(lp.out(out_p))  # spec says "P is a writable output"
   # Inside action:
   ctx.output("P", a)       # ok
   ctx.output("P", b)       # also ok — two tokens land in P
   ctx.output_many("P", xs) # also ok — N tokens land in P
   ```

   This is intentional for streaming actions and conditional XOR
   branches. No `out_many(P)` API is needed — `out(P)` already permits
   variable cardinality.

3. **AND completeness.** `lp.and_(lp.out(A), lp.out(B))` documents that
   both A and B *are* outputs. It does not require the action to write
   to both — partial emissions are accepted at runtime.

4. **XOR exclusivity.** `lp.xor(lp.out(A), lp.out(B))` documents that
   exactly one of A or B is expected per firing. The runtime does not
   reject an action that emits to both, or to neither.

5. **`skip_output_validation` flag on `ExecutorOptions`.** Output-spec
   validation isn't wired through either backend, so the flag is a
   no-op — set or unset freely.

## Where the output spec *does* matter

- **Visualization.** `dot_export` renders the AND/XOR/Timeout structure
  visually so the diagram matches the intended semantics.
- **Verification.** SMT property checking (`lp.verify(...)`,
  `lp.verify_subnet(...)`) consumes the output spec to encode the
  transition's transfer relation. Cardinality and exclusivity are
  modelled there even though the runtime doesn't police them.
- **Future runtime enforcement.** A future release may add opt-in
  runtime enforcement (gated on `skip_output_validation=False`); the
  current declarative behavior remains the default contract.

## Recommendation

Write the output spec to match the *intended* semantics, even though the
runtime won't catch divergence today. This way the diagram stays
truthful and the verification harness can reason about it.

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
