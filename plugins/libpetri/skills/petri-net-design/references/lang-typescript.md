# TypeScript notes (TypeScript 6, ESM only)

Only the things that change a design decision. Everything in `SKILL.md` still applies.

## `Place<T>` equality is name-only at run time

`Place<T>` is an interface carrying a `name` plus a phantom type parameter. The token type does not exist at run time. Two same-named, differently-typed places **merge silently** under auto-composition body inference and direct composition. `tsc` is the only enforcement, and it only sees what you annotate.

Design rule: unique names, always. Do not lean on the type to keep two places apart.

## No guards, no per-token predicates

Guards were removed in the 3.0 wave. There is no `all(place, predicate)` and no per-token value filter anywhere in the model. Conditional selection is modelled as competing transitions with an `Xor` on the producing side, or as ν name correlation.

## Actions and the event loop

Actions return promises, and the event loop provides the concurrency. The trap is different from Java's: it is easy to write an action that resolves immediately and does the real work in a floating promise, which detaches the work from the firing and from every event the net emits about it. Return the promise that actually completes when the work is done.

## Not available here

No `ctx.flush()`, so the mid-action publication rules do not apply. No marking snapshot and restore, so checkpoint and resume designs do not port to TypeScript yet.

## Verification

Z3 runs as a subprocess. The WASM path was removed in the 4.0 wave, so verification needs a real `z3` binary on `PATH` or named by `LIBPETRI_Z3`, not a bundled artefact. Plan for that in CI images.

## Async entry points

Use the async entry points for any net with I/O actions. A synchronous driver occupies the calling context with the executor loop and serialises everything the net was supposed to overlap.
