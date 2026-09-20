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

No `ctx.flush()`, so the mid-action publication rules do not apply.

## Checkpoint and resume (6.1 and later)

`marking.snapshot()` gives place name to tokens, in ascending code-point order with empty places omitted. Hand it back as `{ restore: snap }` with an empty initial marking; supplying both is an error, not a merge. `executor.snapshot()` on a running net returns `{ marking, actionInFlight }`, captured at one instant. Persist only when `isRestorePoint(result)` is true (a function exported from `libpetri`, exactly `!result.actionInFlight`): the flag is true while an action is running **or** while an injected event has been accepted and not yet deposited, and in either case a token is in no place. A saver written as an event-store decorator keys on `transition-completed`, which is emitted from a settled marking. Persist as an array of entries, `JSON.stringify([...snap])` and `new Map(JSON.parse(stored))`, because a JavaScript object reorders integer-like place names.

Design consequences. Clocks restart on resume: a `delayed` is re-waited, a `deadline` or `window` gets a fresh full budget, so a bound that must survive a restore belongs in the token payload or an action timeout. Restore occasionally, never as a scheduling mechanism. If the net mints ν-names, read "Minting across a resume" in `nu-nets.md` before you pin `executionScope`.

## Verification

Z3 runs as a subprocess. The WASM path was removed in the 4.0 wave, so verification needs a real `z3` binary on `PATH` or named by `LIBPETRI_Z3`, not a bundled artefact. Plan for that in CI images.

## A timed-out `run()` does not cancel the loop by itself

`run(timeoutMs)` is built on `Promise.race`, which abandons the losing promise rather than
cancelling it, so the rejection reaches you while the orchestrator keeps firing transitions and
mutating the marking. Since the 5.0 wave `run(timeoutMs, onTimeout)` takes a policy: `'abandon'`
is the default and the historical behaviour, `'close'` shuts the executor down (in-flight actions
still complete, ENV-013). Both executors accept it.

Design consequence: if the actions have external effects, a bare `run(timeoutMs)` means those
effects keep happening after the caller gave up. Rust and Python have no run-with-timeout at all;
there you wrap `run_async` in `tokio::time::timeout`, which drops the future and genuinely does
cancel the loop.

## Async entry points

Use the async entry points for any net with I/O actions. A synchronous driver occupies the calling context with the executor loop and serialises everything the net was supposed to overlap.
