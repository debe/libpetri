# Java notes (Java 25, `CompletionStage`)

Only the things that change a design decision. Everything in `SKILL.md` still applies.

## Action dispatch is inline on the orchestrator thread

`t.action().execute(ctx)` is called directly by the orchestrator loop. No executor dispatches actions. The `ExecutorService` you pass to the builder hosts exactly one task, the orchestrator loop itself, and only under the timed `run(Duration)` form.

Consequences you must design around:

- **A blocking action blocks the whole net.** Not the transition, the net. Every other enabled transition waits.
- Concurrency comes from whatever drives the `CompletionStage` you return, which libpetri does not own. Return a stage backed by your own pool, an async HTTP client, or a virtual thread.
- `CompletableFuture.cancel(true)` on an `Out.Timeout` cannot interrupt anything, because there is nothing to interrupt. Timeout excludes the output; it does not stop the work.

If you find yourself writing `.join()` or `.get()` inside an action, stop. That is the single most common way to turn a concurrent net into a sequential one.

## `Place` is a record with structural equality

`record Place(String name, Class<T> tokenType)`. Equality is on **both** fields, so two same-named, differently-typed places do not merge under auto-composition or direct composition, and the type conflict is rejected naming both types.

This is the strictest of the three engines. A design that relies on it will not port to TypeScript or Rust, where equality is name-only. Keep names unique and the design travels.

## Released-API shape

Adding a component to a public `record` is a breaking change (record patterns destructure positionally). Carry new options as an overload or a parameter object, not as a new record component. The same rule with different mechanics applies to Rust `pub` fields.

## Not available here

- No `ctx.flush()`, so the mid-action publication rules do not apply.
- Marking snapshot and restore is pending, so checkpoint and resume designs do not port to Java yet.

## Available only here

`terminateNow()` and `awaitTermination` on the executor handle.

## Verification

Z3 runs as a subprocess speaking SMT-LIB2 text, the same as every other language. There is no JNI path. `z3` must be on `PATH` or named by `LIBPETRI_Z3`.
