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

## Checkpoint and resume (6.1 and later)

`marking.snapshot()` gives `Map<String, List<Token<?>>>`: place name to tokens, ascending code-point order, empty places omitted. Resume with `BitmapNetExecutor.builder(net, Map.of()).restore(snap).build()` (the precompiled builder is the same); a restore next to a non-empty initial marking throws. `executor.snapshot()` returns `SnapshotResult(marking, actionInFlight)` captured as one pair. Persist only when `isRestorePoint()` is true: the flag is set while an action is running **or** while an accepted `inject` has not yet reached its place. Called from inside an action it returns at once and always reports work in flight, because actions run inline on the orchestrator thread. Called from another thread it waits for the orchestrator, for at most two seconds; if a blocking inline action keeps the request unserved, the last published marking comes back flagged in flight, never as a restore point.

Structural `Place` equality shows up here twice. `Marking.fromSnapshot(snapshot, places)` needs the net's places (`net.places()`), because a place rebuilt from a name alone would not equal the net's own. And a net that declares two places with one name and different token types cannot be snapshotted or restored at all: `snapshot()` throws `IllegalStateException`, `restore(...).build()` throws `IllegalArgumentException`, both on the caller's thread. Keep names unique and neither matters.

Design consequences. Clocks restart on resume: a `delayed` is re-waited, a `deadline` or `window` gets a fresh full budget, so a bound that must survive a restore belongs in the token payload or an action timeout. Restore occasionally, never as a scheduling mechanism. If the net mints ν-names, read "Minting across a resume" in `nu-nets.md` before you pin `executionScope(...)`.

## Available only here

`terminateNow()` and `awaitTermination` on the executor handle.

## Verification

Z3 runs as a subprocess speaking SMT-LIB2 text, the same as every other language. There is no JNI path. `z3` must be on `PATH` or named by `LIBPETRI_Z3`.
