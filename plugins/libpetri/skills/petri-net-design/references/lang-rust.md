# Rust notes (2024 edition, Tokio)

Only the things that change a design decision. Everything in `SKILL.md` still applies.

## `Place<T>` equality is name-only

`Place<T>` derives `PartialEq` and `Hash` on the name; the `PhantomData<T>` does not participate. Two same-named, differently-typed places merge silently under auto-composition and direct composition, exactly as in TypeScript, and unlike Java. Keep names unique.

## No guards

Guards were removed. There is no `all_guarded` and no per-token value predicate. Conditional selection is competing transitions plus `Xor`, or ν name correlation.

## `ctx.flush()` is an atomicity boundary

Rust (and therefore Python) has mid-action publication. Flushed tokens count toward satisfying the output spec and are **not** withdrawn if validation later rejects the firing.

So: an action that needs all-or-nothing output must not flush. Use it for genuine streaming, where each chunk is independently meaningful, and never as a convenience for "get this out early".

## Actions run on Tokio tasks

Real concurrency, which is what you want, and it means an action that blocks a worker thread hurts the whole runtime. Use async I/O inside actions, or `spawn_blocking` for genuinely blocking work.

## Released-API shape

Adding a `pub` field to a released struct is breaking (struct literals). Carry new options as a builder method or an options struct.

## Verification

Verification shells out to the `z3` executable and speaks SMT-LIB2 text. The `z3` cargo feature is an empty compile gate, not the `z3` / `z3-sys` crate: do not go looking for native bindings.

## Executors

`PrecompiledNetExecutor` borrows the precompiled net for zero-cost reuse; the owned variant caches the program. Both are behaviourally identical to the bitmap reference executor, which is the readable definition of the firing semantics. If a behaviour surprises you, check it against the bitmap executor first.
