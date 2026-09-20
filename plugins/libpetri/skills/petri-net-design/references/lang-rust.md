# Rust notes (2024 edition, Tokio)

Only the things that change a design decision. Everything in `SKILL.md` still applies.

## `Place<T>` equality is name-only

`Place<T>` derives `PartialEq` and `Hash` on the name; the `PhantomData<T>` does not participate. Two same-named, differently-typed places merge silently under auto-composition and direct composition, exactly as in TypeScript, and unlike Java. Keep names unique.

## No guards

Guards were removed. There is no `all_guarded` and no per-token value predicate. Conditional selection is competing transitions plus `Xor`, or ν name correlation.

## `ctx.flush()` is an atomicity boundary

Rust (and therefore Python) has mid-action publication. Flushed tokens count toward satisfying the output spec and are **not** withdrawn if validation later rejects the firing.

So: an action that needs all-or-nothing output must not flush. Use it for genuine streaming, where each chunk is independently meaningful, and never as a convenience for "get this out early".

Since the 5.0 wave this interacts with the tightened output check (IO-015). Validation now succeeds only when exactly one branch of the spec claims exactly the produced set, and flushed tokens are part of that set, so flushing into a declared place and then selecting a branch that does not claim it is a violation. It used to be accepted. Flush only inside the branch you have already committed to.

## Actions run on Tokio tasks

Real concurrency, which is what you want, and it means an action that blocks a worker thread hurts the whole runtime. Use async I/O inside actions, or `spawn_blocking` for genuinely blocking work.

## Released-API shape

Adding a `pub` field to a released struct is breaking (struct literals). Carry new options as a builder method or an options struct.

## Checkpoint and resume

`marking.snapshot()` gives a `MarkingSnapshot` (`BTreeMap<Arc<str>, Vec<ErasedToken>>`), so place order is code-point order by construction and empty places are omitted. There is no `restore` option: `Marking::from_snapshot(&snap)` *is* the initial marking you hand the executor. Since 7.0 `handle.snapshot()` resolves to a `SnapshotResult { marking, action_in_flight }`; persist only when `is_restore_point()` is true. Every inject accepted before the request is already in the marking, because injects and snapshot requests share one FIFO channel. An async action may await the reply and is reported in flight. A sync action under `run_async` runs inline in the orchestrator loop: it may send the request but must never block on the reply, which is only produced after the action returns.

Design consequences. Clocks restart on resume: a `delayed` is re-waited, a `deadline` or `window` gets a fresh full budget, so a bound that must survive a restore belongs in the token payload or an action timeout. Restore occasionally, never as a scheduling mechanism. If the net mints ν-names, read "Minting across a resume" in `nu-nets.md` before you pin `execution_scope`; an invalid scope **panics** at executor construction, so run untrusted input through `validate_execution_scope` first.

## Verification

Verification shells out to the `z3` executable and speaks SMT-LIB2 text. The `z3` cargo feature is an empty compile gate, not the `z3` / `z3-sys` crate: do not go looking for native bindings.

## Executors

`PrecompiledNetExecutor` borrows the precompiled net for zero-cost reuse; the owned variant caches the program. Both are behaviourally identical to the bitmap reference executor, which is the readable definition of the firing semantics. If a behaviour surprises you, check it against the bitmap executor first.
