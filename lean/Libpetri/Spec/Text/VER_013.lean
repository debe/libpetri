import Libpetri.Spec.Text

requirement_text VER_013
  id "VER-013"
  title "Solver Transport"
  priority SHOULD
  kind B
  body r#"The SMT pipeline ([VER-001]) reaches the solver through one transport in every implementation:
each query is one `z3` process. The process is started with the argument list

```
z3 -smt2 -in -t:<timeout_ms> -T:<ceil((timeout_ms + 1000) / 1000)>
```

plus `fp.engine=spacer` for the HORN query, is fed the complete SMT-LIB2 script on stdin in a
single write, and then has its stdin closed so it sees end-of-file. Both output streams are
drained concurrently from the start, so a reply larger than a pipe buffer cannot stall the
solver, and a wall-clock watchdog at `timeout_ms + 2000` milliseconds kills a process that
ignored both timeouts. The process is killed and reaped on every exit path. No solver state
survives a query: concurrent verifications in one host process are independent, and a solver
crash is a verdict, never a crashed host. The timeout is per invocation; the HORN query, the
certificate script and its detail re-run each receive the full budget. The formula is fixed for a
`timeout_ms` of at least 1. A timeout of 0 is outside it: Java and TypeScript raise it to 1 ms, so
that `-t:0`, which `z3` reads as no limit, never reaches the solver, and Rust passes `-t:0`.

**Total budget.** Because the timeout is per invocation, one `verify()` can run for several times
it: the bound query ([VER-015]), the state-equation phase shared across its refinements
([VER-018]) and its certificate check and detail re-run, the firing-bound phase at half the
timeout ([VER-019]), the bounded witness phase at an eighth of it ([VER-025]), the HORN query and
its certificate check and detail re-run add up to about 7.6 timeouts, plus 2 s of watchdog slack per process, plus the solver-free work (the enumeration
route [VER-017], Route B [VER-012], the timed check [VER-023], the siphon and trap search
[VER-020], Farkas, the colour-slot simplex of [NU-053]), which no timeout bounds. An
implementation SHOULD therefore offer an
optional **total budget**, a wall-clock limit on the whole call. It is off by default, and with
it unset behaviour and reports are byte-identical to the above. When it is set:

- The deadline starts when `verify()` is entered, before the terminal rewrite of [EXEC-042], so
  all of the call's work counts against it.
- Every `z3` process receives `min(its normal budget, remaining)` as its `timeout_ms`, and derives
  `-t`, `-T` and the watchdog from that clamped value by the formulas above. When nothing
  remains, no process is started.
- The solver-free graph builds (the enumeration route, Route B, the timed check) and the long
  solver-free loops (siphon and trap search, Farkas, the colour-slot simplex, the trim of the
  bounded witness phase [VER-025]) poll the deadline,
  cheaply (every so many classes or iterations), and stop when it has passed. The colour-slot
  simplex runs as its own step, `colour-slot bound`, entered once every other check of the
  coloured plan has passed, and polls before every pivot.
- When the deadline passes before a verdict is reached, the verdict is `Unknown` with the reason
  `total verification budget of <N> ms exhausted during <phase>`, `<phase>` naming the step
  that was running when the budget ran out, and the report carries the same line. A poll made
  on entering a step checks the deadline **before** it records the new step, so an exhaustion
  found there blames the step that just ended, not the one about to start; every implementation
  names the same step for the same stop. A verdict reached before the deadline stands.
- A graph build the deadline stopped is not a class-budget truncation. It MUST NOT be recorded in
  a state-space cache ([VER-017]) as a truncation at the class budget: it leaves the cache entry
  as it found it, like a build that fails.
- The HORN query no longer keeps its full budget. Without a total budget, the fixpoint query gets
  the whole timeout however long the pre-fixpoint phases of [VER-018], [VER-019] and [VER-025]
  took; under a total budget it gets what they left.

The per-call timeout keeps its meaning above: the budget of one process. The total budget
applies to one `verify()` call. `SubnetDef.verify` ([MOD-051]) and open-net verification
([VER-022]) reach it only through their per-query configuration hooks, so each of their queries
gets its own budget; neither has a budget across its queries.

**Cancellation.** An implementation SHOULD let the caller stop a running `verify()` from outside
it. Cancellation is not a second mechanism: it shares the total budget's stop. The deadline
becomes "deadline passed **or** cancelled", and everything that polls the deadline (the clamp
before each `z3` process, the graph builds, the long solver-free loops) sees cancellation at the
same points, whether or not a total budget is set. Beyond that:

- A `z3` process running when cancellation arrives is killed at once and reaped, not left to its
  timeout or watchdog. A cancelled call starts no further process.
- The verdict is `Unknown` with the reason `verification cancelled during <phase>`, `<phase>` named
  as for the total budget, and the report carries the same line. There is no new verdict. A call
  cancelled before it starts returns this at once. A verdict reached before cancellation stands.
- When a total budget is also set, whichever stop comes first names the reason.
- A graph build stopped by cancellation is not a class-budget truncation and leaves a state-space
  cache as it found it, as for the total budget.
- `SubnetDef.verify` ([MOD-051]) and open-net verification ([VER-022]) honour cancellation too,
  including the solver queries open-net verification runs outside `verify()` (its termination
  ranking): a cancelled call starts no further query.

The mechanism follows each language's idiom:

- **TypeScript**: an `AbortSignal`, passed with `SmtVerifier.signal(signal)` (also reachable from
  the `configure` hook of `SubnetDef.verify` and from `OpenNetOptions`). `runZ3Text` takes the signal
  and kills the process with `SIGKILL` when it aborts.
- **Rust**: `CancelToken` (`Clone`, `Send + Sync`, a shared atomic flag; `new()`, `cancel()`,
  `is_cancelled()`), passed with `SmtVerifier::cancel_token(&CancelToken)`. The watchdog's poll
  loop in `Z3Solver::run` checks it and kills and reaps the process.
- **Python**: `libpetri.CancelToken` wraps the Rust token; `verify(..., cancel=token)` and
  `verify_subnet(..., cancel=token)`. The verification runs with the GIL released, so `cancel()`
  from another thread, or from an asyncio task while the call runs in an executor, takes effect.
- **Java**: thread interruption, Java's own cancellation idiom; there is no token. Interrupting the
  thread that runs `verify()` cancels it: the running `z3` process is destroyed, the remaining
  phases are skipped, and the result is the `Unknown` above. The graph builds and loops read the
  thread's interrupt status at their deadline polls without clearing it, and the interrupt flag is
  set again when `verify()` returns, so the caller still sees it.

The executable is `z3` on `PATH` unless the environment variable `LIBPETRI_Z3` names another
one. It is probed once per verification with `--version` and refused below **4.8.0**. Setting
`LIBPETRI_SMT_DUMP` to a directory keeps every script and reply there as `NNN-<phase>.smt2`,
`NNN-<phase>.out` and, when stderr was not empty, `NNN-<phase>.err`, with `NNN` a zero-padded
counter and the phase one of `bound` ([VER-015]), `state-equation`, `invariant` ([VER-018]),
`ranking`, `bmc` ([VER-019]), `witness` ([VER-025]), `horn`, `horn-coloured`, `certificate`,
`certificate-detail`.

**Reply classification.** The verdict is the first stdout line equal to `sat`, `unsat` or
`unknown`, wherever it appears: a build may print a warning first, and the HORN script's paired
`(get-proof)` / `(get-model)` always yields one `(error …)` line. Under the HORN query
`(assert (not Error))`, `sat` is `Proven` and `unsat` is `Violated`. Without a verdict line the
`Unknown` reason is, in this order: the `timeout` line printed by the `-T` backstop; the watchdog
kill; the first `(error …)` line on stdout, then on stderr; any other stderr text; the unexpected
stdout itself. ⟦s1|A verdict line decides whatever else the reply carries, an `(error …)` line or a
non-zero exit included.⟧ The certificate script requires exactly three positional answers; an `(error …)`
on either stream, a `timeout` line, a kill or a non-zero exit makes the check inconclusive and
withholds `Proven`.

**Script determinism.** For the same net, initial marking, property and options every
implementation MUST emit byte-identical HORN and certificate scripts: places in Unicode
code-point order of their names; flat transitions in net order with XOR branches in enumeration
order ([IO-016]); environment-injection rules, sink conjuncts and the property's place lists in
place-index order; invariants in `(support, weights, constant)` order after the [VER-007] union;
lines joined with `\n`; no rule names. The certificate is the `(define-fun …)` block of the
`(get-model)` reply pasted verbatim, and a counterexample is the set of ground `Reachable` facts
in the `(get-proof)` reply, ordered only by the replay ([VER-003]).

**Name order.** ⟦s2|Every ordering of place or transition names that reaches a script, a flat
index, a report, a witness or a violation list MUST compare names by Unicode code point, never
by host locale or UTF-16 code unit: the flat place index above, the canonical clock order of a
state class ([VER-010]), and the markings and violation lists of an open-net report
([VER-022]).⟧ Locale order varies by host; UTF-16 order (JavaScript `<`, Java
`String.compareTo`) differs from code-point order (Rust `str`) wherever a character above
U+FFFF meets one in U+E000–U+FFFF.

**The transport, as EARS sentences.**

⟦s3|*When* the verifier starts a `z3` process with a timeout of `t` milliseconds, `t` at least 1, it *shall* pass `-t:t` and, as `-T`, the smallest whole number of seconds that is at least `(t + 1000) / 1000`, and *shall* kill the process at `t + 2000` milliseconds if it has not exited.⟧

⟦s4|*While* a total budget is set, the verifier *shall* give each `z3` process the smaller of its normal timeout and the whole milliseconds that remain, and *shall* start no process when none remain.⟧

⟦s5|The verifier *shall* read the verdict of a reply off the first stdout line that, trimmed, equals `sat`, `unsat` or `unknown`, wherever that line appears.⟧

⟦s6|*If* no stdout line of a reply is a verdict line, *then* the verifier *shall* give as the reason of the failure the first of these that applies: a `timeout` line on stdout, the watchdog kill, the first `(error …)` line on stdout and then on stderr, any other stderr text, the stdout itself.⟧

⟦s7|*If* a `z3` process gives no verdict line, or no process is started, *then* the step that asked for it *shall* read the failure as no answer, so a step that proves a property only on a solver answer *shall not* return `Proven` from it.⟧

⟦s8|*When* the poll made on entering a step finds the total budget spent or the call cancelled, the verifier *shall* charge the stop to the step that was running before, *shall* not enter the new step, and *shall* end the pipeline without a verdict.⟧

⟦s9|*While* a stop is recorded, the verifier *shall* start no `z3` process, enter no step and reach no verdict.⟧

⟦s10|*When* a stop is recorded, the verifier *shall* keep a `Proven` or `Violated` reached before it, and *shall* give an `Unknown` the reason `total verification budget of <N> ms exhausted during <phase>` or `verification cancelled during <phase>`, `<phase>` the step the stop was charged to.⟧

⟦s11|*While* no total budget is set and the caller does not cancel, the verifier *shall* record no stop.⟧

**Acceptance Criteria:**
1. The same net, marking, property and options produce byte-identical HORN and certificate
   scripts in every implementation (the golden scripts under
   `spec/verification-fixtures/scripts/`).
2. A missing executable yields `Unknown` with a reason naming the command tried and
   `LIBPETRI_Z3`; no exception escapes and the host process survives.
3. An executable below 4.8.0, or one whose `--version` reports no version, yields `Unknown`
   naming both versions (or the reply).
4. A reply without a verdict line yields `Unknown` with the reason of the reply classification
   above: a `timeout` line, a process that never exits (the watchdog kill), an `(error …)` on
   either stream, other stderr text and unexpected stdout each give a distinct reason, and no
   solver process is left behind. A verdict line decides even when an `(error …)` line or a
   non-zero exit comes with it; in the certificate check either makes the check inconclusive.
5. A reply preceded by a banner of arbitrary size on either stream is classified by its verdict
   line.
6. The report carries `  Solver: z3 <version>` in its solver phase, or
   `  Solver: z3 unavailable (<reason>)` followed by the implementation's `UNKNOWN` result
   line naming the same reason when no solver resolved.
7. Sorted from any starting order, the names `""`, `Z`, `a`, `ab`, `Ä` (U+00C4), `中` (U+4E2D),
   U+E000, `Ａ` (U+FF21), U+1D400 and U+1F600 come out in exactly that order in every
   implementation. A UTF-16 code-unit sort puts U+1D400 and U+1F600 before U+E000.
8. With no total budget set, verdicts, reports and solver arguments are those of the
   requirement without it.
9. With a total budget of `N` ms, `verify()` returns within `N` ms plus one process's watchdog
   slack (2 s) and one polling interval; a query it cannot finish in time is `Unknown` with the reason
   `total verification budget of N ms exhausted during <phase>`, and no `z3` process starts
   once the budget is spent.
10. An enumeration build stopped by the total budget leaves a state-space cache as it found it:
    a later query with more time and the same class budget builds rather than declines.
11. Cancelling a verification while a `z3` process runs kills that process at once: the call
    returns well before the process's timeout, with verdict `Unknown` and the reason
    `verification cancelled during <phase>`, and starts no further process. A call cancelled
    before it starts returns the same `Unknown` without starting one. In Java the cancellation is
    an interrupt of the verifying thread, and the thread's interrupt flag is set when `verify()`
    returns.
12. Cancellation during an enumeration or Route B build stops the build at its next deadline poll
    with the same reason, and leaves a state-space cache as it found it.

**Implementation notes:**
- Rust: `libpetri-verification` `z3_process` (`Z3Solver::resolve` / `Z3Solver::run`);
  stub-solver scenarios in `tests/stub_z3.rs`, CI gate in `tests/z3_gate.rs`.
- Python: inherits the Rust transport; `libpetri.z3_available()` reports whether a usable
  executable resolves (`HAS_Z3` is the compile feature only).
- Java: `org.libpetri.smt.z3.Z3Process` / `Z3Solver`; `SmtVerifier.z3Available()`.
- TypeScript: `verification/z3/z3-process` (`resolveZ3` / `runZ3Text`); `z3Available()`.
  Names are ordered by `compareCodePoints` (`core/internal/code-point-order`, ICU's code-point
  fix-up on the first differing UTF-16 unit pair).
- Total budget: Java `SmtVerifier.totalBudget(Duration)`, TypeScript
  `SmtVerifier.totalBudget(ms: number)`, Rust `SmtVerifier::total_budget(ms: u64)`, Python
  `verify(..., total_budget_ms=None)`. Every process passes through one choke point per
  implementation (Java `Z3Solver.run`, TypeScript `runZ3Text`, Rust `Z3Solver::run`), which is
  where the clamp applies. Java's `Z3Solver` is a public record and keeps its components; the
  deadline travels beside it.
- AC1 is checked without a solver: `SmtVerifier::encode_scripts` (Rust), `encodeScripts()`
  (Java, TypeScript) and `libpetri.encode_smt_scripts` (Python) return the HORN script and,
  for the flat encoding, the certificate script around the placeholder certificate
  `(define-fun Reachable (…) Bool true)`; the goldens under
  `spec/verification-fixtures/scripts/<id>/` are written by the Rust verifier
  (`scripts/smt-script-parity.py --update`) and diffed by every implementation's
  script-parity test. A name-coloured HORN script carries the colour-slot bound `k` of
  [NU-053]; each implementation computes it with its own exact simplex, so `encodeScripts()`
  still starts no solver.

**Depends on:** [VER-001], [VER-003], [VER-007], [VER-017], [VER-022], [MOD-051], [IO-016]

**Test derivation:** a stub `z3` shell script named by `LIBPETRI_Z3` that answers `--version`
and then replays a scripted reply: a banner before `unsat`; an `(error …)` on stderr during the
certificate check; a `timeout` line; a script that never exits; a two-megabyte banner on each
stream; a version below the floor; a missing executable. For the total budget: a stub that sleeps past it, with
a total budget below the per-call timeout, yields the exhaustion reason within the budget. For
cancellation: the same sleeping stub, cancelled (Java: the verifying thread interrupted) shortly
after it starts, yields the cancellation reason long before the timeout, and the stub process is
gone; a token cancelled before the call yields it without a process. Plus the golden-script diff over the
shared verdict-parity fixtures, and the AC7 vector through each implementation's name
comparator."#
