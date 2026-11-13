import Libpetri.Spec.Text

requirement_text TIME_001
  id "TIME-001"
  title "Timing Specification"
  priority MUST
  kind F
  body r#"Each transition has an associated timing specification that defines when it can and must fire relative to the moment it was armed. The timing is expressed as an interval `[earliest, latest]` where:
- The transition CANNOT fire before `earliest` time units have elapsed since it was armed ([TIME-010]).
- A reapable transition (`Deadline` or `Window`) MUST be reaped once its elapsed time exceeds `latest` plus the deadline tolerance ([TIME-013]). `Exact` has a latest bound but is enforced softly ([TIME-006]); `Immediate` and `Delayed` have no finite latest bound.

⟦s1|`earliest()` *shall* return 0 for `Immediate` and `Deadline`, `after` for `Delayed(after)`, `earliest` for `Window(earliest, latest)` and `at` for `Exact(at)`.⟧

⟦s2|`latest()` *shall* return the maximum duration for `Immediate` and `Delayed`, `by` for `Deadline(by)`, `latest` for `Window(earliest, latest)` and `at` for `Exact(at)`.⟧

⟦s3|`hasDeadline()` *shall* return true for `Deadline`, `Window` and `Exact`, and false for `Immediate` and `Delayed`.⟧

A maximum duration constant (~100 years: `MAX_DURATION_MS` = 3153600000000 ms in Rust, TypeScript and Python, `MAX_DURATION` = `Duration.ofDays(36500)` in Java) is the finite stand-in for "no constraint" on the upper bound. `Immediate` and `Delayed` have the interval `[earliest, ∞)`; their `latest()` reports the maximum duration, and they are never reapable.

⟦s4|A timing is **valid** exactly when its bounds satisfy these rules, which are canonical for every variant ([TIME-002]–[TIME-006] restate them):⟧

| Variant | Valid when |
|---|---|
| `Immediate` | always |
| `Deadline(by)` | `0 < by <= maximum` |
| `Delayed(after)` | `0 <= after <= maximum` |
| `Window(earliest, latest)` | `0 <= earliest <= latest <= maximum` |
| `Exact(at)` | `0 <= at <= maximum` |

⟦s5|*If* a factory is called with bounds that make the timing invalid, *then* the factory *shall* fail with the message the table below gives for the first rule the bounds break (Rust panics; Python raises `ValueError` with the Rust message; Java throws `IllegalArgumentException`; TypeScript throws `Error`).⟧

| Check | Rust, TypeScript, Python | Java |
|---|---|---|
| `deadline`: `by` not positive | `Deadline must be positive: {by}` | `Deadline must be positive: {by}` |
| `deadline`: `by` above maximum | `Deadline must be at most MAX_DURATION_MS (3153600000000): {by}` | `Deadline must be at most MAX_DURATION (PT876000H): {by}` |
| `delayed`: `after` negative | `Delay must be non-negative: {after}` | `Delay must be non-negative: {after}` |
| `delayed`: `after` above maximum | `Delay must be at most MAX_DURATION_MS (3153600000000): {after}` | `Delay must be at most MAX_DURATION (PT876000H): {after}` |
| `window`: `earliest` negative | `Earliest must be non-negative: {earliest}` | `Earliest must be non-negative: {earliest}` |
| `window`: `earliest` above maximum | `Earliest must be at most MAX_DURATION_MS (3153600000000): {earliest}` | `Earliest must be at most MAX_DURATION (PT876000H): {earliest}` |
| `window`: `latest` below `earliest` | `Latest ({latest}) must be >= earliest ({earliest})` | `Latest ({latest}) must be >= earliest ({earliest})` |
| `window`: `latest` above maximum | `Latest must be at most MAX_DURATION_MS (3153600000000): {latest}` | `Latest must be at most MAX_DURATION (PT876000H): {latest}` |
| `exact`: `at` negative | `Exact time must be non-negative: {at}` | `Exact time must be non-negative: {at}` |
| `exact`: `at` above maximum | `Exact time must be at most MAX_DURATION_MS (3153600000000): {at}` | `Exact time must be at most MAX_DURATION (PT876000H): {at}` |

`{x}` is the rejected argument as the language prints it: decimal milliseconds in Rust, TypeScript and Python, `Duration.toString()` in Java. Rust's `u64` arguments cannot be negative, so the non-negative checks exist only in TypeScript and Java. ⟦s6|The checks run in the order of the table.⟧

An earliest bound above the maximum is rejected for the same reason a negative one is. `delayed(after)` has the interval
`[after, maximum]`, which would be empty, and a state-class graph would read a transition that
can fire as one that never can: a false timed deadlock and a wrong `SPURIOUS_UNDER_TIMING`
([VER-023]). `window` and `exact` follow because a verifier that drops their latest bound reads
them as `delayed(earliest)` ([VER-002]). `deadline(by)` with `by` above the maximum is rejected as well:
`by` is the only bound a `Deadline` has, and a deadline beyond the stand-in for "no constraint" is
one no run reaches. The latest bound of a `Window` is checked against the maximum for the same
reason: a `Window` reports `hasDeadline()` and is reapable, so a latest bound above the maximum
would be a hidden "never". A window with no upper bound is written `delayed(earliest)`.

The same checks apply to a timing written out without a factory. Where the variants can be
constructed directly (Rust's public `Timing` enum variants, a TypeScript object literal), the
transition builder runs the factory's check again when the transition is built and fails with
the factory's message. Java's timing records run the check in their constructors, so no timing
escapes it there. Without this, `Timing::Delayed { after_ms: MAX + 1 }` handed to a Rust
builder reaches the verifier: the timed check reports a wrong `SPURIOUS_UNDER_TIMING`, and a
directly written `Window` whose earliest bound is above the maximum makes the verifier panic
when it rebuilds the window as `delayed(earliest)`.

⟦s7|*If* a transition is built with a timing written out without a factory and that timing is invalid, *then* building the transition *shall* fail with the factory's message.⟧

**Acceptance Criteria:**
1. ⟦s8|Each transition has a timing specification (defaults to Immediate).⟧
2. `earliest()` and `latest()` are queryable.
3. `hasDeadline()` returns true for `Deadline`, `Window` and `Exact` and false for `Immediate`
   and `Delayed`, whatever the bounds (a `Window` whose latest bound equals the maximum still has
   a deadline).
4. The validity table above is canonical. In particular `delayed`, `window` and `exact` reject an
   earliest bound one millisecond above the maximum duration and accept one equal to it, and
   `deadline` rejects a `by` one millisecond above the maximum duration and accepts one equal to
   it, and `window` rejects a latest bound one millisecond above the maximum duration
   (`window(maximum, maximum + 1)`) and accepts one equal to it (`window(maximum, maximum)`,
   `window(0, maximum)`), each with the message of the table.
5. A timing written out without a factory is held to AC4 and to the factories' other checks
   (`deadline(0)`, `window` with latest below earliest): building a transition with one fails
   with the factory's message, and a valid one builds unchanged.

**Test derivation:** Create each timing variant; verify earliest(), latest(), hasDeadline(). For
AC4, construct `delayed`, `window` and `exact` with an earliest bound of `maximum + 1`, and
`deadline` with `maximum + 1`, and `window(maximum, maximum + 1)` and `window(0, maximum + 1)`,
and expect the construction error with the table's message; construct each with `maximum`, and
`window(maximum, maximum)` and `window(0, maximum)`, and expect success. `window(maximum + 1,
maximum + 2)` fails with the earliest bound's message, since the checks run in the table's order. For AC5,
write each invalid timing out directly (a Rust enum variant, a TypeScript object literal, a Java
record constructor) and expect the transition build (Java: the constructor) to fail."#
