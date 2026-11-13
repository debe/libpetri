import Libpetri.Spec.Text

requirement_text CORE_037
  id "CORE-037"
  title "Dead Arc Warning"
  priority SHOULD
  kind F
  body r#"A read, inhibitor or reset arc on place `P` is **dead** when:

- no transition has an input arc on `P`,
- no transition's output spec names `P` anywhere in its tree (every branch of every AND and XOR,
  the `Timeout` child and the `ForwardInput` target included),
- `P` is not an environment place ([ENV-001]), and
- the initial marking holds no token on `P`.

No firing ever puts a token on such a place, and a host injects tokens only into environment
places ([ENV-001]), so a dead read arc means its transition can never be enabled,
a dead inhibitor never blocks and a dead reset clears nothing. Each is legal: a read or
inhibitor on a place the initial marking seeds, or
a reset on a place a host fills through injection, is common and deliberate, which is why the
condition asks about the initial marking and the environment places, and why a dead arc is
**never an error**. But the shape is also what a stale reference looks like: an arc naming a
place that composition renamed away, or a typo, leaves an arc that silently does nothing. The
case that motivated this requirement was a host reset naming a subnet's port place after compose
had bound that port to a host place; [MOD-027] now rejects that case outright, and this warning
covers the rest.

In EARS form, for a net, its initial marking and its environment places, the dead-arc report is
the list of dead arcs an implementation reports:

⟦s1|The dead-arc report *shall* contain a read, inhibitor or reset arc of a transition of the net exactly when no transition has an input arc on the arc's place, no transition's output spec names that place anywhere in its tree (every `And` and `Xor` branch, the `Timeout` child and the `ForwardInput` target included), the place is not an environment place and the initial marking holds no token on it, and *shall* contain nothing else.⟧

⟦s2|The dead-arc report *shall* list each dead arc once, as its own entry (two dead arcs on one place are two entries), in the order the net holds its transitions (the order they were added to the builder) and, within a transition, its read arcs, then its inhibitor arcs, then its reset arcs, each kind in the order the transition declares those arcs.⟧

⟦s3|The warning text of a read, inhibitor or reset arc of a transition *shall* be `<kind> arc of '<transition>' on '<place>': no transition produces into or consumes from it and it starts empty; <effect>.` with `<kind>` the arc's kind (`read`, `inhibitor` or `reset`), `<transition>` the name of the transition that declares the arc, `<place>` the name of its place, and `<effect>` `the transition can never be enabled` for a read arc, `the arc never blocks` for an inhibitor arc and `the arc has no effect` for a reset arc.⟧

An implementation SHOULD report every dead arc, once, where the net meets its initial marking:

- **Executors**, every backend, when the executor is constructed: one log-message event
  ([EVT-013]) per dead arc, through the same mechanism and with the same field shape as the
  unknown-place diagnostic of [CORE-072] AC4: logger `libpetri.runtime` (omitted where the
  log-message event carries no logger field), level `WARN`, transition name = the transition that
  declares the arc, message

  ```
  <kind> arc of '<transition>' on '<place>': no transition produces into or consumes from it and it starts empty; <effect>.
  ```

  with `<kind>` one of `read`, `inhibitor`, `reset` and `<effect>` respectively
  `the transition can never be enabled`, `the arc never blocks`, `the arc has no effect`.
  One message per dead arc, not per place: two dead arcs on one place are two messages. Arcs are
  reported in transition order and, within a transition, read, inhibitor, then reset.
  Like AC4 it is emitted only where events are recorded, and never changes execution.
- **The SMT verifier** ([VER-001]): one report line per dead arc, the same text prefixed with
  `WARNING: `, judged against the verification's own initial marking and environment places, e.g.

  ```
  WARNING: reset arc of 'hub_kill' on 'answer/IN': no transition produces into or consumes from it and it starts empty; the arc has no effect.
  ```

  No result field changes and no verdict depends on it.

In EARS form, for an executor or the SMT verifier that reports dead arcs, with the dead-arc report and the warning text above:

⟦s4|*Where* an executor reports dead arcs, the events that carry the warning text of an arc of the net (its dead-arc events) and that it emits before `ExecutionStarted` *shall* be, in report order, one `WARN` log-message event per entry of the dead-arc report for its net, its environment places and its initial marking, each carrying the name of the transition that declares the arc and the warning text of that arc.⟧

⟦s5|*Where* an executor reports dead arcs, it *shall not* emit a dead-arc event as an engine diagnostic after `ExecutionStarted`.⟧

⟦s6|*Where* an executor reports dead arcs, its other events and its steps *shall* be those of the same executor that does not report dead arcs, as if its dead-arc events had never been emitted.⟧

⟦s7|*Where* the SMT verifier reports dead arcs, the lines of a verification's report that are `WARNING: ` followed by the warning text of an arc of the net (its dead-arc lines) *shall* be, in report order, one line per entry of the dead-arc report for the net as the caller passed it, the verification's initial marking and its environment places, each `WARNING: ` followed by the warning text of that arc.⟧

⟦s8|*Where* the SMT verifier reports dead arcs, its report with the dead-arc lines and the blank line after them left out *shall* be the report of the same verifier that does not report dead arcs, and every other field of its result except the elapsed time *shall* be as it is in that verifier.⟧

**Acceptance Criteria:**
1. A reset arc on a place no transition consumes from or produces into, that is not an
   environment place and that the initial marking leaves empty, produces exactly one `WARN`
   log-message event naming the transition and the place when an executor is constructed, and
   one `WARNING:` line in the verifier's report.
2. The same holds for a read arc (effect: the transition can never be enabled) and an inhibitor
   arc (effect: the arc never blocks).
3. No warning when the initial marking puts a token on the place, when the place is an
   environment place, when any transition has an input arc on it, or when any transition's output
   spec (any branch) contains it.
4. The warning never rejects a net and never changes execution, a verdict or a result field.

**Implementation notes:**
- Java: `BitmapNetExecutor` and `PrecompiledNetExecutor`, beside the [CORE-072] AC4 seam;
  `SmtVerifier.verify()`.
- TypeScript: both executors, beside the [CORE-072] AC4 seam; `SmtVerifier.verify()`.
- Rust: both backends, beside the [CORE-072] AC4 seam; `SmtVerifier::verify()`.
- Python: inherits the Rust executor events and report.

**Depends on:** [CORE-031], [CORE-032], [CORE-034], [CORE-072], [ENV-001], [EVT-013]
**Test derivation:** A net whose transition `kill` resets `x`, where nothing else touches `x`:
construct each executor with an empty initial marking and assert one `WARN` log-message event
naming `kill` and `x`; seed `x` with a token and assert none. Verify any property of the same net
and assert the report line. Repeat with a read arc and an inhibitor arc, and with `x` produced
by another transition's XOR branch (no warning)."#
