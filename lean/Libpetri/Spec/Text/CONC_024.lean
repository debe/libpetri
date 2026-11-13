import Libpetri.Spec.Text

requirement_text CONC_024
  id "CONC-024"
  title "Precomputed Timing Arrays"
  priority SHOULD
  kind F
  body r#"Timing constraints are precomputed into flat arrays at compile time to avoid virtual dispatch on timing types during execution:
- `earliestNanos[]` / `earliestMillis[]` — earliest firing time per transition
- `latestNanos[]` / `latestMillis[]` — latest firing time (MAX_VALUE if no deadline)
- `hasDeadline[]` — boolean flag per transition
- `allImmediate` — global flag: true if all transitions are immediate
- `anyDeadlines` — global flag: true if any transition has a deadline

Millisecond arrays are precomputed to avoid nanosecond-to-millisecond division on the hot path.

⟦s1|*When* a net is precompiled, the timing arrays *shall* hold, for each transition, the `earliest()` of its timing in the array's unit and the `hasDeadline()` of its timing ([TIME-001]).⟧

⟦s2|*When* a net is precompiled, the timing arrays *shall* hold, for each transition whose timing's `hasDeadline()` is true, the `latest()` of its timing in the array's unit.⟧

⟦s3|*When* a net is precompiled, `allImmediate` *shall* be true exactly when every transition of the net has the timing `Immediate`.⟧

⟦s4|*When* a net is precompiled, `anyDeadlines` *shall* be true exactly when some transition of the net has a timing whose `hasDeadline()` is true.⟧

**Acceptance Criteria:**
1. Timing arrays are populated at compile time, not computed per cycle.
2. `allImmediate` flag allows skipping timing checks entirely for immediate-only nets.
3. `anyDeadlines` flag allows skipping deadline enforcement when no deadlines exist.
4. Precomputed millisecond values match the nanosecond values (within rounding).

**Test derivation:** Compile nets with various timing configurations; verify array values and global flags."#
