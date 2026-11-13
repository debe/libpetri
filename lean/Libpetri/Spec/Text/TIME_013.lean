import Libpetri.Spec.Text

requirement_text TIME_013
  id "TIME-013"
  title "Deadline Enforcement"
  priority MUST
  kind T
  body r#"A transition with a **hard deadline** (`Deadline` / `Window`) is **reapable**. ⟦s1|When a reapable transition is expired, that is, armed with an elapsed time strictly greater than its latest bound plus the deadline tolerance, the executor reaps it: it disarms the transition without firing it and emits a `TransitionTimedOut` event.⟧ ⟦s2|Implementations MUST apply a deadline tolerance — a grace band beyond `latest` (default 5ms) that absorbs timer-resolution and scheduling jitter — and SHOULD expose it as a configurable per-executor option (e.g. `deadlineTolerance` / `deadline_tolerance_ms`); a value of `0` gives strict enforcement.⟧

`Exact` timing is **not** subject to destructive enforcement: it is enforced softly per [TIME-006] (fires at the first opportunity at/after its target, never force-disabled). ⟦s3|Only `Deadline` and `Window` transitions are reaped here.⟧

⟦s4|*If* a reapable transition is armed and its elapsed time is greater than its latest bound plus the deadline tolerance, *then* the executor *shall* reap it in the deadline step of that cycle ([EXEC-001] step 4) and emit `TransitionTimedOut` ([EVT-009]).⟧

⟦s5|*If* a reapable transition's elapsed time is greater than its latest bound plus the deadline tolerance, *then* the transition *shall not* fire.⟧

⟦s6|The executor *shall not* reap a transition that is not reapable.⟧

⟦s7|The deadline step *shall* judge expiry at its reading of the firing clock ([TIME-010]), and it *shall not* reap a transition that is not expired at that reading or change the marking.⟧

⟦s8|*While* a transition is reaped, the transition *shall not* fire.⟧

⟦s9|*When* a firing or an injected token writes one of a reaped transition's arc places (an input, read, inhibitor or reset place) and the transition is enabled afterwards, the transition *shall* be newly armed with a fresh clock ([TIME-010]).⟧

⟦s10|*While* a transition is reaped, an enablement update *shall* leave it reaped, and only a firing or an injected token that writes one of its arc places *shall* end its reaped state.⟧

⟦s11|A firing writes a place when it consumes from it, deposits into it or drains it through a reset arc; draining a reset place that is already empty counts as a write.⟧ The tolerance is the `deadlineTolerance` / `deadline_tolerance_ms` option, and with tolerance `0` a reapable transition is reaped on the first cycle whose elapsed time is strictly greater than its latest bound.

**Acceptance Criteria:**
1. A transition with Deadline(5s) still armed past 5s plus the tolerance does not fire after that bound. If it is still armed on the first cycle whose elapsed time is strictly greater than the bound, it is reaped in that cycle and `TransitionTimedOut` is emitted.
2. The tolerance is documented and configurable; the default is 5ms across implementations.
3. An `Exact` transition observed past its target is **not** disabled (see [TIME-006]).
4. A reaped transition does not fire again while none of its arc places is written, on every
   executor backend (Bitmap and Precompiled alike). Once a firing or an injected token writes one
   of its input, read, inhibitor or reset places, it is armed again with a fresh clock if it is
   enabled, and may fire.

⟦s12|A reaped transition keeps its input tokens and is not armed again until one of its arc places is
written, so an executor that fell behind can come to rest at a marking that still
enables it.⟧ Verification accounts for that: a `Deadline` / `Window` transition is **reapable**, and
every quiescence property reads a marking whose enabled transitions are all reapable as quiescent
([VER-002], [VER-004]). The executor that reaps also fires the others late, and fires a late
`Exact` transition after its target, so Route B ([VER-012]), the timed name-aware graph, drops the
latest bound of every `Deadline`, `Window` and `Exact` transition for every property. The opt-out
`assumeNoReaping` assumes an on-time executor instead; on Route B it also assumes actions that
take no time ([VER-004] AC3).

**Depends on:** [TIME-010], [EVT-009]
**Test derivation:** Create a `Window`/`Deadline` transition; block the executor past `latest + tolerance`; verify timeout event and disablement. Separately, verify an `Exact` transition under the same conditions still fires. For AC4, run the reap on both backends, confirm neither fires the reaped transition and both end at the same marking, then add a later transition that deposits into its input place and confirm it fires only after that deposit."#
