import Libpetri.Spec.Text

requirement_text VER_019
  id "VER-019"
  title "Firing-Bound Phase"
  priority SHOULD
  kind B
  body r#"After [VER-018] and before the fixpoint query, the verifier tries to bound the length of every
run. A **ranking** is a weighting `r ≥ 0` of the places with `r·C_t ≤ −1` for every flat
transition `t` that can fire (one that inhibits a place it needs cannot). A consume-all or reset
arc removes at least `pre`, so with `r ≥ 0` the column `C_t = post − pre` bounds such a firing's
effect on `r·M` from above. Every firing therefore lowers `r·M` by at least one, `r·M` never goes
below zero, and no run from `M0` has more than `K = r·M0` firings.
The ranking with the least `K` is found by one `QF_LIA` optimisation query (phase `ranking`) and
re-checked in exact integer arithmetic.

⟦s1|*When* the ranking query answers with a weighting `r`, the phase *shall* re-check in exact integer arithmetic that every weight is at least 0 and that `r·C_t ≤ −1` for every flat transition `t` that can fire, and *shall* take the bound `K = r·M0` only when the re-check passes.⟧

⟦s2|*If* the re-check fails or `K` is larger than `2^53 − 1`, *then* the phase *shall* end inconclusive without a bounded model check, and the pipeline *shall* continue.⟧

`2^53 − 1` is the largest integer that every implementation counts depths in exactly, so all of
them refuse the same bounds.

With the bound, a **bounded model check** decides the property. One `QF_LIA` script (phase `bmc`)
unrolls `d` steps of the exact step relation from `M0`: a selector per step names the transition
fired or an idle step, an idle step is followed only by idle steps, and the violation is asked of
the last marking. The encoder also emits the environment post-caps of [VER-006] for the bounded
witness phase ([VER-025]); here there are none, since this phase sends no query on a net
with injected environment places.

⟦s3|*When* the phase has the bound `K`, it *shall* ask the bounded model check first at depth `min(K, 8, L)`, where `L` is the depth limit, and after an `unsat` answer at a depth `d` below both `K` and `L` it *shall* ask next at depth `min(2d, K, L)`.⟧

⟦s4|The depth limit `L` *shall* be 512 in every implementation.⟧

With the default limit, a bound of 5 is asked at depth 5 alone, and a bound of 25 at the depths
8, 16 and 25.

⟦s5|*If* the bounded model check answers `unsat` at a depth of at least `K`, *then* the phase *shall* return `Proven` with method `bounded-model-check` and the bound `K`.⟧

That is a claim about every run, since none is longer than `K`.

⟦s6|*If* the bounded model check answers `unsat` at the depth limit while `K` is larger, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.⟧

⟦s7|*When* the bounded model check answers `sat` at a depth, the phase *shall* read the run from the model's selectors as the bounded witness phase ([VER-025]) reads it with no injection step, replay it under the exact abstract semantics, and return `Violated` with that run, untrimmed and confirmed, when every step is enabled and the last marking violates the property.⟧

⟦s8|*If* the depth is positive and the model defines none of the step selectors, or the run does not replay to a violating marking, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.⟧

A depth of 0 has no selectors: its run is empty, and it is reported when `M0` violates the
property. That depth is asked only when `K` is 0.

When no ranking exists, Farkas gives firing counts `y ≥ 0, y ≠ 0` with `C·y ≥ 0`, which the
marking equation lets repeat forever. The report names their transitions (a second query) and the
pipeline continues. This does not show that the net has an infinite run (a loop that only an
inhibitor stops has no ranking), only that the phase makes no claim about runs it cannot bound.

⟦s9|*If* the ranking query answers `unsat`, *then* the phase *shall* report that the net has no firing bound, whatever the second query answers, and the pipeline *shall* continue to the fixpoint query.⟧

⟦s10|*If* the ranking query or a bounded model check fails in the transport or answers `unknown`, or the phase budget is spent before its answer, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.⟧

A proof from this phase has no inductive invariant, so the certificate check does not apply; it
rests on the exactly re-checked ranking and the solver's `unsat`. The phase gets half the
timeout, rounded down to whole milliseconds and at least 1 ms: short counterexamples take
seconds, while a proof to a deep bound on a wide net can outlast any budget. It runs on the
queries [VER-018] runs on, whether [VER-018] is enabled or not. Its bounded run has transition
steps only. The bounded witness phase ([VER-025])
shares its encoder, adds injection steps to it and asks one fixed depth without a bound, so it
finds runs but proves nothing; on a net without injection its script is this phase's script. A
name-alignment property ([NU-055]) gets no query from the phase: it ends inconclusive with the
reason of [NU-055] before any other check.

⟦s11|*If* environment places are declared for injection, *then* the phase *shall* send no query and *shall* end inconclusive, also when no arc touches such a place.⟧

No weighting bounds an injection.

⟦s12|Every implementation *shall* turn this phase on by default, as it turns on the phase of [VER-018].⟧

A pre-fixpoint verdict carries its own `method` and report, so differing defaults break the
verdict-parity fixtures without any property differing.

⟦s13|*If* the phase is disabled, *then* the verifier *shall not* run it, and the verdicts and reports *shall* be those of the pipeline without the phase.⟧

Disabling the phase leaves the query to the later steps, up to the fixpoint query.

⟦s14|The pipeline *shall* place the firing-bound phase at one point, after the state-equation phase of [VER-018] and before the bounded witness phase of [VER-025] and the fixpoint query.⟧

So no run enters the state-equation phase after this phase, this phase after the witness phase or the fixpoint query, or this phase twice.

⟦s15|*While* the phase is enabled, the pipeline *shall* run it on exactly the queries that the state-equation phase of [VER-018] runs on when that phase is enabled, whether [VER-018] is enabled or not, unless an earlier step has decided the query or the run has stopped.⟧

⟦s16|*When* the phase ends inconclusive or reports that the net has no firing bound, the pipeline *shall* go on to its next step.⟧

⟦s17|*When* the phase returns `Proven` or `Violated`, the verifier *shall* return that result: `Proven` with the method `bounded-model-check` and neither a counterexample nor `counterexampleConfirmed`; `Violated` with the transitions of the replayed run, in firing order, as the counterexample and `counterexampleConfirmed` `true`.⟧

Measured on the same 23 workflow nets: the violated net [VER-018] leaves open has `K = 25` and a
22-step counterexample at depth 25 in about 11 s; proofs to `K ≤ 22` take 0.1–70 s; `K = 86` on
the twenty-way switch does not finish depth 16 within 120 s; two loop nets have no ranking. Four
agent nets whose round only an inhibitor stops have none either, although every run terminates;
with the re-entry routed through a place of its own they have one, and where their graphs close
`K` equals the longest run (38, 41, 50 and 70 firings).

**Acceptance Criteria:**
1. The ranking is re-checked in exact integer arithmetic before its bound is used; the report
   names it with the bound, e.g. `    Bound: 5 firings (budget + s + 2*src drops on every firing)`.
2. A violating run found by the bounded model check is replayed and reported `violated`,
   confirmed.
3. `unsat` at depth `K` is `Proven` with method `bounded-model-check`, and the report carries
   `  Certificate check: not applicable (bounded model check to the firing bound)`.
4. A net without a ranking is reported with the transitions of a repeatable firing vector
   (`    Status: no firing bound — the marking equation lets t0, t1, t2 repeat; not attempted`),
   or, when the second query finds no vector or gets no answer, with
   `    Status: no firing bound (no weights decrease on every firing); not attempted`, and the
   fixpoint query runs.
5. With the phase disabled, verdicts and reports are those of the pipeline without it.

**Implementation notes:**
- TypeScript: `verification/z3/bounded-run` (`encodeRankingQuery`, `checkRankingExact`,
  `encodeRepeatableVectorQuery`, `encodeBoundedRun`, `replayRun`, `runFiringBoundPhase`);
  `SmtVerifier.firingBound(enabled)`.
- Rust: behind the `z3` feature, `bounded_run` (the same functions in snake case);
  `SmtVerifier::firing_bound(bool)`.
- Python: `verify(..., firing_bound=True)`.
- Java: `org.libpetri.smt.z3.BoundedRun` (the same methods); `SmtVerifier.firingBound(boolean)`.

**Depends on:** [VER-001], [VER-003], [VER-004], [VER-013], [VER-018]

**Test derivation:** the queue-and-bundle net of [VER-018] with that phase disabled, the
enumeration budget of [VER-017] at 0 and `assumeAtomicFiring`: the ranking `budget + s + 2*src`
gives the bound 5, and the bounded model check at depth 5 proves the property; with the cancel
alternative, a replayed run violates it. A ring `p0 → t0 → p1 → t1 → p2 → t2 → p0`, with the
enumeration budget at 0 and the linear bound ([VER-015]) and [VER-018] off, has no ranking: the
report names `t0, t1, t2`, and the fixpoint query proves `placeBound(p0, 1)`."#
