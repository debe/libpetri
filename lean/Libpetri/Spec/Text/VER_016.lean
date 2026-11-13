import Libpetri.Spec.Text

requirement_text VER_016
  id "VER-016"
  title "State-Equation Strengthening with Firing Counters"
  priority SHOULD
  kind B
  body r#"The flat CHC encoding ([VER-001]) MAY carry the **state equation** itself. With the option
enabled the state is `(M, n)` — one firing counter `n_t` per flat transition after the
places — the initial fact has `n = 0`, transition `t`'s rule sets `n'_t = n_t + 1` and copies
every other counter, an environment-injection rule copies them all, and every transition
rule's body conjoins `n' ≥ 0` and, for each place `p` whose column is exact (no
consume-all / reset arc on `p`, `p` not injected), `m'_p = M0_p + Σ_t C[p][t]·n'_t` over the
transitions with a non-zero effect on `p`, in transition order. A place a consume-all or
reset arc clears, and that is not injected, carries the upper bound
`m'_p ≤ M0_p + Σ_t C[p][t]·n'_t` in the same position instead. It is inductive because a
clearing step's guard needs `m_p ≥ pre_p`, so its result `m'_p = post_p` is at most
`m_p + C[p][t]`. The error rule quantifies the counters and constrains the marking only.

Every linear consequence of the marking equation — the equality laws of [VER-005] and
[VER-007], the decreasing laws of [VER-015], and the mixed-sign inequalities
(`y·C ≥ 0 ⇒ y·M ≥ y·M0`) that express *ordering* between the stages of a pipeline — is then a
fact in every rule body rather than a lemma Spacer has to generalise to, and it comes at no
enumeration cost: the cone of inequality laws of a fifty-place net has too many extreme rays
to list, but its defining system has one row per place. This is what a **quiescence** proof
on a workflow net needs and [VER-015] cannot give it (a `DeadlockFree` violation is not a
linear demand): proper completion of a 50-place agent-dispatch net under conditional sinks
([VER-014]) went from `unknown` at 120 s to `proven` in 1.5 s with this as the only change.

The option is **off by default** so scripts and reports stay byte-identical; a genuinely
violated property is still found, about 1.5× slower on the nets above. Soundness is proven in
Lean (`StateEquation.lean`: `rows_hold`, `state_equation_reach_eq`): the counters are exact
bookkeeping, so every row holds on every reachable augmented state and conjoining them
removes none. The **certificate check** ranges over `(M, n)`: the candidate conjoins the
P-invariants, `n ≥ 0` and the marking equation, and re-proves them against the raw step
relation, whose only counter knowledge is the increment. The certificate check is on by
default; with it disabled (`certificateCheck(false)` in Java and TypeScript,
`certificate_check(false)` in Rust, `certificate_check=False` in Python) a `Proven` rests on
the solver's answer alone, and the report carries
`  Certificate check: not applicable (disabled)` in place of the check. The counterexample
decoder reads a fact's marking from its leading `P` arguments. The option does not apply to
the name-coloured encoding ([NU-050]) or to Route B ([VER-012]); the report says so on the
name-coloured path only, and a run that a route or phase decides before the fixpoint query
prints no state-equation line.

⟦s1|*While* the state-equation option is enabled, the initial fact of the flat CHC encoding *shall* set every firing counter to 0.⟧

⟦s2|*While* the option is enabled, the rule of each transition *shall* fire that transition only where it is enabled, with the effect it has in the untimed abstraction of [VER-004], add one to its firing counter and copy every other counter, each environment-injection rule *shall* add one token to its place and copy every counter, and no rule but these and the initial fact *shall* derive a `Reachable` fact.⟧

⟦s3|*While* the option is enabled, each transition rule *shall* require of its successor `(M', n')`, for every place that is not injected, the equality `m'_p = M0_p + Σ_t C[p][t]·n'_t` where no consume-all or reset arc clears the place, and the upper bound `m'_p ≤ M0_p + Σ_t C[p][t]·n'_t` where one does.⟧

⟦s4|*While* the option is enabled, apart from the P-invariant conjuncts of [VER-005] and [VER-007] and the environment bounds of [VER-006], the rule of each transition *shall* accept its firing from every state `(M, n)` in which the transition is enabled and whose successor meets the rows above, and each environment-injection rule *shall* accept its injection from every state, so the rows remove no reachable state.⟧

**Acceptance Criteria:**
1. With the option disabled the scripts and reports are byte-identical to a build without it.
2. With the option enabled `Reachable` has arity `P + T`, the initial fact ends in `T` zeros,
   transition `t`'s rule contains `(= n_tp (+ n_t 1))` and `(= n_jp n_j)` for every `j ≠ t`,
   and every transition rule contains the marking equation of every exact place over the
   primed variables; a consume-all or reset place carries the upper bound `(<= m_pp …)`
   instead, and an injected place carries none.
3. While the certificate check is enabled (the default), a `Proven` verdict that the fixpoint
   query decides passes the certificate check (`init, consecution, safety`) with the equation
   in the candidate; a genuine violation stays `Violated` and its counterexample replays.
4. The report carries `  State equation: encoded over T firing counters (VER-016)` when the
   option applied, and `  State equation: not applied (name-coloured encoding)` when it was
   requested on the coloured path; a run that a route or phase decides before the fixpoint
   query prints no state-equation line.
5. The HORN and certificate scripts with the option enabled are byte-identical across the four
   implementations ([VER-013] AC1).

**Implementation notes:**
- Java: `SmtVerifier.stateEquation(boolean)`.
- TypeScript: `SmtVerifier.stateEquation(enabled)`; `encodeNet(…, { stateEquation })`.
- Rust: `SmtVerifier::state_equation(bool)`.
- Python: `verify(..., state_equation=True)`.
- Python inherits the Rust encoder, upper-bound rows included.

**Depends on:** [VER-001], [VER-004], [VER-005], [VER-006], [VER-007], [VER-013], [VER-015]

**Test derivation:** with the enumeration budget 0, the witness depth 0, the state-equation
phase ([VER-018]) and the firing-bound phase ([VER-019]) off, and the state-equation option of
this requirement on, since [VER-017], [VER-018], [VER-019] and [VER-025] would otherwise decide
these small untimed nets first: the fork-that-may-halt net of [VER-015] under `deadlockFree`
with `done` and `halt` as sinks: proven, certificate check passed, report names five counters;
with `halt` not a sink: violated with a confirmed replay ending in a halted marking. The
`unreachable{ra, rb, halt}` script has arity `7 + 5`, `(= m4p (+ 1 (- n0p) (- n1p)))` in each
of its five rules, and an upper bound rather than an equation for a consume-all place on a
net that has one."#
