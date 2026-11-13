import Libpetri.Spec.Text

requirement_text VER_015
  id "VER-015"
  title "Linear State-Equation Bound"
  priority SHOULD
  kind F
  body r#"Before the fixpoint query, a **reachability-safety** property (`PlaceBound`,
`BranchPlaceBound`, `MutualExclusion`, `Unreachable`) is tried against the **state
equation**: every abstract-reachable marking satisfies `M = M0 + C·σ` for some firing count
vector `σ ≥ 0`, so for any weighting `y ≥ 0` with `y·C ≤ 0` on every transition,
`y·M ≤ y·M0` on every reachable marking — a *decreasing* conservation law, where the
P-invariants of [VER-005] are the equalities. ⟦s1|The violation of such a property is a lower
demand `d` on some places (`m_p ≥ 1` for each place of an `Unreachable` or a two-place
`MutualExclusion`, `m_p ≥ k+1` for a bound `k`); if `y·d > y·M0` for some such `y`, no
reachable marking meets the demand and the property is **proven structurally**, without IC3.⟧
⟦s2|A pairwise `MutualExclusion` over three or more places ([VER-002]) is a disjunction of
demands, one per pair: it is proven when every pair's demand is separated, each pair with its own query.⟧

The weighting for each demand is found by one `QF_LIA` query through the solver transport of [VER-013]
(phase `bound`): variables `y_p ≥ 0` per flat place, `y_p = 0` on every consume-all / reset
place (H1) and every injected environment place (H3'), one row `Σ_p C[p][t]·y_p ≤ 0` per flat
transition, and `Σ_p d_p·y_p ≥ 1 + Σ_p M0_p·y_p`. ⟦s3|A `sat` model is **re-checked in exact
integer arithmetic** (`y ≥ 0`, the zero weights, every row, the demand) before it is
believed; a model that fails the check is discarded.⟧ ⟦s4|`unsat`, `unknown` and any transport
failure hand over to the next phase of the dispatch.⟧ ⟦s5|The phase is skipped under `Ignore` with
environment places registered ([VER-006] AC4) and for the quiescence properties, whose
violation is not a linear demand.⟧ A ν-net's verdict receives the [NU-050] over-approximation
note like any other flat proof.

⟦s6|The verifier *shall* accept a weighting `y` for a demand `d` in the exact re-check only when `y_p ≥ 0` on every flat place, `y_p = 0` on every consume-all, reset and injected environment place, `Σ_p C[p][t]·y_p ≤ 0` for every flat transition `t`, and `Σ_p d_p·y_p ≥ 1 + Σ_p M0_p·y_p`, and *shall* accept every weighting that meets these conditions when every weight, and the sum of the absolute values of the terms of each of these sums, is at most `2^127 − 2`.⟧
⟦s7|A weighting whose sums overflow the implementation's integer arithmetic is rejected; that costs a proof and never makes one.⟧
⟦s8|In the re-check, `C[p][t]` is the number of tokens the flat transition `t` deposits on `p` minus the number its input on `p` requires, which for a consume-all input (`all`, `atLeast`) is its required minimum.⟧

⟦s9|The verifier *shall* take as the demands of a property one demand `m_p ≥ 1` on every listed place for `Unreachable`, one demand `m ≥ 1` on the entries at positions `i` and `j` for every pair of positions `i < j` of a `MutualExclusion` of two or more entries, in lexicographic order of `(i, j)`, and one demand `m_q ≥ k + 1` on the bounded place `q` for `PlaceBound` and `BranchPlaceBound` with bound `k`.⟧
⟦s10|A `MutualExclusion` of fewer than two entries is never violated ([VER-002]), so its demands are left to the implementation and every choice is sound.⟧

⟦s11|*When* the verifier runs the bound phase on a property, it *shall* return `Proven` exactly when, for every demand of the property, the query returned a `sat` model whose weighting the exact re-check accepts for that demand.⟧

⟦s12|The verifier *shall not* return `Violated` from the bound phase; every outcome of the phase other than `Proven` hands over to the next phase of the dispatch.⟧

⟦s13|*When* the bound phase proves the property, it *shall* return `Proven` with method `structural`, an empty counterexample trace and no `counterexampleConfirmed`.⟧

⟦s14|A property with a demand is a `PlaceBound`, `BranchPlaceBound`, `MutualExclusion` or `Unreachable` property; the name-alignment properties of [NU-055] have no demand.⟧
⟦s15|The verifier *shall not* run the bound phase on a property without a demand, while the phase is disabled, or under `Ignore` with environment places registered.⟧
⟦s16|The verifier *shall* run the bound phase at most once in one verification call.⟧
⟦s17|The verifier *shall* send the `bound` query of each demand at most once in one verification call.⟧
⟦s18|The verifier *shall not* run Route B ([VER-012]) after the bound phase, and *shall not* run the bound phase after the colour-slot bound of the coloured encoding ([NU-053]) or after the fixpoint query.⟧
⟦s19|*When* the bound phase is enabled and the verifier runs the colour-slot bound or the fixpoint query on a property with a demand, not under `Ignore` with environment places registered, it *shall* have run the bound phase earlier in the same call.⟧
⟦s20|*When* the bound phase is enabled and the verifier runs the enumeration of [VER-017] on a property with a demand, and the enumeration route applies to a net with no drained forward, it *shall* have run the bound phase earlier in the same call, and *shall not* run the bound phase after the enumeration.⟧
⟦s21|*When* the bound phase runs ahead of the enumeration and does not prove the property, the next phase the verifier runs *shall* be the enumeration.⟧
⟦s22|On a net where the enumeration route does not apply, or that has a drained forward, the verifier *shall not* run the bound phase before the enumeration.⟧

This closes the class of proofs IC3 does not find on pipeline-shaped nets: an *ordering*
argument — "both join slots armed means every upstream stage has run, so no halt is still
possible" — is a weighted count bound, which Spacer's lemma generalisation does not invent
over fifty variables but a linear solver finds in milliseconds. A net that answered `unknown`
after 300 s answers `proven` in under a second.

**Acceptance Criteria:**
1. When the bound query returns, for every demand of a reachability-safety property, a
   weighting that passes the exact re-check, the property is `Proven` with method `structural`,
   without a fixpoint query, and the report names the bound and the demand:
   `  Linear state-equation bound: 2*p0 + a + b <= 2; violation needs a + b + halt >= 3`.
2. A property whose violation the state equation admits (`unsat` from the query) proceeds to
   the fixpoint query with the report line `  Linear state-equation bound: none separates the violation`.
3. The bound is re-proven in exact integer arithmetic; a model that fails it is reported
   `inconclusive (solver model failed the exact re-check)` and the fixpoint query runs.
4. The first demand's `bound` script is byte-identical across implementations ([VER-013] AC1) and is
   reported by `encodeScripts()` (`null` for a quiescence property) whenever `verify()` would
   send it, including on a net with an exact name-coloured plan.
5. A genuine violation is never masked: the phase can only return `Proven`.
6. On a ν-net with an exact name-coloured plan, a reachability-safety property the bound
   separates is `Proven` (structural) without the coloured query; one it does not separate
   reaches the coloured query and gets the verdict it got before.
7. On an untimed net the enumeration route would take, a reachability-safety property the bound
   separates is `Proven` (structural) with no enumeration report line, whatever the class budget.
   A property it does not separate is decided by the enumeration as before, and the run sends the
   `bound` query at most once per demand. On a net with a drained forward the enumeration still decides first.

**On ν-nets the phase also runs before the name-coloured encoding ([NU-053]).** The state
equation is written over the flat, name-blind net, whose firing rule ignores which name a token
carries; every marking the ν semantics reaches is reachable there too, so a weighting that
separates the violation on the flat net separates it on the ν-net, and a structural `Proven` is
sound. A net with an exact coloured plan therefore tries the bound first, under the same
conditions as the flat path (enabled, a reachability-safety property, not `Ignore` with
environment places, the total budget and cancellation of [VER-013] respected), with the same
phase name. `Proven` returns as on the flat path — method `structural`, the lines of AC1 — and
keeps any ν-encoding notes already in the report; anything else hands over to the coloured
query, whose verdict and notes are unchanged. ⟦s23|The coloured plan is built only after the bound
fails to prove; nothing before it reads the plan.⟧ ⟦s24|Route B ([VER-012]) keeps its place in the
dispatch: the bound runs after it, never before.⟧ The colour-slot bound of the coloured encoding
counts coloured tokens rather than names, often two to four times the declared budget, and IC3 over that
many colour slots can time out on a bound the flat state equation proves in milliseconds. On six
PNID ν-nets (`research/net-metrics/validation/pnid/`), `placeBound(X, 1000)` under a budget of 2
went from `Unknown` after about 8 s to `Proven` in about 12 ms.

**On nets the enumeration route takes, the phase runs before it.** ⟦s25|When the enumeration route of
[VER-017] applies to a net with no ν-join (untimed, no environment places, a positive class
budget) and the net has no drained forward ([IO-014], [VER-001] AC5), the bound runs **before**
the enumeration, not after it.⟧ One query costs milliseconds; a graph that does not close costs the
whole class budget before the bound is reached. Measured on a 134-transition composed agent net
whose graph exceeds the budget: about 17 s per `placeBound` claim at a budget of 200 000 classes,
several minutes at 5 000 000, and under 0.1 s with the bound first. A bound that proves returns
as in AC1, with the report line of [VER-017] AC3 for the invariants it did not compute. ⟦s26|Anything
else falls through to the enumeration, and the fixpoint query later does not send the `bound`
query again.⟧ ⟦s27|When the solver cannot be started, the early bound sends no query and hands over
with a report line, and the enumeration runs without a solver, as it did before; the `Unknown` with route `Unavailable`
of [VER-013] comes only from the later phases.⟧ On every other net the phase keeps the slot above.

It is on by default and MAY be disabled (`linearBound(false)`) to force
the fixpoint path — for its certificate, or to exercise the engine itself.

**Implementation notes:**
- TypeScript: `verification/z3/linear-bound` (`encodeLinearBound`, `decodeLinearBound`,
  `checkLinearBoundExact`); `SmtVerifier.linearBound(enabled)`.
- Java: `org.libpetri.smt.z3.LinearBound`; `SmtVerifier.linearBound(boolean)`.
- Rust: `libpetri-verification` `linear_bound`; `SmtVerifier::linear_bound(bool)`.
- Python: `verify(..., linear_bound=True)`.
- ν-nets: the dispatcher runs the bound after Route B and before the coloured IC3 query; the
  goldens under `spec/verification-fixtures/scripts/` carry a `bound.smt2` for the coloured
  fixtures too.

**Depends on:** [VER-001], [VER-004], [VER-005], [VER-006], [VER-013], [NU-053]

**Test derivation:** a fork that may halt instead (`p0 → f → AND(a, b) | halt`, arms
`a → ra`, `b → rb`, join `ra + rb → done`): `unreachable{ra, rb, halt}` has no equality law
excluding it (the halt branch turns two units into one) and is proven by the bound
`2·p0 + a + b + 2·done + halt + ra + rb ≤ 2`; `mutualExclusion(ra, rb)` is reachable and hands
over to the fixpoint query, which reports `violated` with a confirmed replay."#
