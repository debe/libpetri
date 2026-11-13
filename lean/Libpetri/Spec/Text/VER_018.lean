import Libpetri.Spec.Text

requirement_text VER_018
  id "VER-018"
  title "State-Equation Phase with Refinement"
  priority SHOULD
  kind B
  body r#"Before the fixpoint query, the verifier asks one `QF_LIA` query (phase `state-equation`, through
the transport of [VER-013]): can a marking that satisfies the marking equation of [VER-016]
violate the property? The equation is `m = M0 + C·n` over firing counts `n ≥ 0`, with an upper
bound on a place a consume-all or reset arc clears and no row for an injected place; the
violation is encoded exactly as the error rule of [VER-001] encodes it. Every reachable marking
satisfies the equation for the counts of its run, so `unsat` proves the property. Unlike
[VER-015] the query asks for the violation directly, so it covers every property, quiescence
included.

⟦s1|*When* the state-equation query answers `unsat`, the phase *shall* end with a proof over the refinements it has added so far.⟧

⟦s2|*If* the state-equation query fails in the transport, answers `unknown`, gives a model that cannot be decoded, or the timeout runs out before its answer, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.⟧

A `sat` model is a **candidate**: the equation ignores firing order and the guards that impose
it, so the net need not reach the candidate. On a compiled workflow net the typical spurious
candidate is a join's skip transition, inhibited by the data place, firing after the data
arrived. Each candidate is settled, in this order, by:

1. **Witness.** A breadth-first search from `M0` under the exact abstract semantics ([VER-004]:
   consume-all and reset clearing, inhibitor and read guards) that fires each flat transition at
   most as often as the candidate's counts allow and stops at the first violating marking. A run
   found is reported `violated`, confirmed ([VER-003]).

   Injections are not searched. On a net with injected environment places a run found is still
   real: it injects nothing, and quiescence is judged with the relax-env enablement of [VER-006],
   so its marking is stuck whatever the environment does. A completed search there proves
   nothing, since an injected token could enable a run it never tried. The search is the phase's
   only source of witnesses there. A run that needs an injection is left to the bounded witness phase ([VER-025]), which unrolls injection
   steps and runs before the fixpoint query.
2. **Trap.** An initially marked trap the candidate leaves empty (Esparza, Ledesma-Garza,
   Majumdar, Meyer and Niksic, CAV 2014). A transition with a consume-all input or a reset arc on
   a trap place removes tokens from the trap, so it too must put one back. Adds
   `Σ_{q∈Q} m_q ≥ 1`.
3. **Inductive inequality.** A linear inequality `a·M ≤ b` that holds at `M0`, is kept by every
   step of the exact step relation, and excludes the candidate. One `QF_LIA` query (phase
   `invariant`) encodes Farkas consecution with the invariant's multiplier restricted to `{0, 1}`
   per transition (Colón, Sankaranarayanan and Sipma, CAV 2003): each step either keeps the bound
   or re-establishes it from its guard alone. The weights are integers of least total magnitude,
   re-checked in exact integer arithmetic before use. When none exists, the query is repeated
   with the marking equation as a premise of every step (one Farkas weighting of the equation per
   transition). Such a *relative* inequality is inductive only together with the equation, so the
   exact re-check cannot apply and only the certificate check re-proves it. On the join above the
   result is `hasdata ≤ ready_0 + ready_1`; on a queue bundled once a signal arrives,
   `N·out + q ≤ N`, relative to the equation's `q + budget ≤ N`.

⟦s3|*When* the state-equation query answers `sat`, the phase *shall* first run the witness search on the candidate, and *shall* return `Violated` with the run the search reports before it tries any refinement.⟧

⟦s4|The witness search *shall* fire each flat transition at most as often as the candidate's counts allow, under the exact abstract semantics of [VER-004] and with no injection step, and *shall* report a run only when every step is enabled and the last marking violates the property.⟧

⟦s5|A run the witness search reports *shall* be no longer than any other run within the counts that ends in a violating marking.⟧

⟦s6|The witness search *shall* report that no violating run exists only when it has completed, no run within the counts ends in a violating marking, and no environment place is declared for injection.⟧

⟦s7|*While* environment places are declared for injection, the phase *shall* still run the witness search, and the search *shall* report the same run it reports on the same net without injection.⟧

⟦s8|*If* a run within the candidate's counts ends in a violating marking, *then* the witness search *shall* report a run whenever its node budget is large enough.⟧

⟦s9|The trap search *shall* return a set `Q` of places of the flat net only when every flat transition that can take a token from `Q`, through an input arc, a consume-all input or a reset arc, also puts a token into `Q`, some place of `Q` is marked in `M0`, and the candidate leaves every place of `Q` empty.⟧

⟦s10|The trap search *shall* return a trap whenever some initially marked trap among the places of the flat net is empty in the candidate.⟧

⟦s11|The exact re-check *shall* accept an inequality `a·M ≤ b` only when it holds at `M0` and every firing and every injection step of the exact step relation keeps it.⟧

⟦s12|The exact re-check *shall* accept an inequality `a·M ≤ b` that holds at `M0`, gives no injected place a positive weight, and for which every flat transition that can fire, taken from the least marking its guard allows, passes the keep test or the restore test: the keep test, that the firing does not raise `a·M` and every place the firing clears without inhibiting has a weight of at least 0; the restore test, that the marking after the firing meets the bound and every place the firing neither clears nor inhibits has a weight of at most 0.⟧

⟦s13|*When* the witness search reports no run and the phase has added fewer refinements than the refinement limit, the phase *shall* settle the candidate in this order: with `Σ_{q∈Q} m_q ≥ 1` when the trap search returns a trap `Q`; otherwise with the inequality the `invariant` query returns, marked inductive, when the exact re-check accepts it and the candidate violates it; otherwise, when that query answers `unsat`, with the inequality the same query returns with the marking equation as a premise of every step, marked relative, when the candidate violates it.⟧

⟦s14|*When* the phase adds a refinement, it *shall* ask the state-equation query again with every refinement added so far.⟧

⟦s15|*If* no trap and no inequality settles the candidate, an inequality fails the exact re-check or holds at the candidate, or an `invariant` query fails in the transport, answers `unknown`, gives a model that cannot be decoded, or the timeout runs out before its answer, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.⟧

Every trap and inductive refinement holds in every reachable marking, and a relative one does too
when the solver's answer is right, since it is inductive together with the equation; so the query
is asked again and a later `unsat` is still a proof. The phase steps aside, leaving the pipeline unchanged, when nothing
settles a candidate, after 32 refinements, on a transport failure, or when the timeout runs out.

⟦s16|*If* the witness search reports no run on a candidate after the phase has added as many refinements as the refinement limit, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.⟧

⟦s17|The refinement limit *shall* be 32 in every implementation.⟧

⟦s18|The node budget of one witness search *shall* be 100 000 in every implementation.⟧

⟦s19|Each weight of an inductive or relative inequality *shall* have a magnitude of at most the larger of 8 and the number of tokens in `M0`.⟧

**Certificate.** A proof is the inductive invariant `SE(M, n) ∧ ⋀ refinements(M)` over the places
and one counter per flat transition. It goes as the `Reachable` interpretation to the certificate
check of [VER-016], which re-proves initiation, consecution and safety against the raw step
relation before `Proven` is reported with method `state-equation`. The report prints each
refinement and the result lists them as its discovered invariants. A failed or inconclusive check
withholds the `Proven`, says so in the report, and the pipeline continues. The Farkas dual of the
final `unsat` is not used as the certificate: for a quiescence property the violation is a
disjunction, and one inequality per disjunct is exponential in the net.

⟦s20|*While* the certificate check is enabled, the verifier *shall* return the phase's proof as `Proven` with method `state-equation` and neither a counterexample nor `counterexampleConfirmed` when the certificate check of [VER-016] passes on the invariant `SE(M, n) ∧ ⋀ refinements(M)`, and a failed or inconclusive check *shall* withhold the `Proven` and let the pipeline continue.⟧

⟦s21|*While* the certificate check is disabled, the verifier *shall* return the phase's proof as `Proven` with method `state-equation` and neither a counterexample nor `counterexampleConfirmed`, and the report *shall* carry `  Certificate check: not applicable (disabled)` in place of the check.⟧

⟦s22|*When* the phase returns `Violated`, the verifier *shall* return the markings and transitions of the run, in firing order, as the counterexample, with `counterexampleConfirmed` `true`.⟧

**Where it runs.** On the flat path, after [VER-015] and before the fixpoint query. Not on a net
with match transitions (the flat encoding is name-blind there; [VER-012] and [NU-053] are its
exact routes), not on the name-coloured encoding, and not under `Ignore` with environment places
registered ([VER-006]). On by default; MAY be disabled to force the fixpoint path.

⟦s23|The pipeline *shall* place the state-equation phase at one point, after the linear bound of [VER-015] and before the fixpoint query.⟧

⟦s24|*While* the phase is enabled, the pipeline *shall* run it on exactly the queries whose verified net has no match transition and that are not verified under `Ignore` with environment places registered ([VER-006]), unless an earlier step has decided the query or the run has stopped.⟧

⟦s25|*If* the phase is disabled, *then* the verifier *shall not* run it, and the verdicts and reports *shall* be those of the pipeline without the phase.⟧

⟦s26|Every implementation *shall* turn the phase on by default.⟧

Measured on 23 compiled workflow nets of 28–370 places under `DeadlockFree` with conditional
sinks ([VER-014]): 21 proven in 10–220 ms, four after one refinement, among them a 41-node chain
and a twenty-way switch that took 410 s and 277 s on the fixpoint path; one violated in 0.3 s; one
left to the next phase.

**Acceptance Criteria:**
1. A property whose violating markings the marking equation excludes is `Proven` with method
   `state-equation`, without a fixpoint query, and the report carries
   `  Certificate check: PASSED (init, consecution, safety)`.
2. The join-with-skip net below is proven with the report line
   `    Refinement (inductive): hasdata <= ready0 + ready1`, and the result's discovered
   invariants are the refinements as printed.
3. A candidate that a run within its counts realises is reported `violated`, with that run as the
   confirmed counterexample.
4. While the certificate check is enabled (the default), the phase's `Proven` is withheld unless
   the check passes. A genuine violation is never masked: the phase returns `Violated` only for a
   replayed run.
5. With the phase disabled, verdicts and reports are those of the pipeline without it.
6. `LIBPETRI_SMT_DUMP` records the phase's scripts under the phases `state-equation` and
   `invariant` ([VER-013]).
7. The phase's first query is exposed with the other encoded scripts and pinned as a golden of
   [VER-013] AC1, so no implementation's text for it can diverge silently.

**Implementation notes:**
- TypeScript: `verification/z3/state-equation-query`, `trap-refinement`, `invariant-synthesis`,
  `parikh-search`, `state-equation-phase`; `SmtVerifier.stateEquationPhase(enabled)`;
  `encodeScripts().stateEquation` (the first query).
- Rust: behind the `z3` feature, `state_equation_query`, `trap_refinement`,
  `invariant_synthesis`, `parikh_search`, `state_equation_phase`;
  `SmtVerifier::state_equation_phase(bool)`; `encode_scripts().state_equation`.
- Python: `verify(..., state_equation_phase=True)`; `encode_smt_scripts(...)["state_equation"]`,
  gated by `state_equation_phase=`.
- Java: `org.libpetri.smt.z3.StateEquationQuery`, `TrapRefinement`, `InvariantSynthesis`,
  `ParikhSearch`, `StateEquationPhase`; `SmtVerifier.stateEquationPhase(boolean)`;
  `encodeScripts().stateEquation()`.
- Naming: the pre-fixpoint phases are toggled by `linearBound` ([VER-015]),
  `stateEquationPhase` ([VER-018]) and `firingBound` ([VER-019]), one boolean each, spelled as
  the language spells its other toggles. The bounded witness phase ([VER-025]) is set by its
  depth, `witnessDepth`, where 0 turns it off. `stateEquationPhase` is not `stateEquation`
  ([VER-016]), which adds firing counters *inside* the fixpoint encoding and is off by default;
  an implementation SHOULD cross-reference the two wherever it documents either.

**Depends on:** [VER-001], [VER-003], [VER-004], [VER-006], [VER-013], [VER-015], [VER-016]

**Test derivation:** with the enumeration budget of [VER-017] at 0 and `assumeAtomicFiring`,
since [VER-017] would otherwise decide these small untimed nets first and the in-flight split of
[VER-004] would verify the arms of the join and `produce` of the queue in two steps: the join of a
compiled workflow net, `route: start → AND(aData, bEmpty) |
AND(aEmpty, bData)`, a data arm writing `hasdata` with its `ready`, an empty arm its `ready`
alone, `mergeStart: ready0 + ready1 + all(hasdata) → done`, `mergeSkip: ready0 + ready1,
inhibitor(hasdata) → skipped`, under `deadlockFree` with `done` and `skipped` as sinks: the first
candidate skips after the data arrived, one inductive inequality excludes it, and the proof passes
the certificate check. The queue-and-bundle net (`produce: budget → q` inhibited by `s` and by
`out`, `signal: src → s`, `bundle: all(q) + s → out`, `bundleEmpty: s, inhibitor(q) → out`,
`M0 = {budget: 3, src: 1}`) with `out` and `budget` as sinks: proven with `3*out + q <= 3`,
relative to the equation. With a `cancel: src → cancelled` alternative and `cancelled` a sink:
violated, with the run `produce, produce, produce, cancel`."#
