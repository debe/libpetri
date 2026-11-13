import Libpetri.Spec.Text

requirement_text VER_025
  id "VER-025"
  title "Bounded Witness Phase"
  priority SHOULD
  kind B
  body r#"Directly before the flat fixpoint query, the verifier asks one `QF_LIA` query (phase `witness`,
through the transport of [VER-013]): does a run of at most `D` steps lead from `M0` to a
violating marking? A step is the firing of a flat transition or an **injection step** of
[VER-006]. A `sat` answer is decoded into a run, replayed under the exact abstract semantics
([VER-004]), trimmed and reported `Violated`, confirmed. Every other answer leaves the pipeline as
it was, and the fixpoint query runs. The phase finds the short counterexamples the earlier phases
cannot: [VER-018] does not search injections, [VER-019] refuses a net with injected environment
places, and neither runs on a net with match transitions.

The phase proves nothing. `unsat` at depth `D` says nothing about a run of `D + 1` steps, and a
net with injections or loops has no firing bound ([VER-019]) that would turn it into a proof. The
phase therefore adds `Violated` verdicts and never removes one: a replayed run is a run of the
step relation the fixpoint query over-approximates, so a sound fixpoint query could not have
proven the property.

**Where it runs.**

⟦s1|*If* the pipeline reaches the flat fixpoint query, the witness depth `D` is positive, and the net has no match transitions or the property is a reachability-safety property with a budget place declared, *then* the verifier *shall* run the phase directly before the fixpoint script is encoded.⟧

⟦s2|*While* the fixpoint query takes the name-coloured encoding ([NU-053]), the verifier *shall not* run the phase.⟧

⟦s3|*If* the net has match transitions and either the property is not a reachability-safety property or no budget place is declared, *then* the verifier *shall not* run the phase.⟧

The ν guard ([NU-050]) turns every verdict there into `Unknown`, so the query would be pure cost.

⟦s4|*If* the witness depth is 0, *then* the verifier *shall not* run the phase, and its verdict, route, report and scripts *shall* be those of the pipeline without the phase.⟧

⟦s5|*When* the verifier does not run the phase, it *shall* send no query for it and print no report line for it.⟧

⟦s6|*While* environment places are registered under `Ignore`, the phase *shall* run where it runs on any other flat net, with no injection step.⟧

A run that injects nothing is a run of the net, as the fixpoint query's `Violated` is there
([VER-006]). Under `Arrivals` the net is rewritten before any route runs and has no environment
places ([VER-006]), so the arrivals are ordinary transitions of the run.

⟦s7|*While* the counterexample replay of [VER-003] is disabled, the phase *shall* run where it runs with the replay enabled, and a run it reports *shall* still be confirmed.⟧

That option governs the replay after the fixpoint query only; the phase replays its own run.

⟦s8|*If* the property is a name-alignment property ([NU-055]), *then* the phase *shall* send no query and *shall* end inconclusive with the reason of [NU-055] that the property is decided only by the name-partition state-class graph.⟧

Route B decides such a property before the pipeline reaches the phase; the refusal keeps the
phase from reading a run of counts as a claim about names.

**The step relation.** The phase unrolls the flat net's steps:

- a **transition step** fires one flat transition under the exact abstract semantics of [VER-004]
  (consume-all and reset clearing, inhibitor and read guards) and keeps the environment post-caps
  of [VER-006];
- an **injection step** adds one token to one injected environment place that resolves in the
  flat net. Under `Bounded(k)` it is enabled only while the place holds fewer than `k` tokens,
  under `AlwaysAvailable` always. It has no post-cap: its guard already keeps the place at or
  below `k`.

These are the steps of the HORN encoding's transition and injection rules and of the
counterexample replay of [VER-003]. The phase's script and replay carry no P-invariant or
semiflow conjunct ([VER-005], [VER-007]), which the HORN rules add: a `Violated` from the phase
rests on the replay alone and does not depend on the invariants the pipeline computed.

The script caps every marking after `M0` and the replay caps each transition step's successor,
so the two accept the same runs only while `M0` is within the post-caps. The premises of
[VER-006] AC3, checked before any route runs, keep it there.

**The script.** `T` is the number of flat transitions and `J` the number of injected environment
places that resolve in the flat net, taken in place-index order, each with its bound under
`Bounded(k)` or none. Selector value `t < T` is transition `t` in net order, `T + j` is injection
`j`, and `T + J` is the idle step. Each step `i` of the `D` steps emits, in this order:

1. `(assert (and (>= s<i> 0) (<= s<i> <T+J>)))`;
2. when `i + 1 < D`, `(assert (=> (= s<i> <T+J>) (= s<i+1> <T+J>)))`;
3. one guard line per transition, as the bounded run of [VER-019] emits it;
4. one line per bounded injection `j`, in order, `(assert (=> (= s<i> <T+j>) (< <m> <k>)))`, with
   `<m>` the place's marking term at step `i` (the literal from `M0` at step 0); an injection
   without a bound emits no line;
5. per place, the `ite` chain of [VER-019], whose selectors are the transitions that touch the
   place, in net order, followed by `T + j` for each injection `j` into the place, reversed and
   nested as there, with the injection arm `(+ <m> 1)`;
6. the environment post-caps, as the bounded run of [VER-019] emits them.

The violation at the last marking and the trailer are those of [VER-019], and so is the first
line, `; Bounded run (VER-019): <D> steps of the exact step relation from M0, idle`.

⟦s9|*When* the phase runs, the verifier *shall* send this script, and every implementation *shall* emit it byte for byte the same for the same net, initial marking, property and options.⟧

⟦s10|*If* `J` is 0, *then* the script *shall* be byte-identical to the bounded run of [VER-019] at the same depth.⟧

**Decode, replay and trim.**

⟦s11|*When* the solver answers `sat`, the phase *shall* read the run from the model's selectors in step order up to the first idle step, taking a value in `[0, T)` as a transition step, a value in `[T, T + J)` as an injection step, and any other value, or a selector the model leaves undefined, as idle, and *shall* read no run from a model that defines no selector.⟧

⟦s12|*When* the phase replays a run, it *shall* fire each transition step under the exact abstract semantics with the environment post-caps, take each injection step only while its guard holds, and accept the run only when every step is enabled and the last marking violates the property.⟧

⟦s13|*When* a run replays, the phase *shall* trim it: it *shall* first cut the run to its violating prefix, then try the steps from the last to the first, replace the run by the violating prefix of the run without that step whenever one exists, and repeat such passes until one changes nothing.⟧

The violating prefix of a run is its shortest prefix that replays to a violating marking, the
empty prefix (`M0` itself) included; a run has none when no prefix replays to a violating
marking. A step after the violation need not be enabled for a prefix to count.

⟦s14|*When* the phase reports a run, it *shall* report the trimmed run, replayed, with each transition step labelled by its transition's name and each injection step by `inject(<place>)`.⟧

The solver pads a run to the full depth with steps that lead nowhere, and a padded run can pass a
violating marking and go on; the trim removes such steps. The trimmed run ends at the first
violating marking it reaches, and it is irredundant: no single step of it can be dropped so that
some prefix of the rest still replays to a violating marking. When `M0` violates, the trimmed run
is the empty one, whatever model the solver returned. It is not claimed to be a shortest run.
Which run is reported depends on the model the solver returns; for one model the trim fixes it,
so every implementation reports the same run for the same stub model.

**Budget.**

⟦s15|*When* the phase starts, it *shall* start a wall-clock budget of `max(1, floor(timeout_ms / 8))` milliseconds before it encodes the script, and the query *shall* receive what is left of it.⟧

The query passes the total-budget clamp of [VER-013] like every other process. The phase is the
step `witness phase` of that requirement's reason
`total verification budget of <N> ms exhausted during <phase>`. The trim polls the [VER-013]
deadline (the total budget and cancellation) before each candidate it replays; a stop found there
ends the verification as a stop anywhere else in the step `witness phase` does. Outside a
`verify()` call the poll does nothing.

**Report.**

⟦s16|*When* the phase runs, the report *shall* carry the line `  Bounded witness phase (VER-025):` followed by exactly one of the status lines below.⟧

- `    Status: a run of <n> steps reaches a violation (replayed; depth <D>)`, with `<n>` the
  number of steps of the trimmed run, written the same way for every `n` (`a run of 1 steps`
  included, and `0` exactly when `M0` violates)
- `    Status: no run of at most <D> steps reaches a violation (not a proof)`
- `    Status: inconclusive (<reason>)`

The inconclusive reasons are the transport's failure message ([VER-013]);
`z3 reported an error: <line>`, when the reply carries an `(error ...)` line other than
`model is not available`, with a verdict line or without; `time budget of <ms> ms exhausted`,
with `<ms>` the phase budget `max(1, floor(timeout_ms / 8))`, when that budget is spent before
the query starts; `the bounded run at depth <D> answered unknown`; `the bounded run did not
replay under the exact semantics`, when the model yields no run or its run does not replay; and
the reason of [NU-055] for a name-alignment property. A reply with such an error line counts as
a query that fails in the transport: an errored assertion drops out of the query, so its verdict
line would answer a different question. The phases of [VER-018] and [VER-019] read their replies
the same way. When the total budget or a cancellation of [VER-013] stops the verification during
the phase, the trim included, the status line is `    Status: inconclusive (<reason>)` with the
stop reason of [VER-013], and the `Unknown` result of that requirement follows it.

**Outcomes.**

⟦s17|*When* a run replays, the phase *shall* return `Violated` with the trimmed run as the counterexample, `counterexampleConfirmed` `true` and the route of the SMT pipeline ([VER-003]), and the result *shall* continue as the witness result of [VER-018] and [VER-019] does.⟧

That result is `=== RESULT ===`, `VIOLATED: <property>`,
`  Counterexample trace (replay order, <k> states):` with one line per marking,
`  Firing sequence: <a> -> <b>` unless the run is empty, and the untimed warning of [VER-003]
AC7. A run of 0 steps is the empty firing sequence of [VER-003] AC8: one marking, no transition
and no `Firing sequence` line.

⟦s18|*When* the phase returns `Violated` on a net with match transitions, the result *shall* pass the ν guard of [NU-050] as a name-blind verdict and carry the guard's note that the counterexample may be spurious.⟧

⟦s19|*When* the phase returns `Violated`, the counterexample-timing step of [VER-023] *shall* apply to the result as to every result of the pipeline.⟧

⟦s20|*If* the solver answers `unsat`, *then* the phase *shall* report that no run of at most `D` steps reaches a violation, and the pipeline *shall* continue to the fixpoint query.⟧

⟦s21|*If* the query fails in the transport, the solver answers `unknown`, the phase budget is spent or the run does not replay, *then* the phase *shall* report itself inconclusive with its reason, and the pipeline *shall* continue to the fixpoint query.⟧

⟦s22|The phase *shall not* report `Proven`, and *shall not* read an `unsat` answer as a proof.⟧

⟦s23|*If* the phase ends without a run, *then* the pipeline *shall* continue as it does without the phase, and the phase *shall* change no verdict except through the time it spends against the total budget of [VER-013].⟧

**Option.**

⟦s24|The witness depth *shall* default to 8 in every implementation.⟧

⟦s25|*When* the caller sets the witness depth to a positive `n`, the phase *shall* ask one query at depth `n`.⟧

⟦s26|*If* the caller sets a negative witness depth, *then* setting it *shall* fail with the argument error `witnessDepth must be non-negative, got <n>`.⟧

A language whose depth type has no negative value has no such error. Only depth 8 is cheap: a
larger depth costs up to the phase budget on every query that has no short run, each `Proven`
one included.

**Scripts and dump.**

⟦s27|*When* `LIBPETRI_SMT_DUMP` is set, the verifier *shall* keep the phase's script and reply under the phase name `witness` ([VER-013]).⟧

⟦s28|*When* the scripts are encoded without a solver ([VER-013] AC1), the result *shall* carry as its `witness` member the script `verify()` sends when it reaches the phase, present exactly when the encoding is flat, the witness depth is positive, and the net has no match transitions or the property is a reachability-safety property with a budget place declared, and absent otherwise.⟧

The member follows these gates alone: it is present whether or not an earlier phase, an earlier
route or a refusal (an unresolved property place among them) would end `verify()` before the
phase.

Measured on a 169-place net with 18 bounded injected places (z3 4.16.0): three violations need
runs of 7 steps with one or two injections. Depth 8 finds each in 0.15 to 0.25 s, where the
fixpoint query took 57 to 272 s, and every model is 8 steps long before the trim. A depth-8 query
with no run costs 0.15 to 0.32 s. Where no run exists, depth 12 costs up to 3.7 s and depth 16
up to 120 s, so a depth above 8 is opt-in.

**Acceptance Criteria:**
1. **An injection witness.** The fixture `env-bounded-witness-violated` (`envBoundedPair`:
   `t: one(e) → p1`, `e` an environment place under `Bounded(2)`, empty `M0`):
   `PlaceBound(p1, 1)` is `Violated` by the phase at the default depth, confirmed, with a run of
   4 steps, two `inject(e)` and two `t`. The report carries
   `    Status: a run of 4 steps reaches a violation (replayed; depth 8)`, and no fixpoint query
   is sent.
2. **A deeper violation falls through.** The fixture `env-bounded-deep-witness-violated` (the
   same net, `PlaceBound(p1, 4)`, whose shortest run has 10 steps): the report carries
   `    Status: no run of at most 8 steps reaches a violation (not a proof)` and the fixpoint
   query answers `Violated`. With the witness depth 10 the phase reports a run of 10 steps.
3. **Off.** With the witness depth 0, verdict, route, report and encoded scripts are those of
   the pipeline without the phase on every shared verdict-parity fixture; `encodeScripts()` has
   no `witness` script and the dump has no `witness` file.
4. **Name-coloured encoding.** A query that takes the name-coloured encoding ([NU-053]) carries
   no phase line and no `witness` script.
5. **ν gates.** On a net with match transitions the phase does not run for a quiescence property,
   nor for a reachability-safety property with no budget place declared. With a budget place, a
   reachability-safety property and an encoding that stays flat (modelled injection,
   [VER-006] AC7) it runs, and its `Violated` carries the ν guard's note.
6. **Name alignment.** Called directly with a name-alignment property, the phase sends no query
   and ends inconclusive with the reason of [NU-055].
7. **Each fall-through.** With a stub solver ([VER-013]), an `unsat` reply, an `unknown` reply, a
   transport failure, a spent phase budget and a `sat` model whose run does not replay each give
   their own status line, are followed by the fixpoint query, and never give `Proven`.
8. **Selector range.** A stub model whose selector is `T + j` decodes as injection `j`, not as
   idle; a selector of `T + J` or more, or a negative one, ends the run.
9. **Injection replay.** An injection step at a place that holds its bound does not replay; an
   injection without a bound always does; an injection step is labelled `inject(<place>)` and is
   checked against no post-cap.
10. **Trim.** A stub model on `envBoundedPair` padded with needless steps is reported as a run of
    4 steps for `PlaceBound(p1, 1)`; dropping any single step of a reported run makes it fail to
    replay.
11. **Initial violation.** When `M0` violates the property, with the enumeration route, [VER-018]
    and [VER-019] off, the phase reports `a run of 0 steps`, and the result is the empty firing
    sequence of [VER-003] AC8, confirmed. A stub model whose run leaves `M0` and comes back to a
    violating marking (`t1: p0 → p1`, `t2: p1 → p0`, `M0 = {p0: 2}`, `PlaceBound(p0, 1)`, the
    model `t1, t2`) is reported as the run of 0 steps too, and a stub model whose run passes a
    violating marking and goes on is reported cut at that marking.
12. **Replay option.** With the counterexample replay of [VER-003] disabled, the phase still runs
    and its `Violated` has `counterexampleConfirmed` `true`.
13. **Ignore.** Under `Ignore` with environment places registered the phase runs, and its script
    has no injection selector (`J = 0`).
14. **Script.** With `J = 0` the script is byte-identical to the bounded run of [VER-019] at the
    same depth, so the goldens of [VER-019] are unchanged. A golden `witness.smt2` for a net with
    a bounded injected place is the same in every implementation ([VER-013] AC1), and
    `LIBPETRI_SMT_DUMP` names the phase's files `NNN-witness`.
15. **Option.** The default depth is 8 in every implementation; a positive depth `n` sends one
    query at depth `n`; a negative depth fails with `witnessDepth must be non-negative, got -1`.

**Implementation notes:**
- Java: `org.libpetri.smt.z3.BoundedRun` (`encodeBoundedRun`, `decodeBoundedRun`, `replayRun`
  and the phase driver); `SmtVerifier.witnessDepth(int)`; `encodeScripts().witness()`.
- TypeScript: `verification/z3/bounded-run`; `SmtVerifier.witnessDepth(n)`;
  `encodeScripts().witness` (`string | null`). A non-integer depth fails with
  `witnessDepth must be an integer, got <n>`; the other languages' depth types hold integers
  only.
- Rust: behind the `z3` feature, `bounded_run`; `SmtVerifier::witness_depth(usize)`;
  `encode_scripts().witness` (`Option<String>`).
- Python: `verify(..., witness_depth=8)`; `encode_smt_scripts(..., witness_depth=8)["witness"]`.
  The negative-depth error names the option as Python spells it:
  `witness_depth must be non-negative, got <n>`.
- The goldens `spec/verification-fixtures/scripts/<id>/witness.smt2` are written by the Rust
  verifier (`scripts/smt-script-parity.py --update`), never by hand.

**Depends on:** [VER-001], [VER-003], [VER-004], [VER-006], [VER-013], [VER-018], [VER-019],
[VER-023], [NU-050], [NU-053], [NU-055]

**Test derivation:** the `envBoundedPair` fixtures at the default depth and at depth 10. One test
per gate and per outcome, each failing when only that gate or outcome is removed: the stub replies
of AC7 and AC8, and for AC5 the ν-net of [VER-006] AC7 under `Bounded(1)` with `Unreachable(merged)`
and with `DeadlockFree`. A test elsewhere that pins the fixpoint query's own result (its replay
and the replay's outcomes, the replay opt-out, its report lines, a dump listing) sets the witness
depth to 0, since the phase now answers first."#
