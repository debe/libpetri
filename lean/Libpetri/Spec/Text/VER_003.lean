import Libpetri.Spec.Text

requirement_text VER_003
  id "VER-003"
  title "Verification Result"
  priority SHOULD
  kind B
  body r#"The verification result includes:

- **Verdict**: Proven (with proof method and optional inductive invariant), Violated (with counterexample), or Unknown (with reason)
- **Route**: which route decided the verdict — the SMT pipeline, bounded enumeration
  ([VER-017]), the ν name-partition graph ([VER-012]), a structural proof, or `Unavailable` when no route decided it. The graph
  routes compute no P-invariants, so a consumer reading the result's fields rather than its
  report MUST be able to tell "not computed on this route" from "the net has none". The rule
  is about the **empty** case only: an empty list off the SMT route means "not computed", while
  a non-empty list is real whatever the route reports — a run that found no usable solver still
  carries the invariants the pipeline computed before it gave up.
- **P-Invariants**: Place invariants discovered during analysis
- **Counterexample trace**: Sequence of markings and transitions leading to violation
- **Counterexample confirmed** (`counterexampleConfirmed`): whether the trace **replays in the
  untimed abstraction** ([VER-004]) as an ordered firing sequence from the initial marking to a
  violating marking. It is a claim about the untimed, value-blind model only: `true` does not
  mean the run is possible under the net's timing. On a net with match transitions the flat
  replay counts tokens and ignores names, so there `true` confirms a run of the name-blind
  untimed abstraction ([NU-050]), whether the fixpoint query or a pre-fixpoint phase
  ([VER-025]) found it. Absent where no replay applies.
- **Counterexample timing** (`counterexampleTiming`): what the counterexample means for the
  **timed** net. Absent unless the verdict is `Violated`; with `Violated`, exactly one of:
  - `UNTIMED_NET`: every transition is `immediate`, so timing cannot affect the trace.
  - `UNTIMED_ABSTRACTION`: the net is timed and the counterexample comes from the untimed
    abstraction, unchecked under timing: the timed check of [VER-023] was off or did not apply.
  - `TIMED_EXACT`: the deciding route already explores timed behaviour ([VER-012]'s Route B on a
    timed net), so the trace is a path of the graph Route B explored: the late graph by default,
    which keeps each earliest bound and drops each latest bound ([VER-002]), and the on-time graph
    under `assumeNoReaping`. Route B is priority-blind by default
    and honours priority only in part under conflict-only priority ([NU-052]), so the trace is
    timing-feasible **ignoring priority**, not necessarily a run the executor takes.
  - `TIMED_CONFIRMED`: the timed check ran and the timed state-class graph reaches a violating
    class. The trace has been replaced by that graph's shortest path ([VER-023]): a run of the
    **priority-blind** timed semantics, timing-feasible ignoring priority. A net that relies on
    priority to exclude the trace can get `TIMED_CONFIRMED` for a run the executor never takes.

  The timed positive claims are therefore weaker than "the executor can do this": the timed
  graphs expand every enabled transition whatever its priority. `SPURIOUS_UNDER_TIMING` is not
  affected: ignoring priority only adds runs, so a timed graph with no violating class also rules
  out every prioritized run.
  - `SPURIOUS_UNDER_TIMING`: the timed check ran, the timed graph closed, and no class violates:
    the property holds under timing. The verdict is still `Violated`, and the untimed trace is kept.
  - `TIMED_UNDECIDED`: the timed check ran but its graph was truncated at the class budget or
    stopped by the total budget ([VER-013]).

  "Timed" means at least one transition is not `immediate`, the test of [VER-017] condition 3.
  The field never changes a verdict: the untimed claim of [VER-004] is the contract.
- **Statistics**: Number of places, transitions, invariants found, elapsed time

⟦s1|The verifier *shall* return `Proven` with a proof method that is not empty, `Violated`, or `Unknown` with a reason that is not empty.⟧

⟦s2|The places a property of [VER-002] names are the places of `MutualExclusion`, `PlaceBound` and `Unreachable`, and the places and the `waivedBy` places of `QuiescentCount`; the sinks of `DeadlockFree` and `TerminatesAtSink` and the places of a conditional sink declaration ([VER-014]) are not among them, since a sink or marker the net does not hold is never marked and excuses nothing.⟧

⟦s3|*If* a property names a place that the net does not declare, the initial marking does not mark and no rewrite of the verified net adds (the in-flight places of [VER-004], the arrival sources of [VER-006]), *then* the verifier *shall* return `Unknown`, whatever any route would answer.⟧

⟦s4|*If* the verified net cannot be built (the in-flight split of [VER-004] refuses the net, or the premise check of `Bounded(k)` of [VER-006] fails), *then* the verifier *shall* return `Unknown`.⟧

A configuration error is not a verified net that cannot be built. A name that the `Arrivals` closure of [VER-006] would add and that the net already declares, or an `ArrivalsBetween` mode with `max < min`, is rejected with an exception (a panic in Rust) before any route runs, not with a verdict.

⟦s5|*When* the verdict is `Violated` and `counterexampleConfirmed` is `true`, the verifier *shall* report a trace that is a firing sequence of the verified net from the initial marking to a marking that violates the property.⟧

⟦s6|*When* the initial marking violates the property and the verdict is `Violated`, the verifier *shall* report the empty firing sequence, with `counterexampleConfirmed` not `false`, and `true` unless Route B or the name-coloured encoding of [NU-053] decided it.⟧

⟦s7|The verifier *shall* return `Proven` only when no marking reachable from the initial marking in the untimed abstraction of the verified net ([VER-004]) violates the property.⟧

On a ν-net, a `Proven` of Route B is the claim of [VER-012]: where its graph keeps a latest bound (under `assumeNoReaping`, or on a direct call on a timed net), the claim holds for an on-time executor whose actions take no time.

⟦s8|*When* the verifier reports a P-invariant, on any route, its weighted token sum *shall* equal its constant on every marking reachable from the initial marking in the untimed abstraction of the verified net.⟧

⟦s9|The verifier *shall* report a `counterexampleTiming` exactly when the verdict is `Violated`, and `UNTIMED_NET` exactly when every transition of the net is `immediate`.⟧

⟦s10|*When* the verdict is `Violated` and some transition of the net is not `immediate`, the verifier *shall* report `TIMED_EXACT` if Route B decided it, and `UNTIMED_ABSTRACTION` if another route decided it while the timed check of [VER-023] is off.⟧

⟦s11|*When* the verdict is `Proven` or `Violated`, the verifier *shall* name the route that decided it, which is not `Unavailable`.⟧

**Acceptance Criteria:**
1. Proven verdict includes the proof method.
2. Violated verdict includes a counterexample trace of markings and transitions. With
   `counterexampleConfirmed` `true` the trace is a firing sequence of the verified net from the
   initial marking to a violating marking; an unconfirmed trace may be empty.
3. Unknown verdict includes a reason (e.g., timeout, solver limit).
4. The result names the deciding route, so an empty invariant list from a graph route is
   distinguishable from a net that genuinely has none. A non-empty list is valid on every
   route, including one that ended without a solver.
5. A property naming a place the net does not declare **and the initial marking does not mark**
   is refused with `Unknown` **before any route runs**. A place the initial marking marks is a
   place of the verified net ([VER-001]), so a property may name it. Every route answers such a property vacuously and each in its own way — the
   flat encoder emits a violation term of `false`, which proves anything; a linear bound drops
   the unresolved conjunct and separates a strictly stronger demand; an enumeration finds no
   class marking a place that cannot be marked — so a refusal placed inside one route is not a
   refusal at all. It MUST precede the ν route, the structural routes and the encoders alike.
   A place that a rewrite of the verified net adds, such as `inflight:<t>` of [VER-004], resolves:
   the check reads the verified net.
6. `counterexampleTiming` is absent for `Proven` and `Unknown`. For `Violated` it is
   `UNTIMED_NET` on a net whose transitions are all `immediate`, whatever the route;
   `TIMED_EXACT` for a Route B verdict on a timed net; and `UNTIMED_ABSTRACTION` for any other
   route on a timed net while the timed check of [VER-023] is off.
7. A `Violated` reached by the fixpoint query on the flat encodings carries the report lines
   `  WARNING: This counterexample is in UNTIMED semantics.` and
   `  It may be spurious if timing constraints prevent this sequence.`, in every implementation.
8. **An initial violation is the empty trace.** When the initial marking itself violates the
   property, every route's `Violated` carries the **empty firing sequence**: a trace of one
   marking (the initial marking) and no transition, with `counterexampleConfirmed` `true`, or absent on
   Route B ([NU-055]). On the name-coloured encoding ([NU-053]) no replay applies:
   `counterexampleConfirmed` is absent and the trace need not list the initial marking. On the
   flat fixpoint query this holds whether or not the counterexample replay is enabled: the
   refutation proof has no step to decode, so the verifier evaluates the violation predicate
   on the initial marking directly and reports the report line `Counterexample: the initial
   marking violates the property (empty firing sequence)`. At an initial violation off the
   name-coloured encoding, a `Violated` with no trace at all is not conforming, since no one can
   replay it.

**Implementation notes:**
- Java: `SmtVerificationResult.counterexampleTiming()`, a nullable
  `SmtVerificationResult.CounterexampleTiming` enum with the constants above.
- TypeScript: `SmtVerificationResult.counterexampleTiming`, a string-literal union spelled like
  the result's `route` field (`'untimed-net'`, `'untimed-abstraction'`, `'timed-exact'`,
  `'timed-confirmed'`, `'spurious-under-timing'`, `'timed-undecided'`), `null` unless
  violated.
- Rust: `VerificationResult::counterexample_timing: Option<CounterexampleTiming>`, a
  `#[non_exhaustive]` enum (`UntimedNet`, `UntimedAbstraction`, `TimedExact`, `TimedConfirmed`,
  `SpuriousUnderTiming`, `TimedUndecided`).
- Python: `counterexample_timing`, a string spelled as in TypeScript, or `None`.

**Test derivation:** Verify a violated property; inspect counterexample trace for validity. A
violated property on an all-`immediate` net reports `UNTIMED_NET`; the same net with one
`delayed` transition, verified through the SMT pipeline, reports `UNTIMED_ABSTRACTION` and the
untimed warning."#
