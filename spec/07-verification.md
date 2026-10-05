# 07 — Verification

This document specifies formal verification capabilities: SMT/IC3 safety proofs, state class graph analysis, and structural analysis.

---

## SMT Safety Verification

#### VER-001: SMT Verification Pipeline

**Priority:** SHOULD

The engine supports safety property verification using SMT solvers via the IC3/PDR (Property Directed Reachability) algorithm. The verification pipeline is:

1. **Flatten XOR** — expand XOR output branches into virtual transitions
2. **Structural pre-check** — attempt to prove properties via P-invariants alone
3. **P-invariant computation** — derive place invariants from the incidence matrix
4. **SMT encoding** — encode the Petri net as CHC (Constrained Horn Clauses)
5. **IC3 query** — invoke Z3 Spacer engine for reachability analysis
6. **Decode result** — extract verdict, counterexample, or inductive invariant

**Undeclared marked places are inert places.** An initial marking MAY put tokens on a place the
net does not declare; the executor retains them, inert ([CORE-072] AC3). Verification models the
same net the executor runs, so every place the initial marking names that the net does not
declare is added to the verified net as a place with **no arcs**, after the declared places, in
the order the marking lists them, so the place order is deterministic. Such a place keeps its
tokens forever: `DeadlockFree` counts it as stranded unless it is a declared sink, `PlaceBound`
counts its tokens, and it is its own trivial P-invariant. The rule applies before any route runs,
so every route sees the same net: the enumeration route ([VER-017]), Route B and the ν name layer
([VER-012]), Route A ([NU-053]), the structural checks ([VER-020]), the linear bound ([VER-015]),
the state equation ([VER-018]), the encoders and `encodeScripts()` ([VER-013]), open-net closure
([VER-022]), the environment rewrites ([VER-006]), the terminal rewrite ([EXEC-042]) and the
state-space cache key ([VER-017]). A net whose initial marking marks only declared places is
unaffected, byte for byte.

**Places are identified by name.** Verification identifies a place by its name, in every
implementation. An environment place ([VER-006]), a sink or conditional sink ([VER-002],
[VER-014]), a budget or carrier place ([NU-040], [NU-051]), a place a property names, a terminal
([EXEC-042]), a match key or relay target ([NU-020], [NU-054]) and a subnet port ([MOD-051])
each denote the net's place of that name, whichever object or value the caller used to name it.
In TypeScript, where `place('p')` called twice gives two objects of one place ([MOD-024]), no
route and no analysis may test membership by object identity: an environment place registered
through one object and named on an arc through another is still an environment place. Java's
place equality also compares the token type ([CORE-002]); a Java net whose places have distinct
names gets the same answer either way.

**Timeout outcomes are virtual transitions.** Step 1 expands a transition into one virtual
transition per way a firing can end: each output branch the action may write ([IO-016], one
token per place), in enumeration order, then the **timeout outcome** when the spec has a
`Timeout` and that outcome deposits differently from every branch. The timeout outcome is
what the executor deposits when the timeout fires ([IO-013] AC5, [IO-014]): the timeout
child's places only, one minted token each, and for a `ForwardInput(from, to)` one token in
`to` per token consumed from `from`, which is the required count of a `One` / `Exactly(n)` input.
Every analysis that fires a transition reads this one expansion: the flattener behind the
encoders, the linear bound ([VER-015]), the state equation ([VER-016], [VER-018]), the firing
bound ([VER-019]), the enumeration route ([VER-017]), Route B and the ν fragment ([VER-012]),
the name-coloured encoder ([NU-053]) and open-net closure ([VER-022]). A virtual transition is
named after its transition alone when there is one, and `<t>_b<i>` when there are several. A
forward from an `All` / `AtLeast` input deposits the drained batch, which depends on the
marking the firing drains: a **transfer**. The graph routes fire each class's marking, so
they count the drained batch exactly as the executor does: the enumeration route
([VER-017]), the timed state-class graph ([VER-010]) and Route B ([VER-012]) decide such a
net. No post vector holds it, so every route that reads the flat net (the structural
pre-check ([VER-020]), the P-invariants ([VER-005]), the linear bound ([VER-015]), the state
equation ([VER-016], [VER-018]), the firing bound ([VER-019]), the fixpoint query and Route A
([NU-053])) refuses it with `Unknown`. The refusal sits after the graph routes and before
the first linear one, so no exit of the pipeline bypasses it ([VER-003] AC5).

**Acceptance Criteria:**
1. Pipeline accepts a net, initial marking, and property.
2. Returns a verdict (Proven, Violated, or Unknown) with supporting evidence.
3. **Inert undeclared places.** For the net `t: c → d` with sink `d` and initial marking
   `{a: 1}`, where `a` is on no arc and not declared, `DeadlockFree` is `Violated` at every
   enumeration budget (0, 1 and the default), whichever route decides it, and
   `PlaceBound(a, 0)` is `Violated`. The verdict does not depend on the class budget or the
   route. The same net with no token on `a` gets the verdict and the scripts it got before.
4. **Timeout forwards deposit per consumed token.** For `t: exactly(2, a) → xor(c,
   timeout(50, forwardInput(a, b)))` from `{a: 2}`, the flat net has three virtual transitions
   `t_b0` (post `c`), `t_b1` (post `b`) and `t_b2` (post `2·b`), and `PlaceBound(b, 1)` is
   `Violated` with a one-step trace ending at `{b: 2}` on the linear bound ([VER-015]), the
   state-equation phase ([VER-018]), the fixpoint query and the enumeration route ([VER-017]).
   A spec whose timeout outcome equals one of its branches gets the virtual transitions, and
   the scripts, it got before.
5. **Drained forwards are decided by the graphs and refused by the linear routes.** The same
   net with `all(a)` or `atLeast(1, a)` in place of `exactly(2, a)`, from `{a: 2}`: at the
   default enumeration budget the enumeration route decides it: `PlaceBound(b, 1)` is
   `Violated` with a one-step trace ending at `{b: 2}` and `PlaceBound(b, 2)` is `Proven`.
   With the enumeration off (budget 0) it is `Unknown`, with route `Unavailable`, with the
   reason `transition 't' forwards its All/AtLeast input 'a' to 'b' on timeout, which
   deposits one token per token drained (IO-014), a marking-dependent count the flat
   encodings cannot express; refusing to certify on the linear routes (the state-space
   graphs decide it exactly: VER-017 enumeration, Route B)`.

**Implementation notes:**
- All implementations: full pipeline; the CHC system is emitted as SMT-LIB2 text and solved by
  the `z3` executable with `fp.engine=spacer` through the one solver transport of [VER-013].
- Rust: behind the `z3` feature. Python exposes the Rust pipeline via the PyO3 binding (wheel
  built with the `z3` feature).

**Depends on:** [CORE-072]
**Test derivation:** Simple mutual exclusion net; verify Proven verdict for mutual exclusion property. The AC3 net at enumeration budgets 0, 1 and the default, plus `PlaceBound(a, 0)`, and the same net without the stray token. The AC4 net on every route, and its flattened rows; the AC5 nets at budget 0 (refused) and the default (decided both ways).

---

#### VER-002: Safety Properties

**Priority:** SHOULD

**Quiescence.** Every property below that speaks of a quiescent marking reads it
**reap-aware**. A transition is *reapable* when its timing is `Deadline` or `Window`: an
executor that is late past its latest bound plus the tolerance reaps it ([TIME-013]), leaves
its input tokens where they are, and does not enable it again until one of its input places
changes. A late executor can therefore come to rest at a marking that still enables a
reapable transition (Lean `ReapingVsUntimed.reaping_refutes_ver004_ac3`). A marking is
**quiescent** when every transition it enables is reapable. On a net without a reapable
transition this is the plain reading, no transition enabled, and every script, verdict and
report is what it was before reaping was accounted for. "All transitions disabled" in the
error conditions below means "every transition that is not reapable is disabled".

Every route reads this one quiescence (AC7). The encoders leave a reapable
transition out of the quiescence clause of `Bad`, on the fixpoint query, the certificate
check, the [VER-018] and [VER-019] phases and Route A alike. A graph route treats an expanded
class as resting when every transition it enables is reapable (the ν name-partition graph of
[VER-012]: when every firing out of it is of a reapable transition).

Route B keeps timing ([NU-050]). A late executor also fires late: it reaps a `Deadline` or
`Window` transition, and it fires an `Exact` one after its bound, since [TIME-006] enforces
`Exact` softly. A graph under strong semantics forbids both, so it can prove a marking property
that a late executor violates (Lean `TimedScg/Retrodict.reaping_escapes_timed_graph`: `t1: p → a`
at `deadline(5)` and `t2: p → b` at `delayed(10)` never mark `b` on time, and a late executor
marks it). Route B therefore builds its graph, for **every** property, with the latest bound of
every `Deadline`, `Window` and `Exact` transition dropped and the earliest kept: `deadline(d)` is
read as `immediate()`, `window(e, l)` as `delayed(e)` and `exact(a)` as `delayed(a)` (Lean
`TimedScg/Late.relax`, sound by `late_run_sound`). It does not prune by priority ([NU-052]) on a
net with a reapable transition. A net timed only with `Immediate` and `Delayed` has no latest
bound to drop, and its graph, verdict and report do not change. The structural route of [VER-020] rules
out dead markings only, so it does not decide a net with a reapable transition. The open-net
routes of [VER-022] read the same quiescence.

An implementation MUST offer an opt-out, `assumeNoReaping` (`assume_no_reaping`), that
assumes an **on-time executor**: no transition is reaped and none fires after its latest
bound. It restores the plain quiescence and Route B's strong-semantics graph. The report of a
verdict reached under it on a net with a reapable transition, or on a ν-net with a `Deadline`,
`Window` or `Exact` transition, MUST say that the verdict assumes no transition is reaped and
an on-time executor, and the report of a quiescence verdict read reap-aware on a net with a
reapable transition MUST name the reapable transitions. When Route B drops a latest bound its
report MUST name the transitions whose bound it dropped. The marking properties (`PlaceBound`, `Unreachable`, `MutualExclusion`) do not
read quiescence, and their scripts do not depend on the option.

The following safety properties can be verified:

- **DeadlockFree**: no reachable quiescent marking exists where a token is stranded.
  Optionally, the verifier accepts **sink places**: expected terminal
  places where coming to rest is permitted. The error condition is: (all transitions
  disabled) ∧ (some marked place is not a declared sink). A quiescent marking violates
  exactly when it leaves a token outside the declared terminals — workflow-net proper
  completion. With no sinks declared this degenerates to: any quiescent marking still
  holding a token.
- **TerminatesAtSink**: every reachable quiescent marking has at least one declared sink
  marked. The error condition is: (all transitions disabled) ∧ (no sink place has a token).
  This asks the weaker question "did the net come to rest at a declared terminal at all",
  and says nothing about tokens left elsewhere. It is meaningful only when at least one
  sink is declared; with none, every quiescent marking violates vacuously.
- **MutualExclusion(p1, p2)**: places p1 and p2 never both have tokens simultaneously.
  Over a list of places the property is **pairwise**: violated iff some two entries of the
  list, at different positions, hold a token at once, which is the conjunction of
  `MutualExclusion(pi, pj)` over every pair. Every route and encoder of an implementation
  that accepts a list MUST read it this way (a disjunction of pairwise conjunctions, not "all
  marked" and not "at most one token in total"); a list of two is exactly
  `MutualExclusion(p1, p2)`, whose SMT term stays `(and (>= m_p1 1) (>= m_p2 1))`. A place
  listed twice pairs with itself, so `MutualExclusion(p, p)` is violated by any token in `p`;
  a list of fewer than two entries is never violated. An implementation MAY accept exactly two
  places (Java and TypeScript do; Rust and Python take a list). A linear route
  ([VER-015]) proves a list of three or more pair by pair.
- **PlaceBound(place, k)**: place never has more than k tokens
- **Unreachable(places)**: the given set of places is never all simultaneously non-empty
- **QuiescentCount(places, min, max, waivedBy)**: every reachable quiescent marking holds
  between `min` and `max` tokens across `places`; the lower bound is waived while any
  `waivedBy` place holds a token, the upper bound never. The error condition is: (all
  transitions disabled) ∧ ((Σ < min ∧ every `waivedBy` place empty) ∨ Σ > max). With a
  designed-terminal marker ([VER-014]) as waiver, a halted run need not refund its budget but
  never holds more than there is.

  `max` MAY be unbounded, represented however the implementation chooses (the representation
  is not observable). An unbounded `max` MUST contribute no upper-bound clause to the encoding
  and MUST render without an upper bound in the report, so implementations emit the same
  script. `min` MUST be a non-negative integer and `max` MUST be at least `min`; a construction
  breaking either MUST be rejected where it is constructed, as the language reports a caller's
  error, rather than yield a verdict. `min = 0` with `max` unbounded holds on every marking: an
  implementation MAY skip its query and SHOULD then report that it did, so a skipped clause is
  distinguishable from one that passed.

The two sink-sensitive properties are not ordered by strength; they **invert on the empty
marking**. A quiescent `{done:1, stuck:1}` with `done` a sink violates DeadlockFree (it
strands `stuck`) but satisfies TerminatesAtSink. The fully drained marking `{}` satisfies
DeadlockFree (nothing is stranded) but violates TerminatesAtSink (no sink was reached).
Neither subsumes the other, which is why both exist.

**Acceptance Criteria:**
1. Each property can be constructed and passed to the verifier.
2. Properties are verified against the net's reachable state space.
3. **DeadlockFree** reports a violation for a quiescent marking that marks a declared sink
   while also holding a token in a non-sink place.
4. **DeadlockFree** reports no violation for the empty quiescent marking, whether or not
   sinks are declared. A net that drains completely has stranded nothing.
5. **TerminatesAtSink** reports no violation for a quiescent marking that marks any
   declared sink, regardless of tokens held elsewhere.
6. **TerminatesAtSink** reports a violation for the empty quiescent marking when at least
   one sink is declared.
7. Every route that decides these properties decides the **same** predicate: the SMT route
   ([VER-001]) and the ν name-partition state-class graph route ([VER-012]) return the same
   verdict for every marking both can classify.
8. **QuiescentCount** reports a violation for a quiescent marking below `min` while no
   `waivedBy` place is marked, and for one above `max` whether or not one is. A marking below
   `min` with a `waivedBy` place marked is not a violation.
9. **QuiescentCount** with a negative or non-integral `min`, or a `max` below `min`, is
   rejected at construction. Two implementations given the same unbounded `max` emit the same
   script, whatever each stores for it.
10. **MutualExclusion is pairwise on every route.** On `t: s → a + b` with `c` declared and
    never marked, from `{s: 1}`, `MutualExclusion([c, a, b])` is `Violated` with the trace
    `[t]` on the enumeration route, the linear bound, the VER-018 / VER-019 phases and the
    fixpoint query alike; on the chain `s → a → b → c` from `{s: 1}`, `MutualExclusion([a, b,
    c])` is `Proven` on each. `MutualExclusion([c, c])` on the chain is `Violated`, and
    `MutualExclusion([c])` is `Proven`. (Implementations taking exactly two places pass the
    two-place cases.)
11. **Reap-quiescence.** On `p0 → t → p1` with `t` at `window(3, 5)`, one token on `p0` and
    `p1` a sink, `DeadlockFree` is `Violated` with the empty trace (the initial marking is
    quiescent: only the reapable `t` is enabled), on the [VER-018] phase and on the fixpoint
    query alone; `TerminatesAtSink` is `Violated` the same way. With `assumeNoReaping` both are
    `Proven` and the report says the verdict assumes no transition is reaped. The quiescence
    clause of the HORN script leaves `t` out; a `PlaceBound` script is the same either way.
12. **Shadowed reapable transition.** The same net with an `immediate` `u: p0 → p1` added is
    `DeadlockFree` `Proven`: wherever `t` is enabled so is `u`, which cannot be reaped.
13. **No structural proof across a reap.** The self-loop `t: a → a` at `window(3, 5)` from
    `{a: 1}` with the enumeration off is `DeadlockFree` `Violated` with the empty trace, never
    `Proven` by the structural route; with `assumeNoReaping` it is `Proven`.
14. **Route B.** The same-mint join of [VER-012] with the join at `window(50, 200)`, `merged` a
    sink, is `DeadlockFree` `Proven` when nothing is reapable and `Violated` after the fork when
    the join is: a late executor reaps it with both branches marked. Under `Conflict` priority
    semantics the result is the same.
15. **Route B reads a late executor.** Beside the same-mint join of [VER-012], `t1: p → a` at
    `deadline(5)`, `window(3, 5)` or `exact(5)` and `t2: p → b` at `delayed(10)`, from
    `{p: 1, source: 1}`: `Unreachable([b])` is `Violated` on Route B with a trace ending in
    `t2`, and the report names `t1` as a transition whose latest bound was dropped. With
    `assumeNoReaping` it is `Proven`, and the report says the verdict assumes an on-time
    executor. With `t1` at `delayed(5)` nothing is dropped, and the report is the same with or
    without the option.
16. **Every quiescence route.** The AC11 witness is `DeadlockFree` `Violated` on the [VER-019]
    firing bound with the [VER-018] phase off, and on the [VER-018] phase with the firing bound
    off. On Route A ([NU-053]), the same-mint join at `window(50, 200)` with the fork consuming
    one budget token, `merged` a sink and Route B capped at one class, is `DeadlockFree`
    `Violated`; with `assumeNoReaping` it is not `Violated`.

**Implementation notes:**
- QuiescentCount: TypeScript `quiescentCount(places, min, max, waivedBy)` (unbounded `max` is
  `Infinity`); Python `quiescent_count(places, min, max, waived_by=None)` (`math.inf`,
  `ValueError` on a negative or fractional bound or `max < min`); Rust
  `SmtProperty::quiescent_count(places, min, max, waived_by)` (`Option<usize>`, panics on
  `max < min`); Java `SmtProperty.quiescentCount(places, min, max, waivedBy)` (`OptionalInt`,
  `IllegalArgumentException` on a negative `min` or `max < min`). Java and Rust SHOULD use an
  absent optional rather than a sentinel, so no count can collide with it. No shared fixture
  pins it yet.

**Test derivation:** For each property type: construct net where property holds → Proven; construct net where property is violated → Violated. The AC10 nets on the four route setups of the conformance suite. AC11 and AC12 are the shared parity fixtures `reaping-window-deadlock-violated`, `reaping-window-no-reaping-proven` and `reaping-shadowed-deadlock-free`, scripts pinned.

**Depends on:** [TIME-013] (reapable transitions)

---

#### VER-003: Verification Result

**Priority:** SHOULD

The verification result includes:

- **Verdict**: Proven (with proof method and optional inductive invariant), Violated (with counterexample), or Unknown (with reason)
- **Route**: which route decided the verdict — the SMT pipeline, bounded enumeration
  ([VER-017]), the ν name-partition graph ([VER-012]), a structural proof, or none. The graph
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
  mean the run is possible under the net's timing. Absent where no replay applies.
- **Counterexample timing** (`counterexampleTiming`): what the counterexample means for the
  **timed** net. Absent unless the verdict is `Violated`; with `Violated`, exactly one of:
  - `UNTIMED_NET`: every transition is `immediate`, so timing cannot affect the trace.
  - `UNTIMED_ABSTRACTION`: the net is timed and the counterexample comes from the untimed
    abstraction, unchecked under timing: the timed check of [VER-023] was off or did not apply.
  - `TIMED_EXACT`: the deciding route already explores timed behaviour ([VER-012]'s Route B on a
    timed net), so the trace is a run of the timed semantics. Route B is priority-blind by default
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

**Acceptance Criteria:**
1. Proven verdict includes the proof method.
2. Violated verdict includes a counterexample trace of markings and transitions.
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
6. `counterexampleTiming` is absent for `Proven` and `Unknown`. For `Violated` it is
   `UNTIMED_NET` on a net whose transitions are all `immediate`, whatever the route;
   `TIMED_EXACT` for a Route B verdict on a timed net; and `UNTIMED_ABSTRACTION` for any other
   route on a timed net while the timed check of [VER-023] is off.
7. A `Violated` reached by the fixpoint query on the flat encodings carries the report lines
   `  WARNING: This counterexample is in UNTIMED semantics.` and
   `  It may be spurious if timing constraints prevent this sequence.`, in every implementation.
8. **An initial violation is the empty trace.** When the initial marking itself violates the
   property, every route's `Violated` carries the **empty firing sequence**: a trace of one
   marking (the initial marking) and no transition, with `counterexampleConfirmed` `true`. On
   the fixpoint query this holds whether or not the counterexample replay is enabled: the
   refutation proof has no step to decode, so the verifier evaluates the violation predicate
   on the initial marking directly and reports the report line `Counterexample: the initial
   marking violates the property (empty firing sequence)`. A `Violated` with no trace at all
   is not conforming, since no one can replay it.

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
untimed warning.

---

#### VER-004: Untimed Over-Approximation

**Priority:** SHOULD

SMT verification operates on untimed Petri net semantics (marking projection, integer token counts). Timing only restricts which firings happen: every timed firing is an untimed one, and a reap ([TIME-013]) changes no marking, so every marking a timed run visits is reachable in the untimed net (Lean `ReapingVsUntimed.timed_markings_reachable`). A proof of a property of the marking alone on the untimed net therefore holds for the timed net (`marking_properties_transfer`).

Timing does add one thing the untimed net lacks: a place to **rest**. A late executor reaps a `Deadline` or `Window` transition and stops at a marking that still enables it, a marking the untimed net does not count as quiescent (`reaping_refutes_ver004_ac3`: `p0 → t → p1`, `t = window(3, 5)`, rests at `{p0}` with the token stranded while the untimed `DeadlockFree` is `Proven`). The untimed abstraction MUST include this, so every quiescence property reads quiescence reap-aware ([VER-002]): a marking where every enabled transition is reapable counts as quiescent. With that reading, a proof on the untimed net is sound for every timed run, a late one included. `assumeNoReaping` restores the plain reading; a `Proven` under it holds only for an on-time executor, one that reaps no transition and fires none after its latest bound, and the report says so.

**Atomic firings and in-flight actions.** Every route reads a firing as one atomic step: its inputs leave and its outputs arrive in the same step. The executor does not fire that way. It consumes a firing's inputs when the action starts and deposits the outputs when the action completes ([EXEC-001] steps 5 and 1), and it fires other transitions in between. An asynchronous action keeps that gap open while it runs ([CONC-002]). A synchronous one keeps it open to the end of its firing pass, because a drain later in the same pass does not see the deposit ([EXEC-003] AC5). For monotone arcs the gap changes nothing: a run with `t` in flight can be reordered so that `t`'s deposit follows its start at once, because the steps in between only see more tokens in `t`'s output places, and a transition that needs tokens stays enabled and does the same. It does change something when a transition tests one of `t`'s output places **non-monotonically**: an inhibitor arc, a reset arc, or a draining input (`all`, `atLeast`). A terminal place ([EXEC-042]) counts too, since it inhibits every transition. With `t: one(p) → p` and an async action, and `u: one(q) + inhibitor(p) → bad`, `p` is never empty in any atomic run from `{p, q}`, so `Unreachable(bad)` was `Proven`; the executor fires `u` while `t` is in flight. With `start: one(req) + inhibitor(busy) → busy` and two requests, `PlaceBound(busy, 1)` was `Proven` too, and two guarded transitions sharing `busy` both start.

The untimed abstraction MUST therefore model the two-step firing for every transition `t` with an output place (in any branch, the `Timeout` branch included) that some transition tests non-monotonically. Such a `t` is **split** into:
- `t` itself, with every input, read, inhibitor and reset arc, its timing, priority and match spec, whose only output is a fresh place `inflight:<t>`, and
- `complete:<t>`, `immediate()`, with the one input `one(inflight:<t>)` and `t`'s output spec, in which a `forwardInput(from, to)` leaf deposits into `to`.

Two readings split more transitions, because the property or the priority semantics tests the gap too:
- A `QuiescentCount` with `min > 0` on a net with a terminal place it does not waive ([EXEC-042]) splits every transition that deposits into a counted place or a waiver place. A terminal stop abandons an action in flight, so the counted tokens it would deposit never arrive.
- Conflict priority on Route B ([NU-052]) splits every pruning transition `H` (one with strictly higher priority than another it shares a consumed input with) and every transition that deposits into an input or read place of `H`. A pruner pre-empts nothing while `inflight:<H>` is marked. If one of these transitions cannot be split (below), the verifier turns conflict priority off for that call, explores every enabled transition, and the report says which transition could not be split.

The completion step directly follows `t` in the transition order, and the in-flight places follow the net's own places in the order of the split transitions. Every other transition stays atomic, so a net with no such transition is verified, and scripted, exactly as before ([VER-013]). The split comes before the terminal rewrite of [EXEC-042], so a terminal also inhibits each completion step and excuses each in-flight place. A marked in-flight place never rests: its completion step is enabled, immediate and not reapable. A transition that models the environment rather than an action of the net (the arrivals of [VER-006], the environment of an open-net contract, [VER-022]) stays atomic. The completion step is itself one deposit and is never split again.

The split cannot express three cases, and a verifier MUST then answer `Unknown` on every route, naming the transition: a transition to split that is a ν-join, or that writes a coloured place (a match key, a relay target or a declared carrier), since its halves would lose the name the output carries ([NU-010], [NU-020], [NU-054]); a `Timeout` that forwards an `exactly(n)`, `all` or `atLeast` input, whose token count ([IO-014]) the completion step cannot see; and a net that already uses a name the split would add. An implementation MUST offer the opt-out `assumeAtomicFiring` (`assume_atomic_firing`), which reads every firing as one step; the report of a net the split would change then states the assumption, and conflict priority keeps pruning. Tokens an action publishes before it completes (`ctx.flush()`, Rust and Python) are not modelled for a split transition: its completion step deposits every output at once, and the report of every split verdict says so.

The split lets `t` start again while `inflight:<t>` is marked, which the Rust executor does and the Java and TypeScript executors never do ([CONC-002]). That is a sound over-approximation for all three. A `Violated` whose trace starts `t` while `inflight:<t>` is marked MUST say so in its report, naming `t`, since on Java and TypeScript such a trace may be a false alarm:

```
NOTE (CONC-002): the counterexample starts 'start' again while its earlier firing is still in flight (inflight:start marked). The Rust executor starts a transition again while its action runs; the Java and TypeScript executors never do, so on them this counterexample may be a false alarm.
```

Completeness does not hold: a counterexample in the untimed abstraction may be a run the timing forbids. Such a `Violated` stands, because the untimed claim is the contract; [VER-003]'s `counterexampleTiming` says what the counterexample means for the timed net, and the opt-in check of [VER-023] asks the timed state-class graph, without ever changing the verdict.

The encoding is additionally **value-blind**: it carries token counts, not token values. Every value-dependent choice — which XOR branch an action writes to, which token a correlated input picks — is therefore over-approximated as freely available, which is also sound for safety properties. (There is no value-predicate construct left to approximate: guards were removed in [IO-006].)

**ν-net carve-out.** The over-approximation is relaxed for the one *decidable*
predicate. A matched transition's name equality ([NU-020]) MAY be encoded
**exactly** as equality over an uninterpreted name sort (EUF) while token counts
stay in linear integer arithmetic — see [NU-050]. This removes spurious
counterexamples that would require two distinct correlation names to be equal,
without sacrificing soundness, and is the one place the untimed encoder reasons
about token *identity* rather than only token *counts*.

**Acceptance Criteria:**
1. Verification ignores timing constraints.
2. Verification is value-blind — value-dependent branch and correlation choices are
   over-approximated (except the [NU-020] name-equality carve-out of [NU-050], when
   implemented).
3. A Proven verdict on the untimed net implies the property holds for all timed executions,
   including those of an executor that runs late and reaps a transition ([TIME-013]), with
   quiescence read as [VER-002] defines it. Under `assumeNoReaping` a Proven verdict holds for
   the timed executions of an on-time executor, in which no transition is reaped and none
   fires after its latest bound, and the report states that assumption. On Route B
   ([VER-012]), which keeps the latest bounds under `assumeNoReaping`, a firing is also one
   instant step, so the verdict holds only for an executor whose actions take no time. The
   report says so, and a closed graph is called exact only for such an executor: with `t: a →
   p` at `deadline(20)` and a 150 ms action, `h: p + b → ok` at `deadline(20)` and `v: b → bad`
   at `delayed(60)`, beside a ν pair, `Unreachable(bad)` is `Proven` under `assumeNoReaping`
   with that label, `Violated` by default, and the executor marks `bad`.
4. A Proven verdict holds for the executor's runs with actions in flight: every transition
   whose output some transition tests non-monotonically is verified as its start and
   `complete:<name>`, and the report names the split transitions. From `{p, q, go}`, with
   `t: one(p) + one(go) → p` whose action is asynchronous, `u: one(q) + inhibitor(p) → r` makes
   `Unreachable(r)` `Violated`, and `u` with `reset(p)`, `all(p)` or `atLeast(2, p)` instead
   makes `MutualExclusion(p, r)` `Violated` (from two and three tokens on `p` for the two
   drains). The executors reach the same markings.
5. A net with no such transition produces byte-identical scripts, with or without
   `assumeAtomicFiring`.
6. A ν-join or coloured writer that needs the split, and a `Timeout` forward of more than one
   token that needs it, give `Unknown` on every route, naming the transition. Under
   `assumeAtomicFiring` the net is verified atomically and the report states the assumption.
   Under conflict priority a transition that cannot be split turns the pruning off instead:
   the verdict is the one without conflict priority, and the report names the transition.
7. With `t: one(a) → p` (async), `H: p + b → ok` at priority 10, `L: b + inhibitor(a) → bad` at
   priority 0, and a declared ν pair, from `{a, b}`, `Unreachable(bad)` under conflict priority
   is `Violated` and the report names `t` and `H` as split; the executors mark `bad`. Under
   `assumeAtomicFiring` it is `Proven` with the assumption in the report.
8. The guard net `start: one(req) + inhibitor(busy) → busy` from two requests gives a report
   with the CONC-002 note naming `start`; a net whose trace starts no transition while it is
   in flight has no such note.

**Test derivation:** Net with timing constraints; verify property on the untimed abstraction; verify same property holds in timed execution. For AC3, the [VER-002] AC11 witness: `DeadlockFree` is `Violated` at the initial marking, which is where a late executor rests; `Proven` only under `assumeNoReaping`, with the assumption in the report. For AC4, run each net on both executors with an action that sleeps, confirm the executor reaches the marking, then verify it on the enumeration route and on the SMT pipeline alone (`enumerationMaxClasses(0)`); `start: one(req) + inhibitor(busy) → busy` from two requests gives the trace `start, start, complete:start, complete:start`. Disable the split and confirm each test fails.

**Depends on:** [TIME-013], [EXEC-001], [EXEC-003], [EXEC-042], [CONC-002], [NU-052]

---

#### VER-005: P-Invariant Computation

**Priority:** SHOULD

The verifier computes place invariants (P-invariants) from the net's incidence matrix. A P-invariant is a weight vector `w` such that `w · M = constant` for all reachable markings M.

P-invariants provide structural proofs that do not require state enumeration.

**Acceptance Criteria:**
1. P-invariants are computed from the incidence matrix.
2. Each invariant satisfies `sum(weights[i] * marking[i]) = constant` for all reachable markings.
3. Invariants are reported in the verification result.

**Test derivation:** Net with known invariant (e.g., token conservation); verify invariant is discovered.

---

#### VER-006: Environment Analysis Mode

**Priority:** SHOULD

The verifier supports configurable treatment of environment places during analysis:

- **AlwaysAvailable** — environment places are assumed to always have tokens (unbounded external input)
- **Bounded(k)** — at most k tokens **resident** in each environment place at a time: injection
  refills the place up to k, forever, so a transition can take at most k tokens from it per
  firing but the total injected over a run is unbounded. This is the executor only when no
  transition deposits into an environment place and the initial marking holds at most k on each
  one (AC3)
- **Arrivals(k)** — at most k tokens injected into each environment place **in total**, over the
  whole run
- **Arrivals(min, max)** — between `min` and `max` tokens injected into each environment place in
  total: `min` of them are required, the rest optional. `Arrivals(k)` is `Arrivals(0, k)`, and
  `Arrivals(k, k)` is exactly `k`. A configuration with `min < 0` or `max < min` is rejected when
  the mode is built
- **Ignore** — environment places are not modeled

**Arrivals is a net rewrite, not an encoding.** Before any route runs, the verifier closes the
net with the construction [VER-022] uses for an arrival group with the same `min` and `max`
(`min = 0`, `max = k` for `Arrivals(k)`): environment place `P`, the `i`-th registered (from 0, in
registration order), gets a mandatory source place `env:arrivals[i]` holding `min` tokens with an
injection transition `env:arrive[i]:P`, and an optional source place `env:optional[i]` holding
`max − min` tokens with an injection transition `env:arrive?[i]:P` and a transition
`env:decline[i]` with no output that discards a token of it. Each injection transition moves one
token from its source onto `P`. A source whose count is 0 is omitted with its transitions, exactly
as the [VER-022] closure omits it, so `Arrivals(k)` has no mandatory source and `Arrivals(k, k)`
no optional one. `P` stays in the net as an ordinary place. A run may rest only once every
mandatory arrival has happened, and after any number of optional ones: "between min and max"
holds for quiescence properties as well as for safety, once the undelivered optional arrivals are
declined. In particular, under `Arrivals(k, k)` a quiescent marking has seen exactly `k` arrivals,
which is what exact accounting on an open subnet ("k inputs arrive ⇒ k outcomes at quiescence")
needs; under `Arrivals(k)` a run that declines is always a counterexample to it. The rewritten net has **no** environment places,
so every route applies to it as to any closed net: the enumeration route ([VER-017]), P-invariants
and quiescence mean what they mean on a closed net, and none of the `Ignore` refusals or
`AlwaysAvailable` vacuity notes below applies. Consequences a caller sees:

- Counterexample traces name the injection transitions (`env:arrive[i]:P`, `env:arrive?[i]:P`),
  each firing being one arrival, and the declines (`env:decline[i]`); the report says the net was
  closed under `Arrivals`, in the form `arrivals(k)` when `min = 0` and `arrivals(min..max)`
  otherwise, with the same wording in every implementation. P-invariants range over the rewritten
  net, sources included.
- A name the rewrite would add that the net already declares is rejected, as in [VER-022].
- The injected tokens carry names no analysis knows. An injection transition producing into a
  coloured place ([NU-051]) is **not** a mint: the ν routes ([NU-050] Route A, [VER-012] Route B)
  MUST NOT classify it as one, because two arrivals may carry one name and a mint would make them
  distinct, which can hide a reachable join (an unsound `Proven`). When an injected place is
  coloured, the ν routes decline with `Unknown` naming the place, exactly as AC8 does under
  `AlwaysAvailable`.

In `AlwaysAvailable` and `Bounded(k)` the verifier MUST **model external injection**: a
transition gated on an environment place becomes reachable (the SMT encoding emits an
injection rule that produces tokens into each environment place; under `Bounded(k)` injection
is capped). Equivalently, the environment place is treated as an inexhaustible (or k-capped)
external source rather than a column that starts empty and can only be consumed. Conservation
laws (P-invariants) derived from the closed net MUST NOT be applied to injected environment
places, since injection breaks closed-net conservation.

**The mirror-image vacuity.** Under `AlwaysAvailable` (and under `Bounded(k)` whenever the
demand is met) an environment-gated transition is enabled in *every* marking, so **no marking
is quiescent** and every quiescence property — `DeadlockFree`, `TerminatesAtSink`,
`QuiescentCount`, `JoinedOrDeadLettered` — is unviolatable. The `Proven` this yields is correct
and carries no information about the net: an open net with an always-available source never
comes to rest, so "no reachable quiescent marking strands a token" holds whatever the net does.
Unlike the `Ignore` case this is not refused, because the verdict is true; but an implementation
MUST report it, so a caller cannot read the empty claim as a guarantee about their workflow.

Because `Ignore` does not model injection, a safety property that holds **only** because
environment-gated transitions never fire is vacuous. When environment places are registered and
the mode does not model injection (`Ignore`), the verifier MUST NOT return `Proven` for such a
property — it reports `Unknown` (with a reason) instead of silently certifying.

This binds **every route that can return `Proven`**, not only the SMT encoding. An
implementation that decides some properties structurally — the name-partition state-class graph
of [NU-050], say — reaches a verdict without ever building an encoding, and a structural
exploration under `Ignore` treats an environment place as an ordinary place that simply starts
empty. The bound it certifies then holds for exactly the reason this requirement rejects. Only
`Proven` is refused: a `Violated` under `Ignore` is a real counterexample in a strictly smaller
reachable set, so it is a fortiori a counterexample in the injected one.

**Acceptance Criteria:**
1. Each mode is selectable via the verifier configuration.
2. `AlwaysAvailable` allows broader reachability (more states): for a net `env IN → T → OUT`,
   `PlaceBound(OUT, k)` is `Violated` for every finite k (OUT is reachable and unbounded).
3. `Bounded(k)` limits the state space: a transition requiring more than k tokens from an
   environment place per firing is never enabled. This holds against the executor only under two
   premises: no transition deposits into a registered environment place, and the initial marking
   holds at most k on each one. Every route relies on both. The flat encoding caps each successor
   at k on an environment place, the state-class graphs enable an environment input exactly when
   it demands at most k whatever the place holds, and the quiescence clause calls a demand above k
   permanently disabled. Outside the premises the executor can hold more than k there, so a
   `Proven` can miss a firing and a `Violated` can report a rest the executor never reaches.
   Before any route the verifier checks both premises. When one fails it returns `Unknown`, naming
   the environment place and the broken premise (the initial count, or the first depositing
   transition in code-point order, named as the caller wrote it: a completion step
   `complete:<t>` of the in-flight split ([VER-004]) is reported as `t`), and runs no route. For `t0: a → E`, `t1: exactly(2, E) → out`
   under `Bounded(1)` with `M0 = {a: 2}`, `PlaceBound(out, 0)` is `Unknown`, not `Proven`, on the
   flat path and on Route B. For `tQ1: exactly(2, E) → out`, `tQ2: out → out` with `M0 = {E: 2}`,
   `DeadlockFree` is `Unknown`, not `Violated`.
4. `Ignore` with registered environment places never returns `Proven` (reports `Unknown`).
5. AC4 holds on every route the implementation offers, including any structural or state-class
   route that returns a verdict without invoking the solver.
6. When injection makes some transition enabled in every marking, a quiescence property is
   reported as vacuously true: the verdict stands, and the report names the reason.
7. The name-coloured encoding of [NU-050] Route A has no injection rule, so under
   `AlwaysAvailable` or `Bounded(k)` with environment places it MUST NOT answer: the query
   takes the flat encoding, which models injection, and the report says so. For a ν-net
   `env source → fork (mint) → join → merged` with a declared budget, `Unreachable(merged)` is
   `Violated` under both modes.
8. The name-partition state-class graph of [NU-050] Route B models an environment place under
   `AlwaysAvailable` / `Bounded(k)` only as an inexhaustible (k-capped) input: never consumed,
   never injected into, carrying no injected names. Its count in a state class is therefore not
   the environment's. When a Route B verdict would depend on that count or name layer, Route B
   MUST return `Unknown` naming the environment place, never `Proven`: the property reads an
   environment place (a quiescence property only when quiescence is reachable), an inhibitor arc
   tests one, an environment place is coloured (a match key or carrier), or conflict priority
   prunes on an environment input two transitions consume. Otherwise its verdict stands, and a
   quiescence verdict carries the AC6 note. For the ν-net
   `env IN, slot → fork → A, B → join (match) → accepted → ack → slot` under `AlwaysAvailable`,
   `PlaceBound(IN, 0)` is `Unknown` and `Unreachable(accepted)` is `Violated`.
9. `Arrivals(k)` bounds the total: for `env IN → T → OUT`, `PlaceBound(OUT, k)` is `Proven` and
   `PlaceBound(OUT, k − 1)` is `Violated` with a trace of `k` `env:arrive?[0]:IN` firings
   interleaved with `T`, while under `Bounded(k)` both are `Violated`. `DeadlockFree` with `OUT` a
   sink is decided without the AC6 vacuity note.
10. Under `Arrivals(k)` with a coloured environment place (a match key), no ν route returns a
    verdict that treats the injection transition as a mint; the ν routes decline naming the place.
11. `Arrivals(min, max)` requires the mandatory arrivals: for `env IN → T → OUT` with `OUT` a sink,
    `QuiescentCount({OUT}, 2, 2)` is `Proven` under `Arrivals(2, 2)` and `Violated` under
    `Arrivals(2)`, with a trace through `env:decline[0]`. `Arrivals(k)` and `Arrivals(0, k)` give
    the same verdicts, traces and scripts. `min < 0` and `max < min` are rejected.

**Implementation notes:** Java `EnvironmentAnalysisMode.arrivals(int)` and
`arrivals(int min, int max)`; TypeScript `arrivals(maxTokens)` and `arrivals(min, max)` beside
`bounded(maxTokens)`; Rust `arrivals(max_tokens)` and a two-bound form beside `Bounded`, keeping
`arrivals(k)` source-compatible; Python `libpetri.arrivals(max_tokens)` and
`libpetri.arrivals(min_tokens, max_tokens)` beside `bounded(max_tokens)`, passed as
`environment_mode=`. Each implementation reuses its [VER-022] closure code for the rewrite rather
than restating it. `Arrivals(k)` is selectable on
the verifier and in `SubnetDef.verify` ([MOD-051]).

**Depends on:** [VER-022], [NU-050], [NU-051]

**Test derivation:** Same net (`env IN → T → OUT`) with different environment modes; verify
`AlwaysAvailable` → `Violated`, `Bounded(k)` gates by per-firing multiplicity, `Arrivals(k)` bounds
the total (AC9), `Arrivals(k, k)` requires every arrival (AC11), `Ignore` → `Unknown`.
For AC5, a ν-net with an environment place and no declared budget place (which routes to the
state-class graph rather than the solver) under `Ignore`: a bound that is unreachable only because
injection was not modelled reports `Unknown`, not `Proven`. For AC8, the witness net above under
`AlwaysAvailable` and `Bounded(1)`: a bound on the environment place reports `Unknown`, and the
reachable `accepted` is `Violated`. For the AC3 premises, under `Bounded(1)`: a net whose initial
marking holds 2 on the environment place, and a net with a transition that deposits into it, each
report `Unknown` naming the place, with and without a ν-join beside them (the flat path and Route
B), while the same net with 1 on the place and no deposit keeps its verdict.

---

#### VER-007: Invariant Strengthening from P-Semiflows

**Priority:** SHOULD

The verifier's encoders conjoin every accepted conservation law `y·M = y·M0` into the
transition-rule bodies of the CHC/IC3 encoding ([VER-004], [VER-005]). A law is accepted only
by the **exact gate**: `y·C = 0` against the incidence matrix and `y·M0 = c` are re-checked in
exact (overflow-checked) integer arithmetic, and `y` MUST carry zero weight on every place a
transition consumes with `all()` / `atLeast(n)` or clears with a reset arc, because the
encoder's fire relation is not linear there (Lean `Strengthening.lean`, hypotheses H1/H2;
injected environment places are covered by [VER-006], H3'). A law that fails the gate is
dropped from the encoding and listed in the report.

Two sources feed the gate. The null-space basis of [VER-005] is one basis of many: Gaussian
elimination returns mixed-sign rows (discarded as not semi-positive) and rows that fold a reset
place into a chain whose other combinations avoid it (dropped by the gate). On a net with a
handful of reset arcs this can lose every law of the chains those arcs touch, and IC3 then has
to rediscover each conservation law itself, which on a net of a hundred places it does not do
within any practical budget. The non-negative **P-semiflows** (`y ≥ 0`, `y·C = 0`, the minimal
laws of the net, computed by the Farkas / Colom-Silva enumeration) are the missing laws.

**The enumeration is expensive and MUST be skipped when nothing will read it.** The minimal
semiflows of a net are worst-case exponential in its branching: `k` independent diamonds in
series have `2^k` of them, measured at 2 048 for eleven and past the implementation's backstop
beyond thirteen. Computing them for a caller who did not enable this option is a large unforced
cost — 27 s of preprocessing on a 24-layer net before the solver sees anything — and on a wide
net an **uncatchable** one, since the heap it exhausts aborts the process rather than returning a
verdict. An implementation MUST compute semiflows only when the option is enabled. No other phase
reads them: the colour-slot bound of [NU-053] is a linear program over the incidence matrix, not
a semiflow search.

An implementation SHOULD therefore offer an option that unions the gate-validated semiflows
into the invariant list the encoders receive, and SHOULD offer an **`auto`** setting that
applies the condition above on the caller's behalf: compute and union the semiflows exactly
when the basis lost a law to the H1 guard, and skip them otherwise. That is decidable in one
pass, because the drops are known before the semiflows are needed. It is the setting to prefer
**for verification**: the two useful cases are told apart by a fact the pipeline already has, and
leaving that to the caller has a poor record — the option's unqualified reputation as "the
biggest lever" has led a consumer to enable it globally and then build a size ceiling around its
cost.

**What `auto` does not decide.** It answers whether the semiflows would add information to the
**encoding**, not whether they would appear in the result for a caller who *inspects* the
invariant list. A complete basis spans every conservation law, so a semiflow it spans constrains
nothing further and the solver gains nothing — but the basis is the *signed* null-space, and a
law it spans need not appear in it in **non-negative** form. Only the Farkas enumeration produces
that form. A caller looking for a law by its shape — "a non-negative law weighting the budget
place and every running place positively" — can therefore find nothing on a net that plainly has
such a law, because `auto` correctly skipped an enumeration that would have added no constraint.
Such a caller MUST request the union explicitly. The two claims are both true and easily
confused: `auto` is right about strengthening and says nothing about presentation. The option is **off by default** so that reports
stay byte-identical across releases. It is pure strengthening (Lean `Semiflow.lean`,
`semiflow_union_sound`: conjoining any list of gate-validated laws preserves the abstract
reachable set), so enabling it can never turn a `Violated` into a `Proven`.

**What enabling it does and does not promise.** It is a *strength* option, not a
*correctness* one, and on a branchy net the distinction is sharp. An implementation caps the
rows that survive each elimination round, so where the minimal set is exponential the semiflows
that reach the encoders are an **arbitrary truncation** of it: a proof that needs one particular
law can miss it even though the phase ran to completion and reported no drop. Enabling the
option therefore means "try harder", never "this answer is now trustworthy" — a `Proven` is
equally sound either way, and an `Unknown` with the option on is not evidence that no such law
exists. Implementations SHOULD report the truncation when it binds.

"The encoders" is both of them. The strengthened list reaches the **name-coloured** encoder of
[NU-050] exactly as it reaches the flat one — a coloured place's term becomes the sum over its
colour slots, its aggregate count, so one law stays one equation — and the option is at its most
decisive there: a coloured query already carries the
colour layer's cost, so the laws IC3 would otherwise have to rediscover are the ones it can
least afford to. The trigger is worth stating plainly, because it is the common shape rather
than an exotic one: **a net with even one `all()` / `atLeast(n)` or reset arc on a busy place
loses every basis row whose support touches that place**, so the encoder runs on a deficient
invariant set with nothing in the report to say a law is missing beyond the `Dropped` lines.
Draining an input queue is the everyday case. The option does not rescue those rows — semiflows
face the same gate and a law whose support touches the place is dropped either way. It supplies
the *other* laws: the minimal ones that avoid the place entirely, which elimination had folded
away.

**Acceptance Criteria:**
1. Semiflows are re-validated by the same exact gate as the basis rows before use; a semiflow
   that fails it is dropped with a `Dropped semiflow:` report line and is never encoded.
2. With the option disabled (the default) the semiflows do not reach the encoders, are not
   computed at all, and the report is byte-identical to a build without the feature.
3. Under `auto` the report says which way it went and why, the union happens only when a law
   was dropped, and the verdict never differs from whichever explicit setting `auto` chose. The
   report's "off" wording MUST say that the skipped semiflows add no *constraint*, not that they
   would add nothing, so a caller reading the invariant list is not misled about their absence.
4. With the option enabled the report carries `  Semiflows encoded as invariants: N`, where
   `N` counts the semiflows added after deduplication against the basis rows, and the result's
   invariant count and list include them.
5. `Proven` is never weakened: where the certificate check applies (the flat encoding) it
   receives the strengthened list and re-proves every law's initiation and consecution against
   the unstrengthened step relation before the verdict is reported.
6. A genuine violation stays `Violated` with the option enabled.
7. The strengthened list reaches the name-coloured encoder ([NU-050]) as well as the flat one:
   there is a net on the coloured path whose encoded script differs between the option's two
   states. (Not every such net — a semiflow already present in the basis dedups away, and AC3
   admits `N = 0`, in which case the two scripts are identical.) This is about what the encoder
   receives, not about certification — AC4's certificate check is flat-path only, and a coloured
   `Proven` reports `  Certificate check: not applicable (name-coloured encoding)`.

**Implementation notes:**
- Java: `SmtVerifier.semiflowInvariants(boolean)`.
- TypeScript: `SmtVerifier.semiflowInvariants(enabled | 'auto')`.
- Rust: `SmtVerifier::semiflow_invariants(bool)`.
- Python: `verify(..., semiflow_invariants=True)`.

**Depends on:** [VER-004], [VER-005], [VER-006], [NU-050], [NU-053]

**Test derivation:** a budgeted work loop with one reset arc on a side place, whose null-space
basis folds the reset place into the loop's law: a `placeBound` on the loop is proven only with
the option; a bound the loop genuinely exceeds stays `Violated` with it. For AC6, the same loop
beside a budget-declared ν-net, with the reset arc on the uncoloured half (the coloured encoder
refuses a reset on a coloured place, and the net would silently fall back to the flat encoding):
the encoded script must report itself coloured and must differ between the option's two states.

---

#### VER-013: Solver Transport

**Priority:** SHOULD

The SMT pipeline ([VER-001]) reaches the solver through one transport in every implementation:
each query is one `z3` process. The process is started with the argument list

```
z3 -smt2 -in -t:<timeout_ms> -T:<ceil((timeout_ms + 1000) / 1000)>
```

plus `fp.engine=spacer` for the HORN query, is fed the complete SMT-LIB2 script on stdin in a
single write, and then has its stdin closed so it sees end-of-file. Both output streams are
drained concurrently from the start, so a reply larger than a pipe buffer cannot stall the
solver, and a wall-clock watchdog at `timeout_ms + 2000` milliseconds kills a process that
ignored both timeouts. The process is killed and reaped on every exit path. No solver state
survives a query: concurrent verifications in one host process are independent, and a solver
crash is a verdict, never a crashed host. The timeout is per invocation; the HORN query, the
certificate script and its detail re-run each receive the full budget.

**Total budget.** Because the timeout is per invocation, one `verify()` can run for several times
it: the bound query ([VER-015]), the state-equation phase shared across its refinements
([VER-018]) and its certificate check and detail re-run, the firing-bound phase at half the
timeout ([VER-019]), the HORN query and its certificate check and detail re-run add up to about
7.5 timeouts, plus 2 s of watchdog slack per process, plus the solver-free work (the enumeration
route [VER-017], Route B [VER-012], the timed check [VER-023], the siphon and trap search
[VER-020], Farkas, the colour-slot simplex of [NU-053]), which no timeout bounds. An
implementation SHOULD therefore offer an
optional **total budget**, a wall-clock limit on the whole call. It is off by default, and with
it unset behaviour and reports are byte-identical to the above. When it is set:

- The deadline starts when `verify()` is entered, before the terminal rewrite of [EXEC-042], so
  all of the call's work counts against it.
- Every `z3` process receives `min(its normal budget, remaining)` as its `timeout_ms`, and derives
  `-t`, `-T` and the watchdog from that clamped value by the formulas above. When nothing
  remains, no process is started.
- The solver-free graph builds (the enumeration route, Route B, the timed check) and the long
  solver-free loops (siphon and trap search, Farkas, the colour-slot simplex) poll the deadline,
  cheaply (every so many classes or iterations), and stop when it has passed. The colour-slot
  simplex runs as its own step, `colour-slot bound`, entered once every other check of the
  coloured plan has passed, and polls before every pivot.
- When the deadline passes before a verdict is reached, the verdict is `Unknown` with the reason
  `total verification budget of <N> ms exhausted during <phase>`, `<phase>` naming the step
  that was running when the budget ran out, and the report carries the same line. A poll made
  on entering a step checks the deadline **before** it records the new step, so an exhaustion
  found there blames the step that just ended, not the one about to start; every implementation
  names the same step for the same stop. A verdict reached before the deadline stands.
- A graph build the deadline stopped is not a class-budget truncation. It MUST NOT be recorded in
  a state-space cache ([VER-017]) as a truncation at the class budget: it leaves the cache entry
  as it found it, like a build that fails.
- The HORN query no longer keeps its full budget. Without a total budget, the fixpoint query gets
  the whole timeout however long the pre-fixpoint phases of [VER-018] and [VER-019] took; under a
  total budget it gets what they left.

The per-call timeout keeps its meaning above: the budget of one process. The total budget
applies to one `verify()` call. `SubnetDef.verify` ([MOD-051]) and open-net verification
([VER-022]) reach it only through their per-query configuration hooks, so each of their queries
gets its own budget; neither has a budget across its queries.

**Cancellation.** An implementation SHOULD let the caller stop a running `verify()` from outside
it. Cancellation is not a second mechanism: it shares the total budget's stop. The deadline
becomes "deadline passed **or** cancelled", and everything that polls the deadline (the clamp
before each `z3` process, the graph builds, the long solver-free loops) sees cancellation at the
same points, whether or not a total budget is set. Beyond that:

- A `z3` process running when cancellation arrives is killed at once and reaped, not left to its
  timeout or watchdog. A cancelled call starts no further process.
- The verdict is `Unknown` with the reason `verification cancelled during <phase>`, `<phase>` named
  as for the total budget, and the report carries the same line. There is no new verdict. A call
  cancelled before it starts returns this at once. A verdict reached before cancellation stands.
- When a total budget is also set, whichever stop comes first names the reason.
- A graph build stopped by cancellation is not a class-budget truncation and leaves a state-space
  cache as it found it, as for the total budget.
- `SubnetDef.verify` ([MOD-051]) and open-net verification ([VER-022]) honour cancellation too,
  including the solver queries open-net verification runs outside `verify()` (its termination
  ranking): a cancelled call starts no further query.

The mechanism follows each language's idiom:

- **TypeScript**: an `AbortSignal`, passed with `SmtVerifier.signal(signal)` (also reachable from
  the `configure` hook of `SubnetDef.verify` and from `OpenNetOptions`). `runZ3Text` takes the signal
  and kills the process with `SIGKILL` when it aborts.
- **Rust**: `CancelToken` (`Clone`, `Send + Sync`, a shared atomic flag; `new()`, `cancel()`,
  `is_cancelled()`), passed with `SmtVerifier::cancel_token(&CancelToken)`. The watchdog's poll
  loop in `Z3Solver::run` checks it and kills and reaps the process.
- **Python**: `libpetri.CancelToken` wraps the Rust token; `verify(..., cancel=token)` and
  `verify_subnet(..., cancel=token)`. The verification runs with the GIL released, so `cancel()`
  from another thread, or from an asyncio task while the call runs in an executor, takes effect.
- **Java**: thread interruption, Java's own cancellation idiom; there is no token. Interrupting the
  thread that runs `verify()` cancels it: the running `z3` process is destroyed, the remaining
  phases are skipped, and the result is the `Unknown` above. The graph builds and loops read the
  thread's interrupt status at their deadline polls without clearing it, and the interrupt flag is
  set again when `verify()` returns, so the caller still sees it.

The executable is `z3` on `PATH` unless the environment variable `LIBPETRI_Z3` names another
one. It is probed once per verification with `--version` and refused below **4.8.0**. Setting
`LIBPETRI_SMT_DUMP` to a directory keeps every script and reply there as `NNN-<phase>.smt2`,
`NNN-<phase>.out` and, when stderr was not empty, `NNN-<phase>.err`, with `NNN` a zero-padded
counter and the phase one of `bound` ([VER-015]), `state-equation`, `invariant` ([VER-018]),
`ranking`, `bmc` ([VER-019]), `horn`, `horn-coloured`, `certificate`, `certificate-detail`.

**Reply classification.** The verdict is the first stdout line equal to `sat`, `unsat` or
`unknown`, wherever it appears: a build may print a warning first, and the HORN script's paired
`(get-proof)` / `(get-model)` always yields one `(error …)` line. Under the HORN query
`(assert (not Error))`, `sat` is `Proven` and `unsat` is `Violated`. Without a verdict line the
`Unknown` reason is, in this order: the `timeout` line printed by the `-T` backstop; the watchdog
kill; the first `(error …)` line on stdout, then on stderr; any other stderr text; the unexpected
stdout itself. The certificate script requires exactly three positional answers; an `(error …)`
on either stream, a `timeout` line, a kill or a non-zero exit makes the check inconclusive and
withholds `Proven`.

**Script determinism.** For the same net, initial marking, property and options every
implementation MUST emit byte-identical HORN and certificate scripts: places in Unicode
code-point order of their names; flat transitions in net order with XOR branches in enumeration
order ([IO-016]); environment-injection rules, sink conjuncts and the property's place lists in
place-index order; invariants in `(support, weights, constant)` order after the [VER-007] union;
lines joined with `\n`; no rule names. The certificate is the `(define-fun …)` block of the
`(get-model)` reply pasted verbatim, and a counterexample is the set of ground `Reachable` facts
in the `(get-proof)` reply, ordered only by the replay ([VER-003]).

**Name order.** Every ordering of place or transition names that reaches a script, a flat
index, a report, a witness or a violation list MUST compare names by Unicode code point, never
by host locale or UTF-16 code unit: the flat place index above, the canonical clock order of a
state class ([VER-010]), and the markings and violation lists of an open-net report
([VER-022]). Locale order varies by host; UTF-16 order (JavaScript `<`, Java
`String.compareTo`) differs from code-point order (Rust `str`) wherever a character above
U+FFFF meets one in U+E000–U+FFFF.

**Acceptance Criteria:**
1. The same net, marking, property and options produce byte-identical HORN and certificate
   scripts in every implementation (the golden scripts under
   `spec/verification-fixtures/scripts/`).
2. A missing executable yields `Unknown` with a reason naming the command tried and
   `LIBPETRI_Z3`; no exception escapes and the host process survives.
3. An executable below 4.8.0, or one whose `--version` reports no version, yields `Unknown`
   naming both versions (or the reply).
4. A `timeout` reply, an `(error …)` on either stream, a non-zero exit and a process that never
   exits each yield `Unknown` with a distinct reason and leave no solver process behind.
5. A reply preceded by a banner of arbitrary size on either stream is classified by its verdict
   line.
6. The report carries `  Solver: z3 <version>` in its solver phase, or
   `  Solver: z3 unavailable (<reason>)` followed by the implementation's `UNKNOWN` result
   line naming the same reason when no solver resolved.
7. Sorted from any starting order, the names `""`, `Z`, `a`, `ab`, `Ä` (U+00C4), `中` (U+4E2D),
   U+E000, `Ａ` (U+FF21), U+1D400 and U+1F600 come out in exactly that order in every
   implementation. A UTF-16 code-unit sort puts U+1D400 and U+1F600 before U+E000.
8. With no total budget set, verdicts, reports and solver arguments are those of the
   requirement without it.
9. With a total budget of `N` ms, `verify()` returns within `N` ms plus one process's watchdog
   slack (2 s) and one polling interval; a query it cannot finish in time is `Unknown` with the reason
   `total verification budget of N ms exhausted during <phase>`, and no `z3` process starts
   once the budget is spent.
10. An enumeration build stopped by the total budget leaves a state-space cache as it found it:
    a later query with more time and the same class budget builds rather than declines.
11. Cancelling a verification while a `z3` process runs kills that process at once: the call
    returns well before the process's timeout, with verdict `Unknown` and the reason
    `verification cancelled during <phase>`, and starts no further process. A call cancelled
    before it starts returns the same `Unknown` without starting one. In Java the cancellation is
    an interrupt of the verifying thread, and the thread's interrupt flag is set when `verify()`
    returns.
12. Cancellation during an enumeration or Route B build stops the build at its next deadline poll
    with the same reason, and leaves a state-space cache as it found it.

**Implementation notes:**
- Rust: `libpetri-verification` `z3_process` (`Z3Solver::resolve` / `Z3Solver::run`);
  stub-solver scenarios in `tests/stub_z3.rs`, CI gate in `tests/z3_gate.rs`.
- Python: inherits the Rust transport; `libpetri.z3_available()` reports whether a usable
  executable resolves (`HAS_Z3` is the compile feature only).
- Java: `org.libpetri.smt.z3.Z3Process` / `Z3Solver`; `SmtVerifier.z3Available()`.
- TypeScript: `verification/z3/z3-process` (`resolveZ3` / `runZ3Text`); `z3Available()`.
  Names are ordered by `compareCodePoints` (`core/internal/code-point-order`, ICU's code-point
  fix-up on the first differing UTF-16 unit pair).
- Total budget: Java `SmtVerifier.totalBudget(Duration)`, TypeScript
  `SmtVerifier.totalBudget(ms: number)`, Rust `SmtVerifier::total_budget(ms: u64)`, Python
  `verify(..., total_budget_ms=None)`. Every process passes through one choke point per
  implementation (Java `Z3Solver.run`, TypeScript `runZ3Text`, Rust `Z3Solver::run`), which is
  where the clamp applies. Java's `Z3Solver` is a public record and keeps its components; the
  deadline travels beside it.
- AC1 is checked without a solver: `SmtVerifier::encode_scripts` (Rust), `encodeScripts()`
  (Java, TypeScript) and `libpetri.encode_smt_scripts` (Python) return the HORN script and,
  for the flat encoding, the certificate script around the placeholder certificate
  `(define-fun Reachable (…) Bool true)`; the goldens under
  `spec/verification-fixtures/scripts/<id>/` are written by the Rust verifier
  (`scripts/smt-script-parity.py --update`) and diffed by every implementation's
  script-parity test. A name-coloured HORN script carries the colour-slot bound `k` of
  [NU-053]; each implementation computes it with its own exact simplex, so `encodeScripts()`
  still starts no solver.

**Depends on:** [VER-001], [VER-003], [VER-007], [VER-017], [VER-022], [MOD-051], [IO-016]

**Test derivation:** a stub `z3` shell script named by `LIBPETRI_Z3` that answers `--version`
and then replays a scripted reply: a banner before `unsat`; an `(error …)` on stderr during the
certificate check; a `timeout` line; a script that never exits; a two-megabyte banner on each
stream; a version below the floor; a missing executable. For the total budget: a stub that sleeps past it, with
a total budget below the per-call timeout, yields the exhaustion reason within the budget. For
cancellation: the same sleeping stub, cancelled (Java: the verifying thread interrupted) shortly
after it starts, yields the cancellation reason long before the timeout, and the stub process is
gone; a token cancelled before the call yields it without a process. Plus the golden-script diff over the
shared verdict-parity fixtures, and the AC7 vector through each implementation's name
comparator.

---

#### VER-014: Conditional Sink Places (Designed Terminals)

**Priority:** SHOULD

`DeadlockFree` ([VER-002]) reads a quiescent marking against the places where a token may
rest. Besides the unconditional **sink places**, the verifier accepts **conditional sink
places**: a set of places where a token may rest **while a marker place holds a token**,
declared as `sinkPlacesWhen(marker, places…)`. A marked marker is a *designed terminal* — a
halted or paused run, a cancelled batch — under which the work it interrupted legitimately
stays where it was delivered. The marker itself is at rest whenever it is marked, so
`sinkPlacesWhen(marker)` with no further places excuses exactly the marker.

Declarations union. A token in place `p` of a quiescent marking `M` is **stranded** iff `p`
is not a declared sink, `p` is not a marker, and no conditional set naming `p` has its
marker marked in `M`. The `DeadlockFree` error condition becomes: (all transitions disabled)
∧ (some marked place is stranded). Repeated declarations for one marker accumulate;
declarations for different markers are independent, so a place excused by two markers is
stranded only when both are unmarked. `TerminatesAtSink` is unaffected and reads the
unconditional sinks only. An unresolved marker or place contributes nothing, as an
unresolved sink does: a mistyped marker makes the property stricter, never laxer.

**Encoding.** In the flat and name-coloured CHC encodings the stranded disjunction of
[VER-002] gains, for each place `p` excused by markers `k₁ < … < kₙ` (flat indices), the
disjunct `(and (>= m_p 1) (= m_k₁ 0) … (= m_kₙ 0))` in place of `(>= m_p 1)`; declared sinks
and markers contribute no disjunct. Scripts without a conditional declaration are
byte-identical to those of [VER-002]. The report renders the declarations after the property
as `(sinks: a, b; when h: c, d; when p)`, in declaration order.

**Acceptance Criteria:**
1. A quiescent marking that marks a marker and holds tokens only in declared sinks, in the
   marker, and in that marker's conditional places is not a `DeadlockFree` violation.
2. A quiescent marking that holds a token in a conditional place whose marker is **unmarked**
   is a violation, exactly as without the declaration.
3. The marker needs no self-listing: `sinkPlacesWhen(p)` excuses a quiescent marking holding
   only `p`.
4. `TerminatesAtSink` ignores conditional declarations: a quiescent marking that marks a
   marker but no declared sink violates it.
5. Every route that decides `DeadlockFree` — the flat encoder, the name-coloured encoder, the
   certificate check's safety condition, the abstract counterexample replay and the ν
   name-partition graph ([VER-012]) — reads the same rest set; the four implementations emit
   byte-identical scripts for the same declarations ([VER-013] AC1).

**Net-declared terminals.** A terminal place declared on the net ([EXEC-042]) is a designed
terminal that the caller does not restate. Every route verifies the net with `P` inhibiting each
transition, `P` added to the sinks, and `sinkPlacesWhen(P, all places)` added to the conditional
declarations. The open-net route ([VER-022]) merges it as a designed terminal. These additions
apply to the net's own terminals only. A net without them keeps its scripts byte-identical.

**Implementation notes:**
- Java: `SmtVerifier.sinkPlacesWhen(Place<?> marker, Place<?>... places)`.
- TypeScript: `SmtVerifier.sinkPlacesWhen(marker, ...places)`; `verification/rest-set`
  (`strandingExcuses`, `strandsToken`, `describeSinks`).
- Rust: `SmtVerifier::sink_places_when(marker, places)`.
- Python: `verify(..., sink_places_when={marker: [places…]})`.
- Fixtures: `sinkPlacesWhen` in `spec/verification-fixtures/fixtures.json`
  (`sink-partial-terminal-conditional-proven`, `dead-end-chain-marker-proven`,
  `dead-end-chain-unmarked-marker-violated`, `nu-mixed-terminal-route-b-conditional-proven`).

**Depends on:** [VER-002], [VER-012], [VER-013]

**Test derivation:** a fork whose one arm may halt while the other's token is still in
flight, with the halt marker inhibiting the second arm: `deadlockFree` with the halt as a
plain sink is violated (the in-flight token is stranded); with the in-flight place declared
under the halt marker it is proven; with the marker alone it stays violated; `terminatesAtSink`
with the same declarations is violated. A chain whose marker is consumed before quiescence
(AC2), and the same net with the resting place as its own marker (AC3).

---

#### VER-015: Linear State-Equation Bound

**Priority:** SHOULD

Before the fixpoint query, a **reachability-safety** property (`PlaceBound`,
`BranchPlaceBound`, `MutualExclusion`, `Unreachable`) is tried against the **state
equation**: every abstract-reachable marking satisfies `M = M0 + C·σ` for some firing count
vector `σ ≥ 0`, so for any weighting `y ≥ 0` with `y·C ≤ 0` on every transition,
`y·M ≤ y·M0` on every reachable marking — a *decreasing* conservation law, where the
P-invariants of [VER-005] are the equalities. The violation of such a property is a lower
demand `d` on some places (`m_p ≥ 1` for each place of an `Unreachable` or a two-place
`MutualExclusion`, `m_p ≥ k+1` for a bound `k`); if `y·d > y·M0` for some such `y`, no
reachable marking meets the demand and the property is **proven structurally**, without IC3.
A pairwise `MutualExclusion` over three or more places ([VER-002]) is a disjunction of
demands, one per pair: it is proven when every pair's demand is separated, one query each.

The weighting is found by one `QF_LIA` query through the solver transport of [VER-013]
(phase `bound`): variables `y_p ≥ 0` per flat place, `y_p = 0` on every consume-all / reset
place (H1) and every injected environment place (H3'), one row `Σ_p C[p][t]·y_p ≤ 0` per flat
transition, and `Σ_p d_p·y_p ≥ 1 + Σ_p M0_p·y_p`. A `sat` model is **re-checked in exact
integer arithmetic** (`y ≥ 0`, the zero weights, every row, the demand) before it is
believed; a model that fails the check is discarded. `unsat`, `unknown` and any transport
failure hand over to the fixpoint query. The phase is skipped under `Ignore` with
environment places registered ([VER-006] AC4) and for the quiescence properties, whose
violation is not a linear demand. A ν-net's verdict receives the [NU-050] over-approximation
note like any other flat proof.

This closes the class of proofs IC3 does not find on pipeline-shaped nets: an *ordering*
argument — "both join slots armed means every upstream stage has run, so no halt is still
possible" — is a weighted count bound, which Spacer's lemma generalisation does not invent
over fifty variables but a linear solver finds in milliseconds. A net that answered `unknown`
after 300 s answers `proven` in under a second.

**Acceptance Criteria:**
1. A reachability-safety property whose violating markings exceed some `y·M ≤ y·M0`
   (`y ≥ 0`, `y·C ≤ 0`) is `Proven` with method `structural`, without a fixpoint query, and
   the report names the bound and the demand:
   `  Linear state-equation bound: 2*p0 + a + b <= 2; violation needs a + b + halt >= 3`.
2. A property whose violation the state equation admits (`unsat` from the query) proceeds to
   the fixpoint query with the report line `  Linear state-equation bound: none separates the violation`.
3. The bound is re-proven in exact integer arithmetic; a model that fails it is reported
   `inconclusive (solver model failed the exact re-check)` and the fixpoint query runs.
4. The `bound` script is byte-identical across implementations ([VER-013] AC1) and is
   reported by `encodeScripts()` (`null` for a quiescence property) whenever `verify()` would
   send it, including on a net with an exact name-coloured plan.
5. A genuine violation is never masked: the phase can only return `Proven`.
6. On a ν-net with an exact name-coloured plan, a reachability-safety property the bound
   separates is `Proven` (structural) without the coloured query; one it does not separate
   reaches the coloured query and gets the verdict it got before.

**On ν-nets the phase also runs before the name-coloured encoding ([NU-053]).** The state
equation is written over the flat, name-blind net, whose firing rule ignores which name a token
carries; every marking the ν semantics reaches is reachable there too, so a weighting that
separates the violation on the flat net separates it on the ν-net, and a structural `Proven` is
sound. A net with an exact coloured plan therefore tries the bound first, under the same
conditions as the flat path (enabled, a reachability-safety property, not `Ignore` with
environment places, the total budget and cancellation of [VER-013] respected), with the same
phase name. `Proven` returns as on the flat path — method `structural`, the lines of AC1 — and
keeps any ν-encoding notes already in the report; anything else hands over to the coloured
query, whose verdict and notes are unchanged. The coloured plan is built only after the bound
fails to prove; nothing before it reads the plan. Route B ([VER-012]) keeps its place in the
dispatch: the bound runs after it, never before. The colour-slot bound of the coloured encoding
counts coloured tokens rather than names, often two to four times the declared budget, and IC3 over that
many colour slots can time out on a bound the flat state equation proves in milliseconds. On six
PNID ν-nets (`research/net-metrics/validation/pnid/`), `placeBound(X, 1000)` under a budget of 2
went from `Unknown` after about 8 s to `Proven` in about 12 ms.

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
over to the fixpoint query, which reports `violated` with a confirmed replay.

---

#### VER-016: State-Equation Strengthening with Firing Counters

**Priority:** SHOULD

The flat CHC encoding ([VER-001]) MAY carry the **state equation** itself. With the option
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
relation, whose only counter knowledge is the increment. The counterexample decoder reads a
fact's marking from its leading `P` arguments. The option does not apply to the
name-coloured encoding ([NU-050]) or to Route B ([VER-012]); the report says so when both
are requested.

**Acceptance Criteria:**
1. With the option disabled the scripts and reports are byte-identical to a build without it.
2. With the option enabled `Reachable` has arity `P + T`, the initial fact ends in `T` zeros,
   transition `t`'s rule contains `(= n_tp (+ n_t 1))` and `(= n_jp n_j)` for every `j ≠ t`,
   and every transition rule contains the marking equation of every exact place over the
   primed variables; a consume-all or reset place carries the upper bound `(<= m_pp …)`
   instead, and an injected place carries none.
3. A `Proven` verdict passes the certificate check (`init, consecution, safety`) with the
   equation in the candidate; a genuine violation stays `Violated` and its counterexample
   replays.
4. The report carries `  State equation: encoded over T firing counters (VER-016)` when the
   option applied, and `  State equation: not applied (name-coloured encoding)` when it was
   requested on the coloured path.
5. The HORN and certificate scripts with the option enabled are byte-identical across the four
   implementations ([VER-013] AC1).

**Implementation notes:**
- Java: `SmtVerifier.stateEquation(boolean)`.
- TypeScript: `SmtVerifier.stateEquation(enabled)`; `encodeNet(…, { stateEquation })`.
- Rust: `SmtVerifier::state_equation(bool)`.
- Python: `verify(..., state_equation=True)`.
- Python inherits the Rust encoder, upper-bound rows included.

**Depends on:** [VER-001], [VER-004], [VER-005], [VER-013], [VER-015]

**Test derivation:** the fork-that-may-halt net of [VER-015] under `deadlockFree` with
`done` and `halt` as sinks: proven, certificate check passed, report names five counters;
with `halt` not a sink: violated with a confirmed replay ending in a halted marking. The
`unreachable{ra, rb, halt}` script has arity `7 + 5`, `(= m4p (+ 1 (- n0p) (- n1p)))` in each
of its five rules, and an upper bound rather than an equation for a consume-all place on a
net that has one.

---

#### VER-017: Bounded State-Space Enumeration Route

**Priority:** SHOULD

Before the SMT pipeline ([VER-001]), an implementation SHOULD try to decide the property by
**enumerating the state-class graph** ([VER-010]) up to a class budget. When the graph closes
within the budget the verdict is read off it directly and no solver runs; when it does not, the
route declines and the SMT pipeline runs unchanged.

The motivation is a shape the fixpoint engine handles badly and enumeration handles trivially.
IC3/PDR is built for state spaces that are wide and shallow; a workflow net is the opposite,
narrow and deep. A forty-node pipeline has fewer than two thousand reachable classes, but its
*diameter* is the length of the pipeline, so the search needs a frame per stage and its cost
climbs with roughly the cube of the length. Enumeration is linear in the reachable state space.
Measured on a compiled forty-node linear workflow (370 places, 163 transitions, 1 967 classes):
**410 s on the fixpoint path, 0.11 s here**; at 160 nodes (1 450 places) enumeration takes 5.5 s
while the fixpoint path is far beyond any practical budget.

**When the route applies.** All four conditions, so that its verdict is interchangeable with the
one it replaces:

1. The net declares **no match (ν-join) transitions** — a ν-net has its own exact route
   ([VER-012], Route B), which subsumes this one.
2. **No environment places** are registered. The graph does not model injection ([VER-006]), so
   a verdict about an open net would not mean what the encoders' does.
3. The net is **untimed** — every transition `immediate`. The graph carries firing domains, so on
   a timed net it would explore only the runs the timing admits and its `proven` would be the
   weaker *timed* claim; [VER-004] fixes the untimed proof as the stronger one, and a route MUST
   NOT quietly return a weaker claim than the route it replaced. On an untimed net no domain
   excludes anything, so the graph explores exactly the untimed reachable set.
4. The class budget is positive. Setting it to `0` disables the route.

**What the verdict means.** Exact — sound *and* complete. A `violated` is a real firing sequence
with the shortest witnessing path from the initial class, not a possibly-spurious
over-approximation, so it needs no replay: implementations report `counterexampleConfirmed` as
confirmed (AC2), since the path is itself an ordered firing sequence of the untimed abstraction
([VER-003]). Its `counterexampleTiming` is `UNTIMED_NET`, as the route runs only on untimed nets
(condition 3). A `proven` is the
same claim the encoders make, decided by enumeration rather than by search. The route decides the
**same predicate** as every other route ([VER-002] AC7, [VER-014]); implementations MUST share
one predicate implementation between this route and [VER-012]'s rather than restate it.

The route can only add verdicts, never remove them: on truncation the SMT pipeline runs exactly
as before, unless the explored prefix already violates the property (below), so no query that the
solver could decide becomes `unknown`.

**Verdicts from a truncated graph.** A graph cut off at the class budget is not thrown away. Every
class it stored is a real reachable class, and the builder explores breadth-first, so the
depth at which it discovered a class is that class's true distance from the initial class. On
truncation the route therefore runs the **same shared predicate** over the explored prefix, with
one restriction on which classes count:

- **Safety properties** (`placeBound`, `branchPlaceBound`, `unreachable`, `mutualExclusion`): every
  stored class counts, expanded or not.
- **Quiescence properties** (`deadlockFree`, `terminatesAtSink`, `joinedOrDeadLettered`,
  `quiescentCount`, and any other property that reads "this class has no successor"): only classes
  the builder **expanded** and found without successors count. A frontier class, stored but never
  expanded, has no successor only because nobody looked, and MUST NOT count as quiescent. With a
  first-in-first-out worklist the expanded classes are exactly those whose discovery index is
  below the number of classes taken from the worklist, and the builder exposes that number.

A hit is `Violated`, with the shortest path to a violating class inside the explored graph as the
witness; the report says the graph was truncated at `N` classes and that the violation was found
in the explored prefix. A miss changes nothing: the route declines as before. **`Proven` never
comes from a prefix.** The same rule applies to Route B ([VER-012]) and to the timed check
([VER-023]); each uses the one shared predicate, not its own copy.

A graph stopped by the total budget or by cancellation ([VER-013]) is not a truncation at the
class budget: the prefix check does not run on it, and the verdict is the `Unknown` of [VER-013].

**Reusing the state space across queries.** The graph depends only on the net and its initial
marking. The property, the sinks and the conditional sinks only *read* it. A caller that asks many
questions of one net would otherwise rebuild the same graph for every question. When the graph
exceeds the budget, every question pays the full attempt before it falls through. Measured on a
47-place, 54-transition agent net whose graph exceeds the default budget: 3–4.6 s per query with
the route, 17–24 ms without it; 5 183 claims took more than 15 minutes instead of 149 s.

An implementation SHOULD therefore offer an explicit **state-space cache** that the caller creates,
passes to each verification, and owns: `StateSpaceCache` / `stateSpaceCache(cache)`. Without one,
behaviour is exactly as above. With one:

- An entry is keyed by the caller's net, the transitions the in-flight split of [VER-004] rewrote,
  and the initial marking. The split changes the graph: under `assumeAtomicFiring` the net stays
  atomic, and otherwise a transition whose output another tests non-monotonically becomes two
  steps. A key without the split would let a graph of the atomic net answer a query that runs on
  the split one, and that `Proven` can be wrong. The inert-place, split and terminal ([EXEC-042])
  rewrites are a deterministic function of the net and the transitions split, so the rest of the
  key is the net as the caller passed it. An implementation may key on the split net instead. An
  implementation whose nets have no stable identity keys on a structural fingerprint instead. The
  fingerprint MUST cover everything the graph reads: places, arcs with their kinds and
  cardinalities, outputs, timing, priority and terminals. A fingerprint that also covers the actions
  may miss where it could hit, and that is allowed. It MUST NOT hit where the graphs differ.
- The marking half of the key is the marking the caller passed. Where the order in which a marking
  lists its places is observable in a witness, either that order is part of the key, or the
  witness takes its first state from the caller's own marking rather than the cached graph's.
- A **closed** graph of `C` classes is reused for any budget greater than `C`. A budget of `C` or
  less would have truncated, and is answered as truncated.
- A **truncated** attempt at budget `B` is remembered **with its explored prefix**: the stored
  classes, their successors and the number expanded. Any later budget of `B` or less does not
  build: it runs the prefix check above over the remembered prefix, and declines at once when that
  finds nothing. A larger budget builds again and replaces the entry.
- The verdict, the witness and the route are the same with and without the cache, with one
  exception: a query at a budget below `B` that hits a remembered truncation at `B` checks the
  larger remembered prefix, so it can find a violation an uncached query at its own budget would
  not reach. Such a violation is still a real firing sequence; it never turns a verdict into
  `Proven`. The report says when a cached graph, or a cached truncation, was used.
- Concurrent verifications that share a cache build a given entry once. The others wait for it
  rather than build their own. While a larger budget rebuilds a truncated entry, a budget of `B` or
  less still declines at once rather than wait.
- A build that fails leaves the entry as it found it: absent, or the truncation it was replacing.
  The failure reaches the query that ran the build. Queries waiting on it do not inherit the
  failure: each looks again, and declines, reuses or builds as its own budget requires.
- The cache holds its graphs until the caller drops it or clears it. It never shares memory the
  caller did not ask for.

**Acceptance Criteria:**
1. On an untimed net whose state-class graph closes within the budget, the property is decided
   without invoking a solver: the report names the route and its class count, and carries no
   solver phase.
2. A violated verdict carries a counterexample trace whose transition sequence is a real firing
   sequence from the initial marking to the witnessing class, reported as **confirmed**: the
   graph path is a firing sequence, so it is ordered by construction and there is nothing to
   replay. A consumer keying "are these steps ordered" off that field is correct without
   special-casing the route.
3. The result names this route and reports that P-invariants were not computed, so an empty
   invariant list is not mistaken for "the net has none".
4. Exceeding the budget produces a report line naming the budget and, unless the explored prefix
   violates the property, falls through to the SMT pipeline, whose behaviour is unchanged.
5. The route is skipped for a ν-net, for a net with environment places, for a timed net, and
   when the budget is `0`; in each case the report shows the SMT pipeline ran.
6. Where both routes can answer, they return the same verdict for the same net and property.
7. With a state-space cache, the second and later queries on one net and initial marking build
   no graph, and return the same verdict, witness and route as a query without the cache.
8. A cached truncation at budget `B` makes a query at budget `≤ B` answer from the remembered
   prefix without building: `Violated` when the prefix violates the property, otherwise a decline.
   A query at a larger budget builds, and replaces the entry.
9. A different initial marking, or a structurally different net, never hits another entry. Nor
   does the same net verified with a different in-flight split: on a net that the split
   rewrites, a query with `assumeAtomicFiring` and one without build a graph each, in either
   order, and each answers as it does without the cache.
10. Parallel queries sharing a cache on one net build its graph once, where the runtime has
    parallel queries.
11. **Truncated prefix.** A safety property violated by a class inside a truncated graph is
    `Violated` with the shortest witness in the explored graph, and the report names the
    truncation. A quiescence property is never violated by a frontier class: on a net whose only
    successor-free classes in the prefix are unexpanded frontier classes, the route declines. No
    truncated graph yields `Proven`.

**Implementation notes:**
- TypeScript: `verification/scg-verifier` (`verifyViaStateClassGraph`, `isUntimed`);
  `SmtVerifier.enumerationMaxClasses(max)`, default 50 000. The shared predicate is
  `verification/graph-decision` (`decideOverClasses`), used by [VER-012]'s route as well.
  The state-space cache is `StateSpaceCache` (`verification/state-space-cache`; its only public
  method is `clear()`), passed with `SmtVerifier.stateSpaceCache(cache)`. The key is the net
  instance (held weakly), the list of transitions the in-flight split rewrote, the initial marking
  in the order it lists its places, and the `Place`
  objects it names, so an equal marking listed in another order misses. `decideOverStateSpace`
  (exported from `libpetri/verification`) returns an `ScgOutcome`, `truncated` for an incomplete
  graph. The build is synchronous, so concurrent `verify()` calls on one event loop build an entry
  once, and a build that throws leaves the previous entry in place.
- Java: `org.libpetri.smt.ScgVerifier`; `SmtVerifier.enumerationMaxClasses(int)`.
  The state-space cache is `org.libpetri.smt.StateSpaceCache` (`clear()`; `size()` counts entries,
  builds in flight included), passed with `SmtVerifier.stateSpaceCache(StateSpaceCache)`. The key
  is the net by identity, the list of transitions the in-flight split rewrote, the initial marking
  by equality, and the order `placesWithTokens()` lists
  its places in, so the whole witness matches an uncached query. It is thread-safe: concurrent
  queries wait on one build per entry, and waiting is not interruptible.
- Rust: `libpetri-verification` `scg_verifier`; `SmtVerifier::enumeration_max_classes(usize)`.
  The cache is `state_space_cache::StateSpaceCache` (`new`, `clear`, `len`, `is_empty`,
  `build_count`; `len` counts closed and truncated entries, including one whose larger rebuild is
  in flight, but not a first build;
  `Clone` shares it, `Send + Sync`), passed as `SmtVerifier::state_space_cache(&cache)`. A
  `PetriNet` has no identity, so the key is a structural fingerprint of the net every route reads
  (closed under arrivals, with its inert places, split in flight unless `assume_atomic_firing`): the
  `Debug` rendering of its place names, sorted, its terminals and, per transition, name, input specs, output
  spec, inhibitor, read and reset arcs, timing, priority and match presence. Actions and
  transition ids are left out, so clones and rebuilt copies hit. The full string is the key,
  not a hash. The marking is keyed by its counts in place-name order. A witness from a cached
  graph starts at the caller's own listing of the initial marking. Parallel queries wait on a
  per-entry condition variable. A build that panics restores the slot to what it held (empty, or
  the truncation), wakes the waiters to retry, and propagates.
- Python: `verify(..., enumeration_max_classes=50_000)`. The cache is
  `libpetri.StateSpaceCache()` (`len(cache)`, `cache.build_count`, `cache.clear()`), passed as
  `verify(..., state_space_cache=cache)`. It wraps the Rust cache, so it keys on the same
  structural fingerprint, which is why it hits although the binding clones the net on every
  call. An empty cache is falsy, since it defines `__len__`. The `initial_marking` dict is read in
  insertion order, so a witness starts in the caller's order.

**Depends on:** [VER-002], [VER-004], [VER-006], [VER-010], [VER-012], [VER-013], [VER-014]

**Test derivation:** a pipeline `p0 → t0 → p1 → … → pn`, untimed: `deadlockFree` with `pn` a sink
is proven by enumeration with `n+1` classes and no solver phase; without the sink it is violated
with the firing sequence `t0 … t(n-1)`. The same net with a class budget below the graph size
reports truncation and is answered by the SMT pipeline; with the budget `0` the route never runs.
A `delayed` variant of the same net is skipped as timed. For AC5, the same query with and without
the route returns the same verdict. For AC11, an untimed net with an unbounded producer
(`gen: G → G, A`) and `placeBound(A, 2)` under a class budget of 50 is `Violated` by the route with
the trace `gen, gen, gen`, where it used to fall through; `deadlockFree` on the same truncated
graph falls through.

---

#### VER-018: State-Equation Phase with Refinement

**Priority:** SHOULD

Before the fixpoint query, the verifier asks one `QF_LIA` query (phase `state-equation`, through
the transport of [VER-013]): can a marking that satisfies the marking equation of [VER-016]
violate the property? The equation is `m = M0 + C·n` over firing counts `n ≥ 0`, with an upper
bound on a place a consume-all or reset arc clears and no row for an injected place; the
violation is encoded exactly as the error rule of [VER-001] encodes it. Every reachable marking
satisfies the equation for the counts of its run, so `unsat` proves the property. Unlike
[VER-015] the query asks for the violation directly, so it covers every property, quiescence
included.

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
   nothing, since an injected token could enable a run it never tried, so the search MUST report
   itself inconclusive rather than report that no violating run exists. Implementations MUST NOT
   skip the search on such nets: it is the phase's only source of witnesses there.
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

Every refinement holds in every reachable marking, so the query is asked again and a later
`unsat` is still a proof. The phase steps aside, leaving the pipeline unchanged, when nothing
settles a candidate, after 32 refinements, on a transport failure, or when the timeout runs out.

**Certificate.** A proof is the inductive invariant `SE(M, n) ∧ ⋀ refinements(M)` over the places
and one counter per flat transition. It goes as the `Reachable` interpretation to the certificate
check of [VER-016], which re-proves initiation, consecution and safety against the raw step
relation before `Proven` is reported with method `state-equation`. The report prints each
refinement and the result lists them as its discovered invariants. A failed or inconclusive check
withholds the `Proven`, says so in the report, and the pipeline continues. The Farkas dual of the
final `unsat` is not used as the certificate: for a quiescence property the violation is a
disjunction, and one inequality per disjunct is exponential in the net.

**Where it runs.** On the flat path, after [VER-015] and before the fixpoint query. Not on a net
with match transitions (the flat encoding is name-blind there; [VER-012] and [NU-053] are its
exact routes), not on the name-coloured encoding, and not under `Ignore` with environment places
registered ([VER-006]). On by default; MAY be disabled to force the fixpoint path.

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
4. The phase's `Proven` is withheld unless the certificate check passes. A genuine violation is
   never masked: the phase returns `Violated` only for a replayed run.
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
  the language spells its other toggles. `stateEquationPhase` is not `stateEquation`
  ([VER-016]), which adds firing counters *inside* the fixpoint encoding and is off by default;
  an implementation SHOULD cross-reference the two wherever it documents either.

**Depends on:** [VER-001], [VER-003], [VER-004], [VER-006], [VER-013], [VER-015], [VER-016]

**Test derivation:** the join of a compiled workflow net — `route: start → AND(aData, bEmpty) |
AND(aEmpty, bData)`, a data arm writing `hasdata` with its `ready`, an empty arm its `ready`
alone, `mergeStart: ready0 + ready1 + all(hasdata) → done`, `mergeSkip: ready0 + ready1,
inhibitor(hasdata) → skipped` — under `deadlockFree` with `done` and `skipped` as sinks: the first
candidate skips after the data arrived, one inductive inequality excludes it, and the proof passes
the certificate check. The queue-and-bundle net (`produce: budget → q` inhibited by `s` and by
`out`, `signal: src → s`, `bundle: all(q) + s → out`, `bundleEmpty: s, inhibitor(q) → out`,
`M0 = {budget: 3, src: 1}`) with `out` and `budget` as sinks: proven with `3*out + q <= 3`,
relative to the equation. With a `cancel: src → cancelled` alternative and `cancelled` a sink:
violated, with the run `produce, produce, produce, cancel`.

---

#### VER-019: Firing-Bound Phase

**Priority:** SHOULD

After [VER-018] and before the fixpoint query, the verifier tries to bound the length of every
run. A **ranking** is a weighting `r ≥ 0` of the places with `r·C_t ≤ −1` for every flat
transition `t` that can fire (one that inhibits a place it needs cannot). A consume-all or reset
arc removes at least `pre`, so with `r ≥ 0` the column `C_t = post − pre` bounds such a firing's
effect on `r·M` from above. Every firing therefore lowers `r·M` by at least one, `r·M` never goes
below zero, and no run from `M0` has more than `K = r·M0` firings.
The ranking with the least `K` is found by one `QF_LIA` optimisation query (phase `ranking`) and
re-checked in exact integer arithmetic.

With the bound, a **bounded model check** decides the property. One `QF_LIA` script (phase `bmc`)
unrolls `d` steps of the exact step relation from `M0`: a selector per step names the transition
fired or an idle step, an idle step is followed only by idle steps, the environment post-caps
apply, and the violation is asked of the last marking. The depths are 8, 16, 32, … up to `K`.
`sat` is a run; it is replayed firing by firing under the exact abstract semantics and reported
`violated`, confirmed. `unsat` at depth `K` is `Proven` with method `bounded-model-check`, a claim
about every run, since none is longer.

When no ranking exists, Farkas gives firing counts `y ≥ 0, y ≠ 0` with `C·y ≥ 0`, which the
marking equation lets repeat forever. The report names their transitions (a second query) and the
pipeline continues. This does not show that the net has an infinite run — a loop that only an
inhibitor stops has no ranking — only that the phase makes no claim about runs it cannot bound.

A proof from this phase has no inductive invariant, so the certificate check does not apply; it
rests on the exactly re-checked ranking and the solver's `unsat`. The phase gets half the
timeout: short counterexamples take seconds, while a proof to a deep bound on a wide net can
outlast any budget. It runs where [VER-018] runs, and not on a net with injected environment
places, since no weighting bounds an injection. On by default; MAY be disabled to force the
fixpoint path.

Every implementation MUST default this phase and [VER-018]'s the same way: a pre-fixpoint verdict
carries its own `method` and report, so differing defaults break the verdict-parity fixtures
without any property differing.

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
   and the fixpoint query runs.
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

**Test derivation:** the queue-and-bundle net of [VER-018] with that phase disabled: the ranking
`budget + s + 2*src` gives the bound 5, and the bounded model check at depth 5 proves the property;
with the cancel alternative, a replayed run violates it. A ring `p0 → t0 → p1 → t1 → p2 → t2 → p0`
has no ranking: the report names `t0, t1, t2`, and the fixpoint query proves `placeBound(p0, 1)`.

---

## State Class Graph

#### VER-010: State Class Graph Analysis

**Priority:** MAY

The engine may support state class graph construction using the Berthomieu-Diaz (1991) algorithm. State classes combine a marking with a Difference Bound Matrix (DBM) representing timing constraints on enabled transitions.

**Acceptance Criteria:**
1. State class graph enumerates reachable (marking, timing zone) pairs. A class's identity is
   its marking and its **full** firing domain, independent of the order in which its
   transitions became enabled: the successor step lays clocks out persistent-then-newly-
   enabled, which is path-dependent, so implementations MUST put every class's clocks in one
   canonical order (ascending transition name, in the code-point order of [VER-013]) and key
   on the complete difference-bound matrix ([VER-011]), not on the per-clock projections
   alone. Two arrivals at the same marking and zone by different interleavings are one class;
   two zones that agree on every projection but differ in a difference constraint are two. On
   an untimed workflow net the order-sensitive key inflated the class count 1.5× (one marking
   held by fourteen classes); the projection-only key merges classes whose successors differ,
   which can lose a reachable marking.
2. Successor computation correctly handles transition firing and clock updates. The
   number of tokens a firing removes from each input place MUST be the canonical
   `consumptionCount(available)` of [IO-007] — the same function the executor uses —
   and not the enablement threshold `requiredCount()`. In particular `All` and
   `AtLeast(m)` drain the place.
3. XOR outputs are expanded into virtual transitions for branch analysis.
4. Clock persistence uses the intermediate marking of Berthomieu and Diaz. After `t` fires
   from marking `M`, a transition `t' ≠ t` keeps its clock only if it is enabled in `M`, in
   the successor marking `M'`, and in the intermediate marking `M - Pre(t)`: inputs
   consumed, reset places drained, outputs not yet deposited. Every other transition
   enabled in `M'` gets a fresh firing interval. This is the executor's rule ([TIME-012]).
   A successor that keeps a clock the executor restarts under-approximates the executor's
   behaviors. Two limits follow from the graph's abstractions: a transition outside the
   in-flight split of [VER-004] fires atomically and takes no time (a split one completes
   through its immediate completion step at any later time); and under `alwaysAvailable` /
   `bounded` environment modes an environment input never disables a transition.
5. The graph builder (`StateClassGraph.build` in every language) builds the graph of the net it
   is given and does not apply the in-flight split itself. A caller that builds the graph
   directly, outside `SmtVerifier`, MUST apply the split first (`splitInFlight` in TypeScript,
   `in_flight::split_in_flight` in Rust, `InFlight.split` in Java) to get the executor's
   two-step firing ([VER-004]); when the split is refused, no graph of this kind is faithful to
   the executor. The builder's documentation MUST say so.

**Depends on:** [IO-007], [EXEC-010], [TIME-012]

**Implementation notes:**
- Java: Full implementation
- TypeScript: Full implementation
- Rust: Full implementation (`libpetri-verification` `state_class_graph`)

**Test derivation:** Small timed net; construct state class graph; verify reachable
classes match expected. Regression: a transition with an `all(p)` input followed by a
transition inhibited on `p` — the inhibited successor MUST be reachable, since `p` is
drained; an `atLeast(2, p)` input over 5 tokens MUST leave `p` empty. For AC4, a timer
place `p` feeds a delayed transition `d`, and a refresh transition consumes `p` and deposits
into it again: `d` MUST be newly enabled in the successor class. With a second token in
`p` it MUST be persistent; with a reset arc on `p` it MUST be newly enabled.

---

#### VER-011: DBM Zone Representation

**Priority:** MAY

Timing constraints within a state class are represented as a Difference Bound Matrix (DBM), encoding constraints of the form `θᵢ - θⱼ ≤ cᵢⱼ` where θᵢ is the firing clock of transition i.

**Acceptance Criteria:**
1. DBM encodes lower and upper bounds for each transition clock.
2. Zone emptiness is detectable (unsatisfiable constraints).
3. Successor DBM is computed correctly after transition firing.
4. The zone exposes a dedup key over its full canonical matrix (every `θᵢ - θⱼ` bound, not
   only the diagonal projections), and a permutation of its clocks that reorders the matrix
   with them; equality is positional over the canonical order ([VER-010] AC1).

**Implementation notes:**
- Java: Full implementation
- TypeScript: Full implementation
- Rust: Full implementation (`libpetri-verification` `dbm`)

**Test derivation:** Create DBM for 3 timed transitions; fire one; verify successor zone constraints.

---

#### VER-012: Name-Aware State Class Graph (ν-Partition Quotient)

**Priority:** MAY

The state class graph ([VER-010]) MAY be made **ν-aware** to decide [NU-020] join
correlation *exactly* — the [NU-050] **Route B** carve-out. Each correlation
token carries an abstract, interchangeable name-symbol; a matched (ν-join)
transition is enabled only when one symbol is shared by every correlated input
(not merely when the token counts allow); a minting fork introduces a
globally-fresh symbol; and the graph is quotiented under name-permutation
symmetry (its dedup key abstracts the symbol identities). The timed firing domain
([VER-011]) is carried unchanged alongside the name partition, so the analysis is
exact over **name × time**, and quiescence ([NU-050]) is decided over the
name-aware terminal classes.

**Acceptance Criteria:**
1. A ν-join fires in the graph only on a name shared by all correlated inputs; a
   marking reachable only by equating two distinct names is *not* reachable
   (NU-050 #1), with no budget place required.
2. Two markings differing only by a permutation of name-symbols are the same
   state class (the quotient is finite when the live-name pool is structurally
   bounded).
3. **Conditional on an executor-faithful consumption model** (see below): when the
   graph closes within the class bound the verdict is exact (sound and complete) for
   reachability-safety and quiescence, for the net it explores. When that graph keeps a latest
   bound (under `assumeNoReaping`, or a direct call on a timed net) it reads each firing as one
   instant step, so the verdict is exact only for an on-time executor whose actions take no
   time, and the report says so ([VER-004] AC3). A graph that does not close within the class
   bound truncates (NU-050 #2 — undecidability
   surfaces as truncation) and the shared predicate runs over the explored prefix by the rule
   of [VER-017] ("Verdicts from a truncated graph"): a safety property violated by any stored
   class, or a quiescence property violated by an **expanded** class with no successor, is
   `Violated` with the shortest witness in the explored graph and a report line naming the
   truncation; otherwise the verdict is `Unknown`. A truncated graph never yields `Proven`, and a
   reachability-safety `Unknown` from Route B is still final (the dispatcher has no fallback for
   it), so the prefix check is what turns a shallow violation into a verdict. PNID Fig. 11(b)
   (`research/net-metrics/validation/pnid/`), `placeBound(order_clerk, 2)` at a class bound of
   50: `Violated` with the depth-3 trace `create_order ×3`.
4. `All` and `AtLeast(m)` inputs drain their place in the graph exactly as they do at
   run time: after a successor step the source place holds no residue, so an inhibitor
   arc on that place is satisfied in the successor class.
5. **Early stop for safety properties.** For a reachability-safety property (`PlaceBound`,
   `BranchPlaceBound`, `Unreachable`, `MutualExclusion` — the safety set of [VER-017]'s
   "Verdicts from a truncated graph") the build checks each class with the same shared predicate
   as it is discovered and stops at the first violating class. BFS discovers classes in index
   order, so that class is the lowest-index violating class — the one the check over a full or
   truncated graph selects — and its path is the shortest; verdict, route and witness are
   identical to a build without the early stop, and only the class count and time differ. When
   the stop comes before the class bound, the report note
   `Note: Route B stopped at the first violating class after N classes (VER-012). Every explored class is reachable and classes are discovered breadth-first, so the counterexample is a real firing sequence and a shortest one to any violation.`
   replaces both the truncation note and the exact-graph note, and the parent whose expansion
   discovered the violating class does not count as expanded; when the bound is hit first, criterion 3 applies unchanged. Quiescence
   properties do not stop early (they need expanded classes). An early-stopped graph is not
   complete and MUST NOT be treated as closed. PNID Fig. 11(b), `placeBound(order_clerk, 2)` at
   the default class bound: `Violated` with `create_order ×3` after a handful of classes,
   where it took 1.8 s to fill the cap first.

**Exactness precondition (consumption model).** The exactness of criterion 3 is not
unconditional — it holds only while the graph's successor relation removes the *same*
tokens the executor would. The successor step MUST derive each input's token count from
the canonical `consumptionCount(available)` of [IO-007] (so `All` and `AtLeast(m)`
consume **all** available tokens, not merely `requiredCount()`), in the [EXEC-010] FIFO
order. A successor relation that consumes a *minimum* instead leaves phantom residue in
the source place; that residue keeps inhibitor arcs on the place unsatisfied and
suppresses successor classes, so a genuinely reachable marking is reported unreachable —
an **unsound** `Proven`, not a conservative one. Implementations therefore MUST delegate
to the same cardinality contract the executor uses rather than restating it.

**Implementation notes:**
- Rust: Full implementation (`libpetri-verification` `name_state_class_graph` /
  `nu_scg_verifier`); the canonical name-partition key format is shared verbatim.
- Java: Full implementation (`org.libpetri.analysis.NameStateClassGraph` /
  `org.libpetri.smt.NuScgVerifier`).
- TypeScript: Full implementation (`verification/analysis/name-state-class-graph`
  / `verification/nu-scg-verifier`).
- Python: inherits the Rust analysis through `verify`.
- Memory: an implementation MAY intern (hash-cons) the base class and the name layer
  between state classes. The base intern key MUST include the class-relative
  earliest-ready times alongside the marking and zone, because the [NU-052] prune reads
  them while class equality does not. Class identity MUST carry them too: the graph's
  dedup key is the pair of intern ids (base, name layer), not the class object, so two
  arrivals that agree on marking, zone and name layer but disagree on the earliest-ready
  times stay two classes and each keeps its own prune input. Interning is semantics-free by key-equivariance of
  the successor step (Lean `Interning.lean`, `interned_keys_eq`): the reachable quotient
  and the verdict are unchanged; class indices and the reported counterexample trace may
  differ from a non-interned build.
- Successor emission (orbit dedup): a join yields one successor per **distinct signature**
  among its enabling symbols, not one per symbol; a symbol's signature is its count vector over
  the coloured places in `colouredOrder`, and the consume role ([NU-051]) is deduplicated the same
  way. Two symbols with equal signatures are exchanged by a transposition that fixes the name
  marking, so their successors have equal canonical keys: the class set and the set of
  (label, key) successor pairs are unchanged, and only parallel identical edges disappear. The
  per-symbol emission copied and keyed every successor only to collapse them into one class,
  which made join-heavy graphs roughly quadratic in their class count. Measured in TypeScript on
  PNID Fig. 11(b): 8 000 classes in 0.49 s instead of 14.5 s; 100 000 classes in about 19 s
  instead of an estimated 35 min. Class counts and verdicts are unchanged, and so is the discovery
  order when each signature is represented by its first enabling symbol; a count of edges is not a
  stable quantity to test. The renaming-equivariance that Lean `Interning.lean`
  assumes per role still holds, because the number of distinct signatures is itself invariant
  under renaming.
- Early stop (AC5) is Route B only: the [VER-017] enumeration and the [VER-023] timed check still
  build their graphs in full, since those feed the state-space cache and other properties. An
  early-stopped build is a BFS prefix, so every class in it is reachable, by the argument of Lean `build_reach` for the enumeration
  route.
- The counterexample path is read from per-class labelled successor lists, not by scanning every
  edge for each dequeued class.
- Solver-free (no Z3); the verifier prefers Route A's bounded name-colouring for
  budget-declared untimed reachability-safety and uses this route for quiescence,
  budget-less, and timed ν-nets.

**Depends on:** [VER-010], [VER-011], [VER-017], [NU-020], [NU-050], [IO-007]

**Test derivation:** Two independent mints feeding one join with no budget place;
verify the join output is unreachable (NU-050 #1); a same-mint variant reaches it;
an ever-minting net truncates to `Unknown`. For AC3's prefix rule, PNID Fig. 11(b) under
`placeBound(order_clerk, 2)` at a class bound of 50 is `Violated` with a depth-3 trace, and a
quiescence property on an ever-minting net whose only successor-free classes are frontier classes
stays `Unknown`. For the early stop (AC5), the same Fig. 11(b) query at the default class bound
is `Violated` after fewer than 50 classes with the trace `create_order ×3`, a quiescence property
on that net explores as before, and on several fixtures the early-stop witness equals the witness
from a build without it. For the orbit dedup, the class count of every existing Route B fixture is
unchanged, and an 8 000-class build of Fig. 11(b) finishes under a generous time bound.

---

#### VER-023: Timed Counterexample Check

**Priority:** SHOULD

The flat encoders decide the untimed abstraction ([VER-004]), so a `Violated` on a timed net can
rest on a run the timing forbids. A call that answers within `window(0, 2)`, raced by a watchdog
that fires after `delayed(5)`, never times out; `unreachable(TIMEOUT)` is nevertheless
`Violated` by the SMT pipeline, with `counterexampleConfirmed` true, because the trace
`start, watchdog` replays in the untimed abstraction. Until [VER-003]'s `counterexampleTiming`,
the only signal was a warning line in the report. An implementation SHOULD offer an opt-in
**timed check** that asks the timed state-class graph about such a counterexample. It is off by
default.

**When it runs.** The option is on, the verdict is `Violated`, and:

1. the net is timed (some transition is not `immediate`, [VER-017] condition 3);
2. no environment places are registered, since the graph does not model injection ([VER-006],
   [VER-017] condition 2);
3. the net declares no match (ν-join) transitions. The state-class graph is name-blind: it fires a
   join on tokens whose names differ and misses the quiescent markings of a join that never
   matches ([VER-017] condition 1, [VER-022]), so neither its violation nor its closure would
   mean anything about the net. A timed ν-net is normally decided by Route B, which is already
   `TIMED_EXACT`;
4. the deciding route is not already `TIMED_EXACT`.

Otherwise `counterexampleTiming` keeps the value [VER-003] gives it without the check:
`UNTIMED_NET`, `TIMED_EXACT` or `UNTIMED_ABSTRACTION`.

**What it does.** Build the **timed** state-class graph of [VER-010] (firing domains kept) from
the same net, initial marking and terminal rewrite ([EXEC-042]) the other routes use, under the
class budget of [VER-017] and the total budget of [VER-013] when one is set, and decide the same
property over its classes with the same shared predicate the enumeration route and Route B use
([VER-017]), with the same sinks and conditional sinks ([VER-014]). The check does not read or
write a state-space cache ([VER-017]): the cache holds untimed graphs. It runs once, as a wrapper
at the end of `verify()`, after every route has spoken.

The graph is **priority-blind**: like every state-class graph of [VER-010], it expands each
enabled transition whatever its priority. What the check decides is therefore the timed
semantics without priority: a violating class shows a timing-feasible run, not one the
executor's priority-ordered scheduling ([EXEC-003]) must allow, while a closed graph without one
also excludes every prioritized run, since priority only removes runs.

For the quiescence properties the predicate reads "this class has no successor" as "no
transition can ever fire again", and, on a net with a reapable transition, also treats a class
whose enabled transitions are all reapable as resting ([VER-002]). The graph itself fires every
transition on time: it does not hold the runs a late executor takes after a reap, so
`SPURIOUS_UNDER_TIMING` there means that no on-time run reaches a violating rest. On the
[VER-002] AC11 witness the check is `TIMED_CONFIRMED` with the empty trace. On a timed graph that MUST still hold: a class with an enabled
transition has a successor whatever its interval, so a `delayed(5)` transition, whose interval
`[5, ∞)` has no upper bound, still fires out of its class. A graph that dropped such a class's
successors would report a timed deadlock that the net does not have.

**Outcomes.**
- The graph reaches a violating class: `TIMED_CONFIRMED`. The counterexample trace and its
  transitions are **replaced** by the shortest path from the initial class to a violating class,
  a run of the timed semantics **ignoring priority** (the graph of [VER-010] does not order
  transitions by priority), and the report says the trace came from the timed graph. The run is
  timing-feasible, not necessarily one the executor takes: when priority is what keeps the
  executor off the trace (a higher-priority transition always wins the conflict, e.g.
  `hi: A → OK` at priority 10 and `lo: A → BAD` at priority 0, both `delayed(1)`, under
  `unreachable(BAD)`), the result is still `TIMED_CONFIRMED` with the trace `lo`. The path is an
  ordered firing sequence, so `counterexampleConfirmed` reports it confirmed, as for [VER-017]
  AC2.
- The graph closes and no class violates: `SPURIOUS_UNDER_TIMING`. The property holds under
  timing. The untimed trace is kept, and the report says plainly that the counterexample is
  spurious under timing, with the class count. The report MUST also say what that timed claim
  assumes: an on-time executor with atomic firings, one that reaps no transition, fires none
  after its latest bound, and gives an action no duration. A late executor can still reach the
  counterexample (Lean `TimedScg/Retrodict.reaping_escapes_timed_graph`: `t1: p → a` at
  `window(3, 5)`, `t2: p → b` at `delayed(10)`, `unreachable(b)` is `SPURIOUS_UNDER_TIMING`
  while an executor blocked past 5 ms reaps `t1` and marks `b`), and so can an action long
  enough for other firings to interleave with it.
- The graph is truncated at the class budget and its explored prefix violates the property, by
  the rule of [VER-017] ("Verdicts from a truncated graph": any stored class for a safety
  property, only expanded classes without successors for a quiescence property):
  `TIMED_CONFIRMED`, the trace replaced by the shortest path in the explored graph, and the
  report says the timed graph was truncated at `N` classes and the violation found in its prefix.
- The graph is truncated at the class budget with no violation in its prefix, or stopped by the
  total budget or by cancellation ([VER-013]): `TIMED_UNDECIDED`, and the report says which.
  `SPURIOUS_UNDER_TIMING` needs a **closed** graph and never comes from a prefix.

**Why it never changes a verdict.** [VER-004] makes the untimed claim the contract: `Proven`
means the property holds for every run of the untimed abstraction, which implies it for every
timed run. A closed timed graph with no violation establishes only the weaker, timed claim, and
[VER-017] condition 3 forbids a route to return a weaker claim than the route it replaces, which
is why the enumeration route skips timed nets altogether. Turning the `Violated` into `Proven`
would be exactly that substitution; turning it into `Unknown` would withdraw a verdict that is
correct under the contract. The timed claim also rests on the on-time, atomic executor above,
which the executor does not guarantee. So the timed check annotates. `SPURIOUS_UNDER_TIMING` with verdict
`Violated` is not a contradiction: the untimed abstraction violates the property, and the timed
net does not. The route, the invariants and every other field are unchanged, and with the
option off the result and report are byte-identical to a verification without it, apart from
the `counterexampleTiming` field.

**Acceptance Criteria:**
1. The watchdog net (`start: REQ → CALLING`; `answer: CALLING → RESP`, `window(0, 2)`;
   `watchdog: CALLING → TIMEOUT`, `delayed(5)`; one token on `REQ`) under
   `unreachable(TIMEOUT)`: with the check off the result is `Violated`, `UNTIMED_ABSTRACTION`;
   with it on it is `Violated`, `SPURIOUS_UNDER_TIMING`, and the report names the class count.
2. The same net with the watchdog at `delayed(1)`: `Violated`, `TIMED_CONFIRMED`, and the trace
   is the timed graph's shortest path `start, watchdog`.
3. Quiescence on the timed graph. `S → d → X` with `d` at `delayed(5)` and one token on `S`,
   under `deadlockFree` with no sinks: `Violated`, `TIMED_CONFIRMED`, and the replaced trace is
   `d`, not the empty run; the class holding `S` is not a deadlock, because `d` still fires out
   of it. `S → start → A`, `fast: A → DONE` at `window(0, 2)`, `slow: A → STUCK` at
   `delayed(5)`, `DONE` a sink: `Violated` untimed, `SPURIOUS_UNDER_TIMING` with the check on.
4. A class budget below the timed graph's size gives `TIMED_UNDECIDED` when the explored prefix
   holds no violating class; so does a total budget that runs out during the check. When the
   prefix does hold one, the result is `TIMED_CONFIRMED` with the report naming the truncation:
   an unbounded timed producer `gen: G → G, A` at `delayed(1)`, one token on `G`, under
   `placeBound(A, 2)` with a class budget of 50 never closes, and its prefix holds `A = 3` after
   `gen, gen, gen`.
5. With environment places registered, or with match transitions, the check does not run and
   the value is `UNTIMED_ABSTRACTION`; a Route B verdict on a timed net stays `TIMED_EXACT`; an
   untimed net stays `UNTIMED_NET`.
6. The race `t1: p → a` at `window(3, 5)`, `t2: p → b` at `delayed(10)`, one token on `p`, under
   `unreachable(b)` with the check on: the verdict is `Violated`, the value is
   `SPURIOUS_UNDER_TIMING`, and the report says the timed claim assumes an on-time executor with
   atomic firings.
6. No verdict differs between the check on and off, for any net and property.

**Implementation notes:**
- Java: `SmtVerifier.timedCounterexampleCheck(boolean)`; the graph is
  `StateClassGraph.build(..., Options.TIMED)`, the predicate `GraphDecision.decideOverClasses`.
- TypeScript: `SmtVerifier.timedCounterexampleCheck(on: boolean)`; the graph is built with
  `{ untimed: false }`, the predicate `decideOverClasses` (`verification/graph-decision`).
- Rust: `SmtVerifier::timed_counterexample_check(bool)`; the graph is built with
  `StateClassGraph::build_with_options`, the predicate `graph_decision::decide_over_classes`.
- Python: `verify(..., timed_counterexample_check=False)`.

**Depends on:** [VER-003], [VER-004], [VER-006], [VER-010], [VER-013], [VER-014], [VER-017],
[EXEC-042]

**Test derivation:** the watchdog net above with the check off and on (AC1), with the watchdog
made faster than the answer (AC2), and truncated by `enumerationMaxClasses` (AC4); the timed
`deadlockFree` nets of AC3; the watchdog net with an environment
place added (AC5). Two parallel watchdogs close in 10 classes with no `TIMEOUT` marking.

---

## Structural Analysis

#### VER-020: Siphon and Trap Analysis

**Priority:** MAY

The engine may support structural analysis of siphons (sets of places that, once empty, stay empty) and traps (sets of places that, once marked, stay marked).

**Commoner's theorem governs ORDINARY nets only.** The siphon and trap fixpoints are computed
from the pre/post vectors, so they model a net in which the sole reason a transition is disabled
is an input place holding too few tokens. A read arc, an inhibitor arc, a reset arc, a
consume-all input or an arc weight above one is a disablement the fixpoints do not see, and
dropping it yields a strictly **more permissive** net — the wrong direction for a deadlock
proof. An implementation that converts a siphon/trap result into a `Proven` verdict MUST
therefore refuse to do so for any net carrying one of them, exactly as it already refuses when
sinks are declared or environment places are registered. Three witnesses, each a net that is
dead at its initial marking and was reported deadlock-free before the restriction:
`t1: one(a) read(g) → g` with `t2: one(g) → a` from `{a:1}`; `t: exactly(2, a) → a` from
`{a:1}`; `t: one(a) inhibitor(b) → a` from `{a:1, b:1}`.

**Commoner's theorem needs at least one transition.** On a net with no transition every marking
is dead, yet each marked place is a siphon whose maximal trap, the place itself, is marked, so
the condition holds vacuously. An implementation MUST NOT convert the structural result into a
`Proven` for such a net. Witness: one place `a`, no transition, from `{a:1}`; it is quiescent at
once with a token stranded, a `DeadlockFree` violation.

**A structural proof needs every minimal siphon, each with an initially marked trap.**
Commoner's condition quantifies over all siphons; checking the minimal ones suffices, because a
trap inside a minimal siphon lies inside every siphon that contains it. An implementation MUST
therefore find **every** minimal siphon before it concludes "no potential deadlock", and MUST
require each one's maximal trap to hold a token in the **initial** marking; an empty or unmarked
trap is a potential deadlock. Growing a siphon by committing to one input of each producer (the
first, or all of them) is incomplete: it can miss exactly the empty siphon that makes the net
dead. Deciding the condition is co-NP-complete, so the search MAY run under a budget; past it
the result is inconclusive, never a proof. Two witnesses, each dead at its initial marking with
a token stranded: `t1: one(g) one(x) → y, g` with `t2: one(h) one(y) → x, h` from
`{g:1, h:1}` (minimal siphon `{x, y}`); `t1: one(a) one(c) → b, c` with `t2: one(b) → a` from
`{c:1}` (minimal siphon `{a, b}`).

**Acceptance Criteria:**
1. Siphons and traps are identified from the net structure.
2. Results inform deadlock analysis (every siphon containing an initially marked trap ensures
   deadlock-freedom of an ordinary net; liveness only for free-choice nets).
3. A structural `Proven` is offered only for a net with no read, inhibitor or reset arc, no
   consume-all input and no arc weight above one. Each of the three witnesses above returns a
   verdict from a route that models what disables them, never a structural proof. Nor is a net
   with no transition: the one-place witness above is `Violated`, not proven structurally.
4. The siphon search is complete: it finds `{x, y}` and `{a, b}` in the two witnesses above, and
   neither net is proven structurally. A siphon whose maximal trap is empty in the initial
   marking (the ring `a ↔ b` from the empty marking) blocks a structural proof. An exhausted
   search budget yields an inconclusive result.

**Test derivation:** Net with known siphon/trap structure; verify identification.

---

#### VER-021: XOR Branch Analysis

**Priority:** SHOULD

The verifier supports analysis of XOR output branches to identify unreachable branches via state space exploration. Each XOR branch is expanded into a virtual transition for analysis.

**Acceptance Criteria:**
1. XOR branches are expanded into separate virtual transitions.
2. Unreachable branches (those that can never fire given the net structure and initial marking) are identified.

**Depends on:** [IO-012], [IO-016]
**Test derivation:** Net with XOR output where one branch is structurally unreachable; verify identification.

---

## Open-Net Verification

#### VER-022: Open-Net Verification Against a Contract

**Priority:** MAY

An implementation MAY verify a subnet **in isolation**, its ports played by the environment,
against a **contract** stating what the environment does and what the subnet guarantees. A net
built from a fixed vocabulary of subnets is then proven one subnet at a time, each proof costing
what the subnet costs rather than what the composed net's interleavings cost; the composition
argument stays with the caller. Unlike [MOD-051], which wraps a subnet in environment places and
checks each property separately, the contract is judged whole, over a closed net whose
environment runs dry.

**The contract.**
- *Initial marking*: the tokens the subnet holds before anything arrives: its own resources and
  any shared pool it borrows from.
- *Arrival groups*: each delivers between `min` and `max` tokens in total, each onto one of its
  places, at any point of the run. Both bounds are finite: a bound is both the runtime cap and
  the width of the claim.
- *Count clauses*, each named: at every quiescent marking the tokens across the clause's places
  number between `min` and `max`.
- *Rest places*: may hold any number of tokens at quiescence.
- *Designed terminals*: while a terminal's marker holds a token, clause lower bounds are waived
  (upper bounds are not) and the terminal's excused places may hold tokens. The marker itself may
  always rest, as in [VER-014].
- *Environment transitions*: fired by the environment, for a neighbour that reacts to what the
  subnet sends — a tool answering a request, a loop body sending an item back within a budget of
  its own — which an arrival group cannot express because its tokens do not wait for a request. A
  place only environment transitions touch is an **environment place**, the environment's own
  state; a place they share with the subnet is a port.
- *Termination*: every run comes to rest, unless the contract waives it.

A quiescent marking **meets** the contract when every clause holds, lower bounds only while no
terminal marker is marked, and every token lies on a clause place, a rest place, an environment
place, a terminal marker, or an excused place of a marked terminal. The second condition is the
rest set of [VER-014] with the clause, rest and environment places as sinks and each terminal as a
conditional sink, and implementations MUST decide it through that same predicate. Every other
place is internal to the subnet and must be empty.

**Closure.** The subnet is verified as a closed net. Arrival group `i` contributes a source place
holding `min` tokens, a source place holding `max − min`, one transition per target place moving
a token from either source onto it, and a transition with no output that declines a token of the
second source. A run is therefore quiescent only once every required arrival has happened and
every optional one has been delivered or declined. The sources are ordinary places, not the
environment places of [VER-006], which never run dry and would make every quiescence property hold
vacuously.

The contract's environment transitions join the closed net unchanged. Their actions never run, so
one that declares outputs gets a placeholder action instead of a [CORE-043] refusal. Contract
places no arc touches join as places of their own and are listed in the report, so a clause over a
place nothing writes counts zero there: a finding, never a refusal. The closure's names
(`env:arrivals[i]`, `env:optional[i]`, `env:arrive[i]:<place>`, `env:arrive?[i]:<place>`,
`env:decline[i]`) and the environment transitions' names MUST NOT collide with the subnet's, and a
collision is refused.

**Routes.** Both decide the untimed claim of [VER-004].
1. *Graph.* The closed net's state-class graph is built **untimed**: every clock gets the interval
   of `immediate()`, so the graph holds exactly the markings the untimed encoders reason about,
   even for a subnet with timed transitions. When the graph closes within the class budget the
   verdict is exact: every class with no enabled transition is judged, and a reachable cycle is a
   run that never comes to rest. When it does not close, a violation among the explored classes is
   still real, since a class with no enabled transition is quiescent whether or not it was expanded
   and a cycle among explored edges is a real cycle; only the absence of violations needs the
   graph to close.

   The graph route MUST NOT run on a closed net that declares **match (ν-join) transitions**, the
   exclusion of [VER-017] condition 1. The graph is name-blind: it fires a join on tokens whose
   names differ, so it reaches markings the net cannot (the join's output) and misses quiescent
   markings the net reaches (the inputs of a join that never matches), and neither its `proven` nor
   its `violated` can stand. Such a net goes to the SMT route, whose pipeline has exact routes for a
   ν-net ([VER-012]), and the report says why the graph was skipped.
2. *SMT.* When the graph does not close, each part of the contract becomes one query on the closed
   net with every transition `immediate()`, deciding the predicate the graph route reads:
   - stranding: `DeadlockFree`, with the clause, rest and environment places as sinks and the
     terminals as conditional sinks;
   - each count clause: `QuiescentCount` ([VER-002]) over the clause's places and bounds, with
     every terminal marker as a waiver;
   - termination: the ranking of [VER-019] on the closed net, which bounds every run by `r·M0`
     firings. Without a ranking termination is undecided, and the report names the firings the
     marking equation lets repeat.

   The flat encoders ignore timing; a ν-net's exact route ([VER-012]) does not, and on the timed
   net would decide the weaker timed claim.

Both routes read quiescence as [VER-002] does: a class or marking whose enabled transitions are
all reapable ([TIME-013]) rests too. The reapable transitions are named on the closed net before
the SMT route makes every transition `immediate()`. The option `assumeNoReaping` restores the
plain reading, and the report of a closed net with a reapable transition says which reading the
verdict used.

**Verdict.**
- `Proven`: every reachable quiescent marking of the closed net meets the contract and, where
  termination is required, no run fails to come to rest.
- `Violated`: lists every broken part the deciding route found (each clause by name, each stranded
  place by name, and termination), each with a witness. A witness carries the firing sequence from
  the initial marking, environment steps included, the markings along it, and the **port trace**:
  the firings that touch a port or are environment steps (arrivals, declines and environment
  transitions), each marked as such, with the token changes on contract places and on the places
  environment transitions touch. On the graph route a witness is a shortest one, and a termination
  witness is a lasso that marks where its cycle starts. On the SMT route it is the deciding query's
  counterexample, which need not be shortest; one that does not replay as an ordered firing
  sequence ([VER-003]) is marked unconfirmed and names no stranded place.
- `Unknown`: says which parts no route decided, and why.

**Report order.** Names in a result and its report follow the name order of [VER-013]: the places
of every printed marking, the stranded places of the graph route (after the clauses, in contract
order), and the stranded places an SMT stranding violation names.

**Acceptance Criteria:**
1. A subnet that meets its contract is `Proven`. The same subnet with an edge that receives
   neither of its two places is `Violated`: the violation names that edge's clause and
   carries a port trace ending in the quiescent marking.
2. A clause whose upper bound is exceeded is violated whether or not a terminal is marked. A
   lower bound is waived while one is.
3. A token on a place the contract does not name is reported as stranded, and the report
   names the place.
4. A reachable cycle is a `termination` violation with a lasso witness when termination is
   required, and no violation when it is waived.
5. An arrival group that must deliver `n` tokens reaches quiescence only after all `n`; a
   group that may deliver at most `n` also reaches quiescence after fewer.
6. A timed subnet gets the untimed verdict: its class count equals that of the same subnet
   with every transition immediate. On the SMT route, a ν-net whose timing keeps a transition
   from firing is judged as if it could: a stranding only that transition causes is `Violated`.
7. When the graph does not close, the SMT route decides. The result is `Unknown`, naming
   the reason, when that route is disabled or leaves a part undecided.
8. An environment transition's firings are marked as environment steps in the port trace. A
   token left on an environment place is never reported stranded; a place environment
   transitions share with the subnet is judged like any other.
9. A closed net with match transitions is not decided by the graph. On two independently
   minted names reaching a join that requires them equal, the join can never fire and both
   inputs strand: the result is `Violated` on the SMT route, never `Proven` by enumeration, and
   `Unknown` naming the skipped graph when the SMT route is disabled.
10. A subnet that strands places whose locale, UTF-16 code-unit and code-point orders differ
    (`Zeit`, `apfel`, U+E000, U+1F600) lists them in code-point order ([VER-013]), in its
    violations on either route and in the quiescent marking its report prints.
11. The relay `q → relay → out` with `relay` at `window(3, 5)`, one arrival on `q` and the
    clause `out = exactly 1`, is `Violated` on the graph route and on the SMT route: a late
    executor reaps the relay and rests with the token on `q`. With `assumeNoReaping` it is
    `Proven` on both, and the report says the verdict assumes no transition is reaped.

**Cost.** The graph route costs what the closed net's untimed graph costs, which is set by
*reachable combinations*, not size. On a node gadget of the shape a compiled workflow produces
(`typescript/scripts/bench-open-net.ts`) the class count is 30 from 11 places to 59 and from one
outgoing edge to 25, about a millisecond throughout: a node's outgoing edges route together, so
correlated edges add places without adding combinations. Edges that route independently multiply
instead (30, 42, 66, 114, 210, 402, 1554 classes for one to eight). Across 502 compiled node
gadgets the class count is non-monotonic in place count and monotonic in input arity, so an
implementation SHOULD report cost to a user in terms of arity rather than size.

The class count also grows with the **concurrent activations** a subnet admits, and with a budget
place's tokens only while that number exceeds the budget: an arrival is not budget-gated, starting
work is.
- A **join**, whose inputs must all arrive before it fires, runs once whatever the budget and is
  budget-blind (30 classes at arity two and 42 at arity three, identical at budgets one, two, four
  and eight; 464 of 464 join gadgets in the corpus). It still grows combinatorially in arity: 30,
  42, 66 and 210 classes for arities two, three, four and six.
- An **OR**, several producer edges feeding one input, activates once per arrival *that starts
  work* (an arrival routed to a skip path spends no budget), so the budget binds while two or more
  activations can be in flight: a three-arrival OR whose producers can all deliver data has 402,
  516, 546, 546, 546 classes for budgets one to eight, the same subnet with one data producer 228
  at every budget. No gadget of the 502 changes between budgets 4 and 8. Which real OR gadgets are
  budget-sensitive is open: over 31 of them neither producer exclusivity nor a loop-back edge
  predicts it.

An implementation SHOULD describe the claim as blind to the budget above the subnet's
concurrent-activation count, not as unconditional budget-independence. An internal 1-safe mutex
serialising activations adds a 6–13% constant to the class count and does not move that point.

The SMT route costs two to four hundred times as much on the same subnets (193–418 ms from one
edge to eight) and, unlike the graph, grows with size: it is the fallback for a graph that does not
close, not an alternative to one.

**Implementation notes:**
- TypeScript: `verification/open-net`: `verifyOpenNet(net, contract, options)`;
  `OpenNetContract.builder()` (`initialMarking`, `arrive`, `arriveAtMost`, `arriveBetween`,
  `expect`, `expectBetween`, `rest`, `terminal`, `environment`, `requireTermination`);
  `closeOpenNet`; `StateClassGraph.build(…, { untimed: true })`; `rest-set` `strandedPlaces`.
- Rust: behind the `z3` feature, `open_net`: `verify_open_net(&net, &contract, &options)` with
  `OpenNetOptions::default()` and its `with_*` setters (`with_max_classes`, `with_smt`,
  `with_configure_smt`, `with_termination_timeout_ms`, `with_cancel`, `with_assume_no_reaping`,
  `with_assume_atomic_firing`; the struct is `#[non_exhaustive]`);
  `OpenNetContract::builder()` (the TypeScript methods in snake case, plus `initial_tokens`;
  `expect_between` takes `max: Option<usize>`); `close_open_net`;
  `StateClassGraph::build_with_options(…, StateClassGraphOptions { untimed: true })`;
  `rest_set::stranded_places`.
- Python: `verify_open_net(net, contract, *, max_classes=50_000, smt=True,
  termination_timeout_ms=60_000, ...)`; the remaining keywords (`timeout_ms`, `linear_bound`,
  `state_equation`, `state_equation_phase`, `firing_bound`, `semiflow_invariants`, `cancel`,
  `assume_no_reaping`, `assume_atomic_firing`, `mint_transitions`) configure each SMT query as
  for `verify`. `OpenNetContract.builder()` as in Rust, places as varargs, unbounded
  `max` as `math.inf`. Results: `OpenNetResult`, `ContractViolation`, `PortStep`.
- Java: `org.libpetri.smt.opennet`: `OpenNetVerifier.verifyOpenNet(net, contract, options)` with
  `OpenNetOptions(maxClasses, smt, configureSmt, terminationTimeout, assumeNoReaping,
  assumeAtomicFiring)` (the four- and five-argument constructors remain, and
  `OpenNetOptions.DEFAULT.with...()` changes one option); `OpenNetContract.builder()`
  (the TypeScript methods plus `initialTokens`; `expectBetween` takes an `OptionalInt` `max`);
  `OpenNetClosure.closeOpenNet`;
  `StateClassGraph.build(…, StateClassGraph.Options.UNTIMED)`; `RestSet.strandedPlaces`. Results:
  `OpenNetResult`, `ContractViolation`, `ContractViolation.PortStep`. Contract places are matched
  to the net's by name, although Java `Place` equality also compares the token type.
- Every implementation's report is byte-identical to TypeScript's.

**Depends on:** [VER-002], [VER-004], [VER-006], [VER-010], [VER-014], [VER-017], [VER-019]

**Test derivation:** Use a node gadget: one input edge carrying data or empty, one output with
two edges, a shared budget, and a halt that inhibits start and skip. Its contract is proven.
Then check that each defect breaks the named part:
- a skip that writes only the first edge's empty violates the second edge's clause;
- a run that writes both data and empty on one edge violates that clause's upper bound;
- a done that keeps the budget violates the budget clause;
- a transition that re-marks its own input is a termination violation;
- without the terminal, a halt strands the arrival.

For environment transitions, use a node that sends a request and runs again on each answer.
Its environment answers at most twice, from a budget of its own, or ends the exchange. The
contract is proven with termination required, the budget the environment leaves unspent is
not stranded, and the environment's firings are marked in the port trace.
