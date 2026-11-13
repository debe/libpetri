<!-- Generated from lean/Libpetri/Spec/Text/Chapter/Ch07.lean and the requirement texts it lists, by lean/spec-tools/Render.lean. Do not edit: edit the Lean source, then run `lake env lean spec-tools/Render.lean` from lean/. -->
# 07 — Verification

This document specifies formal verification capabilities: SMT/IC3 safety proofs, state class graph analysis, and structural analysis.

---

## SMT Safety Verification

#### VER-001: SMT Verification Pipeline

**Priority:** SHOULD
**Kind:** F

The engine supports safety property verification using SMT solvers via the IC3/PDR (Property Directed Reachability) algorithm. The implementation notes list the phases of the SMT route; their order describes the implementations and is not a requirement.

**Undeclared marked places are inert places.** An initial marking MAY put tokens on a place the
net does not declare; the executor retains them, inert ([CORE-072] AC3). Verification models the
same net the executor runs, so every place the initial marking marks that the net does not
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

*When* the verifier verifies a net from an initial marking, it *shall* verify the net whose places are the declared places followed by every place the initial marking marks that the net does not declare, in the order the marking lists them, and whose transitions are the net's own, with no arc added.

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

**Timeout outcomes are virtual transitions.** The verifier expands a transition into one virtual
transition per way a firing can end: each output branch the action may write ([IO-016], one
token per place), in enumeration order, then the **timeout outcome** when the spec has a
`Timeout` and that outcome deposits differently from every branch. The timeout outcome is
what the executor deposits when the timeout fires ([IO-013] AC5, [IO-014]): the timeout
child's places only, one minted token each, and for a `ForwardInput(from, to)` one token in
`to` per token consumed from `from`, which is the required count of a `One` / `Exactly(n)` input.
Every analysis that fires a transition whose `Timeout` forwards no `All` / `AtLeast` input reads
this one expansion: the flattener behind the
encoders, the linear bound ([VER-015]), the state equation ([VER-016], [VER-018]), the firing
bound ([VER-019]), the bounded witness phase ([VER-025]), the enumeration route ([VER-017]),
Route B and the ν fragment ([VER-012]), the name-coloured encoder ([NU-053]) and open-net
closure ([VER-022]). A virtual transition is
named after its transition alone when there is one, and `<t>_b<i>` when there are several. A
forward from an `All` / `AtLeast` input deposits the drained batch, which depends on the
marking the firing drains: a **transfer**. The graph routes fire each class's marking, so
they count the drained batch exactly as the executor does: the enumeration route
([VER-017]), the timed state-class graph ([VER-010]) and Route B ([VER-012]) decide such a
net. No post vector holds it, so every route that reads the flat net (the structural
pre-check ([VER-020]), the P-invariants ([VER-005]), the linear bound ([VER-015]), the state
equation ([VER-016], [VER-018]), the firing bound ([VER-019]), the bounded witness phase
([VER-025]), the fixpoint query and Route A ([NU-053])) refuses it with `Unknown`. The refusal
sits after the graph routes and before the first linear one, so no exit of the pipeline bypasses it ([VER-003] AC5).

*When* the verifier expands a transition that has an output spec and no `Timeout` that forwards an `All` or `AtLeast` input, it *shall* produce one virtual transition per output branch the action may write, in enumeration order, then one virtual transition for the timeout outcome when the spec has a `Timeout` and that outcome deposits differently from every branch.

The verifier *shall* expand a transition with no output spec into one virtual transition that deposits nothing.

The virtual transition of the timeout outcome *shall* deposit one token in each place the `Timeout` child names through `Place` and, for each `ForwardInput(from, to)` of the child, as many tokens in `to` as the required count of the input on `from`.

The verifier *shall* name a virtual transition `<t>` when its transition `t` has one virtual transition, and `<t>_b<i>` when it is the `i`-th of several, counting from 0.

*If* the `Timeout` of a transition forwards an `All` or `AtLeast` input, *then* no route *shall* read an expansion of that transition into virtual transitions.

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
   `t_b0` (post `c`), `t_b1` (post `b`) and `t_b2` (post `2·b`). The linear bound ([VER-015])
   reads the same three virtual transitions and does not prove `PlaceBound(b, 1)`, which is
   `Violated` with a one-step trace ending at `{b: 2}` on the state-equation phase ([VER-018]),
   the fixpoint query and the enumeration route ([VER-017]).
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
- The SMT route runs these phases in this order. Route B ([VER-012]), the linear bound when the
  enumeration route applies ([VER-015]), the enumeration route ([VER-017]) and the refusal of a
  drained forward run before them.
  1. **Flatten XOR**: expand each transition into its virtual transitions
  2. **Structural pre-check**: the siphon/trap check ([VER-020])
  3. **P-invariant computation**: derive place invariants from the incidence matrix ([VER-005])
  4. **Pre-fixpoint phases**: the linear bound ([VER-015]), the state-equation phase ([VER-018]),
     the firing-bound phase ([VER-019]) and, on the flat encoding, the bounded witness phase
     ([VER-025]), each of which can decide the property before the fixpoint query
  5. **SMT encoding**: encode the Petri net as CHC (Constrained Horn Clauses)
  6. **IC3 query**: invoke the Z3 Spacer engine for reachability analysis
  7. **Decode result**: extract verdict, counterexample, or inductive invariant
- All implementations: full pipeline; the CHC system is emitted as SMT-LIB2 text and solved by
  the `z3` executable with `fp.engine=spacer` through the one solver transport of [VER-013].
- Rust: behind the `z3` feature. Python exposes the Rust pipeline via the PyO3 binding (wheel
  built with the `z3` feature).

**Depends on:** [CORE-072]
**Test derivation:** Simple mutual exclusion net; verify Proven verdict for mutual exclusion property. The AC3 net at enumeration budgets 0, 1 and the default, plus `PlaceBound(a, 0)`, and the same net without the stray token. The AC4 net on every route, and its flattened rows; the AC5 nets at budget 0 (refused) and the default (decided both ways).

---

#### VER-002: Safety Properties

**Priority:** SHOULD
**Kind:** F

**Quiescence.** Every property below that speaks of a quiescent marking reads it
**reap-aware**. A transition is *reapable* when its timing is `Deadline` or `Window`: an
executor that is late past its latest bound plus the tolerance reaps it ([TIME-013]), leaves
its input tokens where they are, and does not arm it again until a firing or an injected token
writes one of its arc places. A late executor can therefore come to rest at a marking that still enables a
reapable transition (Lean `ReapingVsUntimed.reaping_refutes_ver004_ac3`). A marking is
**quiescent** when every transition whose enablement check passes on it is reapable. On a net without a reapable
transition this is the plain reading, no transition enabled, and every script, verdict and
report is what it was before reaping was accounted for. "All transitions disabled" in the
error conditions below means "every transition that is not reapable is disabled".

Every route reads this one quiescence (AC7). The encoders leave a reapable
transition out of the quiescence clause of `Bad`, on the fixpoint query, the certificate
check, the [VER-018], [VER-019] and [VER-025] phases and Route A alike. A graph route treats an expanded
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
  places where coming to rest is permitted. Without a conditional sink declaration
  ([VER-014]), the error condition is: (all transitions disabled) ∧ (some marked place is
  not a declared sink). A quiescent marking violates
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
- **Unreachable(places)**: the given set of places is never all simultaneously non-empty.
  The set is assumed non-empty: the property is not specified over an empty one.
- **QuiescentCount(places, min, max, waivedBy)**: every reachable quiescent marking holds
  between `min` and `max` tokens across `places`; the lower bound is waived while any
  `waivedBy` place holds a token, the upper bound never. The error condition is: (all
  transitions disabled) ∧ ((Σ < min ∧ every `waivedBy` place empty) ∨ Σ > max). With a
  designed-terminal marker ([VER-014]) as waiver, a halted run need not refund its budget but
  never holds more than there is. A place listed twice in `places` is counted once.

  `max` MAY be unbounded, represented however the implementation chooses (the representation
  is not observable). An unbounded `max` MUST contribute no upper-bound clause to the encoding
  and MUST render without an upper bound in the report, so implementations emit the same
  script. `min` MUST be a non-negative integer and a bounded `max` MUST be an integer at least
  `min`; a call of the `QuiescentCount` constructor function (named under Implementation notes) breaking either MUST be
  rejected where it is made, as the language reports a caller's error, rather than yield a verdict. A value built
  without that function, such as a Rust enum literal or a TypeScript object literal, is not checked. `min = 0` with `max` unbounded holds on every marking: an
  implementation MAY skip its query and SHOULD then report that it did, so a skipped clause is
  distinguishable from one that passed.
- **NameAligned(S)** and **QuiescentNameAligned(S)**, for a non-empty list `S` of coloured places:
  the places of `S` together hold at most one distinct name, in every reachable marking or in every
  reachable quiescent one. They read token names, so only Route B decides them and no other route
  gives them a verdict ([NU-055]).

The two sink-sensitive properties are not ordered by strength; they **invert on the empty
marking**. A quiescent `{done:1, stuck:1}` with `done` a sink violates DeadlockFree (it
strands `stuck`) but satisfies TerminatesAtSink. The fully drained marking `{}` satisfies
DeadlockFree (nothing is stranded) but violates TerminatesAtSink (no sink was reached).
Neither subsumes the other, which is why both exist.

The verifier *shall* read a marking as quiescent exactly when every transition whose enablement check ([NU-020]) passes on it is reapable, and, under `assumeNoReaping`, exactly when no transition's enablement check passes on it.

*When* the verifier decides `DeadlockFree`, it *shall* report a marking as a violation exactly when the marking is quiescent and some marked place of it is stranded in the sense of [VER-014].

*When* the verifier decides `TerminatesAtSink`, it *shall* report a marking as a violation exactly when the marking is quiescent and no declared sink holds a token.

*When* the verifier decides `MutualExclusion` over a list of places, it *shall* report a marking as a violation exactly when two entries of the list, at different positions, hold a token.

*When* the verifier decides `PlaceBound(place, k)`, it *shall* report a marking as a violation exactly when the place holds more than `k` tokens.

*When* the verifier decides `Unreachable` over a non-empty list of places, it *shall* report a marking as a violation exactly when every listed place holds a token.

*When* the verifier decides `QuiescentCount(places, min, max, waivedBy)`, it *shall* report a marking as a violation exactly when the marking is quiescent and either the tokens across `places`, each place counted once, number fewer than `min` while every `waivedBy` place is empty, or they number more than a bounded `max`.

*If* the `QuiescentCount` constructor function is called with a `min` that is negative or not a whole number, or with a `max` that is not a whole number or is below `min`, *then* the call *shall* be rejected where it is made.

*When* the `QuiescentCount` constructor function is called with a whole non-negative `min` and a `max` that is unbounded or a whole number at least `min`, the call *shall* yield the property with those bounds.

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
9. **QuiescentCount** with a negative or non-integral `min`, or a non-integral `max` or one
   below `min`, is rejected at construction. Two implementations given the same unbounded `max` emit the same
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
**Kind:** B

The verification result includes:

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

The verifier *shall* return `Proven` with a proof method that is not empty, `Violated`, or `Unknown` with a reason that is not empty.

The places a property of [VER-002] names are the places of `MutualExclusion`, `PlaceBound` and `Unreachable`, and the places and the `waivedBy` places of `QuiescentCount`; the sinks of `DeadlockFree` and `TerminatesAtSink` and the places of a conditional sink declaration ([VER-014]) are not among them, since a sink or marker the net does not hold is never marked and excuses nothing.

*If* a property names a place that the net does not declare, the initial marking does not mark and no rewrite of the verified net adds (the in-flight places of [VER-004], the arrival sources of [VER-006]), *then* the verifier *shall* return `Unknown`, whatever any route would answer.

*If* the verified net cannot be built (the in-flight split of [VER-004] refuses the net, or the premise check of `Bounded(k)` of [VER-006] fails), *then* the verifier *shall* return `Unknown`.

A configuration error is not a verified net that cannot be built. A name that the `Arrivals` closure of [VER-006] would add and that the net already declares, or an `ArrivalsBetween` mode with `max < min`, is rejected with an exception (a panic in Rust) before any route runs, not with a verdict.

*When* the verdict is `Violated` and `counterexampleConfirmed` is `true`, the verifier *shall* report a trace that is a firing sequence of the verified net from the initial marking to a marking that violates the property.

*When* the initial marking violates the property and the verdict is `Violated`, the verifier *shall* report the empty firing sequence, with `counterexampleConfirmed` not `false`, and `true` unless Route B or the name-coloured encoding of [NU-053] decided it.

The verifier *shall* return `Proven` only when no marking reachable from the initial marking in the untimed abstraction of the verified net ([VER-004]) violates the property.

On a ν-net, a `Proven` of Route B is the claim of [VER-012]: where its graph keeps a latest bound (under `assumeNoReaping`, or on a direct call on a timed net), the claim holds for an on-time executor whose actions take no time.

*When* the verifier reports a P-invariant, on any route, its weighted token sum *shall* equal its constant on every marking reachable from the initial marking in the untimed abstraction of the verified net.

The verifier *shall* report a `counterexampleTiming` exactly when the verdict is `Violated`, and `UNTIMED_NET` exactly when every transition of the net is `immediate`.

*When* the verdict is `Violated` and some transition of the net is not `immediate`, the verifier *shall* report `TIMED_EXACT` if Route B decided it, and `UNTIMED_ABSTRACTION` if another route decided it while the timed check of [VER-023] is off.

*When* the verdict is `Proven` or `Violated`, the verifier *shall* name the route that decided it, which is not `Unavailable`.

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
untimed warning.

---

#### VER-004: Untimed Over-Approximation

**Priority:** SHOULD
**Kind:** B

SMT verification operates on untimed Petri net semantics (marking projection, integer token counts). Timing only restricts which firings happen: every timed firing is an untimed one, and a reap ([TIME-013]) changes no marking, so every marking a timed run visits is reachable in the untimed net (Lean `ReapingVsUntimed.timed_markings_reachable`). A proof of a property of the marking alone on the untimed net therefore holds for the timed net (`marking_properties_transfer`).

Timing does add one thing the untimed net lacks: a place to **rest**. A late executor reaps a `Deadline` or `Window` transition and stops at a marking that still enables it, a marking the untimed net does not count as quiescent (`reaping_refutes_ver004_ac3`: `p0 → t → p1`, `t = window(3, 5)`, rests at `{p0}` with the token stranded while the untimed `DeadlockFree` is `Proven`). The untimed abstraction MUST include this, so every quiescence property reads quiescence reap-aware ([VER-002]): a marking where every enabled transition is reapable counts as quiescent. With that reading, a proof on the untimed net is sound for every timed run, a late one included. `assumeNoReaping` restores the plain reading; a `Proven` under it holds only for an on-time executor, one that reaps no transition and lets no armed transition pass its latest bound, and the report says so.

**Atomic firings and in-flight actions.** Every route reads a firing as one atomic step: its inputs leave and its outputs arrive in the same step. The executor does not fire that way. It consumes a firing's inputs when the action starts and deposits the outputs when the action completes ([EXEC-001] steps 5 and 1), and it fires other transitions in between. An asynchronous action keeps that gap open while it runs ([CONC-002]). A synchronous one keeps it open to the end of its firing pass, because a drain later in the same pass does not see the deposit ([EXEC-003] AC5). For monotone arcs the gap changes nothing: a run with `t` in flight can be reordered so that `t`'s deposit follows its start at once, because the steps in between only see more tokens in `t`'s output places, and a transition that needs tokens stays enabled and does the same. It does change something when a transition tests one of `t`'s output places **non-monotonically**: an inhibitor arc, a reset arc, or a draining input (`all`, `atLeast`). A terminal place ([EXEC-042]) counts too, since it inhibits every transition. With `t: one(p) → p` and an async action, and `u: one(q) + inhibitor(p) → bad`, `p` is never empty in any atomic run from `{p, q}`, so `Unreachable(bad)` was `Proven`; the executor fires `u` while `t` is in flight. With `start: one(req) + inhibitor(busy) → busy` and two requests, `PlaceBound(busy, 1)` was `Proven` too, and two guarded transitions sharing `busy` both start.

The untimed abstraction MUST therefore model the two-step firing for every transition `t` with an output place (in any branch, the `Timeout` branch included) that some transition tests non-monotonically. Such a `t` is **split** into:
- `t` itself, with every input, read, inhibitor and reset arc, its timing, priority and match spec, whose only output is a fresh place `inflight:<t>`, and
- `complete:<t>`, `immediate()`, with the one input `one(inflight:<t>)`, no other arc, `t`'s priority and `t`'s output spec, in which a `forwardInput(from, to)` leaf deposits into `to`.

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

Each firing the executor takes under its timing *shall* be a firing of a transition of the untimed net, from the same marking to the same marking.

A reap ([TIME-013]) and the passing of time *shall* change no marking.

*Where* the transitions of a net have distinct names, a marking at which a timed run from the initial marking ([TIME-010]) rests, with no transition it enables armed, *shall* be quiescent as [VER-002] reads quiescence by default: every transition it enables is reapable.

*Where* the transitions of a net have distinct names, a marking at which an on-time run from the initial marking ([TIME-010]) rests, one that reaps no transition and lets no armed transition pass its latest bound, *shall* enable no transition.

A place is tested non-monotonically when it is a terminal place, when some transition has an inhibitor arc, a reset arc or an `all` or `atLeast` input on it, or when one of the two readings below counts it so.

*If* the property is a `QuiescentCount` with `min > 0` and the net has a terminal place its waiver places do not name, *then* the verifier *shall* count the property's places and its waiver places as tested non-monotonically.

*While* conflict priority applies, the verifier *shall* count the input and read places of every pruning transition, one with strictly higher priority than another transition that shares an input place with it, as tested non-monotonically.

*While* `assumeAtomicFiring` is not set, the verifier *shall* split exactly the transitions that model no environment, are not a completion step (a transition named `complete:<x>` whose one input is `one(inflight:<x>)` and that has no read or reset arc), and either are pruning transitions while conflict priority applies or have an output place, in any branch with the `Timeout` branch included, that is tested non-monotonically.

The verifier *shall* replace each split transition `t`, at its position in the transition order, by `t` with every input, read, inhibitor and reset arc and its timing, whose only output is the place `inflight:<t>`, directly followed by `complete:<t>`, `immediate()`, whose one input is `one(inflight:<t>)`, which has no other arc, and whose output spec is that of `t` with each `forwardInput(from, to)` leaf replaced by the place `to`.

The places of the split net *shall* be the places of the net followed by `inflight:<t>` for each split transition `t` in the transition order, and every transition that is not split *shall* stay as it is.

*If* no transition is to be split, *then* the verifier *shall* verify the net as it is.

*If* a transition to split is a ν-join, writes a coloured place, has a `Timeout` that forwards an input whose cardinality is not `one`, or would add a name the net already uses for a place or a transition, *then* the verifier *shall* refuse the split with a reason that opens with `transition '<t>'` for the first such transition `t` in the transition order, and *shall* answer `Unknown` on every route.

*While* `assumeAtomicFiring` is not set, *if* conflict priority applies, the net has a pruning transition, and a transition the verifier would split under conflict priority cannot be split, *then* the verifier *shall*, instead of refusing the split, turn conflict priority off for that call and split the net as it does without conflict priority.

*While* `assumeAtomicFiring` is set, the verifier *shall* verify the net as it is and *shall* keep conflict priority as it applies.

*While* `assumeAtomicFiring` is not set and the split succeeds, *where* no firing fails (no action fails, and output validation and the relay check reject no output or timeout outcome), no action publishes an output before it completes and no token is injected, a marking the executor reaches from the initial marking, with each action in flight of a transition that is not split completed with one of its outcomes, *shall* be reachable in the split net from the initial marking, with one token on `inflight:<t>` for each action of a split transition `t` in flight.

**Acceptance Criteria:**
1. The flat routes read no timing bound: of a transition's timing they read only whether it is
   reapable ([VER-002]). Route B ([VER-012]) keeps each earliest bound, and each latest bound only
   under `assumeNoReaping`.
2. Verification is value-blind — value-dependent branch and correlation choices are
   over-approximated (except the [NU-020] name-equality carve-out of [NU-050], when
   implemented).
3. A Proven verdict on the untimed net implies the property holds for all timed executions,
   including those of an executor that runs late and reaps a transition ([TIME-013]), with
   quiescence read as [VER-002] defines it. Under `assumeNoReaping` a Proven verdict holds for
   the timed executions of an on-time executor, in which no transition is reaped and no armed
   transition passes its latest bound, and the report states that assumption. On Route B
   ([VER-012]), which keeps the latest bounds under `assumeNoReaping`, a firing is also one
   instant step, so the verdict holds only for an executor whose actions take no time. The
   report says so, and a closed graph is called exact only for such an executor: with `t: a →
   p` at `deadline(20)` and a 150 ms action, `h: p + b → ok` at `deadline(20)` and `v: b → bad`
   at `delayed(60)`, beside a ν pair, `Unreachable(bad)` is `Proven` under `assumeNoReaping`
   with that label, `Violated` by default, and the executor marks `bad`.
4. A Proven verdict holds for the executor's runs with actions in flight whose actions publish no
   output before they complete (no `ctx.flush()`): every transition
   whose output some transition tests non-monotonically is verified as its start and
   `complete:<name>`, and the report names the split transitions. From `{p, q, go}`, with
   `t: one(p) + one(go) → p` whose action is asynchronous, `u: one(q) + inhibitor(p) → r` makes
   `Unreachable(r)` `Violated`, and `u` with `reset(p)`, `all(p)` or `atLeast(2, p)` instead
   makes `MutualExclusion(p, r)` `Violated` (from two and three tokens on `p` for the two
   drains). The executors reach the same markings.
5. A net with no such transition produces byte-identical scripts, with or without
   `assumeAtomicFiring`.
6. A ν-join or coloured writer that needs the split, and a `Timeout` forward from an input that is
   not `one` that needs it, give `Unknown` on every route, naming the transition. Under
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
**Kind:** F

The verifier computes place invariants (P-invariants) from the net's incidence matrix. A P-invariant is a nonzero weight vector `w` such that `w · M = constant` for all markings M reachable in the untimed abstraction of the verified net ([VER-004]).

P-invariants provide structural proofs that do not require state enumeration.

*When* the SMT pipeline ([VER-003]) builds its CHC encoding, the verifier *shall* compute the P-invariants of the verified net from the net's incidence matrix, with one injector column for each environment place into which it models injection ([VER-006]).

The verifier *shall* report a nonzero weight vector `w` with a constant `c` as a P-invariant only when the product of `w` with every column of that incidence matrix is zero and `w · M = c` holds on every marking `M` reachable in the untimed abstraction of the verified net ([VER-004]), injections included.

*When* the verifier computes the P-invariants of a net that has a transition and in which no transition has a reset arc, an `All` input or an `AtLeast` input, it *shall* report P-invariants such that every weight vector of zeros and ones over the net's places whose product with every column of that incidence matrix is zero is a rational linear combination of their weight vectors.

*When* the verifier computes P-invariants, it *shall* list each one it reports in the verification result, with its weights and its constant.

**Acceptance Criteria:**
1. P-invariants are computed from the incidence matrix.
2. Each invariant satisfies `sum(weights[i] * marking[i]) = constant` for all markings reachable in the untimed abstraction of the verified net ([VER-004]).
3. Invariants are reported in the verification result.

**Test derivation:** Net with known invariant (e.g., token conservation); verify invariant is discovered.

---

#### VER-006: Environment Analysis Mode

**Priority:** SHOULD
**Kind:** B

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
  the mode is built, and a mode value written directly (a Rust enum variant) is refused before any
  route runs
- **Ignore** — environment places are not modeled

The default mode of the SMT verifier is `AlwaysAvailable`, and this requirement binds that
verifier and every route it dispatches to. The state-class graph API takes `AlwaysAvailable`,
`Bounded(k)` and `Ignore`, defaults to `Ignore`, and refuses `Arrivals`, which only the SMT
verifier applies, as a net rewrite.

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
and quiescence mean what they mean on a closed net, none of the `Ignore` refusals below applies,
and the vacuity note below arises only as it does on a closed net, from a transition that is not
reapable and has no input, read or inhibitor arc. Consequences a caller sees:

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

**The mirror-image vacuity.** Under `AlwaysAvailable`, and under `Bounded(k)` when the cap
meets the demand, an input or read arc on an environment place is no reason a transition is
disabled. A transition with no inhibitor arc whose every input and read arc is such an arc has no
reason left: it is enabled, through injection, in *every* marking, so **no marking is quiescent**
and every quiescence property (`DeadlockFree`, `TerminatesAtSink`, `QuiescentCount`,
`JoinedOrDeadLettered`) is unviolatable. A transition that also needs a token of an ordinary
place, or carries an inhibitor arc, keeps a reason, so quiescent markings can exist beside it. The
`Proven` this yields is correct
and carries no information about the net: an open net with an always-available source never
comes to rest, so "no reachable quiescent marking strands a token" holds whatever the net does.
Unlike the `Ignore` case this is not refused, because the verdict is true; but an implementation
MUST report it, so a caller cannot read the empty claim as a guarantee about their workflow.
`QuiescentNameAligned` ([NU-055]) is the exception: where no marking can be quiescent it is
`Unknown` (AC6). Under a mode that models injection an environment place is an ordinary place for
the rest set of [VER-014]: a token left on it is stranded unless the caller declares the place a
sink, as the closure of [VER-022] does.

Because `Ignore` does not model injection, a safety property that holds **only** because
environment-gated transitions never fire is vacuous, and the verifier cannot tell which properties
hold only for that reason. When environment places are registered and the mode does not model
injection (`Ignore`), the verifier MUST NOT return `Proven` for any property: it reports `Unknown`
(with a reason) instead of silently certifying.

This binds **every route that can return `Proven`**, not only the SMT encoding. An
implementation that decides some properties structurally — the name-partition state-class graph
of [NU-050], say — reaches a verdict without ever building an encoding, and a structural
exploration under `Ignore` treats an environment place as an ordinary place that simply starts
empty. The bound it certifies then holds for exactly the reason this requirement rejects. Only
`Proven` is refused. A `Violated` of a reachability-safety property (`MutualExclusion`,
`PlaceBound`, `Unreachable`) under `Ignore` is a real counterexample in a strictly smaller
reachable set, so it is a fortiori a counterexample in the injected one. A `Violated` of a
quiescence property under `Ignore` is a rest of the net while the environment stays silent, which
need not be a rest under `AlwaysAvailable` or `Bounded(k)`: on `env IN → T → OUT` the empty
marking marks no sink, so `TerminatesAtSink({OUT})` is `Violated` under `Ignore`, while under
`AlwaysAvailable` no marking is quiescent and the property is `Proven` with the vacuity note.

*While* the mode is `AlwaysAvailable`, the verifier *shall* treat as reachable every marking the executor reaches while the environment injects tokens into the environment places.

*While* the mode is `Bounded(k)` and the two premises of AC3 hold, the verifier *shall* treat as reachable every marking the executor reaches while the environment keeps at most `k` tokens resident in each environment place.

*While* the mode is `Bounded(k)`, the verifier *shall* not treat as reachable a marking that holds more than `k` tokens on an environment place, from an initial marking that holds at most `k` on each one.

*While* the mode is `Bounded(k)`, the premise check *shall* pass exactly when the initial marking holds at most `k` tokens on each registered environment place and no transition deposits into one.

*If* the mode is `Bounded(k)` and the premise check fails, *then* the verifier *shall* return `Unknown` naming the environment place and the broken premise, and *shall* run no route.

*While* the mode is `AlwaysAvailable` or `Bounded(k)`, an input or read arc on an environment place *shall* not count as a reason a transition is disabled, unless the mode is `Bounded(k)` and the arc demands more than `k` tokens, in which case the transition *shall* count as permanently disabled.

*While* the mode is `AlwaysAvailable` or `Bounded(k)`, the verifier *shall* treat a marking as quiescent exactly when every transition that is not reapable is permanently disabled or has a disabling reason that holds at the marking. A marking quiescent in this sense that is reachable with injection, from an initial marking that holds at most `k` tokens on each environment place under `Bounded(k)`, enables no transition, and no sequence of injections makes it enable one.

The verifier *shall* report the vacuity note only for a quiescence property, and only when some transition of the verified net that is not reapable is neither permanently disabled nor has a disabling reason left under the mode, an input or read arc on an environment place being a reason under `Ignore` and `Arrivals`, which model no injection, and an inhibitor arc that the terminal rewrite of [EXEC-042] adds being a reason in every mode.

*While* the mode is `AlwaysAvailable` or `Bounded(k)` and environment places are registered, *when* the property is a quiescence property and some transition of the verified net that is not reapable is neither permanently disabled nor has a disabling reason left (an inhibitor arc that the terminal rewrite of [EXEC-042] adds is a reason), the verifier *shall* report the vacuity note with a `Proven` or `Violated` verdict.

*While* the mode is `Arrivals(min, max)`, the verifier *shall* verify the net closed with a mandatory source holding `min` tokens and an optional source holding `max − min` tokens for each environment place, so that a marking of the net is reachable in the closed net exactly when the environment reaches it with at most `max` arrivals on each environment place, and is a dead marking of the closed net exactly when it is reached with at least `min` arrivals on each environment place and enables no transition of the net.

*If* environment places are registered and the mode is `Ignore`, *then* the verifier *shall* not return `Proven`, on any route.

*When* the mode is `Ignore` and the verdict is `Violated` with `counterexampleConfirmed` `true`, the trace *shall* be a firing sequence of the verified net without injection to a marking that violates the property.

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
   `QuiescentNameAligned` ([NU-055]) is the exception: it is `Unknown` instead.
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

**Depends on:** [VER-002], [VER-003], [VER-004], [VER-012], [VER-014], [VER-017], [VER-022], [NU-050], [NU-051], [NU-055]

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
**Kind:** F

The verifier's encoders conjoin every accepted conservation law `y·M = y·M0` into the
transition-rule bodies of the CHC/IC3 encoding ([VER-004], [VER-005]). A law is accepted only
by the **exact gate**: `y·C = 0` against the incidence matrix and `y·M0 = c` are re-checked in
exact (overflow-checked) integer arithmetic, and `y` MUST carry zero weight on every place a
transition consumes with `all()` / `atLeast(n)` or clears with a reset arc, because the
encoder's fire relation is not linear there (Lean `Strengthening.lean`, hypotheses H1/H2;
injected environment places are covered by [VER-006], H3'). A law that fails the gate is
dropped from the encoding and listed in the report.

The encoders *shall* receive a conservation law only when the law passed the exact gate: `y·C = 0` against every column of the incidence matrix, each column counting every token its flat transition deposits and the injector columns of [VER-006] included, and `y·M0` equal to the law's constant, both in exact integer arithmetic, and zero weight on every place a transition consumes with `all()` / `atLeast(n)` or clears with a reset arc.

The encoders *shall* receive every basis row of [VER-005] that passed the gate, whatever the option's setting.

A law whose weights or exact sums leave the implementation's integer range fails the gate with a weight-overflow reason. Every implementation's range holds a law whose weights, and the sum of the absolute values of the terms of each of its sums `y·C` and `y·M0`, are at most `2^31 − 1`.

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
cost (27 s of preprocessing on a 24-layer net before the solver sees anything), and on a wide
net an **uncatchable** one, since the heap it exhausts aborts the process rather than returning a
verdict. An implementation MUST compute semiflows only when the option is on, or is `auto` and the
gate dropped a basis row for its weight on a consume-all or reset place. No other phase
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

*While* the option is off, the encoders *shall* receive exactly the basis rows that passed the gate.

*While* the option is on, the encoders *shall* receive exactly the basis rows and the enumerated semiflows that passed the gate.

*While* the option is `auto`, the encoders *shall* receive what they receive with the option on when the gate dropped a basis row for its weight on a consume-all or reset place, and what they receive with the option off otherwise.

*If* the option is off, or it is `auto` and the gate dropped no basis row for its weight on a consume-all or reset place, *then* the verifier *shall not* compute the semiflows.

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
3. Under `auto` the report says which way it went and why, the union happens exactly when the
   gate dropped a basis row for its weight on a consume-all or reset place, and the verdict never differs from whichever explicit setting `auto` chose. The
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
   states. (Not every such net: a semiflow already present in the basis dedups away, and AC4
   admits `N = 0`, in which case the two scripts are identical.) This is about what the encoder
   receives, not about certification: AC5's certificate check is flat-path only, and a coloured
   `Proven` reports `  Certificate check: not applicable (name-coloured encoding)`.

**Implementation notes:**
- Java: `SmtVerifier.semiflowInvariants(boolean)` and `semiflowInvariants(SemiflowMode)` (`OFF`, `ON`, `AUTO`).
- TypeScript: `SmtVerifier.semiflowInvariants(enabled | 'auto')`.
- Rust: `SmtVerifier::semiflow_invariants(impl Into<SemiflowMode>)`: a `bool`, or `SemiflowMode::Off`, `On` or `Auto`.
- Python: `verify(..., semiflow_invariants=True)`, or `semiflow_invariants="auto"`.

**Depends on:** [VER-004], [VER-005], [VER-006], [NU-050], [NU-053]

**Test derivation:** a budgeted work loop with one reset arc on a side place, whose null-space
basis folds the reset place into the loop's law: a `placeBound` on the loop is proven only with
the option; a bound the loop genuinely exceeds stays `Violated` with it. For AC7, the same loop
beside a budget-declared ν-net, with the reset arc on the uncoloured half (the coloured encoder
refuses a reset on a coloured place, and the net would silently fall back to the flat encoding):
the encoded script must report itself coloured and must differ between the option's two states.

---

#### VER-013: Solver Transport

**Priority:** SHOULD
**Kind:** B

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
certificate script and its detail re-run each receive the full budget. The formula is fixed for a
`timeout_ms` of at least 1. A timeout of 0 is outside it: Java and TypeScript raise it to 1 ms, so
that `-t:0`, which `z3` reads as no limit, never reaches the solver, and Rust passes `-t:0`.

**Total budget.** Because the timeout is per invocation, one `verify()` can run for several times
it: the bound query ([VER-015]), the state-equation phase shared across its refinements
([VER-018]) and its certificate check and detail re-run, the firing-bound phase at half the
timeout ([VER-019]), the bounded witness phase at an eighth of it ([VER-025]), the HORN query and
its certificate check and detail re-run add up to about 7.6 timeouts, plus 2 s of watchdog slack per process, plus the solver-free work (the enumeration
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
  solver-free loops (siphon and trap search, Farkas, the colour-slot simplex, the trim of the
  bounded witness phase [VER-025]) poll the deadline,
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
  the whole timeout however long the pre-fixpoint phases of [VER-018], [VER-019] and [VER-025]
  took; under a total budget it gets what they left.

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
`ranking`, `bmc` ([VER-019]), `witness` ([VER-025]), `horn`, `horn-coloured`, `certificate`,
`certificate-detail`.

**Reply classification.** The verdict is the first stdout line equal to `sat`, `unsat` or
`unknown`, wherever it appears: a build may print a warning first, and the HORN script's paired
`(get-proof)` / `(get-model)` always yields one `(error …)` line. Under the HORN query
`(assert (not Error))`, `sat` is `Proven` and `unsat` is `Violated`. Without a verdict line the
`Unknown` reason is, in this order: the `timeout` line printed by the `-T` backstop; the watchdog
kill; the first `(error …)` line on stdout, then on stderr; any other stderr text; the unexpected
stdout itself. A verdict line decides whatever else the reply carries, an `(error …)` line or a
non-zero exit included. The certificate script requires exactly three positional answers; an `(error …)`
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

**The transport, as EARS sentences.**

*When* the verifier starts a `z3` process with a timeout of `t` milliseconds, `t` at least 1, it *shall* pass `-t:t` and, as `-T`, the smallest whole number of seconds that is at least `(t + 1000) / 1000`, and *shall* kill the process at `t + 2000` milliseconds if it has not exited.

*While* a total budget is set, the verifier *shall* give each `z3` process the smaller of its normal timeout and the whole milliseconds that remain, and *shall* start no process when none remain.

The verifier *shall* read the verdict of a reply off the first stdout line that, trimmed, equals `sat`, `unsat` or `unknown`, wherever that line appears.

*If* no stdout line of a reply is a verdict line, *then* the verifier *shall* give as the reason of the failure the first of these that applies: a `timeout` line on stdout, the watchdog kill, the first `(error …)` line on stdout and then on stderr, any other stderr text, the stdout itself.

*If* a `z3` process gives no verdict line, or no process is started, *then* the step that asked for it *shall* read the failure as no answer, so a step that proves a property only on a solver answer *shall not* return `Proven` from it.

*When* the poll made on entering a step finds the total budget spent or the call cancelled, the verifier *shall* charge the stop to the step that was running before, *shall* not enter the new step, and *shall* end the pipeline without a verdict.

*While* a stop is recorded, the verifier *shall* start no `z3` process, enter no step and reach no verdict.

*When* a stop is recorded, the verifier *shall* keep a `Proven` or `Violated` reached before it, and *shall* give an `Unknown` the reason `total verification budget of <N> ms exhausted during <phase>` or `verification cancelled during <phase>`, `<phase>` the step the stop was charged to.

*While* no total budget is set and the caller does not cancel, the verifier *shall* record no stop.

**Acceptance Criteria:**
1. The same net, marking, property and options produce byte-identical HORN and certificate
   scripts in every implementation (the golden scripts under
   `spec/verification-fixtures/scripts/`).
2. A missing executable yields `Unknown` with a reason naming the command tried and
   `LIBPETRI_Z3`; no exception escapes and the host process survives.
3. An executable below 4.8.0, or one whose `--version` reports no version, yields `Unknown`
   naming both versions (or the reply).
4. A reply without a verdict line yields `Unknown` with the reason of the reply classification
   above: a `timeout` line, a process that never exits (the watchdog kill), an `(error …)` on
   either stream, other stderr text and unexpected stdout each give a distinct reason, and no
   solver process is left behind. A verdict line decides even when an `(error …)` line or a
   non-zero exit comes with it; in the certificate check either makes the check inconclusive.
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
**Kind:** F

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

The verifier *shall* read a token in place `p` of a marking `M` as stranded exactly when `p` is not a declared sink, `p` is not the marker of any conditional declaration, and every conditional declaration that names `p` has its marker unmarked in `M`.

*When* the verifier decides `DeadlockFree`, it *shall* report a quiescent marking as a violation exactly when some marked place of it is stranded.

*When* the verifier decides `TerminatesAtSink`, it *shall* report a quiescent marking as a violation exactly when it would without any conditional declaration.

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
5. Every route that decides `DeadlockFree` reads the same rest set, among them the flat
   encoder, the name-coloured encoder, the certificate check's safety condition, the abstract
   counterexample replay, the ν name-partition graph ([VER-012]), the enumeration route
   ([VER-017]), the state-equation phase ([VER-018]) and open-net verification ([VER-022]); the
   four implementations emit byte-identical scripts for the same declarations ([VER-013] AC1).

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
**Kind:** F

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
demands, one per pair: it is proven when every pair's demand is separated, each pair with its own query.

The weighting for each demand is found by one `QF_LIA` query through the solver transport of [VER-013]
(phase `bound`): variables `y_p ≥ 0` per flat place, `y_p = 0` on every consume-all / reset
place (H1) and every injected environment place (H3'), one row `Σ_p C[p][t]·y_p ≤ 0` per flat
transition, and `Σ_p d_p·y_p ≥ 1 + Σ_p M0_p·y_p`. A `sat` model is **re-checked in exact
integer arithmetic** (`y ≥ 0`, the zero weights, every row, the demand) before it is
believed; a model that fails the check is discarded. `unsat`, `unknown` and any transport
failure hand over to the next phase of the dispatch. The phase is skipped under `Ignore` with
environment places registered ([VER-006] AC4) and for the quiescence properties, whose
violation is not a linear demand. A ν-net's verdict receives the [NU-050] over-approximation
note like any other flat proof.

The verifier *shall* accept a weighting `y` for a demand `d` in the exact re-check only when `y_p ≥ 0` on every flat place, `y_p = 0` on every consume-all, reset and injected environment place, `Σ_p C[p][t]·y_p ≤ 0` for every flat transition `t`, and `Σ_p d_p·y_p ≥ 1 + Σ_p M0_p·y_p`, and *shall* accept every weighting that meets these conditions when every weight, and the sum of the absolute values of the terms of each of these sums, is at most `2^127 − 2`.
A weighting whose sums overflow the implementation's integer arithmetic is rejected; that costs a proof and never makes one.
In the re-check, `C[p][t]` is the number of tokens the flat transition `t` deposits on `p` minus the number its input on `p` requires, which for a consume-all input (`all`, `atLeast`) is its required minimum.

The verifier *shall* take as the demands of a property one demand `m_p ≥ 1` on every listed place for `Unreachable`, one demand `m ≥ 1` on the entries at positions `i` and `j` for every pair of positions `i < j` of a `MutualExclusion` of two or more entries, in lexicographic order of `(i, j)`, and one demand `m_q ≥ k + 1` on the bounded place `q` for `PlaceBound` and `BranchPlaceBound` with bound `k`.
A `MutualExclusion` of fewer than two entries is never violated ([VER-002]), so its demands are left to the implementation and every choice is sound.

*When* the verifier runs the bound phase on a property, it *shall* return `Proven` exactly when, for every demand of the property, the query returned a `sat` model whose weighting the exact re-check accepts for that demand.

The verifier *shall not* return `Violated` from the bound phase; every outcome of the phase other than `Proven` hands over to the next phase of the dispatch.

*When* the bound phase proves the property, it *shall* return `Proven` with method `structural`, an empty counterexample trace and no `counterexampleConfirmed`.

A property with a demand is a `PlaceBound`, `BranchPlaceBound`, `MutualExclusion` or `Unreachable` property; the name-alignment properties of [NU-055] have no demand.
The verifier *shall not* run the bound phase on a property without a demand, while the phase is disabled, or under `Ignore` with environment places registered.
The verifier *shall* run the bound phase at most once in one verification call.
The verifier *shall* send the `bound` query of each demand at most once in one verification call.
The verifier *shall not* run Route B ([VER-012]) after the bound phase, and *shall not* run the bound phase after the colour-slot bound of the coloured encoding ([NU-053]) or after the fixpoint query.
*When* the bound phase is enabled and the verifier runs the colour-slot bound or the fixpoint query on a property with a demand, not under `Ignore` with environment places registered, it *shall* have run the bound phase earlier in the same call.
*When* the bound phase is enabled and the verifier runs the enumeration of [VER-017] on a property with a demand, and the enumeration route applies to a net with no drained forward, it *shall* have run the bound phase earlier in the same call, and *shall not* run the bound phase after the enumeration.
*When* the bound phase runs ahead of the enumeration and does not prove the property, the next phase the verifier runs *shall* be the enumeration.
On a net where the enumeration route does not apply, or that has a drained forward, the verifier *shall not* run the bound phase before the enumeration.

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
query, whose verdict and notes are unchanged. The coloured plan is built only after the bound
fails to prove; nothing before it reads the plan. Route B ([VER-012]) keeps its place in the
dispatch: the bound runs after it, never before. The colour-slot bound of the coloured encoding
counts coloured tokens rather than names, often two to four times the declared budget, and IC3 over that
many colour slots can time out on a bound the flat state equation proves in milliseconds. On six
PNID ν-nets (`research/net-metrics/validation/pnid/`), `placeBound(X, 1000)` under a budget of 2
went from `Unknown` after about 8 s to `Proven` in about 12 ms.

**On nets the enumeration route takes, the phase runs before it.** When the enumeration route of
[VER-017] applies to a net with no ν-join (untimed, no environment places, a positive class
budget) and the net has no drained forward ([IO-014], [VER-001] AC5), the bound runs **before**
the enumeration, not after it. One query costs milliseconds; a graph that does not close costs the
whole class budget before the bound is reached. Measured on a 134-transition composed agent net
whose graph exceeds the budget: about 17 s per `placeBound` claim at a budget of 200 000 classes,
several minutes at 5 000 000, and under 0.1 s with the bound first. A bound that proves returns
as in AC1, with the report line of [VER-017] AC3 for the invariants it did not compute. Anything
else falls through to the enumeration, and the fixpoint query later does not send the `bound`
query again. When the solver cannot be started, the early bound sends no query and hands over
with a report line, and the enumeration runs without a solver, as it did before; the `Unknown` with route `Unavailable`
of [VER-013] comes only from the later phases. On every other net the phase keeps the slot above.

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
**Kind:** B

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
relation, whose only counter knowledge is the increment. The certificate check is on by
default; with it disabled (`certificateCheck(false)` in Java and TypeScript,
`certificate_check(false)` in Rust, `certificate_check=False` in Python) a `Proven` rests on
the solver's answer alone, and the report carries
`  Certificate check: not applicable (disabled)` in place of the check. The counterexample
decoder reads a fact's marking from its leading `P` arguments. The option does not apply to
the name-coloured encoding ([NU-050]) or to Route B ([VER-012]); the report says so on the
name-coloured path only, and a run that a route or phase decides before the fixpoint query
prints no state-equation line.

*While* the state-equation option is enabled, the initial fact of the flat CHC encoding *shall* set every firing counter to 0.

*While* the option is enabled, the rule of each transition *shall* fire that transition only where it is enabled, with the effect it has in the untimed abstraction of [VER-004], add one to its firing counter and copy every other counter, each environment-injection rule *shall* add one token to its place and copy every counter, and no rule but these and the initial fact *shall* derive a `Reachable` fact.

*While* the option is enabled, each transition rule *shall* require of its successor `(M', n')`, for every place that is not injected, the equality `m'_p = M0_p + Σ_t C[p][t]·n'_t` where no consume-all or reset arc clears the place, and the upper bound `m'_p ≤ M0_p + Σ_t C[p][t]·n'_t` where one does.

*While* the option is enabled, apart from the P-invariant conjuncts of [VER-005] and [VER-007] and the environment bounds of [VER-006], the rule of each transition *shall* accept its firing from every state `(M, n)` in which the transition is enabled and whose successor meets the rows above, and each environment-injection rule *shall* accept its injection from every state, so the rows remove no reachable state.

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
net that has one.

---

#### VER-017: Bounded State-Space Enumeration Route

**Priority:** SHOULD
**Kind:** B

Before the SMT pipeline ([VER-001]), an implementation SHOULD try to decide the property by
**enumerating the state-class graph** ([VER-010]) up to a class budget. When the graph closes
with fewer classes than the class budget, the verdict is read off it directly and no solver runs
for the enumeration; when it does not, the route declines and the SMT pipeline runs unchanged. A reachability-safety property first tries
the linear bound of [VER-015], which runs ahead of this route.

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
2. **No environment places** are registered on the net the route receives. The graph does not
   model injection ([VER-006]), so a verdict about an open net would not mean what the encoders'
   does. A net closed under `Arrivals` ([VER-006]) has none left, and the route applies to it.
3. The net is **untimed** — every transition `immediate`. The graph carries firing domains, so on
   a timed net it would explore only the runs the timing admits and its `proven` would be the
   weaker *timed* claim; [VER-004] fixes the untimed proof as the stronger one, and a route MUST
   NOT quietly return a weaker claim than the route it replaced. On an untimed net no domain
   excludes anything, so the graph explores exactly the untimed reachable set.
4. The class budget is positive. Setting it to `0` disables the route.

**What the verdict means.** Exact — sound *and* complete. A `violated` is a real firing sequence
along a shortest path, in the graph the route built, from the initial class to the class it
reports, not a possibly-spurious
over-approximation, so it needs no replay: implementations report `counterexampleConfirmed` as
confirmed (AC2), since the path is itself an ordered firing sequence of the untimed abstraction
([VER-003]). Its `counterexampleTiming` is `UNTIMED_NET`, as the route runs only on untimed nets
(condition 3). A `proven` is the
same claim the encoders make, decided by enumeration rather than by search. The route decides the
**same predicate** as every other route ([VER-002] AC7, [VER-014]); implementations MUST share
one predicate implementation between this route and [VER-012]'s rather than restate it.

Unless the total budget runs out or the caller cancels ([VER-013]), the route can only add
verdicts, never remove them: on truncation the SMT pipeline runs exactly as before, unless the explored prefix already violates the property (below), so no query that the
solver could decide becomes `unknown`.

**Verdicts from a truncated graph.** A graph cut off at the class budget is not thrown away. Every
class it stored is a real reachable class, and the builder explores breadth-first, so no class it
stored later is nearer to the initial class, in the graph it built, than a class it stored earlier. On
truncation the route therefore runs the **same shared predicate** over the explored prefix, with
one restriction on which classes count:

- **Safety properties** (`placeBound`, `branchPlaceBound`, `unreachable`, `mutualExclusion`): every
  stored class counts, expanded or not.
- **Quiescence properties** (`deadlockFree`, `terminatesAtSink`, `joinedOrDeadLettered`,
  `quiescentCount`, and any other property that reads "this class has no successor"): only classes
  the builder **expanded** and found without successors count, where a step of a reapable
  transition ([VER-002]) is not counted as a successor. A frontier class, stored but never
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

**Reusing the state space across queries.** The graph depends only on the net, the in-flight
split of [VER-004], the initial marking and, under [VER-024], whether the graph is reduced. The property, the sinks and the conditional sinks only *read* it. A caller that asks many
questions of one net would otherwise rebuild the same graph for every question. When the graph
exceeds the budget, every question pays the full attempt before it falls through. Measured on a
47-place, 54-transition agent net whose graph exceeds the default budget: 3–4.6 s per query with
the route, 17–24 ms without it; 5 183 claims took more than 15 minutes instead of 149 s.

An implementation SHOULD therefore offer an explicit **state-space cache** that the caller creates,
passes to each verification, and owns: `StateSpaceCache` / `stateSpaceCache(cache)`. Without one,
behaviour is exactly as above. With one:

- An entry is keyed by the caller's net, the transitions the in-flight split of [VER-004] rewrote,
  the initial marking, and, under [VER-024], whether the graph is reduced. Under `Arrivals` the key
  also covers the closure of [VER-006] (the registered environment places in registration order
  and the mode), or the verifier does not use the cache for that query and the report says so:
  two queries on one net and marking that register different environment places verify different
  closed nets. The split changes the graph: under `assumeAtomicFiring` the net stays
  atomic, and otherwise a transition whose output another tests non-monotonically becomes two
  steps. A key without the split would let a graph of the atomic net answer a query that runs on
  the split one, and that `Proven` can be wrong. The inert-place, split and terminal ([EXEC-042])
  rewrites are a deterministic function of the net and the transitions split, and the `Arrivals`
  closure one of the net, the registered environment places and the mode, so with the clause above
  the rest of the key is the net as the caller passed it. An implementation may key on the split net instead. An
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
- The verdict, the witness and the route are the same with and without the cache, with two
  exceptions: a query at a budget below `B` that hits a remembered truncation at `B` checks the
  larger remembered prefix, and a query at a budget of `C` or less that hits a closed graph of `C`
  classes checks that whole graph as a prefix, so either can find a violation an uncached query
  at its own budget would not reach. Such a violation is still a real firing sequence; it never turns a verdict into
  `Proven`. The report says when a cached graph, or a cached truncation, was used.
- Concurrent verifications that share a cache build a given entry once. The others wait for it
  rather than build their own. While a larger budget rebuilds a truncated entry, a budget of `B` or
  less still declines at once rather than wait.
- A build that fails leaves the entry as it found it: absent, or the truncation it was replacing.
  The failure reaches the query that ran the build. Queries waiting on it do not inherit the
  failure: each looks again, and declines, reuses or builds as its own budget requires.
- The cache holds its graphs until the caller drops it or clears it. It never shares memory the
  caller did not ask for.

**The route, as EARS sentences.**

The enumeration route *shall* apply exactly when the net it receives, after the rewrites of [VER-006], [VER-004] and [EXEC-042], declares no match transition, has no environment place registered and has only `immediate` transitions, and the class budget is positive.

An applying route runs unless an earlier step of the pipeline decided or refused the query: the linear bound of [VER-015], Route B for a name-alignment property ([VER-012], [NU-055]), the refusals of [VER-003], [VER-004] and [NU-010], or a stop of [VER-013].

The build *shall* be stopped only when the total budget runs out or the caller cancels ([VER-013]).

*While* the build is neither stopped by the total budget nor cancelled ([VER-013]), the state-class graph *shall* be closed exactly when it has fewer classes than the class budget.

The state-class graph *shall* hold the initial class as its first class, and only classes reachable from it.

*When* the graph is closed, the route *shall* return `Proven` exactly when no marking reachable from the initial marking violates the property, and `Violated` otherwise.

*While* the build is neither stopped by the total budget nor cancelled ([VER-013]), the route *shall* return `Violated` when a counted class violates the property, where a counted class is any stored class for a safety property and a class the builder expanded for a quiescence property.

*When* the route returns `Violated`, it *shall* report a counted class that violates the property, and a firing sequence from the initial marking to the marking of that class that is a path, in the graph the route built, from the initial class to that class.

*When* the route returns `Violated`, the firing sequence it reports *shall* be no longer than any path, in the graph the route built, from the initial class to a counted class that violates the property.

The route *shall not* return `Proven` from a graph that is not closed, and *shall* read nothing off a graph whose build was stopped by the total budget or cancelled.

*When* the route returns `Proven` or `Violated`, the verifier *shall* return that verdict and *shall not* run the SMT pipeline.

*If* the route does not run, or the graph is truncated and no counted class violates the property, *then* the verifier *shall* continue with the rest of the pipeline exactly as it does without the route, except that the time the route took counts against a total budget ([VER-013]).

*If* the build is stopped by the total budget or cancelled, *then* the verifier *shall* return the `Unknown` of [VER-013].

**The state-space cache, as EARS sentences.**

*When* a state-space cache is passed, the verifier *shall* key each entry by the caller's net, the transitions the in-flight split of [VER-004] rewrote, the initial marking and whether the graph is reduced ([VER-024]), and a query *shall* read and write only the entry of its own key.

*While* the mode is `Arrivals(k)` or `Arrivals(min, max)` of [VER-006] and environment places are registered, *when* a state-space cache is passed, the verifier *shall* either key each entry also by the closure (the registered environment places in registration order and the mode), or not use the cache for that query and say so in the report.

*When* an entry holds a closed graph of `C` classes, a query at a budget greater than `C` *shall* reuse it, and a query at a budget of `C` or less *shall* read it as an explored prefix, in both cases without building.

*When* an entry holds a truncation remembered at budget `B`, a query at a budget of `B` or less *shall* read its explored prefix without building.

*When* an entry is empty, or holds a truncation remembered at a budget smaller than the query's, the query *shall* build at its own budget, and the entry *shall* then hold a closed graph as closed, a truncated graph with the query's budget, and, after a build stopped by the total budget or cancelled, what it held before.

*If* a build fails, *then* the entry *shall* stay as the build found it, and the failure *shall* reach the query that ran the build.

A query *shall* read a graph it built or reused as the route reads it without the cache, and a graph it read as an explored prefix as a graph that is not closed.

**Acceptance Criteria:**
1. On an untimed net whose state-class graph closes with fewer classes than the budget, the
   property is decided by the graph, unless the bound of [VER-015] proved it first: the report names the route and its class count, and carries no solver phase
   other than the `bound` phase of [VER-015], which a reachability-safety property tries first.
2. A violated verdict carries a counterexample trace whose transition sequence is a real firing
   sequence from the initial marking to the witnessing class, reported as **confirmed**: the
   graph path is a firing sequence, so it is ordered by construction and there is nothing to
   replay. A consumer keying "are these steps ordered" off that field is correct without
   special-casing the route.
3. The result names this route and reports that P-invariants were not computed, so an empty
   invariant list is not mistaken for "the net has none".
4. Exceeding the budget produces a report line naming the budget and, unless the explored prefix
   violates the property, falls through to the SMT pipeline, whose behaviour is unchanged.
5. The route is skipped for a ν-net, for a net with environment places after the rewrites of
   [VER-006], for a timed net, and when the budget is `0`; in each case the report carries no
   enumeration section, and the verdict is that of the rest of the pipeline.
6. Where both routes can answer, they return the same verdict for the same net and property.
7. With a state-space cache, a later query with the same key (net, in-flight split, initial
   marking, reduced or full graph, and under `Arrivals` the closure) at the same budget builds no
   graph, and returns the same verdict, witness and route as a query without the cache. Under
   `Arrivals` this holds for a query the cache serves; an implementation that does not use the
   cache there builds on every query and says so in the report.
8. A cached truncation at budget `B` makes a query at budget `≤ B` answer from the remembered
   prefix without building: `Violated` when the prefix violates the property, otherwise a decline.
   A query at a larger budget builds, and replaces the entry. A cached closed graph of `C` classes
   answers a query at a budget of `C` or less from the whole graph read as a prefix, without
   building, and never with `Proven`.
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
- Java: `org.libpetri.smt.ScgVerifier`; `SmtVerifier.enumerationMaxClasses(int)`. A transition
  with the deprecated `Timing.Unconstrained` counts as timed there, so a net using it skips the
  route in Java only; the rest of the pipeline gives the same verdict.
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
- Under `Arrivals` ([VER-006]) the implementations differ. Java and TypeScript do not use the
  cache for a query whose `Arrivals` closure closes the net, and the report says so, with the same
  line in both (`SmtVerifier.java` and `smt-verifier.ts`, the enumeration step). Rust and Python
  key the fingerprint of the closed net, so the closure is in the key and a repeated query hits.

**Depends on:** [VER-001], [VER-002], [VER-003], [VER-004], [VER-006], [VER-010], [VER-012],
[VER-013], [VER-014], [VER-015], [VER-024], [EXEC-042]

**Test derivation:** a pipeline `p0 → t0 → p1 → … → pn`, untimed: `deadlockFree` with `pn` a sink
is proven by enumeration with `n+1` classes and no solver phase; without the sink it is violated
with the firing sequence `t0 … t(n-1)`. The same net with a class budget at or below the graph size
reports truncation and is answered by the SMT pipeline; with the budget `0` the route never runs.
A `delayed` variant of the same net is skipped as timed. For AC6, the same query with and without
the route returns the same verdict. For AC11, an untimed net with an unbounded producer
(`gen: G → G, A`) and `placeBound(A, 2)` under a class budget of 50 is `Violated` by the route with
the trace `gen, gen, gen`, where it used to fall through; `deadlockFree` on the same truncated
graph falls through.

---

#### VER-024: Stubborn-Set Reduction of the Enumeration Route

**Priority:** SHOULD
**Kind:** B

The enumeration of [VER-017] explores every interleaving. A net that forks one token into `k`
independent subnets therefore has a state space close to the **product** of the subnets' spaces,
although each subnet closes alone in a few hundred classes. Measured on a 134-transition composed
agent net that forks into six independent subnets (3 to 404 classes each): about 3 000 000
classes explored in 600 s without closing. A quiescence property only asks about the classes
where nothing is enabled, and the order in which independent transitions fire does not change
which dead markings are reachable. On such a property the route SHOULD therefore expand, at each
class, only the enabled transitions of a **stubborn set** (Valmari's deadlock-preserving
reduction), which brings the graph close to the **sum** of the subnets' spaces.

**When the reduction applies.** All of:

1. The enumeration route of [VER-017] runs (no ν-join, no environment places, untimed, positive
   class budget).
2. The property is a **quiescence property**: `deadlockFree`, `terminatesAtSink`,
   `joinedOrDeadLettered` or `quiescentCount`. Each reads only the classes without successors.
   Safety properties keep the full graph; their violations need not be dead.
3. The net has no drained forward ([IO-014]); its marking-dependent deposits are outside the
   model the reduction is proven on.
4. The reduction is enabled. It is on by default; `partialOrderReduction(false)` turns it off.

**Footprints.** The reduction reads the net the graph is built on (after the inert-place,
in-flight split of [VER-004] and terminal rewrites of [EXEC-042]). For a transition `t`, taking
every outcome of every branch ([VER-021]) together:

- `tests(t)`: its input, read and inhibitor places.
- `writes(t)`: its input and reset places and every place an outcome deposits into.
- `overwrites(t)`: its reset places and its consume-all inputs (`all`, `atLeast`), whose new count
  does not depend on the old one.

Two transitions `t ≠ u` are **dependent** when `writes(t) ∩ tests(u)`, `writes(u) ∩ tests(t)`,
`overwrites(t) ∩ writes(u)` or `overwrites(u) ∩ writes(t)` is non-empty. Independent transitions
enabled together stay enabled after either fires, and firing them in either order reaches the same
marking. A transition that can **increase** `p` is one with an outcome depositing into `p`; one that
can **decrease** `p` has `p` among its inputs or resets.

**The stubborn set at a class with marking `M`.** For a seed transition `s` enabled at `M`, the
closure `S(s)` is the least set containing `s` such that, for every `t ∈ S(s)`:

- (D1) if `t` is enabled at `M`, every transition dependent with `t` is in `S(s)`;
- (D2) if `t` is disabled at `M`, take its **first unsatisfied condition**, over its input and
  read places in code-point order of place name, then over its inhibitor places in code-point
  order: an input or read place `p` with too few tokens
  puts every transition that can increase `p` into `S(s)`; a marked inhibitor place `p` puts every
  transition that can decrease `p` into `S(s)`.

The route computes `S(s)` for every enabled seed and keeps the one with the **fewest enabled
transitions**, the code-point-smallest seed name breaking ties, and expands only that set's enabled
transitions, each with all of its outcomes. The choice is a function of the marking and the net,
so every implementation builds the same reduced graph, with the same class count.

**What the verdict means.** Unchanged: exact for the quiescence property. Every class of the
reduced graph is reachable, and every dead marking reachable in the full graph is reachable in the
reduced one: a run to a dead marking must fire a transition of the set (an enabled member that no
transition outside it can disable would otherwise still be enabled at the end), and the first such
firing commutes to the front. A class has no reduced successor exactly when nothing is enabled at
it, so the classes the reduced graph reports quiescent are exactly the reachable dead markings.
A `violated` is a real firing sequence and stays confirmed ([VER-017] AC2), but it is the shortest
path **in the reduced graph**, which may be longer than the shortest run of the net. A truncated
reduced graph is read as in [VER-017]: a violation in its expanded prefix stands, and no truncated
graph yields `Proven`.

**State-space cache.** A reduced graph answers only quiescence properties, so the cache of
[VER-017] keys it apart from the full graph of the same net and marking: a safety query never
reads a reduced entry, and a quiescence query with the reduction off never reads one either.

*While* the enumeration route of [VER-017] runs on a quiescence property (`deadlockFree`, `terminatesAtSink`, `joinedOrDeadLettered` or `quiescentCount`), on a net without a drained forward ([IO-014]), with the reduction enabled, the route *shall* build the reduced graph.

*If* the property is not a quiescence property, the net has a drained forward or the reduction is disabled, *then* the route *shall* build the full graph of [VER-017].

Every implementation *shall* turn the reduction on by default.

*While* the reduction applies, *when* the route expands a class whose marking `M` enables a transition, it *shall* expand exactly the enabled transitions of `S(s)` for the enabled seed `s` whose closure has the fewest enabled transitions, the code-point-smallest seed name breaking ties.

*When* a transition `t` of `S(s)` is disabled at `M`, the closure *shall* read its first unsatisfied condition over its input and read places in code-point order of place name, then over its inhibitor places in code-point order.

*While* the reduction applies, the route *shall* expand the transitions it selects at a class in ascending code-point order of transition name.

*When* the route expands a class, it *shall* expand only enabled transitions, each with all of its outcomes.

*While* the reduction applies, every dead marking reachable from the initial marking *shall* be reachable by a run that fires, at each class, one of the transitions the route expands there.

*While* the reduction applies, a class *shall* have no reduced successor exactly when no transition is enabled at its marking.

The cache of [VER-017] *shall* key a reduced graph apart from the full graph of the same net and initial marking, so that a safety query, and a quiescence query with the reduction off, never read a reduced entry.

**Acceptance Criteria:**
1. On every net and quiescence property of the conformance corpus, the verdict with the reduction
   equals the verdict without it, and every `violated` trace replays.
2. A net that forks one token into `k` independent cycles of length `n` closes in at most
   `1 + k·n` classes with the reduction and `1 + n^k` without it, with the same verdict.
3. A safety property builds the full graph whatever the setting, with the same verdict, witness
   and class count as before.
4. With `partialOrderReduction(false)` the graph, the witness and the class count are those of
   [VER-017].
5. The class count of a reduced graph is the same in every implementation.
6. When the reduction ran, the report contains the line `Stubborn-set reduction (VER-024): on`
   beside the class count of [VER-017] AC1; its indentation is not fixed.

**Implementation notes:**
- TypeScript: `verification/analysis/stubborn-sets`; `SmtVerifier.partialOrderReduction(enabled)`.
- Java: `org.libpetri.analysis.StubbornSets`; `SmtVerifier.partialOrderReduction(boolean)`.
- Rust: `libpetri-verification` `stubborn_sets`; `SmtVerifier::partial_order_reduction(bool)`.
- Python: `verify(..., partial_order_reduction=True)`.

**Depends on:** [VER-004], [VER-017], [VER-021], [EXEC-042], [IO-014]

**Test derivation:** `fork: start → s0_0 … s(k-1)_0`, and per subnet a cycle
`s(i)_j → s(i)_(j+1 mod n)`. `deadlockFree` is proven with `1 + n` classes reduced (every seed's
set has one enabled transition, so the tie-break keeps advancing the first subnet) against
`1 + n^k` full. Replacing each cycle by a chain ending in `s(i)_n` makes the end
marking dead: `deadlockFree` is violated with a trace of `1 + k·n` firings in both modes, and with
every `s(i)_n` a sink it is proven. A reset arc on a place another subnet deposits into makes the
two subnets dependent, so the reduction keeps both orders.

---

#### VER-018: State-Equation Phase with Refinement

**Priority:** SHOULD
**Kind:** B

Before the fixpoint query, the verifier asks one `QF_LIA` query (phase `state-equation`, through
the transport of [VER-013]): can a marking that satisfies the marking equation of [VER-016]
violate the property? The equation is `m = M0 + C·n` over firing counts `n ≥ 0`, with an upper
bound on a place a consume-all or reset arc clears and no row for an injected place; the
violation is encoded exactly as the error rule of [VER-001] encodes it. Every reachable marking
satisfies the equation for the counts of its run, so `unsat` proves the property. Unlike
[VER-015] the query asks for the violation directly, so it covers every property, quiescence
included.

*When* the state-equation query answers `unsat`, the phase *shall* end with a proof over the refinements it has added so far.

*If* the state-equation query fails in the transport, answers `unknown`, gives a model that cannot be decoded, or the timeout runs out before its answer, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.

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

*When* the state-equation query answers `sat`, the phase *shall* first run the witness search on the candidate, and *shall* return `Violated` with the run the search reports before it tries any refinement.

The witness search *shall* fire each flat transition at most as often as the candidate's counts allow, under the exact abstract semantics of [VER-004] and with no injection step, and *shall* report a run only when every step is enabled and the last marking violates the property.

A run the witness search reports *shall* be no longer than any other run within the counts that ends in a violating marking.

The witness search *shall* report that no violating run exists only when it has completed, no run within the counts ends in a violating marking, and no environment place is declared for injection.

*While* environment places are declared for injection, the phase *shall* still run the witness search, and the search *shall* report the same run it reports on the same net without injection.

*If* a run within the candidate's counts ends in a violating marking, *then* the witness search *shall* report a run whenever its node budget is large enough.

The trap search *shall* return a set `Q` of places of the flat net only when every flat transition that can take a token from `Q`, through an input arc, a consume-all input or a reset arc, also puts a token into `Q`, some place of `Q` is marked in `M0`, and the candidate leaves every place of `Q` empty.

The trap search *shall* return a trap whenever some initially marked trap among the places of the flat net is empty in the candidate.

The exact re-check *shall* accept an inequality `a·M ≤ b` only when it holds at `M0` and every firing and every injection step of the exact step relation keeps it.

The exact re-check *shall* accept an inequality `a·M ≤ b` that holds at `M0`, gives no injected place a positive weight, and for which every flat transition that can fire, taken from the least marking its guard allows, passes the keep test or the restore test: the keep test, that the firing does not raise `a·M` and every place the firing clears without inhibiting has a weight of at least 0; the restore test, that the marking after the firing meets the bound and every place the firing neither clears nor inhibits has a weight of at most 0.

*When* the witness search reports no run and the phase has added fewer refinements than the refinement limit, the phase *shall* settle the candidate in this order: with `Σ_{q∈Q} m_q ≥ 1` when the trap search returns a trap `Q`; otherwise with the inequality the `invariant` query returns, marked inductive, when the exact re-check accepts it and the candidate violates it; otherwise, when that query answers `unsat`, with the inequality the same query returns with the marking equation as a premise of every step, marked relative, when the candidate violates it.

*When* the phase adds a refinement, it *shall* ask the state-equation query again with every refinement added so far.

*If* no trap and no inequality settles the candidate, an inequality fails the exact re-check or holds at the candidate, or an `invariant` query fails in the transport, answers `unknown`, gives a model that cannot be decoded, or the timeout runs out before its answer, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.

Every trap and inductive refinement holds in every reachable marking, and a relative one does too
when the solver's answer is right, since it is inductive together with the equation; so the query
is asked again and a later `unsat` is still a proof. The phase steps aside, leaving the pipeline unchanged, when nothing
settles a candidate, after 32 refinements, on a transport failure, or when the timeout runs out.

*If* the witness search reports no run on a candidate after the phase has added as many refinements as the refinement limit, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.

The refinement limit *shall* be 32 in every implementation.

The node budget of one witness search *shall* be 100 000 in every implementation.

Each weight of an inductive or relative inequality *shall* have a magnitude of at most the larger of 8 and the number of tokens in `M0`.

**Certificate.** A proof is the inductive invariant `SE(M, n) ∧ ⋀ refinements(M)` over the places
and one counter per flat transition. It goes as the `Reachable` interpretation to the certificate
check of [VER-016], which re-proves initiation, consecution and safety against the raw step
relation before `Proven` is reported with method `state-equation`. The report prints each
refinement and the result lists them as its discovered invariants. A failed or inconclusive check
withholds the `Proven`, says so in the report, and the pipeline continues. The Farkas dual of the
final `unsat` is not used as the certificate: for a quiescence property the violation is a
disjunction, and one inequality per disjunct is exponential in the net.

*While* the certificate check is enabled, the verifier *shall* return the phase's proof as `Proven` with method `state-equation` and neither a counterexample nor `counterexampleConfirmed` when the certificate check of [VER-016] passes on the invariant `SE(M, n) ∧ ⋀ refinements(M)`, and a failed or inconclusive check *shall* withhold the `Proven` and let the pipeline continue.

*While* the certificate check is disabled, the verifier *shall* return the phase's proof as `Proven` with method `state-equation` and neither a counterexample nor `counterexampleConfirmed`, and the report *shall* carry `  Certificate check: not applicable (disabled)` in place of the check.

*When* the phase returns `Violated`, the verifier *shall* return the markings and transitions of the run, in firing order, as the counterexample, with `counterexampleConfirmed` `true`.

**Where it runs.** On the flat path, after [VER-015] and before the fixpoint query. Not on a net
with match transitions (the flat encoding is name-blind there; [VER-012] and [NU-053] are its
exact routes), not on the name-coloured encoding, and not under `Ignore` with environment places
registered ([VER-006]). On by default; MAY be disabled to force the fixpoint path.

The pipeline *shall* place the state-equation phase at one point, after the linear bound of [VER-015] and before the fixpoint query.

*While* the phase is enabled, the pipeline *shall* run it on exactly the queries whose verified net has no match transition and that are not verified under `Ignore` with environment places registered ([VER-006]), unless an earlier step has decided the query or the run has stopped.

*If* the phase is disabled, *then* the verifier *shall not* run it, and the verdicts and reports *shall* be those of the pipeline without the phase.

Every implementation *shall* turn the phase on by default.

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
violated, with the run `produce, produce, produce, cancel`.

---

#### VER-019: Firing-Bound Phase

**Priority:** SHOULD
**Kind:** B

After [VER-018] and before the fixpoint query, the verifier tries to bound the length of every
run. A **ranking** is a weighting `r ≥ 0` of the places with `r·C_t ≤ −1` for every flat
transition `t` that can fire (one that inhibits a place it needs cannot). A consume-all or reset
arc removes at least `pre`, so with `r ≥ 0` the column `C_t = post − pre` bounds such a firing's
effect on `r·M` from above. Every firing therefore lowers `r·M` by at least one, `r·M` never goes
below zero, and no run from `M0` has more than `K = r·M0` firings.
The ranking with the least `K` is found by one `QF_LIA` optimisation query (phase `ranking`) and
re-checked in exact integer arithmetic.

*When* the ranking query answers with a weighting `r`, the phase *shall* re-check in exact integer arithmetic that every weight is at least 0 and that `r·C_t ≤ −1` for every flat transition `t` that can fire, and *shall* take the bound `K = r·M0` only when the re-check passes.

*If* the re-check fails or `K` is larger than `2^53 − 1`, *then* the phase *shall* end inconclusive without a bounded model check, and the pipeline *shall* continue.

`2^53 − 1` is the largest integer that every implementation counts depths in exactly, so all of
them refuse the same bounds.

With the bound, a **bounded model check** decides the property. One `QF_LIA` script (phase `bmc`)
unrolls `d` steps of the exact step relation from `M0`: a selector per step names the transition
fired or an idle step, an idle step is followed only by idle steps, and the violation is asked of
the last marking. The encoder also emits the environment post-caps of [VER-006] for the bounded
witness phase ([VER-025]); here there are none, since this phase sends no query on a net
with injected environment places.

*When* the phase has the bound `K`, it *shall* ask the bounded model check first at depth `min(K, 8, L)`, where `L` is the depth limit, and after an `unsat` answer at a depth `d` below both `K` and `L` it *shall* ask next at depth `min(2d, K, L)`.

The depth limit `L` *shall* be 512 in every implementation.

With the default limit, a bound of 5 is asked at depth 5 alone, and a bound of 25 at the depths
8, 16 and 25.

*If* the bounded model check answers `unsat` at a depth of at least `K`, *then* the phase *shall* return `Proven` with method `bounded-model-check` and the bound `K`.

That is a claim about every run, since none is longer than `K`.

*If* the bounded model check answers `unsat` at the depth limit while `K` is larger, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.

*When* the bounded model check answers `sat` at a depth, the phase *shall* read the run from the model's selectors as the bounded witness phase ([VER-025]) reads it with no injection step, replay it under the exact abstract semantics, and return `Violated` with that run, untrimmed and confirmed, when every step is enabled and the last marking violates the property.

*If* the depth is positive and the model defines none of the step selectors, or the run does not replay to a violating marking, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.

A depth of 0 has no selectors: its run is empty, and it is reported when `M0` violates the
property. That depth is asked only when `K` is 0.

When no ranking exists, Farkas gives firing counts `y ≥ 0, y ≠ 0` with `C·y ≥ 0`, which the
marking equation lets repeat forever. The report names their transitions (a second query) and the
pipeline continues. This does not show that the net has an infinite run (a loop that only an
inhibitor stops has no ranking), only that the phase makes no claim about runs it cannot bound.

*If* the ranking query answers `unsat`, *then* the phase *shall* report that the net has no firing bound, whatever the second query answers, and the pipeline *shall* continue to the fixpoint query.

*If* the ranking query or a bounded model check fails in the transport or answers `unknown`, or the phase budget is spent before its answer, *then* the phase *shall* end inconclusive, and the pipeline *shall* continue.

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

*If* environment places are declared for injection, *then* the phase *shall* send no query and *shall* end inconclusive, also when no arc touches such a place.

No weighting bounds an injection.

Every implementation *shall* turn this phase on by default, as it turns on the phase of [VER-018].

A pre-fixpoint verdict carries its own `method` and report, so differing defaults break the
verdict-parity fixtures without any property differing.

*If* the phase is disabled, *then* the verifier *shall not* run it, and the verdicts and reports *shall* be those of the pipeline without the phase.

Disabling the phase leaves the query to the later steps, up to the fixpoint query.

The pipeline *shall* place the firing-bound phase at one point, after the state-equation phase of [VER-018] and before the bounded witness phase of [VER-025] and the fixpoint query.

So no run enters the state-equation phase after this phase, this phase after the witness phase or the fixpoint query, or this phase twice.

*While* the phase is enabled, the pipeline *shall* run it on exactly the queries that the state-equation phase of [VER-018] runs on when that phase is enabled, whether [VER-018] is enabled or not, unless an earlier step has decided the query or the run has stopped.

*When* the phase ends inconclusive or reports that the net has no firing bound, the pipeline *shall* go on to its next step.

*When* the phase returns `Proven` or `Violated`, the verifier *shall* return that result: `Proven` with the method `bounded-model-check` and neither a counterexample nor `counterexampleConfirmed`; `Violated` with the transitions of the replayed run, in firing order, as the counterexample and `counterexampleConfirmed` `true`.

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
report names `t0, t1, t2`, and the fixpoint query proves `placeBound(p0, 1)`.

---

#### VER-025: Bounded Witness Phase

**Priority:** SHOULD
**Kind:** B

Directly before the flat fixpoint query, the verifier asks one `QF_LIA` query (phase `witness`,
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

*If* the pipeline reaches the flat fixpoint query, the witness depth `D` is positive, and the net has no match transitions or the property is a reachability-safety property with a budget place declared, *then* the verifier *shall* run the phase directly before the fixpoint script is encoded.

*While* the fixpoint query takes the name-coloured encoding ([NU-053]), the verifier *shall not* run the phase.

*If* the net has match transitions and either the property is not a reachability-safety property or no budget place is declared, *then* the verifier *shall not* run the phase.

The ν guard ([NU-050]) turns every verdict there into `Unknown`, so the query would be pure cost.

*If* the witness depth is 0, *then* the verifier *shall not* run the phase, and its verdict, route, report and scripts *shall* be those of the pipeline without the phase.

*When* the verifier does not run the phase, it *shall* send no query for it and print no report line for it.

*While* environment places are registered under `Ignore`, the phase *shall* run where it runs on any other flat net, with no injection step.

A run that injects nothing is a run of the net, as the fixpoint query's `Violated` is there
([VER-006]). Under `Arrivals` the net is rewritten before any route runs and has no environment
places ([VER-006]), so the arrivals are ordinary transitions of the run.

*While* the counterexample replay of [VER-003] is disabled, the phase *shall* run where it runs with the replay enabled, and a run it reports *shall* still be confirmed.

That option governs the replay after the fixpoint query only; the phase replays its own run.

*If* the property is a name-alignment property ([NU-055]), *then* the phase *shall* send no query and *shall* end inconclusive with the reason of [NU-055] that the property is decided only by the name-partition state-class graph.

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

*When* the phase runs, the verifier *shall* send this script, and every implementation *shall* emit it byte for byte the same for the same net, initial marking, property and options.

*If* `J` is 0, *then* the script *shall* be byte-identical to the bounded run of [VER-019] at the same depth.

**Decode, replay and trim.**

*When* the solver answers `sat`, the phase *shall* read the run from the model's selectors in step order up to the first idle step, taking a value in `[0, T)` as a transition step, a value in `[T, T + J)` as an injection step, and any other value, or a selector the model leaves undefined, as idle, and *shall* read no run from a model that defines no selector.

*When* the phase replays a run, it *shall* fire each transition step under the exact abstract semantics with the environment post-caps, take each injection step only while its guard holds, and accept the run only when every step is enabled and the last marking violates the property.

*When* a run replays, the phase *shall* trim it: it *shall* first cut the run to its violating prefix, then try the steps from the last to the first, replace the run by the violating prefix of the run without that step whenever one exists, and repeat such passes until one changes nothing.

The violating prefix of a run is its shortest prefix that replays to a violating marking, the
empty prefix (`M0` itself) included; a run has none when no prefix replays to a violating
marking. A step after the violation need not be enabled for a prefix to count.

*When* the phase reports a run, it *shall* report the trimmed run, replayed, with each transition step labelled by its transition's name and each injection step by `inject(<place>)`.

The solver pads a run to the full depth with steps that lead nowhere, and a padded run can pass a
violating marking and go on; the trim removes such steps. The trimmed run ends at the first
violating marking it reaches, and it is irredundant: no single step of it can be dropped so that
some prefix of the rest still replays to a violating marking. When `M0` violates, the trimmed run
is the empty one, whatever model the solver returned. It is not claimed to be a shortest run.
Which run is reported depends on the model the solver returns; for one model the trim fixes it,
so every implementation reports the same run for the same stub model.

**Budget.**

*When* the phase starts, it *shall* start a wall-clock budget of `max(1, floor(timeout_ms / 8))` milliseconds before it encodes the script, and the query *shall* receive what is left of it.

The query passes the total-budget clamp of [VER-013] like every other process. The phase is the
step `witness phase` of that requirement's reason
`total verification budget of <N> ms exhausted during <phase>`. The trim polls the [VER-013]
deadline (the total budget and cancellation) before each candidate it replays; a stop found there
ends the verification as a stop anywhere else in the step `witness phase` does. Outside a
`verify()` call the poll does nothing.

**Report.**

*When* the phase runs, the report *shall* carry the line `  Bounded witness phase (VER-025):` followed by exactly one of the status lines below.

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

*When* a run replays, the phase *shall* return `Violated` with the trimmed run as the counterexample, `counterexampleConfirmed` `true` and the route of the SMT pipeline ([VER-003]), and the result *shall* continue as the witness result of [VER-018] and [VER-019] does.

That result is `=== RESULT ===`, `VIOLATED: <property>`,
`  Counterexample trace (replay order, <k> states):` with one line per marking,
`  Firing sequence: <a> -> <b>` unless the run is empty, and the untimed warning of [VER-003]
AC7. A run of 0 steps is the empty firing sequence of [VER-003] AC8: one marking, no transition
and no `Firing sequence` line.

*When* the phase returns `Violated` on a net with match transitions, the result *shall* pass the ν guard of [NU-050] as a name-blind verdict and carry the guard's note that the counterexample may be spurious.

*When* the phase returns `Violated`, the counterexample-timing step of [VER-023] *shall* apply to the result as to every result of the pipeline.

*If* the solver answers `unsat`, *then* the phase *shall* report that no run of at most `D` steps reaches a violation, and the pipeline *shall* continue to the fixpoint query.

*If* the query fails in the transport, the solver answers `unknown`, the phase budget is spent or the run does not replay, *then* the phase *shall* report itself inconclusive with its reason, and the pipeline *shall* continue to the fixpoint query.

The phase *shall not* report `Proven`, and *shall not* read an `unsat` answer as a proof.

*If* the phase ends without a run, *then* the pipeline *shall* continue as it does without the phase, and the phase *shall* change no verdict except through the time it spends against the total budget of [VER-013].

**Option.**

The witness depth *shall* default to 8 in every implementation.

*When* the caller sets the witness depth to a positive `n`, the phase *shall* ask one query at depth `n`.

*If* the caller sets a negative witness depth, *then* setting it *shall* fail with the argument error `witnessDepth must be non-negative, got <n>`.

A language whose depth type has no negative value has no such error. Only depth 8 is cheap: a
larger depth costs up to the phase budget on every query that has no short run, each `Proven`
one included.

**Scripts and dump.**

*When* `LIBPETRI_SMT_DUMP` is set, the verifier *shall* keep the phase's script and reply under the phase name `witness` ([VER-013]).

*When* the scripts are encoded without a solver ([VER-013] AC1), the result *shall* carry as its `witness` member the script `verify()` sends when it reaches the phase, present exactly when the encoding is flat, the witness depth is positive, and the net has no match transitions or the property is a reachability-safety property with a budget place declared, and absent otherwise.

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
depth to 0, since the phase now answers first.

---

## State Class Graph

#### VER-010: State Class Graph Analysis

**Priority:** MAY
**Kind:** B

The engine may support state class graph construction using the Berthomieu-Diaz (1991) algorithm. State classes combine a marking with a Difference Bound Matrix (DBM) representing timing constraints on enabled transitions.

An implementation that offers the graph is bound by the sentences below. In them a timed run of the net starts at an initial marking with every clock at zero, on a net in which no transition's earliest firing time is below zero or above its latest, and follows the Time Petri net semantics: time may pass only as far as no enabled transition goes past its latest firing time, a transition fires no earlier than its earliest firing time and deposits its outputs at the instant it fires, and a clock is kept or restarted by the persistence rule below. A class holds a state when the class's marking is the state's marking and its firing domain holds every combination of firing times the state allows the class's clocks. A class is well formed when its clocks are the transitions enabled in its marking and its firing domain has the form letting time pass leaves: the closure of a matrix with a finite reference bound in which every clock's lower bound is zero. For a well-formed class that holds a state, the class's clocks are the state's enabled transitions.

*When* a timed run of the net reaches a state, the state class graph *shall* hold a class, reachable from its initial class, that holds the state.

Every class the state class graph reaches from its initial class *shall* be well formed and *shall* list its clocks once each, in ascending order of transition name compared by Unicode code point ([VER-013]).

*When* a transition can fire with one of its outcomes ([VER-001]) from a state in which no enabled transition is past its latest firing time, and a well-formed class holds that state, the state class graph *shall* give that class a successor, labelled with the transition's name and the outcome's index, that holds the state the firing leaves.

Every successor of a class *shall* be labelled with the name of a transition among the class's clocks and the index of one of that transition's outcomes, and *shall* have the marking that firing the transition with that outcome leaves: each input place less the `consumptionCount(available)` of [IO-007], so an `All` or `AtLeast` input empties its place, each reset place emptied, and the outcome's tokens added.

*When* a transition `t` fires from marking `M` into marking `M'`, the successor step of the state class graph *shall* keep the clock of a transition `t'` enabled in `M` exactly when `t'` is not `t` and is enabled both in `M'` and in the intermediate marking `M - Pre(t)`, which has the inputs of `t` consumed, its reset places drained and none of its outputs deposited.

The canonical order of the state class graph *shall* either keep a list of transitions or return a permutation of its positions, and *shall* leave every list it is given in ascending order of transition name, compared by Unicode code point ([VER-013]).

*If* the transition names of the net are unique, *then* the class key of the state class graph *shall* give two classes, each with the transitions enabled in its marking as clocks, once each in that order, and a canonical firing domain (closed, zero on the diagonal, every clock with a finite lower bound), the same key exactly when they have the same marking and their firing domains hold the same firing times.

When every bound of the net is a whole number of milliseconds, the successor step of [VER-011] leaves every firing domain canonical, so two classes that step builds on a net with unique names are one exactly when they have the same marking and the same firing domain, whatever interleavings reached them. A net may give two transitions one name ([CORE-021]); the key sentence does not reach such a net, since an order by name cannot tell two enabling orders of one name apart. These sentences speak of the successor's soundness: a class holds every state the firing rule allows. That a class holds no state a timed run cannot reach is the exact half of the successor, not stated here, and so is the exact half of the fresh interval a newly enabled clock gets.

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
3. Every outcome of a transition, each XOR branch and a timeout outcome that deposits
   differently from every branch, is expanded into a virtual transition of its own
   ([VER-001]), and a successor is labelled with the fired transition's name and the
   outcome's index, counting the outcomes in the order in which [VER-001] numbers the
   `_b<i>` virtual transitions: the branches in enumeration order, then the timeout outcome.
4. Clock persistence uses the intermediate marking of Berthomieu and Diaz. After `t` fires
   from marking `M`, a transition `t' ≠ t` keeps its clock only if it is enabled in `M`, in
   the successor marking `M'`, and in the intermediate marking `M - Pre(t)`: inputs
   consumed, reset places drained, outputs not yet deposited. Every other transition
   enabled in `M'` gets a fresh firing interval. This is the executor's rule ([TIME-012])
   for an on-time executor with atomic firings, one that reaps no transition, fires none
   after its latest bound, and gives an action no duration, the assumptions [VER-023] lists;
   the enablement recheck of a firing pass ([EXEC-003] AC3) is part of atomic firings.
   A successor that keeps a clock the executor restarts under-approximates the executor's
   behaviors. A transition outside the in-flight split of [VER-004] fires atomically and
   takes no time (a split one completes through its immediate completion step at any later
   time). Under `alwaysAvailable` an environment input never disables a transition, and under
   `bounded(k)` only one that demands more than `k` tokens does, permanently ([VER-006] AC3).
5. The graph builder (`StateClassGraph.build` in every language) builds the graph of the net it
   is given and does not apply the in-flight split itself. A caller that builds the graph
   directly, outside `SmtVerifier`, MUST apply the split first (`splitInFlight` in TypeScript,
   `in_flight::split_in_flight` in Rust, `InFlight.split` in Java) to get the executor's
   two-step firing ([VER-004]); when the split is refused, no graph of this kind is faithful to
   the executor. The builder's documentation MUST say so.

**Depends on:** [IO-007], [EXEC-010], [TIME-012], [TIME-013], [VER-001], [VER-004], [VER-011],
[VER-013]

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
**Kind:** F

Timing constraints within a state class are represented as a Difference Bound Matrix (DBM), encoding constraints of the form `θᵢ - θⱼ ≤ cᵢⱼ` where θᵢ is the firing time of transition i: the time from entering the class until it fires.

*When* the zone library creates a zone from one lower and one upper bound per clock, the zone *shall* hold exactly the firing times that lie between the bounds of each clock.

Canonicalising a zone *shall not* change the firing times it holds.

*When* a zone holds some firing times, its canonical matrix *shall* be closed: no bound exceeds the sum of the two bounds of a detour through any clock of the matrix, the reference clock included.

The zone library *shall* report a zone empty only when it holds no firing times.

*If* every finite bound of a zone is a whole number of milliseconds and every clock, the reference clock included, has a finite lower bound, *then* the zone library *shall* report the zone empty exactly when it holds no firing times.

*When* a transition fires from a zone, the successor zone, with the persistent clocks first in the order given and the newly enabled clocks after them, *shall* hold every firing time the firing rule allows: the fired clock is not later than any other clock, each persistent clock keeps the time it had left after the fired clock, and each newly enabled clock lies between its static bounds.

*When* the clocks of a zone that holds some firing times are permuted, the zone library *shall* keep the reference clock first, move every other bound of the matrix with its two clocks, and write zero as the bound of the reference clock against itself.

*If* two zones each hold some firing times and every finite bound of both is a whole number of milliseconds, *then* their dedup keys *shall* be equal exactly when their matrices are equal entry by entry, the bounds between two clocks included.

**Acceptance Criteria:**
1. DBM encodes lower and upper bounds for each transition clock.
2. Zone emptiness is detectable (unsatisfiable constraints).
3. Successor DBM is computed correctly after transition firing.
4. The zone exposes a dedup key over its full canonical matrix (every `θᵢ - θⱼ` bound, not
   only the diagonal projections), and a permutation of its clocks that reorders the matrix
   with them; equality is positional over the canonical order ([VER-010] AC1). The key renders
   each finite bound to the millisecond, so on zones that hold some firing times it is exact
   when every finite bound is a whole number of milliseconds.

**Depends on:** [VER-010]

**Implementation notes:**
- Java: Full implementation
- TypeScript: Full implementation
- Rust: Full implementation (`libpetri-verification` `dbm`)

**Test derivation:** Create DBM for 3 timed transitions; fire one; verify successor zone constraints.

---

#### VER-012: Name-Aware State Class Graph (ν-Partition Quotient)

**Priority:** MAY
**Kind:** F

The state class graph ([VER-010]) MAY be made **ν-aware** to decide [NU-020] join
correlation *exactly* — the [NU-050] **Route B** carve-out. Each correlation
token carries an abstract, interchangeable name-symbol; a matched (ν-join)
transition is enabled only when one symbol is shared by every correlated input
(not merely when the token counts allow); a minting fork introduces a
globally-fresh symbol; and the graph is quotiented under name-permutation
symmetry (its dedup key abstracts the symbol identities). The timed firing domain
([VER-011]) is carried beside the name partition, with a matched join's clock gated by
name-enablement ([NU-050]) and, unless `assumeNoReaping` is set, without latest bounds
([TIME-013]); the Route B class key pairs the base class (for a timed net its marking, zone
and earliest-ready times) with the canonical key of the name layer. Quiescence ([NU-050]) is
decided over the name-aware terminal classes.

*When* the Route B graph fires a ν-join on a name-symbol, every correlated input *shall* hold at
least the required count of that symbol, and the firing *shall* remove the required count of that
symbol from each correlated input and add one token of it to each relay target of the fired branch
([NU-054]). *If* every correlated input of a ν-join holds at least the required count of a
name-symbol, *then* the name successors of a firing of that join *shall* include one with the
canonical key of the join fired on that symbol. *When* the Route B graph fires a coloured consumer
([NU-051]), it *shall* fire it on a name-symbol its coloured input holds, removing one token of that
symbol from the input and adding one token of it to each coloured output of the fired branch. *If*
the coloured input of a coloured consumer holds a name-symbol, *then* the name successors of a
firing of that consumer *shall* include one with the canonical key of the consumer fired on that
symbol. *When* the Route B graph fires a minting transition, its one name successor *shall* add one
token of a name-symbol that no coloured place of the class holds to each coloured output of the
fired branch. *When* the Route B graph fires a transition that neither mints, joins nor consumes a
name-symbol, its one name successor *shall* be the name layer of the class unchanged. Two name
layers *shall* have the same canonical key exactly when one is the other with its name-symbols
renamed by a permutation. The Route B graph *shall* identify two classes exactly when they have the
same base class and their name layers have the same canonical key. *When* the Route B graph fires a
transition, the successor *shall* hold on each place the transition does not reset the tokens the
place held, less the tokens the transition's input on that place consumes by [IO-007] (all of them
for an `All` or `AtLeast` input), plus the tokens the fired branch deposits there.

The executor fires a ν-join on one of the names that enable it ([NU-020]); the graph fires it on
each of them, up to renaming, and a coloured consumer ([NU-051]) on each resident name. Route B's
successor step gives any two classes with the same key the same transition labels and successor
keys, up to order, so the premise of the completeness sentence below holds for it.

Every class the Route B build stores *shall* be reachable in the graph from the initial class,
whether the build closed, was truncated, was stopped or stopped early. *If* the Route B build
closes, *then* it *shall* have expanded every class it stored. *While* the graph's successor step
gives any two classes with the same key the same transition labels and successor keys, up to order,
*if* the Route B build closes, *then* it *shall* have stored a class with the key of every class the
graph reaches from the initial class. *If* the Route B build stops early at a violating class of a
reachability-safety property, *then* its verdict for that property *shall* be the verdict of the
same build without the early stop, unless that build is stopped by the total budget or a
cancellation. *If* the Route B build stops early, *then* it *shall not* report the graph as closed.

**Acceptance Criteria:**
1. A ν-join fires in the graph only on a name shared by all correlated inputs; a
   marking reachable only by equating two distinct names is *not* reachable
   (NU-050 #1), with no budget place required.
2. Two markings differing only by a permutation of name-symbols are the same
   state class (the quotient is finite when the live-name pool is structurally
   bounded).
3. **Conditional on an executor-faithful consumption model** (see below): when the
   graph closes within the class bound the verdict for reachability-safety and quiescence is
   sound for every executor run ([NU-050]) and complete for the free-choice name semantics the
   graph explores: every class the graph reaches is stored and expanded, so a property that a
   class the graph reaches violates is `Violated`, and a `Violated` names a class the graph
   reaches. When that graph keeps a latest
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
   `BranchPlaceBound`, `Unreachable` and `MutualExclusion`, the safety set of [VER-017]'s
   "Verdicts from a truncated graph", and `NameAligned` of [NU-055]) the build checks each class
   with the same shared predicate as it is discovered and stops at the first violating class. BFS discovers classes in index
   order, so that class is the lowest-index violating class — the one the check over a full or
   truncated graph selects — and its path is the shortest; verdict and route are
   identical to a build without the early stop and the witness ends at the same class; only the
   class count, the time and, among equally short paths to that class, the path the witness
   takes may differ. When
   the stop comes before the class bound, the report note
   `Note: Route B stopped at the first violating class after N classes (VER-012). Every explored class is reachable and classes are discovered breadth-first, so the counterexample is a real firing sequence and a shortest one to any violation.`
   replaces both the truncation note and the exact-graph note, and the parent whose expansion
   discovered the violating class does not count as expanded; when the bound is hit first, criterion 3 applies unchanged. Quiescence
   properties do not stop early (they need expanded classes). An early-stopped graph is not
   complete and MUST NOT be treated as closed. PNID Fig. 11(b), `placeBound(order_clerk, 2)` at
   the default class bound: `Violated` with `create_order ×3` after a handful of classes,
   where it took 1.8 s to fill the cap first.

**Exactness precondition (consumption model).** The soundness and completeness of
criterion 3 are not unconditional: they hold only while the graph's successor relation
removes as many tokens from each place as the executor would. The successor step MUST
derive each input's token count from the canonical `consumptionCount(available)` of
[IO-007] (so `All` and `AtLeast(m)` consume **all** available tokens, not merely
`requiredCount()`). Which names the removed tokens carry is the graph's free choice, where
the executor takes the oldest ([EXEC-010], [NU-020]), so criterion 3 claims completeness only
for the graph's own name semantics. A successor relation that consumes a *minimum* instead leaves phantom residue in
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
on that net explores as before, and on several fixtures the early-stop witness ends at the class the
witness from a build without it ends at. For the orbit dedup, the class count of every existing Route B fixture is
unchanged, and an 8 000-class build of Fig. 11(b) finishes under a generous time bound.

---

#### VER-023: Timed Counterexample Check

**Priority:** SHOULD
**Kind:** B

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
   [VER-017] condition 2); under the `Arrivals` mode of [VER-006] the net is closed before any
   route and has none, so the check runs on the closed net;
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
`SPURIOUS_UNDER_TIMING` there means that no on-time run reaches a violating rest. On a timed
graph that MUST still hold: a class with an enabled transition has a successor whatever its
interval, so a `delayed(5)` transition, whose interval `[5, ∞)` has no upper bound, still fires
out of its class. A graph that dropped such a class's successors would report a timed deadlock
that the net does not have. On the [VER-002] AC11 witness the check is `TIMED_CONFIRMED` with the empty trace.

**Outcomes.**
- The graph reaches a violating class: `TIMED_CONFIRMED`. The counterexample trace and its
  transitions are **replaced** by the shortest path from the initial class to a violating class
  (the first one the breadth-first build stored, [VER-017]), a run of the timed semantics
  **ignoring priority** (the graph of [VER-010] does not order transitions by priority), and the
  report says the trace came from the timed graph. The run is
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
  property, only expanded classes that rest for a quiescence property, a class resting when it
  has no successor or every transition it enables is reapable, [VER-002]):
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
net does not. The verdict, the route and the invariants are unchanged; under `TIMED_CONFIRMED`
the trace, its transitions and `counterexampleConfirmed` are replaced, and under the other two
outcomes they are kept. With the option off, the result and the report are byte-identical to
those of a verifier that does not offer the check.

**The check, as EARS sentences.**

The verifier *shall* run the timed check exactly when the option is on, the verdict is `Violated`, some transition of the verified net is not `immediate`, no environment place is still registered on the verified net (the `Arrivals` rewrite of [VER-006] removes them), the net declares no match transition, and the route that decided is not Route B ([VER-012]).

*If* the build of the timed graph is stopped by the total budget or cancelled ([VER-013]), *then* the timed check *shall* answer `TIMED_UNDECIDED`.

*While* the build is neither stopped by the total budget nor cancelled, the timed check *shall* answer `TIMED_CONFIRMED` when a counted class of the timed graph violates the property, a counted class being any stored class for a safety property and a class the builder expanded for a quiescence property.

*When* the timed graph is closed and no class of it violates the property, the timed check *shall* answer `SPURIOUS_UNDER_TIMING`.

*When* the timed graph is truncated at the class budget and no counted class of it violates the property, the timed check *shall* answer `TIMED_UNDECIDED`.

*When* the timed check answers `TIMED_CONFIRMED`, the path it reports *shall* lead, in the timed graph it built, from the initial class to the first class, in the order the builder stored the classes, that is counted and violates the property, and *shall* be no longer than any other path of that graph from the initial class to that class.

*If* the timed check does not run, *then* the verifier *shall* leave the result unchanged, its `counterexampleTiming` at the value [VER-003] gives it.

*When* the timed check runs, the verifier *shall* leave the verdict, the route and the reported P-invariants unchanged.

*When* the timed check answers `TIMED_CONFIRMED`, the verifier *shall* report `counterexampleTiming` `TIMED_CONFIRMED`, replace the counterexample's transitions by those of the path the check reports, and report `counterexampleConfirmed` as `true`.

*When* the timed check answers `SPURIOUS_UNDER_TIMING`, the verifier *shall* report it as `counterexampleTiming` and keep the counterexample's transitions and `counterexampleConfirmed`.

*When* the timed check answers `TIMED_UNDECIDED`, the verifier *shall* report it as `counterexampleTiming` and keep the counterexample's transitions and `counterexampleConfirmed`.

**The timed graph, as EARS sentences.**

*While* every finite bound of the net is a whole number of milliseconds, a class of the timed graph *shall* have no successor exactly when its marking enables no transition.

*When* the timed graph is closed and no class of it violates a safety property, the property *shall* hold on every marking that an on-time run with atomic firings reaches from the initial marking.

*When* the timed graph is closed and no class of it violates a quiescence property, the property *shall* hold on every resting marking that an on-time run with atomic firings reaches from the initial marking, a marking resting when every transition it enables is reapable ([VER-002], [TIME-013]), which under `assumeNoReaping` means when it enables none.

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
5. With environment places registered under a mode other than `Arrivals` ([VER-006]), or with
   match transitions, the check does not run and the value is `UNTIMED_ABSTRACTION`; a Route B
   verdict on a timed net stays `TIMED_EXACT`; an untimed net stays `UNTIMED_NET`.
6. The race `t1: p → a` at `window(3, 5)`, `t2: p → b` at `delayed(10)`, one token on `p`, under
   `unreachable(b)` with the check on: the verdict is `Violated`, the value is
   `SPURIOUS_UNDER_TIMING`, and the report says the timed claim assumes an on-time executor with
   atomic firings.
7. No verdict differs between the check on and off, for any net and property.

**Implementation notes:**
- Java: `SmtVerifier.timedCounterexampleCheck(boolean)`; the graph is
  `StateClassGraph.build(..., Options.TIMED)`, the predicate `GraphDecision.decideOverClasses`.
- TypeScript: `SmtVerifier.timedCounterexampleCheck(on: boolean)`; the graph is built with
  `{ untimed: false }`, the predicate `decideOverClasses` (`verification/graph-decision`).
- Rust: `SmtVerifier::timed_counterexample_check(bool)`; the graph is built with
  `StateClassGraph::build_with_options`, the predicate `graph_decision::decide_over_classes`.
- Python: `verify(..., timed_counterexample_check=False)`.

**Depends on:** [VER-002], [VER-003], [VER-004], [VER-006], [VER-010], [VER-012], [VER-013],
[VER-014], [VER-017], [VER-022], [EXEC-003], [EXEC-042], [TIME-013]

**Test derivation:** the watchdog net above with the check off and on (AC1), with the watchdog
made faster than the answer (AC2), and truncated by `enumerationMaxClasses` (AC4); the timed
`deadlockFree` nets of AC3; the watchdog net with an environment
place added (AC5). Two parallel watchdogs close in 10 classes with no `TIMEOUT` marking.

---

## Structural Analysis

#### VER-020: Siphon and Trap Analysis

**Priority:** MAY
**Kind:** F

The engine may support structural analysis of siphons (sets of places that, once empty, stay empty) and traps (sets of places that, once marked, stay marked).

**Commoner's theorem governs ORDINARY nets only.** The siphon and trap fixpoints are computed
from the pre/post vectors, so they model a net in which the sole reason a transition is disabled
is an input place holding too few tokens. A read arc, an inhibitor arc, a reset arc, a
consume-all input or an input arc weight above one is a disablement the fixpoints do not see,
and dropping it yields a strictly **more permissive** net, the wrong direction for a deadlock
proof. An implementation that converts a siphon/trap result into a `Proven` verdict MUST
therefore refuse to do so for any net carrying one of them, exactly as it already refuses when
sinks are declared or environment places are registered on the net it decides. Three
witnesses, each a net that is dead at its initial marking and was reported deadlock-free before
the restriction: `t1: one(a) read(g) → g` with `t2: one(g) → a` from `{a:1}`;
`t: exactly(2, a) → a` from `{a:1}`; `t: one(a) inhibitor(b) → a` from `{a:1, b:1}`.

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

*When* the siphon search returns, every set it returns *shall* be a nonempty siphon that contains no other nonempty siphon.

*When* the siphon search returns, every nonempty siphon *shall* contain a set it returns.

The maximal trap the check computes inside a set of places *shall* be a trap inside that set that contains every trap inside it.

*If* the net has more than 50 places or no transition, *then* the structural check *shall* answer inconclusive.

The structural check *shall* pass the siphon search a budget of 10 000 search nodes.

*If* the siphon search does not return, *then* the structural check *shall* answer inconclusive.

*When* the siphon search returns on a net with at most 50 places and at least one transition, the structural check *shall* answer no potential deadlock exactly when the maximal trap inside each returned siphon holds a token in the initial marking, and potential deadlock otherwise.

*While* the total budget of [VER-013] is not spent, the siphon search *shall* return at a budget of 10 000 search nodes on the two witnesses above with minimal siphons `{x, y}` and `{a, b}`.

*If* the total budget of [VER-013] is spent before the siphon search starts on a net with at least one place, *then* the siphon search *shall not* return.

**A match transition hides a dead marking from the flat net.** A match transition ([NU-020])
joins tokens by identity, which the flat net does not see: the flat net enables the join
whenever the counts are there, so it can have no dead marking while the net it stands for has
one. The structural route therefore does not decide a net with match transitions, as it does
not decide one with a reapable transition ([VER-002]) unless `assumeNoReaping` is set.

The verifier *shall* convert a no-potential-deadlock answer into a `Proven` only when it decides `DeadlockFree` on a net with no match transition ([NU-020]), no reapable transition ([VER-002]) unless `assumeNoReaping` is set, no read, inhibitor or reset arc, no consume-all input, no input arc weight above one, no declared sink or conditional sink and no environment place registered on the net it decides (the `Arrivals` rewrite of [VER-006] leaves none).

**Acceptance Criteria:**
1. Siphons and traps are identified from the net structure.
2. Results inform deadlock analysis (every siphon containing an initially marked trap ensures
   deadlock-freedom of an ordinary net; liveness only for free-choice nets).
3. A structural `Proven` is offered only for `DeadlockFree` on a net with no match transition,
   no reapable transition (unless `assumeNoReaping` is set), no read, inhibitor or reset arc, no
   consume-all input, no input arc weight above one, no declared sink or conditional sink and no
   environment place registered on the net the verifier decides (the `Arrivals` rewrite of
   [VER-006] leaves none). Each of the three witnesses above returns a verdict from a route that
   models what disables them, never a structural proof. Nor is a net with no transition: the
   one-place witness above is `Violated`, not proven structurally.
4. The siphon search is complete: it finds `{x, y}` and `{a, b}` in the two witnesses above, and
   neither net is proven structurally. A siphon whose maximal trap is empty in the initial
   marking (the ring `a ↔ b` from the empty marking) blocks a structural proof. A net with more
   than 50 places or an exhausted search budget yields an inconclusive result.

**Test derivation:** Net with known siphon/trap structure; verify identification.

---

#### VER-021: XOR Branch Analysis

**Priority:** SHOULD
**Kind:** F

The verifier supports analysis of the outcomes of transitions with XOR output branches over a built state class graph ([VER-010]), reporting which outcomes the graph takes. Each outcome of a transition, each XOR branch and a timeout outcome that deposits differently from every branch, is a virtual transition of its own ([VER-001]), and the outcomes are numbered from 0 in that order: the XOR branches in enumeration order, then the timeout outcome.

The XOR branch analysis *shall* report every transition of the net with two or more outcomes, and no other, once each with its number of outcomes.

*While* the graph it reads does not split a transition in flight, the XOR branch analysis *shall* report an index of that transition as taken exactly when an edge of the graph fires the transition with that index.

*While* the graph it reads splits a transition in flight ([VER-004]), that is, while an edge fires its completion `complete:<t>` or a class marks its place `inflight:<t>`, the XOR branch analysis *shall* report an index of that transition as taken exactly when an edge of the graph fires `complete:<t>` with that index.

The XOR branch analysis *shall* report as untaken exactly the outcomes of a reported transition, numbered from 0 below its number of outcomes, that it does not report as taken.

*When* the graph is closed, the XOR branch analysis *shall* report an outcome of a reported transition as untaken exactly when no run of the net from its initial marking fires the transition with that outcome, or fires `complete:<t>` with it when the graph splits the transition.

An index is taken as the edge carries it, with no bound: a graph builder that fires a transition only with its own outcomes gives no index at or above the number of outcomes. A transition whose `Timeout` forwards an `All` or `AtLeast` input ([IO-014]) has no virtual transitions of [VER-001], so the first sentence does not cover it: the analysis may report it with the number of outcomes its graph builder fires, as the runtimes do, and still reports every other transition of the net.

The analysis reads only the graph it is given and does not report whether that graph is closed. On a graph truncated at its class budget ([VER-017]) an untaken outcome may still fire beyond the budget, so a caller reads the graph's completeness (`isComplete`, `is_complete` in Rust) before calling an outcome unreachable.

**Acceptance Criteria:**
1. Every outcome of a transition, each XOR branch and a timeout outcome that deposits differently from every branch, is expanded into a separate virtual transition.
2. An outcome no edge of the graph fires is reported untaken; on a closed graph it is one that no run fires.

**Depends on:** [IO-012], [IO-016], [VER-001], [VER-004], [VER-010]
**Test derivation:** Net with a XOR transition enabled after one step and a second XOR transition whose input place is never marked; on the closed graph the first XOR transition reports every outcome taken and the second every outcome untaken. A graph truncated before the first XOR transition fires is not complete and reports that transition's outcomes untaken. A transition split in flight is read off `complete:<t>`, a start edge alone takes none of its outcomes, and a class that marks `inflight:<t>` splits it before any completion fires. A XOR transition beside an unrelated drained forward is still reported.

---

## Open-Net Verification

#### VER-022: Open-Net Verification Against a Contract

**Priority:** MAY
**Kind:** B

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
- *Count clauses*, each named: at every quiescent marking the tokens across the clause's places,
  each place counted once, number between `min` and `max`, or at least `min` for a clause with no
  `max`.
- *Rest places*: may hold any number of tokens at quiescence.
- *Designed terminals*: while a terminal's marker holds a token, clause lower bounds are waived
  (upper bounds are not) and the terminal's excused places may hold tokens. The marker itself may
  always rest, as in [VER-014].
- *Environment transitions*: fired by the environment, for a neighbour that reacts to what the
  subnet sends — a tool answering a request, a loop body sending an item back within a budget of
  its own — which an arrival group cannot express because its tokens do not wait for a request. A
  place only environment transitions touch is an **environment place**, the environment's own
  state; a place they share with the subnet is a port.
- *Termination*: no run fires forever, unless the contract waives it. A cycle of reapable
  transitions ([TIME-013]) counts too, since a run need not reap them.

A quiescent marking **meets** the contract when every clause holds, lower bounds only while no
terminal marker is marked, and every token lies on a clause place, a rest place, an environment
place, a terminal marker, or an excused place of a marked terminal. The second condition is the
rest set of [VER-014] with the clause, rest and environment places as sinks and each terminal as a
conditional sink, and implementations MUST decide it through that same predicate. Every other
place is internal to the subnet and must be empty.

The verifier *shall* judge a quiescent marking to meet the contract exactly when, counting each
place of a clause once, the tokens across each clause's places number at most the clause's `max` if
it has one, at least its `min` unless some terminal marker is marked, and no marked place is
stranded under the rest set of [VER-014] whose sinks are the clause, rest and environment places and
whose conditional sinks are the terminals.

**Closure.** The subnet is verified as a closed net. Arrival group `i` contributes a source place
holding `min` tokens and a source place holding `max − min`, each left out with its transitions when
its count is 0, one transition per source and target place moving a token from that source onto the
place, and a transition with no output that declines a token of the second source. A run is
therefore quiescent only once every required arrival has happened and every optional one has been
delivered or declined. The sources are ordinary places, not the environment places of [VER-006],
which never run dry and would make every quiescence property hold vacuously.

The contract's environment transitions join the closed net unchanged. Their actions never run, so
one that declares outputs gets a placeholder action instead of a [CORE-043] refusal. Contract
places no arc touches join as places of their own and are listed in the report, so a clause over a
place nothing writes counts zero there: a finding, never a refusal. The closure's names
(`env:arrivals[i]`, `env:optional[i]`, `env:arrive[i]:<place>`, `env:arrive?[i]:<place>`,
`env:decline[i]`) and the environment transitions' names MUST NOT collide with the subnet's, and a
collision is refused. The in-flight split of [VER-004] applies to the closed net before the
terminal rewrite of [EXEC-042]: the environment transitions stay atomic and their arcs count as
tests, and a closed net the split refuses, or one that a declared mint transition ([NU-010]) is
not in, is `Unknown` before either route runs.

*If* a name the closure adds, or the name of an environment transition, is already a place or
transition name of the subnet, *then* the verifier *shall* refuse the closure, and it *shall* not
refuse a closure whose added and environment-transition names are distinct from each other, from the
subnet's names and from the environment places.

The verifier *shall* build the closed net from the subnet's transitions, then the environment
transitions unchanged, then, for each arrival group `i` in order, numbered from 0, one immediate
transition `env:arrive[i]:<place>` per target place, in the group's order, taking one token from the
source `env:arrivals[i]` when `min > 0`, and one immediate transition `env:arrive?[i]:<place>` per
target place, in the group's order, taking one token from the source `env:optional[i]`, followed by
an immediate `env:decline[i]` discarding one, when `max > min`; the transitions the closure adds
have no other arc.

The verifier *shall* start the closed net from the contract's initial marking with `min` tokens on
`env:arrivals[i]` and `max − min` tokens on `env:optional[i]` for each source it builds.

The verifier *shall* treat as an environment place exactly a place that an environment transition
touches and the subnet does not, and *shall* make every place of the subnet and every place the
contract names a place of the closed net.

The verifier *shall* mark as environment steps exactly the environment transitions and the
transitions the closure adds.

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
  termination is required, no run fires forever.
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

*If* the verifier refuses the closure, *then* it *shall* refuse the verification.

*When* the verifier accepts the closure, it *shall* return a result, and that result *shall* be
`Proven` when the closed net declares no match transition, its graph closes within a class budget
above 0, every reachable quiescent marking meets the contract and, where termination is required, no
run fires forever.

The verifier *shall* return `Proven` only when every quiescent marking reachable in the closed net
from its initial marking meets the contract, reading quiescence as [VER-002] does, or, when
`assumeNoReaping` is set, as a marking with no enabled transition, and, where termination is
required, no run of the closed net fires forever.

*When* the verdict is `Violated`, the verifier *shall* list at least one broken part, and for each
part with a confirmed witness *shall* report a firing sequence of the closed net from its initial
marking, environment steps included, that leads to a quiescent marking at which the named clause
fails, or to a quiescent marking at which each named place, at least one, holds a stranded token,
or, for `termination`, whose part before the reported cycle start leads to a marking and whose part
after it, not empty, leads from that marking back to it.

The verifier *shall* mark a witness unconfirmed only when the SMT route decided, and *shall* name in
each clause part, confirmed or not, a clause of the contract.

The verifier *shall* report a `termination` part only when the contract requires termination, and
*shall* name no stranded place in a witness that is not confirmed.

*When* the verdict is `Unknown`, the verifier *shall* give a reason that is not empty.

*If* the closed net declares a match transition, *then* the verifier *shall* return `Proven` or
`Violated` only from the SMT route.

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
   names the place whenever its witness is confirmed, always on the graph route.
4. A reachable cycle is a `termination` violation with a lasso witness when termination is
   required, and no violation when it is waived.
5. An arrival group that must deliver `n` tokens reaches quiescence only after all `n`; a
   group that may deliver at most `n` also reaches quiescence after fewer.
6. A timed subnet gets the verdict of the untimed, reap-aware claim of [VER-004]: its class
   count equals that of the same subnet with every transition immediate, and its verdict equals
   that subnet's when no transition is reapable or under `assumeNoReaping`. On the SMT route, a
   ν-net whose timing keeps a transition from firing is judged as if it could: a stranding only
   that transition causes is `Violated`.
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

**Depends on:** [VER-002], [VER-003], [VER-004], [VER-006], [VER-010], [VER-012], [VER-013],
[VER-014], [VER-017], [VER-019], [TIME-013], [EXEC-042], [CORE-043], [NU-010]

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
