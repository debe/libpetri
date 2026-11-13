import Libpetri.Spec.Text

requirement_text VER_023
  id "VER-023"
  title "Timed Counterexample Check"
  priority SHOULD
  kind B
  body r#"The flat encoders decide the untimed abstraction ([VER-004]), so a `Violated` on a timed net can
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

⟦s1|The verifier *shall* run the timed check exactly when the option is on, the verdict is `Violated`, some transition of the verified net is not `immediate`, no environment place is still registered on the verified net (the `Arrivals` rewrite of [VER-006] removes them), the net declares no match transition, and the route that decided is not Route B ([VER-012]).⟧

⟦s2|*If* the build of the timed graph is stopped by the total budget or cancelled ([VER-013]), *then* the timed check *shall* answer `TIMED_UNDECIDED`.⟧

⟦s3|*While* the build is neither stopped by the total budget nor cancelled, the timed check *shall* answer `TIMED_CONFIRMED` when a counted class of the timed graph violates the property, a counted class being any stored class for a safety property and a class the builder expanded for a quiescence property.⟧

⟦s4|*When* the timed graph is closed and no class of it violates the property, the timed check *shall* answer `SPURIOUS_UNDER_TIMING`.⟧

⟦s5|*When* the timed graph is truncated at the class budget and no counted class of it violates the property, the timed check *shall* answer `TIMED_UNDECIDED`.⟧

⟦s6|*When* the timed check answers `TIMED_CONFIRMED`, the path it reports *shall* lead, in the timed graph it built, from the initial class to the first class, in the order the builder stored the classes, that is counted and violates the property, and *shall* be no longer than any other path of that graph from the initial class to that class.⟧

⟦s7|*If* the timed check does not run, *then* the verifier *shall* leave the result unchanged, its `counterexampleTiming` at the value [VER-003] gives it.⟧

⟦s8|*When* the timed check runs, the verifier *shall* leave the verdict, the route and the reported P-invariants unchanged.⟧

⟦s9|*When* the timed check answers `TIMED_CONFIRMED`, the verifier *shall* report `counterexampleTiming` `TIMED_CONFIRMED`, replace the counterexample's transitions by those of the path the check reports, and report `counterexampleConfirmed` as `true`.⟧

⟦s10|*When* the timed check answers `SPURIOUS_UNDER_TIMING`, the verifier *shall* report it as `counterexampleTiming` and keep the counterexample's transitions and `counterexampleConfirmed`.⟧

⟦s11|*When* the timed check answers `TIMED_UNDECIDED`, the verifier *shall* report it as `counterexampleTiming` and keep the counterexample's transitions and `counterexampleConfirmed`.⟧

**The timed graph, as EARS sentences.**

⟦s12|*While* every finite bound of the net is a whole number of milliseconds, a class of the timed graph *shall* have no successor exactly when its marking enables no transition.⟧

⟦s13|*When* the timed graph is closed and no class of it violates a safety property, the property *shall* hold on every marking that an on-time run with atomic firings reaches from the initial marking.⟧

⟦s14|*When* the timed graph is closed and no class of it violates a quiescence property, the property *shall* hold on every resting marking that an on-time run with atomic firings reaches from the initial marking, a marking resting when every transition it enables is reapable ([VER-002], [TIME-013]), which under `assumeNoReaping` means when it enables none.⟧

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
place added (AC5). Two parallel watchdogs close in 10 classes with no `TIMEOUT` marking."#
