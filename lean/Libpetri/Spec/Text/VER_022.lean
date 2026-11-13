import Libpetri.Spec.Text

requirement_text VER_022
  id "VER-022"
  title "Open-Net Verification Against a Contract"
  priority MAY
  kind B
  body r#"An implementation MAY verify a subnet **in isolation**, its ports played by the environment,
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
- ⟦s1|*Count clauses*, each named: at every quiescent marking the tokens across the clause's places,
  each place counted once, number between `min` and `max`, or at least `min` for a clause with no
  `max`.⟧
- *Rest places*: may hold any number of tokens at quiescence.
- *Designed terminals*: while a terminal's marker holds a token, clause lower bounds are waived
  (upper bounds are not) and the terminal's excused places may hold tokens. The marker itself may
  always rest, as in [VER-014].
- *Environment transitions*: fired by the environment, for a neighbour that reacts to what the
  subnet sends — a tool answering a request, a loop body sending an item back within a budget of
  its own — which an arrival group cannot express because its tokens do not wait for a request. A
  place only environment transitions touch is an **environment place**, the environment's own
  state; a place they share with the subnet is a port.
- *Termination*: no run fires forever, unless the contract waives it. ⟦s2|A cycle of reapable
  transitions ([TIME-013]) counts too, since a run need not reap them.⟧

⟦s3|A quiescent marking **meets** the contract when every clause holds, lower bounds only while no
terminal marker is marked, and every token lies on a clause place, a rest place, an environment
place, a terminal marker, or an excused place of a marked terminal.⟧ ⟦s4|The second condition is the
rest set of [VER-014] with the clause, rest and environment places as sinks and each terminal as a
conditional sink, and implementations MUST decide it through that same predicate.⟧ Every other
place is internal to the subnet and must be empty.

⟦s5|The verifier *shall* judge a quiescent marking to meet the contract exactly when, counting each
place of a clause once, the tokens across each clause's places number at most the clause's `max` if
it has one, at least its `min` unless some terminal marker is marked, and no marked place is
stranded under the rest set of [VER-014] whose sinks are the clause, rest and environment places and
whose conditional sinks are the terminals.⟧

**Closure.** The subnet is verified as a closed net. ⟦s6|Arrival group `i` contributes a source place
holding `min` tokens and a source place holding `max − min`, each left out with its transitions when
its count is 0, one transition per source and target place moving a token from that source onto the
place, and a transition with no output that declines a token of the second source.⟧ ⟦s7|A run is
therefore quiescent only once every required arrival has happened and every optional one has been
delivered or declined.⟧ The sources are ordinary places, not the environment places of [VER-006],
which never run dry and would make every quiescence property hold vacuously.

⟦s8|The contract's environment transitions join the closed net unchanged.⟧ Their actions never run, so
one that declares outputs gets a placeholder action instead of a [CORE-043] refusal. ⟦s9|Contract
places no arc touches join as places of their own and are listed in the report, so a clause over a
place nothing writes counts zero there: a finding, never a refusal.⟧ The closure's names
(`env:arrivals[i]`, `env:optional[i]`, `env:arrive[i]:<place>`, `env:arrive?[i]:<place>`,
`env:decline[i]`) and the environment transitions' names MUST NOT collide with the subnet's, and a
collision is refused. The in-flight split of [VER-004] applies to the closed net before the
terminal rewrite of [EXEC-042]: the environment transitions stay atomic and their arcs count as
tests, and a closed net the split refuses, or one that a declared mint transition ([NU-010]) is
not in, is `Unknown` before either route runs.

⟦s10|*If* a name the closure adds, or the name of an environment transition, is already a place or
transition name of the subnet, *then* the verifier *shall* refuse the closure, and it *shall* not
refuse a closure whose added and environment-transition names are distinct from each other, from the
subnet's names and from the environment places.⟧

⟦s11|The verifier *shall* build the closed net from the subnet's transitions, then the environment
transitions unchanged, then, for each arrival group `i` in order, numbered from 0, one immediate
transition `env:arrive[i]:<place>` per target place, in the group's order, taking one token from the
source `env:arrivals[i]` when `min > 0`, and one immediate transition `env:arrive?[i]:<place>` per
target place, in the group's order, taking one token from the source `env:optional[i]`, followed by
an immediate `env:decline[i]` discarding one, when `max > min`; the transitions the closure adds
have no other arc.⟧

⟦s12|The verifier *shall* start the closed net from the contract's initial marking with `min` tokens on
`env:arrivals[i]` and `max − min` tokens on `env:optional[i]` for each source it builds.⟧

⟦s13|The verifier *shall* treat as an environment place exactly a place that an environment transition
touches and the subnet does not, and *shall* make every place of the subnet and every place the
contract names a place of the closed net.⟧

⟦s14|The verifier *shall* mark as environment steps exactly the environment transitions and the
transitions the closure adds.⟧

**Routes.** Both decide the untimed claim of [VER-004].
1. *Graph.* The closed net's state-class graph is built **untimed**: every clock gets the interval
   of `immediate()`, so the graph holds exactly the markings the untimed encoders reason about,
   even for a subnet with timed transitions. When the graph closes within the class budget the
   verdict is exact: every class with no enabled transition is judged, and a reachable cycle is a
   run that never comes to rest. When it does not close, a violation among the explored classes is
   still real, since a class with no enabled transition is quiescent whether or not it was expanded
   and a cycle among explored edges is a real cycle; only the absence of violations needs the
   graph to close.

   ⟦s15|The graph route MUST NOT run on a closed net that declares **match (ν-join) transitions**, the
   exclusion of [VER-017] condition 1.⟧ The graph is name-blind: it fires a join on tokens whose
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

⟦s16|Both routes read quiescence as [VER-002] does: a class or marking whose enabled transitions are
all reapable ([TIME-013]) rests too.⟧ The reapable transitions are named on the closed net before
the SMT route makes every transition `immediate()`. The option `assumeNoReaping` restores the
plain reading, and the report of a closed net with a reapable transition says which reading the
verdict used.

**Verdict.**
- ⟦s17|`Proven`: every reachable quiescent marking of the closed net meets the contract and, where
  termination is required, no run fires forever.⟧
- `Violated`: lists every broken part the deciding route found (each clause by name, each stranded
  place by name, and termination), each with a witness. A witness carries the firing sequence from
  the initial marking, environment steps included, the markings along it, and the **port trace**:
  the firings that touch a port or are environment steps (arrivals, declines and environment
  transitions), each marked as such, with the token changes on contract places and on the places
  environment transitions touch. On the graph route a witness is a shortest one, and a termination
  witness is a lasso that marks where its cycle starts. ⟦s18|On the SMT route it is the deciding query's
  counterexample, which need not be shortest; one that does not replay as an ordered firing
  sequence ([VER-003]) is marked unconfirmed and names no stranded place.⟧
- `Unknown`: says which parts no route decided, and why.

⟦s19|*If* the verifier refuses the closure, *then* it *shall* refuse the verification.⟧

⟦s20|*When* the verifier accepts the closure, it *shall* return a result, and that result *shall* be
`Proven` when the closed net declares no match transition, its graph closes within a class budget
above 0, every reachable quiescent marking meets the contract and, where termination is required, no
run fires forever.⟧

⟦s21|The verifier *shall* return `Proven` only when every quiescent marking reachable in the closed net
from its initial marking meets the contract, reading quiescence as [VER-002] does, or, when
`assumeNoReaping` is set, as a marking with no enabled transition, and, where termination is
required, no run of the closed net fires forever.⟧

⟦s22|*When* the verdict is `Violated`, the verifier *shall* list at least one broken part, and for each
part with a confirmed witness *shall* report a firing sequence of the closed net from its initial
marking, environment steps included, that leads to a quiescent marking at which the named clause
fails, or to a quiescent marking at which each named place, at least one, holds a stranded token,
or, for `termination`, whose part before the reported cycle start leads to a marking and whose part
after it, not empty, leads from that marking back to it.⟧

⟦s23|The verifier *shall* mark a witness unconfirmed only when the SMT route decided, and *shall* name in
each clause part, confirmed or not, a clause of the contract.⟧

⟦s24|The verifier *shall* report a `termination` part only when the contract requires termination, and
*shall* name no stranded place in a witness that is not confirmed.⟧

⟦s25|*When* the verdict is `Unknown`, the verifier *shall* give a reason that is not empty.⟧

⟦s26|*If* the closed net declares a match transition, *then* the verifier *shall* return `Proven` or
`Violated` only from the SMT route.⟧

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
not stranded, and the environment's firings are marked in the port trace."#
