import Libpetri.Spec.Text

requirement_text VER_017
  id "VER-017"
  title "Bounded State-Space Enumeration Route"
  priority SHOULD
  kind B
  body r#"Before the SMT pipeline ([VER-001]), an implementation SHOULD try to decide the property by
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

⟦s1|The enumeration route *shall* apply exactly when the net it receives, after the rewrites of [VER-006], [VER-004] and [EXEC-042], declares no match transition, has no environment place registered and has only `immediate` transitions, and the class budget is positive.⟧

An applying route runs unless an earlier step of the pipeline decided or refused the query: the linear bound of [VER-015], Route B for a name-alignment property ([VER-012], [NU-055]), the refusals of [VER-003], [VER-004] and [NU-010], or a stop of [VER-013].

⟦s2|The build *shall* be stopped only when the total budget runs out or the caller cancels ([VER-013]).⟧

⟦s3|*While* the build is neither stopped by the total budget nor cancelled ([VER-013]), the state-class graph *shall* be closed exactly when it has fewer classes than the class budget.⟧

⟦s4|The state-class graph *shall* hold the initial class as its first class, and only classes reachable from it.⟧

⟦s5|*When* the graph is closed, the route *shall* return `Proven` exactly when no marking reachable from the initial marking violates the property, and `Violated` otherwise.⟧

⟦s6|*While* the build is neither stopped by the total budget nor cancelled ([VER-013]), the route *shall* return `Violated` when a counted class violates the property, where a counted class is any stored class for a safety property and a class the builder expanded for a quiescence property.⟧

⟦s7|*When* the route returns `Violated`, it *shall* report a counted class that violates the property, and a firing sequence from the initial marking to the marking of that class that is a path, in the graph the route built, from the initial class to that class.⟧

⟦s8|*When* the route returns `Violated`, the firing sequence it reports *shall* be no longer than any path, in the graph the route built, from the initial class to a counted class that violates the property.⟧

⟦s9|The route *shall not* return `Proven` from a graph that is not closed, and *shall* read nothing off a graph whose build was stopped by the total budget or cancelled.⟧

⟦s10|*When* the route returns `Proven` or `Violated`, the verifier *shall* return that verdict and *shall not* run the SMT pipeline.⟧

⟦s11|*If* the route does not run, or the graph is truncated and no counted class violates the property, *then* the verifier *shall* continue with the rest of the pipeline exactly as it does without the route, except that the time the route took counts against a total budget ([VER-013]).⟧

⟦s12|*If* the build is stopped by the total budget or cancelled, *then* the verifier *shall* return the `Unknown` of [VER-013].⟧

**The state-space cache, as EARS sentences.**

⟦s13|*When* a state-space cache is passed, the verifier *shall* key each entry by the caller's net, the transitions the in-flight split of [VER-004] rewrote, the initial marking and whether the graph is reduced ([VER-024]), and a query *shall* read and write only the entry of its own key.⟧

*While* the mode is `Arrivals(k)` or `Arrivals(min, max)` of [VER-006] and environment places are registered, *when* a state-space cache is passed, the verifier *shall* either key each entry also by the closure (the registered environment places in registration order and the mode), or not use the cache for that query and say so in the report.

⟦s14|*When* an entry holds a closed graph of `C` classes, a query at a budget greater than `C` *shall* reuse it, and a query at a budget of `C` or less *shall* read it as an explored prefix, in both cases without building.⟧

⟦s15|*When* an entry holds a truncation remembered at budget `B`, a query at a budget of `B` or less *shall* read its explored prefix without building.⟧

⟦s16|*When* an entry is empty, or holds a truncation remembered at a budget smaller than the query's, the query *shall* build at its own budget, and the entry *shall* then hold a closed graph as closed, a truncated graph with the query's budget, and, after a build stopped by the total budget or cancelled, what it held before.⟧

⟦s17|*If* a build fails, *then* the entry *shall* stay as the build found it, and the failure *shall* reach the query that ran the build.⟧

⟦s18|A query *shall* read a graph it built or reused as the route reads it without the cache, and a graph it read as an explored prefix as a graph that is not closed.⟧

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
graph falls through."#
