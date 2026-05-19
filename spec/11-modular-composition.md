# 11 — Modular Composition

This document specifies the **modular composition** extension of the CTPN engine: open net fragments (subnets) with declared interfaces, instantiation, structural composition by port mapping, synchronous channel fusion of interface transitions, action binding per instance, and orthogonal fusion of N places.

The vocabulary follows the ISO/IEC 15909-2 PNML *modular extension*: an open net is a Petri net augmented with an **interface** consisting of **interface places** (ports) and **interface transitions** (synchronous channels). A **module instance** is a renamed copy of an open net wired into an enclosing net by mapping its interface elements to enclosing-net elements.

Composition is **build-time only**. The runtime, exporter, verifier, and event subsystems see a normal flat `PetriNet` after composition completes. No semantic primitive in this document changes the contract of CORE, EXEC, CONC, EVT, ENV, VER, EXP, or PERF for the resulting flat net.

---

## Subnet Definition

#### MOD-001: SubnetDef Definition (open net + interface)

**Priority:** MUST

A **subnet definition** is an open Petri net fragment paired with a declared **interface**. The fragment is a structurally complete net definition (places, transitions, arcs, timing, priority, optional actions) per [CORE-040]; the interface enumerates which of its places are exposed as **ports** and which of its transitions are exposed as **synchronous channels**.

A subnet definition MAY be parameterised by a typed `Params` value supplied at instantiation time (see [MOD-010]). When unparameterised, the parameter type is the implementation's unit/void type.

**Acceptance Criteria:**
1. A subnet definition can be constructed with a body net and an interface.
2. The body net follows all CORE construction rules and is itself immutable per [CORE-041].
3. The interface enumerates a (possibly empty) set of ports and a (possibly empty) set of channels.
4. The subnet definition exposes both `body()` (the unrenamed body) and `iface()` (the interface) for inspection.
5. A subnet definition is immutable after construction.

**Test derivation:** Build a subnet definition with two places and one transition, exposing one place as a port; verify body, interface, port set, and channel set are accessible and unmodifiable.

---

#### MOD-002: Subnet Identity (sealed/sum-type distinction from PetriNet)

**Priority:** MUST

The engine distinguishes between **closed** nets (a `PetriNet` per [CORE-040], runnable by an executor) and **open** nets (a subnet definition, not directly runnable). The two share a common type abstraction (sealed sum, sealed interface, or enum, depending on language) so APIs can accept "any net" or restrict to one variant.

APIs that require a runnable net MUST reject an open subnet at the type level where the language permits, and at construction-time otherwise. APIs that require an open fragment MUST symmetrically reject a closed net.

**Acceptance Criteria:**
1. A common abstraction (`Subnet`) classifies nets as closed or open.
2. The two variants are distinguishable by type (sealed/sum-type), not merely by a runtime tag.
3. Passing an open subnet to an executor-construction API is a compile-time error in languages with sealed types, or a clearly reported construction-time error otherwise.
4. Passing a closed net to a composition API that expects an open fragment is similarly rejected.

**Test derivation:** Attempt to construct an executor from an open subnet; verify the call site does not compile (Java/Rust) or fails fast at construction (TypeScript). Attempt to compose a closed net into a builder; verify symmetric rejection.

---

## Interface Declaration

#### MOD-003: Port Declaration (name + direction + place)

**Priority:** MUST

An **interface place** (port) declares:
1. A **name** unique within the interface.
2. A **direction**: `Input`, `Output`, or `InOut`.
3. The underlying `Place<T>` from the body net it exposes.

The exposed place MUST be a place of the subnet's body. Two distinct ports MAY expose the same body place only if their directions differ; multiple ports with the same direction exposing the same body place are rejected at construction.

**Acceptance Criteria:**
1. A port can be declared with name, direction, and a body place.
2. The port name is unique within an interface (duplicate names rejected at build).
3. The exposed place's token type is preserved in the port's typed handle (see [MOD-011]).
4. A port whose underlying place is not present in the body net is rejected at build (see [MOD-006]).

**Test derivation:** Build an interface with ports `in: Input<String>` and `out: Output<String>`; verify both names and directions retrievable. Attempt to declare two ports with the same name; verify rejection. Attempt to declare a port over a place not in the body; verify rejection.

---

#### MOD-004: Port Direction Semantics (advisory; arcs govern flow)

**Priority:** SHOULD

Port direction is **advisory metadata** for documentation, visualization, and human reasoning. It does NOT constrain arc flow at runtime: an `Output` port's place MAY have input arcs from internal transitions; an `Input` port's place MAY be read by internal transitions. Actual token flow at run time is governed exclusively by arcs declared per CORE-030..CORE-035.

Implementations MAY emit a build-time warning when declared direction conflicts with the arc structure (e.g., an `Input` port whose place has no internal consumer transition), but MUST NOT reject the subnet on direction-versus-arc mismatch.

**Acceptance Criteria:**
1. Direction metadata is preserved and queryable via the port handle.
2. A subnet whose `Output` port place is also written internally by transitions is accepted at build.
3. A subnet whose `Input` port place is also read internally by transitions is accepted at build.
4. Where a warning channel exists, an obvious mismatch (declared `Input` with no internal consumer; declared `Output` with no internal producer) MAY emit a warning but MUST NOT raise an error.

**Test derivation:** Build a subnet whose `Output` port place has both an internal output arc (producer) and an internal input arc (consumer); verify build succeeds.

---

#### MOD-005: Channel Declaration (interface transitions for synchronous fusion)

**Priority:** MUST

An **interface transition** (synchronous channel) declares:
1. A **name** unique within the interface (sharing namespace with port names is implementation-defined; collisions MUST be rejected if they share a namespace).
2. The underlying `Transition` from the body net it exposes.

A channel MAY be bound at composition time to a caller-side transition, producing a single merged transition in the composed net (see [MOD-021]). Channels are the synchronization primitive for cross-instance and host-instance coupling at the transition level; ports synchronize at the place level.

**Acceptance Criteria:**
1. A channel can be declared with a name and a body transition.
2. The channel name is unique within its namespace.
3. The exposed transition's identity is preserved through the channel handle (see [MOD-011]).
4. A channel whose underlying transition is not present in the body net is rejected at build (see [MOD-006]).

**Test derivation:** Build an interface with one channel exposing a transition `attempt`; verify the channel handle resolves to the same transition identity in the renamed body. Attempt to declare two channels with the same name; verify rejection.

---

#### MOD-006: Subnet Validation at Build

**Priority:** MUST

Construction of a subnet definition MUST validate the interface against the body before producing an immutable result. Validation MUST reject:
1. A port whose underlying place is not present in the body.
2. A channel whose underlying transition is not present in the body.
3. Duplicate port names within the interface.
4. Duplicate channel names within the interface.
5. A body net that itself fails CORE construction validation (per [CORE-040], [CORE-041]).

Each failure MUST produce an error identifying the offending element by name.

**Acceptance Criteria:**
1. Each rejection case above produces an error at subnet build, not later at instantiation or composition.
2. Error messages name the offending port, channel, place, or transition.
3. A valid subnet definition is immutable after build.

**Test derivation:** Construct invalid subnets covering each rejection case; verify each fails at build with a message naming the offending element.

---

## Instantiation

#### MOD-010: Instance Creation via instantiate(prefix, params)

**Priority:** MUST

A subnet definition produces a **module instance** via `instantiate(prefix, params)`. Instantiation:
1. Takes a string `prefix` and a `params` value matching the subnet's parameter type.
2. Produces a renamed copy of the body net where every place name and every transition name is rewritten as `prefix + "/" + originalName`.
3. The renamed body is a structurally valid `PetriNet` per [CORE-040].
4. Arcs in the renamed body reference the renamed places; the arc topology is identical to the body's arc topology modulo the rename.
5. Timing, priority, and action of each transition are preserved (actions are shared by reference; see [MOD-030]).

The separator `"/"` is reserved by this requirement as the prefix separator. Implementations MUST use exactly `"/"`. Nested instantiation produces names of the form `outer/inner/originalName` (see [MOD-013]).

**Acceptance Criteria:**
1. `instantiate("buf1", params)` over a body containing place `slots` produces a renamed place with name `buf1/slots`.
2. Calling `instantiate` twice on the same definition with different prefixes produces two renamed bodies whose place and transition name sets are disjoint.
3. The renamed body is immutable.
4. A `params` value of the wrong type is rejected (compile-time in languages with generics; construction-time error otherwise).

**Depends on:** [CORE-001], [CORE-040]
**Test derivation:** Instantiate a subnet with prefix `b1`; verify every place name in the renamed body begins with `b1/`. Instantiate twice with prefixes `b1` and `b2`; verify name sets disjoint.

---

#### MOD-011: Instance Handle Map (typed port + channel handles)

**Priority:** MUST

A module instance MUST expose typed lookup handles:
1. `port(name, type)` returns the renamed `Place<T>` corresponding to the named port from the original interface.
2. `channel(name)` returns the renamed `Transition` corresponding to the named channel from the original interface.
3. `params()` returns the parameter value supplied at instantiation.
4. `prefix()` returns the prefix string supplied at instantiation.

The type parameter `T` MUST match the originally declared port token type. Mismatches MUST be reported as an error (compile-time error in languages with generics; runtime error otherwise).

**Acceptance Criteria:**
1. `port("input", String)` on an instance whose interface declared `input: Input<String>` returns the renamed `Place<String>`.
2. `port("input", Integer)` on the same instance is rejected (compile-time or runtime, per language).
3. `channel("attempt")` returns the renamed `Transition` whose original name was `attempt`.
4. Looking up a port or channel name that does not exist in the interface produces an error.
5. `params()` returns the value passed to `instantiate`.

**Depends on:** [MOD-003], [MOD-005], [MOD-010]
**Test derivation:** Build a subnet with port `input: Input<String>` and channel `attempt`; instantiate with prefix `r1`; verify `port("input", String)` returns the renamed place and `channel("attempt")` returns the renamed transition.

---

#### MOD-012: Per-Instance State Isolation

**Priority:** MUST

Each module instance has independent runtime state. After composition into a flat net, internal places of two distinct instances of the same subnet definition MUST occupy distinct slots in the compiled net's place index, hold disjoint token bags, and evolve independently under the executor.

This isolation is a structural consequence of name-prefixing per [MOD-010] (distinct prefixed names → distinct place identities → distinct slots). No additional runtime mechanism is required.

Internal place token state, internal transition enablement state, and internal transition timing clocks (per [TIME-010], [TIME-011]) MUST all be per-instance.

**Acceptance Criteria:**
1. Compose two instances of the same subnet definition (different prefixes) into one net; build and execute. Tokens added to instance A's internal place do not appear in instance B's corresponding internal place.
2. Firing a transition in instance A does not affect transition enablement in instance B.
3. Timing clocks of corresponding transitions in two instances are independent.

**Depends on:** [MOD-010], [CORE-070], [TIME-010]
**Test derivation:** Build a bounded-buffer subnet; compose two instances `b1` and `b2`; add tokens to `b1/slots`; verify `b2/slots` token count unchanged.

---

#### MOD-013: Nested Instantiation (prefix concatenation associative)

**Priority:** MUST

A subnet that itself composes other subnets MAY be instantiated. The resulting nested names use `"/"` as the separator at every level: `outer/inner/originalName`.

Prefix concatenation MUST be associative: instantiating a subnet `S` (which internally composes an instance `inner` of subnet `T`) with prefix `outer` produces a name `outer/inner/x` for every internal place `x` of `T`. This is observationally equivalent to: instantiate `T` with prefix `outer/inner` directly into a net, for the resulting flat name set.

**Acceptance Criteria:**
1. A subnet `S` containing a composed instance of `T` (instantiated with prefix `inner`), instantiated with prefix `outer`, produces names of the form `outer/inner/<original>`.
2. The flattened name set of the doubly-prefixed instantiation equals the name set of a single `T` instantiation with prefix `outer/inner`, composed at the top level.
3. Per-instance state isolation per [MOD-012] holds at every nesting level.

**Depends on:** [MOD-010], [MOD-012], [MOD-020]
**Test derivation:** Build subnet `T` with internal place `x`. Build subnet `S` that composes `T` instance with prefix `inner`. Instantiate `S` with prefix `outer`; verify `outer/inner/x` is among the renamed place names.

---

#### MOD-014: SubnetDef.fromNet retrofit utility

**Priority:** MAY

Implementations MAY provide a utility that constructs a subnet definition from an existing closed `PetriNet` plus an interface declaration that names places and transitions of that net by name. This allows pre-existing nets to be wrapped as reusable subnet fragments without rebuilding them.

The retrofit utility MUST validate the interface against the supplied net per [MOD-006] (port places exist, channel transitions exist, names unique).

**Acceptance Criteria:**
1. Where provided, `fromNet(net, iface)` produces a subnet definition whose body equals the supplied net (modulo immutability semantics).
2. The interface validation rules of [MOD-006] apply.
3. The resulting subnet definition is unparameterised (its parameter type is the implementation unit/void type).

**Test derivation:** Where the utility exists, build a `PetriNet` with places `a`, `b`; call `fromNet(net, iface{port: in -> a})`; verify the resulting subnet exposes port `in` over place `a`.

---

## Composition

#### MOD-020: Composition Operation (port mapping by structural rewrite)

**Priority:** MUST

The enclosing net's builder MUST support a `compose(instance, bindings)` operation that integrates a module instance into the enclosing net by **structural rewriting**:

1. Each binding maps an interface port name (resolved on the instance) to a caller-side `Place<T>`.
2. For every binding `(portName -> callerPlace)`: the instance's renamed port place is substituted with the caller place at every arc in the instance's renamed body.
3. Internal (non-port) places of the instance are added to the enclosing builder unchanged.
4. Every transition of the instance's renamed body (with rewritten arcs) is added to the enclosing builder.
5. Composition is **eager**: the rewrite happens at compose time, not at build, executor compile, or run time. The enclosing builder's place and transition sets reflect the composed structure immediately after `compose(...)` returns.

The result of composition over the enclosing builder MUST be observationally indistinguishable from a hand-written flat net containing the same places, transitions, and arcs.

Within a single `compose(instance, bindings)` call, every interface port MAY appear in the bindings at most once. Re-binding the same port name (whether to the same caller place or a different caller place) within one `compose(...)` call is a build-time error; the error message MUST enumerate both bindings (port name, both target caller places, both binding-site indices or labels where available). Symmetrically, the same caller-side `Transition` MAY appear as the target of at most one channel binding within a single `compose(...)` call; re-binding a caller transition to two channels of the same instance in one call is a build-time error enumerating both bindings (see also [MOD-021]).

**Acceptance Criteria:**
1. Compose an instance with binding `port "out" -> callerPlace P`; verify that every arc in the renamed body that referenced the port's renamed place now references `P` directly.
2. Internal places of the instance appear in the enclosing builder under their renamed (prefixed) names.
3. Transition count of the enclosing builder after compose equals (prior count) + (instance transition count).
4. Building the enclosing net produces a `PetriNet` whose structure is identical to a hand-written equivalent.
5. Re-binding the same port name twice in a single `compose(...)` call (whether to the same caller place or different ones) is rejected at compose time with an error naming the port and both target caller places.
6. Binding the same caller-side transition to two distinct channels of one instance in a single `compose(...)` call is rejected at compose time with an error naming the caller transition and both channels.

**Depends on:** [MOD-010], [MOD-011]
**Test derivation:** Build subnet with port `out`; compose with `out -> P`; export the resulting net and a hand-written equivalent; assert structural equivalence. Compose with `out -> P, out -> Q` in one call; verify rejection.

---

#### MOD-021: Channel Composition (transition merge: arc union + conflict resolution)

**Priority:** MUST

When a composition binding maps an interface channel to a caller-side `Transition`, the two transitions are **merged** into a single transition in the composed net. The merged transition combines:

1. **Arcs**: the union of all input, output, inhibitor, read, and reset arcs from both sides, with same-place arcs reconciled per the deduplication rule below.
2. **Timing** (per [TIME-001]): each timing variant is treated as its canonical closed interval on the firing-delay axis (in milliseconds, with `∞` denoting an unbounded upper end):
   - `Immediate` = `[0, 0]`
   - `Deadline(d)` = `[0, d]`
   - `Delayed(d)` = `[d, ∞)`
   - `Window(early, late)` = `[early, late]`
   - `Exact(d)` = `[d, d]`

   The merged timing is the **intersection** of the two intervals. The result is mapped back to a timing variant by shape: `[0, 0]` → `Immediate`; `[d, d]` with `d > 0` → `Exact(d)`; `[0, d]` with `d > 0, d < ∞` → `Deadline(d)`; `[d, ∞)` with `d > 0` → `Delayed(d)`; `[early, late]` with `0 < early < late < ∞` → `Window(early, late)`. Equal timings collapse to themselves (idempotent). If the intersection is empty, the merge MUST be rejected with an error naming both timings.
3. **Priority**: the caller side wins by default. Implementations MAY offer an explicit override.
4. **Action**: composed sequentially: caller-side action first, then instance-side action. The composed action is exposed to the executor as a single atomic firing — the executor sees one transition per [CORE-021].
5. **Identity**: the merged transition's name is the caller-side transition's name; the instance-side renamed channel transition is NOT separately added to the enclosing builder.

**Arc deduplication rule** (for clause 1): for every pair of arcs from the two sides targeting the same `Place` (by identity per [CORE-002]):
- (a) **Same arc type with same cardinality/weight**: collapse to a single arc.
- (b) **Same arc type with additive cardinalities/weights** (two `Input` arcs, two `Output` arcs, or two `Read` arcs whose cardinalities admit summation, e.g. `One` + `One` = `Exactly(2)`, `Exactly(n)` + `Exactly(m)` = `Exactly(n + m)`): the merged arc carries the summed weight.
- (c) **Same arc type with incompatible cardinalities** (e.g. `One` + `Exactly(2)` where the language does not permit summation, or `One` + `All`, or `Exactly(n)` + `AtLeast(m)`): the merge MUST be rejected at compose time with an error identifying both conflicting arcs by transition side, place, and cardinality.
- (d) **Different arc types** (e.g. one side declares an `Input` arc on `P` and the other declares a `Reset` arc on `P`, or `Read` + `Inhibitor`, etc.): the merge MUST be rejected at compose time with an error identifying both conflicting arcs by transition side, place, and arc type.

Inhibitor and Reset arcs to the same place from both sides collapse per rule (a) — they have no cardinality dimension to sum.

The result is one merged `Transition` in the flat net; firing it consumes/produces tokens per the unioned arc set in a single atomic step per [EXEC-001].

**Acceptance Criteria:**
1. Bind a caller transition `T` (with arcs `[in: P]`, `out: Q`, `Immediate`, priority 0) to a channel transition `C` (with arcs `[in: R]`, `out: S`, `Immediate`, priority 0). The composed net contains one transition with input arcs from both `P` and `R`, output arcs to both `Q` and `S`, `Immediate` timing.
2. Bind two transitions with disjoint (empty-intersection) timings — e.g., `Delayed(100ms)` (`[100, ∞)`) vs `Deadline(50ms)` (`[0, 50]`) — verify the compose call is rejected with a message identifying both timings.
3. Bind two transitions with overlapping non-`Immediate` timings — e.g., caller `Deadline(100ms)` (`[0, 100]`) and instance `Delayed(50ms)` (`[50, ∞)`) — verify the merged timing is `Window(50, 100)` (the interval `[50, 100]`). Bind `Window(10, 100)` and `Window(50, 200)`; verify the merged timing is `Window(50, 100)`. Bind `Exact(50)` and `Window(0, 100)`; verify the merged timing is `Exact(50)`.
4. The merged transition's action runs the caller-side action then the instance-side action sequentially within one firing; observable token movement is atomic from the executor's perspective.
5. After build and run, the executor invokes the merged transition once per fire (not twice).
6. **Arc deduplication — additive same-type:** bind a caller transition with `Input(One) -> P` to a channel transition with `Input(One) -> P` on the same caller place `P`; verify the merged transition has a single `Input(Exactly(2)) -> P` arc.
7. **Arc deduplication — different types are rejected:** bind a caller transition with `Input -> P` to a channel transition with `Reset -> P`; verify the compose call is rejected with a message naming both arcs.
8. **Arc deduplication — incompatible cardinalities are rejected:** bind a caller transition with `Input(One) -> P` to a channel transition with `Input(All) -> P`; verify the compose call is rejected with a message naming both arc cardinalities.
9. **Token timestamp on merged production:** when the merged transition fires and produces a token to a place that is itself a port-merge or fusion target, the produced token's timestamp is the timestamp at the production point of the firing per [CORE-013] and [TIME-010]. FIFO order among tokens produced into a merged place by distinct firings of one or more merged transitions is determined by the completion order of those firings, consistent with the happens-before guarantee per [CONC-002] and [CORE-013]. The merged transition emits a single `TokenAdded` event per produced token (cf. EVT-011), not one per side of the merge.

**Depends on:** [MOD-005], [CORE-021], [TIME-001], [CORE-013], [TIME-010], [CONC-002]
**Test derivation:** Compose two transitions with non-overlapping arcs; verify the resulting flat net has one transition combining all arcs. Compose with disjoint timing intervals; verify rejection. Compose with overlapping non-`Immediate` timings; verify the merged interval. Compose with two same-direction same-cardinality arcs on the same place; verify weight summation. Compose with conflicting arc types on the same place; verify rejection.

---

#### MOD-022: Type Compatibility at Compose

**Priority:** MUST

A port binding `port(name, T) -> callerPlace` is well-typed only when the port's declared token type and the caller place's token type are the same `T`. Implementations MUST enforce this:

1. In languages with parametric generics (Java, Rust), enforcement is **compile-time** via the typed binding API.
2. In languages without runtime generic reification (TypeScript), enforcement is **compile-time only** via the static type system; runtime per-token-type tagging is not required.
3. In any language where compile-time enforcement is unavailable for a particular call site (e.g., erased map-based binding overloads in Java), the binding MUST be rejected at compose time with a message identifying the port name, expected type, and observed type.

Channel bindings have no token-type check at the channel level (transitions are not typed); arc-level type compatibility falls out from the underlying place token types per [CORE-003].

**Acceptance Criteria:**
1. `port("in", String) -> Place<String>` binding compiles and composes successfully.
2. `port("in", String) -> Place<Integer>` binding fails at compile time in Java/Rust and is a TypeScript type error in `tsc`.
3. Where the compose API erases generics, a wrong-type binding is rejected at compose with a clear message.

**Depends on:** [CORE-003], [MOD-011], [MOD-020]
**Test derivation:** Java/Rust: write a wrong-type binding; observe compile error. TypeScript: write a wrong-type binding; observe `tsc --noEmit` error. Erased Java overload: verify runtime rejection.

---

#### MOD-023: Composition Produces Flat Net

**Priority:** MUST

After all `compose(...)` (and `fuse(...)` per [MOD-061]) calls have been made on a builder, `build()` MUST produce a `PetriNet` indistinguishable from a hand-written flat net that has the same places, transitions, arcs, timing, priority, and actions.

In particular, downstream consumers — the executor (CONC, EXEC), event subsystem (EVT), verifier (VER), and exporter (EXP) — MUST require no awareness of composition structure to operate on the composed net. Compiled net representations per [CONC-007], [CONC-020] MUST be constructed identically whether the source net was composed from subnets or hand-written.

**Acceptance Criteria:**
1. Build the composed net and a hand-written equivalent net; their compiled representations have identical place index, transition count, arc topology, bitmap masks, and timing arrays.
2. Running both nets under the same executor with the same initial marking produces identical event sequences and final markings.
3. Exporting both nets produces byte-equal DOT modulo group ordering.
4. Running verification on both nets produces identical results.

**Depends on:** [MOD-020], [MOD-021], [CONC-007], [EXEC-001]
**Test derivation:** Build a composed net `N1` and a hand-written equivalent `N2`; run both with identical initial markings; assert identical event sequences and final markings.

---

#### MOD-024: Identity-Default Port Inference (auto-compose)

**Priority:** SHOULD

The enclosing net's builder SHOULD support a single-argument `compose(instance)` overload that auto-binds every interface port declared on the subnet to the host place carried on that port's declaration. For each `port` returned by `instance.def().iface().ports()` the implementation MUST contribute a binding `(port.name() → port.place())`; the resulting binding map MUST be processed identically to an explicit `compose(instance, map)` call per [MOD-020]. The result MUST therefore satisfy [MOD-023] (composition produces a flat net) with no observable difference from the explicit form.

When the subnet declares no interface ports, the implementation MAY additionally infer bindings by walking the instance's renamed body and matching each renamed place against the host builder's place set, probed by the place's original (un-prefixed) identity. Body places that do not match stay private under their prefixed names per [MOD-010] and [MOD-012]. The probe identity SHOULD use the implementation's existing `Place` equality (per [CORE-002]); implementations whose `Place` equality is name-only MAY still implement the body-inference path but MUST document the more permissive matching contract in their API surface.

Channels are NOT auto-bound. If the subnet's interface declares any channel, `compose(instance)` MUST raise an error naming the channels and directing the caller to the explicit-binding `compose(instance, bindings)` overload per [MOD-021]. Transition identity is too delicate for inference — caller code is expected to think about which caller-side transition fuses with which channel.

The single-argument form is **additive** sugar over [MOD-020]; it does NOT replace the explicit-binding overloads. Callers SHOULD use the Consumer/Map overloads when (a) they need to rewire a port to a host place other than the one the SubnetDef declared, (b) the subnet has any channel, or (c) the subnet defines reusable ports whose host targets differ across instances.

**Acceptance Criteria:**
1. `compose(instance)` over a subnet with port `out: Output<T>` carrying host place `P` produces a net structurally equal to `compose(instance, map{out: P})`.
2. When the host builder did not pre-declare `P`, `P` MUST arrive in the merged net via the rewritten port arcs (same flow as explicit `bindPort`).
3. When the subnet declares no interface ports, body places equal to host places (by the implementation's `Place` equality per [CORE-002]) merge; other body places remain prefix-renamed.
4. `compose(instance)` on a subnet that declares any channel raises an error naming the channels and suggesting the explicit-binding overload.
5. Auto-compose followed by `build()` is observationally indistinguishable from the explicit `compose(instance, bindings)` followed by `build()` for the same target wiring (places, transitions, arcs, timing, priority, actions all equal).
6. An empty subnet (no body places, no transitions, no ports, no channels) composes as a no-op: the host builder's place/transition sets are unchanged.

**Depends on:** [MOD-003], [MOD-005], [MOD-010], [MOD-020], [MOD-023]
**Test derivation:** Build a subnet with port `out` carrying host place `P`; compose via `compose(instance)` and via `compose(instance, b -> b.bindPort("out", P))`; assert the resulting flat nets are structurally identical (place set, transition names in order, per-transition arc topology). Compose a subnet that declares a channel; verify the call is rejected with a message naming the channel and pointing at the explicit overload. Compose two instances of a producer-style subnet through a shared host place; verify both producer transitions emit to the same host place.

---

## Action Binding

#### MOD-030: Action Binding Per Instance (share-by-default, override via bindActions)

**Priority:** MUST

Actions associated with transitions in a subnet definition's body are carried through instantiation **by reference**, not by copy: by default, two instances of the same subnet definition share the same action object for each transition.

A module instance MUST support per-instance action override: `instance.bindActions(mapping)` produces a derived instance whose specified transitions (named by their **original**, pre-prefix names) carry the supplied actions instead of the shared defaults. Transitions not named in the override mapping retain the shared default action.

The override mechanism is per-instance: overriding actions on instance A does NOT affect instance B of the same subnet definition.

**Composition of multiple `bindActions` calls — last-wins replace, not chain.** Each call to `bindActions` returns a derived instance whose action map is the parent instance's action map with the per-transition entries from this call **overwriting** any existing entry for the same transition (entries for transitions not named in the call are inherited unchanged from the parent). Successive `bindActions` calls on the same instance compose left-to-right in derivation order: if `inst1 = inst0.bindActions({"t": A})` and `inst2 = inst1.bindActions({"t": B})`, then `inst2`'s `t` carries action `B`, not a sequential composition of `A` and `B`. A transition therefore carries **exactly one** action at composition time, regardless of how many `bindActions` calls produced the instance. Each `bindActions` call returns a new derived instance and MUST NOT mutate the receiver.

This requirement extends [CORE-042] (action binding separation) into the modular composition layer: subnets remain structure-only by default, with per-instance behavior layered on at composition time.

**Acceptance Criteria:**
1. By default, two instances of the same subnet definition reference the same action object per transition.
2. `instance.bindActions({"produce": newAction})` produces an instance whose `produce` transition uses `newAction`; the original instance is unchanged.
3. The override map keys use original (un-prefixed) transition names.
4. Transitions not named in the override map retain their shared default action.
5. Action override is purely structural (no runtime state); the override is established before the subnet is composed and fixed for the lifetime of the resulting net.
6. Successive `bindActions` calls compose as last-wins replacement: `inst.bindActions({"t": A}).bindActions({"t": B})` yields an instance whose `t` carries action `B`; action `A` is not invoked at run time for transition `t`.
7. A `bindActions` call that overrides transition `t` leaves the action of any transition `u != t` exactly as inherited from the receiver instance.
8. `bindActions` is non-mutating: invoking it on instance `inst` returns a derived instance; `inst` itself is unchanged and remains usable for subsequent independent derivations.

**Depends on:** [CORE-042], [MOD-010]
**Test derivation:** Instantiate the same subnet twice as `p1`, `p2`. Override `produce` action on `p1`; verify `p1/produce` runs the override action while `p2/produce` runs the default.

---

## Export and Debug

#### MOD-040: Export Grouping (subgraph cluster_* per instance prefix)

**Priority:** SHOULD

DOT export per [EXP-001] of a composed net SHOULD emit a `subgraph cluster_<sanitizedPrefix>` block for each top-level instance prefix detected in place and transition names. Membership of the cluster is every node whose name begins with `<prefix>/`. Nested instance prefixes (per [MOD-013]) produce nested cluster subgraphs.

The sanitization function applied to the prefix MUST match the existing DOT ID sanitization per [EXP-014] (non-`[A-Za-z0-9_]` characters, including `/`, replaced by `_`).

The cluster label SHOULD be the original (un-sanitized) prefix string for human readability.

This requirement does NOT change the styling, junction, or arc-rendering rules of EXP-002..EXP-014; it only adds grouping structure.

**Acceptance Criteria:**
1. Compose two instances with prefixes `b1` and `b2`; export DOT; verify the output contains `subgraph cluster_b1 { ... }` and `subgraph cluster_b2 { ... }` blocks.
2. Each cluster block contains exactly the nodes whose names begin with the corresponding prefix.
3. Nested instance prefixes produce nested cluster subgraphs.
4. A net with no composed instances (no `/` in any name) produces no cluster subgraphs.
5. Cluster IDs match the regex `cluster_[A-Za-z0-9_]+` (sanitized per [EXP-014]).

**Depends on:** [MOD-010], [EXP-001], [EXP-014]
**Test derivation:** Build a composed net with two top-level instances; export; assert cluster blocks present with correct membership and IDs.

---

#### MOD-041: Debug Protocol Subnet Instances

**Priority:** SHOULD

The debug protocol's `Subscribed` response (live net inspection) SHOULD carry, in addition to the existing place and transition descriptors, an enumeration of **subnet instance descriptors**. Each descriptor describes one top-level (or nested) instance present in the composed net and includes:

1. The instance prefix string (e.g., `b1` or `outer/inner`).
2. The originating subnet definition's name, where available.
3. The parameter value supplied at instantiation, where available.
4. The set of transitions belonging to the instance (full prefixed names).
5. The set of exposed (port) places belonging to the instance (full prefixed names).
6. An optional parent-prefix field for nested instances.

In addition, individual `PlaceInfo` and `TransitionInfo` entries in the debug protocol SHOULD carry an optional `instancePrefix` field derived from the name's prefix portion, so clients that do not parse names themselves can group nodes.

This requirement is observability-only; it does not change net behavior.

**Acceptance Criteria:**
1. A debug session subscribed to a composed net receives a list of subnet instance descriptors with one entry per top-level composed instance.
2. Each descriptor's transition and exposed-place sets accurately enumerate the instance's prefixed elements.
3. Each `PlaceInfo` and `TransitionInfo` for a node belonging to an instance carries the corresponding `instancePrefix`.
4. Nested instances are reported with their parent prefix.
5. A debug session subscribed to a non-composed net returns an empty subnet-instance list and no `instancePrefix` fields.

**Depends on:** [MOD-010], [MOD-013]
**Test derivation:** Subscribe to a debug session for a two-instance pipeline; assert the response carries two instance descriptors with the correct prefix, transitions, and exposed places.

---

## Verification

#### MOD-050: Verification Pass-Through on Composed Flat Net

**Priority:** MUST

All verification facilities specified in section 07 (VER) MUST operate on a composed flat net per [MOD-023] without any composition-aware adaptation. Specifically:

1. Property checks per [VER-002] (deadlock freedom, place bounds, mutual exclusion, unreachability).
2. P-invariant computation per [VER-005].
3. Structural analyses per [VER-020], [VER-021].
4. Untimed over-approximation per [VER-004].
5. State class graph analysis per [VER-010] where supported.

The verifier sees the composed net as a normal `PetriNet`. No modular extension to the verifier API is required by this requirement.

**Acceptance Criteria:**
1. Run the SMT verifier on a composed pipeline net; verification completes and produces a result of the same shape as for a hand-written net.
2. Verification results on the composed net match results on the hand-written equivalent net (per [MOD-023]).
3. P-invariant computation succeeds and produces invariants over the composed (prefixed) place names.

**Depends on:** [MOD-023], [VER-001]
**Test derivation:** Verify deadlock-freedom on a composed producer/buffer/consumer pipeline; verify the same property on the hand-written equivalent; assert identical results.

---

#### MOD-051: SubnetDef.verify(harness) for local property verification

**Priority:** SHOULD

A subnet definition SHOULD support a local verification operation `verify(harness)` that proves properties of the subnet **in isolation**, without first composing it into an enclosing net. The harness supplies:

1. A `params` value of the subnet's parameter type.
2. For each input port, a token-source description (e.g., a generator over an environment place per [ENV-001]) that bounds the input behavior to be considered.
3. The set of properties to check (per [VER-002]).

The implementation MAY realize this by wrapping the subnet in a synthetic enclosing net where each input port is fed by an `EnvironmentPlace` driven by the harness generator and each output port is observed read-only, then invoking the standard verifier per [MOD-050].

**Acceptance Criteria:**
1. Where provided, `verify(harness)` returns a verification result of the same shape as the standard verifier per [VER-003].
2. Invoking `verify` does not require the subnet to be composed into any enclosing net.
3. The harness's input generators bound the input behavior for the verification.

**Depends on:** [MOD-001], [VER-001], [ENV-001]
**Test derivation:** Build a leaky-bucket subnet parameterised by rate; supply a harness with a bounded request generator; verify that the bucket's `accepted` place is k-bounded for the specified k.

---

## Fusion (orthogonal to composition)

#### MOD-060: Fusion Set Declaration (orthogonal to composition)

**Priority:** MUST

A **fusion set** declares that N places — possibly drawn from different module instances — are to be treated as a single canonical place in the composed flat net. Fusion is **orthogonal to composition**:

1. Composition merges places via port-binding (one instance port place ↔ one caller place per binding).
2. Fusion merges N places at once via N-ary equivalence, after composition has flattened all subnet instances.

Fusion is the mechanism for modeling shared cross-instance state (e.g., a global rate limiter shared by three instances of a leaky-bucket subnet) without expressing the shared resource as an interface port on every subnet.

A fusion set has:
1. A canonical name used for the fused result.
2. A set of N member places (N >= 2; N=1 is a no-op and SHOULD be rejected).
3. All members MUST have compatible token types per [CORE-003] (implementation-defined enforcement matching [MOD-022]).

**Order of operations relative to composition.** Port substitution per [MOD-020] and channel merging per [MOD-021] happen **first**, during each `compose(...)` call on the enclosing builder. Fusion sets are then applied to the resulting post-composition flat net during `build()` per [MOD-061]. Consequently, fusion membership is evaluated against **post-composition place identity**: a fusion set MAY validly name a caller-side place that became the destination of one or more port substitutions, and the resulting fused canonical place observes the unioned token bag of all arcs that, after composition, target the (now-substituted) caller place plus all arcs targeting other fusion members.

**Acceptance Criteria:**
1. A fusion set can be declared with a name and a set of N (>= 2) member places.
2. Fusion sets are independent of port bindings: the same caller place MAY be both a port-binding destination and a fusion member; applying fusion produces a flat net in which the canonical fused place is the substitution target for every arc that previously referenced any port-substituted instance place or any non-canonical fusion member.
3. Token-type incompatibility among members is rejected per [CORE-003].
4. Declaring a fusion set with fewer than 2 members SHOULD be rejected as malformed.

**Depends on:** [CORE-003], [MOD-020]
**Test derivation:** Declare a fusion set with three members of type `Token<Permit>`; verify accepted. Declare with one member; verify rejection. Declare with mixed token types; verify rejection. Compose an instance binding port `out -> P`, then declare a fusion set `{P, Q}`; build; verify the canonical fused place is the substitution target of every arc that previously referenced the renamed instance port place or `Q`.

---

#### MOD-061: Fusion Resolution at build()

**Priority:** MUST

When `build()` is invoked on an enclosing builder containing one or more fusion sets, the builder MUST:

1. For each fusion set, choose a canonical member (implementation-defined; first declared member is the conventional choice).
2. Run a structural rewrite over every transition in the builder, substituting every non-canonical member with the canonical member in every input, output, inhibitor, read, and reset arc.
3. Remove non-canonical members from the builder's place set; the canonical member remains.
4. Produce the resulting flat `PetriNet`.

Fusion MUST be applied **after** all `compose(...)` calls have flattened subnet instances into the builder. Fusion membership is checked against the **post-composition** place identity per [MOD-060]: a member may be any place that exists in the builder after all compositions, including caller places that became port-substitution destinations during `compose(...)`. The fusion rewrite MUST be applied before [CORE-040] returns the immutable net so that no downstream consumer sees the un-fused intermediate state.

**Ordering of multiple fusion sets — commutative when disjoint.** When the enclosing builder declares two or more fusion sets, `build()` applies them in an implementation-defined order. If the member sets of every pair of declared fusion sets are pairwise **disjoint** (no place is a member of more than one fusion set), the final flat net MUST be independent of that order — the result is observationally identical regardless of which fusion set is rewritten first. Declaring two fusion sets whose member sets share a place SHOULD be rejected at build with a message naming the shared place and both fusion sets, since the canonical choice and the order of application would otherwise alter the final structure.

The result is a flat `PetriNet` per [MOD-023]; downstream consumers (executor, exporter, verifier, debug protocol) require no awareness of fusion.

Initial markings and per-place token state in the resulting flat net are concentrated on the canonical member: the canonical place observes the union of token bags that would otherwise have lived on the separate members.

**Acceptance Criteria:**
1. Three instances of a leaky-bucket subnet share a global rate-limiter via a single fusion set over their three internal limiter places. The built net contains one canonical limiter place; arcs that originally referenced any of the three members now reference the canonical.
2. Tokens added to any of the (now-fused) member places at initial-marking time appear on the canonical place in the executor's marking.
3. Non-canonical member places do NOT appear in the built net's place set.
4. Fusion is applied after composition: composing then fusing is observationally equivalent to writing a single hand-written net with the fused topology directly.
5. Re-exporting and re-verifying the fused net works without any awareness of fusion in the consumer.
6. Multiple fusion sets with **disjoint** member sets are commutative: building the same enclosing builder twice, with the implementation's fusion sets applied in opposite orders, MUST produce flat nets that are observationally identical (identical place set, transition set, arc topology, initial marking, executor behavior).
7. Declaring two fusion sets whose member sets share at least one place SHOULD be rejected at build with a message naming the shared place and both fusion sets.

**Depends on:** [MOD-023], [MOD-060], [CORE-040]
**Test derivation:** Build three leaky-bucket instances composed into one builder, with their limiter places joined as a fusion set. Build the net; assert (a) only one canonical limiter place exists in the place set, (b) every transition originally referencing any of the three limiter members now references the canonical, (c) executor behavior matches a hand-written equivalent. Declare two disjoint fusion sets; assert order-independence of the built result. Declare two overlapping fusion sets; assert build is rejected.
